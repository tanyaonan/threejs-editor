/**
 * iframe 嵌入桥：RUP 平台通过 iframe 嵌入三维编辑器时的宿主通信层
 *
 * 协议（消息结构 { type, payload?, requestId? }）：
 *   宿主 → iframe: rup:init({sceneDocument,displayType,theme,filePath}) / rup:set-scene({sceneDocument})
 *                 / rup:get-scene(requestId) / rup:set-active({active}) / rup:set-theme({theme})
 *                 / rup:undo / rup:redo
 *   iframe → 宿主: rup:ready({canUndo,canRedo}) / rup:scene-change({sceneDocument})
 *                 / rup:history-change({canUndo,canRedo}) / rup:inline-editing({editing})
 *                 / rup:save / rup:reply-scene(requestId,{sceneDocument})
 *
 * 场景文档: { schemaVersion: '1.0', engine: 'three-edit-cores', state: <saveSceneEdit() 输出> }
 *
 * 启用方式: URL 携带 ?embed=1（query 可位于 location.search 或 hash 内）
 */
import { restoreHistoryHandler } from '../editor/lib'
import templateJson from '../editor/template.json'

const parseQuery = () => {
  const params = new URLSearchParams(window.location.search)
  const hashIndex = window.location.hash.indexOf('?')
  if (hashIndex > -1) new URLSearchParams(window.location.hash.slice(hashIndex + 1)).forEach((v, k) => params.set(k, v))
  return params
}

const query = parseQuery()
const IS_EMBED = query.get('embed') === '1'
const IS_UNDARK = query.get('undark') !== null

const SCENE_WATCH_INTERVAL = 300 // 场景变更轮询间隔（ms）
const SCENE_CHANGE_DEBOUNCE = 300 // 场景变更上报防抖（ms）

let threeEditor = null
let pendingScene = null // { sceneDocument, version } 宿主最近下发的场景
let appliedVersion = 0 // 已注入编辑器的场景版本
let active = false // rup:set-active 记录
let lastSceneState = null
let lastConfigState = null
let watchTimer = null
let changeTimer = null
let embedTitle = '' // 宿主传入的页面标题（嵌入模式顶栏显示）
let titleListener = null // 标题变化回调（index.vue 绑定响应式 ref）

function post(type, payload, requestId) {
  const msg = { type }
  if (payload !== undefined) msg.payload = payload
  if (requestId !== undefined) msg.requestId = requestId
  parent.postMessage(msg, '*')
}

function toState(doc) {
  // 兼容 {schemaVersion,engine,state} 包装结构与裸 state
  return doc && doc.state ? doc.state : doc
}

/**
 * 把 source 中 target 缺失的键补齐（不覆盖既有值，仅深合并缺失部分）。
 * 数组键仅在缺失时补空数组，不合并内容（条目级单独处理）。
 */
function deepFill(target, source) {
  if (!target || !source || typeof target !== 'object' || typeof source !== 'object') return
  for (const key of Object.keys(source)) {
    const sv = source[key]
    if (Array.isArray(sv)) {
      if (target[key] === undefined) target[key] = []
    } else if (sv && typeof sv === 'object') {
      if (target[key] === undefined || target[key] === null) target[key] = {}
      deepFill(target[key], sv)
    } else if (target[key] === undefined) {
      target[key] = sv
    }
  }
}

/** 灯光条目完整骨架（提炼自编辑器官方场景结构，补 target/shadow 等核心必读字段） */
const LIGHT_ITEM_SKELETON = {
  target: { x: 0, y: 0, z: 0 },
  shadow: {
    bias: 0,
    radius: 1,
    mapSize: { x: 512, y: 512 },
    normalBias: 0,
    camera: { near: 0.5, far: 500, left: -5, right: 5, top: 5, bottom: -5 },
  },
  castShadow: false,
  layers: { mask: 1 },
}

/** 基础几何体条目骨架（提炼自编辑器官方场景结构）。material 字段缺失会导致渲染器不绘制（tris 0） */
const INNER_CORE_SKELETON = {
  renderOrder: 0,
  castShadow: false,
  receiveShadow: false,
  frustumCulled: false,
  layers: { mask: 1 },
  material: {
    visible: true,
    wireframe: false,
    vertexColors: false,
    toneMapped: true,
    transparent: false,
    opacity: 1,
    alphaTest: 0,
    depthTest: true,
    depthWrite: true,
    alphaHash: false,
    alphaToCoverage: false,
    blending: 1,
    emissive: 0,
    emissiveIntensity: 1,
    envMapIntensity: 1,
    side: 0,
    color: 0xffffff,
    roughness: 0.5,
    metalness: 0,
  },
}

/**
 * 规范化场景 state：以编辑器官方模板（template.json）为骨架补齐缺失字段，
 * 兼容外部生成的精简场景 JSON（缺 layers/position/target/shadow 等会导致 three-edit-cores
 * 解析抛 "Cannot read properties of undefined (reading 'mask'/'x')"）。
 * 只补缺失的默认值，不覆盖既有值。
 */
function normalizeSceneState(state) {
  if (!state || typeof state !== 'object') return state
  // effectComposer 统一最小化为 WebGL 直渲配置：
  // - 合成器模式在嵌入环境渲染输出为空（场景不可见）
  // - 模板默认的 fxaaPass/outlinePass 等 pass 配置同样会导致渲染中断（tris 0）
  // - 最小配置 { renderWay: 'webglRenderer' } 经验证可正常渲染，且与页面渲染器（scene-3d viewer）一致
  state.effectComposer = { renderWay: 'webglRenderer' }
  // 顶层：数组键缺失补空数组，对象键深合并模板默认
  for (const key of Object.keys(templateJson)) {
    if (Array.isArray(templateJson[key])) {
      if (state[key] === undefined) state[key] = []
    } else if (templateJson[key] && typeof templateJson[key] === 'object') {
      if (state[key] === undefined) state[key] = {}
      deepFill(state[key], templateJson[key])
    }
  }
  // 条目级：补基础 Object3D 字段 + 按模板骨架补全（灯光额外补 target/shadow）
  for (const key of ['lightCores', 'innerCores', 'modelCores', 'drawCores', 'textCores', 'particleCores', 'designCores']) {
    const list = state[key]
    if (!Array.isArray(list)) continue
    const tplList = templateJson[key]
    const tplItem = Array.isArray(tplList) && tplList.length ? tplList[0] : null
    for (const item of list) {
      if (!item || typeof item !== 'object') continue
      if (item.layers === undefined || item.layers === null) item.layers = { mask: 1 }
      if (item.visible === undefined) item.visible = true
      if (item.position === undefined) item.position = { x: 0, y: 0, z: 0 }
      if (item.rotation === undefined) item.rotation = { x: 0, y: 0, z: 0 }
      if (item.scale === undefined) item.scale = { x: 1, y: 1, z: 1 }
      if (tplItem) deepFill(item, tplItem)
      // 灯光条目额外补 target/shadow（模板默认灯光是精简 AmbientLight，DirectionalLight/SpotLight 必读这些字段）
      if (key === 'lightCores') {
        // AmbientLight/HemisphereLight 没有 shadow 对象，带 shadow 字段会导致核心设置 shadow.bias 崩溃
        if (item.type === 'AmbientLight' || item.type === 'HemisphereLight') {
          delete item.shadow
        } else {
          deepFill(item, LIGHT_ITEM_SKELETON)
        }
      }
      // 基础几何体条目补完整字段（material 字段缺失会导致渲染器不绘制，视口空白）
      if (key === 'innerCores') deepFill(item, INNER_CORE_SKELETON)
    }
  }
  return state
}

function applyScene(doc) {
  pendingScene = { sceneDocument: doc, version: (pendingScene?.version || 0) + 1 }
  if (threeEditor && toState(doc)) {
    threeEditor.resetEditorStorage(normalizeSceneState(toState(doc)))
    appliedVersion = pendingScene.version
  }
}

function applyTitle(payload) {
  // 优先页面标题（rup:init payload.title），回退 filePath
  const raw = (payload?.title || payload?.filePath || '')
  const title = typeof raw === 'string' && raw.trim() ? raw.trim() : ''
  if (title && title !== embedTitle) {
    embedTitle = title
    titleListener?.(embedTitle)
  }
}

function applyTheme(theme) {
  // ?undark 兼容：强制不启用暗色
  document.documentElement.classList.toggle('dark', theme === 'dark' && !IS_UNDARK)
}

function wrapScene() {
  return { schemaVersion: '1.0', engine: 'three-edit-cores', state: threeEditor.saveSceneEdit() }
}

/**
 * 构建场景对象树（宿主 AI 对话图层面板使用，参考编辑器右侧场景树面板的递归解析方式）。
 * 过滤辅助对象（helper/相机/变换控件），保留场景对象层级、变换与材质/几何信息。
 */
function buildSceneTree(node, depth = 0) {
  if (!node || typeof node.children === 'undefined' || depth > 12) return []
  const items = []
  for (const child of node.children) {
    if (child.isHelper || child.isCamera || child.isTransformControls) continue
    if (child.type && (child.type.includes('Helper') || child.type === 'Gizmo')) continue
    const item = {
      name: child.name || child.type,
      type: child.type,
      visible: child.visible !== false,
    }
    if (child.position) {
      item.position = { x: +child.position.x.toFixed(3), y: +child.position.y.toFixed(3), z: +child.position.z.toFixed(3) }
    }
    if (child.scale) {
      item.scale = { x: +child.scale.x.toFixed(3), y: +child.scale.y.toFixed(3), z: +child.scale.z.toFixed(3) }
    }
    const mat = child.material
    if (mat && !Array.isArray(mat)) {
      item.material = {
        type: mat.type,
        color: mat.color ? '#' + mat.color.getHexString() : undefined,
      }
      if (mat.transparent) item.material.transparent = true
      if (typeof mat.opacity === 'number') item.material.opacity = +mat.opacity.toFixed(2)
    }
    if (child.geometry) item.geometry = child.geometry.type
    const children = buildSceneTree(child, depth + 1)
    if (children.length) item.children = children
    items.push(item)
  }
  return items
}

function handleUndoRedo(isRedo) {
  const handlerHistory = threeEditor?.handler?.handlerHistory
  if (handlerHistory) {
    restoreHistoryHandler(handlerHistory, isRedo ? 'y' : 'z')
  } else {
    // 核心未暴露历史栈，回告宿主不支持
    post('rup:history-change', { canUndo: false, canRedo: false, unsupported: true })
  }
}

function onMessage(event) {
  const msg = event.data
  if (!msg || typeof msg.type !== 'string') return
  switch (msg.type) {
    case 'rup:init':
      applyScene(msg.payload?.sceneDocument)
      // 设计器保持自身默认主题（暗色），不随宿主 init 的 theme 强制切换；
      // 需要切换主题由宿主显式发送 rup:set-theme
      applyTitle(msg.payload)
      active = !!msg.payload?.active
      break
    case 'rup:set-scene':
      applyScene(msg.payload?.sceneDocument)
      break
    case 'rup:get-scene':
      if (threeEditor) post('rup:reply-scene', { sceneDocument: wrapScene() }, msg.requestId)
      break
    case 'rup:get-scene-tree': {
      if (threeEditor) {
        post('rup:reply-scene-tree', { tree: buildSceneTree(threeEditor.scene) }, msg.requestId)
      }
      break
    }
    case 'rup:set-theme':
      applyTheme(msg.payload?.theme)
      break
    case 'rup:set-active':
      active = !!msg.payload?.active
      break
    case 'rup:undo':
      handleUndoRedo(false)
      break
    case 'rup:redo':
      handleUndoRedo(true)
      break
  }
}

function scheduleSceneChange() {
  if (changeTimer) clearTimeout(changeTimer)
  changeTimer = setTimeout(() => {
    changeTimer = null
    try { post('rup:scene-change', { sceneDocument: wrapScene() }) } catch (e) {}
  }, SCENE_CHANGE_DEBOUNCE)
}

/** 关键配置段快照：坐标轴/网格开关、渲染器、轨道控制、场景环境、相机（不随动画变化，可安全对比） */
function getConfigSnapshot() {
  try {
    const s = threeEditor.saveSceneEdit()
    // 静态配置 + 相机/轨道（视角变化也同步回写；拖拽/阻尼的持续变化由上报防抖合并，停止后单次发送）。
    // 对象变换快照：拖拽/改属性（即使不进 handlerHistory）也能触发回写。
    const orbit = s.orbitControls
    const objects = {}
    for (const key of ['innerCores', 'modelCores', 'lightCores']) {
      objects[key] = (s[key] || []).map((c) => ({
        name: c.name,
        visible: c.visible,
        position: c.position,
        rotation: c.rotation,
        scale: c.scale,
        color: c.material ? c.material.color : undefined,
      }))
    }
    return JSON.stringify({
      helpers: s.handler?.helpers,
      renderer: s.webglRenderer,
      orbit,
      scene: s.scene,
      camera: s.perspectiveCamera,
      objects,
    })
  } catch (e) {
    return null
  }
}

function startSceneWatch() {
  if (watchTimer) return
  watchTimer = setInterval(() => {
    try {
      // 变化检测：① 用户操作历史（对象编辑：拖拽/改属性等）
      //          ② 关键配置段（坐标轴/网格/渲染器/轨道/场景/相机等开关与参数，如"显示坐标轴"开关）
      // 配置段不随动画变化，可安全对比；历史检测避免动画造成的持续序列化差异把上报防抖无限重置
      const history = threeEditor?.handler?.handlerHistory
      const histState = history && typeof history === 'object'
        ? `${history.list?.length ?? 0}:${history.index ?? 0}:${history.reList?.length ?? 0}`
        : null
      const configState = getConfigSnapshot()
      const changed =
        (histState !== null && histState !== lastSceneState) ||
        (configState !== null && configState !== lastConfigState)
      if (changed) {
        const isFirstSnapshot = lastSceneState === null
        lastSceneState = histState
        lastConfigState = configState
        // 首次轮询仅建立基线，不触发上报
        if (!isFirstSnapshot) scheduleSceneChange()
      }
    } catch (e) {}
  }, SCENE_WATCH_INTERVAL)
}

export function isEmbedMode() {
  return IS_EMBED
}

/** 挂载宿主消息监听（组件 onMounted 后调用，仅 embed 模式生效） */
export function initEmbedBridge() {
  if (!IS_EMBED) return
  window.addEventListener('message', onMessage)
}

/** 构造编辑器时读取宿主下发的场景文档（读取后标记已应用，避免重复注入） */
export function getEmbedScene() {
  if (pendingScene && appliedVersion !== pendingScene.version) {
    appliedVersion = pendingScene.version
    const doc = pendingScene.sceneDocument
    normalizeSceneState(toState(doc))
    return doc
  }
  return null
}

/** 嵌入模式顶栏标题：宿主 rup:init 传入的页面标题（filePath） */
export function getEmbedTitle() {
  return embedTitle
}

/** 订阅顶栏标题变化（index.vue 用于绑定响应式 ref） */
export function onEmbedTitleChange(callback) {
  titleListener = callback
}

/** 编辑器构造完成（emitThreeEditor）后调用：注入未应用的宿主场景、上报 rup:ready、启动场景变更轮询 */
export function setupEmbedEditor(editor) {
  if (!IS_EMBED) return
  threeEditor = editor
  if (pendingScene && appliedVersion !== pendingScene.version && toState(pendingScene.sceneDocument)) {
    threeEditor.resetEditorStorage(normalizeSceneState(toState(pendingScene.sceneDocument)))
    appliedVersion = pendingScene.version
  }
  post('rup:ready', { canUndo: false, canRedo: false })
  startSceneWatch()
}
