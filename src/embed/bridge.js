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
import * as THREE from 'three'
import { RoomEnvironment } from 'three/examples/jsm/environments/RoomEnvironment.js'
import { RoundedBoxGeometry } from 'three/examples/jsm/geometries/RoundedBoxGeometry.js'

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

/**
 * 颜色归一化：设计器回写（saveSceneEdit）的材质/灯光颜色可能是 THREE.Color 对象
 * （{isColor:true, r, g, b}，分量 0-1），three-edit-cores 解析时按数字处理，对象会导致颜色变黑。
 * 统一转为十进制数字（0xRRGGBB）。
 */
function normalizeColorValue(value) {
  if (value && typeof value === 'object' && typeof value.r === 'number' && typeof value.g === 'number' && typeof value.b === 'number') {
    const r = Math.max(0, Math.min(1, value.r))
    const g = Math.max(0, Math.min(1, value.g))
    const b = Math.max(0, Math.min(1, value.b))
    return (Math.round(r * 255) << 16) + (Math.round(g * 255) << 8) + Math.round(b * 255)
  }
  return value
}

/** 归一化材质颜色（color/emissive 等 Color 字段） */
function normalizeMaterialColors(mat) {
  if (!mat || typeof mat !== 'object') return
  if (mat.color !== undefined) mat.color = normalizeColorValue(mat.color)
  if (mat.emissive !== undefined) mat.emissive = normalizeColorValue(mat.emissive)
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
      // 颜色归一化：设计器回写的颜色可能是 THREE.Color 对象（isColor），转十进制数字避免变黑
      if (key === 'lightCores' && item.color !== undefined) {
        item.color = normalizeColorValue(item.color)
      }
      if (item.material && typeof item.material === 'object') {
        normalizeMaterialColors(item.material)
      }
      // 灯光条目额外补 target/shadow（模板默认灯光是精简 AmbientLight，DirectionalLight/SpotLight 必读这些字段）
      if (key === 'lightCores') {
        // intensity 必须为有效正数：null/0/NaN 会使 three-edit-cores 光照计算异常，设计器视口全黑
        if (typeof item.intensity !== 'number' || !isFinite(item.intensity) || item.intensity <= 0) {
          item.intensity = 1
        }
        // AmbientLight/HemisphereLight/RectAreaLight 没有 shadow 对象，带 shadow 字段会导致核心设置 shadow.bias 崩溃
        if (item.type === 'AmbientLight' || item.type === 'HemisphereLight' || item.type === 'RectAreaLight') {
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

/**
 * 修复核心包（three-edit-cores）PointLight/SpotLight 强度解析缺陷：
 * 加载场景后其 intensity 可能为 NaN/null（序列化时 NaN 变 null），导致全部片元光照计算污染、视口全黑。
 * 在 resetEditorStorage 之后遍历场景修正，保证渲染与保存（saveSceneEdit）都输出有效强度。
 */
function fixSceneLights(editor) {
  try {
    editor.scene.traverse((o) => {
      if (o.isPointLight || o.isSpotLight) {
        if (typeof o.intensity !== 'number' || !isFinite(o.intensity) || o.intensity <= 0) {
          o.intensity = 1
        }
        if (typeof o.distance !== 'number' || !isFinite(o.distance) || o.distance < 0) o.distance = 0
        if (typeof o.decay !== 'number' || !isFinite(o.decay) || o.decay < 0) o.decay = 1
      }
    })
  } catch (e) {}
}

/**
 * 程序化环境光照（three 内置 RoomEnvironment，无外部资源依赖）：
 * scene.environmentEnabled 开启时注入环境贴图，金属/玻璃材质获得真实反射，提升场景质感。
 * 与页面渲染器（scene-3d viewer）的 environmentEnabled 行为保持一致。
 */
function applySceneEnvironment(editor, state) {
  try {
    const scene = editor.scene
    if (!scene) return
    const enabled = !!(state && state.scene && state.scene.environmentEnabled === true)
    if (enabled) {
      const pmrem = new THREE.PMREMGenerator(editor.renderer)
      const tex = pmrem.fromScene(new RoomEnvironment(), 0.04).texture
      pmrem.dispose()
      scene.environment = tex
    } else if (scene.environment) {
      scene.environment = null
    }
  } catch (e) {}
}

/**
 * 程序化纹理（Canvas 2D 噪声，无外部资源）：与 scene-3d viewer 一致的表面质感，
 * 按对象语义自动附加油墙面微噪/地面颗粒/金属拉丝，消除纯色"塑料感"。
 */
const TEXTURE_KINDS = {
  concrete: { base: 118, amp: 32, detail: 'grain' },
  ground: { base: 72, amp: 22, detail: 'grain' },
  wall: { base: 206, amp: 14, detail: 'grain' },
  metal: { base: 150, amp: 10, detail: 'brushed' },
}

function createProceduralTexture(kind, seed = 7) {
  try {
    const size = 256
    const canvas = document.createElement('canvas')
    canvas.width = canvas.height = size
    const ctx = canvas.getContext('2d')
    let s = seed || 7
    const rand = () => { s = (s * 16807) % 2147483647; return s / 2147483647 }
    const cfg = TEXTURE_KINDS[kind] || TEXTURE_KINDS.concrete
    const img = ctx.createImageData(size, size)
    for (let y = 0; y < size; y++) {
      for (let x = 0; x < size; x++) {
        const i = (y * size + x) * 4
        let v = cfg.base + rand() * cfg.amp
        if (cfg.detail === 'brushed') v = cfg.base + Math.sin(y / size * Math.PI * 26) * 9 + rand() * cfg.amp
        img.data[i] = v
        img.data[i + 1] = v
        img.data[i + 2] = v
        img.data[i + 3] = 255
      }
    }
    ctx.putImageData(img, 0, 0)
    const tex = new THREE.CanvasTexture(canvas)
    tex.wrapS = tex.wrapT = THREE.RepeatWrapping
    tex.repeat.set(3, 3)
    return tex
  } catch (e) {
    return null
  }
}

function inferTextureKind(name, mat) {
  const n = String(name || '').toLowerCase()
  if (mat && (mat.transparent || (mat.emissive && mat.emissive.getHex() !== 0))) return null
  if (/玻璃|glass|透明/.test(n)) return null
  if (/金属|钢|铁|管|柱|烟囱|管道|螺栓|设备|栏杆/.test(n)) return 'metal'
  if (/地面|道路|路面|路|floor|ground|场地|停车位/.test(n)) return 'ground'
  if (/墙|屋顶|楼|建筑|厂房|宿舍|仓库|车间|围墙|勒脚/.test(n)) return 'wall'
  return null
}

/** 场景加载后遍历材质附加程序化纹理（仅未带纹理的 Standard/Lambert/Phong，玻璃/发光跳过） */
function fixSceneMaterials(editor) {
  try {
    editor.scene.traverse((o) => {
      if (!o.isMesh || Array.isArray(o.material)) return
      const mat = o.material
      if (mat.type !== 'MeshStandardMaterial' && mat.type !== 'MeshLambertMaterial' && mat.type !== 'MeshPhongMaterial') return
      if (mat.map || mat.alphaMap) return
      const kind = inferTextureKind(o.name, mat)
      if (!kind) return
      const tex = createProceduralTexture(kind)
      if (tex) {
        mat.map = tex
        mat.bumpMap = tex
        mat.bumpScale = 0.02
        mat.needsUpdate = true
      }
    })
  } catch (e) {}
}

/** 圆角化：比例接近立方体的 Box 替换为 RoundedBoxGeometry（消除"积木直角"塑料感，与 scene-3d viewer 一致） */
function roundSceneBoxes(editor) {
  try {
    editor.scene.traverse((o) => {
      if (!o.isMesh || !o.geometry || o.geometry.type !== 'BoxGeometry') return
      const p = o.geometry.parameters
      if (!p) return
      const w = p.width || 1, h = p.height || 1, d = p.depth || 1
      const maxSide = Math.max(w, h, d)
      const minSide = Math.min(w, h, d)
      if (maxSide <= 0.3 || maxSide / minSide > 3) return
      const g = new RoundedBoxGeometry(w, h, d, 3, minSide * 0.07)
      o.userData.origGeometry = o.geometry // 保留原始 Box，saveSceneEdit 前换回（防止增强类型泄漏到 JSON）
      o.geometry.dispose()
      o.geometry = g
    })
  } catch (e) {}
}

/** 确定性 3D 值噪声（与 scene-3d viewer 一致）：哈希格点 + 三线性插值 + 2 倍频叠加 */
function hashNoise3(x, y, z) {
  let h = (Math.imul(x, 374761393) + Math.imul(y, 668265263) + Math.imul(z, 1274126177)) | 0
  h = Math.imul(h ^ (h >>> 13), 1103515245)
  return ((h ^ (h >>> 16)) >>> 0) / 4294967295
}

function valueNoise3(x, y, z) {
  const xi = Math.floor(x), yi = Math.floor(y), zi = Math.floor(z)
  const xf = x - xi, yf = y - yi, zf = z - zi
  const u = xf * xf * (3 - 2 * xf), v = yf * yf * (3 - 2 * yf), w = zf * zf * (3 - 2 * zf)
  const c000 = hashNoise3(xi, yi, zi), c100 = hashNoise3(xi + 1, yi, zi)
  const c010 = hashNoise3(xi, yi + 1, zi), c110 = hashNoise3(xi + 1, yi + 1, zi)
  const c001 = hashNoise3(xi, yi, zi + 1), c101 = hashNoise3(xi + 1, yi, zi + 1)
  const c011 = hashNoise3(xi, yi + 1, zi + 1), c111 = hashNoise3(xi + 1, yi + 1, zi + 1)
  const x00 = c000 + (c100 - c000) * u, x10 = c010 + (c110 - c010) * u
  const x01 = c001 + (c101 - c001) * u, x11 = c011 + (c111 - c011) * u
  const y0 = x00 + (x10 - x00) * v, y1 = x01 + (x11 - x01) * v
  return y0 + (y1 - y0) * w
}

function fbmNoise3(x, y, z) {
  return 0.65 * valueNoise3(x, y, z) + 0.35 * valueNoise3(x * 2.7 + 11, y * 2.7 + 11, z * 2.7 + 11)
}

/** 有机对象类型（与 scene-3d viewer 一致）：树冠/树叶/灌木/绿化 → leaf；云 → cloud。排除"百叶" */
function inferOrganicKind(name) {
  const n = String(name || '').toLowerCase()
  if (/云|cloud/.test(n)) return 'cloud'
  if (/树冠|树叶|灌木|绿化|(?<!百)叶/.test(n)) return 'leaf'
  return null
}

/** 有机形变（与 scene-3d viewer 一致）：球体/多面体顶点沿法向噪声位移，leaf 面片化、cloud 低频平缓 */
function displaceOrganicGeometry(geometry, kind) {
  const radius = (geometry.parameters && geometry.parameters.radius) || 0.5
  const freq = kind === 'cloud' ? 2.2 / radius : 3.2 / radius
  const amp = kind === 'cloud' ? 0.4 : 0.55
  const pos = geometry.attributes.position
  const v = new THREE.Vector3()
  for (let i = 0; i < pos.count; i++) {
    v.fromBufferAttribute(pos, i)
    const n = fbmNoise3(v.x * freq, v.y * freq, v.z * freq)
    v.multiplyScalar(1 + (n - 0.5) * amp)
    pos.setXYZ(i, v.x, v.y, v.z)
  }
  pos.needsUpdate = true
  if (kind === 'leaf') {
    const g = geometry.toNonIndexed()
    g.computeVertexNormals()
    geometry.dispose()
    return g
  }
  geometry.computeVertexNormals()
  return geometry
}

/** 场景加载后对树冠/云等有机对象做噪声形变（写实轮廓，与 scene-3d viewer 一致） */
function fixSceneOrganic(editor) {
  try {
    editor.scene.traverse((o) => {
      if (!o.isMesh || !o.geometry) return
      const kind = inferOrganicKind(o.name)
      if (!kind) return
      if (o.geometry.type !== 'SphereGeometry' && o.geometry.type !== 'IcosahedronGeometry') return
      o.userData.origGeometry = o.geometry // 保留原始球体，saveSceneEdit 前换回（防止 BufferGeometry 泄漏到 JSON）
      o.geometry = displaceOrganicGeometry(o.geometry, kind)
      if (kind === 'leaf' && o.material && !Array.isArray(o.material)) {
        o.material.flatShading = true
        o.material.needsUpdate = true
      }
    })
  } catch (e) {}
}

/** 场景自动取景：相机对准场景包围盒中心（查看器标准行为；生成质量问题由提示词约束，不做兼容修补） */
function centerAndFrameScene(editor) {
  try {
    const scene = editor.scene
    const camera = editor.camera
    if (!scene || !camera) return
    const box = new THREE.Box3()
    let has = false
    scene.traverse((o) => {
      if (o.isMesh && o.visible && !o.isHelper && o.name && !/云|cloud/i.test(o.name)) {
        box.expandByObject(o)
        has = true
      }
    })
    if (!has) return
    const size = box.getSize(new THREE.Vector3())
    const maxSide = Math.max(size.x, size.y, size.z)
    if (maxSide > 50 || maxSide < 0.05) {
      const k = maxSide > 50 ? 40 / maxSide : 3 / maxSide
      scene.traverse((o) => {
        if (o.isMesh && !o.isHelper) o.scale.multiplyScalar(k)
      })
      box.setFromObject(scene)
      size.copy(box.getSize(new THREE.Vector3()))
    }
    const center = box.getCenter(new THREE.Vector3())
    const d = Math.max(size.x, size.z, 1) * 1.4 + 1.5
    // 相机位于包围盒中心斜上方 45°，轨道目标对准中心（场景偏离原点也能正确取景）
    camera.position.set(center.x + d * 0.72, center.y + d * 0.48, center.z + d * 0.72)
    if (editor.controls) {
      editor.controls.target.set(center.x, center.y, center.z)
      editor.controls.update()
    }
    camera.lookAt(center.x, center.y, center.z)
  } catch (e) {}
}

/** 渲染器质量：ACES 电影色调映射（写实色彩）+ 柔和阴影（与 scene-3d viewer 一致） */
function fixRendererQuality(editor, state) {
  try {
    const r = editor.renderer
    if (!r) return
    const tm = state && state.webglRenderer && typeof state.webglRenderer.toneMapping === 'number' ? state.webglRenderer.toneMapping : 0
    if (tm !== 0) {
      r.toneMapping = 4 // ACESFilmicToneMapping
      r.toneMappingExposure = 1
    }
    const shadows = !!(state && state.webglRenderer && state.webglRenderer.shadowMap && state.webglRenderer.shadowMap.enabled)
    if (shadows) {
      r.shadowMap.enabled = true
      r.shadowMap.type = 2 // PCFSoftShadowMap
    }
  } catch (e) {}
}

function applyScene(doc) {
  pendingScene = { sceneDocument: doc, version: (pendingScene?.version || 0) + 1 }
  if (threeEditor && toState(doc)) {
    const state = normalizeSceneState(toState(doc))
    threeEditor.resetEditorStorage(state)
    fixSceneLights(threeEditor)
    fixSceneMaterials(threeEditor)
    roundSceneBoxes(threeEditor)
    fixSceneOrganic(threeEditor)
    fixRendererQuality(threeEditor, state)
    applySceneEnvironment(threeEditor, state)
    // resetEditorStorage 异步创建场景对象，取景需延迟到对象就绪后执行
    scheduleFrameScene()
    appliedVersion = pendingScene.version
  }
}

let frameSceneTimer = null
/** 延迟取景（等 resetEditorStorage 的场景对象创建完成），并防抖多次触发 */
function scheduleFrameScene() {
  if (frameSceneTimer) clearTimeout(frameSceneTimer)
  frameSceneTimer = setTimeout(() => {
    frameSceneTimer = null
    if (threeEditor) centerAndFrameScene(threeEditor)
  }, 200)
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

/** 关键配置段快照：坐标轴/网格开关、渲染器、轨道控制、场景环境、相机、对象变换。
 * 注意：不能调用 saveSceneEdit()——核心的 saveSceneEdit 会 detach transformControls，
 * 轮询期间反复调用会导致"选中后自动取消"（gizmo 闪烁）。直接从场景对象轻量读取。 */
function getConfigSnapshot() {
  try {
    const te = threeEditor
    // 对象变换（mesh/light）：名称|可见|位置|缩放（顺序稳定 = scene 遍历序）
    const parts = []
    te.scene.traverse((o) => {
      if (o.isHelper || o.isCamera || o.isTransformControls || !o.name) return
      if (!o.isMesh && !o.isLight) return
      parts.push(`${o.name}|${o.visible ? 1 : 0}|${o.position.x.toFixed(3)},${o.position.y.toFixed(3)},${o.position.z.toFixed(3)}|${o.scale.x.toFixed(3)},${o.scale.y.toFixed(3)},${o.scale.z.toFixed(3)}`)
    })
    // 相机 + 轨道目标（视角变化需回写）
    const cam = te.camera
    const orbit = te.controls
    let camState = ''
    if (cam && orbit) {
      camState = `${cam.position.x.toFixed(2)},${cam.position.y.toFixed(2)},${cam.position.z.toFixed(2)}|${orbit.target.x.toFixed(2)},${orbit.target.y.toFixed(2)},${orbit.target.z.toFixed(2)}`
    }
    // 辅助线开关（AxesHelper/GridHelper 可见性）
    const axes = te.scene.getObjectByName('AxesHelper')
    const grid = te.scene.getObjectByName('GridHelper')
    return JSON.stringify({
      helpers: `${axes ? axes.visible : ''}|${grid ? grid.visible : ''}`,
      camera: camState,
      objects: parts.join(';'),
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
  // 核心 saveSceneEdit 会 detach transformControls（保存时清理），导致用户选中被取消；
  // 包装保存函数：保存后恢复选中对象（对象仍在场景中时），保证回写/序列化不打断编辑
  const tc = editor.transformControls
  if (tc && typeof editor.saveSceneEdit === 'function') {
    const origSave = editor.saveSceneEdit.bind(editor)
    editor.saveSceneEdit = (...args) => {
      const prevObject = tc.object
      // 保存前换回原始几何（圆角盒/形变球是渲染增强，JSON 必须保持 Box/Sphere 规范类型，否则 viewer 无法重建丢网格）
      const swapped = []
      editor.scene.traverse((o) => {
        if (o.userData && o.userData.origGeometry) {
          swapped.push([o, o.geometry])
          o.geometry = o.userData.origGeometry
        }
      })
      const result = origSave(...args)
      for (const [o, g] of swapped) o.geometry = g
      if (tc.object !== prevObject && prevObject && prevObject.parent) {
        try { tc.attach(prevObject) } catch (e) {}
      }
      return result
    }
  }
  if (pendingScene && appliedVersion !== pendingScene.version && toState(pendingScene.sceneDocument)) {
    const state = normalizeSceneState(toState(pendingScene.sceneDocument))
    threeEditor.resetEditorStorage(state)
    fixSceneLights(threeEditor)
    fixSceneMaterials(threeEditor)
    roundSceneBoxes(threeEditor)
    fixSceneOrganic(threeEditor)
    fixRendererQuality(threeEditor, state)
    applySceneEnvironment(threeEditor, state)
    scheduleFrameScene()
    appliedVersion = pendingScene.version
  }
  post('rup:ready', { canUndo: false, canRedo: false })
  startSceneWatch()
}
