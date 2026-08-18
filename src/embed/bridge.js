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
// 共享渲染核心（与页面渲染器 scene-3d viewer 同一渲染源，见 render-core.js 头注释）：
// 纹理系统/世界尺度 UV/几何与材质构建/有机形变/阴影调优 全部在此，双端行为永远一致
import {
  SURFACE_UNIT,
  ROUND_BOX_MAX,
  getSurfaceTextures,
  inferSurfaceKind,
  inferOrganicKind,
  nameJitter,
  applyBoxWorldUV,
  applyPlaneWorldUV,
  applyCylinderWorldUV,
  isSlimColumn,
  displaceOrganicGeometry,
} from './render-core.js'

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
let strippedTubeGeometries = [] // 加载时剥离的 TubeGeometry 原始条目（three-edit-cores 无法解析，保存时合并回保持无损）

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
 * 颜色归一化（加载侧）：设计器回写（saveSceneEdit）的材质/灯光颜色可能是 THREE.Color 对象
 * （{isColor:true, r, g, b}，分量 0-1），three-edit-cores 解析时按数字处理，对象会导致颜色变黑。
 * 统一转为十进制数字（0xRRGGBB）。
 * 注意：three r152+ 启用 ColorManagement 后 THREE.Color 内部存储的是**线性空间**分量——
 * 直接把线性分量 ×255 当 sRGB 十进制，会让颜色每次保存/加载循环累积变暗（0.91→0.82→0.65…）。
 * 正确做法：new THREE.Color(线性分量) → getHex()（内部做线性→sRGB 转换），与原始 sRGB 十进制一致。
 */
function normalizeColorValue(value) {
  if (value && typeof value === 'object' && typeof value.r === 'number' && typeof value.g === 'number' && typeof value.b === 'number') {
    try {
      return new THREE.Color(value.r, value.g, value.b).getHex()
    } catch (e) {
      const r = Math.max(0, Math.min(1, value.r))
      const g = Math.max(0, Math.min(1, value.g))
      const b = Math.max(0, Math.min(1, value.b))
      return (Math.round(r * 255) << 16) + (Math.round(g * 255) << 8) + Math.round(b * 255)
    }
  }
  return value
}

/** 序列化后的场景 state 颜色归一化（保存侧）：three-edit-cores 输出 isColor 线性对象 →
 * 转回 sRGB 十进制（与页面 viewer 的 setHex 语义一致），防止线性分量泄漏进 JSON、
 * 以及加载侧把线性值当 sRGB 导致的逐次累积变暗。十进制数字保持不变（幂等）。 */
function normalizeSerializedColors(state) {
  if (!state || typeof state !== 'object') return state
  try {
    const fix = (v) => (v && typeof v === 'object' && typeof v.r === 'number' && typeof v.g === 'number' && typeof v.b === 'number'
      ? new THREE.Color(v.r, v.g, v.b).getHex()
      : v)
    for (const list of [state.innerCores, state.lightCores]) {
      if (!Array.isArray(list)) continue
      for (const item of list) {
        if (!item || typeof item !== 'object') continue
        if (item.material && typeof item.material === 'object') {
          if (item.material.color !== undefined) item.material.color = fix(item.material.color)
          if (item.material.emissive !== undefined) item.material.emissive = fix(item.material.emissive)
        }
        if (item.color !== undefined) item.color = fix(item.color)
      }
    }
  } catch (e) {}
  return state
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
    // 防御：three-edit-cores 的 innerCores 用 new THREE[type](...Object.values(parameters)) 创建，
    // TubeGeometry 的 path 必须是 Curve 实例，纯 JSON 数组无法解析（抛 "path.computeFrenetFrames is not a function"），
    // 且其 setStorage forEach 无 try/catch——单个条目抛错会中断后续全部对象创建（楼栋等主体不显示）。
    // 剥离该类条目：设计器不渲染曲线对象（页面渲染由 scene-3d viewer 自行支持，不受影响），其余对象正常加载；
    // 原始条目暂存，wrapScene 保存时合并回（无损）。
    if (key === 'innerCores') {
      const dropped = []
      for (let i = list.length - 1; i >= 0; i--) {
        const it = list[i]
        if (it && it.geometry && it.geometry.type === 'TubeGeometry') {
          dropped.push(it)
          list.splice(i, 1)
        }
      }
      if (dropped.length) {
        strippedTubeGeometries = dropped
        console.warn('[bridge] 剥离 three-edit-cores 不支持的 TubeGeometry 条目（设计器不显示，保存时保留）：', dropped.map((d) => d.name || 'TubeGeometry').join(', '))
      } else {
        strippedTubeGeometries = []
      }
    }
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
      // 低分段默认（与 viewer 一致，消"塑料圆滑感"，现代游戏低模的可见棱面质感）：
      // three-edit-cores 用 new THREE[type](...Object.values(parameters)) 创建，缺省分段是 32/48 圆滑面；
      // 此处按键序追加默认分段（JSON 显式写过的保留），使圆柱/球/锥/环呈现低模棱面。
      if (key === 'innerCores' && item.geometry && item.geometry.parameters) {
        const gp = item.geometry.parameters
        const gt = item.geometry.type
        if (gt === 'CylinderGeometry' && gp.radialSegments === undefined) gp.radialSegments = 16
        else if (gt === 'ConeGeometry' && gp.radialSegments === undefined) gp.radialSegments = 16
        else if (gt === 'SphereGeometry') {
          if (gp.widthSegments === undefined) gp.widthSegments = 24
          if (gp.heightSegments === undefined) gp.heightSegments = 16
        } else if (gt === 'TorusGeometry') {
          if (gp.radialSegments === undefined) gp.radialSegments = 12
          if (gp.tubularSegments === undefined) gp.tubularSegments = 24
        } else if (gt === 'CapsuleGeometry') {
          if (gp.capSegments === undefined) gp.capSegments = 6
          if (gp.radialSegments === undefined) gp.radialSegments = 16
        }
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

/** 场景加载后遍历材质附加结构化程序化纹理（仅未带纹理的 Standard/Lambert/Phong，玻璃/发光跳过） */
function fixSceneMaterials(editor) {
  try {
    editor.scene.traverse((o) => {
      if (!o.isMesh || Array.isArray(o.material)) return
      const mat = o.material
      if (mat.type !== 'MeshStandardMaterial' && mat.type !== 'MeshLambertMaterial' && mat.type !== 'MeshPhongMaterial') return
      if (mat.map || mat.alphaMap) return
      // inferSurfaceKind 期望纯字段 JSON，但这里 mat 是 three.js Material 实例
      // （emissive 是 Color 对象非 0），必须先扁平化为纯字段，否则会被误判为发光材质跳过纹理
      const matState = {
        type: mat.type,
        transparent: !!mat.transparent,
        emissive: mat.emissive && typeof mat.emissive === 'object' && typeof mat.emissive.getHex === 'function' ? mat.emissive.getHex() : mat.emissive
      }
      const kind = inferSurfaceKind(o.name, matState)
      const tex = kind ? getSurfaceTextures(kind) : null
      // 细长柱体（灯柱/树干/旗杆/栏杆）：纹理在细柱上压缩成横条纹（条纹材质根因），且真实细柱是纯色漆面——跳过纹理
      const geoState = o.geometry ? { type: o.geometry.type, parameters: o.geometry.parameters } : null
      if (kind && tex && !isSlimColumn(geoState)) {
        mat.map = tex.map
        mat.bumpMap = tex.map
        mat.bumpScale = 0.025
        if (tex.normalMap) mat.normalMap = tex.normalMap
        if (tex.roughnessMap) {
          mat.roughnessMap = tex.roughnessMap
          mat.roughness = 1
          if (kind === 'metal') {
            // 金属表面：保留/提升金属度（拉丝与粗糙度变化由贴图表达），增强环境反射（与 viewer 一致）
            mat.metalness = Math.max(typeof mat.metalness === 'number' ? mat.metalness : 0.6, 0.5)
            mat.envMapIntensity = 1.4
          } else {
            mat.metalness = Math.min(typeof mat.metalness === 'number' ? mat.metalness : 0, 0.1)
            mat.envMapIntensity = 0.9
          }
        } else if (kind === 'metal') {
          mat.envMapIntensity = 1.25
        }
        // 楼体/草地同名阵列颜色微抖动 ±4%（暂存原始色：保存时恢复，防止乘算颜色被序列化导致每次保存循环累积加深）
        if (kind === 'facade' || kind === 'grass') {
          if (mat.color) {
            if (o.userData.origColor === undefined) o.userData.origColor = mat.color.getHex()
            mat.color.multiplyScalar(1 + (nameJitter(o.name) - 0.5) * 0.08)
          }
        }
        // 世界尺度 UV：Box/Plane 按真实米数重写（窗/缝/波纹真实尺寸、六面密度一致；圆角化的小 Box 跳过）
        if (o.geometry && o.geometry.type === 'BoxGeometry') {
          const p = o.geometry.parameters || {}
          applyBoxWorldUV(o.geometry, p.width ?? 1, p.height ?? 1, p.depth ?? 1, SURFACE_UNIT[kind])
        } else if (o.geometry && o.geometry.type === 'PlaneGeometry') {
          const p = o.geometry.parameters || {}
          applyPlaneWorldUV(o.geometry, p.width ?? 1, p.height ?? 1, SURFACE_UNIT[kind])
        } else if (o.geometry && (o.geometry.type === 'CylinderGeometry' || o.geometry.type === 'ConeGeometry')) {
          applyCylinderWorldUV(o.geometry, SURFACE_UNIT[kind])
        }
        // facade 楼体顶/底去窗（设计器侧暂时省略材质数组：three-edit-cores 渲染管线对材质数组
        // 支持不完整，设置后 Mesh 不渲染。仅应用基础纹理，俯视的"楼顶有窗"留待 viewer 端处理；
        // viewer 端保留材质数组逻辑（双端渲染特性对齐暂未完成，先保设计器可看）
        // 设计器材质数组被验证会让 Mesh 不可见（截图渲染区空白），故跳过此分支
        if (false && kind === 'facade' && o.geometry && o.geometry.type === 'BoxGeometry') {
          const capMat = mat.clone()
          capMat.map = null
          capMat.bumpMap = null
          capMat.roughnessMap = null
          capMat.normalMap = null
          capMat.roughness = 0.9
          capMat.metalness = 0
          if (capMat.color) capMat.color.multiplyScalar(0.9)
          capMat.needsUpdate = true
          o.userData.origMaterial = mat
          // BoxGeometry 材质组序：px, nx, py, ny, pz, nz——±y（顶/底）用无纹理材质
          o.material = [mat, mat, capMat, capMat, mat, mat]
        }
        mat.needsUpdate = true
      }
    })
  } catch (e) {}
}

/** 对象阴影（与 viewer 一致，写实阴影四要素之物体侧）：全部对象投影 + 接收，云不投影避免糊满地面 */
function fixSceneShadows(editor) {
  try {
    editor.scene.traverse((o) => {
      if (o.isMesh) {
        o.castShadow = !/云|cloud/i.test(o.name || '')
        o.receiveShadow = true
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
      // 与 viewer 一致（ROUND_BOX_MAX）：仅"小且近立方体"的 Box 圆角——大 Box（楼体/墙体/地面）必须
      // 保持直角 BoxGeometry，世界尺度 UV 才能精确映射纹理分格；大 Box 圆角会丢 UV，楼体窗阵列只剩 1 层
      if (maxSide > ROUND_BOX_MAX || maxSide / minSide > 3) return
      const g = new RoundedBoxGeometry(w, h, d, 3, minSide * 0.07)
      o.userData.origGeometry = o.geometry // 保留原始 Box，saveSceneEdit 前换回（防止增强类型泄漏到 JSON）
      o.geometry.dispose()
      o.geometry = g
    })
  } catch (e) {}
}

/** 有机形变（与 viewer 一致）：树冠/叶/灌木/云的球体顶点噪声位移为不规则有机轮廓（写实感，双端同源） */
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

/** 基底层排除（与 scene-3d viewer 一致）：地面/道路/树/路灯等大面积铺底或配景不参与取景包围盒——
 * 否则巨大地面会把包围盒撑爆、取景距离极远，模型在视口中渺小（"显示不全"） */
const FRAME_EXCLUDE_RE = /云|cloud|地面|地坪|地板|场地|道路|公路|路面|人行道|停车场|主干道|主路|支路|车道|标线|中线|黄线|斑马|绿化带|绿带|围栏|护栏|围墙|树|路灯|灯柱|车辆|汽车/i

/** 阴影质量调优（与 viewer 一致）：castShadow 的平行光/聚光灯——2048 贴图、normalBias 防阴影痤疮、
 * shadow camera 范围按主体包围盒自适应（默认 ±5 的阴影相机对园区场景会把阴影裁成碎块） */
function tuneShadowLights(editor, box) {
  try {
    const size = box.getSize(new THREE.Vector3())
    const radius = Math.max(size.x, size.z, 4) * 0.75 + 2
    editor.scene.traverse((o) => {
      if ((o.isDirectionalLight || o.isSpotLight) && o.castShadow && o.shadow) {
        o.shadow.mapSize.set(2048, 2048)
        o.shadow.normalBias = 0.03
        o.shadow.bias = -0.0001
        o.shadow.radius = 4
        const cam = o.shadow.camera
        if (cam) {
          cam.left = -radius; cam.right = radius
          cam.top = radius; cam.bottom = -radius
          cam.near = 0.5
          cam.far = radius * 6
          cam.updateProjectionMatrix()
        }
      }
    })
  } catch (e) {}
}

/** 场景自动取景：相机对准场景包围盒中心（与 scene-3d viewer 同公式，两侧初始视角一致）。
 * 基底层不参与包围盒——取景只框主体群。 */
function centerAndFrameScene(editor) {
  try {
    const scene = editor.scene
    const camera = editor.camera
    if (!scene || !camera) return
    const box = new THREE.Box3()
    let has = false
    scene.traverse((o) => {
      if (o.isMesh && o.visible && !o.isHelper && o.name && !FRAME_EXCLUDE_RE.test(o.name)) {
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
    // 取景距离按水平视场自适应（宽屏水平视野大）：对角机位下内容水平投影 ≈ (size.x+size.z)/√2，
    // 内容占水平视场 ~85%——与 viewer 保持一致，模型在视口中更大更饱满，无需手动放大
    const fovV = (camera.fov * Math.PI) / 360
    const fovH = 2 * Math.atan(Math.tan(fovV) * (camera.aspect || 1.6))
    const spanH = (size.x + size.z) / Math.SQRT2
    const d = Math.max((spanH / 2) / Math.tan(fovH / 2) * 1.18, size.x * 0.4, size.z * 0.4, 2.5)
    // 视角按内容高宽比自适应（与 viewer 一致）：内容越高视角越平、越平视角越陡；下限 0.55 保证顶边射线落地
    const flat = Math.max(size.x, size.z, 1)
    const yFactor = Math.min(0.85, Math.max(0.55, 0.55 + (size.y / flat) * 0.4))
    camera.position.set(center.x + d * 0.72, center.y + d * yFactor, center.z + d * 0.72)
    if (editor.controls) {
      editor.controls.target.set(center.x, center.y, center.z)
      editor.controls.update()
    }
    camera.lookAt(center.x, center.y, center.z)
    tuneShadowLights(editor, box)
    return camera.position.clone()
  } catch (e) {
    return null
  }
}

/** 渲染器质量：ACES 电影色调映射（写实色彩）+ 柔和阴影（与 scene-3d viewer 一致） */
function fixRendererQuality(editor, state) {
  try {
    const r = editor.renderer
    if (!r) return
    const wg = (state && state.webglRenderer) || {}
    const tm = typeof wg.toneMapping === 'number' ? wg.toneMapping : 0
    if (tm !== 0) {
      r.toneMapping = 4 // ACESFilmicToneMapping
      r.toneMappingExposure = typeof wg.toneMappingExposure === 'number' ? wg.toneMappingExposure : 1
    }
    const shadows = !!(wg.shadowMap && wg.shadowMap.enabled)
    if (shadows) {
      r.shadowMap.enabled = true
      r.shadowMap.type = 2 // PCFSoftShadowMap
    }
  } catch (e) {}
}

/** 场景增强链（全部幂等）：灯光/材质纹理/阴影/圆角/有机形变。
 * resetEditorStorage 通过响应式 store 创建场景对象，Mesh 在渲染循环中才真正就绪——
 * applyScene 里同步调用可能遍历不到对象（材质/圆角全部失效），
 * 必须由 scheduleFrameScene 在对象就绪后补跑一次。 */
function applyEnhancements(editor) {
  if (!editor) return
  fixSceneLights(editor)
  fixSceneMaterials(editor)
  fixSceneShadows(editor)
  roundSceneBoxes(editor)
  fixSceneOrganic(editor)
}

function applyScene(doc) {
  pendingScene = { sceneDocument: doc, version: (pendingScene?.version || 0) + 1 }
  if (threeEditor && toState(doc)) {
    const state = normalizeSceneState(toState(doc))
    threeEditor.resetEditorStorage(state)
    applyEnhancements(threeEditor)
    fixRendererQuality(threeEditor, state)
    applySceneEnvironment(threeEditor, state)
    // resetEditorStorage 异步创建场景对象，取景与增强需延迟到对象就绪后执行
    scheduleFrameScene()
    appliedVersion = pendingScene.version
  }
}

let frameSceneTimer = null
let framedCameraPos = null // 首次取景记录的相机位置（二次兜底前校验用户未动相机）
/** 延迟取景（等 resetEditorStorage 的场景对象创建完成）并防抖；800ms 后二次兜底重框——
 * 大场景（80+ 对象）异步构建可能超过单次延迟，首次取景只框到局部（"显示不全"）。
 * 仅当用户未动过相机（位置仍等于首次取景位置）才重框，不覆盖用户操作。 */
function countMeshes(editor) {
  let n = 0
  try {
    editor.scene.traverse((o) => { if (o.isMesh) n++ })
  } catch (e) {}
  return n
}

function scheduleFrameScene(retry = 0) {
  if (frameSceneTimer) clearTimeout(frameSceneTimer)
  frameSceneTimer = setTimeout(() => {
    frameSceneTimer = null
    if (!threeEditor) return
    // 对象就绪后补跑增强（resetEditorStorage 异步创建，applyScene 首轮同步调用可能遍历不到对象）
    applyEnhancements(threeEditor)
    // 大场景对象异步创建可能超过 200ms：无 Mesh 时延后重试，直到就绪（上限 5 次）
    if (countMeshes(threeEditor) === 0 && retry < 5 && pendingScene) {
      scheduleFrameScene(retry + 1)
      return
    }
    framedCameraPos = centerAndFrameScene(threeEditor)
    // 启动嵌入模式专属渲染循环：three-edit-cores 内置循环在嵌入环境下未正确初始化相机方向
    // （camera.lookAt 未被触发），每帧 render 输出空白。手动循环覆盖：每帧 controls.update
    // 让相机看向 target，再 renderer.render 输出到 canvas
    startEmbedRenderLoop()
    setTimeout(() => {
      if (!threeEditor || !threeEditor.camera) return
      const p = threeEditor.camera.position
      const moved = framedCameraPos && (
        Math.abs(p.x - framedCameraPos.x) > 0.01 ||
        Math.abs(p.y - framedCameraPos.y) > 0.01 ||
        Math.abs(p.z - framedCameraPos.z) > 0.01
      )
      if (!framedCameraPos || (!moved && countMeshes(threeEditor) > 0)) {
        centerAndFrameScene(threeEditor)
      }
    }, 800)
  }, 200)
}

/** 嵌入模式渲染循环：每帧 controls.update + camera.lookAt(target) + renderer.render，
 * 解决 three-edit-cores 内置循环在嵌入模式下未触发相机朝向的渲染空白问题。
 * destroySceneRender 同步取消。 */
let embedRenderRaf = null
function startEmbedRenderLoop() {
  if (embedRenderRaf) return
  if (!IS_EMBED) return
  const tick = () => {
    embedRenderRaf = requestAnimationFrame(tick)
    if (!threeEditor || !threeEditor.renderer || !threeEditor.scene || !threeEditor.camera) return
    try {
      if (threeEditor.controls) threeEditor.controls.update()
      const t = threeEditor.controls && threeEditor.controls.target
      if (t) threeEditor.camera.lookAt(t.x, t.y, t.z)
      threeEditor.renderer.render(threeEditor.scene, threeEditor.camera)
    } catch (e) {}
  }
  embedRenderRaf = requestAnimationFrame(tick)
}
function stopEmbedRenderLoop() {
  if (embedRenderRaf) cancelAnimationFrame(embedRenderRaf)
  embedRenderRaf = null
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
  const state = threeEditor.saveSceneEdit()
  // 合并回加载时剥离的 TubeGeometry 条目（设计器不支持但不丢弃，保持场景文档无损）
  if (strippedTubeGeometries.length) {
    try {
      if (!Array.isArray(state.innerCores)) state.innerCores = []
      state.innerCores.push(...strippedTubeGeometries)
    } catch (e) {}
  }
  // 颜色归一化（兜底：即使 saveSceneEdit 包装未生效，输出也保持 sRGB 十进制）
  normalizeSerializedColors(state)
  return { schemaVersion: '1.0', engine: 'three-edit-cores', state }
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
      // 保存前换回单材质（facade 顶/底去窗材质数组是渲染增强，JSON 必须保持单材质，否则核心序列化/页面重建异常）
      const matSwapped = []
      editor.scene.traverse((o) => {
        if (o.userData && o.userData.origMaterial) {
          matSwapped.push([o, o.material])
          o.material = o.userData.origMaterial
        }
      })
      // 保存前恢复原始颜色（微抖动是渲染增强：乘算颜色若被序列化，每次保存/加载循环都会累积加深/变亮）
      const colorSwapped = []
      editor.scene.traverse((o) => {
        const m = Array.isArray(o.material) ? o.material[0] : o.material
        if (o.userData && o.userData.origColor && m && m.color) {
          colorSwapped.push([m, m.color.getHex()])
          m.color.setHex(o.userData.origColor)
        }
      })
      const result = origSave(...args)
      for (const [o, g] of swapped) o.geometry = g
      for (const [o, m] of matSwapped) o.material = m
      for (const [m, hex] of colorSwapped) m.color.setHex(hex)
      // 序列化结果颜色归一化：isColor 线性对象 → sRGB 十进制（防止线性分量泄漏/累积变暗）
      normalizeSerializedColors(result)
      if (tc.object !== prevObject && prevObject && prevObject.parent) {
        try { tc.attach(prevObject) } catch (e) {}
      }
      return result
    }
  }
  if (pendingScene && appliedVersion !== pendingScene.version && toState(pendingScene.sceneDocument)) {
    const state = normalizeSceneState(toState(pendingScene.sceneDocument))
    threeEditor.resetEditorStorage(state)
    applyEnhancements(threeEditor)
    fixRendererQuality(threeEditor, state)
    applySceneEnvironment(threeEditor, state)
    scheduleFrameScene()
    appliedVersion = pendingScene.version
  }
  post('rup:ready', { canUndo: false, canRedo: false })
  startSceneWatch()
}
