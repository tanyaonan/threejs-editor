/**
 * 共享渲染核心（单一渲染源）
 *
 * viewer（scene-3d 页面渲染）与设计器（threejs-editor 嵌入桥）共用本模块——
 * 纹理系统 / 世界尺度 UV / 几何构建（低分段+圆角）/ 材质构建（PBR 附加）/
 * 有机形变 / 阴影调优 全部在此实现，双端行为永远一致，改动只维护一处。
 *
 * 写实策略（重构版）：
 * - 程序化纹理 = 多频率噪声分层（macro 大斑块 + mid 污渍 + micro 微颗粒）+ 结构图案
 * - 每张纹理配套生成 normalMap（亮度高度场 Sobel 梯度）与 roughnessMap（噪声驱动，
 *   打破"全表面同一粗糙度"的塑料感；facade 窗玻璃区域粗糙度更低反射天空光）
 * - 几何低分段（圆柱 16 面/球 24×16/环 24）——现代游戏低模的可见棱面质感
 * - 小/中 Box（≤2.5m 近立方体）圆角消直角塑料感；大 Box 保持直角保世界尺度 UV
 */
import * as THREE from 'three'
import { RoundedBoxGeometry } from 'three/examples/jsm/geometries/RoundedBoxGeometry.js'

/* ============================ 确定性噪声 ============================ */

/** 确定性 3D 值噪声：哈希格点 + 三线性插值 + 2 倍频叠加（同坐标恒同值，双端一致） */
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

/** 确定性 PRNG：同一种纹理每次生成结果一致 */
function makeRand(seed) {
  let s = seed || 7
  return () => { s = (s * 16807) % 2147483647; return s / 2147483647 }
}

/* ==================== 程序化纹理系统（多频率分层 + PBR 三通道） ==================== */

// 纹理分辨率 256：map/normal/roughness 三通道 × 9 种表面在首次加载时同步生成，
// 512² 会让设计器 iframe 主线程阻塞数秒（多频噪声 + Sobel 法线卷积），256 四倍提速、视觉无感。
const TEX_SIZE = 256

/** 每种表面纹理一张贴图对应的世界米数（facade=3m≈一层楼，brick/paver 面砖尺度更小） */
const SURFACE_UNIT = {
  facade: 3, factoryWall: 3, brick: 1.5, concrete: 3, asphalt: 3,
  paver: 1.5, roof: 3, grass: 2, metal: 2,
}

/**
 * 多频率噪声铺底（告别单层噪声的"2D 贴图感"）：
 * macro 大尺度斑块（0.55 权重）+ mid 污渍（0.3）+ micro 微颗粒（0.15），三频叠加。
 */
function fillNoise(ctx, size, rand, base, amp, seed = 7) {
  const img = ctx.createImageData(size, size)
  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      const i = (y * size + x) * 4
      const n1 = fbmNoise3(x / 64, y / 64, seed)
      const n2 = valueNoise3(x / 13, y / 13, seed + 31)
      const n3 = hashNoise3(x, y, seed + 17)
      const v = base + (n1 - 0.5) * amp * 0.55 + (n2 - 0.5) * amp * 0.3 + (n3 - 0.5) * amp * 0.15
      img.data[i] = v; img.data[i + 1] = v; img.data[i + 2] = v; img.data[i + 3] = 255
    }
  }
  ctx.putImageData(img, 0, 0)
}

/** 画一扇"窗"：暗玻璃垂直渐变（上亮下暗＝天空反射）+ 亮窗框厚边 + 中横竖梃 + 窗周 AO 暗环 */
function drawWindowPane(ctx, x, y, w, h, rand, litChance) {
  const lit = rand() < litChance
  const grad = ctx.createLinearGradient(0, y, 0, y + h)
  if (lit) {
    grad.addColorStop(0, 'rgb(250,240,212)')
    grad.addColorStop(1, 'rgb(222,206,168)')
  } else {
    // 未亮窗：顶部高亮 = 天空反射带（参考图幕墙玻璃顶部反光明显），向下渐暗
    grad.addColorStop(0, 'rgb(118,122,140)')
    grad.addColorStop(0.35, 'rgb(96,100,112)')
    grad.addColorStop(1, 'rgb(42,46,58)')
  }
  ctx.fillStyle = grad
  ctx.fillRect(x, y, w, h)
  ctx.fillStyle = 'rgb(198,198,198)'
  ctx.fillRect(x - 1, y - 1, w + 2, 2)
  ctx.fillRect(x - 1, y + h - 1, w + 2, 2)
  ctx.fillRect(x - 1, y, 2, h)
  ctx.fillRect(x + w - 1, y, 2, h)
  ctx.fillStyle = 'rgb(176,176,176)'
  ctx.fillRect(x + w / 2 - 1, y, 2, h)
  ctx.fillRect(x, y + h / 2 - 1, w, 2)
  // 窗周 AO 暗环
  ctx.fillStyle = 'rgba(0,0,0,0.14)'
  ctx.fillRect(x - 3, y - 3, w + 6, 2)
  ctx.fillRect(x - 3, y + h + 1, w + 6, 2)
  ctx.fillRect(x - 3, y - 1, 2, h + 4)
  ctx.fillRect(x + w + 1, y - 1, 2, h + 4)
  return lit
}

/** facade 楼体幕墙：一层楼一格（层线 + 两扇窗 + 窗台线） */
function drawFacade(ctx, size, rand) {
  fillNoise(ctx, size, rand, 234, 10)
  ctx.fillStyle = 'rgb(192,192,192)'
  ctx.fillRect(0, 0, size, 6)
  // 楼板线下方阴影线（立体感）
  ctx.fillStyle = 'rgba(0,0,0,0.10)'
  ctx.fillRect(0, 6, size, 3)
  const wy = Math.round((1 - 0.86) * size), wh = Math.round((0.86 - 0.42) * size)
  const winW = Math.round(0.34 * size)
  drawWindowPane(ctx, Math.round(0.09 * size), wy, winW, wh, rand, 0.1)
  drawWindowPane(ctx, Math.round(0.57 * size), wy, winW, wh, rand, 0.1)
  ctx.fillStyle = 'rgb(205,205,205)'
  ctx.fillRect(0, wy + wh, size, 3)
}

/** factoryWall 厂房彩钢板：12 条竖向波纹（明暗渐变）+ 横向檩条线 */
function drawFactoryWall(ctx, size, rand) {
  fillNoise(ctx, size, rand, 233, 8)
  const ribs = 12, ribW = size / ribs
  for (let i = 0; i < ribs; i++) {
    const grad = ctx.createLinearGradient(i * ribW, 0, (i + 1) * ribW, 0)
    grad.addColorStop(0, 'rgba(255,255,255,0.55)')
    grad.addColorStop(0.5, 'rgba(0,0,0,0.06)')
    grad.addColorStop(1, 'rgba(0,0,0,0.22)')
    ctx.fillStyle = grad
    ctx.fillRect(i * ribW, 0, ribW, size)
  }
  ctx.fillStyle = 'rgba(0,0,0,0.14)'
  ctx.fillRect(0, 0, size, 5)
  ctx.fillRect(0, size / 2, size, 5)
}

/** brick 砖墙：4 行 × 3 列错缝砖（0.5×0.375m），红褐/黄褐砖 + 浅缝 + 气孔 */
function drawBrick(ctx, size, rand) {
  ctx.fillStyle = 'rgb(168,150,135)'
  ctx.fillRect(0, 0, size, size)
  const rows = 4, rowH = size / rows, cols = 3, colW = size / cols
  for (let r = 0; r < rows; r++) {
    const offset = r % 2 === 1 ? colW / 2 : 0
    for (let c = -1; c <= cols; c++) {
      const x = c * colW + offset + 2, y = r * rowH + 2
      const w = colW - 4, h = rowH - 4
      // 红褐到黄褐随机：R 主导，G 中等，B 压低
      const br = Math.round(185 + rand() * 30)
      const bg = Math.round(110 + rand() * 35)
      const bb = Math.round(70 + rand() * 20)
      ctx.fillStyle = `rgb(${br},${bg},${bb})`
      ctx.fillRect(x, y, w, h)
      const holes = rand() < 0.6 ? 1 : 2
      for (let k = 0; k < holes; k++) {
        ctx.fillStyle = 'rgba(0,0,0,0.18)'
        ctx.fillRect(x + rand() * (w - 4), y + rand() * (h - 4), 2, 2)
      }
    }
  }
}

/** concrete 混凝土：颗粒噪声 + 十字诱导缝 + 云状风化渍 */
function drawConcrete(ctx, size, rand) {
  fillNoise(ctx, size, rand, 208, 20)
  for (let i = 0; i < 4; i++) {
    const cx = rand() * size, cy = rand() * size, r = 60 + rand() * 90
    const grad = ctx.createRadialGradient(cx, cy, 0, cx, cy, r)
    grad.addColorStop(0, 'rgba(0,0,0,0.10)')
    grad.addColorStop(1, 'rgba(0,0,0,0)')
    ctx.fillStyle = grad
    ctx.fillRect(cx - r, cy - r, r * 2, r * 2)
  }
  ctx.fillStyle = 'rgb(168,168,168)'
  ctx.fillRect(0, 0, size, 3)
  ctx.fillRect(0, 0, 3, size)
}

/** asphalt 沥青：细颗粒 + 两条车辙压痕带（沿路长方向） */
function drawAsphalt(ctx, size, rand) {
  fillNoise(ctx, size, rand, 156, 34)
  for (let i = 0; i < 1400; i++) {
    const x = rand() * size, y = rand() * size
    ctx.fillStyle = rand() < 0.5 ? 'rgba(255,255,255,0.20)' : 'rgba(0,0,0,0.25)'
    ctx.fillRect(x, y, 1.5, 1.5)
  }
  for (const u of [0.3, 0.7]) {
    const x = u * size, w = size * 0.16
    const grad = ctx.createLinearGradient(x - w / 2, 0, x + w / 2, 0)
    grad.addColorStop(0, 'rgba(0,0,0,0)')
    grad.addColorStop(0.5, 'rgba(0,0,0,0.10)')
    grad.addColorStop(1, 'rgba(0,0,0,0)')
    ctx.fillStyle = grad
    ctx.fillRect(x - w / 2, 0, w, size)
  }
}

/** paver 铺装砖：4×4 分格方砖（错半格）+ 浅缝 */
function drawPaver(ctx, size, rand) {
  fillNoise(ctx, size, rand, 212, 10)
  ctx.fillStyle = 'rgb(176,174,172)'
  const n = 4, cell = size / n
  for (let r = 0; r <= n; r++) ctx.fillRect(0, r * cell - 1.5, size, 3)
  for (let r = 0; r < n; r++) {
    const offset = r % 2 === 1 ? cell / 2 : 0
    for (let c = 0; c <= n; c++) ctx.fillRect(c * cell + offset - 1.5, r * cell, 3, cell)
  }
}

/** roof 屋面：8 条竖向排水细纹 + 分缝 + 颗粒 */
function drawRoof(ctx, size, rand) {
  fillNoise(ctx, size, rand, 200, 14)
  const ribs = 8, ribW = size / ribs
  for (let i = 0; i < ribs; i++) {
    const grad = ctx.createLinearGradient(i * ribW, 0, (i + 1) * ribW, 0)
    grad.addColorStop(0, 'rgba(255,255,255,0.30)')
    grad.addColorStop(1, 'rgba(0,0,0,0.10)')
    ctx.fillStyle = grad
    ctx.fillRect(i * ribW, 0, ribW, size)
  }
  ctx.fillStyle = 'rgb(170,170,170)'
  ctx.fillRect(0, 0, size, 3)
  ctx.fillRect(0, 0, 3, size)
}

/** grass 草地：带色相噪声的黄绿色草地（fbm 云斑 + 草叶亮/暗点） */
function drawGrass(ctx, size) {
  const img = ctx.createImageData(size, size)
  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      const i = (y * size + x) * 4
      const n = fbmNoise3(x / 96, y / 96, 7.3)
      const r2 = hashNoise3(x | 0, y | 0, 13)
      // 中绿偏黄基调（参考 aesthetics #5C8A3C 色系），再叠加云斑与草叶亮/暗点
      const spot = r2 > 0.985 ? 20 : r2 < 0.012 ? -25 : 0
      const cloud = (n - 0.5) * 30
      img.data[i] = Math.min(255, Math.max(0, 142 + cloud + spot))     // R 偏黄
      img.data[i + 1] = Math.min(255, Math.max(0, 188 + cloud + spot)) // G 主导
      img.data[i + 2] = Math.min(255, Math.max(0, 72 + cloud + spot * 0.5)) // B 压低
      img.data[i + 3] = 255
    }
  }
  ctx.putImageData(img, 0, 0)
}

/** metal 金属：32 周期水平拉丝 + 微噪 */
function drawMetal(ctx, size, rand) {
  fillNoise(ctx, size, rand, 224, 8)
  const img = ctx.getImageData(0, 0, size, size)
  for (let y = 0; y < size; y++) {
    const sin = Math.sin((y / size) * Math.PI * 2 * 32) * 9
    for (let x = 0; x < size; x++) {
      const i = (y * size + x) * 4
      const v = img.data[i] + sin
      img.data[i] = v; img.data[i + 1] = v; img.data[i + 2] = v
    }
  }
  ctx.putImageData(img, 0, 0)
}

const SURFACE_DRAWERS = {
  facade: drawFacade,
  factoryWall: drawFactoryWall,
  brick: drawBrick,
  concrete: drawConcrete,
  asphalt: drawAsphalt,
  paver: drawPaver,
  roof: drawRoof,
  grass: drawGrass,
  metal: drawMetal,
}

/** 纹理缓存：kind → { map, normalMap, roughnessMap }（全局共享） */
const SURFACE_TEX_CACHE = {}

function makeCanvasTexture(canvas, srgb) {
  const tex = new THREE.CanvasTexture(canvas)
  tex.wrapS = tex.wrapT = THREE.RepeatWrapping
  tex.anisotropy = 8
  if (srgb) tex.colorSpace = THREE.SRGBColorSpace
  return tex
}

/** 从亮度高度场生成法线贴图（Sobel 梯度，r/g/b = 法线方向）——真实凹凸感的核心通道 */
function heightToNormal(canvas, strength = 1.6) {
  const size = canvas.width
  const data = canvas.getContext('2d').getImageData(0, 0, size, size).data
  const out = new Uint8ClampedArray(data.length)
  const lum = (x, y) => data[(((y + size) & (size - 1)) * size + ((x + size) & (size - 1))) * 4]
  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      const tl = lum(x - 1, y - 1), t = lum(x, y - 1), tr = lum(x + 1, y - 1)
      const l = lum(x - 1, y), r = lum(x + 1, y)
      const bl = lum(x - 1, y + 1), b = lum(x, y + 1), br = lum(x + 1, y + 1)
      const dx = (tr + 2 * r + br) - (tl + 2 * l + bl)
      const dy = (bl + 2 * b + br) - (tl + 2 * t + tr)
      const nx = -dx * strength, ny = -dy * strength
      const len = Math.sqrt(nx * nx + ny * ny + 1) || 1
      const o = (y * size + x) * 4
      out[o] = (nx / len * 0.5 + 0.5) * 255
      out[o + 1] = (ny / len * 0.5 + 0.5) * 255
      out[o + 2] = (1 / len * 0.5 + 0.5) * 255
      out[o + 3] = 255
    }
  }
  const nc = document.createElement('canvas')
  nc.width = nc.height = size
  nc.getContext('2d').putImageData(new ImageData(out, size, size), 0, 0)
  return nc
}

/** 噪声驱动粗糙度图：打破"全表面同一粗糙度"的塑料感（150 基准 ± 30 变化） */
function makeRoughnessCanvas(size, seed) {
  const rc = document.createElement('canvas')
  rc.width = rc.height = size
  const rctx = rc.getContext('2d')
  const rimg = rctx.createImageData(size, size)
  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      const i = (y * size + x) * 4
      const v = 150 + (valueNoise3(x / 40, y / 40, seed + 5) - 0.5) * 60
      rimg.data[i] = v; rimg.data[i + 1] = v; rimg.data[i + 2] = v; rimg.data[i + 3] = 255
    }
  }
  rctx.putImageData(rimg, 0, 0)
  return rc
}

/** 垂直受光渐变（三渲二经典手法，治"纸扎/平板"观感）：建筑类立面的 map 叠"顶部亮→底部暗"渐变，
 * 模拟真实受光 + 环境光遮蔽，楼体侧面立现从上到下的明暗体积层次（Box 侧面 v 沿 y，方向正确；
 * 顶/底面 v 水平，渐变轻微不影响）。地面/道路/草地不加（应均匀）。
 * 注意：concrete 同时用于立面（墙体/勒脚）与水平面（地面/场地/地坪）——纹理 kind 级缓存无法按对象名区分，
 * 若给 concrete 加渐变会让水平地面出现明暗分层（与设计器不一致，实测"地面显示不一致"），故 concrete 不加入。 */
const SHADED_KINDS = new Set(['facade', 'factoryWall', 'brick', 'metal', 'roof'])

function addVerticalShade(canvas, strength = 0.18) {
  const size = canvas.width
  const ctx = canvas.getContext('2d')
  const grad = ctx.createLinearGradient(0, 0, 0, size)
  grad.addColorStop(0, `rgba(255,255,255,${strength})`)
  grad.addColorStop(0.55, 'rgba(255,255,255,0)')
  grad.addColorStop(1, `rgba(0,0,0,${strength})`)
  ctx.fillStyle = grad
  ctx.fillRect(0, 0, size, size)
}

/** 获取（懒生成并缓存）某种表面的程序化纹理：map + normalMap + roughnessMap 三通道 */
function getSurfaceTextures(kind) {
  if (!SURFACE_DRAWERS[kind]) return null
  if (SURFACE_TEX_CACHE[kind]) return SURFACE_TEX_CACHE[kind]
  try {
    const size = TEX_SIZE
    const canvas = document.createElement('canvas')
    canvas.width = canvas.height = size
    const ctx = canvas.getContext('2d')
    const seedMap = { facade: 11, factoryWall: 23, brick: 37, concrete: 41, asphalt: 53, paver: 67, roof: 71, grass: 0, metal: 83 }
    SURFACE_DRAWERS[kind](ctx, size, makeRand(seedMap[kind]))
    // 垂直受光渐变（建筑类）：顶部亮→底部暗，体积感
    if (SHADED_KINDS.has(kind)) addVerticalShade(canvas, kind === 'facade' ? 0.14 : 0.16)
    const entry = {
      map: makeCanvasTexture(canvas, true),
      normalMap: null,
      roughnessMap: null,
    }
    // 法线贴图：从亮度高度场生成（写实凹凸，告别平面贴图感）
    // facade 窗玻璃区域单独做平：避免暗玻璃被算成凹陷法线
    if (kind === 'facade') {
      const flatCanvas = document.createElement('canvas')
      flatCanvas.width = flatCanvas.height = size
      flatCanvas.getContext('2d').drawImage(canvas, 0, 0)
      const fctx = flatCanvas.getContext('2d')
      const wy = Math.round((1 - 0.86) * size), wh = Math.round((0.86 - 0.42) * size)
      const winW = Math.round(0.34 * size)
      fctx.fillStyle = 'rgb(128,128,128)'
      fctx.fillRect(Math.round(0.09 * size), wy, winW, wh)
      fctx.fillRect(Math.round(0.57 * size), wy, winW, wh)
      try { entry.normalMap = makeCanvasTexture(heightToNormal(flatCanvas), false) } catch (e) {}
    } else {
      try { entry.normalMap = makeCanvasTexture(heightToNormal(canvas), false) } catch (e) {}
    }
    // roughnessMap：噪声驱动粗糙度变化；facade 窗玻璃区域覆盖为光滑（反射天空光）
    try {
      const rc = makeRoughnessCanvas(size, seedMap[kind])
      if (kind === 'facade') {
        const rctx = rc.getContext('2d')
        const wy = Math.round((1 - 0.86) * size), wh = Math.round((0.86 - 0.42) * size)
        const winW = Math.round(0.34 * size)
        rctx.fillStyle = 'rgb(18,18,18)' // 窗玻璃 roughness ~0.07（光滑反射）
        rctx.fillRect(Math.round(0.09 * size), wy, winW, wh)
        rctx.fillRect(Math.round(0.57 * size), wy, winW, wh)
      }
      entry.roughnessMap = makeCanvasTexture(rc, false)
    } catch (e) {}
    SURFACE_TEX_CACHE[kind] = entry
    return entry
  } catch (e) {
    return null
  }
}

/**
 * 按对象名与材质参数推断表面纹理类型（优先级从上到下，双端唯一）。
 * 玻璃/发光/透明/标线跳过；仅匹配"楼体部件"语义词（禁裸"楼"，防误贴窗户）。
 */
function inferSurfaceKind(name, materialState) {
  const n = String(name || '')
  const type = (materialState && materialState.type) || ''
  if (type === 'MeshBasicMaterial' || type === 'MeshNormalMaterial') return null
  if (materialState && (materialState.transparent || (materialState.emissive && materialState.emissive !== 0))) return null
  if (/玻璃|glass|透明|标线|黄线|斑马|文字|屏幕|铭牌|指示牌/.test(n)) return null
  if (/楼体|主体|大厦|塔楼|幕墙|写字楼|办公楼|宿舍|住宅|公寓|研发楼|楼层|综合楼/.test(n)) return 'facade'
  if (/厂房|车间|仓库|库房/.test(n)) return 'factoryWall'
  if (/砖/.test(n)) return 'brick'
  if (/屋面|屋顶|屋面板|屋脊|顶板/.test(n)) return 'roof'
  if (/道路|路面|公路|主干道|支路|车道/.test(n)) return 'asphalt'
  if (/人行道|广场|铺装|步道|地砖/.test(n)) return 'paver'
  if (/草坪|草地|绿化带|绿带|绿篱|树池|花坛/.test(n)) return 'grass'
  if (/地面|地坪|场地|停车场|路基|散水/.test(n)) return 'concrete'
  if (/金属|钢|铁|铝|铜|管|烟囱|栏杆|护栏|灯柱|爬梯|支架|支腿|罐|塔|桶|槽|柜|机组|风机|空调外机|设备/.test(n)) return 'metal'
  if (/墙|墙体|围墙|山墙|勒脚|女儿墙|围护|隔墙|隔断|挡墙|桥墩|柱|台阶|坡道/.test(n)) return 'concrete'
  return null
}

/** 名称确定性微抖动（0-1）：同名阵列对象颜色微差 ±4%，消"复制粘贴感" */
function nameJitter(name) {
  const n = String(name || '')
  let h = 0
  for (let i = 0; i < n.length; i++) h = (Math.imul(h, 31) + n.charCodeAt(i)) | 0
  return ((h >>> 0) % 1000) / 1000
}

/* ==================== 世界尺度 UV ==================== */

/** BoxGeometry 面序（three 源码）：px, nx, py, ny, pz, nz，每面 4 顶点；各面 uv 尺寸对应两轴 */
function applyBoxWorldUV(geometry, w, h, d, unit) {
  const uv = geometry.attributes.uv
  if (!uv) return
  const faces = [
    [d, h], [d, h],
    [w, d], [w, d],
    [w, h], [w, h],
  ]
  const vCount = uv.count
  const perFace = Math.floor(vCount / 6)
  for (let f = 0; f < 6; f++) {
    const [ru, rv] = faces[f]
    for (let i = 0; i < perFace; i++) {
      const idx = f * perFace + i
      if (idx >= vCount) break
      uv.setXY(idx, uv.getX(idx) * ru / unit, uv.getY(idx) * rv / unit)
    }
  }
  uv.needsUpdate = true
}

/** PlaneGeometry：整面 uv × (width/unit, height/unit) */
function applyPlaneWorldUV(geometry, w, h, unit) {
  const uv = geometry.attributes.uv
  if (!uv) return
  for (let i = 0; i < uv.count; i++) {
    uv.setXY(i, uv.getX(i) * w / unit, uv.getY(i) * h / unit)
  }
  uv.needsUpdate = true
}

/** Cylinder/ConeGeometry 世界尺度 UV：侧壁 uv（u=圆周 0-1 一圈，v=高度 0-1）按真实米数平铺——
 * 圆周平铺 (周长/unit) 次、高度平铺 (height/unit) 次。缺省单次平铺会把细密纹理（金属拉丝等）
 * 压缩成粗条纹——灯柱"条纹材质"根因（6m 灯柱上 32 条拉丝 = 每 18cm 一条粗横纹）。
 * 侧壁顶点数 = (radialSegments+1)×(heightSegments+1)，位于 uv 数组前部；caps 顶点保持原样。 */
function applyCylinderWorldUV(geometry, unit) {
  const uv = geometry.attributes.uv
  if (!uv) return
  const p = geometry.parameters || {}
  const radial = p.radialSegments ?? 16
  const heightSeg = p.heightSegments ?? 1
  const sideCount = (radial + 1) * (heightSeg + 1)
  // ConeGeometry 用 radius；CylinderGeometry 用 radiusTop/radiusBottom（平均周长 = π(rt+rb)）
  const circum = p.radius != null
    ? Math.PI * p.radius
    : Math.PI * ((p.radiusTop ?? 0) + (p.radiusBottom ?? 0))
  const height = p.height ?? 1
  const count = Math.min(sideCount, uv.count)
  for (let i = 0; i < count; i++) {
    uv.setXY(i, uv.getX(i) * circum / unit, uv.getY(i) * height / unit)
  }
  uv.needsUpdate = true
}

/** 细长柱体（灯柱/树干/旗杆/细管/栏杆）：金属拉丝等纹理在细柱上会被压缩成横条纹，
 * 且真实游戏/现实里细柱就是纯色漆面（无可见纹理）——跳过程序化纹理，保持纯色 + 用户 roughness/metalness。
 * 粗塔罐（化工塔/水塔）不在此列，保留金属质感。 */
function isSlimColumn(geometryState) {
  const gs = geometryState || {}
  if (gs.type !== 'CylinderGeometry' && gs.type !== 'ConeGeometry') return false
  const gp = gs.parameters || {}
  const r = Math.max(gp.radiusTop ?? 0, gp.radiusBottom ?? 0, gp.radius ?? 0)
  const h = gp.height ?? 0
  if (r <= 0.12) return true
  if (r > 0 && h / r >= 12) return true
  return false
}

/** 圆角阈值：≤ 2.5m 的近立方体 Box 圆角（消直角塑料感），大 Box 保持直角保世界 UV */
const ROUND_BOX_MAX = 2.5

/** 从 innerCores geometry 状态创建几何体（低分段 + 近立方体小 Box 圆角） */
function buildGeometry(geometryState) {
  const type = geometryState && geometryState.type
  const p = (geometryState && geometryState.parameters) || {}
  if (type === 'BoxGeometry') {
    const w = p.width ?? 1, h = p.height ?? 1, d = p.depth ?? 1
    const maxSide = Math.max(w, h, d)
    const minSide = Math.min(w, h, d)
    if (maxSide <= ROUND_BOX_MAX && maxSide / minSide <= 3) {
      try {
        return new RoundedBoxGeometry(w, h, d, 3, minSide * 0.07)
      } catch (e) { /* fallback 普通盒 */ }
    }
    return new THREE.BoxGeometry(w, h, d)
  }
  if (type === 'SphereGeometry') return new THREE.SphereGeometry(p.radius ?? 1, p.widthSegments ?? 24, p.heightSegments ?? 16)
  if (type === 'CylinderGeometry') return new THREE.CylinderGeometry(p.radiusTop ?? 1, p.radiusBottom ?? 1, p.height ?? 1, p.radialSegments ?? 16)
  if (type === 'ConeGeometry') return new THREE.ConeGeometry(p.radius ?? 1, p.height ?? 1, p.radialSegments ?? 16)
  if (type === 'TorusGeometry') return new THREE.TorusGeometry(p.radius ?? 1, p.tube ?? 0.4, p.radialSegments ?? 12, p.tubularSegments ?? 24)
  if (type === 'PlaneGeometry') return new THREE.PlaneGeometry(p.width ?? 1, p.height ?? 1)
  if (type === 'CapsuleGeometry') return new THREE.CapsuleGeometry(p.radius ?? 0.5, p.length ?? 1, p.capSegments ?? 6, p.radialSegments ?? 16)
  if (type === 'IcosahedronGeometry') return new THREE.IcosahedronGeometry(p.radius ?? 1, p.detail ?? 1)
  if (type === 'TetrahedronGeometry') return new THREE.TetrahedronGeometry(p.radius ?? 1, p.detail ?? 1)
  if (type === 'TubeGeometry') {
    const pts = Array.isArray(p.path) && p.path.length >= 2
      ? p.path.map((v) => Array.isArray(v) ? new THREE.Vector3(v[0] ?? 0, v[1] ?? 0, v[2] ?? 0) : new THREE.Vector3(v.x ?? 0, v.y ?? 0, v.z ?? 0))
      : [new THREE.Vector3(0, 0, 0), new THREE.Vector3(0, 1, 0)]
    const curve = new THREE.CatmullRomCurve3(pts)
    return new THREE.TubeGeometry(curve, Math.max(pts.length * 6, 12), p.radius ?? 0.1, 8, false)
  }
  return null
}

/* ==================== 材质构建（PBR 三通道附加） ==================== */

const MATERIAL_BUILDERS = {
  MeshStandardMaterial: THREE.MeshStandardMaterial,
  MeshPhysicalMaterial: THREE.MeshPhysicalMaterial,
  MeshBasicMaterial: THREE.MeshBasicMaterial,
  MeshLambertMaterial: THREE.MeshLambertMaterial,
  MeshPhongMaterial: THREE.MeshPhongMaterial,
  MeshNormalMaterial: THREE.MeshNormalMaterial,
}

/** 有机对象类型：树冠/树叶/灌木/绿化 → leaf；云 → cloud（排除"百叶"） */
function inferOrganicKind(name) {
  const n = String(name || '').toLowerCase()
  if (/云|cloud/.test(n)) return 'cloud'
  // 树冠|树叶|灌木|绿化|叶；"冠A/冠1"缩写也算（(?<!塔)排除"塔冠"，(?=[A-Za-z0-9])要求冠后跟编号）
  if (/树冠|树叶|灌木|绿化|(?<!百)叶|(?<!塔)冠(?=[A-Za-z0-9])/.test(n)) return 'leaf'
  return null
}

/** 有机形变：球体/多面体顶点沿法向噪声位移，leaf 面片化、cloud 低频平缓 */
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

/**
 * 从 innerCores material 状态创建材质（Standard/Physical/Lambert/Phong 自动附加合适贴图）。
 * @returns {THREE.Material}
 */
function createMaterialFromCore(materialState = {}, name = '', geometryState = null) {
  const color = materialState.color !== undefined && materialState.color !== null ? materialState.color : 0xffffff
  const options = { color }
  if (materialState.roughness !== undefined) options.roughness = materialState.roughness
  if (materialState.metalness !== undefined) options.metalness = materialState.metalness
  if (materialState.transparent !== undefined) options.transparent = materialState.transparent
  if (materialState.opacity !== undefined) options.opacity = materialState.opacity
  if (materialState.wireframe !== undefined) options.wireframe = materialState.wireframe
  if (materialState.emissive !== undefined && materialState.emissive !== null) {
    options.emissive = materialState.emissive
    if (materialState.emissiveIntensity !== undefined) options.emissiveIntensity = materialState.emissiveIntensity
  }
  if (materialState.side !== undefined) {
    options.side = materialState.side === 'DoubleSide' ? THREE.DoubleSide : materialState.side === 'BackSide' ? THREE.BackSide : THREE.FrontSide
  }
  // MeshPhysicalMaterial 专属参数（玻璃/车漆等）
  if (materialState.transmission !== undefined) options.transmission = materialState.transmission
  if (materialState.ior !== undefined) options.ior = materialState.ior
  if (materialState.thickness !== undefined) options.thickness = materialState.thickness
  if (materialState.clearcoat !== undefined) options.clearcoat = materialState.clearcoat
  if (materialState.clearcoatRoughness !== undefined) options.clearcoatRoughness = materialState.clearcoatRoughness
  if (materialState.attenuationColor !== undefined) options.attenuationColor = materialState.attenuationColor
  if (materialState.attenuationDistance !== undefined) options.attenuationDistance = materialState.attenuationDistance

  const Ctor = MATERIAL_BUILDERS[materialState.type] || THREE.MeshStandardMaterial
  const material = new Ctor(options)

  // 程序化纹理附加：按对象名语义，玻璃/发光/透明/透射跳过；细长柱体跳过。
  // - Standard/Physical：map + normalMap + roughnessMap（PBR 三通道）
  // - Lambert：仅 map + bumpMap（不支持 normalMap/roughnessMap）
  // - Phong：map + bumpMap + normalMap（不支持 roughnessMap，用 shininess/specular）
  const isPBR = Ctor === THREE.MeshStandardMaterial || Ctor === THREE.MeshPhysicalMaterial
  const isLambert = Ctor === THREE.MeshLambertMaterial
  const isPhong = Ctor === THREE.MeshPhongMaterial
  if ((isPBR || isLambert || isPhong) && !isSlimColumn(geometryState)) {
    const kind = inferSurfaceKind(name, materialState)
    const tex = kind ? getSurfaceTextures(kind) : null
    if (kind && tex) {
      material.map = tex.map
      material.bumpMap = tex.map
      material.bumpScale = 0.025
      if (tex.normalMap && (isPBR || isPhong)) material.normalMap = tex.normalMap
      if (tex.roughnessMap && isPBR) {
        material.roughnessMap = tex.roughnessMap
        // Three.js 中 roughnessMap 绿色通道与 base roughness 相乘，不是覆盖。
        // 保留用户传入的 base roughness；未指定时按材质类型给合理默认值。
        const baseRoughness = typeof material.roughness === 'number' ? material.roughness : null
        if (kind === 'metal') {
          material.roughness = baseRoughness ?? 0.3
          material.metalness = Math.max(typeof material.metalness === 'number' ? material.metalness : 0.6, 0.5)
          material.envMapIntensity = 1.4
        } else {
          material.roughness = baseRoughness ?? 0.85
          material.metalness = Math.min(material.metalness ?? 0, 0.1)
          material.envMapIntensity = 1.25
        }
      } else if (kind === 'metal') {
        material.envMapIntensity = 1.25
      }
      // 楼体/草地同名阵列颜色微抖动 ±4%
      if (kind === 'facade' || kind === 'grass') {
        material.color.multiplyScalar(1 + (nameJitter(name) - 0.5) * 0.08)
      }
      // 叶簇面片化
      if (inferOrganicKind(name) === 'leaf') {
        material.flatShading = true
      }
      material.needsUpdate = true
    }
  }
  return material
}

/** 变换应用 */
function resolveVec3(value) {
  if (Array.isArray(value) && value.length >= 3) {
    return {
      x: typeof value[0] === 'number' ? value[0] : 0,
      y: typeof value[1] === 'number' ? value[1] : 0,
      z: typeof value[2] === 'number' ? value[2] : 0,
    }
  }
  if (value && typeof value === 'object') {
    return {
      x: typeof value.x === 'number' ? value.x : 0,
      y: typeof value.y === 'number' ? value.y : 0,
      z: typeof value.z === 'number' ? value.z : 0,
    }
  }
  return null
}

function applyTransform3(obj, transform) {
  const position = resolveVec3(transform && transform.position)
  if (position) obj.position.set(position.x, position.y, position.z)
  const rotation = resolveVec3(transform && transform.rotation)
  if (rotation) obj.rotation.set(rotation.x, rotation.y, rotation.z)
  const scale = resolveVec3(transform && transform.scale)
  if (scale) obj.scale.set(scale.x, scale.y, scale.z)
}

/**
 * 从 innerCores 条目创建网格（低分段几何 + PBR 材质 + 世界尺度 UV + 有机形变 + facade 顶底去窗）。
 * 阴影默认开（云除外）——与页面渲染一致。
 * @returns {THREE.Mesh|null}
 */
function createInnerCoreMesh(core) {
  if (!core || typeof core !== 'object') return null
  const geometryState = core.geometry || {}
  let geometry = buildGeometry(geometryState)
  if (!geometry) return null
  const organic = inferOrganicKind(core.name)
  if (organic && (geometry.type === 'SphereGeometry' || geometry.type === 'IcosahedronGeometry')) {
    geometry = displaceOrganicGeometry(geometry, organic)
  } else {
    const kind = inferSurfaceKind(core.name, core.material)
    if (kind) {
      const unit = SURFACE_UNIT[kind]
      const p = geometryState.parameters || {}
      if (geometryState.type === 'BoxGeometry' && geometry.type === 'BoxGeometry') {
        applyBoxWorldUV(geometry, p.width ?? 1, p.height ?? 1, p.depth ?? 1, unit)
      } else if (geometryState.type === 'PlaneGeometry') {
        applyPlaneWorldUV(geometry, p.width ?? 1, p.height ?? 1, unit)
      } else if (geometryState.type === 'CylinderGeometry' || geometryState.type === 'ConeGeometry') {
        applyCylinderWorldUV(geometry, unit)
      }
    }
  }
  let material = createMaterialFromCore(core.material, core.name, geometryState)
  // facade 楼体顶/底去窗：Box 六面同贴幕墙纹理会把窗户贴到楼顶/楼底（俯视穿帮），
  // 用材质数组把 ±y 面换成同色无纹理材质（稍深呈屋面色）
  if (
    geometryState.type === 'BoxGeometry' && geometry.type === 'BoxGeometry' &&
    inferSurfaceKind(core.name, core.material) === 'facade'
  ) {
    const capMat = material.clone()
    capMat.map = null
    capMat.bumpMap = null
    capMat.roughnessMap = null
    capMat.normalMap = null
    capMat.roughness = 0.9
    capMat.metalness = 0
    capMat.color.multiplyScalar(0.9)
    capMat.needsUpdate = true
    material = [material, material, capMat, capMat, material, material]
  }
  const mesh = new THREE.Mesh(geometry, material)
  mesh.name = typeof core.name === 'string' && core.name ? core.name : geometryState.type
  if (core.visible === false) mesh.visible = false
  mesh.castShadow = !/云|cloud/i.test(mesh.name)
  mesh.receiveShadow = true
  applyTransform3(mesh, core)
  return mesh
}

/* ==================== 阴影质量 ==================== */

/** 阴影质量调优：castShadow 的平行光/聚光灯——2048 贴图、normalBias 防痤疮、阴影相机按主体包围盒自适应 */
function tuneShadowLights(scene, box) {
  const size = box.getSize(new THREE.Vector3())
  const radius = Math.max(size.x, size.z, 4) * 0.75 + 2
  scene.traverse((o) => {
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
}

export {
  THREE,
  SURFACE_UNIT,
  ROUND_BOX_MAX,
  getSurfaceTextures,
  inferSurfaceKind,
  inferOrganicKind,
  nameJitter,
  buildGeometry,
  createMaterialFromCore,
  createInnerCoreMesh,
  displaceOrganicGeometry,
  applyBoxWorldUV,
  applyPlaneWorldUV,
  applyCylinderWorldUV,
  isSlimColumn,
  applyTransform3,
  resolveVec3,
  tuneShadowLights,
}
