import { defineConfig } from 'vite'
import vue from '@vitejs/plugin-vue'
import path from 'path'

export default defineConfig({

  define: {

    __isProduction__: process.env.NODE_ENV === 'production'

  },

  plugins: [
    vue()

  ],

  resolve: {

    alias: [
      {
        find: /^three$/,
        replacement: path.resolve(__dirname, 'node_modules/three')
      }
    ]

  },

  base: './',

  build: {

    outDir: path.resolve(__dirname, '../rup-web-base/packages/three-editor-dist'),

    // outDir 位于项目根之外时 Vite 默认不清空旧产物，需显式开启，避免多轮构建残留旧 chunk
    emptyOutDir: true,

    // 分包：拆分大依赖，降低单 chunk 体积与主线程解析阻塞（iframe 嵌入时宿主页面卡顿主要来源）
    rolldownOptions: {
      output: {
        manualChunks(id) {
          if (id.includes('three-edit-cores') || id.includes('/three@') || id.includes('/cannon-es') || id.includes('/gsap@')) return 'three-vendor'
          if (id.includes('/element-plus') || id.includes('/@element-plus') || id.includes('vue-element-plus-x')) return 'element-plus-vendor'
          if (id.includes('/echarts')) return 'echarts-vendor'
          return undefined
        }
      }
    }

  },

  server: {

    port: 5000,

    open: true,

    host: '0.0.0.0'

  }

})
