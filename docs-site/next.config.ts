import nextra from 'nextra'

const withNextra = nextra({
  defaultShowCopyCode: true,
  search: {
    codeblocks: false
  },
  contentDirBasePath: '/'
})

export default withNextra({
  reactStrictMode: true,
  // Fully static, self-contained output in out/ — no server required.
  output: 'export',
  images: { unoptimized: true }
})
