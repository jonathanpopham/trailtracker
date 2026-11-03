import { Footer, Layout, Navbar } from 'nextra-theme-docs'
import { Head, Search } from 'nextra/components'
import { getPageMap } from 'nextra/page-map'
import 'nextra-theme-docs/style.css'

export const metadata = {
  title: { default: 'TrailTracker', template: '%s — TrailTracker' },
  description:
    'A deterministic, airgap-safe, cross-language code-understanding engine. No LLM, no network, no dependencies.'
}

export default async function RootLayout({ children }: { children: React.ReactNode }) {
  const pageMap = await getPageMap()

  const navbar = (
    <Navbar
      logo={<b>TrailTracker</b>}
      projectLink="https://github.com/jonathanpopham/trailtracker"
    />
  )

  const footer = (
    <Footer>
      TrailTracker &mdash; no license granted yet; all rights reserved.
    </Footer>
  )

  return (
    <html lang="en" dir="ltr" suppressHydrationWarning>
      <Head faviconGlyph="🧭" />
      <body>
        <Layout
          pageMap={pageMap}
          navbar={navbar}
          footer={footer}
          // Outside contributions aren't accepted (see README), so no edit
          // link; bug reports are welcome, so feedback points at real issues.
          editLink={null}
          feedback={{
            content: 'Found a bug? Report it →',
            link: 'https://github.com/jonathanpopham/trailtracker/issues/new'
          }}
          sidebar={{ defaultMenuCollapseLevel: 1, autoCollapse: true }}
          toc={{ float: true }}
          navigation={{ prev: true, next: true }}
          darkMode
          search={<Search placeholder="Search docs…" />}
        >
          {children}
        </Layout>
      </body>
    </html>
  )
}
