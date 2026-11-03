#!/usr/bin/env node
// generate-cli-reference.mjs — emit content/cli-reference.mdx from the
// binary's own `trailtracker capabilities` JSON. The binary is the source of
// truth; this script never hand-writes command semantics.
//
// Resolution order for the capabilities document:
//   1. run $TRAILTRACKER_BIN capabilities
//   2. run <repo-root>/target/release/trailtracker capabilities
//   3. fall back to the committed snapshot generated/capabilities.json
//
// When the binary runs, the snapshot is refreshed so the committed page and
// snapshot never drift silently.

import { execFileSync } from 'node:child_process'
import { existsSync, readFileSync, writeFileSync, mkdirSync } from 'node:fs'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'

const here = dirname(fileURLToPath(import.meta.url))
const siteRoot = join(here, '..')
const repoRoot = join(siteRoot, '..')
const snapshotPath = join(siteRoot, 'generated', 'capabilities.json')
const outPath = join(siteRoot, 'content', 'cli-reference.mdx')

function loadCapabilities() {
  const candidates = [
    process.env.TRAILTRACKER_BIN,
    join(repoRoot, 'target', 'release', 'trailtracker')
  ].filter(Boolean)
  for (const bin of candidates) {
    if (!existsSync(bin)) continue
    try {
      const json = execFileSync(bin, ['capabilities'], { encoding: 'utf8' })
      const doc = JSON.parse(json)
      mkdirSync(dirname(snapshotPath), { recursive: true })
      writeFileSync(snapshotPath, JSON.stringify(doc, null, 1) + '\n')
      console.error(`cli-reference: capabilities from binary ${bin}`)
      return doc
    } catch {
      // fall through to next candidate / snapshot
    }
  }
  console.error(`cli-reference: binary not found, using snapshot ${snapshotPath}`)
  return JSON.parse(readFileSync(snapshotPath, 'utf8'))
}

// MDX treats {, }, < as JSX — escape them in any prose that comes from the
// capabilities document.
const mdx = (s) =>
  String(s)
    .replace(/\\/g, '\\\\')
    .replace(/([{}])/g, '\\$1')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
const esc = (s) => mdx(s).replace(/\|/g, '\\|')
const code = (s) => '`' + String(s).replace(/`/g, '') + '`'

const cap = loadCapabilities()

const lines = []
lines.push('---')
lines.push('title: CLI Reference')
lines.push(
  `description: The complete ${cap.name} command surface, generated from the binary's own machine-readable capabilities document.`
)
lines.push('---')
lines.push('')
lines.push('# CLI Reference')
lines.push('')
lines.push(
  `> Generated from ${code(cap.name + ' capabilities')} (schema ${code(cap.schema)}, version ${cap.version}) by ${code('docs-site/scripts/generate-cli-reference.mjs')}. Do not edit by hand — the binary is the source of truth, and this page is regenerated on every \`npm run build\`.`
)
lines.push('')
lines.push(mdx(cap.description))
lines.push('')

// io contract
lines.push('## Output contract')
lines.push('')
lines.push(`- **stdout** — ${cap.io_contract.stdout}`)
lines.push(`- **stderr** — ${cap.io_contract.stderr}`)
lines.push(`- **determinism** — ${cap.io_contract.determinism}`)
lines.push('')

// global flags
lines.push('## Global flags')
lines.push('')
lines.push('| Flag | Meaning |')
lines.push('|---|---|')
for (const f of cap.global_flags) {
  lines.push(`| ${code(f.flag)} | ${esc(f.meaning)} |`)
}
lines.push('')

// error shape
lines.push('## Error shape')
lines.push('')
lines.push(`Errors are written to ${cap.error_shape.stream}:`)
lines.push('')
lines.push('```text')
lines.push(cap.error_shape.line_1)
lines.push(cap.error_shape.line_2)
lines.push('```')
lines.push('')

// exit codes
lines.push('## Exit codes')
lines.push('')
lines.push('| Code | Meaning |')
lines.push('|---|---|')
for (const [c, meaning] of Object.entries(cap.exit_codes)) {
  lines.push(`| ${code(c)} | ${esc(meaning)} |`)
}
lines.push('')

// commands
lines.push('## Commands')
lines.push('')
for (const cmd of cap.commands) {
  lines.push(`### ${code(cmd.name)}`)
  lines.push('')
  lines.push('```text')
  lines.push(cmd.usage)
  lines.push('```')
  lines.push('')
  lines.push(mdx(cmd.summary))
  lines.push('')
  if (cmd.output) {
    lines.push(`**Output:** ${code(cmd.output.format)}` +
      (cmd.output.notes ? ` — ${mdx(cmd.output.notes)}` : ''))
    lines.push('')
  }
}

// vocabularies
lines.push('## Extractors')
lines.push('')
lines.push(`Names accepted by ${code('trailtracker extract NAME [DIR]')}:`)
lines.push('')
for (const e of cap.extractors) lines.push(`- ${code(e)}`)
lines.push('')
lines.push('## Export views')
lines.push('')
lines.push(
  `Names accepted by ${code('trailtracker export ontoloom [DIR] --view NAME')} (export formats: ${cap.export_formats.map(code).join(', ')}):`
)
lines.push('')
for (const v of cap.views) lines.push(`- ${code(v)}`)
lines.push('')
lines.push('## Query kinds')
lines.push('')
lines.push(`Names accepted by ${code('trailtracker query KIND [TARGET] [DIR]')}:`)
lines.push('')
for (const q of cap.query_kinds) lines.push(`- ${code(q)}`)
lines.push('')
lines.push('## Recommended first calls')
lines.push('')
for (const r of cap.recommended_first_calls) lines.push(`- ${code(r)}`)
lines.push('')

writeFileSync(outPath, lines.join('\n'))
console.error(`cli-reference: wrote ${outPath}`)
