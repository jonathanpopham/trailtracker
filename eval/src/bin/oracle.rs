//! `oracle` — external ground-truth verification.
//!
//! Diffs TrailTracker's exact `(file, kind, name, line)` definition set against a
//! canonical external parser, per file, and reports missed/extra + whole-file
//! drops. The bar is ZERO unexplained diffs: every diff is a real bug to fix or an
//! allowlisted entry with a reason. Aggregate percentages are deliberately NOT the
//! metric — exact per-symbol reconciliation is (a 99.8% "pass" hid two real bugs).
//!
//! Lives in the never-shipped eval crate, so it may shell out to system parsers.
//!
//! Usage:
//!   oracle --lang <name> --repo <dir>
//!          [--oracle ast|ripper|goparser|tsnode|ctags] [--out report.json]
//!
//! Oracles (`--oracle`): `ast` (Python, canonical), `ripper` (Ruby, canonical),
//! `goparser` (Go `go/parser`, canonical), `tsnode` (TypeScript/JavaScript via the
//! `typescript` compiler API, canonical), `ctags` (universal-ctags, coarse Tier B).
//!
//! Exit code: 0 only when there are no unexplained diffs and no whole-file drops.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use trailtracker::pipeline::analyze_dir;

/// A definition keyed for exact reconciliation. `kind` is normalized to `fn` or
/// `type` so TrailTracker and the oracle compare on the same vocabulary.
type Def = (String, String, String, u32); // (relpath, kind, name, line)

struct Args {
    lang: String,
    repo: PathBuf,
    oracle: String,
    out: Option<PathBuf>,
    allowlist: PathBuf,
}

impl Args {
    fn parse() -> Args {
        let mut lang = String::new();
        let mut repo = PathBuf::from(".");
        let mut oracle = String::from("ast");
        let mut out = None;
        let mut allowlist = PathBuf::from("eval/oracle-allowlist.tsv");
        let mut it = std::env::args().skip(1);
        while let Some(a) = it.next() {
            match a.as_str() {
                "--lang" => lang = it.next().unwrap_or_default(),
                "--repo" => repo = PathBuf::from(it.next().unwrap_or_default()),
                "--oracle" => oracle = it.next().unwrap_or_default(),
                "--out" => out = it.next().map(PathBuf::from),
                "--allowlist" => allowlist = PathBuf::from(it.next().unwrap_or_default()),
                other => eprintln!("oracle: ignoring unknown arg {other}"),
            }
        }
        Args {
            lang,
            repo,
            oracle,
            out,
            allowlist,
        }
    }
}

fn main() -> ExitCode {
    let args = Args::parse();
    if args.lang.is_empty() {
        eprintln!("oracle: --lang is required");
        return ExitCode::FAILURE;
    }

    let tt = match trailtracker_defs(&args.repo, &args.lang) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("oracle: analyze failed: {e}");
            return ExitCode::FAILURE;
        }
    };

    let truth = match args.oracle.as_str() {
        "ast" => python_ast_defs(&args.repo),
        "ripper" => ruby_ripper_defs(&args.repo),
        "goparser" => go_parser_defs(&args.repo),
        "tsnode" => ts_node_defs(&args.repo, &args.lang),
        "ctags" => ctags_defs(&args.repo, &args.lang),
        other => Err(std::io::Error::other(format!(
            "oracle '{other}' not implemented (have: ast, ripper, goparser, tsnode, ctags)"
        ))),
    };
    let truth = match truth {
        Ok(d) => d,
        Err(e) => {
            eprintln!("oracle: {} adapter failed: {e}", args.oracle);
            return ExitCode::FAILURE;
        }
    };

    // Compare only files whose extension this language's front end claims. External
    // parsers (notably ctags) detect shebang-only scripts with no extension, which
    // TrailTracker routes purely by extension and never sees — those are not TT
    // misses, so they must not count as drops.
    let exts = lang_extensions(&args.lang);
    let truth: BTreeSet<Def> = truth.into_iter().filter(|d| has_ext(&d.0, &exts)).collect();

    let allow = load_allowlist(&args.allowlist, &args.lang);
    let report = reconcile(&args.lang, &args.oracle, &tt, &truth, &allow);
    report.print_summary();
    if let Some(path) = &args.out {
        if let Err(e) = std::fs::write(path, report.to_json()) {
            eprintln!("oracle: could not write {}: {e}", path.display());
        }
    }
    if report.clean() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

// --- TrailTracker side -----------------------------------------------------

/// Extract TrailTracker's definition set for `lang`, attributing every def to its
/// file via the `DECLARES` edges (every File node DECLARES all its defs directly).
fn trailtracker_defs(repo: &Path, lang: &str) -> std::io::Result<BTreeSet<Def>> {
    let analysis = analyze_dir(repo)?;
    let jsonl = analysis.graph.to_jsonl();

    // def_id -> (kind, name, line) for Function/Type nodes of this language.
    let mut info: BTreeMap<String, (String, String, u32)> = BTreeMap::new();
    // def_id -> the node that DECLARES it (a `file::` OR a `module::`/`mod::`).
    let mut declarer: BTreeMap<String, String> = BTreeMap::new();
    // Undirected CONTAINS adjacency, so a module-declared def can be walked to its
    // file (e.g. OCaml/Haskell/Elm: `module::A DECLARES fn`, `module::A CONTAINS
    // file::a.ml`). Direction-agnostic to also handle `file CONTAINS module`.
    let mut contains: BTreeMap<String, Vec<String>> = BTreeMap::new();

    for line in jsonl.lines() {
        if line.contains("\"record\":\"node\"") {
            let norm = match field(line, "\"kind\":\"").as_deref() {
                Some("Function") => "fn",
                Some("Type") => "type",
                _ => continue,
            };
            if field(line, "\"language\":\"").as_deref() != Some(lang) {
                continue;
            }
            let (Some(id), Some(name), Some(ln)) = (
                field(line, "\"id\":\""),
                field(line, "\"name\":\""),
                num_field(line, "\"line\":"),
            ) else {
                continue;
            };
            info.insert(id, (norm.to_string(), name, ln));
        } else if line.contains("\"record\":\"edge\"") {
            let (Some(from), Some(to)) = (field(line, "\"from\":\""), field(line, "\"to\":\""))
            else {
                continue;
            };
            match field(line, "\"kind\":\"").as_deref() {
                Some("DECLARES") => {
                    // A def can be declared by both its file and a namespace/module
                    // (e.g. Perl: file::Foo.pm AND ns::Mojo::Foo). A `file::`
                    // declarer is directly resolvable, so it always wins; a module
                    // declarer is only a fallback (resolved later by CONTAINS walk).
                    if from.starts_with("file::") {
                        declarer.insert(to, from);
                    } else {
                        declarer.entry(to).or_insert(from);
                    }
                }
                Some("CONTAINS") => {
                    contains.entry(from.clone()).or_default().push(to.clone());
                    contains.entry(to).or_default().push(from);
                }
                _ => {}
            }
        }
    }

    // Resolve a node to its file: itself if it's a `file::`, else the nearest
    // `file::` reachable over CONTAINS edges (BFS handles nested modules).
    let file_of = |start: &str| -> Option<String> {
        if let Some(p) = start.strip_prefix("file::") {
            return Some(p.to_string());
        }
        let mut seen = BTreeSet::new();
        let mut q = VecDeque::new();
        seen.insert(start.to_string());
        q.push_back(start.to_string());
        while let Some(n) = q.pop_front() {
            if let Some(p) = n.strip_prefix("file::") {
                return Some(p.to_string());
            }
            if let Some(neighbors) = contains.get(&n) {
                for m in neighbors {
                    if seen.insert(m.clone()) {
                        q.push_back(m.clone());
                    }
                }
            }
        }
        None
    };

    let mut out = BTreeSet::new();
    for (id, (kind, name, line)) in &info {
        if let Some(decl) = declarer.get(id) {
            if let Some(path) = file_of(decl) {
                out.insert((path, kind.clone(), name.clone(), *line));
            }
        }
    }
    Ok(out)
}

// --- Oracle: Python `ast` (canonical ground truth) -------------------------

fn python_ast_defs(repo: &Path) -> std::io::Result<BTreeSet<Def>> {
    const SCRIPT: &str = r#"
import ast, os, sys
root = sys.argv[1]
for dp, _, fs in os.walk(root):
    if os.sep + ".git" in dp:
        continue
    for f in fs:
        if not f.endswith(".py"):
            continue
        p = os.path.join(dp, f)
        rel = os.path.relpath(p, root)
        try:
            tree = ast.parse(open(p, encoding="utf-8").read())
        except Exception:
            # ast itself can't parse it (e.g. py2 fixture): skip; not our diff.
            continue
        for n in ast.walk(tree):
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
                print(f"{rel}\tfn\t{n.name}\t{n.lineno}")
            elif isinstance(n, ast.ClassDef):
                print(f"{rel}\ttype\t{n.name}\t{n.lineno}")
"#;
    let output = Command::new("python3")
        .arg("-c")
        .arg(SCRIPT)
        .arg(repo)
        .output()?;
    if !output.status.success() {
        return Err(std::io::Error::other(format!(
            "python3 exited non-zero: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    let mut out = BTreeSet::new();
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        let mut it = line.splitn(4, '\t');
        if let (Some(rel), Some(kind), Some(name), Some(ln)) =
            (it.next(), it.next(), it.next(), it.next())
        {
            if let Ok(line_no) = ln.parse::<u32>() {
                out.insert((rel.to_string(), kind.to_string(), name.to_string(), line_no));
            }
        }
    }
    Ok(out)
}

// --- Oracle: Ruby `Ripper` (Tier A canonical) ------------------------------

/// Ruby's own parser (`Ripper`, stdlib). Walks the sexp for `def`/`def self.`
/// (-> fn) and `class` (-> type). Modules are intentionally NOT emitted: TT lowers
/// a Ruby `module` to a `Module` node (not a `Type`), so excluding modules on both
/// sides keeps the fn/type comparison aligned.
fn ruby_ripper_defs(repo: &Path) -> std::io::Result<BTreeSet<Def>> {
    const SCRIPT: &str = r##"
require 'ripper'
root = ARGV[0]
Dir.glob(File.join(root, '**', '*.rb')).each do |p|
  next if p.include?('/.git/')
  rel = p.sub(/^#{Regexp.escape(root)}\/?/, '')
  begin
    sexp = Ripper.sexp(File.read(p))
  rescue
    next
  end
  next if sexp.nil?
  stack = [sexp]
  until stack.empty?
    n = stack.pop
    next unless n.is_a?(Array)
    if n[0] == :def && n[1].is_a?(Array) && n[1][0] == :@ident
      puts "#{rel}\tfn\t#{n[1][1]}\t#{n[1][2][0]}"
    elsif n[0] == :defs && n[3].is_a?(Array) && n[3][0] == :@ident
      puts "#{rel}\tfn\t#{n[3][1]}\t#{n[3][2][0]}"
    elsif (n[0] == :class || n[0] == :module) && n[1].is_a?(Array) && n[1][0] == :const_ref
      # A Ruby `module` is lowered to a `Type` (type_kind: module) by the front end
      # exactly like a `class`, so the oracle counts both. (Compact `A::B` headers
      # use :const_path_ref and are a separate case, not handled here.)
      c = n[1][1]
      puts "#{rel}\ttype\t#{c[1]}\t#{c[2][0]}" if c.is_a?(Array) && c[0] == :@const
    end
    n.each { |ch| stack.push(ch) if ch.is_a?(Array) }
  end
end
"##;
    let output = Command::new("ruby")
        .arg("-e")
        .arg(SCRIPT)
        .arg(repo)
        .output()?;
    if !output.status.success() {
        return Err(std::io::Error::other(format!(
            "ruby/ripper exited non-zero: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    let mut out = BTreeSet::new();
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        let mut it = line.splitn(4, '\t');
        if let (Some(rel), Some(kind), Some(name), Some(ln)) =
            (it.next(), it.next(), it.next(), it.next())
        {
            if let Ok(line_no) = ln.parse::<u32>() {
                out.insert((rel.to_string(), kind.to_string(), name.to_string(), line_no));
            }
        }
    }
    Ok(out)
}

// --- Oracle: Go `go/parser` (Tier A canonical) -----------------------------

/// Go's own parser (`go/parser` + `go/ast`). A generated program walks every
/// `*.go` file and emits `*ast.FuncDecl` (top-level funcs AND methods) as `fn` and
/// each `*ast.TypeSpec` (`type X …`) as `type`, keyed by the name identifier's
/// 1-based line — exactly how the Go front end lowers them.
///
/// Kind alignment with `src/lang/go/lower.rs`:
///   - `func` (with or without a receiver) → `Function` → `fn`. A method also gets
///     `HAS_METHOD`, but it is still one `Function` node, so methods and plain
///     funcs both map to `fn` (no separate kind).
///   - `type T struct{}` / `interface{}` / alias / defined → `Type` → `type`.
///     Structs and interfaces are deliberately INCLUDED (TT lowers them to `Type`
///     with a `type_kind`); only the surface form differs.
///   - Package-level `const`/`var` → `Constant`, and interface *method
///     signatures* (no definition site) → nothing — neither is emitted here, so
///     both sides stay on the `fn`/`type` vocabulary. `*ast.FuncDecl` naturally
///     excludes interface method signatures (those are `*ast.Field`s).
///
/// Directory pruning mirrors the pipeline's `collect_source_files`: skip `target`,
/// `.git`, `node_modules`, and any dot-directory. `vendor` is intentionally NOT
/// skipped — TT descends into it, so the oracle must too for exact reconciliation.
fn go_parser_defs(repo: &Path) -> std::io::Result<BTreeSet<Def>> {
    const PROGRAM: &str = r#"
package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
)

func main() {
	root := os.Args[1]
	filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return nil
		}
		if d.IsDir() {
			if path == root {
				return nil
			}
			name := d.Name()
			if name == "target" || name == ".git" || name == "node_modules" || strings.HasPrefix(name, ".") {
				return filepath.SkipDir
			}
			return nil
		}
		if !strings.HasSuffix(path, ".go") {
			return nil
		}
		fset := token.NewFileSet()
		f, perr := parser.ParseFile(fset, path, nil, 0)
		if perr != nil {
			// go/parser itself cannot parse it: skip; not our diff.
			return nil
		}
		rel, rerr := filepath.Rel(root, path)
		if rerr != nil {
			rel = path
		}
		rel = filepath.ToSlash(rel)
		for _, decl := range f.Decls {
			switch dd := decl.(type) {
			case *ast.FuncDecl:
				line := fset.Position(dd.Name.Pos()).Line
				fmt.Printf("%s\tfn\t%s\t%d\n", rel, dd.Name.Name, line)
			case *ast.GenDecl:
				if dd.Tok == token.TYPE {
					for _, spec := range dd.Specs {
						if ts, ok := spec.(*ast.TypeSpec); ok {
							line := fset.Position(ts.Name.Pos()).Line
							fmt.Printf("%s\ttype\t%s\t%d\n", rel, ts.Name.Name, line)
						}
					}
				}
			}
		}
		return nil
	})
}
"#;
    // `go run` needs the program in a `.go` file. A std-only `package main` runs
    // without a module (no go.mod), so a lone temp file is enough.
    let dir = std::env::temp_dir().join(format!("tt-oracle-go-{}", std::process::id()));
    std::fs::create_dir_all(&dir)?;
    let src_path = dir.join("goparser_main.go");
    std::fs::write(&src_path, PROGRAM)?;
    let output = Command::new("go")
        .arg("run")
        .arg(&src_path)
        .arg(repo)
        .output();
    let _ = std::fs::remove_dir_all(&dir);
    let output = output?;
    if !output.status.success() {
        return Err(std::io::Error::other(format!(
            "go run exited non-zero: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    Ok(parse_tsv_defs(&String::from_utf8_lossy(&output.stdout)))
}

// --- Oracle: TypeScript compiler API (Tier A canonical) --------------------

/// TypeScript's own compiler API (`require('typescript')`), driving one parser for
/// both `--lang typescript` (`.ts`/`.tsx`) and `--lang javascript`
/// (`.js`/`.jsx`/`.mjs`/`.cjs`). A generated Node script walks each source file's
/// definition containers (the file, namespaces, class/interface bodies) — never
/// into function bodies, matching TT's structural lowering — and emits 1-based
/// name lines.
///
/// Kind alignment with `src/lang/typescript/lower.rs` + `…/javascript/lower.rs`:
///   - function declarations, methods, constructors, get/set accessors → `fn`.
///   - class / interface / enum / type-alias → `type`. (TS interface *method
///     signatures* DO become `Function`s in TT, so they are emitted as `fn`.)
///   - A name-bound arrow/function expression (a `const f = () => …` or a class
///     field `m = () => …`) is a `Function` in TT for both TypeScript and
///     JavaScript, so the script emits these as `fn` (gated by `allowVarFns`,
///     now always on). NOTE: TT additionally extracts object-literal methods and
///     CommonJS `exports.x = fn` / `prototype.x = fn` assignments for JS, which
///     this AST-container walk does not descend into — so JS may show residual
///     `extra` until the walk is extended (kept Tier B / report-only meanwhile).
///   - `namespace`/`module` → `Module` (excluded); plain `const`/`let`/`var` and
///     plain class fields → `Constant`/field (excluded). Computed-name members
///     (`[expr]()`) and anonymous default exports have no static name and are
///     skipped on both sides.
///
/// Documented residual mismatches (rare; allowlist if they surface): the TT JS
/// parser records a computed method `[x]()` under the literal name `[`, and the TT
/// TS parser may record an interface construct-signature `new()` as a method
/// `new`; the compiler-API walk has no static name there and emits neither.
///
/// If a compiler-API-bearing `typescript` is not importable, TypeScript 6 is
/// `npm install`ed into a cached temp dir and surfaced via `NODE_PATH`.
fn ts_node_defs(repo: &Path, lang: &str) -> std::io::Result<BTreeSet<Def>> {
    const SCRIPT: &str = r#"
const _ts = require('typescript');
// TS 5.9.3 and 6.0.3 expose the compiler API on the CJS root. npm's current
// latest, 7.0.2, exposes only version metadata there; ensure_typescript()
// provisions TS6 in that case. Keep the fallback for default-wrapped namespaces.
const ts = (_ts && _ts.ScriptKind) ? _ts : (_ts && _ts.default) ? _ts.default : _ts;
const fs = require('fs');
const path = require('path');

const root = process.argv[2];
const lang = process.argv[3];
const exts = lang === 'typescript' ? ['.ts', '.tsx'] : ['.js', '.jsx', '.mjs', '.cjs'];
const allowVarFns = true; // TT emits arrow/fn-expression consts as Function for both ts & js
const SKIP = new Set(['target', '.git', 'node_modules']);

function walk(dir, acc) {
  let entries;
  try { entries = fs.readdirSync(dir, { withFileTypes: true }); } catch (e) { return; }
  for (const e of entries) {
    const full = path.join(dir, e.name);
    if (e.isDirectory()) {
      if (SKIP.has(e.name) || e.name.startsWith('.')) continue;
      walk(full, acc);
    } else if (e.isFile()) {
      if (exts.some((x) => e.name.endsWith(x))) acc.push(full);
    }
  }
}

const files = [];
walk(root, files);
const out = [];

for (const file of files) {
  let src;
  try { src = fs.readFileSync(file, 'utf8'); } catch (e) { continue; }
  const scriptKind = file.endsWith('.tsx') ? ts.ScriptKind.TSX
    : file.endsWith('.jsx') ? ts.ScriptKind.JSX
    : (file.endsWith('.js') || file.endsWith('.mjs') || file.endsWith('.cjs')) ? ts.ScriptKind.JS
    : ts.ScriptKind.TS;
  let sf;
  try { sf = ts.createSourceFile(file, src, ts.ScriptTarget.Latest, true, scriptKind); }
  catch (e) { continue; }
  const rel = path.relative(root, file).split(path.sep).join('/');
  const emit = (kind, name, pos) => {
    const line = sf.getLineAndCharacterOfPosition(pos).line + 1;
    out.push(rel + '\t' + kind + '\t' + name + '\t' + line);
  };
  const named = (n) => n && (ts.isIdentifier(n) || ts.isStringLiteral(n) || ts.isNumericLiteral(n) || ts.isPrivateIdentifier(n));
  const isFnInit = (init) => init && (ts.isArrowFunction(init) || ts.isFunctionExpression(init));
  // The front end treats a `const` whose initializer has a top-level `=>`/`function`
  // as function-valued, so a ternary or logical chain of arrows
  // (`const k = cond ? (a)=>… : (b)=>…`) is a Function. Mirror that for var decls.
  const isFnValuedInit = (init) => {
    if (!init) return false;
    if (ts.isArrowFunction(init) || ts.isFunctionExpression(init)) return true;
    if (ts.isParenthesizedExpression(init)) return isFnValuedInit(init.expression);
    if (ts.isConditionalExpression(init)) return isFnValuedInit(init.whenTrue) || isFnValuedInit(init.whenFalse);
    if (ts.isBinaryExpression(init)) {
      const k = init.operatorToken.kind;
      if (k === ts.SyntaxKind.BarBarToken || k === ts.SyntaxKind.AmpersandAmpersandToken || k === ts.SyntaxKind.QuestionQuestionToken) {
        return isFnValuedInit(init.left) || isFnValuedInit(init.right);
      }
    }
    return false;
  };

  // The JS front end additionally lowers CommonJS member assignments and
  // object-literal methods to `Function` (see src/lang/javascript/lower.rs):
  // `exports.NAME = fn`, `X.prototype.NAME = fn`, `obj = { foo(){}, bar: ()=>{} }`.
  // Mirrored here for JS only so the oracle counts the same definitions.
  const allowMemberFns = lang === 'javascript';

  // Function-valued members of an object literal: shorthand methods
  // (`foo(){}`, `async foo(){}`, `get foo(){}`, `*foo(){}`) and fn/arrow-valued
  // properties (`bar: () => …`). Data properties are ignored; not descended.
  function emitObjectMethods(obj) {
    for (const p of obj.properties) {
      if (ts.isMethodDeclaration(p) || ts.isGetAccessorDeclaration(p) || ts.isSetAccessorDeclaration(p)) {
        if (named(p.name)) emit('fn', p.name.text, p.name.getStart(sf));
      } else if (ts.isPropertyAssignment(p) && named(p.name) && isFnInit(p.initializer)) {
        emit('fn', p.name.text, p.name.getStart(sf));
      }
    }
  }

  // A top-level `<chain> = …` assignment statement. The name is the last segment
  // of a plain dotted member chain (or a bare identifier); the RHS must be a
  // function/arrow (→ that name) or an object literal (→ its function members).
  // For a chained assignment `a = b = fn`, the front end names only the innermost
  // member target (`b`), so recurse into a `=`-valued RHS and emit that one.
  function visitAssignment(e) {
    const rhs = e.right;
    if (ts.isBinaryExpression(rhs) && rhs.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
      visitAssignment(rhs);
      return;
    }
    let nameNode = null;
    if (ts.isPropertyAccessExpression(e.left)) nameNode = e.left.name; // a.b.c
    else if (ts.isIdentifier(e.left)) nameNode = e.left;              // x = fn
    if (!nameNode) return;
    if (isFnInit(rhs)) emit('fn', nameNode.text, nameNode.getStart(sf));
    else if (ts.isObjectLiteralExpression(rhs)) emitObjectMethods(rhs);
  }
  function visitMemberAssignment(stmt) {
    const e = stmt.expression;
    if (!ts.isBinaryExpression(e) || e.operatorToken.kind !== ts.SyntaxKind.EqualsToken) return;
    visitAssignment(e);
  }

  function visitModule(mod) {
    let body = mod.body;
    while (body && ts.isModuleDeclaration(body)) body = body.body;
    if (body && ts.isModuleBlock(body)) visitContainer(body);
  }

  function visitMembers(typeNode) {
    for (const m of typeNode.members) {
      if (ts.isMethodDeclaration(m) || ts.isMethodSignature(m)) {
        if (named(m.name)) emit('fn', m.name.text, m.name.getStart(sf));
      } else if (ts.isConstructorDeclaration(m)) {
        emit('fn', 'constructor', m.getStart(sf));
      } else if (ts.isGetAccessorDeclaration(m) || ts.isSetAccessorDeclaration(m)) {
        if (named(m.name)) emit('fn', m.name.text, m.name.getStart(sf));
      } else if (allowVarFns && ts.isPropertyDeclaration(m)) {
        if (m.name && ts.isIdentifier(m.name) && isFnInit(m.initializer)) emit('fn', m.name.text, m.name.getStart(sf));
      }
    }
  }

  function visitContainer(node) {
    ts.forEachChild(node, (child) => {
      if (ts.isFunctionDeclaration(child)) {
        if (child.name) emit('fn', child.name.text, child.name.getStart(sf));
      } else if (ts.isClassDeclaration(child) || ts.isInterfaceDeclaration(child)) {
        if (child.name) emit('type', child.name.text, child.name.getStart(sf));
        visitMembers(child);
      } else if (ts.isEnumDeclaration(child) || ts.isTypeAliasDeclaration(child)) {
        if (child.name) emit('type', child.name.text, child.name.getStart(sf));
      } else if (ts.isModuleDeclaration(child)) {
        visitModule(child);
      } else if (ts.isVariableStatement(child)) {
        for (const decl of child.declarationList.declarations) {
          if (allowVarFns && ts.isIdentifier(decl.name) && isFnValuedInit(decl.initializer)) {
            emit('fn', decl.name.text, decl.name.getStart(sf));
          } else if (allowMemberFns && ts.isIdentifier(decl.name) && decl.initializer && ts.isObjectLiteralExpression(decl.initializer)) {
            emitObjectMethods(decl.initializer);
          }
        }
      } else if (allowMemberFns && ts.isExpressionStatement(child)) {
        visitMemberAssignment(child);
      }
    });
  }

  visitContainer(sf);
}

process.stdout.write(out.join('\n') + (out.length ? '\n' : ''));
"#;
    let dir = std::env::temp_dir().join(format!("tt-oracle-ts-{}", std::process::id()));
    std::fs::create_dir_all(&dir)?;
    let script_path = dir.join("tsdefs.js");
    std::fs::write(&script_path, SCRIPT)?;

    let node_path = ensure_typescript();
    let mut cmd = Command::new("node");
    cmd.arg(&script_path).arg(repo).arg(lang);
    if let Ok(Some(np)) = &node_path {
        cmd.env("NODE_PATH", np);
    }
    let output = cmd.output();
    let _ = std::fs::remove_dir_all(&dir);
    // Surface an install failure only if node also failed (typescript missing).
    let output = output?;
    if !output.status.success() {
        if let Err(e) = node_path {
            return Err(std::io::Error::other(format!(
                "node failed and typescript could not be installed: {e}: {}",
                String::from_utf8_lossy(&output.stderr)
            )));
        }
        return Err(std::io::Error::other(format!(
            "node exited non-zero: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    Ok(parse_tsv_defs(&String::from_utf8_lossy(&output.stdout)))
}

/// Require the compiler API members used by the adapter, accepting both the
/// classic CommonJS namespace and a default-wrapped namespace.
const TYPESCRIPT_API_PROBE: &str = r#"
const _ts = require('typescript');
const ts = (_ts && _ts.ScriptKind) ? _ts : (_ts && _ts.default) ? _ts.default : _ts;
if (!ts || !ts.ScriptKind || !ts.SyntaxKind ||
    typeof ts.createSourceFile !== 'function' ||
    typeof ts.forEachChild !== 'function') process.exit(1);
"#;

fn typescript_api_available(node_path: Option<&Path>) -> bool {
    let mut cmd = Command::new("node");
    cmd.arg("-e").arg(TYPESCRIPT_API_PROBE);
    if let Some(path) = node_path {
        cmd.env("NODE_PATH", path);
        if let Some(dir) = path.parent() {
            cmd.current_dir(dir);
        }
    }
    cmd.output().is_ok_and(|output| output.status.success())
}

/// Ensure the classic `typescript` compiler API is importable by Node. Returns
/// `Ok(None)` when the ambient package has that API, or
/// `Ok(Some(node_modules_dir))` after provisioning TypeScript 6 in a cached temp
/// dir. TypeScript 7's root export contains version metadata but no compiler API,
/// so package resolution alone is not sufficient.
fn ensure_typescript() -> std::io::Result<Option<PathBuf>> {
    if typescript_api_available(None) {
        return Ok(None);
    }
    let dir = std::env::temp_dir().join("tt-oracle-ts-deps");
    std::fs::create_dir_all(&dir)?;
    let node_modules = dir.join("node_modules");
    if !typescript_api_available(Some(&node_modules)) {
        let st = Command::new("npm")
            .arg("install")
            .arg("typescript@6")
            .arg("--no-save")
            .arg("--silent")
            .arg("--prefix")
            .arg(&dir)
            .output()?;
        if !st.status.success() {
            return Err(std::io::Error::other(format!(
                "npm install typescript@6 failed: {}",
                String::from_utf8_lossy(&st.stderr)
            )));
        }
        if !typescript_api_available(Some(&node_modules)) {
            return Err(std::io::Error::other(
                "installed typescript@6 does not expose the compiler API",
            ));
        }
    }
    Ok(Some(node_modules))
}

/// Parse the shared `rel\tkind\tname\tline` adapter output into a [`Def`] set.
fn parse_tsv_defs(stdout: &str) -> BTreeSet<Def> {
    let mut out = BTreeSet::new();
    for line in stdout.lines() {
        let mut it = line.splitn(4, '\t');
        if let (Some(rel), Some(kind), Some(name), Some(ln)) =
            (it.next(), it.next(), it.next(), it.next())
        {
            if let Ok(line_no) = ln.parse::<u32>() {
                out.insert((rel.to_string(), kind.to_string(), name.to_string(), line_no));
            }
        }
    }
    out
}

// --- Oracle: universal-ctags (Tier B, coarse) ------------------------------

/// universal-ctags adapter. Maps ctags definition kinds onto the normalized
/// fn/type vocabulary. Coarser than a canonical parser (kinds only), so results
/// are Tier B. Requires a genuine Universal Ctags binary (not Emacs etags).
fn ctags_defs(repo: &Path, lang: &str) -> std::io::Result<BTreeSet<Def>> {
    let bin = universal_ctags_bin()?;
    let output = Command::new(&bin)
        .arg("-R")
        .arg(format!("--languages={}", ctags_lang(lang)))
        .arg("--output-format=json")
        .arg("--fields=+nK")
        .arg("-f")
        .arg("-")
        .arg(".")
        .current_dir(repo)
        .output()?;
    if !output.status.success() {
        return Err(std::io::Error::other(format!(
            "ctags exited non-zero: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    let mut out = BTreeSet::new();
    // NOTE: universal-ctags JSON is pretty-spaced (`"key": "value"`), unlike the
    // compact TrailTracker JSONL — so use the whitespace-tolerant `jfield`/`jnum`.
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        if jfield(line, "_type").as_deref() != Some("tag") {
            continue;
        }
        let (Some(path), Some(name), Some(kind)) = (
            jfield(line, "path"),
            jfield(line, "name"),
            jfield(line, "kind"),
        ) else {
            continue;
        };
        // Coarse, language-dependent mapping (ctags is Tier B). `member` is a method
        // in some languages and a field in others — accepted as a known imprecision.
        let norm = match kind.as_str() {
            "function" | "method" | "member" | "subroutine" | "func" | "getter" | "setter"
            | "procedure" | "singletonMethod" => "fn",
            "class" | "struct" | "interface" | "enum" | "trait" | "type" | "union" | "record"
            | "module" | "protocol" => "type",
            _ => continue,
        };
        let line_no = jnum(line, "line").unwrap_or(0);
        let path = path.strip_prefix("./").unwrap_or(&path).to_string();
        out.insert((path, norm.to_string(), name, line_no));
    }
    Ok(out)
}

/// Map a TrailTracker language name to a ctags `--languages` value (best effort).
fn ctags_lang(lang: &str) -> String {
    match lang {
        "cpp" => "C++",
        "csharp" => "C#",
        "javascript" => "JavaScript",
        "typescript" => "TypeScript",
        "php" => "PHP",
        "sql" => "SQL",
        "html" => "HTML",
        "css" => "CSS",
        "ocaml" => "OCaml",
        "vhdl" => "VHDL",
        "matlab" => "MatLab",
        "objc" => "ObjectiveC",
        "bash" => "Sh",
        other => return title_case(other),
    }
    .to_string()
}

fn title_case(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
        None => String::new(),
    }
}

/// Find a genuine Universal Ctags binary (the `ctags` on PATH may be Emacs etags).
fn universal_ctags_bin() -> std::io::Result<String> {
    for cand in [
        "ctags",
        "/opt/homebrew/opt/universal-ctags/bin/ctags",
        "/usr/bin/ctags",
    ] {
        if let Ok(o) = Command::new(cand).arg("--version").output() {
            if String::from_utf8_lossy(&o.stdout).contains("Universal Ctags") {
                return Ok(cand.to_string());
            }
        }
    }
    Err(std::io::Error::other(
        "universal-ctags not found (the `ctags` on PATH may be Emacs etags)",
    ))
}

/// The file extensions this language's front end claims, read from the registry.
fn lang_extensions(lang: &str) -> Vec<String> {
    trailtracker::lang::frontend::front_ends()
        .iter()
        .find(|fe| fe.name() == lang)
        .map(|fe| fe.extensions().iter().map(|s| s.to_string()).collect())
        .unwrap_or_default()
}

/// True if `path`'s extension is one this language claims. An unknown language
/// (empty `exts`) is not filtered; a file with no extension is never claimed.
fn has_ext(path: &str, exts: &[String]) -> bool {
    if exts.is_empty() {
        return true;
    }
    let base = path.rsplit('/').next().unwrap_or(path);
    match base.rsplit_once('.') {
        Some((_, e)) => exts.iter().any(|x| x == e),
        None => false,
    }
}

/// Load allowlisted diffs for `lang` from a TSV:
/// `lang<TAB>file<TAB>kind<TAB>name<TAB>reason`. Blank lines and `#` comments are
/// ignored. Returns the matched `(file, kind, name)` set (line-agnostic).
fn load_allowlist(path: &Path, lang: &str) -> BTreeSet<(String, String, String)> {
    let mut out = BTreeSet::new();
    let Ok(text) = std::fs::read_to_string(path) else {
        return out;
    };
    for line in text.lines() {
        let line = line.trim_end();
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            continue;
        }
        let mut it = line.splitn(5, '\t');
        let (Some(l), Some(file), Some(kind), Some(name)) =
            (it.next(), it.next(), it.next(), it.next())
        else {
            continue;
        };
        if l == lang {
            out.insert((file.to_string(), kind.to_string(), name.to_string()));
        }
    }
    out
}

// --- Reconciliation --------------------------------------------------------

struct Report {
    lang: String,
    oracle: String,
    tt_total: usize,
    truth_total: usize,
    missed: Vec<Def>,              // in oracle, not in TrailTracker
    extra: Vec<Def>,               // in TrailTracker, not in oracle
    whole_file_drops: Vec<String>, // files with >=1 truth def but 0 TT defs
}

fn reconcile(
    lang: &str,
    oracle: &str,
    tt: &BTreeSet<Def>,
    truth: &BTreeSet<Def>,
    allow: &BTreeSet<(String, String, String)>,
) -> Report {
    // A diff is excused only by an allowlist entry matching (file, kind, name) —
    // line-agnostic, since line numbers shift. Every entry carries a written reason.
    let allowed = |d: &Def| allow.contains(&(d.0.clone(), d.1.clone(), d.2.clone()));
    let missed: Vec<Def> = truth
        .difference(tt)
        .filter(|d| !allowed(d))
        .cloned()
        .collect();
    let extra: Vec<Def> = tt
        .difference(truth)
        .filter(|d| !allowed(d))
        .cloned()
        .collect();

    // Whole-file-drop detection: a file the oracle has defs for, but TrailTracker
    // produced ZERO defs for — the signature of a swallowed parse panic.
    let tt_files: BTreeSet<&String> = tt.iter().map(|d| &d.0).collect();
    let mut drop_files: BTreeSet<String> = BTreeSet::new();
    for (path, ..) in truth {
        if !tt_files.contains(path) {
            drop_files.insert(path.clone());
        }
    }

    Report {
        lang: lang.to_string(),
        oracle: oracle.to_string(),
        tt_total: tt.len(),
        truth_total: truth.len(),
        missed,
        extra,
        whole_file_drops: drop_files.into_iter().collect(),
    }
}

impl Report {
    fn clean(&self) -> bool {
        self.missed.is_empty() && self.extra.is_empty() && self.whole_file_drops.is_empty()
    }

    fn print_summary(&self) {
        eprintln!(
            "oracle [{}] vs {}: tt={} truth={} | MISSED={} EXTRA={} WHOLE-FILE-DROPS={}",
            self.lang,
            self.oracle,
            self.tt_total,
            self.truth_total,
            self.missed.len(),
            self.extra.len(),
            self.whole_file_drops.len(),
        );
        for f in self.whole_file_drops.iter().take(10) {
            eprintln!("  DROP  {f}");
        }
        for d in self.missed.iter().take(15) {
            eprintln!("  miss  {}:{}:{} ({})", d.0, d.3, d.2, d.1);
        }
        for d in self.extra.iter().take(15) {
            eprintln!("  extra {}:{}:{} ({})", d.0, d.3, d.2, d.1);
        }
        eprintln!(
            "  => {}",
            if self.clean() {
                "VERIFIED (0 unexplained diffs)"
            } else {
                "DIFFS PRESENT — fix the bug or allowlist with a reason"
            }
        );
    }

    fn to_json(&self) -> String {
        let arr = |v: &[Def]| {
            v.iter()
                .map(|d| {
                    format!(
                        "{{\"file\":{},\"kind\":\"{}\",\"name\":{},\"line\":{}}}",
                        jstr(&d.0),
                        d.1,
                        jstr(&d.2),
                        d.3
                    )
                })
                .collect::<Vec<_>>()
                .join(",")
        };
        let drops = self
            .whole_file_drops
            .iter()
            .map(|f| jstr(f))
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "{{\"lang\":{},\"oracle\":{},\"tt_total\":{},\"truth_total\":{},\"missed_count\":{},\"extra_count\":{},\"whole_file_drops\":[{}],\"missed\":[{}],\"extra\":[{}],\"clean\":{}}}",
            jstr(&self.lang),
            jstr(&self.oracle),
            self.tt_total,
            self.truth_total,
            self.missed.len(),
            self.extra.len(),
            drops,
            arr(&self.missed),
            arr(&self.extra),
            self.clean(),
        )
    }
}

// --- tiny helpers (std-only, no JSON dep) ----------------------------------

/// Extract a string field value that follows `key` (which includes the opening
/// quote), up to the next unescaped `"`.
fn field(line: &str, key: &str) -> Option<String> {
    let start = line.find(key)? + key.len();
    let rest = &line[start..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

/// Extract a numeric field value that follows `key` (e.g. `"line":`).
fn num_field(line: &str, key: &str) -> Option<u32> {
    let start = line.find(key)? + key.len();
    let rest = &line[start..];
    let end = rest
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(rest.len());
    rest[..end].parse::<u32>().ok()
}

/// Whitespace-tolerant JSON string-field reader (`"key": "value"` or
/// `"key":"value"`). `key` is the bare field name. Used for pretty-printed ctags
/// JSON, where the compact `field`/`num_field` readers do not match.
fn jfield(line: &str, key: &str) -> Option<String> {
    let pat = format!("\"{key}\"");
    let i = line.find(&pat)? + pat.len();
    let rest = line[i..].trim_start().strip_prefix(':')?.trim_start();
    let rest = rest.strip_prefix('"')?;
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

/// Whitespace-tolerant JSON numeric-field reader.
fn jnum(line: &str, key: &str) -> Option<u32> {
    let pat = format!("\"{key}\"");
    let i = line.find(&pat)? + pat.len();
    let rest = line[i..].trim_start().strip_prefix(':')?.trim_start();
    let end = rest
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(rest.len());
    rest[..end].parse::<u32>().ok()
}

/// Minimal JSON string encoder (quotes + backslash + control chars).
fn jstr(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
