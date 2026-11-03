//! Std-only `.gitignore` matcher for the pipeline walk (TT bead ei8).
//!
//! Untracked build outputs sitting on disk (`docs-site/out` minified JS, .NET
//! `bin`/`obj`, coverage dumps) must not be swept into analysis: they corrupt
//! file counts, error-byte stats, and every derived ontology view. The repo
//! itself already declares what is not source — its `.gitignore` — so the walk
//! respects that declaration instead of hard-coding guesses like `dist`/`build`
//! (which are real source directories in the wild).
//!
//! Scope — the common subset of the gitignore syntax, deliberately:
//! - blank lines and `#` comments are skipped
//! - `!` negation with last-match-wins evaluation
//! - trailing `/` marks a directory-only pattern
//! - a `/` anywhere else anchors the pattern to the `.gitignore`'s directory;
//!   patterns without `/` match the basename at any depth below it
//! - `*` (any run of non-separator chars), `?` (one non-separator char), and
//!   `**` (any number of whole path segments) globs
//! - `.gitignore` files layer: the repo root's rules apply everywhere, a
//!   subdirectory's rules apply beneath it and take precedence (evaluated
//!   later, so they win ties)
//!
//! Known, documented divergences from git (all conservative):
//! - character classes (`[abc]`) and backslash escapes are matched literally
//! - tracked-but-ignored files are excluded here (git keeps tracking them);
//!   `--no-ignore` restores the old walk for anyone who wants everything
//! - `$GIT_DIR/info/exclude` and the user's global excludes file are not read:
//!   analysis must be a deterministic function of the analyzed tree alone
//! - a directory excluded by a pattern is not descended into, so a negation
//!   inside it cannot re-include (this one matches git's behavior exactly)

/// One parsed gitignore rule.
#[derive(Debug)]
struct Rule {
    /// `!pattern` — a match *un*-ignores (last match wins).
    negated: bool,
    /// Trailing `/` — matches directories only.
    dir_only: bool,
    /// Pattern contained a non-trailing `/` — anchored to the layer's dir.
    anchored: bool,
    /// Pattern split on `/`; a `**` segment matches any number of segments.
    segments: Vec<String>,
}

/// The rules of one `.gitignore` file, tagged with the component depth of the
/// directory that contains it (0 = the analysis root).
struct Layer {
    depth: usize,
    rules: Vec<Rule>,
}

/// The stack of `.gitignore` layers along the current walk path, root first.
/// Push a layer entering a directory, pop it leaving; deeper layers are
/// evaluated later so they override shallower ones, like git.
#[derive(Default)]
pub struct IgnoreStack {
    layers: Vec<Layer>,
}

impl IgnoreStack {
    pub fn new() -> Self {
        Self::default()
    }

    /// Load `dir/.gitignore` (if present and readable) as the layer for the
    /// directory at component `depth`. Returns whether a layer was pushed, so
    /// the walker knows to pop it on the way out. Unreadable files are treated
    /// as absent — ignoring must never fail an analysis.
    pub fn push_dir(&mut self, dir: &std::path::Path, depth: usize) -> bool {
        let Ok(text) = std::fs::read_to_string(dir.join(".gitignore")) else {
            return false;
        };
        let rules: Vec<Rule> = text.lines().filter_map(parse_line).collect();
        if rules.is_empty() {
            return false;
        }
        self.layers.push(Layer { depth, rules });
        true
    }

    /// Pop the most recently pushed layer (call iff `push_dir` returned true).
    pub fn pop_dir(&mut self) {
        self.layers.pop();
    }

    /// Is the entry at `rel` (path components relative to the analysis root)
    /// ignored? Rules are evaluated root layer first, in file order, and the
    /// last matching rule wins — a later `!pattern` re-includes.
    pub fn is_ignored(&self, rel: &[&str], is_dir: bool) -> bool {
        let mut ignored = false;
        for layer in &self.layers {
            let sub = &rel[layer.depth..];
            for rule in &layer.rules {
                if rule.matches(sub, is_dir) {
                    ignored = !rule.negated;
                }
            }
        }
        ignored
    }
}

impl Rule {
    fn matches(&self, rel: &[&str], is_dir: bool) -> bool {
        if self.dir_only && !is_dir {
            return false;
        }
        if self.anchored {
            match_segments(&self.segments, rel)
        } else {
            // No `/`: a single-segment pattern matching the basename at any
            // depth (parents were already tested when the walk visited them).
            rel.last()
                .is_some_and(|base| glob_match(&self.segments[0], base))
        }
    }
}

/// Parse one `.gitignore` line into a rule; `None` for blanks and comments.
fn parse_line(line: &str) -> Option<Rule> {
    let line = line.strip_suffix('\r').unwrap_or(line);
    if line.is_empty() || line.starts_with('#') {
        return None;
    }
    let (negated, rest) = match line.strip_prefix('!') {
        Some(r) => (true, r),
        None => (false, line),
    };
    // Git drops unescaped trailing spaces; escapes are out of subset, so all
    // trailing whitespace is dropped.
    let rest = rest.trim_end();
    let (dir_only, rest) = match rest.strip_suffix('/') {
        Some(r) => (true, r),
        None => (false, rest),
    };
    // Any remaining `/` — leading or interior — anchors the pattern to the
    // `.gitignore`'s own directory (decided BEFORE stripping the leading one).
    let anchored = rest.contains('/');
    let rest = rest.strip_prefix('/').unwrap_or(rest);
    if rest.is_empty() {
        return None;
    }
    let segments = rest.split('/').map(str::to_string).collect();
    Some(Rule {
        negated,
        dir_only,
        anchored,
        segments,
    })
}

/// Match one repository-relative path with the same documented glob subset used
/// by the pipeline's gitignore rules. Directory-only patterns match files below
/// the named directory; negation has no special meaning to exclusion-list
/// callers because they are asking whether the pattern itself matches.
pub(super) fn path_matches(pattern: &str, path: &str) -> bool {
    let Some(rule) = parse_line(pattern) else {
        return false;
    };
    let normalized = path.replace('\\', "/");
    let segments: Vec<&str> = normalized
        .trim_matches('/')
        .split('/')
        .filter(|segment| !segment.is_empty())
        .collect();
    if rule.matches(&segments, false) {
        return true;
    }
    rule.dir_only && (1..segments.len()).any(|length| rule.matches(&segments[..length], true))
}

/// Match pattern segments against path segments; `**` spans zero or more
/// whole segments, every other segment is a within-segment glob.
fn match_segments(pat: &[String], path: &[&str]) -> bool {
    let Some((head, rest)) = pat.split_first() else {
        return path.is_empty();
    };
    if head == "**" {
        (0..=path.len()).any(|k| match_segments(rest, &path[k..]))
    } else {
        path.split_first()
            .is_some_and(|(p, pr)| glob_match(head, p) && match_segments(rest, pr))
    }
}

/// Classic iterative wildcard match: `*` any run of chars, `?` one char.
/// Everything else (including `[`, `]`, `\`) is literal — documented subset.
fn glob_match(pattern: &str, text: &str) -> bool {
    let p: Vec<char> = pattern.chars().collect();
    let t: Vec<char> = text.chars().collect();
    let (mut pi, mut ti) = (0usize, 0usize);
    let mut star: Option<(usize, usize)> = None; // (pattern idx of `*`, text mark)
    while ti < t.len() {
        if pi < p.len() && (p[pi] == '?' || p[pi] == t[ti]) {
            pi += 1;
            ti += 1;
        } else if pi < p.len() && p[pi] == '*' {
            star = Some((pi, ti));
            pi += 1;
        } else if let Some((sp, mark)) = star {
            pi = sp + 1;
            ti = mark + 1;
            star = Some((sp, mark + 1));
        } else {
            return false;
        }
    }
    p[pi..].iter().all(|&c| c == '*')
}

#[cfg(test)]
mod tests {
    use super::*;

    fn stack_of(rules: &str) -> IgnoreStack {
        let mut s = IgnoreStack::new();
        s.layers.push(Layer {
            depth: 0,
            rules: rules.lines().filter_map(parse_line).collect(),
        });
        s
    }

    #[test]
    fn literal_basename_matches_at_any_depth() {
        let s = stack_of("out\n");
        assert!(s.is_ignored(&["out"], true));
        assert!(s.is_ignored(&["docs-site", "out"], true));
        assert!(s.is_ignored(&["a", "b", "out"], false)); // files too
        assert!(!s.is_ignored(&["outer"], true));
    }

    #[test]
    fn dir_suffix_matches_directories_only() {
        let s = stack_of("out/\n");
        assert!(s.is_ignored(&["docs-site", "out"], true));
        assert!(!s.is_ignored(&["docs-site", "out"], false));
    }

    #[test]
    fn slash_anchors_to_the_layer_root() {
        let s = stack_of("/target\ndocs-site/out/\n");
        assert!(s.is_ignored(&["target"], true));
        assert!(!s.is_ignored(&["sub", "target"], true));
        assert!(s.is_ignored(&["docs-site", "out"], true));
        assert!(!s.is_ignored(&["other", "docs-site", "out"], true));
    }

    #[test]
    fn star_globs_within_a_segment() {
        let s = stack_of("*.min.js\nbuild-*/\n");
        assert!(s.is_ignored(&["assets", "app.min.js"], false));
        assert!(!s.is_ignored(&["assets", "app.js"], false));
        assert!(s.is_ignored(&["build-release"], true));
        assert!(!s.is_ignored(&["build-release"], false));
    }

    #[test]
    fn question_mark_matches_one_char() {
        let s = stack_of("v?.rs\n");
        assert!(s.is_ignored(&["v1.rs"], false));
        assert!(!s.is_ignored(&["v12.rs"], false));
    }

    #[test]
    fn double_star_spans_segments() {
        let s = stack_of("a/**/b\n**/gen\nlogs/**\n");
        assert!(s.is_ignored(&["a", "b"], true));
        assert!(s.is_ignored(&["a", "x", "y", "b"], false));
        assert!(s.is_ignored(&["deep", "gen"], true));
        assert!(s.is_ignored(&["gen"], true));
        assert!(s.is_ignored(&["logs", "x", "t.log"], false));
    }

    #[test]
    fn negation_last_match_wins() {
        let s = stack_of("*.js\n!keep.js\n");
        assert!(s.is_ignored(&["app.js"], false));
        assert!(!s.is_ignored(&["src", "keep.js"], false));
        // Order matters: a later broad rule re-ignores.
        let s = stack_of("!keep.js\n*.js\n");
        assert!(s.is_ignored(&["keep.js"], false));
    }

    #[test]
    fn comments_blanks_and_bare_slash_are_inert() {
        let s = stack_of("# comment\n\n/\n!\n");
        assert!(!s.is_ignored(&["anything"], false));
    }

    #[test]
    fn deeper_layers_override_shallower_ones() {
        let mut s = stack_of("*.snap\n");
        s.layers.push(Layer {
            depth: 1,
            rules: "!golden.snap\n".lines().filter_map(parse_line).collect(),
        });
        // Root layer ignores all .snap; the depth-1 layer re-includes one
        // name beneath its own directory.
        assert!(s.is_ignored(&["other.snap"], false));
        assert!(!s.is_ignored(&["tests", "golden.snap"], false));
    }

    #[test]
    fn crlf_lines_parse_like_lf() {
        let s = stack_of("out/\r\n*.min.js\r\n");
        assert!(s.is_ignored(&["out"], true));
        assert!(s.is_ignored(&["a.min.js"], false));
    }

    #[test]
    fn exclusion_path_match_uses_gitignore_glob_subset() {
        assert!(path_matches("README.md", "docs/README.md"));
        assert!(path_matches("docs/**/*.md", "docs/api/reference.md"));
        assert!(path_matches("generated/", "generated/deep/data.txt"));
        assert!(!path_matches("README.md", "docs/README.rst"));
        assert!(!path_matches("docs/*.md", "other/docs/page.md"));
    }
}
