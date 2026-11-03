//! Project/solution topology for .NET repositories.
//!
//! A large .NET solution is organized around *projects* (`.csproj`), not
//! files: the service map ("what are the projects and how do they depend on
//! each other") is the single most useful orientation artifact for such a
//! repo. This module walks a root for `*.csproj` files, hand-parses the
//! simple MSBuild XML (std-only, no XML crate), and produces a deterministic
//! [`ProjectGraph`] with per-project metadata plus the project→project
//! dependency edges derived from `<ProjectReference>` items.
//!
//! Parsing approach: csproj files are trivially regular XML —
//! `<Project ...>` containing `<PropertyGroup>` scalars and `<ItemGroup>`
//! items whose payload lives in the `Include="..."` attribute. We strip the
//! UTF-8 BOM and XML comments, then scan for the three shapes we care about:
//! `<TargetFramework(s)>` element text, and the `Include` attribute of
//! `<ProjectReference>` / `<PackageReference>` tags. `ProjectReference`
//! paths use Windows `\` separators and are resolved lexically against the
//! csproj's directory; the referenced project's *name* is the `.csproj`
//! file stem.

use std::collections::BTreeSet;
use std::path::Path;

/// One `.csproj` project discovered under the analyzed root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Project {
    /// The csproj filename stem, e.g. `Ordering.API`.
    pub name: String,
    /// Root-relative path to the `.csproj` file, `/`-separated.
    pub rel_path: String,
    /// Root-relative directory containing the csproj (`""` for the root).
    pub dir: String,
    /// `<TargetFramework>` (or `<TargetFrameworks>`) value; `""` when the
    /// csproj does not declare one (e.g. inherited from Directory.Build.props).
    pub target_framework: String,
    /// Names of projects referenced via `<ProjectReference>`, sorted, deduped.
    pub project_refs: Vec<String>,
    /// NuGet package names referenced via `<PackageReference>`, sorted, deduped.
    pub package_refs: Vec<String>,
}

/// The set of projects in a repository plus derived topology helpers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectGraph {
    /// All discovered projects, sorted by name then rel_path.
    pub projects: Vec<Project>,
}

impl ProjectGraph {
    /// The project whose directory is the nearest ancestor of `file_rel`
    /// (a root-relative, `/`-separated file path). Ties cannot occur:
    /// directories are unique per project location, and the deepest
    /// (longest) matching directory wins.
    pub fn owning_project(&self, file_rel: &str) -> Option<&Project> {
        let file_rel = file_rel.trim_start_matches('/');
        let mut best: Option<&Project> = None;
        for p in &self.projects {
            let matches = if p.dir.is_empty() {
                true
            } else {
                file_rel.starts_with(&p.dir) && file_rel[p.dir.len()..].starts_with('/')
            };
            if matches {
                let better = match best {
                    None => true,
                    Some(b) => p.dir.len() > b.dir.len(),
                };
                if better {
                    best = Some(p);
                }
            }
        }
        best
    }

    /// A readable service map: one line per project (name, target framework,
    /// directory, package count) with its project references, followed by
    /// the flat project→project dependency edge list. Deterministic.
    pub fn topo_summary(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("projects ({}):\n", self.projects.len()));
        for p in &self.projects {
            let tfm = if p.target_framework.is_empty() {
                "-".to_string()
            } else {
                p.target_framework.clone()
            };
            out.push_str(&format!(
                "  {}  [{}]  {}  ({} packages)\n",
                p.name,
                tfm,
                if p.dir.is_empty() { "." } else { &p.dir },
                p.package_refs.len()
            ));
            if !p.project_refs.is_empty() {
                out.push_str(&format!("    -> {}\n", p.project_refs.join(", ")));
            }
        }
        let mut edges: Vec<(String, String)> = Vec::new();
        for p in &self.projects {
            for r in &p.project_refs {
                edges.push((p.name.clone(), r.clone()));
            }
        }
        edges.sort();
        edges.dedup();
        out.push_str(&format!("edges ({}):\n", edges.len()));
        for (from, to) in &edges {
            out.push_str(&format!("  {} -> {}\n", from, to));
        }
        out
    }
}

/// Walk `root` for `*.csproj` files (skipping `obj/`, `bin/`, and hidden
/// directories), parse each, and return the deterministic project graph.
/// Unreadable files or directories are skipped silently.
pub fn analyze(root: &Path) -> ProjectGraph {
    let mut csprojs: Vec<std::path::PathBuf> = Vec::new();
    walk_csprojs(root, &mut csprojs);
    csprojs.sort();

    let mut projects: Vec<Project> = Vec::new();
    for path in &csprojs {
        let Ok(raw) = std::fs::read_to_string(path) else {
            continue;
        };
        let text = strip_comments(raw.trim_start_matches('\u{feff}'));

        let name = path
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_default();
        let rel_path = rel_slash_path(root, path);
        let dir = match rel_path.rfind('/') {
            Some(i) => rel_path[..i].to_string(),
            None => String::new(),
        };

        let target_framework = element_text(&text, "TargetFramework")
            .or_else(|| element_text(&text, "TargetFrameworks"))
            .unwrap_or_default();

        let mut project_refs: BTreeSet<String> = BTreeSet::new();
        for include in tag_includes(&text, "ProjectReference") {
            if let Some(stem) = csproj_stem(&include) {
                project_refs.insert(stem);
            }
        }
        let package_refs: BTreeSet<String> = tag_includes(&text, "PackageReference")
            .into_iter()
            .collect();

        projects.push(Project {
            name,
            rel_path,
            dir,
            target_framework,
            project_refs: project_refs.into_iter().collect(),
            package_refs: package_refs.into_iter().collect(),
        });
    }

    projects.sort_by(|a, b| {
        a.name
            .cmp(&b.name)
            .then_with(|| a.rel_path.cmp(&b.rel_path))
    });
    ProjectGraph { projects }
}

/// Recursively collect `*.csproj` paths, skipping `obj`, `bin`, and dot-dirs.
fn walk_csprojs(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let file_name = entry.file_name();
        let name = file_name.to_string_lossy();
        let Ok(file_type) = entry.file_type() else {
            continue;
        };
        if file_type.is_dir() {
            let lower = name.to_ascii_lowercase();
            if lower == "obj" || lower == "bin" || name.starts_with('.') {
                continue;
            }
            walk_csprojs(&path, out);
        } else if file_type.is_file() && name.ends_with(".csproj") {
            out.push(path);
        }
    }
}

/// Root-relative `/`-separated path (falls back to the full path if `path`
/// is not under `root`).
fn rel_slash_path(root: &Path, path: &Path) -> String {
    let rel = path.strip_prefix(root).unwrap_or(path);
    let mut s = String::new();
    for comp in rel.components() {
        if !s.is_empty() {
            s.push('/');
        }
        s.push_str(&comp.as_os_str().to_string_lossy());
    }
    s
}

/// Remove `<!-- ... -->` comment spans so commented-out items are ignored.
fn strip_comments(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("<!--") {
        out.push_str(&rest[..start]);
        match rest[start + 4..].find("-->") {
            Some(end) => rest = &rest[start + 4 + end + 3..],
            None => return out, // unterminated comment: drop the tail
        }
    }
    out.push_str(rest);
    out
}

/// The trimmed text of the first `<name>...</name>` element, if any.
fn element_text(text: &str, name: &str) -> Option<String> {
    let open = format!("<{}>", name);
    let close = format!("</{}>", name);
    let start = text.find(&open)? + open.len();
    let end = text[start..].find(&close)? + start;
    let value = text[start..end].trim();
    if value.is_empty() {
        None
    } else {
        Some(value.to_string())
    }
}

/// `Include` attribute values of every `<tag ...>` occurrence, in document
/// order (duplicates preserved; callers dedupe).
fn tag_includes(text: &str, tag: &str) -> Vec<String> {
    let needle = format!("<{}", tag);
    let mut out = Vec::new();
    let mut pos = 0;
    while let Some(found) = text[pos..].find(&needle) {
        let tag_start = pos + found + needle.len();
        // Must be a real tag boundary (`<ProjectReference ` not `<ProjectReferenceX`).
        let boundary = text[tag_start..]
            .chars()
            .next()
            .is_some_and(|c| c.is_whitespace() || c == '>' || c == '/');
        let tag_end = match text[tag_start..].find('>') {
            Some(i) => tag_start + i,
            None => break,
        };
        if boundary {
            if let Some(value) = attr_value(&text[tag_start..tag_end], "Include") {
                out.push(value);
            }
        }
        pos = tag_end + 1;
    }
    out
}

/// The value of `name="..."` (or `name='...'`) inside a tag's attribute text.
fn attr_value(tag_body: &str, name: &str) -> Option<String> {
    let mut pos = 0;
    while let Some(found) = tag_body[pos..].find(name) {
        let at = pos + found;
        // Attribute name must start at a word boundary.
        let starts_clean = at == 0
            || tag_body[..at]
                .chars()
                .next_back()
                .is_some_and(|c| c.is_whitespace());
        let rest = tag_body[at + name.len()..].trim_start();
        if starts_clean {
            if let Some(rest) = rest.strip_prefix('=') {
                let rest = rest.trim_start();
                let quote = rest.chars().next()?;
                if quote == '"' || quote == '\'' {
                    let inner = &rest[1..];
                    let end = inner.find(quote)?;
                    return Some(inner[..end].to_string());
                }
            }
        }
        pos = at + name.len();
    }
    None
}

/// The project name for a `ProjectReference Include` path: normalize `\` to
/// `/` and take the `.csproj` file stem.
fn csproj_stem(include: &str) -> Option<String> {
    let normalized = include.replace('\\', "/");
    let file = normalized.rsplit('/').next()?;
    let stem = file.strip_suffix(".csproj")?;
    if stem.is_empty() {
        None
    } else {
        Some(stem.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    /// A unique per-test temp dir under the system temp root.
    fn tmp_dir(label: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "tt_brief_projects_{}_{}",
            label,
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create tmp dir");
        dir
    }

    fn write(root: &Path, rel: &str, content: &str) {
        let path = root.join(rel);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, content).unwrap();
    }

    #[test]
    fn parses_projects_refs_and_edges() {
        let root = tmp_dir("unit");

        // BOM + CRLF + backslash ProjectReference paths, like real csproj.
        write(
            &root,
            "src/Alpha.API/Alpha.API.csproj",
            "\u{feff}<Project Sdk=\"Microsoft.NET.Sdk.Web\">\r\n\
             <PropertyGroup>\r\n<TargetFramework>net10.0</TargetFramework>\r\n</PropertyGroup>\r\n\
             <ItemGroup>\r\n\
             <ProjectReference Include=\"..\\Alpha.Domain\\Alpha.Domain.csproj\" />\r\n\
             <ProjectReference Include=\"..\\Shared.Bus\\Shared.Bus.csproj\" />\r\n\
             <!-- <ProjectReference Include=\"..\\Ghost\\Ghost.csproj\" /> -->\r\n\
             <PackageReference Include=\"FluentValidation\" />\r\n\
             <PackageReference Include='Asp.Versioning.Http' />\r\n\
             </ItemGroup>\r\n</Project>\r\n",
        );
        write(
            &root,
            "src/Alpha.Domain/Alpha.Domain.csproj",
            "<Project Sdk=\"Microsoft.NET.Sdk\">\n\
             <PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>\n\
             </Project>\n",
        );
        write(
            &root,
            "src/Shared.Bus/Shared.Bus.csproj",
            "<Project Sdk=\"Microsoft.NET.Sdk\">\n\
             <ItemGroup>\n\
             <ProjectReference Include=\"../Alpha.Domain/Alpha.Domain.csproj\"/>\n\
             <PackageReference Include=\"Microsoft.Extensions.Options\">\n\
               <PrivateAssets>all</PrivateAssets>\n\
             </PackageReference>\n\
             </ItemGroup>\n</Project>\n",
        );
        // Must be skipped: build output copies.
        write(
            &root,
            "src/Alpha.API/obj/Alpha.Copy.csproj",
            "<Project><ItemGroup><ProjectReference Include=\"x\\X.csproj\"/></ItemGroup></Project>",
        );
        write(
            &root,
            "src/Alpha.API/bin/Debug/Bin.Copy.csproj",
            "<Project/>",
        );

        let graph = analyze(&root);

        let names: Vec<&str> = graph.projects.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(names, vec!["Alpha.API", "Alpha.Domain", "Shared.Bus"]);

        let api = &graph.projects[0];
        assert_eq!(api.rel_path, "src/Alpha.API/Alpha.API.csproj");
        assert_eq!(api.dir, "src/Alpha.API");
        assert_eq!(api.target_framework, "net10.0");
        assert_eq!(api.project_refs, vec!["Alpha.Domain", "Shared.Bus"]);
        assert_eq!(
            api.package_refs,
            vec!["Asp.Versioning.Http", "FluentValidation"]
        );

        let domain = &graph.projects[1];
        assert!(domain.project_refs.is_empty());
        assert!(domain.package_refs.is_empty());

        let bus = &graph.projects[2];
        assert_eq!(bus.project_refs, vec!["Alpha.Domain"]);
        assert_eq!(bus.package_refs, vec!["Microsoft.Extensions.Options"]);
        assert_eq!(bus.target_framework, ""); // none declared

        // owning_project: nearest ancestor directory wins.
        let owner = graph
            .owning_project("src/Alpha.API/Apis/OrdersApi.cs")
            .expect("owner");
        assert_eq!(owner.name, "Alpha.API");
        assert!(graph.owning_project("src/Unrelated/Program.cs").is_none());
        assert!(graph.owning_project("src/Alpha.APIx/Program.cs").is_none());

        // topo_summary contains the projects and the deduped edge list.
        let summary = graph.topo_summary();
        assert!(summary.contains("projects (3):"));
        assert!(summary.contains("Alpha.API  [net10.0]  src/Alpha.API  (2 packages)"));
        assert!(summary.contains("edges (3):"));
        assert!(summary.contains("Alpha.API -> Alpha.Domain"));
        assert!(summary.contains("Alpha.API -> Shared.Bus"));
        assert!(summary.contains("Shared.Bus -> Alpha.Domain"));
        assert!(!summary.contains("Ghost")); // commented-out ref ignored

        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn eshop_integration_project_map() {
        let root = Path::new(
            "/private/tmp/claude-501/-Users-jag/e05fd682-3a3e-4c4f-8cb7-f66d17e5c3ac/scratchpad/eShop",
        );
        if !root.is_dir() {
            eprintln!("skipping eshop_integration_project_map: fixture not present");
            return;
        }

        let graph = analyze(root);
        let names: Vec<&str> = graph.projects.iter().map(|p| p.name.as_str()).collect();

        for expected in [
            "Catalog.API",
            "Ordering.API",
            "Ordering.Domain",
            "Ordering.Infrastructure",
            "Basket.API",
            "Identity.API",
            "EventBus",
        ] {
            assert!(names.contains(&expected), "missing project {expected}");
        }

        let ordering_api = graph
            .projects
            .iter()
            .find(|p| p.name == "Ordering.API")
            .expect("Ordering.API");
        assert!(ordering_api
            .project_refs
            .iter()
            .any(|r| r == "Ordering.Domain"));
        assert!(ordering_api
            .project_refs
            .iter()
            .any(|r| r == "Ordering.Infrastructure"));

        // owning_project on a real service file.
        let owner = graph
            .owning_project("src/Ordering.API/Program.cs")
            .expect("owner");
        assert_eq!(owner.name, "Ordering.API");

        println!("{}", graph.topo_summary());
    }
}
