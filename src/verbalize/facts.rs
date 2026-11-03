//! Fact extraction for the verbalizer (V1, epic E-V): read-only consumption
//! of the passes the crate already computes, projected into the typed fact
//! structs the templates render.
//!
//! Single sources of truth, never re-derivations:
//! - domains + inter-domain mass: [`assign_domains`]
//! - unit/layer placement: [`assign_layers`]
//! - archetypes: [`classify_with`] over the built-in [`RULES`]
//! - layer violations: [`violations_report`]
//! - blast radius: [`blast_radius_set`] (the `query blast-radius` machinery)
//! - file ownership: the same containment walk `explain`/`nav` use
//!
//! The only tallies computed here are the ones no pass exposes publicly:
//! distinct-neighbor fan-in/fan-out per node, the chief target unit per
//! domain pair, and the file-level dependency cycles (iterative Tarjan,
//! structurally mirroring `brief`'s). Everything iterates `BTreeMap`s and
//! breaks ties lexicographically, so the extraction is a pure, deterministic
//! function of the analysis.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::json::Json;
use crate::extract::archetypes::{classify_with, SymbolFacts, RULES};
use crate::extract::domains::{assign_domains, KIND_BUSINESS};
use crate::extract::layers::assign_layers;
use crate::graph::{Graph, GraphNode};
use crate::ir::ontology::{node as ont, parent_relation, relation};
use crate::pipeline::Analysis;
use crate::query::blast_radius_set;
use crate::violations::violations_report;

/// How many nodes each hotspot ranking (fan-in, fan-out) contributes to the
/// verbalized symbol set. Counts stay exact; only the selection is capped.
const HOTSPOT_N: usize = 8;

/// How many named dependents each [`SymbolFact`] carries, ranked by the
/// dependent's own fan-in (centrality proxy) descending, id ascending. The
/// count stays exact in [`SymbolFact::fan_in`]; only the naming is capped.
const DEPENDENT_N: usize = 8;

/// Node kinds that count as project symbols for hotspot selection and the
/// symbol totals. Placeholders (`UnresolvedSymbol`, `ExternalDependency`)
/// and `File`/`Package` containers are not hotspot material.
const SYMBOL_KINDS: &[&str] = &[
    ont::FUNCTION,
    ont::TYPE,
    ont::MODULE,
    ont::CONSTANT,
    ont::MACRO,
];

/// Whole-graph and coverage numbers (every denominator the templates need).
#[derive(Clone, Debug, Default)]
pub struct Totals {
    /// All graph nodes.
    pub nodes: u64,
    /// All graph edges.
    pub edges: u64,
    /// `File` nodes.
    pub files: u64,
    /// Nodes of a [`SYMBOL_KINDS`] kind.
    pub symbols: u64,
    /// Source files discovered by the pipeline.
    pub discovered_files: u64,
    /// Discovered files whose parse failed.
    pub parse_failures: u64,
    /// Total cross-domain DEPENDS-family edge mass.
    pub domain_references: u64,
    /// Total layer-violating edge mass.
    pub violation_edges: u64,
}

/// One recovered business domain (clustered code), value-ranked.
#[derive(Clone, Debug)]
pub struct DomainFact {
    pub name: String,
    pub files: u64,
    pub symbols: u64,
}

/// One infrastructure group (deterministic path classification).
#[derive(Clone, Debug)]
pub struct GroupFact {
    pub name: String,
    pub files: u64,
}

/// One counted inter-domain dependency, with its chief target unit.
#[derive(Clone, Debug)]
pub struct DepFact {
    pub from: String,
    pub to: String,
    pub references: u64,
    /// The unit on the `to` side receiving the most of this pair's edges.
    pub chief_unit: Option<String>,
}

/// One named dependent of a symbol: a node with a DEPENDS-family edge into
/// it. Carries exactly what the `dependent_edge` template renders.
#[derive(Clone, Debug)]
pub struct DependentFact {
    pub name: String,
    pub kind: &'static str,
    /// Dependent's owning file path; empty when unknown.
    pub path: String,
}

/// One hotspot symbol: identity, classification, and connectivity.
#[derive(Clone, Debug)]
pub struct SymbolFact {
    pub id: String,
    pub name: String,
    pub kind: &'static str,
    /// Owning file path; empty when unknown.
    pub path: String,
    /// 1-based source line; 0 when unknown.
    pub line: u64,
    pub domain: String,
    pub layer: String,
    pub archetype: &'static str,
    /// Distinct DEPENDS-family dependents.
    pub fan_in: u64,
    /// Distinct DEPENDS-family dependencies.
    pub fan_out: u64,
    /// Transitive reverse-reachability set size.
    pub blast: u64,
    /// The top [`DEPENDENT_N`] dependents by name (dependent fan-in desc,
    /// id asc). `fan_in` is the exact total; the rest are unnamed.
    pub dependents: Vec<DependentFact>,
}

/// One `main`-named Function (an entry point).
#[derive(Clone, Debug)]
pub struct EntryFact {
    pub name: String,
    pub kind: &'static str,
    pub path: String,
}

/// One recovered workflow (`flow` Function node).
#[derive(Clone, Debug)]
pub struct FlowFact {
    pub name: String,
    pub depth: u64,
    pub elements: u64,
}

/// One layer-direction violation at unit grain.
#[derive(Clone, Debug)]
pub struct ViolationFact {
    pub from_unit: String,
    pub from_layer: String,
    pub to_unit: String,
    pub to_layer: String,
    pub violations: u64,
}

/// Every fact the verbalizer states, extracted once per analysis.
#[derive(Clone, Debug, Default)]
pub struct Facts {
    pub totals: Totals,
    /// Business domains, value-ranked (symbols desc, files desc, name asc):
    /// the D-handle assignment order.
    pub domains: Vec<DomainFact>,
    /// Infrastructure groups, ranked (files desc, name asc).
    pub groups: Vec<GroupFact>,
    /// Inter-domain dependencies, ordered by (from-rank, to-rank); pairs
    /// whose `from` is a group follow all business-domain pairs.
    pub deps: Vec<DepFact>,
    /// Hotspot symbols, value-ranked (fan-in desc, fan-out desc, id asc):
    /// the F-handle assignment order.
    pub symbols: Vec<SymbolFact>,
    /// Entry points, ordered by id.
    pub entries: Vec<EntryFact>,
    /// Flows, ordered by (depth desc, id asc).
    pub flows: Vec<FlowFact>,
    /// Layer violations, worst-first (the `violations` report order).
    pub violations: Vec<ViolationFact>,
    /// File-level dependency cycles: member paths sorted, list sorted.
    pub cycles: Vec<Vec<String>>,
}

/// Extract every fact family from one analysis. Pure and deterministic:
/// same analysis, same facts.
pub fn extract(analysis: &Analysis) -> Facts {
    let graph = &analysis.graph;
    let domains = assign_domains(graph);
    let layers = assign_layers(graph);
    let file_of = crate::explain::file_of_map(graph);
    let by_id: BTreeMap<&str, &GraphNode> = graph.nodes().map(|n| (n.id.as_str(), n)).collect();

    // File node id → source path.
    let mut path_of: BTreeMap<&str, &str> = BTreeMap::new();
    for n in graph.nodes().filter(|n| n.kind == ont::FILE) {
        if let Some(Json::Str(p)) = n.props.get("path") {
            path_of.insert(n.id.as_str(), p.as_str());
        }
    }
    let owning_file = |id: &str| -> Option<&str> {
        if by_id.get(id).map(|n| n.kind) == Some(ont::FILE) {
            Some(by_id[id].id.as_str())
        } else {
            file_of.get(id).copied()
        }
    };

    // One pass over DEPENDS-family edges: distinct-neighbor fan maps, the
    // chief target unit per domain pair, and the file-level dependency graph.
    let mut incoming: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let mut outgoing: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let mut chief: BTreeMap<(&str, &str), BTreeMap<&str, u64>> = BTreeMap::new();
    let mut file_deps: BTreeSet<(&str, &str)> = BTreeSet::new();
    for e in graph.edges() {
        if parent_relation(e.kind) != Some(relation::DEPENDS) {
            continue;
        }
        if e.from != e.to {
            incoming
                .entry(e.to.as_str())
                .or_default()
                .insert(e.from.as_str());
            outgoing
                .entry(e.from.as_str())
                .or_default()
                .insert(e.to.as_str());
        }
        let (Some(ff), Some(tf)) = (owning_file(e.from.as_str()), owning_file(e.to.as_str()))
        else {
            continue;
        };
        if ff != tf {
            file_deps.insert((ff, tf));
        }
        let (Some(fd), Some(td)) = (domains.file_domain.get(ff), domains.file_domain.get(tf))
        else {
            continue;
        };
        if fd != td {
            if let Some(tu) = domains.file_unit.get(tf) {
                *chief
                    .entry((fd.as_str(), td.as_str()))
                    .or_default()
                    .entry(tu.as_str())
                    .or_default() += 1;
            }
        }
    }

    // Domains and groups, value-ranked.
    let mut business: Vec<DomainFact> = Vec::new();
    let mut groups: Vec<GroupFact> = Vec::new();
    for (name, info) in &domains.domains {
        if info.kind == KIND_BUSINESS {
            business.push(DomainFact {
                name: name.clone(),
                files: info.file_count,
                symbols: info.symbol_count,
            });
        } else {
            groups.push(GroupFact {
                name: name.clone(),
                files: info.file_count,
            });
        }
    }
    business.sort_by(|a, b| {
        b.symbols
            .cmp(&a.symbols)
            .then_with(|| b.files.cmp(&a.files))
            .then_with(|| a.name.cmp(&b.name))
    });
    groups.sort_by(|a, b| b.files.cmp(&a.files).then_with(|| a.name.cmp(&b.name)));

    // Inter-domain dependencies in (from-rank, to-rank) order; group-led
    // pairs after every business-led pair.
    let rank_of = |name: &str| -> (usize, usize) {
        if let Some(i) = business.iter().position(|d| d.name == name) {
            (0, i)
        } else if let Some(i) = groups.iter().position(|g| g.name == name) {
            (1, i)
        } else {
            (2, 0)
        }
    };
    let mut deps: Vec<DepFact> = domains
        .domain_deps
        .iter()
        .map(|((from, to), refs)| {
            let chief_unit = chief.get(&(from.as_str(), to.as_str())).map(|units| {
                units
                    .iter()
                    .max_by(|a, b| a.1.cmp(b.1).then_with(|| b.0.cmp(a.0)))
                    .map(|(unit, _)| (*unit).to_string())
                    .unwrap_or_default()
            });
            DepFact {
                from: from.clone(),
                to: to.clone(),
                references: *refs,
                chief_unit: chief_unit.filter(|u| !u.is_empty()),
            }
        })
        .collect();
    deps.sort_by(|a, b| {
        (rank_of(&a.from), rank_of(&a.to), &a.from, &a.to).cmp(&(
            rank_of(&b.from),
            rank_of(&b.to),
            &b.from,
            &b.to,
        ))
    });
    let domain_references: u64 = deps.iter().map(|d| d.references).sum();

    // Hotspot symbols: internal project symbols ranked by degree.
    let degree = |map: &BTreeMap<&str, BTreeSet<&str>>, id: &str| -> u64 {
        map.get(id).map_or(0, |s| s.len() as u64)
    };
    let mut candidates: Vec<(&str, u64, u64)> = graph
        .nodes()
        .filter(|n| SYMBOL_KINDS.contains(&n.kind) && file_of.contains_key(n.id.as_str()))
        .map(|n| {
            (
                n.id.as_str(),
                degree(&incoming, &n.id),
                degree(&outgoing, &n.id),
            )
        })
        .collect();
    let mut chosen: BTreeSet<&str> = BTreeSet::new();
    candidates.sort_by(|a, b| {
        b.1.cmp(&a.1)
            .then_with(|| b.2.cmp(&a.2))
            .then_with(|| a.0.cmp(b.0))
    });
    chosen.extend(
        candidates
            .iter()
            .filter(|c| c.1 > 0)
            .take(HOTSPOT_N)
            .map(|c| c.0),
    );
    candidates.sort_by(|a, b| {
        b.2.cmp(&a.2)
            .then_with(|| b.1.cmp(&a.1))
            .then_with(|| a.0.cmp(b.0))
    });
    chosen.extend(
        candidates
            .iter()
            .filter(|c| c.2 > 0)
            .take(HOTSPOT_N)
            .map(|c| c.0),
    );

    let mut symbols: Vec<SymbolFact> = chosen
        .iter()
        .map(|id| {
            symbol_fact(
                graph, by_id[id], &by_id, &domains, &layers, &file_of, &path_of, &incoming,
                &outgoing,
            )
        })
        .collect();
    symbols.sort_by(|a, b| {
        b.fan_in
            .cmp(&a.fan_in)
            .then_with(|| b.fan_out.cmp(&a.fan_out))
            .then_with(|| a.id.cmp(&b.id))
    });

    // Entry points: `main`-named Functions, id order.
    let entries: Vec<EntryFact> = graph
        .nodes()
        .filter(|n| n.kind == ont::FUNCTION && n.name == "main")
        .map(|n| EntryFact {
            name: n.name.clone(),
            kind: n.kind,
            path: owning_file(&n.id)
                .and_then(|f| path_of.get(f))
                .map(|p| (*p).to_string())
                .unwrap_or_default(),
        })
        .collect();

    // Flows: `flow`-kind Function nodes, (depth desc, id asc).
    let mut flows: Vec<(u64, &str, FlowFact)> = graph
        .nodes()
        .filter(|n| {
            n.kind == ont::FUNCTION
                && matches!(n.props.get("type_kind"), Some(Json::Str(k)) if k == "flow")
        })
        .map(|n| {
            let depth = prop_u64(n, "depth");
            (
                depth,
                n.id.as_str(),
                FlowFact {
                    name: n.name.clone(),
                    depth,
                    elements: prop_u64(n, "element_count"),
                },
            )
        })
        .collect();
    flows.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(b.1)));
    let flows: Vec<FlowFact> = flows.into_iter().map(|(_, _, f)| f).collect();

    // Layer violations: the report's worst-first order, verbatim.
    let report = violations_report(graph);
    let violations: Vec<ViolationFact> = report
        .violations
        .iter()
        .map(|v| ViolationFact {
            from_unit: v.from_unit.clone(),
            from_layer: v.from_layer.clone(),
            to_unit: v.to_unit.clone(),
            to_layer: v.to_layer.clone(),
            violations: v.count,
        })
        .collect();

    // File-level dependency cycles (Tarjan SCCs of size > 1), as paths.
    let cycles = file_cycles(&file_deps)
        .into_iter()
        .map(|scc| {
            let mut paths: Vec<String> = scc
                .into_iter()
                .map(|f| {
                    path_of
                        .get(f)
                        .map_or_else(|| f.to_string(), |p| (*p).to_string())
                })
                .collect();
            paths.sort();
            paths
        })
        .collect::<Vec<_>>();
    let mut cycles = cycles;
    cycles.sort();

    let totals = Totals {
        nodes: graph.node_count() as u64,
        edges: graph.edge_count() as u64,
        files: graph.count_nodes_of(ont::FILE) as u64,
        symbols: SYMBOL_KINDS
            .iter()
            .map(|k| graph.count_nodes_of(k) as u64)
            .sum(),
        discovered_files: analysis.stats.files as u64,
        parse_failures: analysis.stats.parse_failures as u64,
        domain_references,
        violation_edges: report.total_edges,
    };

    Facts {
        totals,
        domains: business,
        groups,
        deps,
        symbols,
        entries,
        flows,
        violations,
        cycles,
    }
}

/// Build the [`SymbolFact`] for one resolved node (also the `--target` path).
#[allow(clippy::too_many_arguments)]
fn symbol_fact(
    graph: &Graph,
    node: &GraphNode,
    by_id: &BTreeMap<&str, &GraphNode>,
    domains: &crate::extract::domains::DomainAssignment,
    layers: &crate::extract::layers::LayerAssignment,
    file_of: &BTreeMap<&str, &str>,
    path_of: &BTreeMap<&str, &str>,
    incoming: &BTreeMap<&str, BTreeSet<&str>>,
    outgoing: &BTreeMap<&str, BTreeSet<&str>>,
) -> SymbolFact {
    let file_id: Option<&str> = if node.kind == ont::FILE {
        Some(node.id.as_str())
    } else {
        file_of.get(node.id.as_str()).copied()
    };
    let path = file_id
        .and_then(|f| path_of.get(f))
        .map(|p| (*p).to_string())
        .unwrap_or_default();
    let domain = file_id
        .and_then(|f| domains.file_domain.get(f))
        .cloned()
        .unwrap_or_else(|| "unassigned".to_string());
    let layer = file_id
        .and_then(|f| layers.file_unit.get(f))
        .and_then(|u| layers.unit_layer.get(u))
        .cloned()
        .unwrap_or_else(|| "unassigned".to_string());
    let declared_path = if path.is_empty() {
        None
    } else {
        Some(path.as_str())
    };
    SymbolFact {
        id: node.id.clone(),
        name: node.name.clone(),
        kind: node.kind,
        line: prop_u64(node, "line"),
        archetype: classify_with(RULES, &SymbolFacts::of(node, declared_path)),
        path,
        domain,
        layer,
        fan_in: incoming.get(node.id.as_str()).map_or(0, |s| s.len() as u64),
        fan_out: outgoing.get(node.id.as_str()).map_or(0, |s| s.len() as u64),
        blast: blast_radius_set(graph, std::slice::from_ref(&node.id)).len() as u64,
        dependents: top_dependents(node, by_id, file_of, path_of, incoming),
    }
}

/// The top [`DEPENDENT_N`] dependents of one node, by name: every node with
/// a distinct DEPENDS-family edge into it, ranked by the dependent's own
/// fan-in (centrality proxy) descending, id ascending — the same distinct-
/// neighbor `incoming` map that produces `fan_in`, so counts and names never
/// disagree.
fn top_dependents(
    node: &GraphNode,
    by_id: &BTreeMap<&str, &GraphNode>,
    file_of: &BTreeMap<&str, &str>,
    path_of: &BTreeMap<&str, &str>,
    incoming: &BTreeMap<&str, BTreeSet<&str>>,
) -> Vec<DependentFact> {
    let mut dep_ids: Vec<&str> = incoming
        .get(node.id.as_str())
        .map(|s| s.iter().copied().collect())
        .unwrap_or_default();
    dep_ids.sort_by(|a, b| {
        let fa = incoming.get(a).map_or(0, BTreeSet::len);
        let fb = incoming.get(b).map_or(0, BTreeSet::len);
        fb.cmp(&fa).then_with(|| a.cmp(b))
    });
    dep_ids
        .into_iter()
        .take(DEPENDENT_N)
        .filter_map(|id| by_id.get(id).copied())
        .map(|n| {
            let file_id: Option<&str> = if n.kind == ont::FILE {
                Some(n.id.as_str())
            } else {
                file_of.get(n.id.as_str()).copied()
            };
            DependentFact {
                name: n.name.clone(),
                kind: n.kind,
                path: file_id
                    .and_then(|f| path_of.get(f))
                    .map(|p| (*p).to_string())
                    .unwrap_or_default(),
            }
        })
        .collect()
}

/// Extract the full [`SymbolFact`] for one explicitly targeted node — the
/// `verbalize --target` path. Shares every convention with the hotspot set.
pub fn target_fact(analysis: &Analysis, node: &GraphNode) -> SymbolFact {
    let graph = &analysis.graph;
    let domains = assign_domains(graph);
    let layers = assign_layers(graph);
    let file_of = crate::explain::file_of_map(graph);
    let by_id: BTreeMap<&str, &GraphNode> = graph.nodes().map(|n| (n.id.as_str(), n)).collect();
    let mut path_of: BTreeMap<&str, &str> = BTreeMap::new();
    for n in graph.nodes().filter(|n| n.kind == ont::FILE) {
        if let Some(Json::Str(p)) = n.props.get("path") {
            path_of.insert(n.id.as_str(), p.as_str());
        }
    }
    let mut incoming: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let mut outgoing: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for e in graph.edges() {
        if parent_relation(e.kind) != Some(relation::DEPENDS) || e.from == e.to {
            continue;
        }
        incoming
            .entry(e.to.as_str())
            .or_default()
            .insert(e.from.as_str());
        outgoing
            .entry(e.from.as_str())
            .or_default()
            .insert(e.to.as_str());
    }
    symbol_fact(
        graph, node, &by_id, &domains, &layers, &file_of, &path_of, &incoming, &outgoing,
    )
}

fn prop_u64(node: &GraphNode, key: &str) -> u64 {
    match node.props.get(key) {
        Some(Json::U64(v)) => *v,
        Some(Json::I64(v)) if *v >= 0 => *v as u64,
        _ => 0,
    }
}

/// Strongly connected components (size > 1) of the file dependency graph,
/// iterative Tarjan — structurally the same walk `brief` uses, over the
/// same DEPENDS-family file pairs.
fn file_cycles<'g>(file_deps: &BTreeSet<(&'g str, &'g str)>) -> Vec<Vec<&'g str>> {
    let mut index_of: BTreeMap<&str, usize> = BTreeMap::new();
    for (from, to) in file_deps {
        let next = index_of.len();
        index_of.entry(from).or_insert(next);
        let next = index_of.len();
        index_of.entry(to).or_insert(next);
    }
    let n = index_of.len();
    let mut files: Vec<&str> = vec![""; n];
    for (f, i) in &index_of {
        files[*i] = f;
    }
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (from, to) in file_deps {
        adj[index_of[from]].push(index_of[to]);
    }
    for targets in &mut adj {
        targets.sort_unstable();
        targets.dedup();
    }

    const UNVISITED: usize = usize::MAX;
    let mut index = vec![UNVISITED; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut counter = 0usize;
    let mut sccs: Vec<Vec<usize>> = Vec::new();

    for start in 0..n {
        if index[start] != UNVISITED {
            continue;
        }
        let mut frames: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(frame) = frames.last_mut() {
            let (v, child) = *frame;
            if child == 0 {
                index[v] = counter;
                low[v] = counter;
                counter += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            if child < adj[v].len() {
                frame.1 += 1;
                let w = adj[v][child];
                if index[w] == UNVISITED {
                    frames.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                frames.pop();
                if let Some(&(p, _)) = frames.last() {
                    low[p] = low[p].min(low[v]);
                }
                if low[v] == index[v] {
                    let mut scc = Vec::new();
                    loop {
                        let w = stack.pop().expect("Tarjan stack underflow");
                        on_stack[w] = false;
                        scc.push(w);
                        if w == v {
                            break;
                        }
                    }
                    if scc.len() > 1 {
                        sccs.push(scc);
                    }
                }
            }
        }
    }

    let mut cycles: Vec<Vec<&str>> = sccs
        .into_iter()
        .map(|scc| {
            let mut members: Vec<&str> = scc.into_iter().map(|i| files[i]).collect();
            members.sort_unstable();
            members
        })
        .collect();
    cycles.sort();
    cycles
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::ontology::edge;

    fn file(g: &mut Graph, path: &str) -> String {
        let name = path.rsplit('/').next().unwrap().to_string();
        let id = format!("file::{path}");
        g.upsert_node(id.clone(), ont::FILE, name, vec![("path", Json::str(path))]);
        id
    }

    fn sym(g: &mut Graph, file_id: &str, kind: &'static str, name: &str) -> String {
        let id = format!("sym::{file_id}::{name}");
        g.upsert_node(id.clone(), kind, name, vec![]);
        g.add_edge(file_id.to_string(), edge::DECLARES, id.clone(), vec![]);
        id
    }

    /// Two units with a deliberate layer inversion, a hotspot, an entry
    /// point, and a two-file cycle.
    fn sample() -> Analysis {
        let mut g = Graph::new();
        let fd = file(&mut g, "src/Shop.Domain/Order.cs");
        let order = sym(&mut g, &fd, ont::TYPE, "Order");
        let fi = file(&mut g, "src/Shop.Infrastructure/Repo.cs");
        let repo = sym(&mut g, &fi, ont::TYPE, "Repo");
        let fa = file(&mut g, "src/Shop.API/Program.cs");
        let main_fn = sym(&mut g, &fa, ont::FUNCTION, "main");
        // Inversion: Domain → Infrastructure.
        g.add_edge(order.clone(), edge::USES_TYPE, repo.clone(), vec![]);
        // Clean inward edge + hotspot mass on Order.
        g.add_edge(main_fn.clone(), edge::USES_TYPE, order.clone(), vec![]);
        g.add_edge(repo.clone(), edge::USES_TYPE, order.clone(), vec![]);
        // A two-file cycle.
        g.add_edge(repo, edge::USES_TYPE, main_fn, vec![]);
        Analysis {
            graph: g,
            stats: crate::pipeline::AnalysisStats {
                files: 3,
                lossless_files: 3,
                diagnostics: 0,
                error_bytes: 0,
                total_bytes: 100,
                parse_failures: 0,
            },
        }
    }

    #[test]
    fn extracts_ranked_facts_from_a_small_graph() {
        let facts = extract(&sample());
        assert_eq!(facts.totals.files, 3);
        assert!(facts.totals.symbols >= 3);
        assert!(!facts.domains.is_empty());
        // Hotspot ranking: Order has the highest fan-in.
        assert!(!facts.symbols.is_empty());
        assert_eq!(facts.symbols[0].name, "Order");
        assert!(facts.symbols[0].fan_in >= 2);
        // Both inversions are reported (Domain→Infrastructure and the
        // Infrastructure→Presentation edge that closes the cycle).
        assert_eq!(facts.violations.len(), 2);
        assert!(facts
            .violations
            .iter()
            .any(|v| v.from_layer == "Domain" && v.to_layer == "Infrastructure"));
        // Entry point found with its path.
        assert_eq!(facts.entries.len(), 1);
        assert_eq!(facts.entries[0].path, "src/Shop.API/Program.cs");
        // The file dependency edges close one three-file cycle.
        assert_eq!(facts.cycles.len(), 1);
        assert_eq!(facts.cycles[0].len(), 3);
    }

    #[test]
    fn hotspots_carry_named_dependents_ranked_and_capped() {
        let facts = extract(&sample());
        // Order's dependents are main and Repo (distinct incoming neighbors);
        // Repo has fan-in 1 (from Order), main has fan-in 1 (from Repo), so
        // the tie breaks on id: Repo's sym id sorts before main's? Both are
        // `sym::file::...` ids — the assertion pins the deterministic order.
        let order = &facts.symbols[0];
        assert_eq!(order.name, "Order");
        assert_eq!(order.dependents.len() as u64, order.fan_in);
        let names: Vec<&str> = order.dependents.iter().map(|d| d.name.as_str()).collect();
        assert!(names.contains(&"main"), "{names:?}");
        assert!(names.contains(&"Repo"), "{names:?}");
        // Every named dependent carries its owning path.
        for d in &order.dependents {
            assert!(!d.path.is_empty(), "{d:?}");
        }
    }

    #[test]
    fn target_fact_names_the_same_dependents_as_the_hotspot_set() {
        let analysis = sample();
        let node = analysis
            .graph
            .nodes()
            .find(|n| n.name == "Order")
            .unwrap()
            .clone();
        let t = target_fact(&analysis, &node);
        let hot = extract(&analysis);
        let same = hot.symbols.iter().find(|s| s.id == t.id).unwrap();
        assert_eq!(
            format!("{:?}", t.dependents),
            format!("{:?}", same.dependents)
        );
        assert!(!t.dependents.is_empty());
    }

    #[test]
    fn extraction_is_deterministic() {
        let a = extract(&sample());
        let b = extract(&sample());
        assert_eq!(format!("{a:?}"), format!("{b:?}"));
    }

    #[test]
    fn target_fact_matches_hotspot_conventions() {
        let analysis = sample();
        let node = analysis
            .graph
            .nodes()
            .find(|n| n.name == "Order")
            .unwrap()
            .clone();
        let t = target_fact(&analysis, &node);
        let hot = extract(&analysis);
        let same = hot.symbols.iter().find(|s| s.id == t.id).unwrap();
        assert_eq!(t.fan_in, same.fan_in);
        assert_eq!(t.fan_out, same.fan_out);
        assert_eq!(t.blast, same.blast);
        assert_eq!(t.domain, same.domain);
        assert_eq!(t.layer, same.layer);
    }

    #[test]
    fn cycles_are_sorted_and_size_gt_one() {
        let mut deps: BTreeSet<(&str, &str)> = BTreeSet::new();
        deps.insert(("b", "a"));
        deps.insert(("a", "b"));
        deps.insert(("c", "a")); // acyclic tail
        let cycles = file_cycles(&deps);
        assert_eq!(cycles, vec![vec!["a", "b"]]);
    }
}
