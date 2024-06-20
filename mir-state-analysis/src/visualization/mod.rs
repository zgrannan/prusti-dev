// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub mod mir_graph;

use crate::{
    borrows::domain::{Borrow, BorrowKind, BorrowsDomain, RegionAbstraction},
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilitySummary},
    utils::{Place, PlaceRepacker},
};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fs::File,
    io::{self, Write},
    rc::Rc,
};

use prusti_rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{
            calculate_borrows_out_of_scope_at_location, BorrowIndex, Borrows, LocationTable,
            PoloniusInput, PoloniusOutput, RegionInferenceContext,
        },
    },
    data_structures::fx::{FxHashMap, FxIndexMap},
    dataflow::{Analysis, ResultsCursor},
    index::IndexVec,
    middle::{
        mir::{
            self, Body, Local, Location, PlaceElem, Promoted, TerminatorKind, UnwindAction,
            VarDebugInfo, RETURN_PLACE,
        },
        ty::{self, GenericArgsRef, ParamEnv, RegionVid, TyCtxt},
    },
};

pub fn place_id<'tcx>(place: &Place<'tcx>) -> String {
    format!("{:?}", place)
}

struct GraphDrawer {
    file: File,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct NodeId(usize);

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "n{}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct GraphNode {
    id: NodeId,
    node_type: NodeType,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NodeType {
    PlaceNode {
        label: String,
        capability: Option<CapabilityKind>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ReferenceEdgeType {
    RustcBorrow(BorrowIndex, RegionVid),
    PCS,
}

impl std::fmt::Display for ReferenceEdgeType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RustcBorrow(borrow_index, region_vid) => {
                write!(f, "{:?}: {:?}", borrow_index, region_vid)
            }
            Self::PCS => write!(f, "PCS"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum GraphEdge {
    ReferenceEdge {
        borrowed_place: NodeId,
        assigned_place: NodeId,
        edge_type: ReferenceEdgeType,
    },
    ProjectionEdge {
        source: NodeId,
        target: NodeId,
    },
}

struct Graph {
    nodes: Vec<GraphNode>,
    edges: HashSet<GraphEdge>,
}

impl Graph {
    fn new(nodes: Vec<GraphNode>, edges: HashSet<GraphEdge>) -> Self {
        Self { nodes, edges }
    }
}

pub fn get_source_name_from_local(local: &Local, debug_info: &[VarDebugInfo]) -> Option<String> {
    if local.as_usize() == 0 {
        return None;
    }
    debug_info
        .get(&local.as_usize() - 1)
        .map(|source_info| format!("{}", source_info.name))
}

pub fn get_source_name_from_place<'tcx>(
    place: &Place<'tcx>,
    debug_info: &[VarDebugInfo],
) -> Option<String> {
    get_source_name_from_local(&place.local, debug_info).map(|mut name| {
        let mut iter = place.projection.iter().peekable();
        while let Some(elem) = iter.next() {
            match elem {
                mir::ProjectionElem::Deref => {
                    if iter.peek().is_some() {
                        name = format!("(*{})", name);
                    } else {
                        name = format!("*{}", name);
                    }
                }
                mir::ProjectionElem::Field(field, _) => {
                    name = format!("{}.{}", name, field.as_usize());
                }
                mir::ProjectionElem::Index(_) => todo!(),
                mir::ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => todo!(),
                mir::ProjectionElem::Subslice { from, to, from_end } => todo!(),
                mir::ProjectionElem::Downcast(_, _) => todo!(),
                mir::ProjectionElem::OpaqueCast(_) => todo!(),
            }
        }
        name
    })
}

struct GraphConstructor<'a, 'tcx> {
    summary: &'a CapabilitySummary<'tcx>,
    repacker: Rc<PlaceRepacker<'a, 'tcx>>,
    borrows_domain: &'a BorrowsDomain<'tcx>,
    borrow_set: &'a BorrowSet<'tcx>,
    places: Vec<Place<'tcx>>,
    nodes: Vec<GraphNode>,
    edges: HashSet<GraphEdge>,
    rank: HashMap<NodeId, usize>,
}

impl<'a, 'tcx> GraphConstructor<'a, 'tcx> {
    fn new(
        summary: &'a CapabilitySummary<'tcx>,
        repacker: Rc<PlaceRepacker<'a, 'tcx>>,
        borrows_domain: &'a BorrowsDomain<'tcx>,
        borrow_set: &'a BorrowSet<'tcx>,
    ) -> Self {
        Self {
            summary,
            repacker,
            borrows_domain,
            borrow_set,
            places: vec![],
            nodes: vec![],
            edges: HashSet::new(),
            rank: HashMap::new(),
        }
    }

    fn existing_node_id(&self, place: &Place<'tcx>) -> Option<NodeId> {
        self.places
            .iter()
            .position(|p| p == place)
            .map(|idx| NodeId(idx))
    }

    fn node_id(&mut self, place: &Place<'tcx>) -> NodeId {
        if let Some(idx) = self.places.iter().position(|p| p == place) {
            NodeId(idx)
        } else {
            self.places.push(place.clone());
            NodeId(self.places.len() - 1)
        }
    }

    fn rank(&self, node: NodeId) -> usize {
        *self.rank.get(&node).unwrap_or(&usize::MAX)
    }

    fn insert_node(&mut self, node: GraphNode) {
        if !self.nodes.contains(&node) {
            self.nodes.push(node);
        }
    }

    fn insert_place_node(&mut self, place: Place<'tcx>, kind: Option<CapabilityKind>) -> NodeId {
        if let Some(node_id) = self.existing_node_id(&place) {
            return node_id;
        }
        let id = self.node_id(&place);
        let label = get_source_name_from_place(&place, &self.repacker.body().var_debug_info)
            .unwrap_or_else(|| format!("{:?}: {}", place, place.ty(*self.repacker).ty));
        let node = GraphNode {
            id,
            node_type: NodeType::PlaceNode {
                label,
                capability: kind,
            },
        };
        self.insert_node(node);
        self.rank.insert(id, place.local.as_usize());
        id
    }

    fn insert_place_and_previous_projections(
        &mut self,
        place: Place<'tcx>,
        kind: Option<CapabilityKind>,
    ) -> NodeId {
        let node = self.insert_place_node(place, kind);
        let mut projection = place.projection;
        let mut last_node = node;
        while !projection.is_empty() {
            projection = &projection[..projection.len() - 1];
            let place = Place::new(place.local, &projection);
            let node = self.insert_place_node(place, None);
            self.edges.insert(GraphEdge::ProjectionEdge {
                source: node,
                target: last_node,
            });
            last_node = node.clone();
        }
        node
    }

    fn construct_graph(mut self) -> Graph {
        for (local, capability) in self.summary.iter().enumerate() {
            match capability {
                CapabilityLocal::Unallocated => {}
                CapabilityLocal::Allocated(projections) => {
                    for (place, kind) in projections.iter() {
                        self.insert_place_and_previous_projections(*place, Some(*kind));
                    }
                }
            }
        }
        for borrow in &self.borrows_domain.live_borrows {
            let borrowed_place = self.insert_place_and_previous_projections(
                borrow.borrowed_place(&self.borrow_set).into(),
                None,
            );
            let assigned_place = self.insert_place_and_previous_projections(
                borrow.assigned_place(&self.borrow_set).into(),
                None,
            );
            match borrow.kind {
                BorrowKind::Rustc(borrow_index) => {
                    let borrow_data = &self.borrow_set[borrow_index];
                    self.edges.insert(GraphEdge::ReferenceEdge {
                        borrowed_place,
                        assigned_place,
                        edge_type: ReferenceEdgeType::RustcBorrow(borrow_index, borrow_data.region),
                    });
                }
                BorrowKind::PCS { .. } => {
                    self.edges.insert(GraphEdge::ReferenceEdge {
                        borrowed_place,
                        assigned_place,
                        edge_type: ReferenceEdgeType::PCS,
                    });
                }
            }
        }
        let mut nodes = self.nodes.clone().into_iter().collect::<Vec<_>>();
        nodes.sort_by(|a, b| self.rank(a.id).cmp(&self.rank(b.id)));
        Graph::new(nodes, self.edges)
    }
}

impl GraphDrawer {
    fn new(file_path: &str) -> Self {
        let file = File::create(file_path).unwrap();
        Self { file }
    }

    fn draw(mut self, graph: Graph) -> io::Result<()> {
        writeln!(self.file, "digraph CapabilitySummary {{")?;
        writeln!(self.file, "node [shape=rect]")?;
        for node in graph.nodes {
            self.draw_node(node)?;
        }
        for edge in graph.edges {
            self.draw_edge(edge)?;
        }
        writeln!(&mut self.file, "}}")
    }

    fn escape_html(input: String) -> String {
        input
            .replace("&", "&amp;")
            .replace("<", "&lt;")
            .replace(">", "&gt;")
            .replace("\"", "&quot;")
            .replace("'", "&#39;")
    }

    fn draw_node(&mut self, node: GraphNode) -> io::Result<()> {
        match node.node_type {
            NodeType::PlaceNode { capability, label } => {
                let (capability_text, color) = match capability {
                    Some(k) => (format!("{:?}", k), "black"),
                    None => ("N".to_string(), "gray"),
                };
                writeln!(
                    self.file,
                    "    \"{}\" [label=<<FONT FACE=\"courier\">{}</FONT>&nbsp;{}>, fontcolor=\"{}\", color=\"{}\"];",
                    node.id, Self::escape_html(label), Self::escape_html(capability_text), color, color
                )?;
            }
        }
        Ok(())
    }

    fn draw_dot_edge(
        &mut self,
        source: NodeId,
        target: NodeId,
        label: &str,
        style: Option<&str>,
        arrowhead: bool,
    ) -> io::Result<()> {
        let style_part = match style {
            Some(style) => format!(", style=\"{}\"", style),
            None => "".to_string(),
        };
        let arrowhead_part = if !arrowhead {
            ", arrowhead=\"none\""
        } else {
            ""
        };
        writeln!(
            self.file,
            "    \"{}\" -> \"{}\" [label=\"{}\"{}{}]",
            source, target, label, style_part, arrowhead_part
        )
    }

    fn draw_edge(&mut self, edge: GraphEdge) -> io::Result<()> {
        match edge {
            GraphEdge::ReferenceEdge {
                borrowed_place,
                assigned_place,
                edge_type,
            } => {
                self.draw_dot_edge(
                    borrowed_place,
                    assigned_place,
                    &format!("{}", edge_type),
                    Some("dashed"),
                    true,
                )?;
            }
            GraphEdge::ProjectionEdge { source, target } => {
                self.draw_dot_edge(source, target, "", None, false)?;
            }
        }
        Ok(())
    }
}

pub fn generate_dot_graph<'a, 'tcx: 'a>(
    location: Location,
    repacker: Rc<PlaceRepacker<'a, 'tcx>>,
    summary: &CapabilitySummary<'tcx>,
    borrows_domain: &BorrowsDomain<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    input_facts: &PoloniusInput,
    file_path: &str,
) -> io::Result<()> {
    eprintln!("{:?}", repacker.body().var_debug_info);
    let constructor = GraphConstructor::new(summary, repacker, borrows_domain, borrow_set);
    let graph = constructor.construct_graph();
    let mut drawer = GraphDrawer::new(file_path);
    drawer.draw(graph)

    // for (idx, region_abstraction) in borrows_domain.region_abstractions.iter().enumerate() {
    //     let ra_node_label = format!("ra{}", idx);
    //     writeln!(
    //         drawer.file,
    //         "    \"{}\" [label=\"{}\", shape=egg];",
    //         ra_node_label, ra_node_label
    //     )?;
    //     for loan_in in &region_abstraction.loans_in {
    //         drawer.add_place_if_necessary((*loan_in).into())?;
    //         dot_edge(
    //             &mut drawer.file,
    //             &place_id(&(*loan_in).into()),
    //             &ra_node_label,
    //             "loan_in",
    //             false,
    //         )?;
    //     }
    //     for loan_out in &region_abstraction.loans_out {
    //         drawer.add_place_if_necessary((*loan_out).into())?;
    //         dot_edge(
    //             &mut drawer.file,
    //             &ra_node_label,
    //             &place_id(&(*loan_out).into()),
    //             "loan_out",
    //             false,
    //         )?;
    //     }
    // }
}
