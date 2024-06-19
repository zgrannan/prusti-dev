// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    borrows::domain::{Borrow, BorrowsDomain, RegionAbstraction},
    utils::{Place, PlaceRepacker},
};
use std::{
    collections::{HashSet, VecDeque},
    fs::File,
    io::{self, Write},
    rc::Rc,
};

use super::{CapabilityKind, CapabilityLocal, CapabilitySummary};
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
            RETURN_PLACE,
        },
        ty::{self, GenericArgsRef, ParamEnv, RegionVid, TyCtxt},
    },
};
use serde::Serialize;

impl<'tcx> CapabilityLocal<'tcx> {
    pub fn to_dot(&self, local: usize, file: &mut File) -> io::Result<()> {
        match self {
            CapabilityLocal::Unallocated => {
                writeln!(file, "    {} [label=\"Unallocated\"];", local)?;
            }
            CapabilityLocal::Allocated(projections) => {
                for (place, kind) in projections.iter() {
                    writeln!(file, "    {} -> {:?} [label=\"{:?}\"];", local, place, kind)?;
                }
            }
        }
        Ok(())
    }
}
#[derive(Serialize)]
struct MirGraph {
    nodes: Vec<MirNode>,
    edges: Vec<MirEdge>,
}

#[derive(Serialize)]
struct MirNode {
    id: String,
    label: String,
}

#[derive(Serialize)]
struct MirEdge {
    source: String,
    target: String,
    label: String,
}

fn mk_mir_graph(body: &Body<'_>) -> MirGraph {
    let mut nodes = Vec::new();
    let mut edges = Vec::new();

    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let mut label = String::new();
        label.push_str(
            &format!(
                r#"<table data-bb="bb{}" border="1" cellspacing="0" cellpadding="4" style="border-collapse: collapse;">"#,
                bb.as_usize()
            )
        );
        label.push_str(&format!(
            "<tr><td>(on start)</td><td><b>BB{}</b></td></tr>",
            bb.as_usize()
        ));

        for (i, stmt) in data.statements.iter().enumerate() {
            label.push_str(&format!(
                "<tr data-bb=\"{}\" data-statement=\"{}\"><td>{}</td> <td>{:?}</td></tr>",
                bb.as_usize(),
                i,
                i,
                stmt
            ));
        }

        label.push_str(&format!(
            "<tr><td>T</td> <td>{:?}</td></tr>",
            data.terminator().kind
        ));
        label.push_str("<tr><td>(on end)</td></tr>");
        label.push_str("</table>");

        nodes.push(MirNode {
            id: format!("{:?}", bb),
            label,
        });

        match &data.terminator().kind {
            TerminatorKind::Goto { target } => {
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", target),
                    label: "goto".to_string(),
                });
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                for (val, target) in targets.iter() {
                    edges.push(MirEdge {
                        source: format!("{:?}", bb),
                        target: format!("{:?}", target),
                        label: format!("{}", val),
                    });
                }
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", targets.otherwise()),
                    label: "otherwise".to_string(),
                });
            }
            TerminatorKind::UnwindResume => {}
            TerminatorKind::UnwindTerminate(_) => todo!(),
            TerminatorKind::Return => {}
            TerminatorKind::Unreachable => todo!(),
            TerminatorKind::Drop {
                place,
                target,
                unwind,
                replace,
            } => todo!(),
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                call_source,
                fn_span,
            } => {
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", target.unwrap()),
                    label: "call".to_string(),
                });
            }
            TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                unwind,
            } => {
                match unwind {
                    UnwindAction::Continue => todo!(),
                    UnwindAction::Unreachable => todo!(),
                    UnwindAction::Terminate(_) => todo!(),
                    UnwindAction::Cleanup(cleanup) => {
                        edges.push(MirEdge {
                            source: format!("{:?}", bb),
                            target: format!("{:?}", cleanup),
                            label: format!("unwind"),
                        });
                    }
                }
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", target),
                    label: format!("success"),
                });
            }
            TerminatorKind::Yield {
                value,
                resume,
                resume_arg,
                drop,
            } => todo!(),
            TerminatorKind::GeneratorDrop => todo!(),
            TerminatorKind::FalseEdge {
                real_target,
                imaginary_target,
            } => todo!(),
            TerminatorKind::FalseUnwind {
                real_target,
                unwind,
            } => todo!(),
            TerminatorKind::InlineAsm {
                template,
                operands,
                options,
                line_spans,
                destination,
                unwind,
            } => todo!(),
        }
    }

    MirGraph { nodes, edges }
}

pub fn generate_json_from_mir(path: &str, body: &Body<'_>) -> io::Result<()> {
    let mir_graph = mk_mir_graph(body);
    let mut file = File::create(path)?;
    serde_json::to_writer(&mut file, &mir_graph)?;
    Ok(())
}

pub fn place_id<'tcx>(place: &Place<'tcx>) -> String {
    format!("{:?}", place)
}

pub fn has_place<'tcx>(summary: &CapabilitySummary<'tcx>, place: &Place<'tcx>) -> bool {
    if let CapabilityLocal::Allocated(projs) = &summary[place.local] {
        projs.contains_key(place)
    } else {
        false
    }
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
            Self::RustcBorrow(borrow_index, region_vid) => write!(f, "{:?}: {:?}", borrow_index, region_vid),
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
    nodes: HashSet<GraphNode>,
    edges: HashSet<GraphEdge>,
}

impl Graph {
    fn new() -> Self {
        Self {
            nodes: HashSet::new(),
            edges: HashSet::new(),
        }
    }

    fn insert_node(&mut self, node: GraphNode) {
        self.nodes.insert(node);
    }

    fn insert_edge(&mut self, edge: GraphEdge) {
        self.edges.insert(edge);
    }
}

struct GraphConstructor<'a, 'tcx> {
    summary: &'a CapabilitySummary<'tcx>,
    repacker: Rc<PlaceRepacker<'a, 'tcx>>,
    borrows_domain: &'a BorrowsDomain<'tcx>,
    borrow_set: &'a BorrowSet<'tcx>,
    graph: Graph,
    places: Vec<Place<'tcx>>,
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
            graph: Graph::new(),
            borrows_domain,
            borrow_set,
            places: vec![]
        }
    }

    fn node_id(&mut self, place: &Place<'tcx>) -> NodeId {
        if let Some(idx) = self.places.iter().position(|p| p == place) {
            NodeId(idx)
        } else {
            self.places.push(place.clone());
            NodeId(self.places.len() - 1)
        }
    }

    fn insert_place_node(&mut self, place: Place<'tcx>, kind: Option<CapabilityKind>) -> NodeId {
        let id = self.node_id(&place);
        let node = GraphNode {
            id,
            node_type: NodeType::PlaceNode {
                label: format!("{:?}: {}", place, place.ty(*self.repacker).ty),
                capability: kind,
            },
        };
        self.graph.insert_node(node);
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
            self.graph.insert_edge(GraphEdge::ProjectionEdge {
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
            match borrow {
                Borrow::Rustc(borrow_index) => {
                    let borrow_data = &self.borrow_set[*borrow_index];
                    let borrowed_place = self.insert_place_and_previous_projections(
                        borrow_data.borrowed_place.into(),
                        None,
                    );
                    let assigned_place = self.insert_place_and_previous_projections(
                        borrow_data.assigned_place.into(),
                        None,
                    );
                    self.graph.insert_edge(GraphEdge::ReferenceEdge {
                        borrowed_place,
                        assigned_place,
                        edge_type: ReferenceEdgeType::RustcBorrow(
                            *borrow_index,
                            borrow_data.region,
                        ),
                    });
                }
                Borrow::PCS {
                    borrowed_place,
                    assigned_place,
                } => {
                    let borrowed_place =
                        self.insert_place_and_previous_projections(*borrowed_place, None);
                    let assigned_place =
                        self.insert_place_and_previous_projections(*assigned_place, None);
                    self.graph.insert_edge(GraphEdge::ReferenceEdge {
                        borrowed_place,
                        assigned_place,
                        edge_type: ReferenceEdgeType::PCS,
                    });
                }
            }
        }
        self.graph
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

    fn draw_node(&mut self, node: GraphNode) -> io::Result<()> {
        match node.node_type {
            NodeType::PlaceNode { capability, label } => {
                let (capability_text, color) = match capability {
                    Some(k) => (format!("{:?}", k), "black"),
                    None => ("0".to_string(), "gray"),
                };
                writeln!(
                    self.file,
                    "    \"{}\" [label=\"{} {}\", fontcolor=\"{}\", color=\"{}\"];",
                    node.id, label, capability_text, color, color
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
        disabled: bool,
    ) -> io::Result<()> {
        if disabled {
            writeln!(
            self.file,
            "    \"{}\" -> \"{}\" [label=\"{}\", color=\"gray\", style=\"dashed\", fontcolor=\"gray\"];",
            source, target, label
        )?;
        } else {
            writeln!(
                self.file,
                "    \"{}\" -> \"{}\" [label=\"{}\"];",
                source, target, label
            )?;
        }
        Ok(())
    }

    fn draw_edge(&mut self, edge: GraphEdge) -> io::Result<()> {
        match edge {
            GraphEdge::ReferenceEdge { borrowed_place, assigned_place, edge_type } => {
                self.draw_dot_edge(borrowed_place, assigned_place, &format!("{}", edge_type), false)?;
            }
            GraphEdge::ProjectionEdge { source, target } => {
                self.draw_dot_edge(source, target, "", false)?;
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
