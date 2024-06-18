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
    collections::HashSet, fs::File, io::{self, Write}, rc::Rc
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
        mir::{self, Body, Local, Location, Promoted, TerminatorKind, UnwindAction, RETURN_PLACE},
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

pub fn generate_json_from_mir(body: &Body<'_>) -> io::Result<()> {
    let mir_graph = mk_mir_graph(body);
    let mut file = File::create("visualization/mir_output.json")?;
    serde_json::to_writer(&mut file, &mir_graph)?;
    Ok(())
}

pub fn place_id<'tcx>(place: &Place<'tcx>) -> String {
    format!("{:?}", place)
}

pub fn dot_edge(
    file: &mut File,
    source: &str,
    target: &str,
    label: &str,
    disabled: bool,
) -> io::Result<()> {
    if disabled {
        writeln!(
            file,
            "    \"{}\" -> \"{}\" [label=\"{}\", color=\"gray\", style=\"dashed\", fontcolor=\"gray\"];",
            source, target, label
        )?;
    } else {
        writeln!(
            file,
            "    \"{}\" -> \"{}\" [label=\"{}\"];",
            source, target, label
        )?;
    }
    Ok(())
}

pub fn has_place<'tcx>(summary: &CapabilitySummary<'tcx>, place: &Place<'tcx>) -> bool {
    if let CapabilityLocal::Allocated(projs) = &summary[place.local] {
        projs.contains_key(place)
    } else {
        false
    }
}

struct GraphDrawer<'a, 'tcx> {
    file: File,
    written_places: HashSet<Place<'tcx>>,
    repacker: Rc<PlaceRepacker<'a, 'tcx>>,
}

impl<'a, 'tcx: 'a> GraphDrawer<'a, 'tcx> {
    fn new(file_path: &str, repacker: Rc<PlaceRepacker<'a, 'tcx>>) -> Self {
        let file = File::create(file_path).unwrap();
        Self {
            file,
            written_places: HashSet::new(),
            repacker,
        }
    }

    fn add_place_if_necessary(&mut self, place: Place<'tcx>) -> io::Result<()> {
        if !self.written_places.contains(&place) {
            self.write_place(place, None)?;
        }
        Ok(())
    }

    pub fn edge_between_places(
        &mut self,
        summary: &CapabilitySummary<'tcx>,
        source: &Place<'tcx>,
        target: &Place<'tcx>,
        label: &str,
    ) -> io::Result<()> {
        let disabled = !has_place(summary, source) || !has_place(summary, target);
        self.add_place_if_necessary(source.clone())?;
        self.add_place_if_necessary(target.clone())?;
        dot_edge(
            &mut self.file,
            &place_id(source),
            &place_id(target),
            label,
            disabled,
        )
    }

    fn write_place(&mut self, place: Place<'tcx>, kind: Option<CapabilityKind>) -> io::Result<()> {
        self.written_places.insert(place);
        let (label_text, color) = match kind {
            Some(k) => (format!("{:?}", k), "black"),
            None => ("?".to_string(), "gray"),
        };
        writeln!(
            self.file,
            "    \"{:?}\" [label=\"{:?}: {} {}\", fontcolor=\"{}\", color=\"{}\"];",
            place,
            place,
            place.ty(*self.repacker).ty,
            label_text,
            color,
            color
        )
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
    let mut drawer = GraphDrawer::new(file_path, repacker);
    writeln!(drawer.file, "digraph CapabilitySummary {{")?;
    writeln!(drawer.file, "node [shape=rect]")?;

    for (local, capability) in summary.iter().enumerate() {
        match capability {
            CapabilityLocal::Unallocated => {}
            CapabilityLocal::Allocated(projections) => {
                for (place, kind) in projections.iter() {
                    drawer.write_place(*place, Some(*kind))?;
                }
            }
        }
    }
    for borrow in &borrows_domain.live_borrows {
        match borrow {
            Borrow::Rustc(borrow_index) => {
                let borrow_data = &borrow_set[*borrow_index];
                drawer.edge_between_places(
                    summary,
                    &borrow_data.borrowed_place.into(),
                    &borrow_data.assigned_place.into(),
                    &format!("{:?}: {:?}", borrow_index, borrow_data.region),
                )?
            }
            Borrow::PCS { borrowed_place, assigned_place } => {
                drawer.edge_between_places(
                    summary,
                    borrowed_place,
                    assigned_place,
                    "PCS",
                )?
            }
        }
    }

    for (idx, region_abstraction) in borrows_domain.region_abstractions.iter().enumerate() {
        let ra_node_label = format!("ra{}", idx);
        writeln!(
            drawer.file,
            "    \"{}\" [label=\"{}\", shape=egg];",
            ra_node_label, ra_node_label
        )?;
        for loan_in in &region_abstraction.loans_in {
            drawer.add_place_if_necessary((*loan_in).into())?;
            dot_edge(
                &mut drawer.file,
                &place_id(&(*loan_in).into()),
                &ra_node_label,
                "loan_in",
                false,
            )?;
        }
        for loan_out in &region_abstraction.loans_out {
            drawer.add_place_if_necessary((*loan_out).into())?;
            dot_edge(
                &mut drawer.file,
                &ra_node_label,
                &place_id(&(*loan_out).into()),
                "loan_out",
                false,
            )?;
        }
    }

    writeln!(&mut drawer.file, "}}");
    Ok(())
}
