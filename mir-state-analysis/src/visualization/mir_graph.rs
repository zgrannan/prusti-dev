use serde::Serialize;
use crate::{
    borrows::domain::{Borrow, BorrowsDomain, RegionAbstraction}, free_pcs::{CapabilityKind, CapabilityLocal, CapabilitySummary}, utils::{Place, PlaceRepacker}
};
use std::{
    collections::{HashSet, VecDeque},
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
            RETURN_PLACE,
        },
        ty::{self, GenericArgsRef, ParamEnv, RegionVid, TyCtxt},
    },
};

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
