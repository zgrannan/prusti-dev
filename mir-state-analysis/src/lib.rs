// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(unused)]
#![feature(rustc_private)]
#![feature(box_patterns, hash_extract_if, extract_if)]

pub mod visualization;
pub mod free_pcs;
pub mod utils;
pub mod coupling_graph;
pub mod r#loop;
pub mod combined_pcs;
pub mod borrows;

use std::{fs::create_dir_all, rc::Rc};

use borrows::domain::BorrowsDomain;
use combined_pcs::{PcsEngine, PlaceCapabilitySummary};
use free_pcs::HasExtra;
use prusti_rustc_interface::{
    borrowck::consumers::BodyWithBorrowckFacts,
    dataflow::Analysis,
    index::IndexVec,
    middle::{
        mir::{Body, Promoted, START_BLOCK},
        ty::TyCtxt,
    },
};
use visualization::mir_graph::generate_json_from_mir;

use crate::visualization::generate_dot_graph;

pub type FpcsOutput<'mir, 'tcx> = free_pcs::FreePcsAnalysis<
    'mir,
    'tcx,
    BorrowsDomain<'tcx>,
    PlaceCapabilitySummary<'mir, 'tcx>,
    PcsEngine<'mir, 'tcx>,
>;

impl<'mir, 'tcx> HasExtra<BorrowsDomain<'tcx>> for PlaceCapabilitySummary<'mir, 'tcx> {
    fn get_extra(&self) -> BorrowsDomain<'tcx> {
        self.borrows.clone()
    }
}

#[tracing::instrument(name = "run_free_pcs", level = "debug", skip(mir, tcx))]
pub fn run_free_pcs<'mir, 'tcx>(
    mir: &'mir BodyWithBorrowckFacts<'tcx>,
    tcx: TyCtxt<'tcx>,
    visualization_output_path: &str
) -> FpcsOutput<'mir, 'tcx> {
    let cgx = coupling_graph::CgContext::new(tcx, mir);
    let fpcs = PcsEngine::new(cgx);
    let analysis = fpcs
        .into_engine(tcx, &mir.body)
        .pass_name("free_pcs")
        .iterate_to_fixpoint();
    let mut fpcs_analysis = free_pcs::FreePcsAnalysis::new(analysis.into_results_cursor(&mir.body));

    let fn_name = tcx.item_name(mir.body.source.def_id());
    let dir_path = format!("{}/{}", visualization_output_path, fn_name);
    if std::path::Path::new(&dir_path).exists() {
        std::fs::remove_dir_all(&dir_path).expect("Failed to delete directory contents");
    }
    create_dir_all(&dir_path).expect("Failed to create directory for DOT files");
    generate_json_from_mir(&format!("{}/mir.json", dir_path), &mir.body)
        .expect("Failed to generate JSON from MIR");

    let input_facts = mir.input_facts.as_ref().unwrap().clone();
    let output_facts = mir.output_facts.as_ref().unwrap().clone();
    let location_table = mir.location_table.as_ref().unwrap().clone();
    let fn_name = tcx.item_name(mir.body.source.def_id());

    let rp = coupling_graph::CgContext::new(tcx, mir).rp;

    // Iterate over each statement in the MIR
    for (block, data) in mir.body.basic_blocks.iter_enumerated() {
        let pcs_block = fpcs_analysis.get_all_for_bb(block);
        for (statement_index, statement) in pcs_block.statements.iter().enumerate() {
            let file_path = format!(
                "{}/block_{}_stmt_{}.dot",
                &dir_path,
                block.index(),
                statement_index
            );
            eprintln!("{}", file_path);
            generate_dot_graph(
                statement.location,
                Rc::new(rp),
                &statement.state,
                &statement.extra,
                &mir.borrow_set,
                &input_facts,
                &file_path,
            )
            .expect("Failed to generate DOT graph");
        }
    }

    fpcs_analysis
}

pub fn get_cgx<'mir, 'tcx>(
    mir: &'mir BodyWithBorrowckFacts<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> coupling_graph::CgContext<'mir, 'tcx> {
    coupling_graph::CgContext::new(tcx, mir)
}

#[tracing::instrument(name = "run_coupling_graph", level = "debug", skip(tcx))]
pub fn run_coupling_graph<'mir, 'tcx>(
    cgx: coupling_graph::CgContext<'mir, 'tcx>,
    tcx: TyCtxt<'tcx>,
    top_crates: bool,
) -> coupling_graph::cursor::CgAnalysis<'mir, 'mir, 'tcx> {
    // if tcx.item_name(mir.source.def_id()).as_str().starts_with("main") {
    //     return;
    // }
    let cgx = std::rc::Rc::new(cgx);
    let fpcs = coupling_graph::engine::CgEngine::new(cgx.clone(), top_crates);
    let analysis = fpcs
        .into_engine(tcx, &cgx.mir.body)
        .pass_name("coupling_graph")
        .iterate_to_fixpoint();
    let mut c = analysis.into_results_cursor(&cgx.mir.body);
    if cfg!(debug_assertions) && !top_crates {
        coupling_graph::engine::draw_dots(&mut c);
    }
    c.seek_to_block_start(START_BLOCK);
    coupling_graph::cursor::CgAnalysis::new(c)
}
