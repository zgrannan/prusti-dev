// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{loops, mir_utils::RealEdges, EnvQuery};
use crate::data::ProcedureDefId;
use log::{debug, trace};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    hir::def_id,
    middle::{
        mir::{self, AggregateKind, BasicBlock, BasicBlockData, Body, Rvalue, StatementKind},
        ty::TyCtxt,
    },
};

/// Index of a Basic Block
pub type BasicBlockIndex = mir::BasicBlock;

/// A facade that provides information about the Rust procedure.
pub struct Procedure<'tcx> {
    #[allow(unused)]
    tcx: TyCtxt<'tcx>,
    #[allow(unused)]
    proc_def_id: ProcedureDefId,
    #[allow(unused)]
    mir: mir::Body<'tcx>,
    #[allow(unused)]
    real_edges: RealEdges,
    loop_info: loops::ProcedureLoops,
    reachable_basic_blocks: FxHashSet<BasicBlock>,
    nonspec_basic_blocks: FxHashSet<BasicBlock>,
}

impl<'tcx> Procedure<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, proc_def_id: ProcedureDefId, mir: mir::Body<'tcx>) -> Self {
        let real_edges = RealEdges::new(&mir);
        let reachable_basic_blocks = build_reachable_basic_blocks(&mir, &real_edges);
        let nonspec_basic_blocks =
            build_nonspec_basic_blocks(EnvQuery::new(tcx), &mir, &real_edges);
        let loop_info = loops::ProcedureLoops::new(&mir, &real_edges);

        Self {
            tcx,
            proc_def_id,
            mir,
            real_edges,
            loop_info,
            reachable_basic_blocks,
            nonspec_basic_blocks,
        }
    }

    pub fn get_loop_head(&self, bbi: BasicBlockIndex) -> Option<BasicBlockIndex> {
        self.loop_info.get_loop_head(bbi)
    }

    /// Iterate over all reachable CFG basic blocks
    pub fn get_reachable_cfg_blocks(&self) -> Vec<BasicBlock> {
        self.get_all_cfg_blocks()
            .into_iter()
            .filter(|bbi| self.is_reachable_block(*bbi))
            .collect()
    }
    /// Iterate over all CFG basic blocks
    pub fn get_all_cfg_blocks(&self) -> Vec<BasicBlock> {
        self.loop_info.ordered_blocks.clone()
    }

    /// Check whether the block is reachable
    pub fn is_reachable_block(&self, bbi: BasicBlockIndex) -> bool {
        self.reachable_basic_blocks.contains(&bbi)
    }

    /// Check whether the block is used for typechecking the specification
    pub fn is_spec_block(&self, bbi: BasicBlockIndex) -> bool {
        !self.nonspec_basic_blocks.contains(&bbi)
    }
}

/// Returns the set of basic blocks that are not used as part of the typechecking of Prusti specifications
fn build_reachable_basic_blocks(mir: &Body, real_edges: &RealEdges) -> FxHashSet<BasicBlock> {
    let mut reachable_basic_blocks: FxHashSet<BasicBlock> = FxHashSet::default();
    let mut visited: FxHashSet<BasicBlock> = FxHashSet::default();
    let mut to_visit: Vec<BasicBlock> = vec![mir.basic_blocks.indices().next().unwrap()];

    while let Some(source) = to_visit.pop() {
        if visited.contains(&source) {
            continue;
        }

        visited.insert(source);
        reachable_basic_blocks.insert(source);

        for &target in real_edges.successors(source) {
            if !visited.contains(&target) {
                to_visit.push(target);
            }
        }
    }

    reachable_basic_blocks
}

fn build_nonspec_basic_blocks(
    env_query: EnvQuery,
    mir: &Body,
    real_edges: &RealEdges,
) -> FxHashSet<BasicBlock> {
    let dominators = mir.basic_blocks.dominators();
    let mut loop_heads: FxHashSet<BasicBlock> = FxHashSet::default();

    for source in mir.basic_blocks.indices() {
        for &target in real_edges.successors(source) {
            if dominators.dominates(target, source) {
                loop_heads.insert(target);
            }
        }
    }

    let mut visited: FxHashSet<BasicBlock> = FxHashSet::default();
    let mut to_visit: Vec<BasicBlock> = vec![mir.basic_blocks.indices().next().unwrap()];

    let mut bb_graph: FxHashMap<BasicBlock, BasicBlockNode> = FxHashMap::default();

    while let Some(source) = to_visit.pop() {
        if visited.contains(&source) {
            continue;
        }

        bb_graph.entry(source).or_insert_with(|| BasicBlockNode {
            successors: FxHashSet::default(),
            predecessors: FxHashSet::default(),
        });

        visited.insert(source);

        let is_loop_head = loop_heads.contains(&source);
        if is_loop_head {
            trace!("MIR block {source:?} is a loop head");
        }
        for &target in real_edges.successors(source) {
            if !visited.contains(&target) {
                to_visit.push(target);
            }

            bb_graph.entry(target).or_insert_with(|| BasicBlockNode {
                successors: FxHashSet::default(),
                predecessors: FxHashSet::default(),
            });
            bb_graph
                .get_mut(&target)
                .unwrap()
                .predecessors
                .insert(source);
            bb_graph.get_mut(&source).unwrap().successors.insert(target);
        }
    }

    get_nonspec_basic_blocks(env_query, bb_graph, mir)
}

#[derive(Debug)]
struct BasicBlockNode {
    successors: FxHashSet<BasicBlock>,
    predecessors: FxHashSet<BasicBlock>,
}

fn get_nonspec_basic_blocks(
    env_query: EnvQuery,
    bb_graph: FxHashMap<BasicBlock, BasicBlockNode>,
    mir: &Body,
) -> FxHashSet<BasicBlock> {
    let mut spec_basic_blocks: FxHashSet<BasicBlock> = FxHashSet::default();
    for (bb, _) in bb_graph.iter() {
        if is_marked_specification_block(env_query, &mir[*bb]) {
            spec_basic_blocks.insert(*bb);
            spec_basic_blocks.extend(blocks_definitely_leading_to(&bb_graph, *bb));
            spec_basic_blocks.extend(blocks_dominated_by(mir, *bb));
        }
    }
    debug!("spec basic blocks: {spec_basic_blocks:#?}");

    let all_basic_blocks: FxHashSet<BasicBlock> = bb_graph.keys().cloned().collect();
    all_basic_blocks
        .difference(&spec_basic_blocks)
        .cloned()
        .collect()
}

pub fn is_marked_specification_block(env_query: EnvQuery, bb_data: &BasicBlockData) -> bool {
    for stmt in &bb_data.statements {
        if let StatementKind::Assign(box (
            _,
            Rvalue::Aggregate(box AggregateKind::Closure(def_id, _), _),
        )) = &stmt.kind
        {
            if is_spec_closure(env_query, *def_id) {
                return true;
            }
        }
    }
    false
}

fn blocks_dominated_by(mir: &Body, dominator: BasicBlock) -> FxHashSet<BasicBlock> {
    let dominators = mir.basic_blocks.dominators();
    let mut blocks = FxHashSet::default();
    for bb in mir.basic_blocks.indices() {
        if dominators.dominates(dominator, bb) {
            blocks.insert(bb);
        }
    }
    blocks
}

#[tracing::instrument(level = "debug", skip_all)]
fn _blocks_definitely_leading_to<'a>(
    bb_graph: &'a FxHashMap<BasicBlock, BasicBlockNode>,
    target: BasicBlock,
    blocks: &'a mut FxHashSet<BasicBlock>,
) -> &'a mut FxHashSet<BasicBlock> {
    for pred in bb_graph[&target].predecessors.iter() {
        debug!("target: {target:#?}, pred: {pred:#?}");
        if bb_graph[pred].successors.len() == 1 {
            debug!("pred {pred:#?} has 1 successor");
            blocks.insert(*pred);
            _blocks_definitely_leading_to(bb_graph, *pred, blocks);
        }
    }
    blocks
}

fn blocks_definitely_leading_to(
    bb_graph: &FxHashMap<BasicBlock, BasicBlockNode>,
    target: BasicBlock,
) -> FxHashSet<BasicBlock> {
    let mut blocks = FxHashSet::default();
    _blocks_definitely_leading_to(bb_graph, target, &mut blocks);
    blocks
}

fn is_spec_closure(env_query: EnvQuery, def_id: def_id::DefId) -> bool {
    crate::utils::has_spec_only_attr(env_query.get_attributes(def_id))
}
