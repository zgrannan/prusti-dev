use std::{collections::HashSet, ops::ControlFlow, rc::Rc};

use prusti_rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{
            BorrowIndex, LocationTable, PoloniusInput, RegionInferenceContext, RichLocation,
        },
    },
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{Analysis, AnalysisDomain, Forward},
    index::IndexVec,
    middle::{
        mir::{
            visit::{TyContext, Visitor},
            BasicBlock, Body, CallReturnPlaces, HasLocalDecls, Local, Location, Operand, Place,
            ProjectionElem, Promoted, Rvalue, Statement, StatementKind, Terminator,
            TerminatorEdges, TerminatorKind, RETURN_PLACE, START_BLOCK,
        },
        ty::{self, Region, RegionKind, RegionVid, TyCtxt, TypeVisitor},
    },
};

use crate::{borrows::domain::RegionAbstraction, utils};

use super::domain::{Borrow, BorrowKind, BorrowsDomain};

pub struct BorrowsEngine<'mir, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'mir Body<'tcx>,
    location_table: &'mir LocationTable,
    input_facts: &'mir PoloniusInput,
    borrow_set: Rc<BorrowSet<'tcx>>,
    region_inference_context: Rc<RegionInferenceContext<'tcx>>,
}
impl<'mir, 'tcx> BorrowsEngine<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        location_table: &'mir LocationTable,
        input_facts: &'mir PoloniusInput,
        borrow_set: Rc<BorrowSet<'tcx>>,
        region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    ) -> Self {
        BorrowsEngine {
            tcx,
            body,
            location_table,
            input_facts,
            borrow_set,
            region_inference_context,
        }
    }

    fn get_regions_in(&self, ty: ty::Ty<'tcx>, location: Location) -> HashSet<RegionVid> {
        struct RegionVisitor(HashSet<RegionVid>);

        impl<'tcx> ty::TypeVisitor<ty::TyCtxt<'tcx>> for RegionVisitor {
            fn visit_region(&mut self, region: Region<'tcx>) -> ControlFlow<Self::BreakTy> {
                match region.kind() {
                    RegionKind::ReEarlyBound(_) => todo!(),
                    RegionKind::ReLateBound(_, _) => todo!(),
                    RegionKind::ReFree(_) => todo!(),
                    RegionKind::ReStatic => todo!(),
                    RegionKind::ReVar(vid) => {
                        self.0.insert(vid);
                    }
                    RegionKind::RePlaceholder(_) => todo!(),
                    RegionKind::ReErased => todo!(),
                    RegionKind::ReError(_) => todo!(),
                }
                ControlFlow::Continue(())
            }
        }
        let mut visitor = RegionVisitor(HashSet::new());
        visitor.visit_ty(ty);
        visitor.0
    }

    fn loan_issued_at_location(&self, location: Location) -> Option<BorrowIndex> {
        self.input_facts
            .loan_issued_at
            .iter()
            .find_map(
                |(_, loan, loan_point)| match self.location_table.to_location(*loan_point) {
                    RichLocation::Start(loan_location) if loan_location == location => Some(*loan),
                    RichLocation::Mid(loan_location) if loan_location == location => Some(*loan),
                    _ => None,
                },
            )
    }

    fn placed_loaned_to_place(&self, place: Place<'tcx>) -> Vec<Place<'tcx>> {
        self.borrow_set
            .location_map
            .iter()
            .filter(|(_, borrow)| borrow.assigned_place == place)
            .map(|(_, borrow)| borrow.borrowed_place)
            .collect()
    }

    fn find_exclusive_loan_assigned_to_place(
        &self,
        state: &mut BorrowsDomain<'tcx>,
        origin: utils::Place<'tcx>,
    ) -> Option<Borrow<'tcx>> {
        let loans_to = state
            .live_borrows
            .iter()
            .filter(|borrow| borrow.assigned_place(&self.borrow_set) == origin.into())
            .collect::<Vec<_>>();
        // assert!(loans_to.len() == 1);
        loans_to.first().copied().cloned()
    }

    fn remove_loans_assigned_to(
        &self,
        state: &mut BorrowsDomain<'tcx>,
        assigned_to: Place<'tcx>,
    ) -> FxHashSet<Borrow<'tcx>> {
        let (to_remove, to_keep): (FxHashSet<_>, FxHashSet<_>) = state
            .live_borrows
            .clone()
            .into_iter()
            .partition(|borrow| borrow.assigned_place(&self.borrow_set) == assigned_to.into());

        state.live_borrows = to_keep;

        to_remove
    }

    fn remove_loans_borrowed_from(
        &self,
        state: &mut BorrowsDomain<'tcx>,
        origin: Place<'tcx>,
    ) -> FxHashSet<Borrow<'tcx>> {
        let (to_remove, to_keep): (FxHashSet<_>, FxHashSet<_>) = state
            .live_borrows
            .clone()
            .into_iter()
            .partition(|borrow| borrow.borrowed_place(&self.borrow_set) == origin.into());

        state.live_borrows = to_keep;

        to_remove
    }

    fn outlives_or_eq(&self, sup: RegionVid, sub: RegionVid) -> bool {
        if sup == sub {
            true
        } else {
            // eprintln!("Checking outlives {:?} {:?}", sup, sub);
            self.region_inference_context
                .outlives_constraints()
                .any(|constraint| {
                    sup == constraint.sup
                        && (sub == constraint.sub || self.outlives_or_eq(constraint.sub, sub))
                })
        }
    }
}

impl<'tcx, 'a> AnalysisDomain<'tcx> for BorrowsEngine<'a, 'tcx> {
    type Domain = BorrowsDomain<'tcx>;
    type Direction = Forward;
    const NAME: &'static str = "borrows";

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        todo!()
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        todo!()
    }
}

fn get_location(rich_location: RichLocation) -> Location {
    match rich_location {
        RichLocation::Start(location) => location,
        RichLocation::Mid(location) => location,
    }
}

impl<'tcx, 'a> Analysis<'tcx> for BorrowsEngine<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut BorrowsDomain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
    }

    fn apply_statement_effect(
        &mut self,
        state: &mut BorrowsDomain<'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        if let Some(loan) = self.loan_issued_at_location(location) {
            let loan_borrow_data = &self.borrow_set[loan];
            state.add_rustc_borrow(loan);
        }
        match &statement.kind {
            StatementKind::Assign(box (target, rvalue)) => match rvalue {
                Rvalue::Use(Operand::Move(from)) => {
                    self.remove_loans_assigned_to(state, *target);
                    let loans_to_move = self.remove_loans_assigned_to(state, *from);
                    for loan in loans_to_move {
                        state.add_borrow(Borrow::new(
                            BorrowKind::PCS {
                                borrowed_place: loan.borrowed_place(&self.borrow_set),
                                assigned_place: (*target).into(),
                            },
                            None,
                        ));
                    }
                }
                _ => {}
            },
            StatementKind::StorageDead(local) => {
                state
                    .live_borrows
                    .retain(|borrow| borrow.assigned_place(&self.borrow_set).local != *local);
            }
            _ => {}
        }
        // Implement logic to update the state after a statement
        // No additional logic needed for now
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut BorrowsDomain<'tcx>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                call_source,
                fn_span,
            } => {
                for dest_region in self.get_regions_in(
                    destination.ty(self.body.local_decls(), self.tcx).ty,
                    location,
                ) {
                    let mut region_abstraction = RegionAbstraction::new();
                    region_abstraction.add_loan_out(*destination);
                    for arg in args.iter() {
                        for arg_region in
                            self.get_regions_in(arg.ty(self.body.local_decls(), self.tcx), location)
                        {
                            if self.outlives_or_eq(arg_region, dest_region) {
                                for origin_place in
                                    self.placed_loaned_to_place(arg.place().unwrap())
                                {
                                    region_abstraction.add_loan_in(origin_place);
                                }
                            }
                        }
                    }
                    eprintln!("Add RA {:?}", region_abstraction);
                    state.add_region_abstraction(region_abstraction);
                }
            }
            _ => {}
        }
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut BorrowsDomain<'tcx>,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        match &terminator.kind {
            TerminatorKind::Call { args, .. } => {
                for arg in args {
                    if let Operand::Move(arg) = arg {
                        self.remove_loans_assigned_to(state, *arg);
                    }
                }
            }
            _ => {}
        }
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        state: &mut Self::Domain,
        block: BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        todo!()
    }
}
