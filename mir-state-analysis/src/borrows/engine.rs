use prusti_rustc_interface::{
    borrowck::consumers::{LocationTable, PoloniusInput, RichLocation},
    dataflow::{Analysis, AnalysisDomain, Forward},
    index::IndexVec,
    middle::{
        mir::{
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, Local, Location, Promoted,
            Statement, Terminator, TerminatorEdges, RETURN_PLACE, START_BLOCK,
        },
        ty::TyCtxt,
    },
};

use super::domain::BorrowsDomain;

pub struct BorrowsEngine<'mir> {
    location_table: &'mir LocationTable,
    input_facts: &'mir PoloniusInput,
}
impl<'mir> BorrowsEngine<'mir> {
    pub fn new(location_table: &'mir LocationTable, input_facts: &'mir PoloniusInput) -> Self {
        BorrowsEngine {
            location_table,
            input_facts,
        }
    }
}


impl<'tcx, 'a> AnalysisDomain<'tcx> for BorrowsEngine<'a> {
    type Domain = BorrowsDomain;
    type Direction = Forward;
    const NAME: &'static str = "borrows";

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        todo!()
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        todo!()
    }
}

impl<'tcx, 'a> Analysis<'tcx> for BorrowsEngine<'a> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut BorrowsDomain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
    }

    fn apply_statement_effect(
        &mut self,
        state: &mut BorrowsDomain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        for (origin, loan, loan_point) in self.input_facts.loan_issued_at.iter() {
            match self.location_table.to_location(*loan_point) {
                RichLocation::Start(loan_location) if loan_location == location => {
                    state.add_borrow(*loan);
                }
                RichLocation::Mid(loan_location) if loan_location == location => {
                    state.add_borrow(*loan);
                }
                _ => {}
            }
        }
        // Implement logic to update the state after a statement
        // No additional logic needed for now
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut BorrowsDomain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut BorrowsDomain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
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
