use prusti_rustc_interface::{
    errors::{EmissionGuarantee, MultiSpan, Diag},
    middle::ty::TyCtxt,
};

pub struct EnvDiagnostic<'tcx> {
    tcx: TyCtxt<'tcx>,
    // warn_buffer: RefCell<Vec<prusti_rustc_interface::errors::Diagnostic>>,
}

impl<'tcx> EnvDiagnostic<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        EnvDiagnostic {
            tcx,
            // warn_buffer: RefCell::new(Vec::new()),
        }
    }

    fn configure_diagnostic<S: Into<MultiSpan> + Clone, T: EmissionGuarantee>(
        diagnostic: &mut Diag<T>,
        sp: S,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        diagnostic.span(sp);
        if let Some(help_msg) = help {
            diagnostic.help(help_msg.clone());
        }
        for (note_msg, opt_note_sp) in notes {
            if let Some(note_sp) = opt_note_sp {
                diagnostic.span_note(note_sp.clone(), note_msg.clone());
            } else {
                diagnostic.note(note_msg.clone());
            }
        }
    }

    /// Emits an error message.
    pub fn span_err_with_help_and_notes<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        let mut diagnostic = self.tcx.sess.dcx().struct_err(msg.to_string());
        Self::configure_diagnostic(&mut diagnostic, sp, help, notes);
        // TODO
        // for warn in self.warn_buffer.borrow_mut().iter_mut() {
        //     self.tcx.sess.dcx().emit_diagnostic(warn.clone());
        // }
        diagnostic.emit();
    }

    /// Emits a warning message.
    pub fn span_warn_with_help_and_notes<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        let mut diagnostic = self.tcx.sess.dcx().struct_warn(msg.to_string());
        Self::configure_diagnostic(&mut diagnostic, sp, help, notes);
        diagnostic.emit();
    }

    /// Buffers a warning message, to be emitted on error.
    pub fn span_warn_on_err_with_help_and_notes<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        let mut diagnostic = self.tcx.sess.dcx().struct_warn(msg.to_string());
        Self::configure_diagnostic(&mut diagnostic, sp, help, notes);
        diagnostic.emit();
        // TODO: original buffer logic
        // diagnostic.buffer(&mut self.warn_buffer.borrow_mut());
    }

    /// Returns true if an error has been emitted
    pub fn has_errors(&self) -> bool {
        self.tcx.sess.dcx().has_errors().is_some()
    }
}
