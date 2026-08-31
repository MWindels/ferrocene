use rustc_session::{declare_lint, declare_lint_pass};

use crate::{LateContext, LateLintPass};

// Define our Lint (sub)type. This carries "metadata" for the lint (severity level, descriptive info, etc).
declare_lint! {
    pub BASIC_LINT,
    Warn,
    "does something basic"
}

// Define our LintPass (sub)type. This supplies functionality to the Lint declared above.
declare_lint_pass!(BasicPass => [BASIC_LINT]);

// Implement some functionality for our LintPass (sub)type.
impl<'l> LateLintPass<'l> for BasicPass {
    fn check_crate(&mut self, _ctx: &LateContext<'l>) {
        tracing::warn!("BASIC_LINT test artefact.");
        //todo!("you shall not pass");
        //ctx.emit_span_lint(BASIC_LINT, span, decorator);
    }
}