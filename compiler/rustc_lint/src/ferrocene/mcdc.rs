use compiler::rustc_session::{declare_lint, declare_lint_pass};

use crate::{LateContext};

declare_lint! {
    pub BASIC_LINT,
    Warn,
    "does something basic"
}