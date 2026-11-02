use core::panic;
use std::vec::Vec;
use std::ops::Index;

use rustc_hir as hir;
use rustc_ast as ast;
use rustc_span as span;
//use rustc_macros::Diagnostic;
use rustc_session::{declare_lint, declare_lint_pass};
use rustc_data_structures::fx::FxHashMap;
use rustc_ast::{BinOpKind, UnOp};
use petgraph as pg;

use crate::{LateContext, LateLintPass, /*LintContext*/};

/// A representation of a three-valued bit.
#[derive(Clone, Copy)]
enum Trit {
    TRUE,
    FALSE,
    UNKNOWN,
}

/// Converts a boolean value to a three-state value.
fn trit_from_bool(value: bool) -> Trit {
    match value {
        true => Trit::TRUE,
        false => Trit::FALSE,
    }
}

/// Coerces a three-value bit into a boolean.
/// If the value is unknown, an error is returned.
fn bool_from_trit(value: Trit) -> Result<bool, &'static str> {
    match value {
        Trit::TRUE => Ok(true),
        Trit::FALSE => Ok(false),
        Trit::UNKNOWN => Err("value is unknown"),
    }
}

/// A Boolean condition identified in Rust code.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
enum Condition {
    LITERAL(bool),
    LOCAL(hir::HirId),
    FIELD(hir::HirId, span::Symbol),
    EXPRESSION(hir::HirId),
}

/// A node in a tree-based representation of a Boolean expression written in Rust.
#[derive(Clone, Copy, Debug)]
enum ParseNode {
    AND,
    OR,
    NOT,
    LEAF(Condition),
}

/// A representation of a Boolean expression as a tree.
type ParseTreeGraph = pg::stable_graph::StableGraph<ParseNode, ()>;

/// A mapping from Boolean variables (MC/DC conditions) to their occurrences in an expression tree.
type ConditionMap = FxHashMap<Condition, Vec<pg::graph::NodeIndex>>;

/// A representation of a Boolean expression (MC/DC decision) as parsed by the HIR.
#[derive(Clone)]
struct ParseTree {
    tree: ParseTreeGraph,
    root: pg::graph::NodeIndex,
    conditions: ConditionMap,
}

/// Represents the children of a node in a parse tree.
enum ParseNodeChildren {
    AND(pg::graph::NodeIndex, pg::graph::NodeIndex),
    OR(pg::graph::NodeIndex, pg::graph::NodeIndex),
    NOT(pg::graph::NodeIndex),
    LEAF(),
}

impl ParseTree {
    /// Build a new parse tree from an HIR expression.
    fn new(expr: &hir::Expr<'_>) -> Self {
        let mut tree = ParseTreeGraph::new();
        let mut conditions = ConditionMap::default();
        let root = parse_decision_recursive(expr, &mut tree, &mut conditions, None);

        Self {
            tree,
            root,
            conditions,
        }
    }

    /// Tries to compute the value of a node by looking only at the given node.
    /// Returns true or false for literal nodes, otherwise returns unknown.
    fn node_value(self: &Self, node: pg::graph::NodeIndex) -> Trit {
        if !self.tree.contains_node(node) {
            // A Result type might handle this more gracefully, but it
            // also clutters code that calls this function.
            panic!("node is not in the parse tree");
        }

        if let ParseNode::LEAF(condition) = self.tree[node] {
            if let Condition::LITERAL(value) = condition {
                return trit_from_bool(value);
            }
        }

        Trit::UNKNOWN
    }

    /// Finds the parent of the given node in the parse tree.
    fn node_parent(self: &Self, node: pg::graph::NodeIndex) -> Option<pg::graph::NodeIndex> {
        let mut parents = self.tree.neighbors_directed(node, pg::Direction::Incoming);

        match parents.next() {
            Some(parent) => {
                match parents.next() {
                    Some(_) => panic!("mal-formed parse tree: node {:?} has more than one parent", self.tree[node]),
                    None => Some(parent),
                }
            },
            None => {
                if self.tree.contains_node(node) {
                    None
                } else {
                    // Again, we could use a Result here.
                    panic!("node is not in the parse tree");
                }
            },
        }
    }

    /// Finds the children of the given node in the parse tree.
    fn node_children(self: &Self, node: pg::graph::NodeIndex) -> ParseNodeChildren {
        if !self.tree.contains_node(node) {
            // Again, we could use a Result here.
            panic!("node is not in the parse tree");
        }

        let children: Vec<pg::graph::NodeIndex> = self.tree.neighbors_directed(node, pg::Direction::Outgoing).collect();

        match self.tree[node] {
            ParseNode::AND => {
                if children.len() == 2 {
                    ParseNodeChildren::AND(children[0], children[1])
                } else {
                    panic!("mal-formed parse tree: AND node does not have exactly two children");
                }
            },
            ParseNode::OR => {
                if children.len() == 2 {
                    ParseNodeChildren::OR(children[0], children[1])
                } else {
                    panic!("mal-formed parse tree: OR node does not have exactly two children");
                }
            },
            ParseNode::NOT => {
                if children.len() == 1 {
                    ParseNodeChildren::NOT(children[0])
                } else {
                    panic!("mal-formed parse tree: NOT node does not have exactly one child");
                }
            },
            ParseNode::LEAF(_) => {
                if children.len() == 0 {
                    ParseNodeChildren::LEAF()
                } else {
                    panic!("mal-formed parse tree: leaf node has children");
                }
            },
        }
    }

    /// Computes the value of a node using information derived from its children.
    fn node_evaluate(self: &Self, node: pg::graph::NodeIndex) -> Trit {
        // We're only going to search one level deep here.
        // TODO: This assumes that there are no sub-decisions with only literal
        // leaves. Address this assumption later! If a branch of the tree has only
        // literal leaves, it will never be visited during BDD construction. This
        // will eventually cause issues with the correctness of this function.
        match self.node_children(node) {
            ParseNodeChildren::AND(a, b) => {
                let a_tr = self.node_value(a);
                let b_tr = self.node_value(b);

                match a_tr {
                    Trit::FALSE => Trit::FALSE,
                    Trit::TRUE => b_tr,
                    Trit::UNKNOWN => match b_tr {
                        Trit::FALSE => Trit::FALSE,
                        _ => Trit::UNKNOWN,
                    },
                }
            },
            ParseNodeChildren::OR(a, b) => {
                let a_tr = self.node_value(a);
                let b_tr = self.node_value(b);

                match a_tr {
                    Trit::TRUE => Trit::TRUE,
                    Trit::FALSE => b_tr,
                    Trit::UNKNOWN => match b_tr {
                        Trit::TRUE => Trit::TRUE,
                        _ => Trit::UNKNOWN,
                    }
                }
            },
            ParseNodeChildren::NOT(a) => {
                match self.node_value(a) {
                    Trit::FALSE => Trit::TRUE,
                    Trit::TRUE => Trit::FALSE,
                    Trit::UNKNOWN => Trit::UNKNOWN,
                }
            },
            ParseNodeChildren::LEAF() => self.node_value(node),
        }
    }

    /// Removes a node and all its descendants from the parse tree.
    /// Updates the parse tree's conditions vector where necessary.
    fn remove_node(self: &mut Self, node: pg::graph::NodeIndex) {
        match self.node_children(node) {
            ParseNodeChildren::AND(a, b) | ParseNodeChildren::OR(a, b) => {
                self.remove_node(a);
                self.remove_node(b);
            },
            ParseNodeChildren::NOT(a) => {
                self.remove_node(a);
            },
            ParseNodeChildren::LEAF() => {
                // Here we remove the condition from the parse tree's list of conditions if it appears therein.
                if let ParseNode::LEAF(cond) = self.tree.index(node) {
                    if let Some(cond_nodes) = self.conditions.get_mut(cond) {
                        // Note: `position` returns the first instance of n to satisfy the predicate.
                        if let Some(node_idx) = cond_nodes.iter().position(|n| {*n == node}) {
                            cond_nodes.remove(node_idx);
                        }

                        if cond_nodes.len() == 0 {
                            self.conditions.remove(cond);
                        }
                    }
                } else {
                    // Don't expect to see this, but just in case...
                    panic!("node was incorrectly identified as a leaf");
                }
            },
        }

        self.tree.remove_node(node);
    }

    /// Recursively ascends the parse tree from a given node, resolving
    /// the nodes to literals where possible. If the ascent encounters an
    /// unresolvable node, "unknown" is returned. If the ascent reaches the
    /// root of the parse tree, a concrete (true/false) value is returned. 
    /// The children of resolved nodes are removed from the parse tree.
    fn ascend_tree(self: &mut Self, node: pg::graph::NodeIndex) -> Trit {
        let resolution = self.node_evaluate(node);

        match resolution {
            Trit::FALSE | Trit::TRUE => {
                let parent = self.node_parent(node);
                
                // Since the node has resolved to a value, we no longer need to consider anything below it.
                self.remove_node(node);

                // We're going to replace the newly resolved node with a literal representing its resolution.
                let resolved = self.tree.add_node(ParseNode::LEAF(Condition::LITERAL(bool_from_trit(resolution).unwrap())));

                match parent {
                    Some(parent) => {
                        // This node has resolved, continue by checking its parent.
                        self.tree.add_edge(parent, resolved, ());
                        self.ascend_tree(parent)
                    },
                    None => {
                        // The tree is fully resolved.
                        self.root = resolved;
                        resolution
                    },
                }
            },
            Trit::UNKNOWN => {
                // We've hit an unresolvable node and can go no further.
                Trit::UNKNOWN
            },
        }
    }
}

/// A representation of a BDD as a directed acyclic graph.
type BDDGraph = pg::stable_graph::StableGraph<Condition, bool>;

/// A Binary Decision Diagram (BDD). This is a binary tree representing all possible
/// evaluations of a Boolean decision (expression) made up of Boolean conditions.
struct BDD {
    tree: BDDGraph,
    root: Option<pg::graph::NodeIndex>,
    true_terminal: pg::graph::NodeIndex,
    false_terminal: pg::graph::NodeIndex,
}

/// Uniquely identifies a node in a BDD.
#[derive(Eq, PartialEq, Hash)]
struct BDDNodeIdentity {
    condition: Condition,
    resolve_true: pg::graph::NodeIndex,
    resolve_false: pg::graph::NodeIndex,
}

/// Keeps track of BDD nodes during BDD construction to prevent the
/// insertion of duplicate nodes. Maps node identities to node indices.
type BDDNodeMap = FxHashMap<BDDNodeIdentity, pg::graph::NodeIndex>;

impl BDD {
    /// Build a new BDD from a parse tree.
    fn new(decision: &ParseTree) -> Self {
        let mut bdd_graph = BDDGraph::new();
        let true_terminal = bdd_graph.add_node(Condition::LITERAL(true));
        let false_terminal = bdd_graph.add_node(Condition::LITERAL(false));

        let mut bdd = Self {
            tree: bdd_graph,
            root: None,
            true_terminal,
            false_terminal,
        };

        let mut mutable_decision = decision.clone();
        // Query instability is not an issue here because:
        // (1) the predicate operates on individual key/value pairs,
        // (2) the predicate has no side effects.
        #[allow(rustc::potential_query_instability)]
        mutable_decision.conditions.retain(|_, occurrences| -> bool {occurrences.len() > 0});

        let mut node_map = BDDNodeMap::default();

        bdd.root = Self::new_recursive(&mut bdd, &mut mutable_decision, &mut node_map);

        bdd
    }

    /// Build out the BDD from a parse tree by selecting a condition to resolve. Once
    /// a condition is selected, sub-BDDs are computed based on the resolution of the
    /// condition to true and false. If there are conditions to resolve, a BDD node
    /// is returned, otherwise `None` is returned.
    fn new_recursive(self: &mut Self, decision: &mut ParseTree, node_map: &mut BDDNodeMap) -> Option<pg::graph::NodeIndex> {
        // Query instability is not an issue here because:
        // (1) all we need is an arbitrary condition,
        // (2) the condition will be removed from the mapping during resolution.
        #[allow(rustc::potential_query_instability)]
        if let Some((condition, _)) = decision.conditions.iter().next() {
            // Compute the sub-BDDs where the condition under consideration has been resolved true and false.
            // TODO: May want to consider representing the parse tree as a tree of pointers to keep copy overhead down.
            let node_identity = BDDNodeIdentity {
                condition: *condition,
                resolve_true: self.new_resolution(true, &mut decision.clone(), node_map, condition),
                resolve_false: self.new_resolution(false, &mut decision.clone(), node_map, condition),
            };

            if let Some(node) = node_map.get(&node_identity) {
                // If an identical node exists in the BDD, use it instead.
                return Some(*node);
            } else {
                if node_identity.resolve_false == node_identity.resolve_true {
                    // If both true and false resolutions resolve to the same child, use it instead.
                    return Some(node_identity.resolve_false);
                } else {
                    // The new node is only added to the BDD if it is unique and non-redundant (to maintain "reducedness").
                    let node = self.tree.add_node(node_identity.condition);
                    self.tree.add_edge(node, node_identity.resolve_false, false);
                    self.tree.add_edge(node, node_identity.resolve_true, true);

                    node_map.insert(node_identity, node);

                    return Some(node);
                }
            }
        }
        
        None
    }

    /// Build out the BDD and simplify the parse tree by resolving a condition
    /// to a given boolean value. When every occurrence of the condition resolved,
    /// a BDD node representing the resolution of the remaining conditions is returned.
    fn new_resolution(self: &mut Self, resolution: bool, decision: &mut ParseTree, node_map: &mut BDDNodeMap, condition: &Condition) -> pg::graph::NodeIndex {
        if let Some(occurrences) = decision.conditions.remove(condition) {
            // Start by resolving all occurrences of the condition in the parse tree.
            for occurrence in occurrences.iter() {
                decision.tree[*occurrence] = ParseNode::LEAF(Condition::LITERAL(resolution));
            }

            for occurrence in occurrences.iter() {
                // Ascending the tree from one occurrence may remove other occurrences.
                if self.tree.contains_node(*occurrence) {
                    match decision.ascend_tree(*occurrence) {
                        Trit::FALSE => {
                            // The parse tree has fully resolved to false.
                            return self.false_terminal;
                        },
                        Trit::TRUE => {
                            // The parse tree has fully resolved to true.
                            return self.true_terminal;
                        },
                        Trit::UNKNOWN => {},
                    }
                }
            }
        }

        // Continue resolving additional conditions on the simplified parse tree.
        match self.new_recursive(decision, node_map) {
            Some(next) => {
                return next;
            },
            None => {
                // TODO: investigate how much this happens!
                panic!("parse tree is unresolved and contains no more conditions to consider");
            },
        }
    }
}

// TODO: get rid of this when it's no longer needed.
#[allow(dead_code)]
fn expr_to_str(expr: &hir::Expr<'_>) -> &'static str {
    match expr.kind {
        hir::ExprKind::ConstBlock(_) => "const block",
        hir::ExprKind::Array(_) => "array",
        hir::ExprKind::Call(_, _) => "call",
        hir::ExprKind::MethodCall(_, _, _, _) => "method call",
        hir::ExprKind::Use(_, _) => "use",
        hir::ExprKind::Tup(_) => "tuple",
        hir::ExprKind::Binary(_, _, _) => "binary op",
        hir::ExprKind::Unary(_, _) => "unary op",
        hir::ExprKind::Lit(_) => "literal",
        hir::ExprKind::Cast(_, _) => "cast",
        hir::ExprKind::Type(_, _) => "type",
        hir::ExprKind::DropTemps(_) => "drop temps",
        hir::ExprKind::Let(_) => "let",
        hir::ExprKind::If(_, _, _) => "if",
        hir::ExprKind::Loop(_, _, _, _) => "loop",
        hir::ExprKind::Match(_, _, _) => "match",
        hir::ExprKind::Closure(_) => "closure",
        hir::ExprKind::Block(_, _) => "block",
        hir::ExprKind::Assign(_, _, _) => "assign",
        hir::ExprKind::AssignOp(_, _, _) => "assign op",
        hir::ExprKind::Field(_, _) => "field",
        hir::ExprKind::Index(_, _, _) => "index",
        hir::ExprKind::Path(_) => "path",
        hir::ExprKind::AddrOf(_, _, _) => "addr of",
        hir::ExprKind::Break(_, _) => "break",
        hir::ExprKind::Continue(_) => "continue",
        hir::ExprKind::Ret(_) => "return",
        hir::ExprKind::Become(_) => "become",
        hir::ExprKind::InlineAsm(_) => "inline assembly",
        hir::ExprKind::OffsetOf(_, _) => "offset of",
        hir::ExprKind::Struct(_, _, _) => "struct",
        hir::ExprKind::Repeat(_, _) => "repeat",
        hir::ExprKind::Yield(_, _) => "yield",
        hir::ExprKind::UnsafeBinderCast(_, _, _) => "unsafe binder cast",
        hir::ExprKind::Err(_) => "error",
    }
}

// TODO: again, remove this when it's no longer needed
#[allow(dead_code)]
fn res_to_str(res: hir::def::Res) -> &'static str {
    match res {
        hir::def::Res::Def(_, _) => "def",
        hir::def::Res::Local(_) => "local",
        hir::def::Res::NonMacroAttr(_) => "non-macro attr",
        hir::def::Res::OpenMod(_) => "open mod",
        hir::def::Res::ToolMod => "tool mod",
        hir::def::Res::PrimTy(_) => "primitive type",
        hir::def::Res::SelfCtor(_) => "self ctor",
        hir::def::Res::SelfTyAlias{alias_to: _, is_trait_impl: _} => "self type alias",
        hir::def::Res::SelfTyParam{trait_: _} => "self type parameter",
        hir::def::Res::Err => "error",
    }
}

// TODO: remove when no longer needed
#[allow(dead_code)]
fn print_node(parse_tree: &ParseTree, node: pg::graph::NodeIndex) {
    match parse_tree.tree.index(node) {
        ParseNode::AND => {
            println!(" AND ");
        },
        ParseNode::OR => {
            println!(" OR ");
        },
        ParseNode::NOT => {
            println!(" NOT ");
        },
        ParseNode::LEAF(cond) => {
            print_condition(cond);
        },
    }

    for neighbour in parse_tree.tree.neighbors_directed(node, pg::Direction::Outgoing) {
        print_node(parse_tree, neighbour);
    }
}

// TODO: remove when no longer needed
#[allow(dead_code)]
fn print_condition(cond: &Condition) {
    match cond {
        Condition::LITERAL(value) => {
            println!(" (LIT {}) ", value);
        },
        Condition::LOCAL(id) => {
            println!(" (LOCAL {}) ", id);
        },
        Condition::FIELD(id, name) => {
            println!(" (FIELD {}, {}) ", id, name);
        },
        Condition::EXPRESSION(id) => {
            println!(" (EXPR {}) ", id);
        },
    }
}

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
    /*
    fn check_crate(&mut self, _ctx: &LateContext<'l>) {
        tracing::warn!("BASIC_LINT test artefact.");
        //todo!("you shall not pass");
        //ctx.emit_span_lint(BASIC_LINT, span, decorator);
    }
    */

    // TODO: remove this when no longer iterating over hash maps
    #[allow(rustc::potential_query_instability)]
    fn check_expr(&mut self, _ctx: &LateContext<'l>, expr: &hir::Expr<'_>) {
        /*
        if let hir::ExprKind::Match(_expr, arms, _source) = expr.kind {
            //tracing::warn!("found a match");
            //ctx.emit_span_lint(BASIC_LINT, expr.span, BasicDiagnostic{});
            for arm in arms {
                if let Some(guard) = arm.guard {
                    ctx.emit_span_lint(BASIC_LINT, guard.span, BasicDiagnostic{});
                }
            }
        }
        */
        if let hir::ExprKind::If(decision, _, _) = expr.kind {
            let parse_tree = ParseTree::new(decision);
            //println!("{}", pg::dot::Dot::with_config(&parse_tree, &[pg::dot::Config::EdgeNoLabel]));
            print_node(&parse_tree, parse_tree.root);
            println!();
            for (k, v) in parse_tree.conditions.iter() {
                print_condition(&k);
                println!("\tOccurrences: {}", v.len());
            }
        }
    }
}

/*
/// Constructs a BDD from a parse tree.
fn build_bdd(decision: &mut ParseTree) -> BDD {
    //
}
*/

/// TODO
fn parse_decision_recursive(expr: &hir::Expr<'_>, decision: &mut ParseTreeGraph, conditions: &mut ConditionMap, parent: Option<pg::graph::NodeIndex>) -> pg::graph::NodeIndex {
    match expr.kind {
        hir::ExprKind::Binary(op, a, b) => {
            let op_node: Option<ParseNode> = match op.node {
                BinOpKind::And => Some(ParseNode::AND),
                BinOpKind::Or => Some(ParseNode::OR),
                _ => None,
            };

            if let Some(op_node) = op_node {
                let node = add_decision_node(op_node, decision, parent);
                parse_decision_recursive(a, decision, conditions, Some(node));
                parse_decision_recursive(b, decision, conditions, Some(node));
                return node;
            }
        },
        hir::ExprKind::Unary(op, a) => {
            if let UnOp::Not = op {
                let node = add_decision_node(ParseNode::NOT, decision, parent);
                parse_decision_recursive(a, decision, conditions, Some(node));
                return node;
            }
        },
        _ => {}
    }

    let condition = parse_condition(expr);
    let node = add_decision_node(ParseNode::LEAF(condition), decision, parent);
    conditions.entry(condition)
        .and_modify(|nodes| {nodes.push(node);})
        .or_insert(vec![node]);

    node
}

/// TODO
fn add_decision_node(kind: ParseNode, decision: &mut ParseTreeGraph, parent: Option<pg::graph::NodeIndex>) -> pg::graph::NodeIndex {
    let node = decision.add_node(kind);
    if let Some(parent) = parent {
        decision.add_edge(parent, node, ());
    }

    node
}

/// Attempts to create a new `Condition` (parse tree leaf node) from an HIR expression.
fn parse_condition(expr: &hir::Expr<'_>) -> Condition {
    match expr.kind {
        hir::ExprKind::Lit(lit) => {
            if let ast::LitKind::Bool(value) = lit.node {
                return Condition::LITERAL(value);
            }

            // The compiler should already catch non-booleans in if statements.
            panic!("if statement contains non-boolean literal condition");
        },
        hir::ExprKind::Path(q_path) => {
            let hir_id = match resolve_path(q_path) {
                Some(hir_id) => hir_id,
                None => expr.hir_id,
            };

            Condition::LOCAL(hir_id)
        },
        hir::ExprKind::Field(structure, field) => {
            match structure.kind {
                hir::ExprKind::Path(q_path) => {
                    let hir_id = match resolve_path(q_path) {
                        Some(hir_id) => hir_id,
                        None => structure.hir_id,
                    };

                    Condition::FIELD(hir_id, field.name)
                },
                _ => {
                    // TODO: This is a sloppy catch-all, get more specific.
                    Condition::FIELD(structure.hir_id, field.name)
                },
            }
        },
        // Functions/methods must be assumed to be non-deterministic unless they are marked `const`.
        /*
        hir::ExprKind::Call(_, _) => _,
        hir::ExprKind::MethodCall(_, _, _, _) => _,
        */
        _ => {
            // Careful: using the expression's HIR ID assumes that the expression is a unique condition.
            // This could cause issues with MC/DC if an expression is repeated in some way.
            // More specificity is more better.
            // Otherwise, maybe we should just assume the most pessimistic case: that all EXPRESSION variants are mutually dependent.
            Condition::EXPRESSION(expr.hir_id)
        },
    }
}

/// Resolves a given path to produce a unique identifier for the path's expression.
fn resolve_path(q_path: hir::QPath<'_>) -> Option<hir::HirId> {
    let resolution = match q_path {
        hir::QPath::Resolved(_, path) => path.res,
        // TODO: May need to reassess how we treat the `ty` (first) parameter here.
        hir::QPath::TypeRelative(_, path_segment) => path_segment.res,
    };

    match resolution {
        hir::def::Res::Local(hir_id) => Some(hir_id),
        // TODO: Handle more edge cases. Won't be able to handle all of them though (e.g. Err).
        _ => None,
    }
}

/*
// Define a simple diagnostic to report trouble spans.
#[derive(Diagnostic)]
#[diag("guard identified in match statement")]
struct BasicDiagnostic {}
*/