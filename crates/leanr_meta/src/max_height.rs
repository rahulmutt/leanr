//! oracle: `getMaxHeight` (`Lean/Environment.lean:2890-2901`). Seam:
//! `defHeightOverrideExt` (`:2883-2888`) is not modelled — only
//! structural recursion writes it, which M4c-1 does not elaborate.

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::{ConstantInfo, ReducibilityHints};

use crate::{MetaCtx, MetaError};

impl<'e> MetaCtx<'e> {
    /// oracle: `getMaxHeight` — `foldConsts` visits every distinct
    /// subterm once; each `.const` resolving to a definition with
    /// `.regular h` hints raises the max.
    pub fn get_max_height(&mut self, e: ExprId) -> Result<u32, MetaError> {
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![e];
        let mut max = 0u32;
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            self.step()?;
            match self.node(x) {
                Node::Const { name: Some(n), .. } => {
                    if let Some(ConstantInfo::Defn(v)) = self.view.get(n) {
                        if let ReducibilityHints::Regular(h) = v.hints {
                            max = max.max(h);
                        }
                    }
                }
                Node::App { f, arg } => stack.extend([f, arg]),
                Node::Lam {
                    binder_type, body, ..
                }
                | Node::Forall {
                    binder_type, body, ..
                } => stack.extend([binder_type, body]),
                Node::LetE {
                    ty, value, body, ..
                } => stack.extend([ty, value, body]),
                Node::MData { expr, .. } => stack.push(expr),
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                    stack.push(structure)
                }
                _ => {}
            }
        }
        Ok(max)
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::{app, c, with_meta0_ctx};

    #[test]
    fn max_height_takes_the_max_regular_hint_and_ignores_abbrev_and_theorems() {
        with_meta0_ctx(|ctx| {
            let id = c(ctx, "id"); // regular 1
            let sunfold = c(ctx, "count._sunfold"); // regular 2
            let ndrec = c(ctx, "Eq.ndrec"); // abbrev
            let thm = c(ctx, "twoZeroEqA"); // theorem
            let ctor = c(ctx, "N.zero"); // constructor
            assert_eq!(ctx.get_max_height(id).unwrap(), 1);
            let e = app(ctx, sunfold, id);
            assert_eq!(ctx.get_max_height(e).unwrap(), 2);
            let e = app(ctx, id, sunfold);
            assert_eq!(ctx.get_max_height(e).unwrap(), 2, "order-independent max");
            let e = app(ctx, ndrec, thm);
            let e = app(ctx, e, ctor);
            assert_eq!(ctx.get_max_height(e).unwrap(), 0);
        });
    }
}
