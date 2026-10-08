//! `Nat` offset constraints: `isDefEqOffset` and the helpers it rests on
//! (`evalNat`, `isOffset?`/`getOffset`, `mkOffset`).
//!
//! oracle: `Lean/Meta/Offset.lean` (toolchain leanprover/lean4:v4.33.0-rc1),
//! the structural instance testers of `Lean/Meta/NatInstTesters.lean:17-74`
//! (`open Structural`, Offset.lean:24), and the term builders of
//! `Lean/Expr.lean` (`mkNatLit` :741-750, `Nat.mkInstAdd`/`mkInstHAdd`
//! :2211-2212, `mkNatAdd` :2235-2253).
//!
//! # `match_expr` semantics
//!
//! Every Lean-side `match_expr`/`let_expr` here sits in a `do` block with
//! the default `meta := true`, which first runs `instantiateMVarsIfMVarApp`
//! on the discriminant (`Elab/BuiltinDo/MatchExpr.lean:43`,
//! `Meta/Basic.lean:2554-2558`) and then `Expr.cleanupAnnotations`
//! (`Elab/MatchExpr.lean:189`, `Expr.lean:1754-1756`). A pattern `F a1 .. an`
//! peels exactly `n` applications with `appFnCleanup` (`Expr.lean:1762-1764`)
//! and tests the head with `isConstOf F` (name only, levels ignored).
//! [`MetaCtx::match_expr_spine`] is that test.
//!
//! # Names
//!
//! Every constant name is interned lazily through `dotted` at its use site,
//! so `MetaCtx` carries no new fields.
//!
//! # What is NOT ported here
//!
//! The other `isOffset?` consumers stay seams: `cleanupNatOffsetMajor`
//! (`WHNF.lean:219`, `whnf.rs`) and `CtorRecognizer.lean:47,98`.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::Nat;

use crate::{MetaCtx, MetaError, TransparencyMode};

impl<'e> MetaCtx<'e> {
    /// `Expr.cleanupAnnotations` (`Expr.lean:1754-1756`): `consumeMData`
    /// (:1076-1078) then `consumeTypeAnnotations` (:1739-1745), to a fixpoint.
    fn cleanup_annotations(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let mut cur = e;
        loop {
            let mut next = cur;
            while let Node::MData { expr, .. } = self.node(next) {
                next = expr;
            }
            next = self.consume_type_annotations(next)?;
            if next == cur {
                return Ok(cur);
            }
            cur = next;
        }
    }

    /// `Expr.consumeTypeAnnotations` (`Expr.lean:1739-1745`): `optParam _ _`
    /// / `autoParam _ _` keep their first argument, `outParam _` /
    /// `semiOutParam _` their only one (`isAppOfArity`, :1709-1722).
    fn consume_type_annotations(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let mut cur = e;
        loop {
            let n = self.get_app_num_args(cur);
            let head = match self.node(self.get_app_fn(cur)) {
                Node::Const { name: Some(h), .. } => h,
                _ => return Ok(cur),
            };
            let args = self.get_app_args(cur);
            // Both arms keep the FIRST argument (`e.appFn!.appArg!` of a
            // binary gadget, `e.appArg!` of a unary one).
            let binary = n == 2
                && (head == self.dotted(&["optParam"])? || head == self.dotted(&["autoParam"])?);
            let unary = n == 1
                && (head == self.dotted(&["outParam"])?
                    || head == self.dotted(&["semiOutParam"])?);
            if !(binary || unary) {
                return Ok(cur);
            }
            cur = args[0];
        }
    }

    /// The discriminant preparation and spine walk of one `match_expr`
    /// (module doc): `instantiateMVarsIfMVarApp`, `cleanupAnnotations`, then
    /// the `appFnCleanup` peel. Returns the head constant's name and the
    /// arguments (raw, as the oracle binds them) in application order.
    fn match_expr_spine(&mut self, e: ExprId) -> Result<Option<(NameId, Vec<ExprId>)>, MetaError> {
        let e = if matches!(self.node(self.get_app_fn(e)), Node::MVar { .. }) {
            self.instantiate_mvars(e)?
        } else {
            e
        };
        let mut cur = self.cleanup_annotations(e)?;
        let mut args = Vec::new();
        while let Node::App { f, arg } = self.node(cur) {
            args.push(arg);
            cur = self.cleanup_annotations(f)?;
        }
        args.reverse();
        Ok(match self.node(cur) {
            Node::Const { name: Some(n), .. } => Some((n, args)),
            _ => None,
        })
    }

    /// `isConstOf` after the `match_expr` discriminant preparation: the
    /// zero-pattern-variable `let_expr c ← e` shape.
    fn match_expr_const(&mut self, e: ExprId, name: &[&str]) -> Result<bool, MetaError> {
        let want = self.dotted(name)?;
        Ok(matches!(self.match_expr_spine(e)?, Some((h, args)) if h == want && args.is_empty()))
    }

    /// `let_expr c a1 .. an ← e` returning the bound arguments.
    fn match_expr_app(
        &mut self,
        e: ExprId,
        name: &[&str],
        arity: usize,
    ) -> Result<Option<Vec<ExprId>>, MetaError> {
        let want = self.dotted(name)?;
        Ok(match self.match_expr_spine(e)? {
            Some((h, args)) if h == want && args.len() == arity => Some(args),
            _ => None,
        })
    }

    /// `Structural.isInst*` (`NatInstTesters.lean:23-64`): syntactic tests,
    /// as `evalNat` uses them (`open Structural`, Offset.lean:24).
    fn is_inst_nat_structural(&mut self, op: NatInstOp, i: ExprId) -> Result<bool, MetaError> {
        Ok(match op {
            // :23-25
            NatInstOp::OfNat => self.match_expr_app(i, &["instOfNatNat"], 1)?.is_some(),
            // :26-40
            NatInstOp::Add => self.match_expr_const(i, &["instAddNat"])?,
            NatInstOp::Sub => self.match_expr_const(i, &["instSubNat"])?,
            NatInstOp::Mul => self.match_expr_const(i, &["instMulNat"])?,
            NatInstOp::Div => self.match_expr_const(i, &["Nat", "instDiv"])?,
            NatInstOp::Mod => self.match_expr_const(i, &["Nat", "instMod"])?,
            // :41-43
            NatInstOp::NatPow => self.match_expr_const(i, &["instNatPowNat"])?,
            // :44-46
            NatInstOp::Pow => match self.match_expr_app(i, &["instPowNat"], 2)? {
                Some(a) => self.is_inst_nat_structural(NatInstOp::NatPow, a[1])?,
                None => false,
            },
            // :47-61: `instH* _ i` then the homogeneous test on `i`.
            NatInstOp::H(inner) => {
                let (name, base) = match inner {
                    HOp::Add => ("instHAdd", NatInstOp::Add),
                    HOp::Sub => ("instHSub", NatInstOp::Sub),
                    HOp::Mul => ("instHMul", NatInstOp::Mul),
                    HOp::Div => ("instHDiv", NatInstOp::Div),
                    HOp::Mod => ("instHMod", NatInstOp::Mod),
                };
                match self.match_expr_app(i, &[name], 2)? {
                    Some(a) => self.is_inst_nat_structural(base, a[1])?,
                    None => false,
                }
            }
            // :62-64
            NatInstOp::HPow => match self.match_expr_app(i, &["instHPow"], 3)? {
                Some(a) => self.is_inst_nat_structural(NatInstOp::Pow, a[2])?,
                None => false,
            },
        })
    }

    /// oracle: `evalNat` (Offset.lean:28-64). `None` is `OptionT`'s
    /// `failure`. Assumes `e : Nat` (the oracle's own remark).
    pub(crate) fn eval_nat(&mut self, e: ExprId) -> Result<Option<Nat>, MetaError> {
        self.guarded(|ctx| match ctx.node(e) {
            Node::LitNat { v } => Ok(Some(ctx.scratch.nat_at(Some(ctx.view.store), v).clone())),
            Node::MData { expr, .. } => ctx.eval_nat(expr),
            Node::Const { name: Some(n), .. } if n == ctx.nat_zero => Ok(Some(Nat::from(0u64))),
            Node::App { .. } | Node::MVar { .. } => ctx.eval_nat_visit(e),
            _ => Ok(None),
        })
    }

    /// `evalNat.visit` (Offset.lean:41-64).
    fn eval_nat_visit(&mut self, e: ExprId) -> Result<Option<Nat>, MetaError> {
        let (head, args) = match self.match_expr_spine(e)? {
            Some(x) => x,
            None => return Ok(None),
        };
        // `OfNat.ofNat _ n i` (:43).
        if args.len() == 3 && head == self.dotted(&["OfNat", "ofNat"])? {
            if !self.is_inst_nat_structural(NatInstOp::OfNat, args[2])? {
                return Ok(None);
            }
            return self.eval_nat(args[1]);
        }
        // `Nat.succ a` (:44).
        if args.len() == 1 && head == self.nat_succ {
            return Ok(self.eval_nat(args[0])?.map(|v| v.add(&Nat::from(1u64))));
        }
        let (op, a, b) = match self.nat_bin_op_of(head, &args)? {
            Some(x) => x,
            None => return Ok(None),
        };
        if op == BinOp::Pow {
            // `evalPow` (:37-40): the exponent first, then `checkExponent`.
            let n = match self.eval_nat(b)? {
                Some(n) => n,
                None => return Ok(None),
            };
            let exp = match n.to_usize() {
                Some(k) if k <= crate::whnf::EXPONENTIATION_THRESHOLD => k,
                _ => return Ok(None),
            };
            return Ok(self.eval_nat(a)?.map(|base| base.pow(exp as u32)));
        }
        let va = match self.eval_nat(a)? {
            Some(v) => v,
            None => return Ok(None),
        };
        let vb = match self.eval_nat(b)? {
            Some(v) => v,
            None => return Ok(None),
        };
        Ok(Some(match op {
            BinOp::Add => va.add(&vb),
            BinOp::Sub => va.sub(&vb),
            BinOp::Mul => va.mul(&vb),
            BinOp::Div => va.div(&vb),
            BinOp::Mod => va.modulo(&vb),
            BinOp::Pow => unreachable!("handled above"),
        }))
    }

    /// The arithmetic arms of `evalNat.visit` (Offset.lean:45-63): `Nat.op a
    /// b`, `Op.op _ i a b` and `HOp.hOp _ _ _ i a b`, each instance guarded by
    /// its `Structural` tester. Returns the operation and its two operands,
    /// or `None` when no arm matches or the guard fails.
    fn nat_bin_op_of(
        &mut self,
        head: NameId,
        args: &[ExprId],
    ) -> Result<Option<(BinOp, ExprId, ExprId)>, MetaError> {
        const TABLE: [(BinOp, &str, &str, &str, &str, &str); 5] = [
            (BinOp::Add, "add", "Add", "add", "HAdd", "hAdd"),
            (BinOp::Sub, "sub", "Sub", "sub", "HSub", "hSub"),
            (BinOp::Mul, "mul", "Mul", "mul", "HMul", "hMul"),
            (BinOp::Div, "div", "Div", "div", "HDiv", "hDiv"),
            (BinOp::Mod, "mod", "Mod", "mod", "HMod", "hMod"),
        ];
        match args.len() {
            2 => {
                for (op, nat_fn, ..) in TABLE {
                    if head == self.dotted(&["Nat", nat_fn])? {
                        return Ok(Some((op, args[0], args[1])));
                    }
                }
                if head == self.dotted(&["Nat", "pow"])? {
                    return Ok(Some((BinOp::Pow, args[0], args[1])));
                }
                Ok(None)
            }
            4 => {
                for (op, _, cls, f, ..) in TABLE {
                    if head == self.dotted(&[cls, f])? {
                        let inst = match op {
                            BinOp::Add => NatInstOp::Add,
                            BinOp::Sub => NatInstOp::Sub,
                            BinOp::Mul => NatInstOp::Mul,
                            BinOp::Div => NatInstOp::Div,
                            BinOp::Mod => NatInstOp::Mod,
                            BinOp::Pow => unreachable!(),
                        };
                        return Ok(self
                            .is_inst_nat_structural(inst, args[1])?
                            .then_some((op, args[2], args[3])));
                    }
                }
                if head == self.dotted(&["NatPow", "pow"])? {
                    return Ok(self
                        .is_inst_nat_structural(NatInstOp::NatPow, args[1])?
                        .then_some((BinOp::Pow, args[2], args[3])));
                }
                Ok(None)
            }
            5 => {
                if head == self.dotted(&["Pow", "pow"])? {
                    return Ok(self
                        .is_inst_nat_structural(NatInstOp::Pow, args[2])?
                        .then_some((BinOp::Pow, args[3], args[4])));
                }
                Ok(None)
            }
            6 => {
                for (op, _, _, _, hcls, hf) in TABLE {
                    if head == self.dotted(&[hcls, hf])? {
                        let h = match op {
                            BinOp::Add => HOp::Add,
                            BinOp::Sub => HOp::Sub,
                            BinOp::Mul => HOp::Mul,
                            BinOp::Div => HOp::Div,
                            BinOp::Mod => HOp::Mod,
                            BinOp::Pow => unreachable!(),
                        };
                        return Ok(self
                            .is_inst_nat_structural(NatInstOp::H(h), args[3])?
                            .then_some((op, args[4], args[5])));
                    }
                }
                if head == self.dotted(&["HPow", "hPow"])? {
                    return Ok(self
                        .is_inst_nat_structural(NatInstOp::HPow, args[3])?
                        .then_some((BinOp::Pow, args[4], args[5])));
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// oracle: `matchesInstance` (Offset.lean:72-74):
    /// `withNewMCtxDepth (withTransparency .instances (isDefEq e inst))`.
    fn matches_instance(&mut self, e: ExprId, inst: ExprId) -> Result<bool, MetaError> {
        self.with_new_mctx_depth(false, |ctx| {
            ctx.with_transparency(TransparencyMode::Instances, |ctx| ctx.is_def_eq(e, inst))
        })
    }

    /// oracle: `getOffset` (Offset.lean:83-84): `isOffset?` or `(e, 0)` —
    /// the ORIGINAL `e`, not the instantiated/cleaned discriminant.
    fn get_offset(&mut self, e: ExprId) -> Result<(ExprId, Nat), MetaError> {
        Ok(self.is_offset(e)?.unwrap_or_else(|| (e, Nat::from(0u64))))
    }

    /// oracle: `isOffset?` (Offset.lean:89-101).
    pub(crate) fn is_offset(&mut self, e: ExprId) -> Result<Option<(ExprId, Nat)>, MetaError> {
        self.guarded(|ctx| {
            let (head, args) = match ctx.match_expr_spine(e)? {
                Some(x) => x,
                None => return Ok(None),
            };
            // `Nat.succ a` (:95-97).
            if args.len() == 1 && head == ctx.nat_succ {
                let (s, k) = ctx.get_offset(args[0])?;
                return Ok(Some((s, k.add(&Nat::from(1u64)))));
            }
            let (a, b) = if args.len() == 2 && head == ctx.dotted(&["Nat", "add"])? {
                // :98
                (args[0], args[1])
            } else if args.len() == 4 && head == ctx.dotted(&["Add", "add"])? {
                // :99
                let inst = ctx.mk_inst_add_nat()?;
                if !ctx.matches_instance(args[1], inst)? {
                    return Ok(None);
                }
                (args[2], args[3])
            } else if args.len() == 6 && head == ctx.dotted(&["HAdd", "hAdd"])? {
                // :100
                let inst = ctx.mk_inst_hadd_nat()?;
                if !ctx.matches_instance(args[3], inst)? {
                    return Ok(None);
                }
                (args[4], args[5])
            } else {
                return Ok(None);
            };
            // `add a b` (:90-93): `evalNat b` first, then `getOffset a`.
            let v = match ctx.eval_nat(b)? {
                Some(v) => v,
                None => return Ok(None),
            };
            let (s, k) = ctx.get_offset(a)?;
            Ok(Some((s, k.add(&v))))
        })
    }

    /// oracle: `isNatZero` (Offset.lean:105-108).
    fn is_nat_zero(&mut self, e: ExprId) -> Result<bool, MetaError> {
        Ok(self.eval_nat(e)?.is_some_and(|v| v.is_zero()))
    }

    /// oracle: `mkOffset` (Offset.lean:110-116).
    fn mk_offset(&mut self, e: ExprId, offset: &Nat) -> Result<ExprId, MetaError> {
        if offset.is_zero() {
            Ok(e)
        } else if self.is_nat_zero(e)? {
            self.mk_nat_lit(offset)
        } else {
            let lit = self.mk_nat_lit(offset)?;
            self.mk_nat_add(e, lit)
        }
    }

    fn const_at_level_zero(
        &mut self,
        parts: &[&str],
        n_levels: usize,
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let name = self.dotted(parts)?;
        let z = self.scratch.level_zero(base)?;
        let zs = [z; 3];
        let ls = self.scratch.intern_level_list(base, &zs[..n_levels])?;
        Ok(self.scratch.expr_const(base, Some(name), ls)?)
    }

    fn nat_const(&mut self) -> Result<ExprId, MetaError> {
        self.const_at_level_zero(&["Nat"], 0)
    }

    /// oracle: `mkNatLit` (`Expr.lean:741-750`): `@OfNat.ofNat.{0} Nat
    /// (lit n) (instOfNatNat (lit n))` — the frontend's numeral, NOT the raw
    /// literal.
    pub(crate) fn mk_nat_lit(&mut self, n: &Nat) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let raw = self.scratch.expr_lit_nat(base, n)?;
        let of_nat = self.const_at_level_zero(&["OfNat", "ofNat"], 1)?;
        let nat = self.nat_const()?;
        let inst_fn = self.const_at_level_zero(&["instOfNatNat"], 0)?;
        let inst = self.scratch.expr_app(base, inst_fn, raw)?;
        self.mk_app_spine(of_nat, &[nat, raw, inst])
    }

    /// oracle: `Nat.mkInstAdd` (`Expr.lean:2211`).
    fn mk_inst_add_nat(&mut self) -> Result<ExprId, MetaError> {
        self.const_at_level_zero(&["instAddNat"], 0)
    }

    /// oracle: `Nat.mkInstHAdd` (`Expr.lean:2212`):
    /// `@instHAdd.{0} Nat instAddNat`.
    fn mk_inst_hadd_nat(&mut self) -> Result<ExprId, MetaError> {
        let f = self.const_at_level_zero(&["instHAdd"], 1)?;
        let nat = self.nat_const()?;
        let add = self.mk_inst_add_nat()?;
        self.mk_app_spine(f, &[nat, add])
    }

    /// oracle: `mkNatAdd` (`Expr.lean:2235-2253`):
    /// `@HAdd.hAdd.{0,0,0} Nat Nat Nat (instHAdd Nat instAddNat) a b`.
    fn mk_nat_add(&mut self, a: ExprId, b: ExprId) -> Result<ExprId, MetaError> {
        let f = self.const_at_level_zero(&["HAdd", "hAdd"], 3)?;
        let nat = self.nat_const()?;
        let inst = self.mk_inst_hadd_nat()?;
        self.mk_app_spine(f, &[nat, nat, nat, inst, a, b])
    }

    /// `isDefEqOffset`'s `ifNatExpr` (Offset.lean:119-125): run `x` only when
    /// the ORIGINAL left operand's type is `Nat` (checked under
    /// `withNewMCtxDepth`, so nothing is assigned), else `undef`.
    fn if_nat_expr(
        &mut self,
        s: ExprId,
        x: impl FnOnce(&mut Self) -> Result<Option<bool>, MetaError>,
    ) -> Result<Option<bool>, MetaError> {
        let ty = self.infer_type(s)?;
        let nat = self.nat_const()?;
        if self.with_new_mctx_depth(false, |ctx| ctx.is_def_eq_core(ty, nat))? {
            x(self)
        } else {
            Ok(None)
        }
    }

    /// `isDefEqOffset`'s local `isDefEq` (Offset.lean:126-127).
    fn offset_def_eq(
        &mut self,
        s0: ExprId,
        a: ExprId,
        b: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        self.if_nat_expr(s0, |ctx| Ok(Some(ctx.is_def_eq_core(a, b)?)))
    }

    /// oracle: `isDefEqOffset` (Offset.lean:118-163). Called as
    /// `isDefEqOffset t s` from `isExprDefEqExpensive` (ExprDefEq.lean:2216),
    /// so the oracle's `s` is the caller's `t`. `None` is `LBool.undef`.
    pub(crate) fn is_def_eq_offset(
        &mut self,
        s: ExprId,
        t: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        // :128-129
        if !self.cfg.offset_cnstrs {
            return Ok(None);
        }
        match self.is_offset(s)? {
            Some((s1, k1)) => match self.is_offset(t)? {
                // :134-140, `s+k₁ =?= t+k₂`
                Some((t1, k2)) => {
                    if k1 == k2 {
                        self.offset_def_eq(s, s1, t1)
                    } else if k1.0 < k2.0 {
                        let t2 = self.mk_offset(t1, &k2.sub(&k1))?;
                        self.offset_def_eq(s, s1, t2)
                    } else {
                        let s2 = self.mk_offset(s1, &k1.sub(&k2))?;
                        self.offset_def_eq(s, s2, t1)
                    }
                }
                None => match self.eval_nat(t)? {
                    // :143-147, `s+k₁ =?= v₂`
                    Some(v2) => {
                        if v2.0 >= k1.0 {
                            let lit = self.mk_nat_lit(&v2.sub(&k1))?;
                            self.offset_def_eq(s, s1, lit)
                        } else {
                            self.if_nat_expr(s, |_| Ok(Some(false)))
                        }
                    }
                    None => Ok(None),
                },
            },
            None => match self.eval_nat(s)? {
                Some(v1) => match self.is_offset(t)? {
                    // :154-158, `v₁ =?= t+k₂`
                    Some((t1, k2)) => {
                        if v1.0 >= k2.0 {
                            let lit = self.mk_nat_lit(&v1.sub(&k2))?;
                            self.offset_def_eq(s, lit, t1)
                        } else {
                            self.if_nat_expr(s, |_| Ok(Some(false)))
                        }
                    }
                    // :159-162, `v₁ =?= v₂`
                    None => match self.eval_nat(t)? {
                        Some(v2) => self.if_nat_expr(s, |_| Ok(Some(v1 == v2))),
                        None => Ok(None),
                    },
                },
                None => Ok(None),
            },
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
}

#[derive(Clone, Copy)]
enum HOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

/// Which `Structural.isInst*Nat` tester (`NatInstTesters.lean:23-64`).
#[derive(Clone, Copy)]
enum NatInstOp {
    OfNat,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    NatPow,
    Pow,
    H(HOp),
    HPow,
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use leanr_kernel::bank::{ExprId, NameId, Store};
    use leanr_kernel::{
        AxiomVal, BinderInfo, CheckedConstants, ConstSource, ConstantInfo, ConstantVal, EnvView,
        Nat,
    };

    fn name(base: &mut Store, dotted: &str) -> NameId {
        let mut n = None;
        for part in dotted.split('.') {
            let s = base.intern_str(None, part).unwrap();
            n = Some(base.name_str(None, n, s).unwrap());
        }
        n.unwrap()
    }

    fn axiom(base: &mut Store, extra: &mut HashMap<NameId, ConstantInfo>, n: &str, ty: ExprId) {
        let n = name(base, n);
        extra.insert(
            n,
            ConstantInfo::Axiom(AxiomVal {
                val: ConstantVal {
                    name: n,
                    level_params: vec![],
                    ty,
                },
                is_unsafe: false,
            }),
        );
    }

    fn cnst(base: &mut Store, n: &str) -> ExprId {
        let n = name(base, n);
        let ls = base.intern_level_list(None, &[]).unwrap();
        base.expr_const(None, Some(n), ls).unwrap()
    }

    /// oracle: `isDefEqOffset`'s `ifNatExpr` (Offset.lean:119-125) — the
    /// arithmetic verdict is returned only when the left operand's type is
    /// `Nat`; otherwise `undef`, so the rest of the ladder decides. Both
    /// sides here `evalNat` to `0` (`OfNat.ofNat _ 0 (instOfNatNat 0)`,
    /// Offset.lean:43 never looks at the type argument), so only the guard
    /// separates the `Nat` pair (`Some(true)`, :161) from the `Foo` pair
    /// (`None`). The constants are level-free axioms: `OfNat.ofNat : (α :
    /// Type) → Nat → Foo → α` is all `inferType` needs.
    #[test]
    fn if_nat_expr_guards_the_offset_verdict_on_the_operand_type() {
        let mut base = Store::persistent();
        let mut extra = HashMap::new();
        let z = base.level_zero(None).unwrap();
        let one = base.level_succ(None, z).unwrap();
        let ty = base.expr_sort(None, one).unwrap();
        let nat = cnst(&mut base, "Nat");
        let foo = cnst(&mut base, "Foo");
        axiom(&mut base, &mut extra, "Nat", ty);
        axiom(&mut base, &mut extra, "Foo", ty);
        let nat_to_foo = base
            .expr_forall(None, None, nat, foo, BinderInfo::Default)
            .unwrap();
        axiom(&mut base, &mut extra, "instOfNatNat", nat_to_foo);
        let b2 = base.expr_bvar(None, &Nat::from(2u64)).unwrap();
        let foo_to_a = base
            .expr_forall(None, None, foo, b2, BinderInfo::Default)
            .unwrap();
        let nat_foo_to_a = base
            .expr_forall(None, None, nat, foo_to_a, BinderInfo::Default)
            .unwrap();
        let of_nat_ty = base
            .expr_forall(None, None, ty, nat_foo_to_a, BinderInfo::Default)
            .unwrap();
        axiom(&mut base, &mut extra, "OfNat.ofNat", of_nat_ty);
        let of_nat = cnst(&mut base, "OfNat.ofNat");
        let inst_fn = cnst(&mut base, "instOfNatNat");
        let lit0 = base.expr_lit_nat(None, &Nat::from(0u64)).unwrap();
        let inst = base.expr_app(None, inst_fn, lit0).unwrap();
        let numeral = |base: &mut Store, at: ExprId| {
            let a = base.expr_app(None, of_nat, at).unwrap();
            let a = base.expr_app(None, a, lit0).unwrap();
            base.expr_app(None, a, inst).unwrap()
        };
        let zero_nat = numeral(&mut base, nat);
        let zero_foo = numeral(&mut base, foo);

        let empty = CheckedConstants::new(HashMap::new());
        let view = EnvView {
            consts: ConstSource::Gated(&empty),
            extra: Some(&extra),
            quot_initialized: false,
            store: &base,
        };
        let mut scratch = Store::scratch();
        let mut ctx = crate::MetaCtx::new(
            view,
            &mut scratch,
            crate::Config::default(),
            crate::EnvExtensions::default(),
        );
        assert_eq!(ctx.eval_nat(zero_foo), Ok(Some(Nat::from(0u64))));
        assert_eq!(ctx.is_def_eq_offset(zero_nat, zero_nat), Ok(Some(true)));
        assert_eq!(
            ctx.is_def_eq_offset(zero_foo, zero_foo),
            Ok(None),
            "a non-`Nat` operand must leave the offset arm undecided"
        );
        ctx.cfg.offset_cnstrs = false;
        assert_eq!(ctx.is_def_eq_offset(zero_nat, zero_nat), Ok(None));
    }

    /// oracle: `mkNatLit` (`Expr.lean:741-750`) is the `OfNat.ofNat`
    /// numeral, never the raw literal — the term `isDefEqOffset` assigns
    /// (`Nat.succ ?x =?= 2` gives `?x := 1`, row `offset/m3`).
    #[test]
    fn mk_nat_lit_is_the_ofnat_numeral() {
        crate::test_support::with_ctx(|ctx| {
            let one = ctx.mk_nat_lit(&Nat::from(1u64)).unwrap();
            let args = ctx.get_app_args(one);
            assert_eq!(args.len(), 3);
            let raw = ctx
                .scratch
                .expr_lit_nat(Some(ctx.view.store), &Nat::from(1u64))
                .unwrap();
            assert_eq!(args[1], raw);
            assert_ne!(one, raw);
        });
    }
}
