use std::fmt;
use std::mem;
use std::sync::Arc;

use crate::{Int, KernelError, Level, Name, Nat, RecGuard, Syntax};

/// Binder annotation (oracle: src/Lean/Expr.lean:71-80).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

/// Literal (oracle: src/Lean/Expr.lean:18-23).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    NatVal(Nat),
    StrVal(String),
}

/// A value in expression metadata (oracle: src/Lean/Data/KVMap.lean:18-25).
/// The Task 8 stdlib sweep found real constants carrying `ofSyntax`
/// metadata (5 of 2,433 modules), so it is represented faithfully via
/// the kernel `Syntax` family (human-approved). `Syntax`'s `Debug` is
/// non-recursive, so the derived `Debug` here stays depth-safe.
#[derive(Debug, Clone)]
pub enum DataValue {
    OfString(String),
    OfBool(bool),
    OfName(Arc<Name>),
    OfNat(Nat),
    OfInt(Int),
    OfSyntax(Arc<Syntax>),
}

/// Expression metadata map (oracle: src/Lean/Data/KVMap.lean:71-73; a
/// single-field structure, so its runtime representation is the entry
/// list itself).
#[derive(Debug, Clone, Default)]
pub struct KVMap(pub Vec<(Arc<Name>, DataValue)>);

/// Kernel expression node (oracle: src/Lean/Expr.lean:321-471), renamed
/// from the M1a `Expr` when M1b wrapped it in `Expr { data, node }`
/// (see below) to reintroduce the oracle's cached `Expr.Data` word.
/// Fields are unchanged from M1a except that every recursive child is
/// now `Arc<Expr>` instead of `Arc<ExprNode>` (children carry their own
/// cached data alongside their shape).
///
/// No derived Eq/Hash (see `Level`); `Drop` is iterative because term
/// depth is attacker-controlled. Manual iterative Debug impl (see Name
/// for pattern): depth is attacker-controlled and recursion is
/// forbidden.
pub enum ExprNode {
    BVar {
        idx: Nat,
    },
    FVar {
        id: Arc<Name>,
    },
    MVar {
        id: Arc<Name>,
    },
    Sort {
        level: Arc<Level>,
    },
    Const {
        name: Arc<Name>,
        levels: Vec<Arc<Level>>,
    },
    App {
        f: Arc<Expr>,
        arg: Arc<Expr>,
    },
    Lam {
        binder_name: Arc<Name>,
        binder_type: Arc<Expr>,
        body: Arc<Expr>,
        binder_info: BinderInfo,
    },
    ForallE {
        binder_name: Arc<Name>,
        binder_type: Arc<Expr>,
        body: Arc<Expr>,
        binder_info: BinderInfo,
    },
    LetE {
        decl_name: Arc<Name>,
        ty: Arc<Expr>,
        value: Arc<Expr>,
        body: Arc<Expr>,
        non_dep: bool,
    },
    Lit(Literal),
    MData {
        data: KVMap,
        expr: Arc<Expr>,
    },
    Proj {
        type_name: Arc<Name>,
        idx: Nat,
        structure: Arc<Expr>,
    },
}

/// Manual (non-derived) impl: iterative formatting instead of recursing
/// into Arc children, so it stays safe on adversarially deep chains.
/// Renders as `ExprNode::BVar { .. }`, etc.
impl fmt::Debug for ExprNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExprNode::BVar { idx } => write!(f, "ExprNode::BVar {{ idx: {:?} }}", idx),
            ExprNode::FVar { id } => write!(f, "ExprNode::FVar {{ id: {:?} }}", id),
            ExprNode::MVar { id } => write!(f, "ExprNode::MVar {{ id: {:?} }}", id),
            ExprNode::Sort { level: _ } => f.write_str("ExprNode::Sort { level: .. }"),
            ExprNode::Const { name, levels: _ } => {
                write!(f, "ExprNode::Const {{ name: {:?}, levels: .. }}", name)
            }
            ExprNode::App { f: _, arg: _ } => f.write_str("ExprNode::App { f: .., arg: .. }"),
            ExprNode::Lam {
                binder_name,
                binder_type: _,
                body: _,
                binder_info,
            } => {
                write!(f, "ExprNode::Lam {{ binder_name: {:?}, binder_type: .., body: .., binder_info: {:?} }}", binder_name, binder_info)
            }
            ExprNode::ForallE {
                binder_name,
                binder_type: _,
                body: _,
                binder_info,
            } => {
                write!(f, "ExprNode::ForallE {{ binder_name: {:?}, binder_type: .., body: .., binder_info: {:?} }}", binder_name, binder_info)
            }
            ExprNode::LetE {
                decl_name,
                ty: _,
                value: _,
                body: _,
                non_dep,
            } => {
                write!(
                    f,
                    "ExprNode::LetE {{ decl_name: {:?}, ty: .., value: .., body: .., non_dep: {} }}",
                    decl_name, non_dep
                )
            }
            ExprNode::Lit(lit) => write!(f, "ExprNode::Lit({:?})", lit),
            ExprNode::MData { data: _, expr: _ } => {
                f.write_str("ExprNode::MData { data: .., expr: .. }")
            }
            ExprNode::Proj {
                type_name,
                idx,
                structure: _,
            } => {
                write!(
                    f,
                    "ExprNode::Proj {{ type_name: {:?}, idx: {:?}, structure: .. }}",
                    type_name, idx
                )
            }
        }
    }
}

// ---------------------------------------------------------------------
// M1b Task 3: `Expr.Data` (oracle: src/Lean/Expr.lean:118-182) — a
// packed u64 of hash/depth/flags/loose-bvar-range cached on every node,
// recomputed at construction from already-cached child data (O(1) per
// smart constructor call; only `sort`/`const_` walk into `Level` and so
// need a `RecGuard`, per the task brief).
// ---------------------------------------------------------------------

// Bit layout, exactly Lean/Expr.lean:118-127 (and the C++ mirror
// `lean_expr_mk_data`, kernel/expr.cpp:105-113):
//   bits 0..32   hash
//   bits 32..40  approxDepth
//   bit  40      hasFVar
//   bit  41      hasExprMVar
//   bit  42      hasLevelMVar
//   bit  43      hasLevelParam
//   bits 44..64  looseBVarRange
const LOOSE_BVAR_SAT: u32 = (1 << 20) - 1;
// `approxDepth` is packed as a `u8`, which already saturates at 255 on
// `saturating_add` — no separate `DEPTH_SAT` constant is needed (unlike
// `LOOSE_BVAR_SAT`, whose cap is narrower than its backing `u32`).

const HASH_SHIFT: u32 = 0;
const DEPTH_SHIFT: u32 = 32;
const HAS_FVAR_BIT: u32 = 40;
const HAS_EXPR_MVAR_BIT: u32 = 41;
const HAS_LEVEL_MVAR_BIT: u32 = 42;
const HAS_LEVEL_PARAM_BIT: u32 = 43;
const RANGE_SHIFT: u32 = 44;

/// Packed per-node metadata (oracle: `Expr.Data`, Lean/Expr.lean:118-127).
/// We do NOT promise oracle-identical hash *values* (its mixer lives in
/// the closed-source runtime); the task brief's only requirement is
/// `structural_eq ⇒ equal hashes`, which holds because every field here
/// is a pure, deterministic function of the (already-computed) child
/// `ExprData` words.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExprData(u64);

impl ExprData {
    fn pack(
        hash64: u64,
        loose_bvar_range: u32,
        approx_depth: u8,
        has_fvar: bool,
        has_expr_mvar: bool,
        has_level_mvar: bool,
        has_level_param: bool,
    ) -> ExprData {
        let range = loose_bvar_range.min(LOOSE_BVAR_SAT);
        let hash32 = (hash64 & 0xFFFF_FFFF) as u32;
        let mut word: u64 = (hash32 as u64) << HASH_SHIFT;
        word |= (approx_depth as u64) << DEPTH_SHIFT;
        if has_fvar {
            word |= 1 << HAS_FVAR_BIT;
        }
        if has_expr_mvar {
            word |= 1 << HAS_EXPR_MVAR_BIT;
        }
        if has_level_mvar {
            word |= 1 << HAS_LEVEL_MVAR_BIT;
        }
        if has_level_param {
            word |= 1 << HAS_LEVEL_PARAM_BIT;
        }
        word |= (range as u64) << RANGE_SHIFT;
        ExprData(word)
    }

    pub fn hash(self) -> u32 {
        (self.0 >> HASH_SHIFT) as u32
    }

    pub fn approx_depth(self) -> u8 {
        ((self.0 >> DEPTH_SHIFT) & 0xFF) as u8
    }

    pub fn loose_bvar_range(self) -> u32 {
        (self.0 >> RANGE_SHIFT) as u32
    }

    /// The exact loose-bvar range when the packed word proves it, or
    /// `None` when the packed value is the saturation sentinel
    /// (`LOOSE_BVAR_SAT`). `bvar_loose_range`/`close_one` above pack
    /// `min(actual, LOOSE_BVAR_SAT)`, so an *exact* (non-saturated)
    /// value is a real bound — but once a subtree saturates, `close_one`
    /// keeps it stuck at the cap even as enclosing binders close over
    /// it, so the saturated value no longer bounds the actual range from
    /// either side (M1b Task 4's `subst.rs` port found this: a
    /// substitution's "closed enough, skip this subtree" optimization
    /// must never trust a `<=` comparison against a saturated word,
    /// since the true range could by then be either far larger or far
    /// smaller). Callers doing that optimization must treat `None` as
    /// "must walk the real (bignum) indices to know."
    pub(crate) fn loose_bvar_range_exact(self) -> Option<u32> {
        let r = self.loose_bvar_range();
        if r < LOOSE_BVAR_SAT {
            Some(r)
        } else {
            None
        }
    }

    pub fn has_fvar(self) -> bool {
        (self.0 >> HAS_FVAR_BIT) & 1 == 1
    }

    pub fn has_expr_mvar(self) -> bool {
        (self.0 >> HAS_EXPR_MVAR_BIT) & 1 == 1
    }

    pub fn has_level_mvar(self) -> bool {
        (self.0 >> HAS_LEVEL_MVAR_BIT) & 1 == 1
    }

    pub fn has_level_param(self) -> bool {
        (self.0 >> HAS_LEVEL_PARAM_BIT) & 1 == 1
    }
}

/// `Expr`, wrapping the M1a enum (now `ExprNode`) with the packed
/// metadata word above. Built ONLY through the smart constructors below
/// so `data` is always in sync with `node` (private fields enforce
/// this from outside the module).
pub struct Expr {
    data: ExprData,
    node: ExprNode,
}

/// Delegates to `ExprNode`'s manual (non-recursive) `Debug`, plus the
/// packed word; stays depth-safe for the same reason `ExprNode`'s does.
impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Expr {{ data: {:?}, node: {:?} }}", self.data, self.node)
    }
}

impl Drop for Expr {
    fn drop(&mut self) {
        let mut stack: Vec<Arc<Expr>> = Vec::new();
        take_expr_children(&mut self.node, &mut stack);
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                take_expr_children(&mut owned.node, &mut stack);
            }
        }
    }
}

/// Detach `Arc<Expr>` children into `stack`, leaving a cheap leaf
/// behind so the node's own drop is O(1). Reaches through `ExprNode`
/// (the brief's Step 3.1) since children now live one level deeper than
/// the M1a enum.
fn take_expr_children(e: &mut ExprNode, stack: &mut Vec<Arc<Expr>>) {
    let leaf = || Expr::bvar(Nat::from(0u64));
    match e {
        ExprNode::BVar { .. }
        | ExprNode::FVar { .. }
        | ExprNode::MVar { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Const { .. }
        | ExprNode::Lit(_) => {}
        ExprNode::App { f, arg } => {
            stack.push(mem::replace(f, leaf()));
            stack.push(mem::replace(arg, leaf()));
        }
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => {
            stack.push(mem::replace(binder_type, leaf()));
            stack.push(mem::replace(body, leaf()));
        }
        ExprNode::LetE {
            ty, value, body, ..
        } => {
            stack.push(mem::replace(ty, leaf()));
            stack.push(mem::replace(value, leaf()));
            stack.push(mem::replace(body, leaf()));
        }
        ExprNode::MData { expr, .. }
        | ExprNode::Proj {
            structure: expr, ..
        } => {
            stack.push(mem::replace(expr, leaf()));
        }
    }
}

// ---------------------------------------------------------------------
// Hashing helpers. `mix` is our own avalanche finalizer (murmur3-style):
// the oracle's per-constructor combination *structure* (which fields
// get folded together) is cited from Lean/Expr.lean:471-513 at each use
// site below, but its actual bit-mixing constants live in the
// closed-source C++ runtime (`lean_expr_mk_data`/`lean_expr_mk_app_data`,
// kernel/expr.cpp:105-127) and are not required to match (task brief:
// "we do NOT promise oracle-identical hash values"; only
// `structural_eq ⇒ equal hashes` is required, which holds here because
// every hash below is a pure function of already-computed child data).
pub(crate) fn mix(a: u64, b: u64) -> u64 {
    let mut h = a ^ b.wrapping_mul(0x9E37_79B9_7F4A_7C15);
    h ^= h >> 33;
    h = h.wrapping_mul(0xFF51_AFD7_ED55_8CCD);
    h ^= h >> 33;
    h = h.wrapping_mul(0xC4CE_B9FE_1A85_EC53);
    h ^= h >> 33;
    h
}

// Per-constructor tags, taken from the oracle's own literal constants
// at Lean/Expr.lean:473-513 (`const`=5, `bvar`=7, `sort`=11, `fvar`=13,
// `mvar`=17, `lit`=3) so at least the *tag* half of each leaf mix
// matches the oracle, even though the mixer itself (`mix` above) does
// not reproduce the oracle's own bit-mixing constants (see `mix`'s doc
// comment above).
const TAG_CONST: u64 = 5;
const TAG_BVAR: u64 = 7;
const TAG_SORT: u64 = 11;
const TAG_FVAR: u64 = 13;
const TAG_MVAR: u64 = 17;
const TAG_LIT: u64 = 3;

fn name_hash(n: &Arc<Name>) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut h = DefaultHasher::new();
    n.hash(&mut h);
    h.finish()
}

fn literal_hash(l: &Literal) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut h = DefaultHasher::new();
    l.hash(&mut h);
    h.finish()
}

/// `idx` (and `Proj`'s field index) are bignum `Nat`s decoded straight
/// from untrusted `.olean` bytes, so an attacker can hand us an
/// arbitrarily large one; hashing it losslessly would be O(its bit
/// length) per construction. The task brief calls for exactly this
/// lossy truncation for `bvar`'s hash; we reuse it for `Proj`'s index
/// for the same reason (both are attacker-sized `Nat`s feeding a hash
/// that must stay O(1)).
fn nat_lossy_u64(n: &Nat) -> u64 {
    n.0.to_u64_digits().first().copied().unwrap_or(0)
}

/// `idx + 1`, saturating at `LOOSE_BVAR_SAT` (oracle: bvar's
/// `looseBVarRange`, Lean/Expr.lean:474, is `idx + 1` with no upper
/// bound in the Lean source itself — the saturation is the C++
/// runtime's `lean_expr_mk_data` panicking past `1048575`,
/// kernel/expr.cpp:108; we saturate instead of panicking, per the
/// crate's no-panic-on-untrusted-input discipline). Any range at or
/// beyond the cap means "treat as open, skip no optimizations" (task
/// brief), so once saturated it is a sticky ceiling, not a precise
/// count.
fn bvar_loose_range(idx: &Nat) -> u32 {
    let digits = idx.0.to_u64_digits();
    if digits.len() > 1 {
        return LOOSE_BVAR_SAT;
    }
    let v = digits.first().copied().unwrap_or(0u64);
    match v.checked_add(1) {
        Some(inc) if inc < LOOSE_BVAR_SAT as u64 => inc as u32,
        _ => LOOSE_BVAR_SAT,
    }
}

/// A binder closes one bvar level (task brief): `range - 1`, floored at
/// 0, EXCEPT a saturated range (already "treat as open") never
/// subtracts — it stays saturated, since it no longer represents an
/// exact count.
fn close_one(range: u32) -> u32 {
    if range >= LOOSE_BVAR_SAT {
        LOOSE_BVAR_SAT
    } else {
        range.saturating_sub(1)
    }
}

fn depth_of(children_max: u8) -> u8 {
    children_max.saturating_add(1)
}

/// oracle: Lean/Expr.lean:485 (`.app f a => mkAppData f.data a.data`)
/// combined with the C++ mirror `lean_expr_mk_app_data`
/// (kernel/expr.cpp:116-122): depth and loose-bvar-range both take the
/// max of the two children (an application binds nothing, so neither
/// child's range is decremented).
fn combine_app(fd: ExprData, ad: ExprData) -> ExprData {
    let depth = depth_of(fd.approx_depth().max(ad.approx_depth()));
    let range = fd.loose_bvar_range().max(ad.loose_bvar_range());
    let h = mix(depth as u64, mix(fd.hash() as u64, ad.hash() as u64));
    ExprData::pack(
        h,
        range,
        depth,
        fd.has_fvar() || ad.has_fvar(),
        fd.has_expr_mvar() || ad.has_expr_mvar(),
        fd.has_level_mvar() || ad.has_level_mvar(),
        fd.has_level_param() || ad.has_level_param(),
    )
}

/// oracle: Lean/Expr.lean:486-503 (`.lam`/`.forallE`) — flags/depth are
/// the max over both children; `looseBVarRange` takes the type's range
/// directly (the domain type lives in the *outer* scope, same as the
/// binder node itself) and the body's range *minus one* (the body lives
/// one binder deeper, so closing this binder removes exactly one level
/// of escaping reference) — asymmetric on purpose, matching
/// `max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1)`
/// literally.
fn combine_binder(td: ExprData, bd: ExprData) -> ExprData {
    let depth = depth_of(td.approx_depth().max(bd.approx_depth()));
    let range = td.loose_bvar_range().max(close_one(bd.loose_bvar_range()));
    let h = mix(depth as u64, mix(td.hash() as u64, bd.hash() as u64));
    ExprData::pack(
        h,
        range,
        depth,
        td.has_fvar() || bd.has_fvar(),
        td.has_expr_mvar() || bd.has_expr_mvar(),
        td.has_level_mvar() || bd.has_level_mvar(),
        td.has_level_param() || bd.has_level_param(),
    )
}

/// oracle: Lean/Expr.lean:504-512 (`.letE`) — same asymmetry as
/// `combine_binder`, with a third (`value`) child that, like `ty`,
/// lives in the outer scope and so is not decremented.
fn combine_let(td: ExprData, vd: ExprData, bd: ExprData) -> ExprData {
    let depth = depth_of(
        td.approx_depth()
            .max(vd.approx_depth())
            .max(bd.approx_depth()),
    );
    let range = td
        .loose_bvar_range()
        .max(vd.loose_bvar_range())
        .max(close_one(bd.loose_bvar_range()));
    let h = mix(
        depth as u64,
        mix(td.hash() as u64, mix(vd.hash() as u64, bd.hash() as u64)),
    );
    ExprData::pack(
        h,
        range,
        depth,
        td.has_fvar() || vd.has_fvar() || bd.has_fvar(),
        td.has_expr_mvar() || vd.has_expr_mvar() || bd.has_expr_mvar(),
        td.has_level_mvar() || vd.has_level_mvar() || bd.has_level_mvar(),
        td.has_level_param() || vd.has_level_param() || bd.has_level_param(),
    )
}

impl Expr {
    // -- Smart constructors --------------------------------------------
    // The ONLY way to build an `Expr` outside this module. Each computes
    // `ExprData` in O(1) from already-cached child data (except
    // `sort`/`const_`, which walk attacker-depth `Level`s and so need a
    // `RecGuard` and can report `KernelError::DeepRecursion`).

    /// oracle: Lean/Expr.lean:474 (`.bvar idx => mkData (mixHash 7 <|
    /// hash idx) (idx+1)`).
    pub fn bvar(idx: Nat) -> Arc<Expr> {
        let range = bvar_loose_range(&idx);
        let h = mix(TAG_BVAR, nat_lossy_u64(&idx));
        let data = ExprData::pack(h, range, 1, false, false, false, false);
        Arc::new(Expr {
            data,
            node: ExprNode::BVar { idx },
        })
    }

    /// oracle: Lean/Expr.lean:476 (`.fvar fvarId => mkData (mixHash 13
    /// <| hash fvarId) 0 0 true`).
    pub fn fvar(id: Arc<Name>) -> Arc<Expr> {
        let h = mix(TAG_FVAR, name_hash(&id));
        let data = ExprData::pack(h, 0, 1, true, false, false, false);
        Arc::new(Expr {
            data,
            node: ExprNode::FVar { id },
        })
    }

    /// oracle: Lean/Expr.lean:477 (`.mvar fvarId => mkData (mixHash 17
    /// <| hash fvarId) 0 0 false true`).
    pub fn mvar(id: Arc<Name>) -> Arc<Expr> {
        let h = mix(TAG_MVAR, name_hash(&id));
        let data = ExprData::pack(h, 0, 1, false, true, false, false);
        Arc::new(Expr {
            data,
            node: ExprNode::MVar { id },
        })
    }

    /// oracle: Lean/Expr.lean:475 (`.sort lvl => mkData (mixHash 11 <|
    /// hash lvl) 0 0 false false lvl.hasMVar lvl.hasParam`). Fallible:
    /// `Level::has_mvar`/`has_param`/`hash_val` walk attacker-depth
    /// `Level`s under a `RecGuard`.
    pub fn sort(level: Arc<Level>, g: &mut RecGuard) -> Result<Arc<Expr>, KernelError> {
        let has_mvar = Level::has_mvar(&level, g)?;
        let has_param = Level::has_param(&level, g)?;
        let lh = Level::hash_val(&level, g)?;
        let h = mix(TAG_SORT, lh);
        let data = ExprData::pack(h, 0, 1, false, false, has_mvar, has_param);
        Ok(Arc::new(Expr {
            data,
            node: ExprNode::Sort { level },
        }))
    }

    /// oracle: Lean/Expr.lean:473 (`.const n lvls => mkData (mixHash 5
    /// <| mixHash (hash n) (hash lvls)) 0 0 false false (lvls.any
    /// Level.hasMVar) (lvls.any Level.hasParam)`). Fallible for the same
    /// reason as `sort`.
    pub fn const_(
        name: Arc<Name>,
        levels: Vec<Arc<Level>>,
        g: &mut RecGuard,
    ) -> Result<Arc<Expr>, KernelError> {
        let mut has_mvar = false;
        let mut has_param = false;
        let mut levels_hash: u64 = 0;
        for l in &levels {
            has_mvar |= Level::has_mvar(l, g)?;
            has_param |= Level::has_param(l, g)?;
            levels_hash = mix(levels_hash, Level::hash_val(l, g)?);
        }
        let h = mix(TAG_CONST, mix(name_hash(&name), levels_hash));
        let data = ExprData::pack(h, 0, 1, false, false, has_mvar, has_param);
        Ok(Arc::new(Expr {
            data,
            node: ExprNode::Const { name, levels },
        }))
    }

    /// oracle: Lean/Expr.lean:485 / kernel/expr.cpp:116-122.
    pub fn app(f: Arc<Expr>, arg: Arc<Expr>) -> Arc<Expr> {
        let data = combine_app(f.data, arg.data);
        Arc::new(Expr {
            data,
            node: ExprNode::App { f, arg },
        })
    }

    /// oracle: Lean/Expr.lean:486-494.
    pub fn lam(
        binder_name: Arc<Name>,
        binder_type: Arc<Expr>,
        body: Arc<Expr>,
        binder_info: BinderInfo,
    ) -> Arc<Expr> {
        let data = combine_binder(binder_type.data, body.data);
        Arc::new(Expr {
            data,
            node: ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            },
        })
    }

    /// oracle: Lean/Expr.lean:495-503.
    pub fn forall_e(
        binder_name: Arc<Name>,
        binder_type: Arc<Expr>,
        body: Arc<Expr>,
        binder_info: BinderInfo,
    ) -> Arc<Expr> {
        let data = combine_binder(binder_type.data, body.data);
        Arc::new(Expr {
            data,
            node: ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            },
        })
    }

    /// oracle: Lean/Expr.lean:504-512.
    pub fn let_e(
        decl_name: Arc<Name>,
        ty: Arc<Expr>,
        value: Arc<Expr>,
        body: Arc<Expr>,
        non_dep: bool,
    ) -> Arc<Expr> {
        let data = combine_let(ty.data, value.data, body.data);
        Arc::new(Expr {
            data,
            node: ExprNode::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            },
        })
    }

    /// oracle: Lean/Expr.lean:513 (`.lit l => mkData (mixHash 3 (hash
    /// l))`).
    pub fn lit(l: Literal) -> Arc<Expr> {
        let h = mix(TAG_LIT, literal_hash(&l));
        let data = ExprData::pack(h, 0, 1, false, false, false, false);
        Arc::new(Expr {
            data,
            node: ExprNode::Lit(l),
        })
    }

    /// oracle: Lean/Expr.lean:478-480 (`.mdata _m e => ...`): depth
    /// bumps by one, flags/range pass through from the single child.
    pub fn mdata(data: KVMap, expr: Arc<Expr>) -> Arc<Expr> {
        let cd = expr.data;
        let depth = depth_of(cd.approx_depth());
        let h = mix(depth as u64, cd.hash() as u64);
        let out = ExprData::pack(
            h,
            cd.loose_bvar_range(),
            depth,
            cd.has_fvar(),
            cd.has_expr_mvar(),
            cd.has_level_mvar(),
            cd.has_level_param(),
        );
        Arc::new(Expr {
            data: out,
            node: ExprNode::MData { data, expr },
        })
    }

    /// oracle: Lean/Expr.lean:481-484 (`.proj s i e => ...`): same shape
    /// as `mdata` plus the type name/index folded into the hash.
    pub fn proj(type_name: Arc<Name>, idx: Nat, structure: Arc<Expr>) -> Arc<Expr> {
        let cd = structure.data;
        let depth = depth_of(cd.approx_depth());
        let nh = name_hash(&type_name);
        let ih = nat_lossy_u64(&idx);
        let h = mix(depth as u64, mix(nh, mix(ih, cd.hash() as u64)));
        let out = ExprData::pack(
            h,
            cd.loose_bvar_range(),
            depth,
            cd.has_fvar(),
            cd.has_expr_mvar(),
            cd.has_level_mvar(),
            cd.has_level_param(),
        );
        Arc::new(Expr {
            data: out,
            node: ExprNode::Proj {
                type_name,
                idx,
                structure,
            },
        })
    }

    // -- Accessors -------------------------------------------------------

    pub fn node(&self) -> &ExprNode {
        &self.node
    }

    pub fn data(&self) -> ExprData {
        self.data
    }

    /// oracle: `Expr.equal`/kernel `expr_eq_fn` — ptr fast path, then
    /// the cached data word (covers hash + all flags + loose-bvar-range
    /// in one compare), then a guarded structural descent. `MData` is
    /// compared structurally (including its `KVMap`, per
    /// `DataValue::OfSyntax`'s documented ptr-eq rule below) because the
    /// oracle's own equality does not skip metadata.
    ///
    /// This is `expr_eq_fn<true>` (`is_bi_equal`, kernel/expr_eq_fn.cpp:
    /// 141) — binder names AND `BinderInfo` are compared. See
    /// `alpha_eq` below for the `expr_eq_fn<false>` (`is_equal`) variant
    /// used by `operator!=`.
    pub fn structural_eq(
        a: &Arc<Expr>,
        b: &Arc<Expr>,
        g: &mut RecGuard,
    ) -> Result<bool, KernelError> {
        Self::eq_impl(a, b, g, true)
    }

    /// oracle: `expr_eq_fn<false>` (kernel/expr_eq_fn.cpp:22-131),
    /// exposed as `is_equal`/`operator!=` (expr_eq_fn.cpp:140-142,
    /// `bool operator!=(expr const & a, expr const & b) { return
    /// !is_equal(a, b); }` in kernel/expr.h). Identical to
    /// `structural_eq` except binder names and `BinderInfo` are ignored
    /// for `Lam`/`ForallE` (expr_eq_fn.cpp:113-119: `(!CompareBinderInfo
    /// || binding_name(a) == binding_name(b)) && (!CompareBinderInfo ||
    /// binding_info(a) == binding_info(b))`) and the declaration name is
    /// ignored for `LetE` (expr_eq_fn.cpp:126-129, same
    /// `!CompareBinderInfo ||` guard on `let_name`).
    ///
    /// Sharing `structural_eq`'s data-word fast-reject (below) is sound:
    /// `ExprData`'s packed hash/depth/flags/loose-bvar-range are built by
    /// `combine_binder`/`combine_app`/`combine_let` (above) purely from
    /// the *children's* already-computed `ExprData` words — binder names
    /// and `BinderInfo` are never folded into the packed word at the
    /// binder's own node (verified by reading every `ExprData::pack`
    /// call site above before writing this fn: none takes a name or
    /// `BinderInfo` as input). So two trees that are alpha-equal (equal
    /// up to binder name/info) always carry equal packed data words,
    /// exactly as the oracle's own `hash(a) != hash(b)` fast-reject
    /// relies on `Expr::hash` excluding binder names/info
    /// (Lean/Expr.lean:486-503's `mkDataForBinder`/`mkDataForLet` fold
    /// only the child hashes, never the name).
    pub fn alpha_eq(a: &Arc<Expr>, b: &Arc<Expr>, g: &mut RecGuard) -> Result<bool, KernelError> {
        Self::eq_impl(a, b, g, false)
    }

    fn eq_impl(
        a: &Arc<Expr>,
        b: &Arc<Expr>,
        g: &mut RecGuard,
        compare_binders: bool,
    ) -> Result<bool, KernelError> {
        if Arc::ptr_eq(a, b) {
            return Ok(true);
        }
        if a.data != b.data {
            return Ok(false);
        }
        match (&a.node, &b.node) {
            (ExprNode::BVar { idx: ia }, ExprNode::BVar { idx: ib }) => Ok(ia == ib),
            (ExprNode::FVar { id: ia }, ExprNode::FVar { id: ib }) => Ok(ia == ib),
            (ExprNode::MVar { id: ia }, ExprNode::MVar { id: ib }) => Ok(ia == ib),
            (ExprNode::Sort { level: la }, ExprNode::Sort { level: lb }) => {
                Level::structural_eq(la, lb, g)
            }
            (
                ExprNode::Const {
                    name: na,
                    levels: lsa,
                },
                ExprNode::Const {
                    name: nb,
                    levels: lsb,
                },
            ) => {
                if na != nb || lsa.len() != lsb.len() {
                    return Ok(false);
                }
                for (x, y) in lsa.iter().zip(lsb.iter()) {
                    if !Level::structural_eq(x, y, g)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (ExprNode::App { f: fa, arg: aa }, ExprNode::App { f: fb, arg: ab }) => {
                let (fa, aa, fb, ab) = (
                    Arc::clone(fa),
                    Arc::clone(aa),
                    Arc::clone(fb),
                    Arc::clone(ab),
                );
                g.enter(|g| {
                    Ok(Expr::eq_impl(&fa, &fb, g, compare_binders)?
                        && Expr::eq_impl(&aa, &ab, g, compare_binders)?)
                })
            }
            (
                ExprNode::Lam {
                    binder_name: na,
                    binder_type: ta,
                    body: ba,
                    binder_info: ia,
                },
                ExprNode::Lam {
                    binder_name: nb,
                    binder_type: tb,
                    body: bb,
                    binder_info: ib,
                },
            )
            | (
                ExprNode::ForallE {
                    binder_name: na,
                    binder_type: ta,
                    body: ba,
                    binder_info: ia,
                },
                ExprNode::ForallE {
                    binder_name: nb,
                    binder_type: tb,
                    body: bb,
                    binder_info: ib,
                },
            ) => {
                // expr_eq_fn.cpp:113-119: binder name/info are only
                // compared under `CompareBinderInfo` (i.e. `structural_eq`,
                // `compare_binders == true`); `alpha_eq` skips both.
                if compare_binders && (na != nb || ia != ib) {
                    return Ok(false);
                }
                let (ta, ba, tb, bb) = (
                    Arc::clone(ta),
                    Arc::clone(ba),
                    Arc::clone(tb),
                    Arc::clone(bb),
                );
                g.enter(|g| {
                    Ok(Expr::eq_impl(&ta, &tb, g, compare_binders)?
                        && Expr::eq_impl(&ba, &bb, g, compare_binders)?)
                })
            }
            (
                ExprNode::LetE {
                    decl_name: na,
                    ty: ta,
                    value: va,
                    body: ba,
                    non_dep: da,
                },
                ExprNode::LetE {
                    decl_name: nb,
                    ty: tb,
                    value: vb,
                    body: bb,
                    non_dep: db,
                },
            ) => {
                // expr_eq_fn.cpp:126-129: `let_name` is likewise only
                // compared under `CompareBinderInfo`; `non_dep`
                // (`let_nondep`) is always compared.
                if da != db || (compare_binders && na != nb) {
                    return Ok(false);
                }
                let (ta, va, ba, tb, vb, bb) = (
                    Arc::clone(ta),
                    Arc::clone(va),
                    Arc::clone(ba),
                    Arc::clone(tb),
                    Arc::clone(vb),
                    Arc::clone(bb),
                );
                g.enter(|g| {
                    Ok(Expr::eq_impl(&ta, &tb, g, compare_binders)?
                        && Expr::eq_impl(&va, &vb, g, compare_binders)?
                        && Expr::eq_impl(&ba, &bb, g, compare_binders)?)
                })
            }
            (ExprNode::Lit(la), ExprNode::Lit(lb)) => Ok(la == lb),
            (ExprNode::MData { data: da, expr: ea }, ExprNode::MData { data: db, expr: eb }) => {
                if !kvmap_eq(da, db) {
                    return Ok(false);
                }
                let (ea, eb) = (Arc::clone(ea), Arc::clone(eb));
                g.enter(|g| Expr::eq_impl(&ea, &eb, g, compare_binders))
            }
            (
                ExprNode::Proj {
                    type_name: na,
                    idx: ia,
                    structure: sa,
                },
                ExprNode::Proj {
                    type_name: nb,
                    idx: ib,
                    structure: sb,
                },
            ) => {
                // Proj has no binder; `type_name`/`idx` are always
                // compared regardless of `compare_binders`.
                if na != nb || ia != ib {
                    return Ok(false);
                }
                let (sa, sb) = (Arc::clone(sa), Arc::clone(sb));
                g.enter(|g| Expr::eq_impl(&sa, &sb, g, compare_binders))
            }
            _ => Ok(false),
        }
    }

    // -- App spine helpers (iterative; used constantly from Task 6 on) --

    pub fn get_app_fn(e: &Arc<Expr>) -> &Arc<Expr> {
        let mut cur = e;
        while let ExprNode::App { f, .. } = &cur.node {
            cur = f;
        }
        cur
    }

    pub fn get_app_args(e: &Arc<Expr>) -> Vec<Arc<Expr>> {
        let mut args = Vec::new();
        let mut cur = e;
        while let ExprNode::App { f, arg } = &cur.node {
            args.push(Arc::clone(arg));
            cur = f;
        }
        args.reverse();
        args
    }

    pub fn get_app_num_args(e: &Arc<Expr>) -> usize {
        let mut n = 0usize;
        let mut cur = e;
        while let ExprNode::App { f, .. } = &cur.node {
            n += 1;
            cur = f;
        }
        n
    }

    pub fn mk_app_spine(f: Arc<Expr>, args: &[Arc<Expr>]) -> Arc<Expr> {
        let mut r = f;
        for a in args {
            r = Expr::app(r, Arc::clone(a));
        }
        r
    }

    pub fn is_bvar(&self) -> bool {
        matches!(self.node, ExprNode::BVar { .. })
    }

    pub fn is_fvar(&self) -> bool {
        matches!(self.node, ExprNode::FVar { .. })
    }

    pub fn is_mvar(&self) -> bool {
        matches!(self.node, ExprNode::MVar { .. })
    }

    pub fn is_sort(&self) -> bool {
        matches!(self.node, ExprNode::Sort { .. })
    }

    pub fn is_const(&self) -> bool {
        matches!(self.node, ExprNode::Const { .. })
    }

    pub fn is_app(&self) -> bool {
        matches!(self.node, ExprNode::App { .. })
    }

    pub fn is_lambda(&self) -> bool {
        matches!(self.node, ExprNode::Lam { .. })
    }

    pub fn is_forall(&self) -> bool {
        matches!(self.node, ExprNode::ForallE { .. })
    }

    pub fn is_let(&self) -> bool {
        matches!(self.node, ExprNode::LetE { .. })
    }

    pub fn is_proj(&self) -> bool {
        matches!(self.node, ExprNode::Proj { .. })
    }

    pub fn is_lit(&self) -> bool {
        matches!(self.node, ExprNode::Lit(_))
    }

    pub fn is_mdata(&self) -> bool {
        matches!(self.node, ExprNode::MData { .. })
    }

    pub fn const_name(&self) -> Option<&Arc<Name>> {
        match &self.node {
            ExprNode::Const { name, .. } => Some(name),
            _ => None,
        }
    }
}

/// `KVMap` equality: same length, same entries in order (the decoder
/// builds these deterministically from the file's own entry order, so
/// order-sensitive comparison is exact for our one producer).
pub(crate) fn kvmap_eq(a: &KVMap, b: &KVMap) -> bool {
    a.0.len() == b.0.len()
        && a.0
            .iter()
            .zip(b.0.iter())
            .all(|((na, va), (nb, vb))| na == nb && data_value_eq(va, vb))
}

/// oracle: `expr_eq_fn` on `MData` walks the full `KVMap`, including
/// `DataValue::OfSyntax` payloads — but the kernel checker never
/// inspects `Syntax` (it is elaborator/pretty-printer plumbing, e.g.
/// `mkPatternWithRef`, Expr.lean:2136-2140), and the decoder's
/// per-offset memo (leanr_olean's `Interp`) means two `Arc<Syntax>`
/// built from the same file's object DAG are pointer-equal exactly when
/// they are structurally equal. So `Arc::ptr_eq` is exact for the one
/// producer of `Expr` values in this codebase, and is what we use here
/// (human-approved rationale, per the task brief).
pub(crate) fn data_value_eq(a: &DataValue, b: &DataValue) -> bool {
    match (a, b) {
        (DataValue::OfString(x), DataValue::OfString(y)) => x == y,
        (DataValue::OfBool(x), DataValue::OfBool(y)) => x == y,
        (DataValue::OfName(x), DataValue::OfName(y)) => x == y,
        (DataValue::OfNat(x), DataValue::OfNat(y)) => x == y,
        (DataValue::OfInt(x), DataValue::OfInt(y)) => x == y,
        (DataValue::OfSyntax(x), DataValue::OfSyntax(y)) => Arc::ptr_eq(x, y),
        _ => false,
    }
}

#[cfg(test)]
mod m1b_tests {
    use super::*;
    use crate::{Level, Name, Nat, RecGuard};
    use std::sync::Arc;

    // `Name::from_str` doesn't exist (see name.rs): `Name` has no
    // constructor helpers, just the plain enum variants, which are
    // public. Build a single-component name with an `Anonymous` parent
    // by hand instead (same adjustment Task 2's own tests made).
    fn nm(s: &str) -> Arc<Name> {
        Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: s.to_string(),
        })
    }

    #[test]
    fn loose_bvar_range_tracks_binders() {
        let b0 = Expr::bvar(Nat::from(0u64));
        let b3 = Expr::bvar(Nat::from(3u64));
        assert_eq!(b0.data().loose_bvar_range(), 1);
        assert_eq!(b3.data().loose_bvar_range(), 4);
        // NOTE: the brief's own draft reused `Expr::bvar(0)` as the
        // binder *type* here, which (per the oracle formula cited on
        // `combine_binder` above: type range counts directly, only the
        // body is closed by the binder) would make the whole lambda
        // still carry a loose reference from its domain type — the
        // draft's "is closed" comment describes the *body*, not a
        // genuinely closed type, and its own asserted value (0) only
        // holds when the domain type is actually closed. Using a closed
        // leaf (`fvar`) for the type here fixes that inconsistency
        // without changing `loose_bvar_range`'s semantics.
        let lam = Expr::lam(
            nm("x"),
            Expr::fvar(nm("T")),
            Arc::clone(&b0),
            BinderInfo::Default,
        );
        // λ (x : T), #0 is closed: the body's #0 is x itself.
        assert_eq!(lam.data().loose_bvar_range(), 0);
        let lam_open = Expr::lam(
            nm("x"),
            Arc::clone(&b0),
            Arc::clone(&b3),
            BinderInfo::Default,
        );
        // body #3 under one binder → range 3; binder type #0 → range 1
        assert_eq!(lam_open.data().loose_bvar_range(), 3);
        let app = Expr::app(b0, b3);
        assert_eq!(app.data().loose_bvar_range(), 4);
    }

    #[test]
    fn flags_propagate() {
        let mut g = RecGuard::new();
        let fv = Expr::fvar(nm("h"));
        let mv = Expr::mvar(nm("m"));
        let app = Expr::app(fv, mv);
        assert!(app.data().has_fvar());
        assert!(app.data().has_expr_mvar());
        let sp = Expr::sort(Arc::new(Level::Param(nm("u"))), &mut g).unwrap();
        assert!(sp.data().has_level_param());
        assert!(!sp.data().has_fvar());
    }

    #[test]
    fn structural_eq_implies_hash_eq_and_ptr_neq_ok() {
        let mut g = RecGuard::new();
        let mk = |g: &mut RecGuard| {
            let n = Expr::const_(nm("Nat"), vec![], g).unwrap();
            Expr::forall_e(
                nm("x"),
                Arc::clone(&n),
                Expr::bvar(Nat::from(0u64)),
                BinderInfo::Default,
            )
        };
        let a = mk(&mut g);
        let b = mk(&mut g);
        assert!(!Arc::ptr_eq(&a, &b));
        assert!(Expr::structural_eq(&a, &b, &mut g).unwrap());
        assert_eq!(a.data().hash(), b.data().hash());
    }

    #[test]
    fn alpha_eq_true_for_name_and_info_differing_binders() {
        // `Π (x : Nat), #0` vs `Π (y : Nat), #0` with `BinderInfo`
        // additionally flipped (Default vs Implicit): `structural_eq`
        // (expr_eq_fn<true>/is_bi_equal) must reject on both counts,
        // but `alpha_eq` (expr_eq_fn<false>/is_equal, quot.cpp:33/42's
        // `operator!=`) must accept — binder name and info are exactly
        // what it's insensitive to (expr_eq_fn.cpp:113-119).
        let mut g = RecGuard::new();
        let n = Expr::const_(nm("Nat"), vec![], &mut g).unwrap();
        let a = Expr::forall_e(
            nm("x"),
            Arc::clone(&n),
            Expr::bvar(Nat::from(0u64)),
            BinderInfo::Default,
        );
        let b = Expr::forall_e(
            nm("y"),
            Arc::clone(&n),
            Expr::bvar(Nat::from(0u64)),
            BinderInfo::Implicit,
        );
        assert!(!Expr::structural_eq(&a, &b, &mut g).unwrap());
        assert!(Expr::alpha_eq(&a, &b, &mut g).unwrap());
    }

    #[test]
    fn alpha_eq_false_for_genuine_structural_difference() {
        // Same binder name/info on both sides, but the bodies differ
        // (`#0` vs a literal): a real structural difference, which
        // `alpha_eq` must still catch (it only ignores binder name/
        // info, nothing else).
        let mut g = RecGuard::new();
        let n = Expr::const_(nm("Nat"), vec![], &mut g).unwrap();
        let a = Expr::forall_e(
            nm("x"),
            Arc::clone(&n),
            Expr::bvar(Nat::from(0u64)),
            BinderInfo::Default,
        );
        let b = Expr::forall_e(
            nm("x"),
            Arc::clone(&n),
            Expr::lit(Literal::NatVal(Nat::from(0u64))),
            BinderInfo::Default,
        );
        assert!(!Expr::alpha_eq(&a, &b, &mut g).unwrap());
    }

    #[test]
    fn hash_reject_makes_deep_unequal_cheap() {
        // Two 100k-deep spines differing at the leaf: hash differs, so
        // structural_eq must return false without deep traversal.
        // (Correctness assertion only; the perf claim is the design.)
        let mut g = RecGuard::new();
        let mut a = Expr::bvar(Nat::from(0u64));
        let mut b = Expr::bvar(Nat::from(1u64));
        for _ in 0..100_000 {
            a = Expr::app(a, Expr::lit(Literal::StrVal("x".into())));
            b = Expr::app(b, Expr::lit(Literal::StrVal("x".into())));
        }
        assert!(!Expr::structural_eq(&a, &b, &mut g).unwrap());
    }

    #[test]
    fn app_spine_helpers() {
        let mut g = RecGuard::new();
        let f = Expr::const_(nm("f"), vec![], &mut g).unwrap();
        let x = Expr::lit(Literal::NatVal(Nat::from(1u64)));
        let y = Expr::lit(Literal::NatVal(Nat::from(2u64)));
        let e = Expr::mk_app_spine(Arc::clone(&f), &[x, y]);
        assert!(Arc::ptr_eq(Expr::get_app_fn(&e), &f));
        assert_eq!(Expr::get_app_num_args(&e), 2);
        assert_eq!(Expr::get_app_args(&e).len(), 2);
    }
}
