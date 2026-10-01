//! M4b-4c P1: the `shouldElabAsElim` environment predicates
//! (`AuxRecursor.lean:31-51`; `App.lean:1322-1328`). Oracle-gated over the
//! whole Elab0 fixture by `tests/aux_recursor_oracle.rs`; these pin the
//! suffix rules and the `Eq.ndrec*` hard-codes on synthetic names, which
//! no fixture declares.

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::Environment;

use crate::{Config, EnvExtensions, MetaCtx};

fn name(st: &mut Store, dotted: &str) -> NameId {
    let mut parent = None;
    for part in dotted.split('.') {
        let s = st.intern_str(None, part).unwrap();
        parent = Some(st.name_str(None, parent, s).unwrap());
    }
    parent.unwrap()
}

#[test]
fn aux_recursor_suffix_rules() {
    let mut env = Environment::default();
    let names: Vec<NameId> = [
        "T.casesOn",
        "T.casesOn_1",
        "T.casesOnX",
        "T.recOn",
        "T.brecOn",
        "T.below",
        "U.casesOn",
        "Eq.ndrec",
        "Eq.ndrec_symm",
        "Eq.ndrecOn",
        "tagged",
    ]
    .iter()
    .map(|s| name(env.store_mut(), s))
    .collect();
    let [cases, cases_1, cases_x, rec_on, brec_on, below, untagged_cases, ndrec, ndrec_symm, ndrec_on, tagged] =
        names[..]
    else {
        unreachable!()
    };
    // `U.casesOn` is deliberately NOT in the tag set: the suffix alone
    // never makes an aux recursor (`isAuxRecursorWithSuffix`, :39-42).
    let aux = [cases, cases_1, cases_x, rec_on, brec_on, below];
    let view = env.view();
    let mut scratch = Store::scratch();
    let ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        EnvExtensions {
            aux_recs: &aux,
            elab_as_elim: &[tagged],
            ..Default::default()
        },
    );
    assert!(ctx.is_cases_on_recursor(cases));
    assert!(
        ctx.is_cases_on_recursor(cases_1),
        "`casesOn_` prefix is accepted"
    );
    assert!(
        !ctx.is_cases_on_recursor(cases_x),
        "`casesOnX` is not `casesOn_…`"
    );
    assert!(ctx.is_aux_recursor(cases_x), "but it IS tagged");
    assert!(
        !ctx.is_cases_on_recursor(untagged_cases),
        "suffix without tag"
    );
    assert!(ctx.is_rec_on_recursor(rec_on) && !ctx.is_rec_on_recursor(cases));
    assert!(ctx.is_brec_on_recursor(brec_on) && !ctx.is_brec_on_recursor(rec_on));
    assert!(ctx.is_aux_recursor(below) && !ctx.is_cases_on_recursor(below));
    // Hard-coded in `isAuxRecursor` (AuxRecursor.lean:33-36), untagged.
    for n in [ndrec, ndrec_symm, ndrec_on] {
        assert!(ctx.is_aux_recursor(n));
    }
    assert!(
        !ctx.is_rec_on_recursor(ndrec_on),
        "`ndrecOn` is not `recOn`"
    );
    assert!(ctx.has_elab_as_elim_tag(tagged) && !ctx.has_elab_as_elim_tag(cases));
}
