//! M4b-4a P1: `MetaCtx`'s structure accessors against the oracle's own
//! answers (`tests/fixtures/elab/structures.jsonl`, written by
//! `dump_structs.lean`). Every value compared here was computed by the
//! pinned oracle, none by hand (design spec § Testing).

mod support;

use leanr_kernel::bank::Store;
use leanr_meta::{Config, EnvExtensions, MetaCtx};
use serde_json::Value;
use support::*;

#[test]
fn structure_accessors_match_the_oracle_dump() {
    let r = replay_fixture_in("elab", "Elab0.olean");
    let view = r.env.view();
    let mut scratch = Store::scratch();
    let base = Some(view.store);
    let text = std::fs::read_to_string(fixture_in("elab", "structures.jsonl")).unwrap();
    // Intern every name we will look up BEFORE building the MetaCtx,
    // which borrows `scratch` mutably for its lifetime.
    let recs: Vec<Value> = text
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    let mut name = |s: &str| decode_name(&mut scratch, base, s);
    let mut probes = Vec::new();
    for rec in &recs {
        let s = rec["s"].as_str().unwrap();
        let sid = name(s);
        let finds: Vec<_> = rec["find"]
            .as_array()
            .unwrap()
            .iter()
            .map(|f| {
                (
                    name(f["f"].as_str().unwrap()),
                    f["in"].as_str().map(str::to_string),
                )
            })
            .collect();
        let paths: Vec<_> = rec["paths"]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| {
                (
                    name(p["base"].as_str().unwrap()),
                    p["path"].as_array().map(|a| {
                        a.iter()
                            .map(|x| x.as_str().unwrap().to_string())
                            .collect::<Vec<_>>()
                    }),
                )
            })
            .collect();
        probes.push((s.to_string(), sid, finds, paths, rec.clone()));
    }
    let nat = name("Nat");
    let ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        EnvExtensions {
            structures: &r.structures,
            ..Default::default()
        },
    );
    let render = |n| name_to_string(ctx.store(), base, Some(n));
    assert!(
        probes.len() >= 20,
        "expected every Elab0 structure, got {}",
        probes.len()
    );
    for (s, sid, finds, paths, rec) in probes {
        assert!(ctx.is_structure(sid), "{s}: not a structure");
        let fields: Vec<String> = ctx
            .get_structure_fields(sid)
            .iter()
            .map(|&n| render(n))
            .collect();
        let want: Vec<String> = rec["fields"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_str().unwrap().to_string())
            .collect();
        assert_eq!(fields, want, "{s}: fields");
        let info = ctx.get_structure_info(sid).unwrap();
        let got_info: Vec<Value> = info
            .field_info
            .iter()
            .map(|fi| {
                serde_json::json!({
            "f": render(fi.field_name), "proj": render(fi.proj_fn),
            "sub": fi.subobject.map(render), "bi": bi_str(fi.binder_info)})
            })
            .collect();
        assert_eq!(
            Value::Array(got_info),
            rec["info"],
            "{s}: fieldInfo (order included)"
        );
        let got_parents: Vec<Value> = info
            .parent_info
            .iter()
            .map(|p| {
                serde_json::json!({
            "s": render(p.struct_name), "sub": p.subobject, "proj": render(p.proj_fn)})
            })
            .collect();
        assert_eq!(Value::Array(got_parents), rec["parents"], "{s}: parentInfo");
        for (f, want) in finds {
            assert_eq!(
                ctx.find_field(sid, f).map(render),
                want,
                "{s}: findField? {}",
                render(f)
            );
        }
        for (b, want) in paths {
            let got = ctx
                .get_path_to_base_structure(b, sid)
                .map(|p| p.into_iter().map(render).collect::<Vec<_>>());
            assert_eq!(got, want, "{s}: getPathToBaseStructure? {}", render(b));
        }
    }
    // A non-structure answers "no" without panicking (the oracle's
    // `getStructureInfo` panics; untrusted input forbids that here).
    assert!(!ctx.is_structure(nat));
    assert!(ctx.get_structure_fields(nat).is_empty());
    assert!(ctx.find_field(nat, nat).is_none());
    assert!(ctx.get_path_to_base_structure(nat, nat).is_some()); // base == s: `[]`, as the oracle
}

/// The dumper's `biStr` spelling (`dump_structs.lean`).
fn bi_str(bi: leanr_kernel::BinderInfo) -> &'static str {
    use leanr_kernel::BinderInfo::*;
    match bi {
        Default => "default",
        Implicit => "implicit",
        StrictImplicit => "strictImplicit",
        InstImplicit => "instImplicit",
    }
}
