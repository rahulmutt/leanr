//! #[cfg(test)] support: a real `Workspace` resolved from a synthetic
//! on-disk project (no git, no lake, fake toolchain dir). Shared by the
//! setup and compile unit tests.

pub(crate) struct TestWs {
    // Never read directly; kept alive so its `Drop` doesn't delete the
    // synthetic project out from under `ws` while a test still holds it.
    #[allow(dead_code)]
    pub tmp: tempfile::TempDir,
    pub ws: crate::Workspace,
}

pub(crate) fn synthetic() -> TestWs {
    synthetic_with(
        "name = \"app\"\ndefaultTargets = [\"App\"]\nleanOptions = {autoImplicit = false}\n\n\
         [[lean_lib]]\nname = \"App\"\nleanOptions = {\"pp.unicode.fun\" = true}\n",
        &[("App.lean", "import App.Sub\n"), ("App/Sub.lean", "")],
    )
}

pub(crate) fn synthetic_with(lakefile: &str, files: &[(&str, &str)]) -> TestWs {
    let tmp = tempfile::TempDir::new().unwrap();
    let write = |rel: &str, text: &str| {
        let p = tmp.path().join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    };
    write("lakefile.toml", lakefile);
    for (rel, text) in files {
        write(rel, text);
    }
    write(
        "lake-manifest.json",
        r#"{"version": "1.2.0", "packages": []}"#,
    );
    let fake_toolchain = tmp.path().join("fake-toolchain");
    std::fs::create_dir_all(&fake_toolchain).unwrap();
    std::fs::write(fake_toolchain.join("Init.olean"), "").unwrap();
    let opts = crate::ResolveOptions {
        targets: vec![],
        lake: crate::bridge::LakeInvoker::default(),
        toolchain_olean_dir: fake_toolchain,
        cache_root: tmp.path().join("xdg-cache"),
    };
    let ws = crate::resolve(tmp.path(), &opts).unwrap();
    TestWs { tmp, ws }
}
