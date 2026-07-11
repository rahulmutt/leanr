use std::path::Path;

use leanr_build::config::{parse_lakefile_toml, LeanOptionValue};
use leanr_build::modules::{Glob, ModuleName};

/// Every vendored real-world lakefile parses with zero unknown-key warnings.
#[test]
fn all_vendored_lakefiles_parse_cleanly() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lakefiles");
    let mut seen = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("toml") {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        let parsed = parse_lakefile_toml(&text, &path).unwrap();
        assert!(
            parsed.warnings.is_empty(),
            "{}: unexpected warnings {:?}",
            path.display(),
            parsed.warnings
        );
        assert!(!parsed.config.name.is_empty());
        seen += 1;
    }
    assert!(seen >= 7, "expected the 7 vendored fixtures, found {seen}");
}

#[test]
fn batteries_fields_land_where_expected() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lakefiles");
    let path = dir.join("batteries.toml");
    let parsed = parse_lakefile_toml(&std::fs::read_to_string(&path).unwrap(), &path).unwrap();
    let c = parsed.config;
    assert_eq!(c.name, "batteries");
    assert_eq!(c.default_targets, ["Batteries", "runLinter"]);
    assert_eq!(
        c.lean_options.get("linter.missingDocs"),
        Some(&LeanOptionValue::Bool(true))
    );
    let recycling = c
        .lean_libs
        .iter()
        .find(|l| l.name == "BatteriesRecycling")
        .unwrap();
    assert_eq!(
        recycling.effective_globs(),
        [Glob::Submodules(
            ModuleName::parse("BatteriesRecycling").unwrap()
        )]
    );
    // Default globs: roots default to [name], globs default to roots.map(One).
    let main = c.lean_libs.iter().find(|l| l.name == "Batteries").unwrap();
    assert_eq!(
        main.effective_roots(),
        [ModuleName::parse("Batteries").unwrap()]
    );
    assert_eq!(
        main.effective_globs(),
        [Glob::One(ModuleName::parse("Batteries").unwrap())]
    );
    assert_eq!(c.lean_exes.len(), 3);
    let shake = c.lean_exes.iter().find(|e| e.name == "shake").unwrap();
    assert_eq!(shake.root.as_deref(), Some("Shake.Main"));
}

#[test]
fn unknown_keys_warn_but_do_not_fail() {
    let text = r#"
name = "x"
someFutureLakeKey = 3

[[lean_lib]]
name = "X"
anotherNewKey = "y"
"#;
    let parsed = parse_lakefile_toml(text, Path::new("lakefile.toml")).unwrap();
    assert_eq!(parsed.config.name, "x");
    assert_eq!(parsed.warnings.len(), 2);
    assert!(parsed.warnings[0].contains("someFutureLakeKey"));
    assert!(parsed.warnings[1].contains("anotherNewKey"));
}

#[test]
fn option_value_types_and_guillemet_exe_names() {
    let text = r#"
name = "x"

[[lean_lib]]
name = "X"
leanOptions = {a = true, b = 3, c = "s"}

[[lean_exe]]
name = "«cache-test»"
root = "Cache.Test"
"#;
    let parsed = parse_lakefile_toml(text, Path::new("lakefile.toml")).unwrap();
    let lib = &parsed.config.lean_libs[0];
    assert_eq!(
        lib.lean_options.get("a"),
        Some(&LeanOptionValue::Bool(true))
    );
    assert_eq!(lib.lean_options.get("b"), Some(&LeanOptionValue::Int(3)));
    assert_eq!(
        lib.lean_options.get("c"),
        Some(&LeanOptionValue::String("s".into()))
    );
    assert_eq!(parsed.config.lean_exes[0].name, "«cache-test»");
}

#[test]
fn toml_syntax_error_names_the_file() {
    let err = parse_lakefile_toml("name = ", Path::new("pkg/lakefile.toml")).unwrap_err();
    assert!(err.to_string().contains("pkg/lakefile.toml"));
}

/// Regression (differential tier, `closure_resolves_without_warnings`):
/// ProofWidgets' bridged lakefile.lean carries `needs` on its `lean_lib`
/// targets and top-level `input_file`/`input_dir` facet declarations
/// (Lake's own snake_case keys, unlike its otherwise-camelCase schema).
/// None of these affect module resolution; they must parse as
/// parsed-but-unused, not warn as unknown keys.
#[test]
fn proofwidgets_needs_and_input_facets_do_not_warn() {
    let text = r#"
name = "proofwidgets"
testDriver = "test"
defaultTargets = ["ProofWidgets"]

[[lean_lib]]
name = "ProofWidgets"
needs = ["widgetJsAll"]

[[lean_lib]]
name = "ProofWidgets.Demos"
globs = ["ProofWidgets.Demos.+"]
needs = ["widgetJsAll"]

[[lean_lib]]
name = "test"
globs = ["test.+"]

[[input_file]]
name = "widgetPackageJson"
path = "widget/package.json"
text = true

[[input_dir]]
name = "widgetJsSrcs"
path = "widget/src"
text = true
filter = {extension = ["ts", "tsx", "js", "jsx"]}
"#;
    let parsed = parse_lakefile_toml(text, Path::new("lakefile.toml")).unwrap();
    assert!(
        parsed.warnings.is_empty(),
        "unexpected warnings: {:?}",
        parsed.warnings
    );
    let lib = parsed
        .config
        .lean_libs
        .iter()
        .find(|l| l.name == "ProofWidgets")
        .unwrap();
    assert_eq!(
        lib.needs.as_deref(),
        Some(["widgetJsAll".to_string()].as_slice())
    );
    assert!(parsed.config.input_file.is_some());
    assert!(parsed.config.input_dir.is_some());
}
