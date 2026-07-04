use std::sync::{Arc, Mutex};

use leanr_query::{line_count, trimmed_text, SourceText};
use salsa::Setter;

/// A database that records which queries actually executed, so tests can
/// assert on recomputation behavior — over-invalidation is a perf bug,
/// under-invalidation is a correctness bug, and both are tested this way.
///
/// Note on salsa 0.23 adaptation: `Database::salsa_event` is no longer a
/// trait method to override. Instead the event hook is a closure passed to
/// `Storage::new`, and `Database` (via `HasStorage`) requires `Clone`. This
/// mirrors the idiom used in salsa's own `tests/common/mod.rs`
/// (`EventLoggerDatabase`).
#[salsa::db]
#[derive(Clone)]
struct TestDb {
    storage: salsa::Storage<Self>,
    executed: Arc<Mutex<Vec<String>>>,
}

impl Default for TestDb {
    fn default() -> Self {
        let executed = Arc::new(Mutex::new(Vec::new()));
        let storage = salsa::Storage::new(Some(Box::new({
            let executed = Arc::clone(&executed);
            move |event: salsa::Event| {
                if let salsa::EventKind::WillExecute { database_key } = event.kind {
                    executed.lock().unwrap().push(format!("{database_key:?}"));
                }
            }
        })));
        Self { storage, executed }
    }
}

#[salsa::db]
impl salsa::Database for TestDb {}

impl TestDb {
    fn executions_of(&self, query: &str) -> usize {
        self.executed
            .lock()
            .unwrap()
            .iter()
            .filter(|k| k.contains(query))
            .count()
    }
}

#[test]
fn repeated_queries_are_memoized() {
    let db = TestDb::default();
    let src = SourceText::new(&db, "a\nb\nc".to_string());

    assert_eq!(line_count(&db, src), 3);
    assert_eq!(line_count(&db, src), 3);

    assert_eq!(db.executions_of("line_count"), 1);
    assert_eq!(db.executions_of("trimmed_text"), 1);
}

#[test]
fn editing_the_input_invalidates() {
    let mut db = TestDb::default();
    let src = SourceText::new(&db, "a\nb".to_string());

    assert_eq!(line_count(&db, src), 2);
    src.set_text(&mut db).to("a\nb\nc".to_string());
    assert_eq!(line_count(&db, src), 3);

    assert_eq!(db.executions_of("line_count"), 2);
}

#[test]
fn early_cutoff_shields_downstream_queries() {
    let mut db = TestDb::default();
    let src = SourceText::new(&db, "a\nb".to_string());

    assert_eq!(line_count(&db, src), 2);

    // Whitespace-only edit: trimmed_text must re-run, but its value is
    // unchanged, so line_count must NOT re-run. This is the firewall.
    src.set_text(&mut db).to("a\nb   \n\n".to_string());
    assert_eq!(line_count(&db, src), 2);

    assert_eq!(db.executions_of("trimmed_text"), 2);
    assert_eq!(db.executions_of("line_count"), 1);
}

#[test]
fn trimmed_text_behavior() {
    let db = TestDb::default();
    let src = SourceText::new(&db, "x  \n".to_string());
    assert_eq!(trimmed_text(&db, src), "x");
}
