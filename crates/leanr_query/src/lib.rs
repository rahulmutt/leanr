//! The incremental query engine. Everything leanr computes is a memoized
//! salsa query; early cutoff is the mechanism firewall queries rely on.

#[salsa::input]
pub struct SourceText {
    #[returns(ref)]
    pub text: String,
}

#[salsa::tracked]
pub fn trimmed_text(db: &dyn salsa::Database, source: SourceText) -> String {
    source.text(db).trim_end().to_string()
}

#[salsa::tracked]
pub fn line_count(db: &dyn salsa::Database, source: SourceText) -> usize {
    trimmed_text(db, source).lines().count()
}
