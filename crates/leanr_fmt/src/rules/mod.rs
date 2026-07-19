//! Style rules (spec §Rule dispatch). Each rule either restructures a
//! node (imports) or is applied by the renderer (spacing); everything
//! without a rule is preserve-fallback.

pub mod imports;
pub mod spacing;
