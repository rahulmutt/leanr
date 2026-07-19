//! The `leanr fmt` engine (M3c): a preserve-fallback source formatter
//! over `leanr_syntax` lossless trees. Consumes trees only; never
//! re-lexes source. See docs/superpowers/specs/2026-07-19-m3c-fmt-thin-slice-design.md.

pub mod doc;
