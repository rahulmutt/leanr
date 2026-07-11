//! Lake-compatible package model + module graph (M2a).
//! Spec: docs/superpowers/specs/2026-07-11-m2a-package-model-design.md

pub mod bridge;
pub mod config;
mod error;
pub mod fetch;
pub mod graph;
pub mod manifest;
pub mod modules;
pub mod scanner;

pub use error::BuildError;
