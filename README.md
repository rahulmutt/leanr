# leanr

A pure-Rust implementation of the Lean 4 toolchain, built for
declaration-level incremental compilation and aggressive, correct caching.
End goal: a drop-in replacement for `lean`/`lake` that builds Mathlib —
with sub-second edit feedback.

**Status:** M0 (foundations). Nothing usable yet. Roadmap and design:
[`docs/superpowers/specs/2026-07-04-leanr-architecture-design.md`](docs/superpowers/specs/2026-07-04-leanr-architecture-design.md).

## Quickstart

Requires [mise](https://mise.jdx.dev). Then:

    git clone https://github.com/rahulmutt/leanr && cd leanr
    mise install
    mise run test

All workflows are named mise tasks — run `mise tasks` to list them
(`build`, `test`, `lint`, `ci`, …).

## Layout

See [ARCHITECTURE.md](ARCHITECTURE.md) for the crate map and why the
boundaries fall where they do.

## License

Apache-2.0.
