#!/usr/bin/env bash
# Enumerate the pinned toolchain's compiled builtin parsers — the M3a
# porting surface (spec §Architecture / builtin, docs/superpowers/specs/
# 2026-07-13-m3a-parser-foundations-design.md). Output: one line per
# attribute hit, "<category>\t<file>:<line>\t<decl>", sorted.
#
# Why this is more than a `grep -rnoE` one-liner:
#   - `@[builtin_*_parser]` category names are NOT all lowercase
#     (`builtin_doElem_parser`, `builtin_structInstFieldDecl_parser`) — a
#     `[a-z_]+` class silently drops two whole categories (do-elements:
#     28 hits; struct-instance field decls: 2 hits).
#   - The attribute and its `def` sometimes sit on different lines
#     (`@[builtin_term_parser]\ndef «forall» := ...`) — a same-line-only
#     regex silently drops those decls (found: atom, nonReserved,
#     unicodeAtom, moduleDoc, «forall», «letrec» — the last two are not
#     obscure).
#   - Declared names are sometimes qualified (`Term.quot`,
#     `Tactic.quotSeq`) — an identifier class without `.` truncates them.
#   - The toolchain's own doc comments and `--`-commented-out code show
#     *example* `@[builtin_..._parser] def ...` lines as prose (found in
#     Lean/Parser/Term.lean, Lean/Attributes.lean, Lean/Elab/StructInst.lean,
#     Lean/Meta/RecursorInfo.lean, Lean/Compiler/ExternAttr.lean) — plain
#     grep counts these as hits, but they are not compiled declarations.
#   - The attribute is not confined to `Lean/Parser/`: three genuine
#     builtin parsers live under `Lean/Elab/` and `Lean/Meta/`
#     (`Term.elabToSyntax`, `grindPattern`, `initGrindNorm`).
#
# This script scans the whole pinned `src/lean` tree (grep -l prefilter
# for speed; ~14 files ever match) with a comment/string-aware character
# scanner (nested `/- -/`, `--` line comments, `"..."` string literals),
# so it reports only live declarations, from wherever they actually live.
set -euo pipefail

L="$(lean --print-prefix)/src/lean"

SCANNER=$(mktemp)
trap 'rm -f "$SCANNER"' EXIT INT TERM

cat >"$SCANNER" <<'PERL'
#!/usr/bin/env perl
# Comment/string-aware scan for live `@[builtin_*_parser] def NAME`
# declarations. Tracks nested `/- -/` block comments, `--` line comments,
# and `"..."` string literals (with `\`-escaping) so that example code in
# doc comments or disabled code in line comments never counts as a hit.
use strict;
use warnings;

for my $file (@ARGV) {
    open(my $fh, '<', $file) or die "cannot open $file: $!";
    local $/;
    my $src = <$fh>;
    close $fh;

    my @chars = split //, $src;
    my $n = scalar @chars;
    my $i = 0;
    my $line = 1;
    my $depth = 0;          # nested /- -/ block-comment depth
    my $in_string = 0;
    my $in_line_comment = 0;

    while ($i < $n) {
        my $c = $chars[$i];

        if ($c eq "\n") {
            $line++;
            $in_line_comment = 0;
            $i++;
            next;
        }
        if ($in_line_comment) { $i++; next; }
        if ($in_string) {
            if ($c eq '\\') { $i += 2; next; }
            if ($c eq '"')  { $in_string = 0; $i++; next; }
            $i++;
            next;
        }

        if ($depth == 0) {
            if ($c eq '"') { $in_string = 1; $i++; next; }
            if ($c eq '-' && $i+1 < $n && $chars[$i+1] eq '-') {
                $in_line_comment = 1; $i += 2; next;
            }
            if ($c eq '/' && $i+1 < $n && $chars[$i+1] eq '-') {
                $depth = 1; $i += 2; next;
            }
            if ($c eq '@' && substr($src, $i, 10) eq '@[builtin_') {
                if (substr($src, $i) =~ /\A@\[(builtin_[A-Za-z]+_parser)/) {
                    my $cat = $1;
                    my $hitline = $line;
                    # `def NAME` follows within the attribute's own
                    # statement — same line or (if the attribute list is
                    # alone on its line) the next; bounded window is
                    # plenty and avoids crossing into unrelated code.
                    my $window = substr($src, $i, 400);
                    if ($window =~ /\][\s\S]*?\bdef\s+([A-Za-z0-9_.«»?!']+)/) {
                        print "$cat\t$file:$hitline\t$1\n";
                    } else {
                        print STDERR "builtin-surface: unmatched attribute at $file:$hitline\n";
                    }
                }
                $i++;
                next;
            }
            $i++;
            next;
        } else {
            # inside a (possibly nested) block comment: only /- and -/ matter
            if ($c eq '/' && $i+1 < $n && $chars[$i+1] eq '-') { $depth++; $i += 2; next; }
            if ($c eq '-' && $i+1 < $n && $chars[$i+1] eq '/') { $depth--; $i += 2; next; }
            $i++;
            next;
        }
    }
}
PERL

mapfile -t candidates < <(grep -rlE '@\[builtin_[A-Za-z_]+_parser' "$L")
if [ "${#candidates[@]}" -eq 0 ]; then
    echo "builtin-surface: no @[builtin_*_parser] hits found under $L — toolchain layout changed?" >&2
    exit 1
fi

perl "$SCANNER" "${candidates[@]}" | sort
