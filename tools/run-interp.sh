#!/usr/bin/env bash
#
# run-interp.sh -- run the AGDA-SIDE interpreters on a term and print
# what each one answers.
#
# Three independent implementations, on the same closed linear lambda
# term:
#
#   REF   Compile.ClosureConv.Correct.obs      -- the IR's own abstract
#                                                 machine, fuel 64
#   ARM   Compile.ClosureConv.ARM.answerT      -- real AArch64, executed
#                                                 by Control.run, and the
#                                                 heap answer DECODED
#   RUST  Compile.LinToRust.Eval.evalRust      -- the big-step relation
#                                                 `_⇓_`, as a function
#
# REF and ARM are directly comparable: both are `Maybe IR.Val`, and
# `Compile/ClosureConv/ARM.agda` §11 already pins them equal term by
# term.  This script recomputes that rather than trusting it.
#
# RUST is NOT directly comparable and the table says so.  The closure
# converter's answer carries the free variables its block was compiled
# with; the Rust backend SUBSTITUTES them into the body instead.
# `Correct.RelE`'s `rcap` is the constructor saying those two agree only
# up to the realisation relation, so what is printed is the native Rust
# normal form, side by side, and no verdict is offered.  (For a verdict
# up to alpha on the RUST side alone, use `tools/compare.sh`.)
#
# WHAT THIS PROVES.  Nothing that was not already a `refl` in the source
# -- these all compute at typecheck time.  What it BUYS is that you can
# see them, on a term you name, without editing Agda.
#
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib-extract.sh"

usage() {
  cat <<'EOF'
run-interp.sh -- print what each Agda-side interpreter says about a term

USAGE
  tools/run-interp.sh [options] [TERM ...]

With no TERM, every term the driver knows is run.

OPTIONS
  -l, --list     list the terms the driver knows and exit
  -h, --help     this

COLUMNS
  REF        Correct.obs           the IR abstract machine (fuel 64)
  ARM        ARM.answerT           real AArch64, decoded (500 steps, depth 8)
  ARM/REF    do they agree?  Both are `Maybe IR.Val`, compared directly.
  EXIT       the eight-bit observable the emitted binary would exit with
             -- field 0 of the answer record.  `tools/run-arm.sh` checks
             this one against a real process.
  RUST       evalRust's normal form (fuel 40).  A DIFFERENT vocabulary:
             substituted, not captured.  No verdict; see the header.

EXIT STATUS
  0  REF and ARM agreed everywhere
  1  they differed somewhere
  2  the harness failed
EOF
}

TERMS=()
while [ $# -gt 0 ]; do
  case "$1" in
    -l|--list) agda_string 'R.names' || exit 2; printf '%s' "$AGDA_OUT"; exit 0 ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "run-interp.sh: unknown option '$1' (try --help)" >&2; exit 2 ;;
    *)  TERMS+=("$1"); shift ;;
  esac
done

if [ ${#TERMS[@]} -eq 0 ]; then
  agda_string 'R.names' || exit 2
  while IFS= read -r n; do [ -n "$n" ] && TERMS+=("$n"); done <<< "$AGDA_OUT"
fi

printf '%-10s  %-14s %-8s %-8s %-8s %-6s %s\n' TERM REF REF-W ARM-W ARM/REF EXIT RUST
printf -- '--------------------------------------------------------------------------------------\n'

BAD=0
for t in "${TERMS[@]}"; do
  # one agda run per term: the driver packs the whole row
  agda_string "R.interpRow \"$t\"" || exit 2
  IFS=';' read -r REF REFW ARMW RUST DEC <<< "$AGDA_OUT"
  if [ "$REF" = "?" ]; then
    printf '%-10s  unknown term\n' "$t"
    BAD=1
    continue
  fi
  if [ "$REFW" = "$ARMW" ]; then V=AGREE; else V=DIFFER; BAD=1; fi
  printf '%-10s  %-14s %-8s %-8s %-8s %-6s %s\n' \
    "$t" "$REF" "$REFW" "$ARMW" "$V" "$((ARMW % 256))" "$RUST"
done

printf -- '--------------------------------------------------------------------------------------\n'
if [ $BAD -eq 0 ]; then
  echo "REF and ARM agreed on every term."
else
  echo "at least one row DIFFERED (or named an unknown term)."
fi
exit $BAD
