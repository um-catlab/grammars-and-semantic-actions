#!/usr/bin/env bash
#
# run-arm.sh -- compile a closed linear lambda term all the way to real
# AArch64, assemble it with clang, RUN it, and check the process's exit
# status against the number the Agda model predicted.
#
# The chain is
#
#     Tm []  --Convert-->  IR + Table  --ARM.compileC-->  CProg
#            --ControlEmit.unitWith-->  AArch64 text  --clang-->  a.out
#
# and every arrow but the last is in `src/Compile/LinNum/` (which is
# `src/Compile/ClosureConv/` extended with literals and `+`).  The
# assembly text is `Compile.LinNum.Emit.asmN`, extracted by the sentinel
# trick in `tools/lib-extract.sh`.  On a term with no arithmetic in it
# that emitter reproduces `ClosureConv.Emit.asmT` character for
# character -- `Compile/LinNum/Emit.agda` section 3.3 pins it.
#
# WHAT THE EXIT STATUS IS.  The emitted `finCode` does `ldr x0, [x9]`
# and masks to eight bits: the machine halts holding a heap ADDRESS,
# and what is reported is FIELD 0 OF THE RECORD AT THAT ADDRESS.
#
#   for a NUMBER   that field IS the number -- so `(\x. x + 1) 41`
#                  exits 42, and nothing is forgotten;
#   for a CLOSURE  it is the block's CODE ADDRESS, so the status names
#                  the instruction the answer closure would jump to and
#                  forgets its environment.  `Compile/ClosureConv/Emit.agda`
#                  section B is the argument that this is the best eight-bit
#                  channel available for a language with no base values.
#
# WHAT THIS PROVES.  That the emitted text assembles and runs, and that
# the real process agrees with `Control.run` -- the Agda model of the
# machine -- on the observable.  It does NOT prove the model faithful:
# no development proves its own model of a chip.  A DISAGREEMENT here
# would be a real bug in the emitter or in the model, and that is the
# whole point of running it.
#
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib-extract.sh"

OUTDIR="${OUTDIR:-$(mktemp -d "${TMPDIR:-/tmp}/run-arm.XXXXXX")}"
SHOW_ASM=no
KEEP_OUT=no

usage() {
  cat <<'EOF'
run-arm.sh -- assemble and execute the AArch64 a linear lambda term compiles to

USAGE
  tools/run-arm.sh [options] TERM

OPTIONS
  -a, --asm      print the emitted assembly as well
  -o, --out DIR  write TERM.s and TERM.bin into DIR and keep them
  -l, --list     list the terms the driver knows and exit
  -h, --help     this

TERM is a name from `Compile.Suite.Run.table`; --list prints them.

EXIT STATUS
  0  the process ran and its status matched the model's prediction
  1  they DIFFERED (a real divergence between the machine and the model)
  2  the harness failed (no agda, no clang, unknown term, ...)
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    -a|--asm)  SHOW_ASM=yes; shift ;;
    -o|--out)  OUTDIR="$2"; KEEP_OUT=yes; mkdir -p "$OUTDIR"; shift 2 ;;
    -l|--list) agda_string 'R.names' || exit 2; printf '%s' "$AGDA_OUT"; exit 0 ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "run-arm.sh: unknown option '$1' (try --help)" >&2; exit 2 ;;
    *)  TERM_NAME="$1"; shift ;;
  esac
done

if [ -z "${TERM_NAME:-}" ]; then usage >&2; exit 2; fi

command -v clang >/dev/null 2>&1 || { echo "run-arm.sh: no 'clang' on PATH" >&2; exit 2; }

case "$(uname -m)" in
  arm64|aarch64) ;;
  *) echo "run-arm.sh: this emits AArch64; you are on $(uname -m)." >&2
     echo "            the .s will still be written, but not assembled." >&2 ;;
esac

echo "run-arm.sh: term = $TERM_NAME"

check_known "$TERM_NAME" || exit 2

# ---- the model's numbers -------------------------------------------
agda_string "R.armLen \"$TERM_NAME\"" || exit 2 ; LEN="$AGDA_OUT"
agda_string "R.armExit \"$TERM_NAME\"" || exit 2 ; RAW="$AGDA_OUT"
agda_string "R.refExit \"$TERM_NAME\"" || exit 2 ; REFW="$AGDA_OUT"
agda_string "R.refAns  \"$TERM_NAME\"" || exit 2 ; ANS="$AGDA_OUT"
PRED=$(( RAW % 256 ))

echo "  model: ${LEN} instructions; answer = ${ANS}"
echo "         IR word = ${REFW}; AArch64 word = ${RAW}; predicted exit = ${PRED}"
if [ "$RAW" != "$REFW" ]; then
  echo "  WARNING: the IR model and the AArch64 model disagree on the word." >&2
fi

# ---- the assembly ---------------------------------------------------
agda_string "R.armAsm \"$TERM_NAME\"" || exit 2
S="$OUTDIR/$TERM_NAME.s"
printf '%s' "$AGDA_OUT" > "$S"
echo "  emitted $(wc -l < "$S" | tr -d ' ') lines of AArch64 -> $S"

[ "$SHOW_ASM" = yes ] && { echo; cat "$S"; echo; }

case "$(uname -m)" in
  arm64|aarch64) ;;
  *) echo "  (not assembled: wrong host architecture)"; exit 0 ;;
esac

# ---- assemble and run -----------------------------------------------
BIN="$OUTDIR/$TERM_NAME.bin"
if ! clang -o "$BIN" "$S" 2>"$OUTDIR/$TERM_NAME.clang.log"; then
  echo "  clang FAILED:" >&2
  cat "$OUTDIR/$TERM_NAME.clang.log" >&2
  exit 2
fi
echo "  clang accepted it -> $BIN"

"$BIN"
GOT=$?
echo "  ran it: exit status = $GOT"

RC=0
if [ "$GOT" = "$PRED" ]; then
  echo "  AGREE: the process and Control.run both say $PRED."
else
  echo "  DIFFER: process said $GOT, the model said $PRED."
  RC=1
fi

if [ "$KEEP_OUT" = no ]; then
  rm -rf "$OUTDIR"
else
  echo "  kept: $S  $BIN"
fi
exit $RC
