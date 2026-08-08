#!/usr/bin/env bash
#
# run-rust.sh -- emit the Rust a closed linear lambda term compiles to,
# compile it with rustc, RUN it, and check what it printed against the
# Agda-side evaluator.
#
# TWO RENDERINGS, and the difference is the point.
#
#   --old   `Compile.LinToRust.Codegen.srcTm`, the original emitter --
#           only defined on the pure lambda fragment, so an arithmetic
#           term answers `-`.
#           It binds the value to `_`, so running it observes nothing;
#           and rustc REJECTS it outright with E0282 ("type annotations
#           needed"), because an untyped lambda has no Rust type.  Kept
#           so that this stays a measurement.
#
#   default `Compile.LinNum.Rust.srcOf`.  The same compiled expression,
#           rendered into ONE universal value type
#
#               enum V { Fun(Box<dyn FnOnce(V) -> V>), Num(u64) }
#
#           and it PRINTS its answer: a number if the program computed
#           one, `fun` if the answer is a closure.
#
# WHAT RUSTC IS BEING ASKED.  Every emitted closure is `move` and every
# variable occurs exactly once, so the borrow checker is an INDEPENDENT
# check of the source's linearity: `Box<dyn FnOnce>` may be called at
# most once and `move` takes captures by value, so a term that used a
# variable twice would compile to code that moves out of a moved value
# and rustc would reject it (E0382).  The source type system makes that
# term unwritable (`Use⊎` has no `(true,true)`); rustc makes the output
# unbuildable; neither knows about the other.  `rustc` accepting the
# output is therefore a real result, and it is reported separately from
# the answer.
#
# WHAT IT DOES NOT PROVE.  rustc is not in this development's trusted
# base.  Agreement between the printed string and `evalRust`'s answer
# is a DIFFERENTIAL check between two implementations, not a theorem.
#
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib-extract.sh"

OUTDIR="${OUTDIR:-$(mktemp -d "${TMPDIR:-/tmp}/run-rust.XXXXXX")}"
SHOW_SRC=no
OLD=no
KEEP_OUT=no
EDITION=2021

usage() {
  cat <<'EOF'
run-rust.sh -- compile and execute the Rust a linear lambda term compiles to

USAGE
  tools/run-rust.sh [options] TERM

OPTIONS
  -s, --src      print the emitted Rust as well
      --old      emit Codegen.srcTm instead (the `let _ =` unit rustc rejects)
  -o, --out DIR  write TERM.rs and TERM.bin into DIR and keep them
  -l, --list     list the terms the driver knows and exit
  -h, --help     this

EXIT STATUS
  0  rustc accepted it, it ran, and it agreed with the Agda evaluator
  1  it ran and DISAGREED, or rustc rejected it
  2  the harness failed (no agda, unknown term, ...)
     -- a MISSING rustc is not a failure: the source is still emitted
        and checked against the model, and the script says so.
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    -s|--src)  SHOW_SRC=yes; shift ;;
    --old)     OLD=yes; shift ;;
    -o|--out)  OUTDIR="$2"; KEEP_OUT=yes; mkdir -p "$OUTDIR"; shift 2 ;;
    -l|--list) agda_string 'R.names' || exit 2; printf '%s' "$AGDA_OUT"; exit 0 ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "run-rust.sh: unknown option '$1' (try --help)" >&2; exit 2 ;;
    *)  TERM_NAME="$1"; shift ;;
  esac
done

if [ -z "${TERM_NAME:-}" ]; then usage >&2; exit 2; fi

echo "run-rust.sh: term = $TERM_NAME"
check_known "$TERM_NAME" || exit 2

# ---- what the Agda evaluator says -----------------------------------
agda_string "R.rustAns \"$TERM_NAME\"" || exit 2 ; ANS="$AGDA_OUT"
echo "  Agda-side evaluator: $ANS"

# what the emitted program will print, predicted by the model
agda_string "R.rustPred \"$TERM_NAME\"" || exit 2 ; PRED="$AGDA_OUT"
echo "  predicted stdout:   $PRED"

# ---- the source -----------------------------------------------------
if [ "$OLD" = yes ]; then
  agda_string "R.rustSrc0 \"$TERM_NAME\"" || exit 2
else
  agda_string "R.rustSrc \"$TERM_NAME\"" || exit 2
fi
if [ "$OLD" = yes ] && [ "$AGDA_OUT" = "-" ]; then
  echo "  '$TERM_NAME' has arithmetic in it; the --old emitter does not accept it." >&2
  [ "$KEEP_OUT" = no ] && rm -rf "$OUTDIR"
  exit 2
fi
RS="$OUTDIR/$TERM_NAME.rs"
printf '%s' "$AGDA_OUT" > "$RS"
echo "  emitted $(wc -l < "$RS" | tr -d ' ') lines of Rust -> $RS"

[ "$SHOW_SRC" = yes ] && { echo; cat "$RS"; echo; }

# ---- rustc ----------------------------------------------------------
if ! command -v rustc >/dev/null 2>&1; then
  echo "  rustc is NOT installed, so the borrow-checker result is UNKNOWN."
  echo "  (the emitted source above is still exactly what the model says)"
  [ "$KEEP_OUT" = no ] && rm -rf "$OUTDIR"
  exit 0
fi

BIN="$OUTDIR/$TERM_NAME.bin"
LOG="$OUTDIR/$TERM_NAME.rustc.log"
if rustc --edition "$EDITION" -D warnings -o "$BIN" "$RS" > "$LOG" 2>&1; then
  echo "  rustc ACCEPTED it (edition $EDITION, -D warnings)."
  echo "    -- every closure is 'move', every variable used once:"
  echo "       the borrow checker independently validated linearity."
else
  echo "  rustc REJECTED it:"
  sed 's/^/    /' "$LOG"
  [ "$KEEP_OUT" = no ] && rm -rf "$OUTDIR"
  exit 1
fi

GOT="$("$BIN")"
echo "  ran it: stdout = $GOT"

RC=0
if [ "$GOT" = "$PRED" ]; then
  echo "  AGREE: the process and the Agda evaluator both say $PRED."
else
  echo "  DIFFER: process printed '$GOT', the model predicted '$PRED'."
  RC=1
fi

if [ "$KEEP_OUT" = no ]; then rm -rf "$OUTDIR"; else echo "  kept: $RS  $BIN"; fi
exit $RC
