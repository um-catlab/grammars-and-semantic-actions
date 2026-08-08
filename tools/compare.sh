#!/usr/bin/env bash
#
# compare.sh -- run the three backends on generated closed linear
# lambda terms and print a divergence table.
#
# Nothing is executed at runtime: every observable in this development
# computes at TYPECHECK time, so the harness generates a tiny Agda file
# that pins the whole report against a sentinel string, runs `agda`, and
# reads the normal form Agda prints back in the resulting type error.
# That is the extraction mechanism, and it is deliberate: the error IS
# the output channel.
#
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$REPO_ROOT/src"

# ------------------------------------------------------------------ #
# defaults
# ------------------------------------------------------------------ #
COUNT=6            # number of GENERATED terms
DEPTH=5            # height bound on generated terms
SEED=42            # LCG seed (TheoryGrammar.Generate's own LCG)
ARM_FUEL=500       # AArch64 machine steps
ARM_DEPTH=8        # closure-decode depth
REF_FUEL=64        # IR abstract-machine fuel (64 == Correct.obs)
RUST_FUEL=40       # big-step evaluator fuel
BAD_ARM=false
BAD_RUST=false
SYNTACTIC=false   # RUST/SRC compares up to alpha unless this is true
CORPUS=yes         # include the six pinned sample terms
GEN=yes            # include generated terms
RAW=no
KEEP=no
MAXW=30            # truncation width for the wide columns
AGDA_TIMEOUT=900

usage() {
  cat <<'EOF'
compare.sh -- differential testing of the ARM, IR and Rust backends

USAGE
  tools/compare.sh [options]

OPTIONS
  -n, --count N        number of generated terms          (default 6)
  -d, --depth D        height bound on generated terms    (default 5)
                       D=4 -> 9 closed terms, D=5 -> 108, D=6 -> 12237
  -s, --seed S         seed for the generator's LCG       (default 42)
      --no-corpus      omit the six pinned sample terms
      --only-corpus    omit the generated terms
      --broken[=WHICH] swap in a deliberately mutated backend.
                       WHICH is arm, rust or both         (default rust)
      --syntactic      compare RUST/SRC on the nose instead of up to
                       alpha.  Shows the raw binder-level difference.
      --arm-fuel N     AArch64 machine steps              (default 500)
      --arm-depth N    closure decode depth               (default 8)
      --ref-fuel N     IR abstract machine fuel           (default 64)
      --rust-fuel N    Rust big-step evaluator fuel       (default 40)
  -w, --width N        truncate wide columns to N chars   (default 30)
      --raw            print the raw semicolon-separated rows
      --keep           keep the generated Agda file and say where
  -h, --help           this

COLUMNS
  TERM       the term's name (gN for a generated one)
  SOURCE     the term itself, rendered as Rust source
  REF        runP (the IR abstract machine) -- the reference answer
  ARM        answerT (real AArch64, decoded) -- the ARM answer
  ARM/REF    do ARM and REF agree?  Both are `Maybe Val`, compared
             DIRECTLY.  A DIFFER here is a genuine backend divergence.
  RUST       valOf (evalRust (compileRust t)) -- the Rust answer
  RUST-EXP   compileRust (evalV t) -- what the SOURCE semantics says
             the Rust answer should be
  RUST/SRC   do those agree, UP TO A RENAMING OF BINDERS?
               AGREE   syntactically equal
               ALPHA   equal up to binder levels only -- the residue
                       `Relational/Square.squareDet` licenses, NOT a bug
               DIFFER  not even alpha-equivalent: a real divergence
             With --syntactic, ALPHA collapses back into DIFFER.

EXIT STATUS
  0  every column agreed
  1  at least one DIFFER
  2  the harness itself failed (agda error, missing file, ...)
EOF
}

# ------------------------------------------------------------------ #
# args
# ------------------------------------------------------------------ #
while [ $# -gt 0 ]; do
  case "$1" in
    -n|--count)      COUNT="$2"; shift 2 ;;
    -d|--depth)      DEPTH="$2"; shift 2 ;;
    -s|--seed)       SEED="$2"; shift 2 ;;
    --no-corpus)     CORPUS=no; shift ;;
    --only-corpus)   GEN=no; shift ;;
    --broken)        BAD_RUST=true; shift ;;
    --broken=arm)    BAD_ARM=true; shift ;;
    --broken=rust)   BAD_RUST=true; shift ;;
    --broken=both)   BAD_ARM=true; BAD_RUST=true; shift ;;
    --syntactic)     SYNTACTIC=true; shift ;;
    --arm-fuel)      ARM_FUEL="$2"; shift 2 ;;
    --arm-depth)     ARM_DEPTH="$2"; shift 2 ;;
    --ref-fuel)      REF_FUEL="$2"; shift 2 ;;
    --rust-fuel)     RUST_FUEL="$2"; shift 2 ;;
    -w|--width)      MAXW="$2"; shift 2 ;;
    --raw)           RAW=yes; shift ;;
    --keep)          KEEP=yes; shift ;;
    -h|--help)       usage; exit 0 ;;
    *) echo "compare.sh: unknown option '$1' (try --help)" >&2; exit 2 ;;
  esac
done

command -v agda >/dev/null 2>&1 || { echo "compare.sh: no 'agda' on PATH" >&2; exit 2; }
[ -f "$SRC/grammar.agda-lib" ] || { echo "compare.sh: cannot find $SRC/grammar.agda-lib" >&2; exit 2; }

# which corpus expression?
if   [ "$CORPUS" = yes ] && [ "$GEN" = yes ]; then
  TERMS="T.suite $DEPTH $COUNT $SEED"
elif [ "$CORPUS" = yes ]; then
  TERMS="T.corpus"
elif [ "$GEN" = yes ]; then
  TERMS="T.drawn $DEPTH $COUNT $SEED"
else
  echo "compare.sh: --no-corpus and --only-corpus together select nothing" >&2
  exit 2
fi

# ------------------------------------------------------------------ #
# the work directory: a scratch Agda project that depends on `grammar`
# ------------------------------------------------------------------ #
WORK="$(mktemp -d "${TMPDIR:-/tmp}/compare-sh.XXXXXX")"
cleanup() { [ "$KEEP" = yes ] || rm -rf "$WORK"; }
trap cleanup EXIT

cat > "$WORK/probe.agda-lib" <<EOF
name: compare-probe
include: .
depend: grammar cubical cubical-categorical-logic
flags: --cubical --guardedness --guarded --rewriting
EOF

# a libraries file that additionally registers the project itself
if [ -f "$HOME/.agda/libraries" ]; then cat "$HOME/.agda/libraries" > "$WORK/libraries"; else : > "$WORK/libraries"; fi
echo "$SRC/grammar.agda-lib" >> "$WORK/libraries"

SENTINEL="@@COMPARE_SH_SENTINEL@@"

cat > "$WORK/CompareRun.agda" <<EOF
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module CompareRun where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Cubical.Data.Bool using (true; false)

import Compile.Suite.Compare as C
import Compile.Suite.Terms   as T

out : String
out = C.report $ARM_FUEL $ARM_DEPTH $REF_FUEL $RUST_FUEL $BAD_ARM $BAD_RUST
        $SYNTACTIC ($TERMS)

_ : out ≡ "$SENTINEL"
_ = refl
EOF

[ "$KEEP" = yes ] && echo "compare.sh: generated driver kept at $WORK/CompareRun.agda" >&2

# ------------------------------------------------------------------ #
# run
# ------------------------------------------------------------------ #
LOG="$WORK/agda.log"
( cd "$WORK" && timeout "$AGDA_TIMEOUT" agda --no-libraries \
    --library-file="$WORK/libraries" CompareRun.agda ) > "$LOG" 2>&1
RC=$?

if [ $RC -eq 124 ]; then
  echo "compare.sh: agda timed out after ${AGDA_TIMEOUT}s. Try a smaller --depth/--count." >&2
  exit 2
fi

# the report is the line immediately after `The terms` in the
# UnequalTerms error.  Anything else is a real failure.
REPORT="$(awk '/^The terms$/ { getline; print; exit }' "$LOG")"

if [ -z "$REPORT" ]; then
  echo "compare.sh: could not extract a report; agda said:" >&2
  cat "$LOG" >&2
  exit 2
fi

# strip the leading indent and the surrounding quotes, then unescape
ROWS="$(printf '%s\n' "$REPORT" \
  | awk '{ sub(/^[ \t]+/, ""); sub(/^"/, ""); sub(/"$/, "");
           gsub(/\\n/, "\n"); gsub(/\\"/, "\""); gsub(/\\\\/, "\\");
           printf "%s", $0 }')"

if [ "$RAW" = yes ]; then
  printf '%s\n' "$ROWS"
  exit 0
fi

# ------------------------------------------------------------------ #
# the table
# ------------------------------------------------------------------ #
if   [ "$BAD_ARM" = true ] && [ "$BAD_RUST" = true ]; then MODE="BROKEN-ARM+RUST"
elif [ "$BAD_ARM" = true ];                           then MODE="BROKEN-ARM"
elif [ "$BAD_RUST" = true ];                          then MODE="BROKEN-RUST"
else                                                       MODE="clean"
fi

echo "backend comparison  --  mode: $MODE"
echo "  arm-fuel=$ARM_FUEL arm-depth=$ARM_DEPTH ref-fuel=$REF_FUEL rust-fuel=$RUST_FUEL"
echo "  corpus=$CORPUS  generated=$GEN (depth=$DEPTH count=$COUNT seed=$SEED)"
if [ "$SYNTACTIC" = true ]; then
  echo "  RUST/SRC: SYNTACTIC equality (alpha-equivalent answers read as DIFFER)"
else
  echo "  RUST/SRC: up to alpha (Relational/Square.squareDet); ALPHA = renamed binders only"
fi
echo

printf '%s\n' "$ROWS" | awk -F';' -v W="$MAXW" '
  function trunc(s) {
    if (length(s) > W) return substr(s, 1, W-1) "~";
    return s;
  }
  BEGIN {
    printf "%-9s  %-*s  %-10s %-10s %-7s  %-*s %-*s %-8s\n",
           "TERM", W, "SOURCE", "REF", "ARM", "ARM/REF",
           W, "RUST", W, "RUST-EXP", "RUST/SRC";
    n = 9 + 2 + W + 2 + 10 + 1 + 10 + 1 + 7 + 2 + W + 1 + W + 1 + 8;
    for (i = 0; i < n; i++) printf "-"; printf "\n";
  }
  NF >= 8 {
    printf "%-9s  %-*s  %-10s %-10s %-7s  %-*s %-*s %-8s\n",
           $1, W, trunc($2), trunc($3), trunc($4), $5,
           W, trunc($6), W, trunc($7), $8;
    if ($5 == "DIFFER") armbad++;
    if ($8 == "DIFFER") rustbad++;
    if ($8 == "ALPHA")  rustalpha++;
    rows++;
  }
  END {
    printf "\n%d term(s).  ARM/REF: %d DIFFER.  RUST/SRC: %d DIFFER",
           rows, armbad+0, rustbad+0;
    if (rustalpha+0 > 0) printf ", %d ALPHA (binder renaming only)", rustalpha;
    printf ".\n";
    if (armbad+rustbad > 0) exit 1;
  }
'
exit $?
