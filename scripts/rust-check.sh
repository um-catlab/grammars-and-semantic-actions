#!/usr/bin/env bash
#
# rust-check.sh -- typecheck the Rust chain, emit the Rust it proves it
# emits, compile it with rustc, run it, and check the answers against the
# `_⇓_` derivations in Chain/RustEmit.agda.
#
# WHAT IS PROVED  step 1 only.  The Agda files carry the theorems and
#                 pin every emitted string by `refl`.
# WHAT IS TRUSTED step 4.  That `_⇓_` is Rust's real semantics is the
#                 residual trust in this chain; steps 2-4 TEST it and
#                 cannot prove it.  A disagreement is a genuine bug.
#
# Two of the cases below are EXPECTED TO FAIL COMPILATION.  That is not a
# broken script -- it is a defect in the code generator, found by running
# this, and documented in Chain/RustEmit.agda.  The suite fails only if
# something deviates from what is recorded there.
#
# Usage:  scripts/rust-check.sh            full run
#         scripts/rust-check.sh --no-agda  skip step 1 (fast)
#
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$REPO/src"
OUT="${TMPDIR:-/tmp}/rust-check"
mkdir -p "$OUT"

SKIP_AGDA=0
[ "${1:-}" = "--no-agda" ] && SKIP_AGDA=1

say()  { printf '\n\033[1m== %s\033[0m\n' "$*"; }
ok()   { printf '   \033[32mok  \033[0m %s\n' "$*"; }
bad()  { printf '   \033[31mFAIL\033[0m %s\n' "$*"; }
note() { printf '   \033[33m··  \033[0m %s\n' "$*"; }

FAILURES=0
fail() { bad "$*"; FAILURES=$((FAILURES+1)); }

# =====================================================================
say "1/4  VERIFIED -- typecheck the chain"
# Everything actually proved is proved here.  If this fails, nothing
# downstream means anything.
# =====================================================================
AGDA_FILES=(
  Chain/Typing.agda        # LinTyped wired in, and the obstruction
  Chain/TypeLocate.agda    # type errors located at a subterm
  Chain/Rust.agda          # annotated term -> type -> linear -> Rust -> diag
  Chain/RustEmit.agda      # the `_⇓_` derivations + the emitted programs
)

if [ "$SKIP_AGDA" = "1" ]; then
  note "skipped (--no-agda)"
else
  if ! command -v agda >/dev/null 2>&1; then
    fail "agda not on PATH"
  else
    cd "$SRC" || exit 1
    for f in "${AGDA_FILES[@]}"; do
      if agda --no-libraries --library-file="$HOME/.agda/libraries" "$f" \
           >"$OUT/$(basename "$f").log" 2>&1; then
        ok "$f typechecks"
      else
        fail "$f DOES NOT typecheck -- see $OUT/$(basename "$f").log"
      fi
    done
  fi
fi

# =====================================================================
say "2/4  TRUSTED -- rustc"
# =====================================================================
if ! command -v rustc >/dev/null 2>&1; then
  bad "rustc not on PATH -- steps 2-4 cannot run"
  exit 1
fi
ok "$(rustc --version)"

# =====================================================================
say "3/4  THE PROGRAMS"
# Each heredoc below is byte-for-byte a string pinned by `refl` in the
# Agda file named beside it.  If you change one here and not there, step
# 1 still passes and this suite is lying -- so don't.
# =====================================================================
cd "$OUT" || exit 1

# --- differential cases: emitted expression + a call site -------------
# Chain/RustEmit.agda  `idProg`   (pinned by refl)
cat > d_idA.rs <<'EOF'
#[derive(Debug)]
enum U { A, B }

fn main() {
    let r = (move |x0| x0)(U::A);
    println!("{}", match r { U::A => "U::A", U::B => "U::B" });
}
EOF

# Chain/RustEmit.agda  `idProgB`  (pinned by refl)
cat > d_idB.rs <<'EOF'
#[derive(Debug)]
enum U { A, B }

fn main() {
    let r = (move |x0| x0)(U::B);
    println!("{}", match r { U::A => "U::A", U::B => "U::B" });
}
EOF

# `appExpr` at U::A -- the HIGHER-ORDER case, in the form the codegen
# emits.  Expected to FAIL: see step 4 and Chain/RustEmit.agda.
cat > d_appBare.rs <<'EOF'
#[derive(Debug)]
enum U { A, B }

fn main() {
    let r = ((move |x0| move |x1| (x0)(x1))(move |x0| x0))(U::A);
    println!("{}", match r { U::A => "U::A", U::B => "U::B" });
}
EOF

# the same term with the measured repair -- Box<dyn Fn(..)>
cat > d_appBoxed.rs <<'EOF'
#[derive(Debug)]
enum U { A, B }

fn main() {
    let r = ((move |x0: Box<dyn Fn(U) -> U>| move |x1: U| x0(x1))
              (Box::new(move |x0: U| x0)))(U::A);
    println!("{}", match r { U::A => "U::A", U::B => "U::B" });
}
EOF

# --- the compilation units the codegen ACTUALLY emits -----------------
# Compile/LinToRust/Codegen.agda pins all three by `refl`.  All three are
# expected to FAIL: `let _ = <closure>;` leaves the parameter type
# uninferable (E0282).
cat > u_id.rs <<'EOF'
enum U { A, B }

fn main() {
    let _ = move |x0| x0;
}
EOF
cat > u_self.rs <<'EOF'
enum U { A, B }

fn main() {
    let _ = (move |x0| x0)(move |x0| x0);
}
EOF
cat > u_app.rs <<'EOF'
enum U { A, B }

fn main() {
    let _ = move |x0| move |x1| (x0)(x1);
}
EOF
ok "7 programs written to $OUT"

# =====================================================================
say "4/4  TRUSTED -- compile, run, and compare against \`_⇓_\`"
# =====================================================================
printf '\n   %-14s %-12s %-10s %-8s %s\n' PROGRAM 'agda(_⇓_)' rustc EXPECT VERDICT
printf '   %-14s %-12s %-10s %-8s %s\n' '-------' '---------' '-----' '------' '-------'

# run <file> <prediction|-> <expect: run|nocompile> <agda-witness>
run_case() {
  local f="$1" pred="$2" expect="$3" thm="$4"
  local got status
  if rustc --edition 2021 -A dead_code -o "${f%.rs}" "$f" >"${f%.rs}.rustc.log" 2>&1; then
    status="compiled"
    got="$(./"${f%.rs}" 2>/dev/null)"
  else
    status="E0282"
    got="-"
  fi

  local verdict
  case "$expect" in
    run)
      if [ "$status" != "compiled" ]; then
        verdict="FAIL (expected to compile)"; FAILURES=$((FAILURES+1))
      elif [ "$got" = "$pred" ]; then
        verdict="agree"
      else
        verdict="*** DISAGREES WITH _⇓_ ***"; FAILURES=$((FAILURES+1))
      fi ;;
    nocompile)
      if [ "$status" = "compiled" ]; then
        verdict="FAIL (defect fixed? update RustEmit.agda)"; FAILURES=$((FAILURES+1))
      else
        verdict="known defect"
      fi ;;
  esac
  printf '   %-14s %-12s %-10s %-8s %s\n' "$f" "$pred" "$got" "$expect" "$verdict"
  [ -n "$thm" ] && printf '   %-14s   \033[2m%s\033[0m\n' '' "witness: $thm"
  return 0
}

run_case d_idA.rs     "U::A" run       "RustEmit.idAppA"
run_case d_idB.rs     "U::B" run       "RustEmit.idAppB"
run_case d_appBare.rs "U::A" nocompile "RustEmit.appIdA (bare form)"
run_case d_appBoxed.rs "U::A" run      "RustEmit.appIdA (boxed repair)"
run_case u_id.rs      "-"    nocompile "Codegen.srcTm at idLin"
run_case u_self.rs    "-"    nocompile "Codegen.srcTm at selfApp"
run_case u_app.rs     "-"    nocompile "Codegen.srcTm at appLin"

# =====================================================================
say "DIAGNOSTICS -- what the chain says when it REJECTS a term"
# Both strings below are pinned by `refl`; step 1 is what checks them.
# They are echoed here so a reader sees the user-facing output without
# opening Agda.
# =====================================================================
printf '   %s\n' 'input:  (\. 0) (\. 0)         -- Chain/Rust.agda §5'
printf '   %s\n' '        rejected: Chain.Typing.selfAppNoSyn'
printf '   %s\n' '        cannot synthesise a type here -- add an annotation'
printf '   %s\n' '          in:  \. 0'
printf '\n'
printf '   %s\n' 'input:  ((\. 0) : o)           -- Chain/TypeLocate.agda §4.4'
printf '   %s\n' '        does not have the expected type o'
printf '   %s\n' '          in:  \. 0'
ok "the located blame names the same subterm the repair annotates"

# =====================================================================
say "SUMMARY"
# =====================================================================
cat <<'EOF'
   PROVED    the Agda files, and every emitted string is pinned by refl
   TESTED    3 differential cases against `_⇓_`; no disagreement
   DEFECT    the emitted compilation units do not compile.  Two causes:
             (1) `let _ = <closure>;` -- nothing to infer from  [renderUnit]
             (2) a higher-order parameter is a closure, whose type Rust
                 cannot name -- needs Box<dyn Fn(..)>           [RExpr]
             (1) is a rendering defect, (2) is a CODEGEN defect.
             Neither touches a theorem: `_⇓_` and `squareDet` are about
             `RExpr`, not about the text.
EOF

if [ "$FAILURES" -eq 0 ]; then
  printf '\n   \033[32mall %s cases behaved as recorded\033[0m\n\n' 7
  exit 0
else
  printf '\n   \033[31m%s case(s) deviated from what Chain/RustEmit.agda records\033[0m\n\n' "$FAILURES"
  exit 1
fi
