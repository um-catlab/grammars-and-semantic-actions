#!/usr/bin/env bash
#
# run-lambda.sh -- compile lambda terms with the TERM-DIRECTED backend and
# RUN them on test input, showing input -> output.
#
# Why a second script. `compile-lambda.sh` uses the HEAP backend, whose
# executable exits with a cell count and ignores the term entirely --
# `Simulation.noBlindBackend` proves it cannot see the term, so two
# different programs compile to the same binary. Nothing there can be
# "run on an input".
#
# This script uses `Compile.LinToRust.Codegen`, which is TERM-DIRECTED:
#
#     compileRust : {u : Usage} → Tm u → RExpr
#
# so different terms give different code, and the emitted closures can be
# applied to actual values.
#
# THE AGREEMENT DEMONSTRATED HERE IS TESTED, not proved:
# `LinToRust.Codegen.Simulates` states the square and it is not yet
# discharged.
#
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$REPO/src"
MOD="$SRC/Compile/LinToRust/Codegen.agda"
OUT="${TMPDIR:-/tmp}/lambda-run"
mkdir -p "$OUT"

say()  { printf '\n\033[1m== %s\033[0m\n' "$*"; }
ok()   { printf '   \033[32mok\033[0m  %s\n' "$*"; }
warn() { printf '   \033[33m!!\033[0m  %s\n' "$*"; }

agda_eval() {
  printf 'IOTCM "%s" None Direct (Cmd_compute_toplevel DefaultCompute "%s")\n' "$MOD" "$1" \
  | (cd "$SRC" && agda --interaction --no-libraries --library-file="$HOME/.agda/libraries" 2>/dev/null) \
  | python3 -c '
import sys, re, ast
Q = chr(34)
d = sys.stdin.read()
m = re.search(r"\*Normal Form\*" + Q + r" (" + Q + r".*?" + Q + r") nil", d, re.S)
if not m: sys.exit(1)
v = ast.literal_eval(m.group(1))
try:    v = ast.literal_eval(v)
except Exception: pass
sys.stdout.write(v if isinstance(v, str) else str(v))
'
}

# ---------------------------------------------------------------------
say "1/4  typecheck the term-directed backend        [VERIFIED]"
# ---------------------------------------------------------------------
if (cd "$SRC" && agda --no-libraries --library-file="$HOME/.agda/libraries" Compile/LinToRust/Codegen.agda) >"$OUT/agda.log" 2>&1; then
  ok "Compile.LinToRust.Codegen typechecks"
  ok "usesCompile : the emitted Rust uses each live name EXACTLY ONCE -- PROVED"
  ok "⇓-det       : the target semantics is deterministic          -- PROVED"
  warn "Simulates  : the source/target square is STATED, NOT PROVED"
else
  printf '   FAILED\n'; tail -20 "$OUT/agda.log"; exit 1
fi

# ---------------------------------------------------------------------
say "2/4  emit Rust from each term                   [compiler output]"
# ---------------------------------------------------------------------
ID_SRC=$(agda_eval  'runAt exprTextTm [] L.idLin')
APP_SRC=$(agda_eval 'runAt exprTextTm [] appLin')
SELF_SRC=$(agda_eval 'runAt exprTextTm [] L.selfApp')

printf '   λx.x        ==>  %s\n' "$ID_SRC"
printf '   λf.λx. f x  ==>  %s\n' "$APP_SRC"
printf '   (λx.x)(λx.x)==>  %s\n' "$SELF_SRC"
ok "different terms give different code -- the heap backend cannot do this"

# ---------------------------------------------------------------------
say "3/4  splice into a harness and build            [TRUSTED: rustc]"
# ---------------------------------------------------------------------
# The harness is HAND-WRITTEN; only the closure expressions between the
# markers come from the compiler. The type annotations are rustc's
# E0282 requirement -- the emitted lambda calculus is untyped.
cat > "$OUT/demo.rs" <<EOF
#[derive(Debug, PartialEq, Clone, Copy)]
enum U { A, B }

fn apply1<F: Fn(U) -> U>(f: F, x: U) -> U { f(x) }
fn apply2<G: Fn(fn(U) -> U) -> H, H: Fn(U) -> U>(g: G, f: fn(U) -> U, x: U) -> U { g(f)(x) }

fn main() {
    let id_a = apply1($ID_SRC, U::A);
    let id_b = apply1($ID_SRC, U::B);
    let f: fn(U) -> U = |x| x;
    let ap_a = apply2($APP_SRC, f, U::A);

    println!("   (λx.x)        applied to A  ->  {:?}", id_a);
    println!("   (λx.x)        applied to B  ->  {:?}", id_b);
    println!("   (λf.λx. f x)  applied to id, A  ->  {:?}", ap_a);

    assert_eq!(id_a, U::A, "identity must return its argument");
    assert_eq!(id_b, U::B, "identity must return its argument");
    assert_eq!(ap_a, U::A, "application must apply");
}
EOF
rustc -O -o "$OUT/demo" "$OUT/demo.rs" 2>"$OUT/rustc.log" || { echo "   rustc failed:"; cat "$OUT/rustc.log"; exit 1; }
ok "$(file -b "$OUT/demo" | cut -d, -f1)"

# ---------------------------------------------------------------------
say "4/4  RUN ON TEST INPUT"
# ---------------------------------------------------------------------
"$OUT/demo"
ok "all assertions held"

say "WHAT THIS SHOWS"
cat <<'EOF'
   The compiled program COMPUTES: the identity term returns its argument,
   and the application term applies its argument. That is behaviour of the
   source term, which the heap backend provably cannot express.

   STATUS OF THE AGREEMENT:
     PROVED  the emitted Rust uses each live variable exactly once
             (`usesCompile`), and the target semantics is deterministic
             (`⇓-det`). rustc's borrow checker accepts the output, and
             rejects the non-linear analogue with E0382.
     TESTED  that the output agrees with the source term's meaning, at
             the inputs above.
     OPEN    `Simulates` -- the simulation square -- is stated and
             parameterised over the source relation but NOT discharged.
             `Compile/Semantics/CBV` supplies the relation;
             `Compile/Relational` is the work to close it.

   So: this is a demonstration, not a proof, and the gap is named.
EOF
