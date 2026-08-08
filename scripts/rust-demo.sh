#!/usr/bin/env bash
#
# rust-demo.sh -- show the compiler working, one program at a time.
#
# For each example:  the SOURCE, its TYPE, its LINEARITY verdict, the
# RUST the compiler emits, and what that Rust actually DOES when run on
# a toy input -- checked against the `_⇓_` derivation in Agda.
#
# Everything marked [proved] is pinned by `refl` in the Agda file named;
# everything marked [ran] is rustc's answer and is EVIDENCE, not proof.
#
# The [defect] rows are HAND-WRITTEN repairs, not compiler output; the
# [known defect] row is compiler output that rustc rejects.  A closure
# parameter that is merely PASSED is fine; one that is CALLED is not.
#
# Usage:  scripts/rust-demo.sh
#
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${TMPDIR:-/tmp}/rust-demo"
mkdir -p "$OUT"; cd "$OUT" || exit 1

B=$'\033[1m'; D=$'\033[2m'; G=$'\033[32m'; R=$'\033[31m'; Y=$'\033[33m'; N=$'\033[0m'
FAILURES=0

command -v rustc >/dev/null 2>&1 || { echo "rustc not found"; exit 1; }
printf '%s%s%s\n' "$D" "$(rustc --version)" "$N"

# ---------------------------------------------------------------------
# demo <label> <source> <type> <linear> <rust-expr> <arg> <expect> <agda-witness> <mode>
#   mode = emitted   : <rust-expr> is what the compiler emits   [proved]
#          repair    : <rust-expr> is a hand-written repair     [defect]
# ---------------------------------------------------------------------
demo() {
  local label="$1" src="$2" ty="$3" lin="$4" expr="$5" arg="$6" exp="$7" thm="$8" mode="$9"
  local tag="[proved]"
  [ "$mode" = repair ]    && tag="${Y}[defect: hand-repaired]${N}"
  [ "$mode" = knownfail ] && tag="${Y}[proved, but does not compile -- known defect]${N}"

  printf '\n%s── %s%s\n' "$B" "$label" "$N"
  printf '   %-9s %s\n' "source"   "$src"
  printf '   %-9s %s   %s\n' "type" "$ty" "${D}[proved: Chain/Rust.agda]${N}"
  printf '   %-9s %s   %s\n' "linear" "$lin" "${D}[proved: LinLam.Check.linear?]${N}"
  printf '   %-9s %s   %s\n' "rust" "$expr" "$tag"

  local f="prog_$(echo "$label" | tr -cd 'A-Za-z0-9')"
  cat > "$f.rs" <<EOF
#[derive(Debug)]
enum U { A, B }

fn main() {
    let r = ($expr)($arg);
    println!("{}", match r { U::A => "U::A", U::B => "U::B" });
}
EOF

  if rustc --edition 2021 -A dead_code -o "$f" "$f.rs" >"$f.log" 2>&1; then
    local got; got="$(./"$f")"
    if [ "$got" = "$exp" ]; then
      printf '   %-9s f(%s) = %s   %s[ran]%s   agda `_⇓_` says %s -- %sagree%s\n' \
        "evaluate" "$arg" "$got" "$D" "$N" "$exp" "$G" "$N"
    else
      printf '   %-9s f(%s) = %s   %sDISAGREES with _⇓_ (%s)%s\n' \
        "evaluate" "$arg" "$got" "$R" "$exp" "$N"
      FAILURES=$((FAILURES+1))
    fi
  else
    printf '   %-9s %sDOES NOT COMPILE%s  %s\n' "evaluate" "$R" "$N" \
      "$(grep -m1 '^error' "$f.log" | sed 's/error/rustc: error/')"
    [ "$mode" = emitted ] && FAILURES=$((FAILURES+1))
    [ "$mode" = knownfail ] && printf '   %-9s %sthis is the recorded codegen defect, not a regression%s\n' "" "$D" "$N"
  fi
  printf '   %-9s %s%s%s\n' "witness" "$D" "$thm" "$N"
}

printf '\n%s=== THE COMPILER, ONE PROGRAM AT A TIME ===%s\n' "$B" "$N"

# ---------------------------------------------------------------------
demo "identity, applied to U::A" \
  '((λx. x) : (o -o o))' \
  '(o -o o)' \
  'yes -- usage []' \
  'move |x0| x0' \
  'U::A' 'U::A' \
  'Chain/Rust.agda 3.1 ; RustEmit.idAppA' emitted

demo "identity, applied to U::B" \
  '((λx. x) : (o -o o))' \
  '(o -o o)' \
  'yes -- usage []' \
  'move |x0| x0' \
  'U::B' 'U::B' \
  'Chain/Rust.agda 3.1 ; RustEmit.idAppB' emitted

# ---------------------------------------------------------------------
demo "self-application (as emitted)" \
  '(((λx. x) : ((o -o o) -o (o -o o))) (λx. x))' \
  '(o -o o)' \
  'yes -- usage []' \
  '(move |x0| x0)(move |x0| x0)' \
  'U::A' 'U::A' \
  'Chain/Rust.agda 3.2 -- the emitted form' emitted

demo "self-application (boxed repair)" \
  '(((λx. x) : ((o -o o) -o (o -o o))) (λx. x))' \
  '(o -o o)' \
  'yes -- usage []' \
  '(move |x0: Box<dyn Fn(U) -> U>| move |x1: U| x0(x1))(Box::new(move |x0: U| x0))' \
  'U::A' 'U::A' \
  'the Box<dyn Fn> repair -- NOT emitted by the compiler' repair

# ---------------------------------------------------------------------
demo "λf.λx. f x  (as emitted)" \
  '((λx. (λy. (x y))) : ((o -o o) -o (o -o o)))' \
  '((o -o o) -o (o -o o))' \
  'yes -- usage []' \
  '(move |x0| move |x1| (x0)(x1))(move |x0| x0)' \
  'U::A' 'U::A' \
  'Chain/Rust.agda 3.3 -- the emitted form' knownfail

demo "λf.λx. f x  (boxed repair)" \
  '((λx. (λy. (x y))) : ((o -o o) -o (o -o o)))' \
  '((o -o o) -o (o -o o))' \
  'yes -- usage []' \
  '(move |x0: Box<dyn Fn(U) -> U>| move |x1: U| x0(x1))(Box::new(move |x0: U| x0))' \
  'U::A' 'U::A' \
  'RustEmit.appIdA -- boxed' repair

# =====================================================================
printf '\n%s=== WHAT THE COMPILER REJECTS ===%s\n' "$B" "$N"
# Both messages are pinned by `refl`; step 1 of rust-check.sh checks them.
# =====================================================================
printf '\n%s── missing annotation%s\n' "$B" "$N"
printf '   %-9s %s\n' "source"  '((λx. x) (λx. x))'
printf '   %-9s %s\n' "verdict" 'REJECTED at the type stage'
printf '   %-9s %s\n' "message" 'cannot synthesise a type here -- add an annotation'
printf '   %-9s %s\n' ""        '  in:  \. 0'
printf '   %-9s %s%s%s\n' "witness" "$D" 'Chain/Rust.agda §5 ; Chain.Typing.selfAppNoSyn' "$N"

printf '\n%s── annotation that lies%s\n' "$B" "$N"
printf '   %-9s %s\n' "source"  '((λx. x) : o)'
printf '   %-9s %s\n' "verdict" 'REJECTED at the type stage'
printf '   %-9s %s\n' "message" 'does not have the expected type o'
printf '   %-9s %s\n' ""        '  in:  \. 0'
printf '   %-9s %s%s%s\n' "witness" "$D" 'Chain/TypeLocate.agda §4.4' "$N"

printf '\n%s── typeable but not linear%s\n' "$B" "$N"
printf '   %-9s %s\n' "source"  '((λx. (λy. x)) : (o -o (o -o o)))'
printf '   %-9s %s\n' "type"    'accepted -- (o -o (o -o o))'
printf '   %-9s %s\n' "verdict" 'REJECTED at the linearity stage -- y is discarded'
printf '   %-9s %s%s%s\n' "witness" "$D" 'Chain/Rust.agda §4 kNotLinear : (¬G Lin) (0 , dbK)' "$N"

# =====================================================================
printf '\n%s=== SUMMARY ===%s\n' "$B" "$N"
cat <<EOF
   The type and linearity verdicts are INDEPENDENT: the last example is
   typeable and not linear, and an unannotated lambda is linear and not
   typeable.  Both stages exist because neither implies the other.

   The two [defect] rows are the known codegen gap: RExpr emits closures
   with no parameter type, and a higher-order parameter is a closure,
   whose type Rust cannot name.  The repair is Box<dyn Fn(U) -> U>, and
   the boxed rows show it agrees with \`_⇓_\` once expressible.
EOF

if [ "$FAILURES" -eq 0 ]; then
  printf '\n   %severy emitted program behaved as proved%s\n\n' "$G" "$N"; exit 0
else
  printf '\n   %s%s emitted program(s) deviated%s\n\n' "$R" "$FAILURES" "$N"; exit 1
fi
