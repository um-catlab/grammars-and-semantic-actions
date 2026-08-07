#!/usr/bin/env bash
#
# compile-lambda.sh -- compile a lambda-calculus program to a native
# Apple Silicon executable, through the Agda pipeline.
#
#   ./scripts/compile-lambda.sh 'x y'
#   ./scripts/compile-lambda.sh 'λx. x λy. y'
#
# THE LANGUAGE is `Lambda.Parse.Tok`: a four-token alphabet, the
# variables `x` and `y` and the binders `λx.` and `λy.`. Anything else
# is a LEXICAL error -- `λz. z` is rejected by the lexer, not the parser.
#
# READ scripts/TRUST.md. One link in this chain is proved; the rest is
# tested or trusted, and the script labels each step as it goes.
#
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$REPO/src"
MOD="$SRC/Chain/Run.agda"
OUT="${TMPDIR:-/tmp}/lambda-build"
mkdir -p "$OUT"

INPUT="${1:-}"
if [ -z "$INPUT" ]; then
  echo "usage: $0 '<lambda program>'   e.g.  $0 'x y'"; exit 2
fi

say()  { printf '\n\033[1m== %s\033[0m\n' "$*"; }
ok()   { printf '   \033[32mok\033[0m  %s\n' "$*"; }
warn() { printf '   \033[33m!!\033[0m  %s\n' "$*"; }
bad()  { printf '   \033[31mno\033[0m  %s\n' "$*"; }

# normalise an Agda expression against Chain.Run and print the result.
# Agda's interaction mode returns an Elisp string wrapping an Agda string
# literal, so the payload is escaped twice; python undoes both levels.
agda_eval() {
  printf 'IOTCM "%s" None Direct (Cmd_compute_toplevel DefaultCompute "%s")\n' "$MOD" "$1" \
  | (cd "$SRC" && agda --interaction --no-libraries --library-file="$HOME/.agda/libraries" 2>/dev/null) \
  | python3 -c '
import sys, re, ast
Q = chr(34)                               # avoids nesting quotes inside the shell
d = sys.stdin.read()
m = re.search(r"\*Normal Form\*" + Q + r" (" + Q + r".*?" + Q + r") nil", d, re.S)
if not m: sys.exit(1)
v = ast.literal_eval(m.group(1))          # un-escape the Elisp layer
try:    v = ast.literal_eval(v)           # ... and the Agda string literal, if it is one
except Exception: pass
sys.stdout.write(v if isinstance(v, str) else str(v))
'
}

echo "input: $INPUT"

# ---------------------------------------------------------------------
say "1/6  typecheck the pipeline            [VERIFIED]"
# ---------------------------------------------------------------------
if (cd "$SRC" && agda --no-libraries --library-file="$HOME/.agda/libraries" Chain/Run.agda) >"$OUT/agda.log" 2>&1; then
  ok "Chain.Run typechecks (so does everything it imports)"
  ok "Codegen.runU : exec (compileU u) [] Eq.≡ layout u   -- PROVED"
else
  bad "typecheck failed"; tail -20 "$OUT/agda.log"; exit 1
fi

# ---------------------------------------------------------------------
say "2/6  lex the program                   [VERIFIED LEXER]"
# ---------------------------------------------------------------------
LEXOK=$(agda_eval "lexOK \\\"$INPUT\\\"")
if [ "$LEXOK" = "true" ]; then
  ok "lexes"
else
  bad "LEXICAL ERROR -- the alphabet is only x, y, λx., λy."
  echo "      (this is the lexer's error branch, a real refutation, not a crash)"
  exit 1
fi

NTOK=$(agda_eval "tokCount \\\"$INPUT\\\"")
ok "$NTOK tokens"

# ---------------------------------------------------------------------
say "3/6  emit AArch64                      [UNVERIFIED PRINTER]"
# ---------------------------------------------------------------------
agda_eval "asmFor \\\"$INPUT\\\"" > "$OUT/out.s"
ok "wrote $(wc -l < "$OUT/out.s" | tr -d ' ') lines to $OUT/out.s"
warn "emitARM has no theorem -- see TRUST.md gap (A)"

# ---------------------------------------------------------------------
say "4/6  assemble and link                 [TRUSTED: clang]"
# ---------------------------------------------------------------------
clang -o "$OUT/prog" "$OUT/out.s"
ok "$(file -b "$OUT/prog" | cut -d, -f1)"

# ---------------------------------------------------------------------
say "5/6  run                               [TRUSTED: hardware]"
# ---------------------------------------------------------------------
set +e; "$OUT/prog"; ACTUAL=$?; set -e
ok "exit status = $ACTUAL"

# ---------------------------------------------------------------------
say "6/6  check against the prediction"
# ---------------------------------------------------------------------
if [ "$ACTUAL" -eq "$NTOK" ]; then
  ok "matches the token count ($NTOK)"
else
  bad "MISMATCH: expected $NTOK, got $ACTUAL"; exit 1
fi

say "RESULT"
printf '   executable : %s\n   assembly   : %s\n   exit code  : %s\n' "$OUT/prog" "$OUT/out.s" "$ACTUAL"
cat <<'EOF'

   WHAT THE EXIT CODE MEANS: the number of TOKENS, i.e. the shape of the
   program -- not what it computes. Every ACCEPTED program here is
   CLOSED, and `Simulation.noBlindBackend` proves the heap backend
   cannot see the term at all, so a term-derived observable is not
   available from this backend. Swapping it in is `Chain.Run`'s §2 and
   needs the term-directed backend. See scripts/TRUST.md.
EOF
