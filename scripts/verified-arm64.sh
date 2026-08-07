#!/usr/bin/env bash
#
# verified-arm64.sh -- typecheck the Agda pipeline, emit AArch64, assemble,
# run on Apple Silicon, and check the result against the proved prediction.
#
# READ scripts/TRUST.md BEFORE BELIEVING ANYTHING THIS PRINTS.
# The proof covers step 1. Steps 2-5 are unverified or trusted, and the
# script says so as it goes.
#
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$REPO/src"
AGDA_FILE="Compile/LinToISA/ARM64.agda"
OUT="${TMPDIR:-/tmp}/verified-arm64"
mkdir -p "$OUT"

say() { printf '\n\033[1m== %s\033[0m\n' "$*"; }
ok()  { printf '   \033[32mok\033[0m  %s\n' "$*"; }
warn(){ printf '   \033[33m!!\033[0m  %s\n' "$*"; }

# ---------------------------------------------------------------------
say "1/5  VERIFIED STEP -- typecheck the compiler and its theorem"
# Everything that is actually proved is proved here. If this fails,
# nothing downstream means anything.
# ---------------------------------------------------------------------
cd "$SRC"
if agda --no-libraries --library-file="$HOME/.agda/libraries" "$AGDA_FILE" >"$OUT/agda.log" 2>&1; then
  ok "$AGDA_FILE typechecks"
  ok "Codegen.runU : exec (compileU u) [] Eq.≡ layout u   -- PROVED"
  ok "the emitted string is pinned by refl at the terms tested"
else
  printf '   \033[31mFAILED\033[0m -- see %s\n' "$OUT/agda.log"; tail -20 "$OUT/agda.log"; exit 1
fi

# ---------------------------------------------------------------------
say "2/5  UNVERIFIED STEP -- extract the pinned assembly literal"
# The literal is extracted mechanically from the source, NOT retyped, so
# it cannot drift from what step 1 proved equal to `emitARM (compileU ugap)`.
# But `emitARM` itself has no theorem: see TRUST.md gap (A).
# ---------------------------------------------------------------------
LIT=$(grep -m1 '≡ "        .section __TEXT' "$SRC/$AGDA_FILE" \
      | sed -e 's/^[[:space:]]*≡ "//' -e 's/"$//')
if [ -z "$LIT" ]; then echo "   could not find the pinned literal"; exit 1; fi
printf '%b' "$LIT" > "$OUT/gap.s"
ok "extracted $(wc -l < "$OUT/gap.s" | tr -d ' ') lines to $OUT/gap.s"
warn "emitARM is UNVERIFIED -- no theorem relates this string to the heap"

# ---------------------------------------------------------------------
say "3/5  TRUSTED STEP -- assemble and link (clang, Mach-O linker)"
# ---------------------------------------------------------------------
clang -o "$OUT/gap" "$OUT/gap.s"
ok "$(file -b "$OUT/gap" | cut -d, -f1)"
warn "clang, the linker and the loader are in the trusted base"

# ---------------------------------------------------------------------
say "4/5  RUN on this machine"
# ---------------------------------------------------------------------
set +e; "$OUT/gap"; ACTUAL=$?; set -e
ok "exit status = $ACTUAL"

# ---------------------------------------------------------------------
say "5/5  CHECK against the proved prediction"
# `live ugap ≡ 2` is proved in ARM64.agda by refl. Every stored value is
# v1 = 1, so the accumulator should equal the number of live positions.
# ---------------------------------------------------------------------
EXPECTED=2
if [ "$ACTUAL" -eq "$EXPECTED" ]; then
  ok "matches live(true,false,true) = $EXPECTED"
else
  printf '   \033[31mMISMATCH\033[0m expected %s, got %s\n' "$EXPECTED" "$ACTUAL"; exit 1
fi

say "SUMMARY"
cat <<'EOF'
   PROVED    compileU u produces an instruction list whose execution,
             under the Agda machine model, is exactly `layout u`.
   TESTED    the printed AArch64 text, at the terms with refl tests.
   TRUSTED   clang, the linker, the loader, the silicon, Agda itself.
   UNMODELLED  AArch64 semantics -- nothing in Agda knows what `str` does.

   So: the exit status agreeing with `live u` is EVIDENCE the printer and
   the hardware agree with the model. It is not a proof that they do.
   See scripts/TRUST.md.
EOF
