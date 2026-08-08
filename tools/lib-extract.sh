#!/usr/bin/env bash
#
# lib-extract.sh -- the ONE way this repository gets a string out of Agda.
#
# Everything in this development computes at TYPECHECK time.  So the
# harness generates a throwaway Agda project, pins the expression it
# wants against a sentinel string, runs `agda`, and reads the normal
# form Agda prints back in the resulting `UnequalTerms` error.  The
# error IS the output channel.
#
# This is `tools/compare.sh`'s mechanism, factored out so that
# run-arm.sh, run-rust.sh and run-interp.sh all use exactly one.
#
# Usage:  source lib-extract.sh ; agda_string 'R.armAsm "idLin"'
# Sets:   AGDA_OUT   the extracted string, unescaped
# Returns 0 on success, 2 if agda failed or nothing could be extracted.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$REPO_ROOT/src"
AGDA_TIMEOUT="${AGDA_TIMEOUT:-900}"

agda_string() {
  local expr="$1"
  local sentinel='@@RUN_SH_SENTINEL@@'

  command -v agda >/dev/null 2>&1 || { echo "no 'agda' on PATH" >&2; return 2; }
  [ -f "$SRC/grammar.agda-lib" ] || { echo "cannot find $SRC/grammar.agda-lib" >&2; return 2; }

  local work
  work="$(mktemp -d "${TMPDIR:-/tmp}/run-sh.XXXXXX")"

  cat > "$work/probe.agda-lib" <<'EOF'
name: run-probe
include: .
depend: grammar cubical cubical-categorical-logic
flags: --cubical --guardedness --guarded --rewriting
EOF

  if [ -f "$HOME/.agda/libraries" ]; then
    cat "$HOME/.agda/libraries" > "$work/libraries"
  else
    : > "$work/libraries"
  fi
  echo "$SRC/grammar.agda-lib" >> "$work/libraries"

  cat > "$work/RunProbe.agda" <<EOF
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module RunProbe where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import Compile.Suite.Run as R

out : String
out = $expr

_ : out ≡ "$sentinel"
_ = refl
EOF

  local log="$work/agda.log"
  ( cd "$work" && timeout "$AGDA_TIMEOUT" agda --no-libraries \
      --library-file="$work/libraries" RunProbe.agda ) > "$log" 2>&1
  local rc=$?

  if [ $rc -eq 124 ]; then
    echo "agda timed out after ${AGDA_TIMEOUT}s" >&2
    [ "${KEEP:-no}" = yes ] || rm -rf "$work"
    return 2
  fi

  # the value is the line immediately after `The terms`
  local raw
  raw="$(awk '/^The terms$/ { getline; print; exit }' "$log")"

  if [ -z "$raw" ]; then
    echo "could not extract a value; agda said:" >&2
    cat "$log" >&2
    [ "${KEEP:-no}" = yes ] || rm -rf "$work"
    return 2
  fi

  # strip indent + surrounding quotes, then unescape via python
  AGDA_OUT="$(printf '%s\n' "$raw" | python3 -c '
import sys, ast
s = sys.stdin.read().strip()
try:
    sys.stdout.write(ast.literal_eval(s))
except Exception:
    sys.stdout.write(s)
')"

  [ "${KEEP:-no}" = yes ] && echo "probe kept at $work" >&2
  [ "${KEEP:-no}" = yes ] || rm -rf "$work"
  return 0
}

# a name is valid iff the driver knows it; `?` is the driver's answer
# for an unknown one (Compile/Suite/Run.agda §3)
check_known() {
  local name="$1"
  agda_string "R.armExit \"$name\"" || return 2
  if [ "$AGDA_OUT" = "?" ]; then
    echo "unknown term '$name'." >&2
    echo "known terms:" >&2
    agda_string 'R.names' && printf '%s\n' "$AGDA_OUT" | sed 's/^/  /' >&2
    return 2
  fi
  return 0
}
