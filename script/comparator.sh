#!/usr/bin/env bash
# Run Comparator (https://github.com/leanprover/comparator) on comparator/config.json:
# checks that every theorem listed there is proved in comparator/Solution.lean with
# exactly the statement of comparator/Challenge.lean, using only the permitted axioms.
#
# Prerequisites (see README): the comparator binary, lean4export built for this
# project's Lean version, and landrun (Linux) or Comparator's fake-landrun shim (macOS).
# Locations default to ../comparator-tools/ and can be overridden by the environment:
#   COMPARATOR_BIN, COMPARATOR_LEAN4EXPORT, COMPARATOR_LANDRUN
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS="${COMPARATOR_TOOLS:-$ROOT_DIR/../comparator-tools}"
LEAN_VER="$(sed 's/.*://' "$ROOT_DIR/lean-toolchain")"
BIN="${COMPARATOR_BIN:-$TOOLS/comparator/.lake/build/bin/comparator}"
EXPORT="${COMPARATOR_LEAN4EXPORT:-$TOOLS/lean4export-$LEAN_VER/.lake/build/bin/lean4export}"
if [ -z "${COMPARATOR_LANDRUN:-}" ]; then
  if command -v landrun >/dev/null 2>&1; then LANDRUN="$(command -v landrun)";
  else LANDRUN="$TOOLS/comparator/scripts/fake-landrun.sh"; echo "note: using fake-landrun (no sandbox)"; fi
else LANDRUN="$COMPARATOR_LANDRUN"; fi
for f in "$BIN" "$EXPORT" "$LANDRUN"; do [ -x "$f" ] || { echo "missing: $f" >&2; exit 1; }; done
cd "$ROOT_DIR"
exec env COMPARATOR_LANDRUN="$LANDRUN" COMPARATOR_LEAN4EXPORT="$EXPORT" lake env "$BIN" comparator/config.json
