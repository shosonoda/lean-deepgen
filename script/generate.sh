#!/usr/bin/env bash
# Build the Lean project, extract the blueprint with LeanArchitect and render it locally.
#
# Usage:
#   ./script/generate.sh [options]
#
# Options:
#   --no-pdf         Skip the PDF version (leanblueprint pdf).
#   --no-cache       Skip `lake exe cache get`.
#   --serve [port]   Serve the generated site locally after building (default port 8000).
#   -h, --help       Show this help.
#
# Output:
#   .lake/build/blueprint/   TeX extracted from the @[blueprint] annotations
#   blueprint/web/           web version of the blueprint
#   blueprint/print/         PDF version of the blueprint
#   site/                    home page + blueprint, ready for ./script/publish-page.sh

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib.sh
source "$SCRIPT_DIR/lib.sh"
cd "$ROOT_DIR"

WITH_PDF=1 WITH_CACHE=1 SERVE=0 PORT=8000
while [ $# -gt 0 ]; do
  case "$1" in
    --no-pdf)   WITH_PDF=0; shift ;;
    --no-cache) WITH_CACHE=0; shift ;;
    --serve)    SERVE=1; shift; if [ $# -gt 0 ] && [[ "$1" =~ ^[0-9]+$ ]]; then PORT="$1"; shift; fi ;;
    -h|--help)  usage; exit 0 ;;
    *)          die "unknown option: $1 (see --help)" ;;
  esac
done

require_cmd lake "Install elan: https://github.com/leanprover/elan"
require_cmd leanblueprint "Install it with: pip install leanblueprint"

LIB="$(project_lib_name)"
[ -n "$LIB" ] || die "could not read the library name from lakefile.toml"
has_dependency LeanArchitect || die "LeanArchitect is not in lake-manifest.json; run 'lake update' first"

if [ "$WITH_CACHE" = 1 ] && has_dependency mathlib; then
  info "Fetching the Mathlib cache"
  lake exe cache get
fi

info "Building the Lean project"
lake build

info "Extracting the blueprint (lake build :blueprint)"
lake build :blueprint
LIB_TEX=".lake/build/blueprint/library/$LIB.tex"
[ -f "$LIB_TEX" ] || die "expected $LIB_TEX to be generated; is '$LIB' the library name in lakefile.toml?"

info "Rendering the web version (leanblueprint web)"
leanblueprint web

if [ "$WITH_PDF" = 1 ]; then
  if command -v latexmk >/dev/null 2>&1; then
    info "Rendering the PDF version (leanblueprint pdf)"
    leanblueprint pdf
  else
    warn "latexmk not found; skipping the PDF (install TeX Live or pass --no-pdf to silence this)"
    WITH_PDF=0
  fi
fi

if has_dependency checkdecls && [ -f blueprint/lean_decls ]; then
  info "Checking that every declaration in the blueprint exists (checkdecls)"
  lake exe checkdecls blueprint/lean_decls
fi

info "Assembling site/"
SITE="$ROOT_DIR/site"
rm -rf "$SITE"
mkdir -p "$SITE"
cp -R "$ROOT_DIR/home_page/." "$SITE/"
cp -R "$ROOT_DIR/blueprint/web" "$SITE/blueprint"
if [ "$WITH_PDF" = 1 ] && [ -f blueprint/print/print.pdf ]; then
  cp blueprint/print/print.pdf "$SITE/blueprint.pdf"
fi
touch "$SITE/.nojekyll"

ok "Blueprint generated in site/ (open site/index.html, or use --serve)"

if [ "$SERVE" = 1 ]; then
  require_cmd python3
  info "Serving http://localhost:$PORT/ (Ctrl-C to stop)"
  python3 -m http.server "$PORT" --directory "$SITE"
fi
