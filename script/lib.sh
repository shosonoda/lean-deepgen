#!/usr/bin/env bash
# Shared helpers for the scripts in ./script. Source this file; do not run it.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CONFIG_FILE="$ROOT_DIR/publish.env"
PUBLISH_IGNORE="$ROOT_DIR/.publishignore"

if [ -t 2 ]; then
  C_INFO=$'\033[1;34m'; C_WARN=$'\033[1;33m'; C_ERR=$'\033[1;31m'; C_OK=$'\033[1;32m'; C_RESET=$'\033[0m'
else
  C_INFO=""; C_WARN=""; C_ERR=""; C_OK=""; C_RESET=""
fi

info() { echo "${C_INFO}==>${C_RESET} $*" >&2; }
ok()   { echo "${C_OK}==>${C_RESET} $*" >&2; }
warn() { echo "${C_WARN}warning:${C_RESET} $*" >&2; }
die()  { echo "${C_ERR}error:${C_RESET} $*" >&2; exit 1; }

# Print the leading comment block of a script as its help text.
usage() { sed -n '2,/^$/p' "${BASH_SOURCE[1]}" | sed -e 's/^# \{0,1\}//'; }

require_cmd() {
  local cmd="$1" hint="${2:-}"
  command -v "$cmd" >/dev/null 2>&1 || die "'$cmd' is required but was not found in PATH.${hint:+ $hint}"
}

make_tmpdir() { mktemp -d "${TMPDIR:-/tmp}/lean-publish.XXXXXX"; }

# ---------------------------------------------------------------------------
# Project metadata (read from lakefile.toml)
# ---------------------------------------------------------------------------

# Name of the first [[lean_lib]] (also the root module name).
project_lib_name() {
  awk '/^\[\[lean_lib\]\]/ { f = 1; next }
       f && /^name[ \t]*=/ { sub(/^[^"]*"/, ""); sub(/".*$/, ""); print; exit }' "$ROOT_DIR/lakefile.toml"
}

# Lake package name (top-level `name = "..."`).
project_pkg_name() {
  awk '/^name[ \t]*=/ { sub(/^[^"]*"/, ""); sub(/".*$/, ""); print; exit }' "$ROOT_DIR/lakefile.toml"
}

has_dependency() { grep -q "\"name\": \"$1\"" "$ROOT_DIR/lake-manifest.json" 2>/dev/null; }

# ---------------------------------------------------------------------------
# Publishing configuration (publish.env)
# ---------------------------------------------------------------------------

# Load publish.env. Variables already set in the environment take precedence.
load_config() {
  local env_repo="${PUBLIC_REPO:-}" env_branch="${PUBLIC_BRANCH:-}" env_pages="${PAGES_BRANCH:-}"
  if [ -f "$CONFIG_FILE" ]; then
    # shellcheck disable=SC1090
    source "$CONFIG_FILE"
  fi
  PUBLIC_REPO="${env_repo:-${PUBLIC_REPO:-}}"
  PUBLIC_BRANCH="${env_branch:-${PUBLIC_BRANCH:-main}}"
  PAGES_BRANCH="${env_pages:-${PAGES_BRANCH:-gh-pages}}"
}

# Normalize a repository reference (owner/name, https URL or ssh URL) to owner/name.
normalize_repo() {
  local r="$1"
  r="${r%/}"; r="${r%.git}"
  r="${r#https://github.com/}"; r="${r#http://github.com/}"
  r="${r#git@github.com:}"; r="${r#ssh://git@github.com/}"
  echo "$r"
}

# Fail unless a public repository is configured. Sets PUBLIC_REPO and PUBLIC_REPO_URL.
require_public_repo() {
  load_config
  if [ -z "${PUBLIC_REPO:-}" ]; then
    die "the public repository is not configured.
  Set it with one of:
    ./script/init.sh --public-repo <owner>/<name>
    edit PUBLIC_REPO in $CONFIG_FILE
    PUBLIC_REPO=<owner>/<name> $0"
  fi
  PUBLIC_REPO="$(normalize_repo "$PUBLIC_REPO")"
  [[ "$PUBLIC_REPO" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]] \
    || die "PUBLIC_REPO must look like owner/name (got '$PUBLIC_REPO')"
  # PUBLIC_REPO_URL may be overridden (e.g. with a local bare repository for testing).
  if [ -n "${PUBLIC_REPO_URL:-}" ]; then
    PUBLIC_REPO_IS_GITHUB=0
  else
    PUBLIC_REPO_URL="https://github.com/$PUBLIC_REPO.git"
    PUBLIC_REPO_IS_GITHUB=1
  fi
}

# Ensure the public repository exists on GitHub. With "1" as argument, create it when missing.
ensure_public_repo_exists() {
  local create="${1:-0}"
  [ "$PUBLIC_REPO_IS_GITHUB" = 1 ] || return 0
  require_cmd gh "Install the GitHub CLI: https://cli.github.com/"
  if gh repo view "$PUBLIC_REPO" >/dev/null 2>&1; then
    return 0
  fi
  if [ "$create" = 1 ]; then
    info "Creating public repository https://github.com/$PUBLIC_REPO"
    gh repo create "$PUBLIC_REPO" --public >/dev/null
  else
    die "repository https://github.com/$PUBLIC_REPO does not exist or is not accessible.
  Create it with: ./script/publish-code.sh --create"
  fi
}

# Check out <branch> in the clone at <dir>, creating an orphan branch if it does not exist remotely.
checkout_branch() {
  local dir="$1" branch="$2"
  if git -C "$dir" ls-remote --exit-code --heads origin "$branch" >/dev/null 2>&1; then
    git -C "$dir" checkout --quiet "$branch"
  else
    info "Branch '$branch' does not exist in the public repository yet; creating it"
    git -C "$dir" checkout --quiet --orphan "$branch"
  fi
}

# Remove everything in <dir> except .git.
clear_worktree() {
  find "$1" -mindepth 1 -maxdepth 1 -not -name .git -exec rm -rf {} +
}
