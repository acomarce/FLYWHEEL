#!/bin/bash
# SessionStart hook for Claude Code cloud sessions.
#
# 1. Installs elan and the toolchain pinned in lean-toolchain. Both come from
#    GitHub release assets, because releases.lean-lang.org (elan's default
#    source) is blocked by the cloud network policy.
# 2. Clones Mathlib at the pinned revision (its sources are then greppable
#    under .lake/packages/mathlib) and, if a Mathlib cache host is reachable,
#    runs `lake exe cache get` for prebuilt oleans. If the cache hosts are
#    blocked it says so and skips it, because building Mathlib from source
#    takes hours.
#
# Never fails the session: every problem is reported on stdout (which Claude
# sees) and the script exits 0. Full log: $LOG.
set -uo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(cd "$(dirname "$0")/../.." && pwd)}"
ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
ELAN_VERSION="v4.2.4"
LOG="${TMPDIR:-/tmp}/flywheel-session-start.log"
export ELAN_HOME PATH="$ELAN_HOME/bin:$PATH"
: > "$LOG"

say() { echo "[session-start] $*"; echo "[session-start] $*" >> "$LOG"; }
run() { "$@" >> "$LOG" 2>&1; }

if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  echo "export ELAN_HOME=\"$ELAN_HOME\"; export PATH=\"$ELAN_HOME/bin:\$PATH\"" >> "$CLAUDE_ENV_FILE"
fi

case "$(uname -m)" in
  x86_64) elan_arch=x86_64; lean_platform=linux ;;
  aarch64 | arm64) elan_arch=aarch64; lean_platform=linux_aarch64 ;;
  *) say "unsupported architecture $(uname -m); skipping Lean setup"; exit 0 ;;
esac

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# --- elan ------------------------------------------------------------------
if [ ! -x "$ELAN_HOME/bin/elan" ]; then
  url="https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-$elan_arch-unknown-linux-gnu.tar.gz"
  if run curl -sSfL --retry 3 -o "$work/elan.tar.gz" "$url" &&
     run tar -xzf "$work/elan.tar.gz" -C "$work" &&
     run "$work/elan-init" -y --default-toolchain none --no-modify-path; then
    say "installed elan $ELAN_VERSION"
  else
    say "ERROR: could not install elan from $url (see $LOG)"; exit 0
  fi
fi

# --- toolchain -------------------------------------------------------------
toolchain="$(tr -d '[:space:]' < "$PROJECT_DIR/lean-toolchain")"  # leanprover/lean4:v4.26.0-rc2
origin="${toolchain%%:*}"
version="${toolchain#*:}"
tc_dir="$ELAN_HOME/toolchains/$(echo "$toolchain" | sed 's|/|--|g; s|:|---|g')"
if [ -x "$tc_dir/bin/lean" ]; then
  say "toolchain $toolchain already installed"
else
  asset="lean-${version#v}-$lean_platform.tar.zst"
  url="https://github.com/$origin/releases/download/$version/$asset"
  decompress() {
    if command -v zstd > /dev/null; then
      zstd -dc "$1"
    else
      # No zstd binary: use the python package in a throwaway directory.
      python3 -m pip install --quiet --target "$work/py" zstandard >> "$LOG" 2>&1 &&
        python3 -I -c 'import sys; sys.path.insert(0, sys.argv[1]); import zstandard
zstandard.ZstdDecompressor().copy_stream(sys.stdin.buffer, sys.stdout.buffer)' "$work/py" < "$1"
    fi
  }
  mkdir -p "$ELAN_HOME/toolchains" "$work/tc"
  if run curl -sSfL --retry 3 -o "$work/$asset" "$url" &&
     decompress "$work/$asset" 2>> "$LOG" | tar -x -C "$work/tc" 2>> "$LOG" &&
     [ -x "$work/tc/${asset%.tar.zst}/bin/lean" ]; then
    rm -f "$work/$asset"
    rm -rf "$tc_dir"
    mv "$work/tc/${asset%.tar.zst}" "$tc_dir"
    say "installed toolchain $toolchain from GitHub releases"
  else
    say "ERROR: could not install $toolchain from $url (see $LOG)"; exit 0
  fi
fi

# --- Mathlib ---------------------------------------------------------------
cd "$PROJECT_DIR" || exit 0
# Clone the dependencies pinned in lake-manifest.json without building
# anything. Never `lake update`: lakefile.toml tracks Mathlib master.
if timeout 900 lake env true >> "$LOG" 2>&1; then
  clone="Mathlib sources are in .lake/packages/mathlib (grep them for lemma names)"
else
  clone="cloning the Mathlib dependency also failed"
fi
# When the cache host is blocked, `lake exe cache get` retries every one of
# ~7700 files (about an hour), so probe the hosts first.
cache_host=""
for h in lakecache.blob.core.windows.net mathlib4.lean-cache.cloud; do
  if curl -s -o /dev/null --max-time 10 "https://$h/"; then cache_host="$h"; break; fi
done
no_build="Do not run \`lake build\` or \`lake env lean\` here: without the cache they compile Mathlib from source, which takes hours. Verify by pushing and reading the CI logs instead (see CLAUDE.md)."
if [ -z "$cache_host" ]; then
  say "WARNING: Mathlib cache hosts (lakecache.blob.core.windows.net, mathlib4.lean-cache.cloud) are blocked by the network policy, so \`lake exe cache get\` was skipped. $clone. $no_build To build locally, ask the owner to add those hosts to the environment's allowed domains."
elif timeout 1200 lake exe cache get >> "$LOG" 2>&1; then
  say "Mathlib cache ready ($clone). \`lake build\` checks the whole project; \`lake env lean src/<File>.lean\` checks one file."
else
  say "WARNING: \`lake exe cache get\` failed although $cache_host is reachable. $clone. $no_build Log: $LOG"
fi
exit 0
