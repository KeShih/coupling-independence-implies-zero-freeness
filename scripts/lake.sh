#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
local_lean_bin="$project_dir/.tools/lean-4.33.1-darwin_aarch64/bin"
if [[ -x "$local_lean_bin/lake" ]]; then
  export PATH="$local_lean_bin:$PATH"
fi
export MATHLIB_CACHE_DIR="$project_dir/.cache/mathlib"
cd "$project_dir"
exec lake "$@"
