#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
"$project_dir/scripts/lake.sh" build ZeroFreeness.Potts.Main ZeroFreeness.LeeYang ZeroFreeness.Holant
"$project_dir/scripts/lake.sh" env lean -DwarningAsError=true audit/Main.lean
