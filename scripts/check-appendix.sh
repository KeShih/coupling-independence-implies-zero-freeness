#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
"$project_dir/scripts/lake.sh" build CI2ZF.Appendix.CompletedRegions
"$project_dir/scripts/lake.sh" env lean -DwarningAsError=true AppendixAxiomAudit.lean
