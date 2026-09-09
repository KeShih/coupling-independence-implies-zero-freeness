#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
compatibility_targets=(
  CI2ZF.Appendix.BBRHigh
  CI2ZF.Appendix.CLMMTransfer
  CI2ZF.Appendix.CVZeroFree
  CI2ZF.Appendix.EdgePottsZeroFree
  CI2ZF.Appendix.GirthFiveClosedPoincare
  CI2ZF.Appendix.GirthFiveZeroFree
  CI2ZF.Appendix.GirthHigh
  CI2ZF.Appendix.GirthResidualOriginal
  CI2ZF.Appendix.HighTemperatureZeroFree
  CI2ZF.Appendix.NearVigoda
)
"$project_dir/scripts/lake.sh" build CI2ZF CI2ZF.Appendix.CompletedRegions "${compatibility_targets[@]}"
"$project_dir/scripts/lake.sh" env lean -DwarningAsError=true audit/All.lean
