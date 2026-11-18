#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/check_modules.py
lake --wfail build
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true checks/Axioms.lean
python3 check_map.py --lean .
