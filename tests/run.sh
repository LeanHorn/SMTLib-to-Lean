#!/usr/bin/env bash
# Run translator checks and demos from any working directory.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build smt2lean testSource testParser testReconstruction testHorn testTranslation testArrays
lake env python3 tests/run.py "$@"
