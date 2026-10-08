#!/usr/bin/env bash
# Run translator checks and demos from any working directory.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 tests/cli_selection.py
lake build smt2lean testSource testParser testReconstruction testHorn testTranslation testArrays
for test_target in testSource testParser testReconstruction testHorn testTranslation testArrays; do
  lake env ".lake/build/bin/$test_target"
done
lake env python3 tests/cli.py
lake env python3 tests/anchor.py

echo "All translator checks and demos passed; all generated test files were temporary."
