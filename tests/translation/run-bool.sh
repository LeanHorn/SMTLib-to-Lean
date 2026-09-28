#!/usr/bin/env bash
# Run the Boolean demo checks from any working directory.
set -euo pipefail
cd "$(dirname "$0")/../.."

lake build smt2lean testReconstruction
lake env .lake/build/bin/testReconstruction
lake env python3 tests/cli.py

echo "Boolean demo passed; all generated test files were temporary."
