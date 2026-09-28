#!/usr/bin/env bash
# Run the Boolean, integer, and function demos from any working directory.
set -euo pipefail
cd "$(dirname "$0")/../.."

lake build smt2lean testReconstruction
lake env .lake/build/bin/testReconstruction
lake env python3 tests/cli.py

echo "Boolean, integer, and function demos passed; all generated test files were temporary."
