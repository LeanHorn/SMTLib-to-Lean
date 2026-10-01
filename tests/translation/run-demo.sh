#!/usr/bin/env bash
# Compatibility entrypoint; the complete translator suite lives at tests/run.sh.
set -euo pipefail
exec "$(dirname "$0")/../run.sh" "$@"
