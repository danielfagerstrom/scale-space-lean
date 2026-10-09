#!/usr/bin/env bash
# Thin wrapper so this generator can be invoked as `bash scripts/gen-library-reference.sh`.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec lake env python3 "$here/gen_library_reference.py" "$@"
