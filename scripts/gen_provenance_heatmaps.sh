#!/usr/bin/env bash
set -euo pipefail

# Ensure ESMETA_HOME is set to repo root by default
export ESMETA_HOME="${ESMETA_HOME:-$(cd "$(dirname "$0")/.." && pwd)}"

echo "[1/2] Running esmeta tycheck with provenance logs..." >&2
"$ESMETA_HOME/bin/esmeta" tycheck \
  -tycheck:detail-log \
  -tycheck:provenance

echo "[2/2] Generating heatmaps from provenance tables..." >&2
cd "$ESMETA_HOME/logs/analyze"

# Prefer python3 if available
PY=python3
if ! command -v "$PY" >/dev/null 2>&1; then
  PY=python
fi

"$PY" "$ESMETA_HOME/scripts/provenance_heatmaps.py"

echo "Done. PDFs at: $ESMETA_HOME/logs/analyze" >&2

