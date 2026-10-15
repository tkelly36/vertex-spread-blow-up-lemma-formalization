#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "Usage: scripts/rebuild_viewer.sh /path/to/trellis-checkout" >&2
  exit 2
fi

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
trellis_checkout="$(cd "$1" && pwd)"

# Reproduce with Trellis revision 98db307f88de34ac4d6311d2efafeb88b5f21827.
# Build the pinned Lean project first: the exporter also checks target axioms.
(cd "$repo_root/formalization" && lake build Tablet)
python3 "$trellis_checkout/scripts/export_public_tablet_viewer.py" \
  "$repo_root/formalization" "$repo_root/docs" \
  --title "A Vertex-Spread Blow-Up Lemma" \
  --github-base "https://github.com/tkelly36/vertex-spread-blow-up-lemma-formalization/blob/main/formalization" \
  --emit-semantic-closure "$repo_root/formalization/semantic-closure.json" \
  --mathlib-imports-json "$repo_root/docs/data/mathlib-imports.json"
python3 "$repo_root/scripts/validate_release.py"
