#!/bin/bash
# PAP public slice — the grounding gate, demonstrated.
# Runs the gate (verifier/pap_check.py) over four expressions and shows it ACCEPT a
# well-grounded one and REFUSE a spoofed / stale / overclaimed one. Self-contained:
# the grounding receipts resolve against this repo's own proofs/ (GateProofs.lean).
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
for ex in "$HERE"/examples/*.pap.json; do
  echo "============================================================"
  echo "CHECK: $(basename "$ex")"
  echo "------------------------------------------------------------"
  python3 "$HERE/verifier/pap_check.py" "$ex" \
    --proof-index   "$HERE/proof_index_subset.json" \
    --frontier-index "$HERE/frontier_index_subset.json" \
    --held-index    "$HERE/held_index_subset.json" \
    --lean-root     "$HERE/proofs"
  echo
done
