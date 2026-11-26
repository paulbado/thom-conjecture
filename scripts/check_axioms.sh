#!/usr/bin/env bash
# Verification gate: no sorry/admit/custom axioms, and every audited theorem depends only on
# propext, Classical.choice and Quot.sound.
# Usage: scripts/check_axioms.sh [audit-output-file]
set -euo pipefail
out="${1:-audit.txt}"
status=0

echo "== Source scan"
if grep -rnwE "sorry|admit" ThomLean Audit.lean ThomLean.lean; then
  echo "FAIL: found sorry/admit"; status=1
else
  echo "ok: no sorry, no admit"
fi
if grep -rnE "^\s*((private|protected|noncomputable)\s+)*axiom\s" ThomLean ThomLean.lean; then
  echo "FAIL: found a custom axiom declaration"; status=1
else
  echo "ok: no custom axiom declarations"
fi

echo "== Axiom audit (lake env lean Audit.lean)"
lake env lean Audit.lean > "$out" 2>&1 || { cat "$out"; echo "FAIL: Audit.lean did not elaborate"; exit 1; }
total=$(grep -cE "depends on axioms|does not depend on any axioms" "$out" || true)
bad=$(grep "depends on axioms" "$out" | grep -vE "\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]" || true)
expected=$(grep -c "^#print axioms" Audit.lean)
echo "audited theorems: $total (expected $expected)"
if [ "$total" -ne "$expected" ]; then echo "FAIL: audit count mismatch"; status=1; fi
if [ -n "$bad" ]; then echo "FAIL: non-standard axioms:"; echo "$bad"; status=1; else echo "ok: only standard axioms"; fi
if grep -q "sorryAx" "$out"; then echo "FAIL: sorryAx in audit"; status=1; fi
exit $status
