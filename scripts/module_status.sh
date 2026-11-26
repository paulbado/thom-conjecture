#!/usr/bin/env bash
# Builds each module of ThomLean separately and prints a Markdown status table.
# Usage: scripts/module_status.sh [output.md]
set -uo pipefail
out="${1:-module_status.md}"
{
  echo "| Module | File | Build | Theorems/lemmas | Audited in Audit.lean |"
  echo "|---|---|---|---|---|"
} > "$out"
fail=0
for mod in $(grep -E "^import ThomLean\." ThomLean.lean | awk '{print $2}'); do
  file="$(echo "$mod" | tr . /).lean"
  if lake build "$mod" > /tmp/build_"$mod".log 2>&1; then res="✅ passing"; else res="❌ failing"; fail=1; fi
  nthm=$(grep -cE "^(private |protected )?(theorem|lemma) " "$file" || true)
  ns=$(grep -m1 -oE "^namespace [A-Za-z]+" "$file" | awk '{print $2}')
  naud=0
  for t in $(grep -oE "^(private |protected )?(theorem|lemma) [A-Za-z0-9_.'₀-₉]+" "$file" | awk '{print $NF}'); do
    if grep -qE "^#print axioms ${ns}\.${t}\s*$" Audit.lean; then naud=$((naud+1)); fi
  done
  echo "| \`$mod\` | \`$file\` | $res | $nthm | $naud |" >> "$out"
done
cat "$out"
exit $fail
