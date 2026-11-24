#!/usr/bin/env bash
set -euo pipefail

echo "=== 1. Lake build ==="
lake exe cache get || true
lake build PolarCodes Solution

echo "=== 2. Static hygiene check ==="
hygiene_hits=$(grep -rnE '\b(sorry|sorryAx|admit|axiom|native_decide|unsafe|unsafeCast|implemented_by|extern|partial|skipKernelTC|local instance)\b' PolarCodes.lean PolarCodes/ comparator/ChallengeDefs.lean comparator/Solution.lean | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(--|/[-!]|/-)' | grep -vE 'AuditAxioms\.lean' || true)
if [ -n "$hygiene_hits" ]; then
  echo "HYGIENE CHECK FAILED:"
  echo "$hygiene_hits"
  exit 1
fi
echo "HYGIENE CHECK PASSED"

echo "=== 3. Axiom audit ==="
if [ -f PolarCodes/AuditAxioms.lean ]; then
  lake env lean PolarCodes/AuditAxioms.lean
fi

echo "=== 4. Comparator ==="
lake comparator --paranoid
