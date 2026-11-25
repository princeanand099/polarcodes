#!/usr/bin/env bash
set -euo pipefail

echo "=== 1. Fetching Mathlib cache ==="
lake exe cache get || true

echo "=== 2. Building PolarCodes and comparator Solution ==="
lake build PolarCodes Solution

echo "=== 3. Static hygiene check ==="
hygiene_hits=$(grep -rnE '\b(sorry|sorryAx|admit|axiom|native_decide|unsafe|unsafeCast|implemented_by|extern|partial|skipKernelTC|local instance)\b' \
  PolarCodes.lean PolarCodes/ comparator/ChallengeDefs.lean comparator/Solution.lean \
  | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(--|/[-!]|/-)' \
  | grep -vE 'AuditAxioms\.lean' || true)
if [ -n "$hygiene_hits" ]; then
  echo "HYGIENE_CHECK_FAILED:"
  echo "$hygiene_hits"
  exit 1
fi
echo "HYGIENE_CHECK_PASSED (0 forbidden constructs)"

echo "=== 4. Axiom audit ==="
lake env lean PolarCodes/AuditAxioms.lean

echo "=== 5. Lake comparator ==="
lake comparator
