#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-Bispectrum}"

# Count sorry occurrences by Lean file (excluding .lake)
find "$ROOT" -name '*.lean' -type f | while read -r f; do
  c=$(grep -o '\bsorry\b' "$f" | wc -l || true)
  if [ "$c" -gt 0 ]; then
    printf "%4d  %s\n" "$c" "$f"
  fi
done | sort -nr
