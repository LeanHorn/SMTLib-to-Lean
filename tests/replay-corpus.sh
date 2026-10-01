#!/usr/bin/env bash
# Replay every query in tests/smt and tests/chc through z3 and compare the
# answers against the recorded ones.
#
#   smt/*.smt2  expected answers = fixpoint's "; SMT Says: Sat|Unsat" comments,
#               one per (check-sat), in order.
#   chc/*.smt2  expected answer  = the (set-info :status ...) line; z3 picks the
#               Spacer engine because of (set-logic HORN).
#
# Usage: tests/replay-corpus.sh            (Z3=/path/to/z3 and TIMEOUT=secs are optional)
set -u
Z3=${Z3:-z3}
TIMEOUT=${TIMEOUT:-60}
cd "$(dirname "$0")"

now() { perl -MTime::HiRes=time -e 'printf "%.3f", time'; }

"$Z3" --version
printf '\n%-36s %6s %8s  %s\n' FILE CHECKS SECONDS RESULT
fail=0
for f in smt/*.smt2 chc/*.smt2; do
  expected=$(grep -E '^; SMT Says: ' "$f" | awk '{print tolower($4)}')
  if [ -z "$expected" ]; then
    expected=$(grep -E '^\(set-info :status ' "$f" | awk '{print $3}' | tr -d ')')
  fi
  t0=$(now)
  out=$("$Z3" -T:"$TIMEOUT" "$f" 2>&1)
  t1=$(now)
  got=$(printf '%s\n' "$out" | grep -E '^(sat|unsat|unknown|timeout)$')
  n=$(printf '%s\n' "$expected" | grep -c .)
  if printf '%s\n' "$out" | grep -q '^(error'; then
    result="FAIL $(printf '%s\n' "$out" | grep -m1 '^(error')"
    fail=1
  elif [ "$got" != "$expected" ]; then
    result="FAIL (answers differ from recorded)"
    fail=1
  else
    result="ok  $(printf '%s\n' "$got" | grep -c '^unsat$') unsat, $(printf '%s\n' "$got" | grep -c '^sat$') sat"
  fi
  printf '%-36s %6s %8.2f  %s\n' "$f" "$n" "$(echo "$t1 - $t0" | bc)" "$result"
  if [ $fail -ne 0 ] && [ -n "${VERBOSE:-}" ]; then printf '%s\n' "$out"; fi
done
exit $fail
