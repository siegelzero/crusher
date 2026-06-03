#!/usr/bin/env bash
# MiniZinc Challenge conformance checks for Crusher.
#
# These verify the challenge-specific behaviour that the correctness suite
# (`make mztest`) does not cover: the exact FREE/PAR invocations, FlatZinc
# output separators, intermediate-solution streaming (`-i`), the UNKNOWN
# fallback for unsupported constraints, and graceful SIGTERM handling.
#
# Run after `make fzcrusher`.  Self-contained: builds its own tiny models so it
# needs no external instance data.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SOLVER_MSC="$PROJECT_ROOT/minizinc/crusher.msc"
FZCRUSHER="$PROJECT_ROOT/fzcrusher"

RED='\033[0;31m'; GREEN='\033[0;32m'; NC='\033[0m'
passed=0; failed=0; errors=()

command -v minizinc &>/dev/null || { echo "Error: minizinc not found"; exit 1; }
[ -f "$FZCRUSHER" ] || { echo "Error: fzcrusher not found. Run 'make fzcrusher' first."; exit 1; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

pass() { printf "  %-45s ${GREEN}PASS${NC} %s\n" "$1" "${2:-}"; passed=$((passed+1)); }
fail() { printf "  %-45s ${RED}FAIL${NC} %s\n" "$1" "${2:-}"; failed=$((failed+1)); errors+=("$1: ${2:-}"); }

# Tiny models ----------------------------------------------------------------
cat > "$WORK/sat.mzn" <<'EOF'
include "alldifferent.mzn";
array[1..5] of var 1..5: x;
constraint alldifferent(x);
constraint x[1] < x[2];
solve satisfy;
EOF

cat > "$WORK/opt.mzn" <<'EOF'
int: n = 6;
array[1..n] of int: w = [2,3,4,5,6,7];
array[1..n] of int: v = [3,4,5,6,7,9];
array[1..n] of var 0..1: x;
constraint sum(i in 1..n)(w[i]*x[i]) <= 12;
solve maximize sum(i in 1..n)(v[i]*x[i]);
EOF

echo "Crusher Challenge Conformance Checks"
echo "===================================="

# 1. FREE (satisfy): one solution block terminated by the solution separator.
out=$(minizinc --solver "$SOLVER_MSC" -i --output-mode dzn --output-objective -f \
        --time-limit 8000 "$WORK/sat.mzn" 2>/dev/null)
if echo "$out" | grep -q -- '----------' && echo "$out" | grep -q 'x = '; then
  pass "FREE satisfy: solution + separator"
else
  fail "FREE satisfy: solution + separator" "$(echo "$out" | tr '\n' ' ')"
fi

# 2. PAR (satisfy): -p 4 must be accepted and still produce a solution.
out=$(minizinc --solver "$SOLVER_MSC" -i --output-mode dzn --output-objective -p 4 \
        --time-limit 8000 "$WORK/sat.mzn" 2>/dev/null)
if echo "$out" | grep -q -- '----------' && echo "$out" | grep -q 'x = '; then
  pass "PAR satisfy (-p 4): solution + separator"
else
  fail "PAR satisfy (-p 4): solution + separator" "$(echo "$out" | tr '\n' ' ')"
fi

# 3. FREE (optimize): intermediate solutions stream with improving objective and
#    the search terminates with the optimality marker.
out=$(minizinc --solver "$SOLVER_MSC" -i --output-mode dzn --output-objective -f \
        --time-limit 10000 "$WORK/opt.mzn" 2>/dev/null)
objs=$(echo "$out" | grep '_objective' | sed -E 's/.*=[[:space:]]*(-?[0-9]+).*/\1/')
nobj=$(echo "$objs" | grep -c .)
sorted=$(echo "$objs" | sort -n | tr '\n' ' ')
asis=$(echo "$objs" | tr '\n' ' ')
if [ "$nobj" -ge 2 ] && [ "$sorted" = "$asis" ]; then
  pass "FREE optimize: $nobj improving solutions" "($asis)"
else
  fail "FREE optimize: monotone intermediates" "objs=[$asis]"
fi
if echo "$out" | grep -q -- '=========='; then
  pass "FREE optimize: optimality marker (==========)"
else
  fail "FREE optimize: optimality marker (==========)" "$(echo "$out" | tr '\n' ' ')"
fi

# 4. Unsupported constraint -> UNKNOWN (never a constraint-violating solution).
cat > "$WORK/unk.fzn" <<'EOF'
var 0..5: x:: output_var;
constraint some_unknown_global(x, 3);
solve satisfy;
EOF
out=$("$FZCRUSHER" "$WORK/unk.fzn" 2>/dev/null)
if [ "$out" = "=====UNKNOWN=====" ]; then
  pass "Unsupported constraint -> UNKNOWN"
else
  fail "Unsupported constraint -> UNKNOWN" "got: $out"
fi

# 5. SIGTERM mid-solve flushes a complete last solution block.
minizinc --solver "$SOLVER_MSC" --compile --fzn "$WORK/opt.fzn" "$WORK/opt.mzn" 2>/dev/null
"$FZCRUSHER" -i --time-limit 60000 "$WORK/opt.fzn" > "$WORK/term.out" 2>/dev/null &
pid=$!
sleep 2
kill -TERM "$pid" 2>/dev/null
wait "$pid" 2>/dev/null
if grep -q 'x = ' "$WORK/term.out" && grep -q -- '----------' "$WORK/term.out"; then
  pass "SIGTERM: flushed a complete solution"
else
  fail "SIGTERM: flushed a complete solution" "$(tr '\n' ' ' < "$WORK/term.out")"
fi

echo ""
echo "Results: $passed passed, $failed failed"
if [ ${#errors[@]} -gt 0 ]; then
  echo ""; echo "Failures:"
  for e in "${errors[@]}"; do echo "  - $e"; done
fi
exit $((failed > 0 ? 1 : 0))
