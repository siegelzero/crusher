#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SOLVER_MSC="$PROJECT_ROOT/minizinc/crusher.msc"
FZCRUSHER="$PROJECT_ROOT/fzcrusher"
TEST_DEFS="$SCRIPT_DIR/mztest.csv"
MZN_DIR="$PROJECT_ROOT/minizinc_challenge"

RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[1;33m'; NC='\033[0m'
passed=0; failed=0; errors=()

# Prerequisites
command -v minizinc &>/dev/null || { echo "Error: minizinc not found"; exit 1; }
[ -f "$FZCRUSHER" ] || { echo "Error: fzcrusher not found. Run 'make fzcrusher' first."; exit 1; }

echo "MiniZinc Integration Tests"
echo "=========================="

while IFS=, read -r name model data type time_limit min_obj max_obj; do
    # Skip comments and blank lines
    [[ "$name" =~ ^#.*$ || -z "$name" ]] && continue

    # Build minizinc command
    cmd=(minizinc --solver "$SOLVER_MSC" --output-objective --output-mode json
         --time-limit "$time_limit" "$MZN_DIR/$model")
    [ "$data" != "-" ] && cmd+=("$MZN_DIR/$data")

    printf "  %-35s " "$name"

    # Run, capture stdout (solutions+objective), discard stderr
    if ! output=$("${cmd[@]}" 2>/dev/null); then
        # Non-zero exit could be timeout (normal) or error
        # MiniZinc returns 0 even on timeout with --time-limit, so non-zero = real error
        if [ -z "$output" ]; then
            printf "${RED}ERROR${NC} (minizinc failed)\n"
            failed=$((failed + 1))
            errors+=("$name: minizinc command failed")
            continue
        fi
        # Some output was produced before failure — process it
    fi

    # Check for no-solution statuses
    if echo "$output" | grep -q "=====UNKNOWN====="; then
        printf "${RED}FAIL${NC} (no solution found)\n"
        failed=$((failed + 1)); errors+=("$name: no solution (UNKNOWN)"); continue
    fi
    if echo "$output" | grep -q "=====UNSATISFIABLE====="; then
        printf "${RED}FAIL${NC} (unsatisfiable)\n"
        failed=$((failed + 1)); errors+=("$name: unsatisfiable"); continue
    fi

    # Satisfy: just check solution exists
    if [ "$type" = "satisfy" ]; then
        if echo "$output" | grep -q '"'; then
            printf "${GREEN}PASS${NC}\n"; passed=$((passed + 1))
        else
            printf "${RED}FAIL${NC} (no solution)\n"
            failed=$((failed + 1)); errors+=("$name: no solution output")
        fi
        continue
    fi

    # Optimization: extract _objective from last JSON solution
    obj=$(echo "$output" | grep '"_objective"' | tail -1 |
          sed -E 's/.*"_objective"[[:space:]]*:[[:space:]]*(-?[0-9]+).*/\1/')

    if [ -z "$obj" ]; then
        printf "${RED}FAIL${NC} (no objective in output)\n"
        failed=$((failed + 1)); errors+=("$name: could not parse _objective"); continue
    fi

    # Check bounds (directional: minimize cares about max_obj, maximize about min_obj)
    bound_ok=true
    if [ "$type" = "minimize" ] && [ -n "$max_obj" ] && [ "$obj" -gt "$max_obj" ]; then
        bound_ok=false
    fi
    if [ "$type" = "maximize" ] && [ -n "$min_obj" ] && [ "$obj" -lt "$min_obj" ]; then
        bound_ok=false
    fi

    if $bound_ok; then
        printf "${GREEN}PASS${NC} (obj=%d)\n" "$obj"; passed=$((passed + 1))
    else
        printf "${RED}FAIL${NC} (obj=%d, expected %s..%s)\n" "$obj" "${min_obj:-*}" "${max_obj:-*}"
        failed=$((failed + 1)); errors+=("$name: obj=$obj outside bounds [${min_obj:-*}, ${max_obj:-*}]")
    fi
done < "$TEST_DEFS"

echo ""
echo "Results: $passed passed, $failed failed"
if [ ${#errors[@]} -gt 0 ]; then
    echo ""; echo "Failures:"
    for err in "${errors[@]}"; do echo "  - $err"; done
fi
exit $((failed > 0 ? 1 : 0))
