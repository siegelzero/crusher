#!/usr/bin/env bash
# Repeated-run benchmark of fzcrusher builds on MiniZinc Challenge instances.
#
#   tests/bench/challenge_bench.sh -o OUTDIR [-r RUNS] [-t MS] [-p WORKERS] [-l LIST] LABEL=BINARY...
#
# Each instance is compiled once (crusher mznlib, dzn output with _objective) into
# OUTDIR/fzn, then every build runs it RUNS times; the build order rotates per
# run so drift on the machine does not favour one build. Each run's final
# objective is taken from the last solution (solns2out with the .ozn) and
# appended to OUTDIR/results.tsv; existing rows are skipped, so an interrupted
# benchmark resumes. Summarize with tests/bench/bench_summary.py OUTDIR.
#
# Runs are sequential and capped at 12 GB of address space each.
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
MSC="$ROOT/minizinc/crusher.msc"
OUT=""; RUNS=3; TL=60000; WORKERS=4; LIST="$ROOT/tests/bench/challenge_bench.csv"
while getopts "o:r:t:p:l:" opt; do
    case $opt in
        o) OUT=$OPTARG ;; r) RUNS=$OPTARG ;; t) TL=$OPTARG ;; p) WORKERS=$OPTARG ;; l) LIST=$OPTARG ;;
        *) exit 2 ;;
    esac
done
shift $((OPTIND - 1))
[ -n "$OUT" ] && [ $# -ge 1 ] || { sed -n 2,12p "$0"; exit 2; }
labels=(); bins=()
for kv in "$@"; do
    labels+=("${kv%%=*}"); b="${kv#*=}"
    [ -x "$b" ] || { echo "not executable: $b"; exit 2; }
    bins+=("$(realpath "$b")")
done
mkdir -p "$OUT/fzn" "$OUT/runs"
RES="$OUT/results.tsv"
[ -f "$RES" ] || printf "instance\tbuild\trun\tstatus\tobjective\tseconds\n" > "$RES"
{ echo "time_limit_ms=$TL workers=$WORKERS runs=$RUNS list=$LIST"
  for i in "${!labels[@]}"; do echo "${labels[$i]}=${bins[$i]}"; done; } > "$OUT/config.txt"

mapfile -t rows < <(grep -vE '^\s*(#|$)' "$LIST")
for row in "${rows[@]}"; do
    IFS=, read -r name model data <<< "$row"
    [ -f "$OUT/fzn/$name.fzn" ] && continue
    echo "compile $name"
    minizinc -c --solver "$MSC" --output-mode dzn --output-objective "$ROOT/minizinc_challenge/$model" \
        "$ROOT/minizinc_challenge/$data" -o "$OUT/fzn/$name.fzn" --ozn "$OUT/fzn/$name.ozn" \
        > "$OUT/fzn/$name.compile.log" 2>&1 || echo "  compile FAILED (see $OUT/fzn/$name.compile.log)"
done

nb=${#labels[@]}
for ((run = 1; run <= RUNS; run++)); do
    for row in "${rows[@]}"; do
        IFS=, read -r name model data <<< "$row"
        [ -f "$OUT/fzn/$name.fzn" ] || continue
        for ((k = 0; k < nb; k++)); do
            i=$(( (k + run) % nb ))
            label=${labels[$i]}; bin=${bins[$i]}
            grep -q "^$name	$label	$run	" "$RES" && continue
            tag="$OUT/runs/$name.$label.$run"
            t0=$(date +%s.%N)
            prlimit --as=$((12 * 1024**3)) timeout $((TL / 1000 + 60)) \
                "$bin" -p "$WORKERS" -t "$TL" "$OUT/fzn/$name.fzn" > "$tag.raw" 2> "$tag.err"
            secs=$(printf "%.0f" "$(echo "$(date +%s.%N) - $t0" | bc)")
            status=NONE; obj="-"
            if grep -q "^=====UNSATISFIABLE=====" "$tag.raw"; then
                status=UNSAT
            elif grep -q "^----------" "$tag.raw"; then
                status=SOL
                minizinc --ozn-file "$OUT/fzn/$name.ozn" < "$tag.raw" > "$tag.out" 2>/dev/null
                obj=$(grep -oE "^_objective = -?[0-9]+" "$tag.out" | tail -1 | awk '{print $3}')
                [ -z "$obj" ] && obj="sat"
            fi
            printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$name" "$label" "$run" "$status" "$obj" "$secs" | tee -a "$RES"
        done
    done
done
echo "BENCH DONE"
