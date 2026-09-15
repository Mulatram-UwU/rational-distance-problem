#!/usr/bin/env bash
# ---------------------------------------------------------------------------
# The Q <= 5*10^10 extension, run in resumable pieces.
#
#     bash run_5e10.sh [N] [pieces]          default: 50000000000 24
#
# Why pieces.  The plain whole-run form
#
#     ./bin/fast_search5 --N 50000000000
#
# takes hours on one machine and prints its counters only when it is finished,
# so a reboot anywhere in it loses everything -- which is exactly what happened
# on the first attempt (raw log: results/attempt1_5e10_interrupted.err, stopped
# at 11000/23842 segments with an empty stdout).  The engine handles each C
# independently of the segment that C falls in, and every counter it prints is
# a sum over C, so the segment range can be cut into pieces (--seglo/--seghi)
# and the printed lines simply added: partners, candidates, tested, solutions,
# divisor_steps and sieve_overflow are additive, max_partners_per_C is a
# maximum.  checks/verify_chunking.sh proves on N = 10^8 and 10^9 that the
# pieces reproduce the whole-run numbers exactly.
#
# The pieces are cut by *estimated work*, not by C-range: the cost per C was
# assumed to grow roughly like C^1.8, so 24 equal C-ranges would have made the
# last piece many times the first.  That exponent turned out to be too large --
# the measured per-segment cost falls off far more slowly (see
# notes/cost-5e10.md), so the pieces are in fact unequal in wall time: piece 00
# took 3932 s and piece 23 took 111 s.  That costs nothing conclusion-wise:
# every segment is still visited exactly once and the pieces still sum to the
# whole-run line (checks/verify_chunking.sh), which is all the cut is for -- an
# interruption costs at most one piece.
#
# Resuming is automatic: a piece whose output already holds a final line is
# skipped, so simply run the script again after a crash.  Raw per-piece output
# stays in results/chunks5e10/, and when every piece is done the sum is written
# to results/run_N5e10.txt (the single line a whole run would have printed).
# ---------------------------------------------------------------------------
set -u
cd "$(dirname "$0")"

N="${1:-50000000000}"
K="${2:-24}"
SEGSZ=$((1 << 21))                       # the engine's default segment size
nseg=$(( (N + SEGSZ - 1) / SEGSZ ))
OUT=results/chunks5e10

case "$(uname -s 2>/dev/null)" in MINGW*|MSYS*|CYGWIN*) EXE=".exe" ;; *) EXE="" ;; esac
BIN="./bin/fast_search5$EXE"
[ -x "$BIN" ] || { echo "missing $BIN -- build it with: bash run_all.sh quick"; exit 1; }

mkdir -p "$OUT"
awk -v n="$nseg" -v k="$K" 'BEGIN{ for(i=0;i<=k;i++) printf "%d\n", int(n*(i/k)^(1/1.8)+0.5) }' \
    > "$OUT/bounds.txt"
BOUND=($(cat "$OUT/bounds.txt"))

echo "N=$N  pieces=$K  segments=$nseg of $SEGSZ residues"
printf 'schedule:'; for k in $(seq 0 "$K"); do printf ' %s' "${BOUND[$k]}"; done; echo

summarise() {                            # rewrite the combined progress log
  {
    echo "# stderr of the piecewise Q <= $N run (see run_5e10.sh)."
    echo "# Each piece below is one invocation of"
    echo "#   bin/fast_search5 --N $N --seglo <lo> --seghi <hi>"
    echo "# over segments [lo,hi) of $SEGSZ residues each; the raw per-piece"
    echo "# stdout is results/chunks5e10/part_<k>.txt."
    for k in $(seq 0 $((K - 1))); do
      kk=$(printf '%02d' "$k")
      lo=${BOUND[$k]}; hi=${BOUND[$((k + 1))]}
      [ -s "$OUT/part_$kk.err" ] || continue
      echo "# --- piece $kk: segments [$lo,$hi)"
      cat "$OUT/part_$kk.err"
    done
  } > results/run_N5e10.err
}

aggregate() {                            # all pieces -> results/run_N5e10.txt
  local done_n=0
  for k in $(seq 0 $((K - 1))); do
    kk=$(printf '%02d' "$k")
    grep -q '^N=' "$OUT/part_$kk.txt" 2>/dev/null && done_n=$((done_n + 1))
  done
  if [ "$done_n" -ne "$K" ]; then
    echo "incomplete: $done_n/$K pieces finished, results/run_N5e10.txt not written"
    return 1
  fi
  cat "$OUT"/part_*.txt > "$OUT/pieces.txt"       # the raw lines, in order
  # every field is a key=value token, so read the number after the '='
  awk -v n="$N" '
      function val(t, a) { split(t, a, "="); return a[2] + 0 }
      /^N=/ { for (i = 2; i <= 8; ++i) s[i] += val($i)
              m = (val($4) > m) ? val($4) : m; ++p }
      END { printf "N=%s divisor_steps=%.0f partners=%.0f max_partners_per_C=%.0f " \
                    "candidates=%.0f tested=%.0f solutions=%.0f sieve_overflow=%.0f\n",
                    n, s[2], s[3], m, s[5], s[6], s[7], s[8] }
    ' "$OUT/pieces.txt" > results/run_N5e10.txt
  echo "sum of $K pieces -> results/run_N5e10.txt:"
  sed 's/^/  /' results/run_N5e10.txt
}

fail=0
for k in $(seq 0 $((K - 1))); do
  kk=$(printf '%02d' "$k")
  lo=${BOUND[$k]}; hi=${BOUND[$((k + 1))]}
  part="$OUT/part_$kk.txt"
  if grep -q '^N=' "$part" 2>/dev/null; then
    echo "piece $kk [$lo,$hi): done, skipped"
    continue
  fi
  if [ "$lo" -ge "$hi" ]; then : > "$part"; summarise; continue; fi
  echo "piece $kk [$lo,$hi): running ..."
  t0=$(date +%s)
  if "$BIN" --N "$N" --seglo "$lo" --seghi "$hi" > "$part.partial" 2> "$OUT/part_$kk.err"; then
    mv -f "$part.partial" "$part"
    echo "piece $kk done in $(( $(date +%s) - t0 ))s: $(cat "$part")"
  else
    echo "piece $kk FAILED (exit $?) after $(( $(date +%s) - t0 ))s -- rerun this script to resume"
    fail=1
    summarise
    break
  fi
  summarise
done

[ "$fail" -eq 0 ] && aggregate
echo "== run_5e10 done =="
