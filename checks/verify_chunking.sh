#!/usr/bin/env bash
# Validate the --seglo/--seghi piecewise mode of bin/fast_search5 against the
# archived whole-run numbers in results/.  Run it as
#
#     bash checks/verify_chunking.sh > results/verify_chunking.txt 2>&1
#
# from anywhere (the script re-roots itself).  It needs the binaries built by
# run_all.sh and about ten minutes (the 1e9 run dominates).  Exits non-zero if
# any check fails; raw per-run files are left in results/.verify/.
#
# Two things about the text make the comparisons delicate, and both are handled
# here rather than by eye:
#   * a line is a sequence of key=value tokens, so a numeric field must be read
#     after the '=' (awk's $2 would be the string "divisor_steps=...", i.e. 0);
#   * the C programs write CRLF while awk/sed write LF, so every captured line
#     is passed through `norm` (drop \r) before it is compared or summed.
#     The captured log lines are otherwise byte-for-byte the programs' stdout.
set -u
cd "$(dirname "$0")/.."                 # -> repository root
T=results/.verify
rm -rf "$T"; mkdir -p "$T"
FAIL=0
norm() { tr -d '\r'; }

# the additive counters, summed field by field; max_partners_per_C is a maximum
SUM='function val(t, a) { split(t, a, "="); return a[2] + 0 }
     /^N=/ { for (i = 2; i <= 8; ++i) s[i] += val($i)
             m = (val($4) > m) ? val($4) : m; ++p }
     END { printf "N=%s divisor_steps=%.0f partners=%.0f max_partners_per_C=%.0f candidates=%.0f tested=%.0f solutions=%.0f sieve_overflow=%.0f\n",
                   n, s[2], s[3], m, s[5], s[6], s[7], s[8] }'

# v5 prints one field more than the v3 archives (sieve_overflow), and
# divisor_steps is allowed to differ (v5 prunes harder): drop both before
# comparing a v5 line with an archived v3 line.
v5cmp() { sed -e 's/ sieve_overflow=[0-9]*//' -e 's/divisor_steps=[0-9]* //' | norm; }
v3cmp() { sed -e 's/divisor_steps=[0-9]* //' | norm; }

echo "# Validation of the piecewise (--seglo/--seghi) mode of fast_search5."
echo "# Each check echoes its command line, then that run's stdout (CR stripped)."
echo "# Compiler: $(g++ --version | head -1)"
echo "# Machine: $(nproc) threads, seg = 2^21 = 2097152 (the engine default)."
echo

# --- A: a fresh whole run must reproduce the v3 archive ---------------------
echo "## A. whole N=1e8, v3's filter set, freshly built binary"
echo "\$ ./bin/fast_search5.exe --N 100000000 --no-mod3"
./bin/fast_search5.exe --N 100000000 --no-mod3 2>"$T/a.err" | norm | tee "$T/a.txt"
if [ ! -s "$T/a.txt" ]; then
  echo "   CHECK A: FAILED -- no output line (was the run interrupted?)"; FAIL=1
else
  echo "\$ grep '^N=' results/run_v3_N1e8.txt        # archive: v3, earlier build"
  grep '^N=' results/run_v3_N1e8.txt | tee "$T/a.arch" | sed 's/^/   /'
  v5cmp < "$T/a.txt"  > "$T/a.cmp"
  v3cmp < "$T/a.arch" > "$T/a.arch.cmp"
  if diff -q "$T/a.cmp" "$T/a.arch.cmp" >/dev/null; then
    echo "   CHECK A: partners / max_partners_per_C / candidates / tested / solutions"
    echo "            identical to the v3 archive (divisor_steps is smaller: 3903016895"
    echo "            vs 11885034948, v5's stronger v <= 3N prune, REPORT.md 2.1)"
  else
    echo "   CHECK A: DIFFERS"; diff "$T/a.cmp" "$T/a.arch.cmp" | sed 's/^/   /'; FAIL=1
  fi
fi
echo

# --- B: the pieces of the same bound must sum to the whole run --------------
echo "## B. the same bound cut into three pieces: nseg = ceil(1e8/2^21) = 48"
for r in "0 16" "16 32" "32 48"; do
  set -- $r
  echo "\$ ./bin/fast_search5.exe --N 100000000 --no-mod3 --seglo $1 --seghi $2"
  ./bin/fast_search5.exe --N 100000000 --no-mod3 --seglo "$1" --seghi "$2" \
      2>>"$T/b.err" | norm | tee -a "$T/b.txt"
done
echo
echo "## B'. the three pieces summed field by field must reproduce the whole run A"
awk -v n=100000000 "$SUM" "$T/b.txt" | norm > "$T/b.sum"
echo "   pieces counted: $(grep -c '^N=' "$T/b.txt") of 3"
echo "   sum   : $(cat "$T/b.sum")"
echo "   whole : $(cat "$T/a.txt")"
if [ -s "$T/a.txt" ] && diff -q "$T/b.sum" "$T/a.txt" >/dev/null; then
  echo "   CHECK B: the pieces reproduce the whole run exactly (diff is empty)"
else
  echo "   CHECK B: DIFFERS"; diff "$T/b.sum" "$T/a.txt" | sed 's/^/   /'; FAIL=1
fi
echo

# --- C: the same at 1e9, where the archive is a whole v3 run -----------------
echo "## C. whole N=1e9, v3's filter set, freshly built binary"
echo "\$ ./bin/fast_search5.exe --N 1000000000 --no-mod3"
./bin/fast_search5.exe --N 1000000000 --no-mod3 2>"$T/c.err" | norm | tee "$T/c.txt"
if [ ! -s "$T/c.txt" ]; then
  echo "   CHECK C: FAILED -- no output line (was the run interrupted?)"; FAIL=1
else
  echo "\$ grep '^N=' results/run_N1e9.txt           # archive: v3, earlier build"
  grep '^N=' results/run_N1e9.txt | tee "$T/c.arch" | sed 's/^/   /'
  v5cmp < "$T/c.txt"  > "$T/c.cmp"
  v3cmp < "$T/c.arch" > "$T/c.arch.cmp"
  if diff -q "$T/c.cmp" "$T/c.arch.cmp" >/dev/null; then
    echo "   CHECK C: partners / max_partners_per_C / candidates / tested / solutions"
    echo "            identical to the v3 archive"
  else
    echo "   CHECK C: DIFFERS"; diff "$T/c.cmp" "$T/c.arch.cmp" | sed 's/^/   /'; FAIL=1
  fi
fi
echo
echo "## summary: $FAIL failing check(s); raw files in $T/"
exit "$FAIL"
