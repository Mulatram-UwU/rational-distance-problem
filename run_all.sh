#!/usr/bin/env bash
# Reproduce the computational results of REPORT.md.
#
# Usage: bash run_all.sh [quick|full|deep|5e10]     (default: quick)
#   quick : minutes  small engines, all cross-checks, both Lean projects
#   full  : hours    also 1e9 / 3e9 (v3 and v4/v5) and the brute force to 1e4
#   deep  : ~1.5 h   the headline run: every Q <= 2e10, plus the midline at 2e10
#   5e10  : hours    the extension: Q <= 5e10 in resumable pieces (run_5e10.sh)
#
# Requirements: g++ (C++17 + OpenMP) and python3.  The Lean steps are skipped
# unless a `lake` is found on PATH, in ~/.elan/bin, or via LEAN_BIN=<toolchain bin dir>.
set -u
cd "$(dirname "$0")"
MODE="${1:-quick}"
CXX="${CXX:-g++}"

# On Windows/MSYS the executables carry a suffix; everywhere else they do not.
case "$(uname -s 2>/dev/null)" in MINGW*|MSYS*|CYGWIN*) EXE=".exe" ;; *) EXE="" ;; esac

find_lake() {
  if [ -n "${LEAN_BIN:-}" ] && [ -x "$LEAN_BIN/lake$EXE" ]; then echo "$LEAN_BIN/lake$EXE"; return; fi
  if command -v lake >/dev/null 2>&1; then command -v lake; return; fi
  [ -x "$HOME/.elan/bin/lake$EXE" ] && { echo "$HOME/.elan/bin/lake$EXE"; return; }
  return 1
}
LAKE="$(find_lake)" || LAKE=""

if [ -n "${PYTHON:-}" ]; then PY="$PYTHON"
elif command -v python3 >/dev/null 2>&1; then PY=python3
else PY=python
fi

mkdir -p bin results

# build <output> <source> [compiler flags...]
# Compiles to a temporary name first: on Windows an executable that is currently
# running cannot be overwritten, and we would rather keep the old binary than
# lose the new one.
build() {
  local out="$1" src="$2"; shift 2
  local tmp="bin/.tmp.$$.$(basename "$out")"
  if ! "$CXX" "$@" -o "$tmp" "$src"; then echo "  !! compile failed: $src"; rm -f "$tmp"; return 1; fi
  if ! mv -f "$tmp" "$out" 2>/dev/null; then
    echo "  !! $out is locked by a running process -- kept the existing binary"
    rm -f "$tmp"
  fi
}

echo "== build: search engines, brute force, pair counter, checks =="
build bin/fast_search_v1$EXE src/fast_search.cpp    -O2 -march=native -fopenmp -std=c++17
build bin/fast_search2$EXE    src/fast_search2.cpp   -O2 -march=native -fopenmp -std=c++17
build bin/fast_search3$EXE    src/fast_search3.cpp   -O2 -march=native -fopenmp -std=c++17
build bin/fast_search4$EXE    src/fast_search4.cpp   -O3 -march=native -fopenmp -std=c++17
build bin/fast_search5$EXE    src/fast_search5.cpp   -O3 -march=native -fopenmp -std=c++17
build bin/brute$EXE           src/brute.cpp          -O2 -march=native -fopenmp -std=c++17
build bin/brute_pairs$EXE     src/brute_pairs.cpp    -O2 -march=native -std=c++17
build bin/paircount$EXE       src/paircount.cpp      -O2 -march=native -std=c++17
build bin/midline_search$EXE  src/midline_search.cpp -O2 -march=native -fopenmp -std=c++17
build bin/candcheck$EXE       checks/candcheck.cpp   -O2 -march=native -std=c++17
build bin/partners_ref$EXE    checks/partners_ref.cpp -O2 -march=native -std=c++17
build bin/midline_ref$EXE     checks/midline_ref.cpp -O2 -march=native -std=c++17
build bin/sievecheck$EXE      checks/sievecheck.cpp  -O2 -march=native -std=c++17

echo "== engines agree (candidates / tested / solutions) on N = 1e4 .. 1e7 =="
for n in 10000 100000 1000000 10000000; do
  for v in fast_search_v1 fast_search2 fast_search3; do
    printf '%-16s ' "$v"; ./bin/"$v$EXE" --N "$n" 2>/dev/null | grep -E '^N='
  done
done

echo "== v4 (segmented sieve, residue classes) must reproduce v3 exactly, both filter sets =="
for n in 10000 100000 1000000 10000000; do
  printf 'v3 mod3off %-10s ' "$n"; ./bin/fast_search3$EXE --N "$n"           2>/dev/null | grep -E '^N='
  printf 'v4 mod3off %-10s ' "$n"; ./bin/fast_search4$EXE --N "$n" --no-mod3 2>/dev/null | grep -E '^N='
  printf 'v3 mod3on  %-10s ' "$n"; ./bin/fast_search3$EXE --N "$n" --mod3    2>/dev/null | grep -E '^N='
  printf 'v4 mod3on  %-10s ' "$n"; ./bin/fast_search4$EXE --N "$n"           2>/dev/null | grep -E '^N='
  printf 'v5 mod3on  %-10s ' "$n"; ./bin/fast_search5$EXE --N "$n"           2>/dev/null | grep -E '^N='
done

echo "== the four counters straight from the definition (checks/candcheck.cpp) =="
echo "   the engines must print the same partners / candidates / tested:"
for n in 1000 2000 3000; do
  printf '  candcheck      N=%-5s ' "$n"; ./bin/candcheck$EXE "$n"
  printf '  fast_search5   N=%-5s ' "$n"; ./bin/fast_search5$EXE --N "$n" --no-mod3 2>/dev/null | grep -E '^N='
done
echo "   (these are also the counters proved in lean/RationalDistance/Count.lean)"

echo "== the partner set straight from the definition vs the engines' divisor walk =="
printf '  partners_ref N=10000   '; ./bin/partners_ref$EXE --N 10000
printf '  fast_search5 N=10000   '; ./bin/fast_search5$EXE --N 10000 --no-mod3 2>/dev/null | grep -E '^N='

echo "== the segmented sieve of v4 against trial division =="
./bin/sievecheck$EXE 2000000        # -> checked=1999999 mismatches=0

echo "== positive control for the midline enumerator (checks/midline_ref.cpp) =="
echo "   midline_search takes N and enumerates Amax = N/2, so pass 100000 here:"
printf '  midline_ref    Amax=50000  '; ./bin/midline_ref$EXE 50000        # -> 7312
printf '  midline_search Amax=50000  '; ./bin/midline_search$EXE 100000  # -> primitive_triples=7312

echo "== relaxed problem (3 conditions) must find solutions: positive control =="
./bin/fast_search3$EXE --N 1000000 --three --no-parity 2>/dev/null | grep -c '^SOLUTION'

echo "== main searches (no solutions expected) =="
./bin/fast_search_v1$EXE --N 100000000 | tee results/run_N1e8.txt
./bin/fast_search3$EXE   --N 100000000 | tee results/run_v3_N1e8.txt
./bin/paircount$EXE 1000000000        | tee results/paircount_N1e9.txt

echo "== local structure of the system (modular analysis) =="
"$PY" src/residue_structure.py | tee results/residue_structure.txt

echo "== centre line x = 1/2: reduction checks + rational point search =="
"$PY" src/center_line.py 200 --fast | tee results/center_line_ffcheck.txt
"$PY" src/center_line.py 1500       | tee results/center_line_search.txt

echo "== independent brute force, Q <= 3000 (minutes) =="
./bin/brute$EXE 3000 | tee results/brute_3000.txt

echo "== middle line x = 1/2 (the A = B case): exhaustive search =="
./bin/midline_search$EXE 100000000 | tee results/midline_N1e8.txt

if [ "$MODE" = full ]; then
  echo "== heavy runs =="
  ./bin/fast_search2$EXE --N 300000000  | tee results/run_N3e8.txt     # ~6 min
  ./bin/fast_search3$EXE --N 1000000000 | tee results/run_N1e9.txt     # ~11 min
  ./bin/fast_search3$EXE --N 3000000000 | tee results/run_N3e9.txt     # ~26 min
  ./bin/brute$EXE 10000 | tee results/brute_10000.txt                  # ~4 min
  ./bin/midline_search$EXE 3000000000 | tee results/midline_N3e9.txt   # ~3 s
  # v4 at 1e9 with v3's filter set: must reproduce run_N1e9.txt exactly
  ./bin/fast_search4$EXE --N 1000000000 --no-mod3 | tee results/run_v4_N1e9.txt   # ~4 min
  # v5 at 3e9 with v3's filter set: must reproduce run_N3e9.txt exactly
  ./bin/fast_search5$EXE --N 3000000000 --no-mod3 | tee results/run_v5_N3e9.txt   # ~25 min
fi

if [ "$MODE" = deep ]; then
  echo "== deep run: every quadruple with common denominator Q <= 2e10 =="
  ./bin/fast_search5$EXE --N 20000000000 | tee results/run_N2e10.txt    # ~1.5 h, 12 threads
  ./bin/midline_search$EXE 20000000000  | tee results/midline_N2e10.txt # ~26 s
  ./bin/paircount$EXE  20000000000      | tee results/paircount_N2e10.txt
  echo "   (partners in run_N2e10.txt must equal 2 * the pair count just printed)"
fi

if [ "$MODE" = 5e10 ]; then
  echo "== extension: every quadruple with common denominator Q <= 5e10 =="
  echo "   (piecewise and resumable; see the header of run_5e10.sh)"
  bash run_5e10.sh 50000000000 24
fi

echo "== Lean 4 formalisation, core part (no Mathlib) =="
if [ -n "$LAKE" ]; then
  ( cd lean && "$LAKE" build )
else
  echo "Lean not found -- skipping (install elan, or set LEAN_BIN=<toolchain>/bin)"
fi

echo "== Lean 4 formalisation, Mathlib part (geometry bridge + midline) =="
if [ -n "$LAKE" ] && [ -d lean-mathlib/.lake/packages/mathlib ]; then
  ( cd lean-mathlib && "$LAKE" build RationalDistanceAlgo.Main )
else
  echo "Mathlib not set up in lean-mathlib -- skipping (see notes/lean-setup.md)"
fi
echo "== publication hygiene: no local path or machine name anywhere in the tree =="
"$PY" checks/scan_leaks.py . || echo "   ^^ rewrite those before publishing"
echo "== done =="
