// midline_search.cpp
// ---------------------------------------------------------------------------
// Exhaustive check of the *middle line* x = 1/2 of the unit square: is there a
// point (1/2, y) with 0 < y < 1 whose four distances to the corners are all
// rational, with common denominator Q <= N ?
//
// The main search (fast_search4.cpp) enumerates pairs A < B and therefore does
// NOT cover the midline case A = B (which is exactly x = 1/2).  This program
// covers it, so that "search engine returned 0 solutions" upgrades to "no
// solution at all with common denominator <= N" without appealing to the
// published midline theorem.
//
// Math.  With A = Qx = Q/2 (so A = B) and C = Qy, D = Q - C:
//     midline solution  <=>  A + A = Q = C + D, 0 < A,C,D < Q,
//                           A^2 + C^2 and A^2 + D^2 both perfect squares.
// All conditions are homogeneous of degree 2 in (A, C, D), so the primitive
// normal form gcd(A, C, D) = 1 has a solution iff any solution exists.
// In the primitive form:
//   * A must be even.  Indeed A = B, and if A were odd then C, D would be even
//     with 4 | C, 4 | D (Lemma 4), so Q = C + D = 0 (mod 4) while Q = 2A = 2
//     (mod 4) -- a contradiction.
//   * gcd(A, C) = 1: a prime dividing A and C divides D = 2A - C and hence
//     gcd(A, C, D) = 1.
//   * so (A, C, h1) is a *primitive* Pythagorean triple with even leg A, i.e.
//     A = 2mn, C = m^2 - n^2, h1 = m^2 + n^2 with gcd(m, n) = 1, m > n and
//     m - n odd.
// Hence it suffices to run over primitive (m, n) with
//     A = 2mn <= N/2,   D = 2A - C = 4mn - m^2 + n^2 > 0,
// and test whether A^2 + D^2 is a perfect square.
//
// 128-bit note.  At N = 2*10^10 we get A <= 10^10 and D < 2A <= 2*10^10, so
// A^2 + D^2 is about 5*10^20 and does NOT fit in u64 (max 1.8*10^19).  Both
// the square test and its sqrt are therefore 128-bit here.  The m-loop is also
// bounded by the D > 0 condition m < (2+sqrt5) n, which removes wasted work
// and, more importantly, keeps m^2 inside u64 at every step.
//
// Build: g++ -O3 -march=native -fopenmp -std=c++17 -o bin/midline_search.exe src/midline_search.cpp
// Run:   ./bin/midline_search.exe 20000000000
// ---------------------------------------------------------------------------

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cmath>
#include <chrono>

typedef uint64_t u64;
typedef unsigned __int128 u128;

// squares modulo 64, used as a cheap pre-filter
static bool sq64[64];

static inline bool isSquare128(u128 n) {
    if (n == 0) return true;
    if (!sq64[(u64)n & 63]) return false;
    u64 r = (u64)sqrt((double)n);
    while ((u128)r * r > n) --r;
    while ((u128)(r + 1) * (r + 1) <= n) ++r;
    return (u128)r * r == n;
}

static inline u64 gcd64(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
    u64 N = 1000000;
    if (argc > 1) N = strtoull(argv[1], 0, 10);
    for (int i = 0; i < 64; ++i) sq64[(u64)i * i % 64] = true;

    const u64 Amax = N / 2;              // A <= N/2  (Q = 2A <= N)
    auto t0 = std::chrono::steady_clock::now();

    u64 triples = 0, tests = 0, sols = 0;
    u64 solA = 0, solC = 0, solD = 0, solM = 0, solN = 0;

    long long nmax = 1;
    while ((u64)(2 * (nmax + 1)) * (nmax + 1) <= Amax) ++nmax;

#pragma omp parallel for schedule(dynamic, 64) reduction(+:triples,tests,sols)
    for (long long n = 1; n <= nmax; ++n) {
        // m > n, m - n odd  =>  m has the parity opposite to n.
        // Bounds: A = 2mn <= Amax, and D = 2A - C > 0  <=>  m < (2+sqrt5) n.
        u64 mb = (u64)(4.2360679774998 * (double)n) + 2;
        if (mb > Amax / (u64)n) mb = Amax / (u64)n;
        for (u64 m = (u64)n + 1; m <= mb; m += 2) {
            u64 A = 2 * m * n;
            if (A > Amax) break;
            // D = 2A - C = 4mn - (m^2 - n^2) must be positive, i.e. m^2 - 4mn - n^2 < 0
            u64 C = m * m - n * n;
            if (C >= 2 * A) continue;     // equivalent to D <= 0; note C < 2A is the D > 0 test
            if (gcd64(m, n) != 1) continue;
            ++triples;
            u64 D = 2 * A - C;
            u128 s = (u128)A * A + (u128)D * D;
            if (!sq64[(u64)s & 63]) continue;   // cheap filter
            ++tests;
            if (isSquare128(s)) {
                ++sols;
                solA = A; solC = C; solD = D; solM = m; solN = n;
            }
        }
    }

    auto t1 = std::chrono::steady_clock::now();
    printf("N=%llu Amax=%llu primitive_triples=%llu isqrt_tests=%llu midline_solutions=%llu\n",
           (unsigned long long)N, (unsigned long long)Amax,
           (unsigned long long)triples, (unsigned long long)tests,
           (unsigned long long)sols);
    if (sols) printf("  first: m=%llu n=%llu A=%llu C=%llu D=%llu Q=%llu\n",
                     (unsigned long long)solM, (unsigned long long)solN,
                     (unsigned long long)solA, (unsigned long long)solC,
                     (unsigned long long)solD, (unsigned long long)(2 * solA));
    fprintf(stderr, "[midline] %.2fs\n", std::chrono::duration<double>(t1 - t0).count());
    return 0;
}
