// Check: positive control for the midline enumerator src/midline_search.cpp.
//
// That enumerator walks primitive Pythagorean triples (A,C) = (2mn, m^2-n^2) and
// then tests a second square condition.  On the ranges that matter it finds
// nothing, so its "0 solutions" would be vacuous on its own: an enumerator that
// walked the wrong set (or nothing at all) would print 0 as well.  This program
// counts the *same* set from the other side -- every primitive pair (A,C) with A
// even, A <= Amax, C < 2A and A^2+C^2 a square, by brute force -- and the two
// counts must agree.  The enumerator reports this count as `primitive_triples`,
// e.g. 1462708696 at Amax = 10^10 (results/midline_N2e10.txt).
//
//   g++ -O2 -std=c++17 -o bin/midline_ref checks/midline_ref.cpp
//   ./bin/midline_ref 50000     # -> 7312
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cmath>

typedef uint64_t u64;
typedef unsigned __int128 u128;

static inline bool isSq(u128 n) {
    if (n == 0) return true;
    u64 r = (u64)sqrt((double)n);
    while ((u128)r * r > n) --r;
    while ((u128)(r + 1) * (r + 1) <= n) ++r;
    return (u128)r * r == n;
}
static inline u64 g64(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
    u64 Amax = argc > 1 ? strtoull(argv[1], 0, 10) : 500000;
    u64 cnt = 0;
    for (u64 A = 2; A <= Amax; A += 2) {
        for (u64 C = 1; C < 2 * A; ++C) {
            if (g64(A, C) != 1) continue;
            if (isSq((u128)A * A + (u128)C * C)) ++cnt;
        }
    }
    printf("Amax=%llu primitive (A even, gcd(A,C)=1, A^2+C^2 square, C<2A) = %llu\n",
           (unsigned long long)Amax, (unsigned long long)cnt);
    return 0;
}
