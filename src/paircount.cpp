// paircount.cpp -- independent count of the Pythagorean pairs used by the search.
// Counts unordered pairs (u,v), 1 <= u < v <= N, u^2+v^2 a perfect square, by
// running over primitive triples (m^2-n^2, 2mn, m^2+n^2) and their scalings.
// Engine v3 generates the same pairs from the factorisation of C^2; its
// "partners" statistic must equal exactly 2 * (this count), for every N.
// Build: g++ -O2 -o paircount paircount.cpp
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cmath>

typedef uint64_t u64;
static u64 g(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
    u64 N = argc > 1 ? strtoull(argv[1], 0, 10) : 1000000;
    u64 pairs = 0, triples = 0;
    u64 mMax = (u64)sqrtl(1.21L * (long double)N) + 2;
    for (u64 m = 2; m <= mMax; ++m)
        for (u64 n = 1 + (m & 1); n < m; n += 2) {
            if (g(m, n) != 1) continue;
            u64 p = m * m - n * n, q = 2 * m * n;
            if (p > N || q > N) continue;
            u64 kMax = (N / p < N / q) ? N / p : N / q;
            pairs += kMax;
            triples += kMax;
        }
    printf("N=%llu  unordered Pythagorean pairs (u<v, both <= N) = %llu\n",
           (unsigned long long)N, (unsigned long long)pairs);
    printf("N=%llu  v3 'partners' must equal 2*pairs = %llu\n",
           (unsigned long long)N, (unsigned long long)(2 * pairs));
    return 0;
}
