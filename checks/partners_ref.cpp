// Check: the Pythagorean partner count sum_C |T(C)| straight from the definition.
//
//   T(C) = { A in [1,N] : A^2 + C^2 is a perfect square }
//
// No divisor walk, no segmentation, no table: a 128-bit square test per pair.
// This is the ground truth for the engines' `partners` counter (and for their
// `max_partners_per_C`), and it also reports the count restricted to
// C not = 2 (mod 4), which is the residue class the engines skip.
//
//   g++ -O2 -std=c++17 -o bin/partners_ref checks/partners_ref.cpp
//   ./bin/partners_ref --N 10000    # -> partners_all=28948 partners_skip2mod4=25335 max=59
//   ./bin/partners_ref --N 10000 --C 25   # list T(25) explicitly
//
// Cost is O(N^2), so this is only usable for small N.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cmath>
#include <vector>
#include <algorithm>

typedef uint64_t u64;
typedef unsigned __int128 u128;

static inline bool isSq(u128 n) {
    if (n == 0) return true;
    u64 r = (u64)sqrt((double)n);
    while ((u128)r * r > n) --r;
    while ((u128)(r + 1) * (r + 1) <= n) ++r;
    return (u128)r * r == n;
}

int main(int argc, char **argv) {
    u64 N = 10000, onlyC = 0;
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--N")) N = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "--C")) onlyC = strtoull(argv[++i], 0, 10);
    }
    if (onlyC) {
        std::vector<u64> v;
        for (u64 A = 1; A <= N; ++A)
            if (isSq((u128)A * A + (u128)onlyC * onlyC)) v.push_back(A);
        printf("C=%llu partners=%zu :", (unsigned long long)onlyC, v.size());
        for (u64 a : v) printf(" %llu", (unsigned long long)a);
        printf("\n");
        return 0;
    }
    u64 total = 0, totalSkip = 0, maxp = 0;
    for (u64 C = 1; C <= N; ++C) {
        u64 k = 0;
        for (u64 A = 1; A <= N; ++A)
            if (isSq((u128)A * A + (u128)C * C)) ++k;
        total += k;
        if ((C & 3) != 2) totalSkip += k;
        if (k > maxp) maxp = k;
    }
    printf("N=%llu partners_all=%llu partners_skip2mod4=%llu max=%llu\n",
           (unsigned long long)N, (unsigned long long)total,
           (unsigned long long)totalSkip, (unsigned long long)maxp);
    return 0;
}
