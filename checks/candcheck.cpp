// Check: the engines' counters recomputed straight from the definitions, with no
// divisor walk, no segmentation and no precomputed table.
//
//   T(C)        = { A in [1,N] : A^2 + C^2 is a perfect square }
//   partners    = sum over C of |T(C)|
//   candidates  = #{ A < B in T(C) : A+B <= N, A+B > C }               summed over C
//   tested      = those also satisfying the parity pattern of Lemma 4     -- "  --
//   tested_mod3 = those also satisfying the mod 3 condition of Lemma 5    -- "  --
//   solutions   = those that in addition pass the last two square tests   -- "  --
//
// The counters of lean/RationalDistance/Count.lean (kernel-checked with
// native_decide) are statements about exactly this predicate, so this program is
// the bridge between the Lean theorems and the C++ output.
//
//   g++ -O2 -std=c++17 -o bin/candcheck checks/candcheck.cpp
//   ./bin/candcheck 3000
//   # -> partners=7388 candidates=16868 tested=3774 tested_mod3=1796 solutions=0
//   #    fast_search5 --N 3000 --no-mod3 prints the same four counters
//
// Cost is O(N^2), so this is only usable for small N.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cmath>
#include <vector>
#include <algorithm>

typedef uint64_t u64;
static inline bool isSq(u64 n) {
    u64 r = (u64)sqrt((double)n);
    while (r > 0 && r * r > n) --r;
    while ((r + 1) * (r + 1) <= n) ++r;
    return r * r == n;
}

int main(int argc, char **argv) {
    u64 N = argc > 1 ? strtoull(argv[1], 0, 10) : 10000;
    u64 cand = 0, test = 0, test3 = 0, part = 0, sols = 0;
    std::vector<u64> T;
    for (u64 C = 1; C <= N; ++C) {
        T.clear();
        for (u64 A = 1; A <= N; ++A)
            if (isSq((u64)A * A + (u64)C * C)) T.push_back(A);
        std::sort(T.begin(), T.end());
        part += T.size();
        for (size_t i = 0; i < T.size(); ++i) {
            for (size_t j = i + 1; j < T.size(); ++j) {
                u64 A = T[i], B = T[j], Q = A + B;
                if (Q > N) break;
                if (Q <= C) continue;
                ++cand;
                u64 D = Q - C;
                bool ok = ((A & 1) && (B & 1) && !(C & 3) && !(D & 3)) ||
                          ((C & 1) && (D & 1) && !(A & 3) && !(B & 3));
                if (!ok) continue;
                ++test;
                if (!((A % 3 == 0 && B % 3 == 0) || (C % 3 == 0 && D % 3 == 0))) continue;
                ++test3;
                if (isSq(A * A + D * D) && isSq(B * B + D * D)) ++sols;
            }
        }
    }
    printf("REF N=%llu partners=%llu candidates=%llu tested=%llu tested_mod3=%llu solutions=%llu\n",
           (unsigned long long)N, (unsigned long long)part,
           (unsigned long long)cand, (unsigned long long)test,
           (unsigned long long)test3, (unsigned long long)sols);
    return 0;
}
