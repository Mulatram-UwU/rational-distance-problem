// Check: is the segmented residual sieve of src/fast_search4.cpp a *complete*
// factorisation?
//
// The engines divide every C by all primes p <= sqrt(C) and then call the
// leftover (1 or a prime) the largest prime factor.  Everything downstream --
// the divisor walk, and the "omega(C) <= 10" assumption behind the
// sieve_overflow counter -- rests on that being right.  This program runs the
// same sieve over [1,M] and compares the resulting multiset of (prime,
// exponent), plus the leftover, against plain trial division for every C.
//
//   g++ -O2 -std=c++17 -o bin/sievecheck checks/sievecheck.cpp
//   ./bin/sievecheck 2000000        # -> checked=1999999 mismatches=0  (M=2000000 seg=32768)
//
// Exit status is non-zero if anything mismatched.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cmath>
#include <vector>
#include <algorithm>

typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t u8;

static const int MAXF = 10;

int main(int argc, char **argv) {
    u64 M = argc > 1 ? strtoull(argv[1], 0, 10) : 2000000;
    u64 segSize = argc > 2 ? strtoull(argv[2], 0, 10) : (1u << 15);

    u64 root = (u64)sqrt((double)M) + 2;
    std::vector<u32> primes;
    {
        std::vector<u8> comp(root + 1, 0);
        for (u64 i = 2; i <= root; ++i)
            if (!comp[i]) { primes.push_back((u32)i); for (u64 j = i * i; j <= root; j += i) comp[j] = 1; }
    }

    u64 nseg = (M + segSize - 1) / segSize;
    u64 bad = 0, checked = 0;
    for (u64 si = 0; si < nseg; ++si) {
        u64 lo = si * segSize, hi = lo + segSize - 1;
        if (hi > M) hi = M;
        size_t len = (size_t)(hi - lo + 1);
        std::vector<u64> rem(len);
        std::vector<u64> fs((size_t)len * MAXF);
        std::vector<u8> cnt(len);
        for (size_t i = 0; i < len; ++i) { rem[i] = lo + i; cnt[i] = 0; }
        for (size_t pi = 0; pi < primes.size(); ++pi) {
            u64 p = primes[pi];
            if (p * p > hi) break;
            u64 start = ((lo + p - 1) / p) * p;
            if (start < p * p) start = p * p;
            for (u64 m = start; m <= hi; m += p) {
                size_t i = (size_t)(m - lo);
                if (rem[i] % p == 0) {
                    if (cnt[i] < MAXF) fs[i * MAXF + cnt[i]++] = p;
                    do { rem[i] /= p; } while (rem[i] % p == 0);
                }
            }
        }
        for (size_t i = 0; i < len; ++i) {
            u64 C = lo + i;
            if (C < 2) continue;
            ++checked;
            // reference: trial division
            std::vector<std::pair<u64,int>> ref;
            u64 t = C;
            for (u64 p = 2; p * p <= t; ++p)
                if (t % p == 0) { int e = 0; while (t % p == 0) { t /= p; ++e; } ref.push_back({p, e}); }
            if (t > 1) ref.push_back({t, 1});
            // sieve result
            std::vector<std::pair<u64,int>> got;
            for (int j = 0; j < (int)cnt[i]; ++j) {
                u64 p = fs[i * MAXF + j], tt = C; int e = 0;
                while (tt % p == 0) { tt /= p; ++e; }
                got.push_back({p, e});
            }
            if (rem[i] > 1) got.push_back({rem[i], 1});
            std::sort(ref.begin(), ref.end());
            std::sort(got.begin(), got.end());
            if (ref != got) {
                ++bad;
                if (bad <= 20) {
                    printf("MISMATCH C=%llu  ref:", (unsigned long long)C);
                    for (auto &q : ref) printf(" %llu^%d", (unsigned long long)q.first, q.second);
                    printf("   got:");
                    for (auto &q : got) printf(" %llu^%d", (unsigned long long)q.first, q.second);
                    printf("\n");
                }
            }
        }
    }
    printf("checked=%llu mismatches=%llu  (M=%llu seg=%llu)\n",
           (unsigned long long)checked, (unsigned long long)bad,
           (unsigned long long)M, (unsigned long long)segSize);
    return bad ? 1 : 0;
}
