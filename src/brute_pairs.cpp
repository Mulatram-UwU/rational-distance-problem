// ---------------------------------------------------------------------------
// brute_pairs.cpp -- INDEPENDENT enumerator of all Pythagorean leg pairs
// ---------------------------------------------------------------------------
// Task: list ALL pairs (u,v) with 1 <= u,v <= N such that u^2 + v^2 is a
// perfect square, one pair per line "u v", ascending in u then v, no duplicates.
//
// TWO INDEPENDENT METHODS (they must agree):
//
// (A) default: DIVISOR / FACTORISATION METHOD -- NOT the classical parametrisation.
//     Given u with u^2 + v^2 = w^2, we have
//         u^2 = w^2 - v^2 = (w - v)(w + v).
//     So put d = w - v and e = w + v.  Then
//         d * e = u^2,   d < e,   d and e have the SAME PARITY,
//         v = (e - d) / 2,   w = (e + d) / 2,
//     and conversely every factorisation u^2 = d*e with d < e and e - d even
//     yields a valid Pythagorean pair with leg u (v >= 1 automatically since
//     e > d).  Hence: for each u, factor u (smallest-prime-factor sieve), write
//     u^2 = prod p_i^(2 a_i), enumerate ALL divisors d of u^2 by depth-first
//     multiplication over the prime powers, keep those with d < u, test
//     (u^2/d - d) even, and emit v = (u^2/d - d)/2 when 1 <= v <= N.
//     This is a bijection with the set of Pythagorean pairs of leg u: the map
//     (u,v,w) -> (d,e) is inverse to (d,e) -> v, so nothing is missed and
//     nothing is produced twice for a fixed u.
//
// (B) --via-triples: CLASSICAL primitive-triple parametrisation
//     m > n >= 1, gcd(m,n) = 1, m - n odd; primitive legs (m^2-n^2, 2mn),
//     scaled by k >= 1.  Both orderings are emitted when both legs are <= N.
//     Completeness: every Pythagorean triangle is k times a unique primitive
//     one, so this enumerates exactly the same unordered leg pairs.
//     m is bounded by m^2 <= 2N because (m^2-n^2) + 2mn = m^2 + n(2m-n) > m^2,
//     so max(leg1, leg2) > m^2/2, which must be <= N.
//
// The two modes are compared by byte-comparing their output files (see report).
//
// Usage:
//   brute_pairs <N> [--out FILE] [--via-triples] [--quiet]
//   (without --out the list goes to stdout; statistics go to stderr)
//
// Compile:
//   g++ -O2 -march=native -std=c++17 -o brute_pairs brute_pairs.cpp
// ---------------------------------------------------------------------------

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <cmath>
#include <string>
#include <vector>
#include <algorithm>
#include <numeric>
#include <chrono>

// Exact integer square root (same two-stage exact construction as brute.cpp):
// for n < 2^52 the double sqrt is used only as a seed that is provably within
// +-1 of floor(sqrt(n)) (n is exact as a double, sqrtsd is correctly rounded),
// and the answer is repaired by exact integer comparisons; above 2^52 an
// overflow-free pure-integer restoring square root is used.  See brute.cpp for
// the full argument.  Compiling with -DISQRT_PURE_INT=1 disables the floating
// seed completely (pure integer arithmetic only).
#ifndef ISQRT_PURE_INT
#define ISQRT_PURE_INT 0
#endif

static inline uint64_t isqrt_u64(uint64_t n) {
    if (n == 0) return 0;
    if (!ISQRT_PURE_INT && n < (1ULL << 52)) {
        uint64_t r = (uint64_t)std::sqrt((double)n);
        while (r > 0 && r * r > n) --r;
        while ((r + 1) * (r + 1) <= n) ++r;
        return r;
    }
    uint64_t r = 0;
    for (int b = 31; b >= 0; --b) {
        uint64_t t = r | (1ULL << b);
        if (t <= n / t) r = t;
    }
    return r;
}
static inline bool is_square(uint64_t n) {
    const uint64_t r = isqrt_u64(n);
    return r * r == n;
}

typedef std::pair<uint32_t, uint32_t> Pair;

// Enumerate all divisors of prod p_i^(e_i) by DFS.
static void enum_divisors(const std::vector<std::pair<uint32_t, uint32_t>>& pf,
                          size_t idx, uint64_t cur, std::vector<uint64_t>& out) {
    if (idx == pf.size()) { out.push_back(cur); return; }
    uint64_t p = pf[idx].first, e = pf[idx].second, mul = 1;
    for (uint64_t j = 0; j <= e; ++j) {
        enum_divisors(pf, idx + 1, cur * mul, out);
        mul *= p;
    }
}

int main(int argc, char** argv) {
    if (argc < 2) {
        std::fprintf(stderr, "usage: %s <N> [--out FILE] [--via-triples] [--quiet]\n", argv[0]);
        return 2;
    }
    uint64_t N = std::strtoull(argv[1], nullptr, 10);
    std::string outPath;
    bool viaTriples = false, quiet = false;
    for (int i = 2; i < argc; ++i) {
        if (std::strcmp(argv[i], "--via-triples") == 0) viaTriples = true;
        else if (std::strcmp(argv[i], "--quiet") == 0) quiet = true;
        else if (std::strcmp(argv[i], "--out") == 0 && i + 1 < argc) outPath = argv[++i];
        else if (std::strncmp(argv[i], "--out=", 6) == 0) outPath = argv[i] + 6;
        else { std::fprintf(stderr, "unknown argument: %s\n", argv[i]); return 2; }
    }

    const auto t0 = std::chrono::steady_clock::now();
    std::vector<Pair> pairs;

    if (!viaTriples) {
        // ---------------- Method (A): divisor / factorisation method ----------
        // smallest-prime-factor sieve up to N
        std::vector<uint32_t> spf((size_t)N + 1, 0);
        for (uint64_t i = 2; i <= N; ++i) {
            if (spf[(size_t)i] == 0) {
                for (uint64_t j = i; j <= N; j += i)
                    if (spf[(size_t)j] == 0) spf[(size_t)j] = (uint32_t)i;
            }
        }
        std::vector<uint64_t> divs;
        std::vector<std::pair<uint32_t, uint32_t>> pf;
        for (uint64_t u = 1; u <= N; ++u) {
            // factor u; u = 1 gives the empty factorisation.
            // We store DOUBLE exponents because the divisors we need are the
            // divisors of u^2 = prod p_i^(2 a_i).
            pf.clear();
            uint64_t t = u;
            while (t > 1) {
                uint32_t p = spf[(size_t)t];
                uint32_t e = 0;
                while (t % p == 0) { t /= p; ++e; }
                pf.push_back({p, 2 * e});
            }
            const uint64_t u2 = u * u;
            divs.clear();
            enum_divisors(pf, 0, 1, divs);
            for (uint64_t d : divs) {
                if (d >= u) continue;              // d < e  <=>  d < u
                const uint64_t e = u2 / d;
                if (((e - d) & 1ULL) != 0) continue;   // v would not be integral
                const uint64_t v = (e - d) / 2;
                if (v >= 1 && v <= N) pairs.push_back({(uint32_t)u, (uint32_t)v});
            }
        }
    } else {
        // ---------------- Method (B): classical primitive triples -------------
        for (uint64_t m = 2; m * m <= 2 * N; ++m) {
            for (uint64_t n = 1; n < m; ++n) {
                if (((m - n) & 1ULL) == 0) continue;       // m - n odd
                if (std::gcd(m, n) != 1) continue;         // primitive
                const uint64_t a = m * m - n * n;
                const uint64_t b = 2 * m * n;
                if (a > N && b > N) continue;              // even k=1 impossible
                for (uint64_t k = 1; k * a <= N && k * b <= N; ++k) {
                    pairs.push_back({(uint32_t)(k * a), (uint32_t)(k * b)});
                    pairs.push_back({(uint32_t)(k * b), (uint32_t)(k * a)});
                }
            }
        }
    }

    const auto t1 = std::chrono::steady_clock::now();

    // Deterministic ordering: ascending u, then v; duplicates removed.
    std::sort(pairs.begin(), pairs.end());
    pairs.erase(std::unique(pairs.begin(), pairs.end()), pairs.end());
    const auto t2 = std::chrono::steady_clock::now();

    // Optional self-check: every emitted pair really satisfies u^2+v^2 square.
    uint64_t bad = 0;
    for (const Pair& p : pairs)
        if (!is_square((uint64_t)p.first * p.first + (uint64_t)p.second * p.second)) ++bad;

    const size_t count = pairs.size();
    const double secEnum = std::chrono::duration<double>(t1 - t0).count();
    const double secSort = std::chrono::duration<double>(t2 - t1).count();
    const double secTot  = std::chrono::duration<double>(t2 - t0).count();

    // ---------------- output ----------------
    if (outPath.empty()) {
        for (const Pair& p : pairs) std::printf("%u %u\n", p.first, p.second);
    } else {
        FILE* f = std::fopen(outPath.c_str(), "wb");
        if (!f) { std::fprintf(stderr, "cannot open %s\n", outPath.c_str()); return 1; }
        // Buffered manual formatting: fast for multi-million line files.
        const size_t BUFSZ = 1u << 22;
        std::vector<char> buf(BUFSZ);
        size_t pos = 0;
        for (const Pair& p : pairs) {
            if (pos + 64 > BUFSZ) { std::fwrite(buf.data(), 1, pos, f); pos = 0; }
            char tmp[24]; int len = 0;
            uint32_t vals[2] = {p.first, p.second};
            for (int s = 0; s < 2; ++s) {
                uint32_t x = vals[s];
                char r[12]; int rl = 0;
                do { r[rl++] = (char)('0' + x % 10); x /= 10; } while (x);
                while (rl) tmp[len++] = r[--rl];
                tmp[len++] = (s == 0) ? ' ' : '\n';
            }
            std::memcpy(buf.data() + pos, tmp, (size_t)len);
            pos += (size_t)len;
        }
        if (pos) std::fwrite(buf.data(), 1, pos, f);
        std::fclose(f);
    }

    if (!quiet) {
        std::fprintf(stderr, "brute_pairs N=%llu mode=%s\n",
                     (unsigned long long)N, viaTriples ? "via-triples (classical m,n,k)"
                                                       : "divisor/factorisation");
        std::fprintf(stderr, "pairs written      : %zu\n", count);
        if (!outPath.empty()) std::fprintf(stderr, "output file        : %s\n", outPath.c_str());
        std::fprintf(stderr, "self-check failures: %llu\n", (unsigned long long)bad);
        std::fprintf(stderr, "enumerate time     : %.3f s\n", secEnum);
        std::fprintf(stderr, "sort/dedup time    : %.3f s\n", secSort);
        std::fprintf(stderr, "elapsed wall time  : %.3f s\n", secTot);
    }
    return 0;
}
