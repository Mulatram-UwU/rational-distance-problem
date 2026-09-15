// fast_search2.cpp
// ---------------------------------------------------------------------------
// Memory-optimised version of fast_search.cpp (same mathematics; see the header
// of fast_search.cpp and notes/reduction.md for the reduction and the lemmas).
//
// Two changes versus v1, both needed to reach much larger Q-ranges:
//   1. The partner table stores, for each C, only partners A with A <= N/2.
//      This is complete: the pair loop needs A, B in T(C) with A + B = Q <= N,
//      so A < B <= N/2 necessarily.  Lists are therefore half as long and the
//      CSR offsets fit in 32 bits.
//   2. Membership "D in T(A)" is no longer a table lookup (D can exceed N/2 and
//      would have been truncated); it is decided by an exact integer square
//      test A^2 + D^2 == square, which is just as fast.
//   The pairs themselves are enumerated twice (count, then fill) so that the
//   8-bytes-per-pair scratch vector of v1 is not needed.
//
// Build: g++ -O2 -march=native -fopenmp -std=c++17 -o fast_search2 fast_search2.cpp
// Run:   fast_search2 --N 300000000
// ---------------------------------------------------------------------------

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cmath>
#include <string>
#include <vector>
#include <algorithm>
#include <chrono>

#ifdef _OPENMP
#include <omp.h>
#endif

typedef uint32_t u32;
typedef uint64_t u64;

static inline bool isSquare(u64 n) {
    if (n == 0) return true;
    u64 r = (u64)sqrtl((long double)n);
    while (r > 0 && r * r > n) --r;
    while ((r + 1) * (r + 1) <= n) ++r;
    return r * r == n;
}

static u64 gcd64(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }

// f(a,b) is called once for every pair 1 <= a < b <= N with a^2 + b^2 a square.
template <class F>
static void forEachPythagPair(u64 N, F f) {
    u64 mMax = (u64)sqrtl(1.21L * (long double)N) + 2;
    for (u64 m = 2; m <= mMax; ++m) {
        for (u64 n = 1 + (m & 1); n < m; n += 2) {
            if (gcd64(m, n) != 1) continue;
            u64 p = m * m - n * n, q = 2 * m * n;
            if (p > N || q > N) continue;
            u64 kMax = std::min(N / p, N / q);
            for (u64 k = 1; k <= kMax; ++k) {
                u32 u = (u32)(k * p), v = (u32)(k * q);
                if (u < v) f(u, v); else f(v, u);
            }
        }
    }
}

int main(int argc, char **argv) {
    u64 N = 1000000;
    bool useParity = true, useMod3 = false, threeCond = false, dump = false;
    std::string dumpFile;
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--N") && i + 1 < argc) N = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "--no-parity")) useParity = false;
        else if (!strcmp(argv[i], "--mod3")) useMod3 = true;
        else if (!strcmp(argv[i], "--three")) threeCond = true;
        else if (!strcmp(argv[i], "--dump-pairs") && i + 1 < argc) { dump = true; dumpFile = argv[++i]; }
        else { fprintf(stderr, "unknown arg %s\n", argv[i]); return 2; }
    }
    auto t0 = std::chrono::steady_clock::now();

    if (dump) {   // independent output path for cross-checking enumerations
        FILE *fp = fopen(dumpFile.c_str(), "w");
        if (!fp) { fprintf(stderr, "cannot open %s\n", dumpFile.c_str()); return 1; }
        u64 cnt = 0;
        forEachPythagPair(N, [&](u32 a, u32 b) { fprintf(fp, "%u %u\n", a, b); cnt++; });
        fclose(fp);
        printf("dumped %llu pairs to %s\n", (unsigned long long)cnt, dumpFile.c_str());
        return 0;
    }

    // The table must contain *every* partner <= N of C: the pair loop needs
    // A + B = Q <= N, so B can be as large as N-1 (only A < Q/2 <= N/2 is
    // forced).  Truncating to partners <= N/2 would therefore lose genuine
    // solutions with B > N/2, so cap = N.
    const u32 cap = (u32)std::min<u64>(N, 4000000000ull);
    // entries of the table: partner b of a is stored iff b <= cap (a <= N)
    std::vector<u32> off(N + 2, 0);          // counts first, then offsets
    u64 entries = 0;
    forEachPythagPair(N, [&](u32 a, u32 b) {
        if (b <= cap) off[a]++;
        if (a <= cap) off[b]++;
    });
    {   // prefix sums in place
        u64 acc = 0;
        for (u64 u = 1; u <= N; ++u) { u32 c = off[u]; off[u] = (u32)acc; acc += c; }
        off[N + 1] = (u32)acc;
        entries = acc;
    }
    std::vector<u32> cur(off.begin(), off.begin() + N + 1);
    std::vector<u32> data(entries);
    forEachPythagPair(N, [&](u32 a, u32 b) {
        if (b <= cap) data[cur[a]++] = b;
        if (a <= cap) data[cur[b]++] = a;
    });
    cur.clear(); cur.shrink_to_fit();
    for (u64 u = 1; u <= N; ++u)
        std::sort(data.begin() + off[u], data.begin() + off[u + 1]);

    auto t1 = std::chrono::steady_clock::now();
    fprintf(stderr, "[build] N=%llu entries=%llu %.2fs\n",
            (unsigned long long)N, (unsigned long long)entries,
            std::chrono::duration<double>(t1 - t0).count());

    std::vector<std::string> solutions;
    u64 candidates = 0, tested = 0, survivors = 0;

#ifdef _OPENMP
    int nthreads = omp_get_max_threads();
#else
    int nthreads = 1;
#endif
    std::vector<std::vector<std::string>> local(nthreads);

#pragma omp parallel for schedule(dynamic, 256) reduction(+:candidates,tested,survivors)
    for (long long C = 1; C <= (long long)N; ++C) {
#ifdef _OPENMP
        int tid = omp_get_thread_num();
#else
        int tid = 0;
#endif
        u64 nc = 0, nt = 0, ns = 0;
        u64 lo = off[C], hi = off[C + 1], k = hi - lo;
        const u32 *L = data.data() + lo;
        for (u64 i = 0; i < k; ++i) {
            u32 A = L[i];
            for (u64 j = i + 1; j < k; ++j) {
                u32 B = L[j];
                u64 Q = (u64)A + B;
                if (Q > N) break;         // list is ascending
                if (Q <= (u64)C) continue;    // D = Q - C would be <= 0
                nc++;
                u32 D = (u32)(Q - (u64)C);
                if (useParity) {
                    bool ok;
                    if ((A & 1) && (B & 1) && !((u32)C & 3) && !(D & 3)) ok = true;
                    else if (((u32)C & 1) && (D & 1) && !(A & 3) && !(B & 3)) ok = true;
                    else ok = false;
                    if (!ok) continue;
                }
                if (useMod3) {
                    bool ok = ((A % 3 == 0) && (B % 3 == 0)) ||
                              (((u32)C % 3 == 0) && (D % 3 == 0));
                    if (!ok) continue;
                }
                ns++; nt++;
                bool okAD = isSquare((u64)A * A + (u64)D * D);
                bool okBD = threeCond ? true : isSquare((u64)B * B + (u64)D * D);
                if (okAD && okBD) {
                    char buf[160];
                    snprintf(buf, sizeof buf, "SOLUTION Q=%llu A=%u B=%u C=%u D=%u  (x=%llu/%llu,y=%u/%llu)",
                             (unsigned long long)Q, A, B, (u32)C, D,
                             (unsigned long long)A, (unsigned long long)Q,
                             (u32)C, (unsigned long long)Q);
                    local[tid].push_back(buf);
                }
            }
        }
        candidates += nc; tested += nt; survivors += ns;
    }
    for (int t = 0; t < nthreads; ++t)
        for (auto &s : local[t]) solutions.push_back(s);

    auto t2 = std::chrono::steady_clock::now();
    printf("N=%llu entries=%llu candidates=%llu survivors=%llu tested=%llu solutions=%zu\n",
           (unsigned long long)N, (unsigned long long)entries,
           (unsigned long long)candidates, (unsigned long long)survivors,
           (unsigned long long)tested, solutions.size());
    for (auto &s : solutions) printf("%s\n", s.c_str());
    fflush(stdout);
    fprintf(stderr, "[search] %.2fs total %.2fs threads=%d parity=%s mod3=%s three=%s\n",
            std::chrono::duration<double>(t2 - t1).count(),
            std::chrono::duration<double>(t2 - t0).count(), nthreads,
            useParity ? "on" : "off", useMod3 ? "on" : "off", threeCond ? "on" : "off");
    return 0;
}
