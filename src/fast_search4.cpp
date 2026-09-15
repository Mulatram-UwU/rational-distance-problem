// fast_search4.cpp
// ---------------------------------------------------------------------------
// Engine v4 -- same decision procedure as fast_search3.cpp, restructured so
// that N = 2*10^10 is reachable at all.  Two things break in v3 at that size:
//
//   (1) memory: v3 sieves the least prime factor of every C <= N into a u16
//       array, 2 bytes per entry = 40 GB at N = 2*10^10.  (And u16 would no
//       longer be enough either: sqrt(2*10^10) = 141422 > 65535.)  v4 keeps
//       no global table: C runs over segments [lo,hi) and a segmented
//       residual sieve factorises every C of the segment, so peak memory is
//       O(segment) instead of O(N).
//
//   (2) overflow: the divisor walk of v3 forms C*C in u64.  C = 2*10^10 gives
//       C^2 = 4.0*10^20 > 2^64.  v4 never forms C^2.  A divisor u of C^2 with
//       u <= C is built multiplicatively, and its complement v = C^2/u is
//       built at the same time from the *complementary* exponents,
//       v = prod p^(2e-f); both are capped with a 128-bit compare, so the
//       walk needs neither a 64x64->128 division nor a 128-bit square root.
//       The cap comes from the observation that a partner A = (v-u)/2 is only
//       useful when A <= N, i.e. v <= 2N+u <= 3N; a node whose complement
//       product already exceeds that is pruned with its whole subtree, because
//       the complement only grows as the walk descends.
//
// On top of that the pair loop is reorganised.  v3 enumerated all C(k,2)
// pairs of T(C) and threw away ~94% of them inside the loop.  The two local
// necessary conditions (notes/reduction.md):
//
//   Lemma 4 (parity).  If A,B,C,D are not all even then either
//       A,B odd and 4|C, 4|D,   or   C,D odd and 4|A, 4|B.
//   Lemma 5 (mod 3).   3 | Q,  and more precisely 3|A and 3|B, or 3|C and 3|D.
//
// pin the pair (A mod 12, B mod 12) down to a handful of classes once C mod 12
// is known, and they rule C = 2 (mod 4) out completely (Lemma 4 needs C = 0
// (mod 4), Lemma 5's second case needs C odd).  So v4 skips those C outright
// and, for the others, only visits pairs that can possibly pass.  Lemma 5 is a
// *necessary* condition, so the decision is unchanged; --no-mod3 keeps only
// the parity classes, which reproduces v3's `tested` count exactly and lets
// the two engines be compared number for number.
//
// Build: g++ -O3 -march=native -fopenmp -std=c++17 -o bin/fast_search4.exe src/fast_search4.cpp
// Run:   ./bin/fast_search4.exe --N 20000000000
//        ./bin/fast_search4.exe --N 100000000 --no-mod3      (v3's filter set)
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
#include <atomic>

#ifdef _OPENMP
#include <omp.h>
#endif

typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t  u8;
typedef unsigned __int128 u128;

static bool SQ64[64];

static inline void initSq64(void) {
    for (int i = 0; i < 64; ++i) SQ64[(u64)i * i % 64] = true;
}

// exact, rejects ~81% of non-squares before doing any square root
static inline bool isSquare128(u128 n) {
    if (n == 0) return true;
    if (!SQ64[(u64)n & 63]) return false;
    u64 r = (u64)sqrt((double)n);
    while ((u128)r * r > n) --r;
    while ((u128)(r + 1) * (r + 1) <= n) ++r;
    return (u128)r * r == n;
}

static inline u64 isqrt128(u128 n) {
    if (n == 0) return 0;
    u64 r = (u64)sqrt((double)n);
    while ((u128)r * r > n) --r;
    while ((u128)(r + 1) * (r + 1) <= n) ++r;
    return r;
}

// ---------------------------------------------------------------------------
// residue classes (A mod 12, B mod 12) compatible with the local conditions,
// indexed by C mod 12.  r == s means "pairs inside that one class, A < B".
// ---------------------------------------------------------------------------
struct ClassList { int n; int r[12]; int s[12]; };

// parity and 3 | Q, i.e. Lemmas 4 and 5 together
static const ClassList CLASSES_M3[12] = {
    /* C=0  : 4|C, 3|C  */ {3, {1, 3, 5}, {11, 9, 7}},
    /* C=1  : odd, 3 nm  */ {1, {0},       {0}},
    /* C=2  : ruled out  */ {0, {0},       {0}},
    /* C=3  : odd, 3|C   */ {2, {0, 4},    {0, 8}},
    /* C=4  : 4|C, 3 nm  */ {1, {3},       {9}},
    /* C=5  : odd, 3 nm  */ {1, {0},       {0}},
    /* C=6  : ruled out  */ {0, {0},       {0}},
    /* C=7  : odd, 3 nm  */ {1, {0},       {0}},
    /* C=8  : 4|C, 3 nm  */ {1, {3},       {9}},
    /* C=9  : odd, 3|C   */ {2, {0, 4},    {0, 8}},
    /* C=10 : ruled out  */ {0, {0},       {0}},
    /* C=11 : odd, 3 nm  */ {1, {0},       {0}},
};

// parity alone (exactly v3's filter, which is also Lemma 4's (P1) v (P2))
static const ClassList CLASSES_PAR[12] = {
    /* C=0  */ {9, {1, 1, 1, 3, 3, 5, 5, 7, 9}, {3, 7, 11, 5, 9, 7, 11, 9, 11}},
    /* C=1  */ {6, {0, 0, 0, 4, 4, 8},           {0, 4, 8, 4, 8, 8}},
    /* C=2  */ {0, {0},                          {0}},
    /* C=3  */ {6, {0, 0, 0, 4, 4, 8},           {0, 4, 8, 4, 8, 8}},
    /* C=4  */ {9, {1, 1, 1, 3, 3, 5, 5, 7, 9}, {3, 7, 11, 5, 9, 7, 11, 9, 11}},
    /* C=5  */ {6, {0, 0, 0, 4, 4, 8},           {0, 4, 8, 4, 8, 8}},
    /* C=6  */ {0, {0},                          {0}},
    /* C=7  */ {6, {0, 0, 0, 4, 4, 8},           {0, 4, 8, 4, 8, 8}},
    /* C=8  */ {9, {1, 1, 1, 3, 3, 5, 5, 7, 9}, {3, 7, 11, 5, 9, 7, 11, 9, 11}},
    /* C=9  */ {6, {0, 0, 0, 4, 4, 8},           {0, 4, 8, 4, 8, 8}},
    /* C=10 */ {0, {0},                          {0}},
    /* C=11 */ {6, {0, 0, 0, 4, 4, 8},           {0, 4, 8, 4, 8, 8}},
};

static const int MAXF = 10;   // omega(n) <= 10 for n <= 2e10 (2*3*...*29 <= 2e10 < 2*3*...*31)
static const int MAXE = 72;   // 2 * v_2(n) + 1 for n <= 2e10

struct Worker {
    u64 N, VMAX;
    bool useMod3, statsOnly, dumpC;

    u64 C;
    int nf;
    u64 pr[12];
    int ex[12];
    u64 pwv[12][MAXE];        // pwv[i][t] = min(pr[i]^t, VMAX+1)

    std::vector<u64> lst;
    std::vector<u64> buck[12];

    u64 cSteps, cPartners, cCand, cTest, cSol, maxPart;
    std::vector<std::string> sols;

    void fillPowers(void) {
        for (int i = 0; i < nf; ++i) {
            u64 p = pr[i], cap = VMAX + 1, cur = 1;
            int e2 = 2 * ex[i], t = 0;
            for (; t <= e2; ++t) {
                pwv[i][t] = cur;
                if (t == e2) break;
                if (cur > cap / p) break;
                cur *= p;
            }
            for (++t; t <= e2; ++t) pwv[i][t] = cap;
        }
    }

    inline void leafAdd(u64 u, u64 v) {
        if (u >= C) return;                  // need v > u, i.e. A >= 1
        if ((u ^ v) & 1) return;             // A = (v - u)/2 must be an integer
        u64 A = (v - u) >> 1;
        if (A <= N) lst.push_back(A);
    }

    void go(int idx, u64 u, u64 v) {
        ++cSteps;
        if (v > VMAX) return;                // A = (v-u)/2 > N throughout this subtree
        if (idx == nf) { leafAdd(u, v); return; }
        u64 p = pr[idx];
        int e2 = 2 * ex[idx];
        u64 ucur = u;
        for (int f = 0; f <= e2; ++f) {
            if (ucur > C) break;             // u > C: every larger f is worse
            u64 vf = pwv[idx][e2 - f];
            if (vf > VMAX) {
                go(idx + 1, ucur, VMAX + 1);
            } else {
                u128 t = (u128)vf * v;
                go(idx + 1, ucur, (t > VMAX) ? VMAX + 1 : (u64)t);
            }
            u128 t2 = (u128)ucur * p;
            if (t2 > C) break;
            ucur = (u64)t2;
        }
    }

    inline void tryPair(u64 A, u64 B) {
        u64 Q = A + B;
        if (Q <= C) return;                  // D = Q - C > 0
        u64 D = Q - C;
        ++cTest;
        if (!isSquare128((u128)A * A + (u128)D * D)) return;
        if (!isSquare128((u128)B * B + (u128)D * D)) return;
        ++cSol;
        char buf[192];
        snprintf(buf, sizeof buf,
                 "SOLUTION Q=%llu A=%llu B=%llu C=%llu D=%llu  (x=%llu/%llu,y=%llu/%llu)",
                 (unsigned long long)Q, (unsigned long long)A, (unsigned long long)B,
                 (unsigned long long)C, (unsigned long long)D,
                 (unsigned long long)A, (unsigned long long)Q,
                 (unsigned long long)C, (unsigned long long)Q);
        sols.push_back(buf);
    }

    // Valid j for a given a are those with x[j] > C-a and x[j] <= N-a.  Both
    // bounds shrink as a grows, so both pointers only ever move down.
    inline void loopSame(int r) {
        const std::vector<u64> &x = buck[r];
        long long k = (long long)x.size();
        if (k < 2) return;
        long long hi = k - 1, hc = k - 1;
        for (long long i = 0; i + 1 < k; ++i) {
            u64 a = x[i];
            if (2 * (u128)a > N) break;          // then a + x[j] > N for every j > i
            u64 limN = N - a;
            u64 limC = (C > a) ? (u64)(C - a) : 0;
            while (hi > i && x[hi] > limN) --hi;
            if (hi <= i) break;
            while (hc >= 0 && x[hc] > limC) --hc;
            long long lo = hc + 1;
            if (lo < i + 1) lo = i + 1;
            for (long long j = lo; j <= hi; ++j) tryPair(a, x[j]);
        }
    }

    inline void loopCross(int r, int s) {
        const std::vector<u64> &x = buck[r], &y = buck[s];
        long long kx = (long long)x.size(), ky = (long long)y.size();
        if (kx == 0 || ky == 0) return;
        long long hi = ky - 1, hc = ky - 1;
        for (long long i = 0; i < kx; ++i) {
            u64 a = x[i];
            if ((u128)a + y[0] > N) break;
            u64 limN = N - a;
            u64 limC = (C > a) ? (u64)(C - a) : 0;
            while (hi > 0 && y[hi] > limN) --hi;
            while (hc >= 0 && y[hc] > limC) --hc;
            long long lo = hc + 1;
            for (long long j = lo; j <= hi; ++j) tryPair(a, y[j]);
        }
    }
};

int main(int argc, char **argv) {
    u64 N = 1000000;
    bool useMod3 = true, statsOnly = false, dumpC = false;
    u64 segSize = 1u << 21;
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--N") && i + 1 < argc) N = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "--no-mod3")) useMod3 = false;
        else if (!strcmp(argv[i], "--stats")) statsOnly = true;
        else if (!strcmp(argv[i], "--dumpC")) dumpC = true;
        else if (!strcmp(argv[i], "--seg") && i + 1 < argc) segSize = strtoull(argv[++i], 0, 10);
        else { fprintf(stderr, "unknown arg %s\n", argv[i]); return 2; }
    }
    initSq64();
    const u64 VMAX = 3 * N;
    auto t0 = std::chrono::steady_clock::now();

    u64 root = isqrt128(N) + 2;
    std::vector<u32> primes;
    {
        std::vector<u8> comp(root + 1, 0);
        for (u64 i = 2; i <= root; ++i)
            if (!comp[i]) { primes.push_back((u32)i); for (u64 j = i * i; j <= root; j += i) comp[j] = 1; }
    }
    auto t1 = std::chrono::steady_clock::now();
    fprintf(stderr, "[setup] N=%llu primes<=%llu: %zu seg=%llu %.2fs\n",
            (unsigned long long)N, (unsigned long long)root, primes.size(),
            (unsigned long long)segSize,
            std::chrono::duration<double>(t1 - t0).count());

    const u64 nseg = (N + segSize - 1) / segSize;
    std::atomic<u64> doneSeg(0);
    u64 gSteps = 0, gPartners = 0, gCand = 0, gTest = 0, gSol = 0, gMaxPart = 0, gOver = 0;
    std::vector<std::string> allSols;

#ifdef _OPENMP
    int nthreads = omp_get_max_threads();
#else
    int nthreads = 1;
#endif

#pragma omp parallel
    {
        Worker W;
        W.N = N; W.VMAX = VMAX; W.useMod3 = useMod3; W.statsOnly = statsOnly; W.dumpC = dumpC;
        W.cSteps = W.cPartners = W.cCand = W.cTest = W.cSol = 0; W.maxPart = 0;
        W.lst.reserve(1 << 14);
        std::vector<u64> rem(segSize);
        std::vector<u64> fs((size_t)segSize * MAXF);
        std::vector<u8> cnt(segSize);
        u64 locMaxPart = 0, locOver = 0;

#pragma omp for schedule(dynamic, 1)
        for (long long si = 0; si < (long long)nseg; ++si) {
            u64 lo = (u64)si * segSize;
            u64 hi = lo + segSize - 1;
            if (hi > N) hi = N;
            size_t len = (size_t)(hi - lo + 1);

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
                        else ++locOver;
                        do { rem[i] /= p; } while (rem[i] % p == 0);
                    }
                }
            }

            for (size_t i = 0; i < len; ++i) {
                u64 C = lo + i;
                // C = 2 (mod 4) admits no solution (Lemma 4 needs C = 0 (mod 4),
                // Lemma 5's second case needs C odd), so the pair loop is skipped.
                // The walk is still run here so that `partners`, `divisor_steps`
                // and `candidates` keep exactly v3's meaning and can be compared.
                const bool c2mod4 = ((C & 3) == 2);
                W.C = C;
                W.nf = 0;
                for (int j = 0; j < (int)cnt[i] && W.nf < 12; ++j) {
                    u64 p = fs[i * MAXF + j], t = C; int e = 0;
                    while (t % p == 0) { t /= p; ++e; }
                    W.pr[W.nf] = p; W.ex[W.nf] = e; ++W.nf;
                }
                if (rem[i] > 1) { W.pr[W.nf] = rem[i]; W.ex[W.nf] = 1; ++W.nf; }
                if (W.nf == 0) continue;                 // C = 1
                W.fillPowers();

                W.lst.clear();
                W.go(0, 1, 1);
                if (W.lst.empty()) continue;
                W.cPartners += W.lst.size();
                if (W.lst.size() > locMaxPart) locMaxPart = W.lst.size();
                std::sort(W.lst.begin(), W.lst.end());
                if (dumpC) {
                    printf("C=%llu T:", (unsigned long long)C);
                    for (size_t t = 0; t < W.lst.size(); ++t)
                        printf(" %llu", (unsigned long long)W.lst[t]);
                    printf("\n");
                }

                // v3's `candidates`: every pair A<B of T(C) with A+B <= N and A+B > C
                {
                    long long k = (long long)W.lst.size();
                    long long hi = k - 1, hc = k - 1;
                    for (long long a = 0; a + 1 < k; ++a) {
                        u64 ai = W.lst[a];
                        if (2 * (u128)ai > N) break;
                        u64 limN = N - ai;
                        u64 limC = (C > ai) ? (u64)(C - ai) : 0;
                        while (hi > a && W.lst[hi] > limN) --hi;
                        if (hi <= a) break;
                        while (hc >= 0 && W.lst[hc] > limC) --hc;
                        long long lo = hc + 1;
                        if (lo < a + 1) lo = a + 1;
                        if (lo <= hi) W.cCand += (u64)(hi - lo + 1);
                    }
                }
                if (statsOnly) continue;
                if (c2mod4) continue;

                for (int r = 0; r < 12; ++r) W.buck[r].clear();
                for (size_t t = 0; t < W.lst.size(); ++t)
                    W.buck[W.lst[t] % 12].push_back(W.lst[t]);

                const ClassList &CL = useMod3 ? CLASSES_M3[C % 12] : CLASSES_PAR[C % 12];
                for (int c = 0; c < CL.n; ++c) {
                    if (CL.r[c] == CL.s[c]) W.loopSame(CL.r[c]);
                    else W.loopCross(CL.r[c], CL.s[c]);
                }
            }
            u64 d = ++doneSeg;
            if (d % 1000 == 0)
                fprintf(stderr, "[prog] %llu/%llu segments\n",
                        (unsigned long long)d, (unsigned long long)nseg);
        }

#pragma omp critical
        {
            gSteps += W.cSteps; gPartners += W.cPartners; gCand += W.cCand;
            gTest += W.cTest; gSol += W.cSol; gOver += locOver;
            if (locMaxPart > gMaxPart) gMaxPart = locMaxPart;
            for (auto &s : W.sols) allSols.push_back(s);
        }
    }

    auto t2 = std::chrono::steady_clock::now();
    printf("N=%llu divisor_steps=%llu partners=%llu max_partners_per_C=%llu "
           "candidates=%llu tested=%llu solutions=%llu sieve_overflow=%llu\n",
           (unsigned long long)N, (unsigned long long)gSteps,
           (unsigned long long)gPartners, (unsigned long long)gMaxPart,
           (unsigned long long)gCand, (unsigned long long)gTest,
           (unsigned long long)gSol, (unsigned long long)gOver);
    for (auto &s : allSols) printf("%s\n", s.c_str());
    fflush(stdout);
    fprintf(stderr, "[search] %.2fs total %.2fs threads=%d mod3=%s seg=%llu\n",
            std::chrono::duration<double>(t2 - t1).count(),
            std::chrono::duration<double>(t2 - t0).count(), nthreads,
            useMod3 ? "on" : "off", (unsigned long long)segSize);
    return 0;
}
