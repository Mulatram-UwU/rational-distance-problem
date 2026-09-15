// fast_search.cpp
// ---------------------------------------------------------------------------
// Complete search for a point strictly inside the unit square at rational
// distance from all four vertices ("rational distance problem", interior case).
//
// REDUCTION (proved in notes/reduction.md):
//   P = (x,y) inside the square has all four distances rational
//     <=>  x = A/Q, y = C/Q with integers Q > 0, 0 < A,B,C,D < Q,
//          A + B = Q,  C + D = Q,  and the four integers
//             A^2 + C^2,  B^2 + C^2,  A^2 + D^2,  B^2 + D^2
//          are all perfect squares.
//   ("=>" uses that x = (a^2-b^2+1)/2 and y = (a^2-c^2+1)/2 for the squared
//    distances a^2,b^2,c^2 so x,y are rational; "<=" is immediate.)
//   Every rational point is representable with common denominator
//   Q = lcm(den x, den y); hence searching all Q <= N covers exactly the
//   rational points with lcm(den x, den y) <= N.
//
// ALGORITHM (why this is fast):
//   Let T(u) = { v : 1 <= v <= N, u^2 + v^2 is a perfect square }.
//   The conditions say   A,B in T(C)  and   A,B in T(D)  with A+B = C+D = Q.
//   So: enumerate C; enumerate pairs A < B in T(C) with A+B <= N; put
//   Q = A+B and D = Q-C; then only D in T(A) and D in T(B) remain to check.
//   Cost is sum_C |T(C)|^2 (instead of O(N^2) for a scan over (x,y)), and the
//   tables T(.) are built by enumerating Pythagorean triples: O(#pairs).
//
// PARITY LEMMA (proved in notes/reduction.md, used as a filter):
//   If all four of A^2+C^2, B^2+C^2, A^2+D^2, B^2+D^2 are squares and A+B=C+D
//   then either A,B,C,D are all even, or
//       (A,B odd and 4 | C, 4 | D)   or   (C,D odd and 4 | A, 4 | B).
//   Dividing an all-even solution by 2 gives another solution with Q/2, so the
//   search may restrict itself to the two odd patterns without losing
//   solutions (the descent terminates at a primitive solution, which is found
//   at its own, smaller Q).  Flag --no-parity disables the filter; both modes
//   must agree on every N tested.
//
// All arithmetic is exact integer arithmetic (unsigned 64-bit); square tests
// are exact (integer square root with correction loop).
//
// Build: g++ -O2 -march=native -fopenmp -o fast_search fast_search.cpp
// Run:   fast_search --N 1000000
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

// ----------------------------- exact square test ---------------------------
static inline bool isSquare(u64 n) {
    if (n == 0) return true;
    u64 r = (u64)sqrtl((long double)n);
    while (r > 0 && r * r > n) --r;
    while ((r + 1) * (r + 1) <= n) ++r;
    return r * r == n;
}

// ----------------------------- CSR partner table ---------------------------
// T(u) for u in 1..N is stored sorted ascending in data[off[u] .. off[u+1]).
struct PartnerTable {
    u64 N = 0;
    std::vector<u64> off;    // size N+2
    std::vector<u32> data;

    // binary search: is v in T(u) ?
    inline bool contains(u32 u, u32 v) const {
        const u32 *b = data.data() + off[u];
        const u32 *e = data.data() + off[u + 1];
        return std::binary_search(b, e, v);
    }
    inline u64 size(u32 u) const { return off[u + 1] - off[u]; }
};

// Enumerate every (u,v) with 1<=u,v<=N and u^2+v^2 a perfect square, by
// running over primitive Pythagorean triples (legs m^2-n^2, 2mn, hypotenuse
// m^2+n^2) and all their scalings k.
static u64 gcd64(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }

static void buildPartners(u64 N, PartnerTable &T, u64 &pairCount,
                          const std::string &dumpFile) {
    // both legs <= N forces m <= sqrt((1+sqrt2)/2 * N) + 2; every triple is a
    // scaling of a primitive one, so only primitive (m,n) need to be visited.
    u64 mMax = (u64)sqrtl(1.21L * (long double)N) + 2;
    std::vector<std::pair<u32,u32>> pairs;   // u < v, canonical
    pairs.reserve(1u << 20);

    for (u64 m = 2; m <= mMax; ++m) {
        for (u64 n = 1 + (m & 1); n < m; n += 2) {   // m - n odd
            if (gcd64(m, n) != 1) continue;
            u64 p = m * m - n * n;      // odd leg
            u64 q = 2 * m * n;          // even leg
            if (p > N || q > N) continue;      // no scaling fits
            u64 kMax = std::min(N / p, N / q);
            for (u64 k = 1; k <= kMax; ++k) {
                u32 u = (u32)(k * p), v = (u32)(k * q);
                u32 a = std::min(u, v), b = std::max(u, v);
                pairs.push_back({a, b});
            }
        }
    }
    pairCount = pairs.size();

    T.N = N;
    T.off.assign(N + 2, 0);
    std::vector<u64> c2(N + 2, 0);
    for (auto &pr : pairs) { c2[pr.first]++; c2[pr.second]++; }
    u64 acc = 0;
    for (u64 u = 1; u <= N; ++u) { T.off[u] = acc; acc += c2[u]; }
    T.off[N + 1] = acc;
    T.data.assign(acc, 0);
    std::vector<u64> pos(N + 1);
    for (u64 u = 1; u <= N; ++u) pos[u] = T.off[u];
    for (auto &pr : pairs) {
        T.data[pos[pr.first]++]  = pr.second;
        T.data[pos[pr.second]++] = pr.first;
    }
    for (u64 u = 1; u <= N; ++u)
        std::sort(T.data.begin() + T.off[u], T.data.begin() + T.off[u + 1]);

    if (!dumpFile.empty()) {
        FILE *f = fopen(dumpFile.c_str(), "w");
        if (f) {
            for (auto &pr : pairs) fprintf(f, "%u %u\n", pr.first, pr.second);
            fclose(f);
        }
    }
}

// ------------------------------- parity filter -----------------------------
// accepts exactly the two primitive patterns of the parity lemma
static inline bool parityOK(u32 A, u32 B, u32 C, u32 D) {
    bool Aodd = (A & 1), Bodd = (B & 1), Codd = (C & 1), Dodd = (D & 1);
    if (Aodd && Bodd && !(C & 3) && !(D & 3)) return true;
    if (Codd && Dodd && !(A & 3) && !(B & 3)) return true;
    return false;
}

int main(int argc, char **argv) {
    u64 N = 100000;
    bool useParity = true, threeCond = false, quiet = false;
    std::string dumpFile;
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--N") && i + 1 < argc) N = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "--no-parity")) useParity = false;
        else if (!strcmp(argv[i], "--three")) threeCond = true;
        else if (!strcmp(argv[i], "--quiet")) quiet = true;
        else if (!strcmp(argv[i], "--dump-pairs") && i + 1 < argc) dumpFile = argv[++i];
        else { fprintf(stderr, "unknown arg %s\n", argv[i]); return 2; }
    }

    auto t0 = std::chrono::steady_clock::now();
    PartnerTable T;
    u64 pairCount = 0;
    buildPartners(N, T, pairCount, dumpFile);
    auto t1 = std::chrono::steady_clock::now();
    if (!quiet) {
        fprintf(stderr, "[build] N=%llu  pairs(u<v)=%llu  table entries=%llu  %.2fs\n",
                (unsigned long long)N, (unsigned long long)pairCount,
                (unsigned long long)T.off[N + 1],
                std::chrono::duration<double>(t1 - t0).count());
    }

    std::vector<std::string> solutions;
    u64 candidates = 0, tested = 0, survivedParity = 0;

#ifdef _OPENMP
    int nthreads = omp_get_max_threads();
#else
    int nthreads = 1;
#endif
    std::vector<std::vector<std::string>> local(nthreads);
    std::vector<u64> locCand(nthreads, 0), locTest(nthreads, 0), locSurv(nthreads, 0);

#pragma omp parallel for schedule(dynamic, 64) reduction(+:candidates,tested,survivedParity)
    for (long long C = 1; C <= (long long)N; ++C) {
#ifdef _OPENMP
        int tid = omp_get_thread_num();
#else
        int tid = 0;
#endif
        u64 nc = 0, nt = 0, ns = 0;
        u64 lo = T.off[C], hi = T.off[C + 1];
        u64 k = hi - lo;
        const u32 *L = T.data.data() + lo;
        for (u64 i = 0; i < k; ++i) {
            u32 A = L[i];
            for (u64 j = i + 1; j < k; ++j) {
                u32 B = L[j];
                u64 Q = (u64)A + B;
                if (Q > N) break;                 // list ascending
                if (Q <= C) continue;             // would give D <= 0
                nc++;
                u32 D = (u32)(Q - C);
                if (useParity && !parityOK(A, B, (u32)C, D)) continue;
                ns++;
                nt++;
                bool okAD = T.contains(A, D);
                bool okBD = threeCond ? true : T.contains(B, D);
                if (okAD && okBD) {
                    char buf[160];
                    snprintf(buf, sizeof buf,
                             "SOLUTION Q=%llu A=%u B=%u C=%u D=%u  (x=%llu/%llu, y=%u/%llu)",
                             (unsigned long long)Q, A, B, (u32)C, D,
                             (unsigned long long)A, (unsigned long long)Q,
                             (u32)C, (unsigned long long)Q);
                    local[tid].push_back(buf);
                }
            }
        }
        locCand[tid] += nc; locTest[tid] += nt; locSurv[tid] += ns;
        candidates += nc; tested += nt; survivedParity += ns;
    }
    for (int t = 0; t < nthreads; ++t)
        for (auto &s : local[t]) solutions.push_back(s);
    (void)locCand; (void)locTest; (void)locSurv;

    auto t2 = std::chrono::steady_clock::now();
    printf("N=%llu pairs=%llu candidates=%llu parity_survivors=%llu tested=%llu solutions=%zu\n",
           (unsigned long long)N, (unsigned long long)pairCount,
           (unsigned long long)candidates, (unsigned long long)survivedParity,
           (unsigned long long)tested, solutions.size());
    for (auto &s : solutions) printf("%s\n", s.c_str());
    fflush(stdout);
    fprintf(stderr, "[search] %.2fs  total %.2fs  threads=%d  parity=%s three=%s\n",
            std::chrono::duration<double>(t2 - t1).count(),
            std::chrono::duration<double>(t2 - t0).count(),
            nthreads, useParity ? "on" : "off", threeCond ? "on" : "off");
    return 0;
}
