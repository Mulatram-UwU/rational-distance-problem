// ---------------------------------------------------------------------------
// brute.cpp -- INDEPENDENT brute-force search for the rational distance problem
// ---------------------------------------------------------------------------
// Object of study:
//   A point P=(x,y) strictly inside the unit square has rational distance to
//   all four vertices iff, writing x = A/Q, y = C/Q with integers
//   0 < A,B,C,D < Q, A+B = Q, C+D = Q, the four integers
//        A^2+C^2,  B^2+C^2,  A^2+D^2,  B^2+D^2
//   are all perfect squares.  (dist^2 to (0,0) = (A^2+C^2)/Q^2, etc.)
//   Recovering the point:  (x,y) = (A/Q, C/Q),  B = Q-A,  D = Q-C.
//
// This program simply enumerates EVERY quadruple (Q,A,C) with 1 <= A,C <= Q-1
// (so that 0 < B,D < Q) for Q = 1..N and tests the four conditions with exact
// integer arithmetic.  It makes no use of any Pythagorean-triple structure,
// no divisor tricks, no algebra -- it is a pure "try everything" search, so it
// is genuinely independent evidence about the search space.
//
// Usage:
//   brute <N> [--symmetric] [--threads T]
//
//   --symmetric : also admit the degenerate/boundary cases B = 0 or D = 0,
//                 i.e. also test A in {0,Q} and C in {0,Q} (points on the
//                 boundary of the square).  Expected to find nothing either.
//
// Exact integer square root
// -------------------------
// All perfect-square tests go through isqrt_u64(), never through floating point
// comparisons.  Two implementations are used:
//
//   * For n < 2^52 we take the IEEE-754 double sqrt as a *seed only*:
//     n < 2^52 is exactly representable as a double, and the hardware sqrtsd
//     with default rounding is correctly rounded, so
//        | (double)sqrt(n) - sqrt(n) | <= 1/2 ulp <= 1
//     hence | floor(sqrt(n)) - (uint64_t)(double)sqrt(n) | <= 1.
//     The seed is therefore within +-1 of the true value, and the answer is
//     then CORRECTED with pure integer arithmetic:
//        while (r > 0 && r*r >  n) --r;
//        while ((r+1)*(r+1) <= n) ++r;
//     which is a verified loop (each step is an exact integer comparison), so
//     the returned r satisfies r*r <= n < (r+1)*(r+1) = floor(sqrt(n)) exactly,
//     whatever the seed was.  The seed only affects the loop count, never the
//     result.  No overflow: r <= 2^26 + 1 here, so r*r < 2^53.
//
//   * For n >= 2^52 (never reached in this program, kept for completeness) we
//     use a pure-integer restoring square root, 32 iterations of
//        t = r | (1<<b);  if (t*t <= n) r = t;
//     tested with the overflow-free division form  t <= n/t, which is
//     equivalent to t*t <= n for t > 0.  This is exact for every uint64 n by
//     construction (it finds the largest r with r*r <= n, bit by bit).
//
// Compile:
//   g++ -O2 -march=native -fopenmp -std=c++17 -o brute brute.cpp
// ---------------------------------------------------------------------------

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cmath>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <chrono>

#ifdef _OPENMP
#include <omp.h>
#endif

// ---------------------------------------------------------------------------
// Exact integer square root (see the long comment above for the proof).
// ISQRT_PURE_INT=1 (compile with -DISQRT_PURE_INT=1) disables the floating
// seed entirely and always uses the pure-integer restore loop; the results are
// then provably free of any floating-point influence, at some cost in speed.
// ---------------------------------------------------------------------------
#ifndef ISQRT_PURE_INT
#define ISQRT_PURE_INT 0
#endif

static inline uint64_t isqrt_u64(uint64_t n) {
    if (n == 0) return 0;
    if (!ISQRT_PURE_INT && n < (1ULL << 52)) {
        // Seed from hardware sqrt, then repair with exact integer comparisons.
        uint64_t r = (uint64_t)std::sqrt((double)n);
        while (r > 0 && r * r > n) --r;            // exact: r*r fits in uint64
        while ((r + 1) * (r + 1) <= n) ++r;        // exact: (r+1)^2 < 2^53
        return r;
    }
    // Pure-integer fallback, exact for the whole uint64 range.
    uint64_t r = 0;
    for (int b = 31; b >= 0; --b) {
        uint64_t t = r | (1ULL << b);
        if (t <= n / t) r = t;                     // t*t <= n, overflow-free
    }
    return r;
}

static inline bool is_square(uint64_t n) {
    const uint64_t r = isqrt_u64(n);
    return r * r == n;                             // r*r <= n, cannot overflow
}

struct Solution {
    uint64_t Q, A, C, B, D;
};

int main(int argc, char** argv) {
    if (argc < 2) {
        std::fprintf(stderr,
            "usage: %s <N> [--symmetric] [--threads T]\n", argv[0]);
        return 2;
    }
    uint64_t N = std::strtoull(argv[1], nullptr, 10);
    bool symmetric = false;
    int threads = 0;
    for (int i = 2; i < argc; ++i) {
        if (std::strcmp(argv[i], "--symmetric") == 0) symmetric = true;
        else if (std::strcmp(argv[i], "--threads") == 0 && i + 1 < argc)
            threads = std::atoi(argv[++i]);
        else { std::fprintf(stderr, "unknown argument: %s\n", argv[i]); return 2; }
    }

    std::printf("=== brute.cpp  N=%llu  mode=%s ===\n",
                (unsigned long long)N, symmetric ? "symmetric (boundary allowed)"
                                                 : "strict interior");

    // Candidate ranges: strict interior needs 1 <= A,C <= Q-1; symmetric mode
    // also allows A or C equal to 0 or Q (B = 0 or D = 0, points on the edge).
    const uint64_t lo = symmetric ? 0 : 1;

    std::vector<Solution> solutions;
    unsigned long long candidates = 0;
    double elapsed = 0.0;

#ifdef _OPENMP
    if (threads > 0) omp_set_num_threads(threads);
    const double t0 = omp_get_wtime();
#else
    (void)threads;
    const auto t0 = std::chrono::steady_clock::now();
#endif

    // Naive triple loop over Q, A, C.  Parallelised over Q only, so that the
    // per-thread work is a contiguous, reproducible set of Q values; the
    // solution list is sorted at the end, hence the output is deterministic.
    long long localCand = 0;
#ifdef _OPENMP
    #pragma omp parallel reduction(+:localCand)
    {
        std::vector<Solution> mine;
        #pragma omp for schedule(dynamic, 1)
        for (long long Ql = 1; Ql <= (long long)N; ++Ql) {
            const uint64_t Q = (uint64_t)Ql;
            for (uint64_t A = lo; A + lo <= Q; ++A) {
                const uint64_t B = Q - A;
                const uint64_t A2 = A * A, B2 = B * B;
                for (uint64_t C = lo; C + lo <= Q; ++C) {
                    const uint64_t D = Q - C;
                    ++localCand;
                    if (!is_square(A2 + C * C)) continue;   // |P-(0,0)|
                    if (!is_square(B2 + C * C)) continue;   // |P-(1,0)|
                    if (!is_square(A2 + D * D)) continue;   // |P-(0,1)|
                    if (!is_square(B2 + D * D)) continue;   // |P-(1,1)|
                    mine.push_back(Solution{Q, A, C, B, D});
                }
            }
        }
        #pragma omp critical
        solutions.insert(solutions.end(), mine.begin(), mine.end());
    }
#else
    for (uint64_t Q = 1; Q <= N; ++Q) {
        for (uint64_t A = lo; A + lo <= Q; ++A) {
            const uint64_t B = Q - A;
            const uint64_t A2 = A * A, B2 = B * B;
            for (uint64_t C = lo; C + lo <= Q; ++C) {
                const uint64_t D = Q - C;
                ++localCand;
                if (!is_square(A2 + C * C)) continue;
                if (!is_square(B2 + C * C)) continue;
                if (!is_square(A2 + D * D)) continue;
                if (!is_square(B2 + D * D)) continue;
                solutions.push_back(Solution{Q, A, C, B, D});
            }
        }
    }
#endif
    candidates = (unsigned long long)localCand;

#ifdef _OPENMP
    elapsed = omp_get_wtime() - t0;
#else
    elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
#endif

    // Deterministic output ordering.
    std::sort(solutions.begin(), solutions.end(),
              [](const Solution& p, const Solution& q) {
                  if (p.Q != q.Q) return p.Q < q.Q;
                  if (p.A != q.A) return p.A < q.A;
                  return p.C < q.C;
              });

    for (const Solution& s : solutions) {
        std::printf("SOLUTION Q A C B D = %llu %llu %llu %llu %llu"
                    "   (x=%llu/%llu, y=%llu/%llu)\n",
                    (unsigned long long)s.Q, (unsigned long long)s.A,
                    (unsigned long long)s.C, (unsigned long long)s.B,
                    (unsigned long long)s.D,
                    (unsigned long long)s.A, (unsigned long long)s.Q,
                    (unsigned long long)s.C, (unsigned long long)s.Q);
    }

    std::printf("candidates tested : %llu\n", candidates);
    std::printf("solutions found   : %llu\n", (unsigned long long)solutions.size());
#ifdef _OPENMP
    std::printf("threads           : %d\n", omp_get_max_threads());
#endif
    std::printf("elapsed wall time : %.3f s\n", elapsed);
    return 0;
}
