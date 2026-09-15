# What the `Q ≤ 5·10¹⁰` run costs, and why the pieces are cut the way they are

Raw output of every probe quoted here: `results/probe_cost_5e10.txt` (verbatim;
the probes ran while the main run was using ~11 of the 12 threads, so the wall
times are upper bounds — the ratios are what matters).

## The bound itself is not what makes it expensive

Same segment range, only `--N` changed (`--stats`, segments `[0,50)`, i.e. `C`
up to `1.05·10⁸`):

| `N` | `divisor_steps` | `candidates` | wall |
|---|---|---|---|
| `2·10¹⁰` | 6 894 591 912 | 258 255 121 611 | 47.8 s |
| `5·10¹⁰` | 7 265 057 364 (+5.4 %) | 311 629 062 699 (+20.7 %) | 50.7 s (+6 %) |

So raising the bound by 2.5× costs only a few percent at a *fixed* `C`: the walk
window `u ≥ C²/(3N)` widens, and the pair loop admits pairs with `A+B ≤ N`. What
actually costs is the **low-`C` region**, and that was already true at 2·10¹⁰.

## The cost is concentrated at small `C`, not at large `C`

| segments (`C` range) | `divisor_steps` per segment | `candidates` per segment | full-mode wall per segment |
|---|---|---|---|
| `[0,10)`  (`C ≈ 10⁷`) | 1.39·10⁸ | 5.31·10⁹ | 3.4–3.6 s |
| `[20000,20010)` (`C ≈ 4.2·10¹⁰`) | 1.01·10⁸ | 8.28·10⁷ (64× less) | 0.77–0.81 s |

The walk (`divisor_steps`) is nearly flat in `C` — it is the divisor walk of
`C²`, and for large `C` the band `[C²/(3N), C]` narrows around `C` — while the
pair loop collapses by two orders of magnitude, because the pairs of `T(C)` that
fit under `A+B ≤ N` are plentiful for small `C` and rare for large `C`. The
archived 2·10¹⁰ run averaged 382 `candidates` per `C`; the first 50 segments of
the 5·10¹⁰ run have 2960 per `C`. So the first piece is the most expensive piece
of the run, not the cheapest.

## Consequences

* **The schedule is deliberately kept but its shape is a guess.** The pieces were
  cut by estimated work `∝ C^1.8`, so the low-`C` pieces got the most segments.
  The measurements say the true exponent is nearer `0` (mild *decrease*), so the
  pieces are unbalanced in *time*: piece 00 (`[0,4079)`) should take on the order
  of two hours while the later, larger-`C` pieces are much shorter. The total is
  unaffected — every segment is visited once either way — and the pieces still
  sum to the whole-run line (`checks/verify_chunking.sh`).
* **Rough cost model** for the loaded machine: flat part (sieve + walk +
  candidate sweep) `≈ 0.5–1.0 s` per segment, pair loop `≈ 0.28 + 4.4·10⁻¹⁰ ·
  candidates` seconds per segment. Integrated over the 23 842 segments this puts
  the whole run at roughly **6 hours** on this laptop (8 cores / 12 threads,
  i5-13420H, 100 % loaded), i.e. about 3.4 h of pure work at an unloaded
  machine's rate.
* The first measured milestone agrees: piece 00 needed 1875 s for its first 1000
  segments (1.88 s per segment), and the model gives ≈2 s per segment for that
  range under load.

## Measured, piece by piece (2026-09-15, the real run)

The model above turned out to be **too pessimistic** — see the correction at the
end. These are the actual wall times, from `results/run_5e10.log` (the driver's
own lines) and the `[search] … total` lines in `results/chunks5e10/part_kk.err`:

| piece | segment range | segments | wall (driver) | inner total | per segment |
|---|---|---|---|---|---|
| 00 | `[0,4079)` | 4079 | 3932 s | 3929.94 s | 0.964 s |
| 01 | `[4079,5995)` | 1916 | 1022 s | 1020.30 s | 0.533 s |
| 02 | `[5995,7510)` | 1515 | 723 s | 720.20 s | 0.477 s |
| 03 | `[7510,8811)` | 1301 | 561 s | 559.23 s | 0.431 s |
| 04 | `[8811,9974)` | 1163 | 447 s | 445.43 s | 0.384 s |
| 05 | `[9974,11037)` | 1063 | 391 s | 388.42 s | 0.368 s |

Cost per segment keeps falling (0.96 → 0.53 → 0.48 → 0.43 → 0.38 → 0.37), i.e.
the density is much flatter than `C^-1`; a local fit on pieces 02–04 gives
≈ `C^-0.66`. Two caveats on the first row: piece 00 overlapped the tail of the
`paircount` / `midline` companions (they hold the remaining threads until
14:10), and it contains the whole low-`C` spike, so 0.964 s/segment is an upper
bound on what piece 00 would cost with the machine to itself.

Extrapolating the remaining 19 pieces (13 868 segments at ≈0.35 s/segment, or
less if the decay continues) gives **≈1.0–1.5 h more**, i.e. **≈2.9–3.2 h** for
the whole 5·10¹⁰ run on this loaded laptop — about half the 6 h the model
predicted. The reason is the flat part: the sieve + walk + candidate sweep is
nearer **0.2–0.25 s** per segment than the 0.5–1.0 s assumed, and the pair loop
term was already close.

### Correction to the estimate above

The "roughly 6 hours" figure in the previous section was derived from probes that
ran *while the machine was saturated* by the main run itself, so it inherited that
contention; it also assumed a larger flat cost per segment. The measured
per-segment times above replace it. This is exactly the discipline the rest of
this repository follows: the probe-based number was an estimate from a proxy, the
per-piece numbers are the run's own output, and the estimate is corrected here in
writing rather than quietly dropped.

### Monitoring a resumable run (why it can look stalled)

Three things about this run are easy to misread as "it has stopped", and none of
them is a stall:

* `results/chunks5e10/part_kk.txt.partial` stays **0 bytes** for the whole piece —
  the C program's stdout is redirected to a file, hence block-buffered, so its
  counters reach disk only when the process exits (this is the same block
  buffering that lost the first attempt's final line after the power cut, §3.2 of
  `REPORT.md`). The driver renames the file to `part_kk.txt` only on success.
* `results/run_5e10.log` gains exactly **one line per finished piece**, so there
  are 7–12 minute gaps in it with no output at all.
* the real liveness signal is the piece's own stderr, which prints
  `[prog] 1000/1301 segments …` partway through and `[search] … total …` at the
  end:

  ```bash
  tail -1 $(ls -t results/chunks5e10/part_*.err | head -1)
  ```

  while the process is running, `powershell -Command "(Get-Process fast_search5).CPU"`
  sampled twice shows the CPU total climbing by ≈10 s per second of wall clock
  (i.e. ~10 of the 12 threads busy).

