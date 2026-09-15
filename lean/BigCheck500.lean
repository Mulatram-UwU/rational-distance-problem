/-
  (P1) Large-bound finite check — bound 500.

  This file is deliberately excluded from the library glob.  The library is
  declared as `[[lean_lib]] name = "RationalDistance"` in `lakefile.toml`, for
  which Lake derives the glob `["RationalDistance", "RationalDistance.*"]`; a
  root-level module named `BigCheck500` does not match it, so `lake build` does
  not compile this file.  That keeps the default build fast (~25 s instead of
  ~2.7 min).

  To run this check explicitly (from `lean/`, with `lake` on PATH):

      lake env lean -DmaxHeartbeats=0 BigCheck500.lean

  Observed 2026-09-14: exit 0, no output, 139 s wall clock.
  Bounds 100 / 200 / 300 / 400 / 500 all compiled: 18 / 33 / 64 / 90 / 139 s.
-/

import RationalDistance.Search

set_option maxHeartbeats 0 in
/-- **(P1)** There is no solution with common denominator `Q <= 500`. -/
theorem no_solution_Q_le_500 : noSolutionUpto 500 = true := by native_decide
