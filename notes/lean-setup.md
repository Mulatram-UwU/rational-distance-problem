# Lean 4 toolchain setup — findings

Environment: Windows 10 (win32 10.0.26200), Git Bash.
Date: 2026-09-14.
Lean: **4.34.0-rc2** (`x86_64-w64-windows-gnu`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`).
Lake: 5.0.0-src (`Lean version 4.34.0-rc2`).
`ELAN_HOME=<elan>`.

> **Paths in this file.** `<repo>` is the root of this checkout and `<elan>` is the
> elan home directory (`~/.elan` by default).  They stand in for the absolute paths of
> the machine these notes were written on, so that no local path is published; every
> command below was run verbatim with them expanded.

> **Update (2026-09-15):** this file records the situation on 2026-09-14, when
> `github.com:443` was unreachable; §3 below concludes "Mathlib is NOT usable on this
> machine right now".  That verdict was **superseded the next day**: access was restored,
> `lake exe cache get` fetched the official oleans, and `lake build` succeeds — the Mathlib
> layer now lives in `lean-mathlib/` (see `notes/lean-formalisation.md`).  The core project
> under `lean/` is still deliberately dependency-free (`Init` only), which is why the two
> projects are kept separate and why `lean-mathlib` reuses `lean/` via `srcDir`.

---

## 0. Root cause of the original problem, and the fix

`<elan>\settings.toml` had `default_toolchain = "stable"`, and **`stable` was never
installed**. Every bare `elan`-shim invocation (`lean`, `lake` from `<elan>\bin`)
therefore tried to download a fresh toolchain from `releases.lean-lang.org` and died:

```
info: downloading https://releases.lean-lang.org/lean4/v4.34.0/lean-4.34.0-windows.tar.zst
error: could not download file from '...'
```

That download host is effectively **dead from this machine: measured 128 B/s, and a
60 s attempt transferred 0 bytes** (curl exit 28 = timeout). So a bare `lake` can never
succeed here.

**Fix applied:** `settings.toml` now points at the toolchain that is already on disk:

```toml
default_toolchain = "leanprover/lean4:v4.34.0-rc2"
telemetry = false
version = "12"

[overrides]
```

(Backup of the old file: `<elan>\settings.toml.bak`.) After this change a bare
`lake`/`lean` on `PATH` resolves to the installed toolchain with no download. Projects
that carry their own `lean-toolchain` still win, because elan prefers the project file.

---

## 1. GOAL 1 — core-Lean project (COMPLETE, builds clean)

### Files
```
<repo>\lean\lean-toolchain                          # leanprover/lean4:v4.34.0-rc2
<repo>\lean\lakefile.toml                           # package RationalDistance
<repo>\lean\RationalDistance.lean                   # lib root, imports Smoke
<repo>\lean\RationalDistance\Smoke.lean             # all passing tests
<repo>\lean\RationalDistance\MathlibOnly.lean.txt   # failing tests, recorded (not compiled)
```

`lakefile.toml`:
```toml
name = "RationalDistance"
version = "0.1.0"
defaultTargets = ["RationalDistance"]

[[lean_lib]]
name = "RationalDistance"
```

Note: a `[[lean_lib]]` named `X` **requires a root module file `X.lean`** next to the
`X/` directory. Without `RationalDistance.lean`, `lake build` fails with
`no such file or directory ... RationalDistance.lean`.

### EXACT working commands

Let `TC=<elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin`.

**(A) Recommended — full path to the toolchain's own `lake.exe`.**
No elan shim involved, no network, no toolchain resolution:
```bash
cd <repo>/lean
<elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lake.exe build
```
Observed output:
```
✔ [2/4] Built RationalDistance.Smoke (1.4s)
✔ [3/4] Built RationalDistance (2.1s)
Build completed successfully (4 jobs).
```
Wall clock `real 0m3.754s`. Artifacts:
`.lake/build/lib/lean/RationalDistance/Smoke.olean`, `.lake/build/lib/lean/RationalDistance.olean`.

**(B) Via the elan shim, pinning the toolchain explicitly.**
Needed if you want the `PATH`-installed `lake` but the project has no `lean-toolchain`:
```bash
cd <repo>/lean
ELAN_HOME=<elan> ELAN_TOOLCHAIN=leanprover/lean4:v4.34.0-rc2 <elan>/bin/lake.exe build
```
Verified: `Build completed successfully (4 jobs).`
(With the `settings.toml` fix from section 0, the bare `lake build` also works.)

**(C) Compile a single file without Lake at all:**
```bash
TC=<elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin
"$TC/lean.exe" -o /tmp/out.olean <repo>/lean/RationalDistance/Smoke.lean
```
Verified working. Use `-o /dev/null` if you only want diagnostics.

**Do NOT** run a bare `lake`/`lean` from `<elan>\bin` while `settings.toml` still says
`default_toolchain = "stable"` — it hangs ~21 s then fails on the dead download host.

---

## 2. GOAL 1 — tactic availability WITHOUT Mathlib

Method: each snippet written to its own file, compiled with
`lean.exe <file>` against the default prelude (no imports; `import Init` explicitly also
verified). A missing tactic is a hard error, so the snippets must be tested one at a time.

### AVAILABLE (no Mathlib)

| Tactic / feature   | Status | Evidence |
|--------------------|--------|----------|
| `decide`           | OK | `example : (12:Nat)^2 = 144 := by decide` compiles |
| `native_decide`    | OK | `example : (12:Nat)^2 = 144 := by native_decide` compiles |
| `omega`            | OK | Nat *and* Int goals; works even with only `import Init` |
| `simp`             | OK | `example (a : Nat) : a + 0 = a := by simp` |
| `simp_all`         | OK | |
| `simp +arith`      | OK | (see note on `simp_arith` below) |
| `rfl`              | OK | |
| `trivial`          | OK | |
| `intro` / `exact`  | OK | |
| `rw`               | OK | |
| `cases`            | OK | |
| `induction`        | OK | `induction n <;> simp_all` works |
| `subst`            | OK | |
| `by_cases`         | OK | |
| `exfalso`          | OK | |
| `calc`             | OK | |
| `ext`              | OK | |
| `funext`           | OK | |
| `norm_cast`        | OK | `example (a : Nat) : ((a:Int) + 0) = a := by norm_cast` |
| `push_cast`        | OK | |
| `have`             | OK | |

Confirmed WITH `decide`: Nat squares, Int squares, Pythagorean triple
`7² + 24² = 25²`, `2^10 = 1024`, and a negative statement `¬(3 = 4)`.
`omega` verified on `a ≤ b ⊢ a + 1 ≤ b + 1`, on a substitution goal, and on
`Int` antisymmetry.

### NOT AVAILABLE (Mathlib-only). Exact error for each: `error: unknown tactic`

`norm_num`, `ring`, `ring_nf`, `linarith`, `nlinarith`, `positivity`, `push_neg`,
`by_contra`, `contrapose`, `tauto`, `aesop`, `abel`, `group`, `field_simp`.

Full captured stderr, e.g. for the two the task asked about:

```
$ lean.exe /tmp/norm_num.lean      # example : (3 : Nat) ^ 2 = 9 := by norm_num
norm_num.lean:1:35: error: unknown tactic
norm_num.lean:1:31: error: unsolved goals
⊢ 3 ^ 2 = 9

$ lean.exe /tmp/ring.lean          # example (a b : Nat) : (a+b)^2 = a^2 + 2*a*b + b^2 := by ring
ring.lean:1:69: error: unknown tactic
ring.lean:1:65: error: unsolved goals
a b : Nat
⊢ (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2

$ lean.exe /tmp/linarith.lean      # example (a b : Nat) (h : a < b) : a + 1 ≤ b := by linarith
linarith.lean:1:51: error: unknown tactic
linarith.lean:1:47: error: unsolved goals
a b : Nat
h : a < b
⊢ a + 1 ≤ b
```

Note the "unknown tactic" error is *followed by* an "unsolved goals" error — the tactic
is simply not in scope, so the goal is left open.

**Special case — `simp_arith` EXISTS but is deprecated** (Exit 1):
```
`simp_arith` has been deprecated. It was a shorthand for `simp +arith +decide`,
but most of the time, `+decide` was redundant since simprocs have been implemented.
Try these:
  [apply] simp +arith
  [apply] simp +arith +decide
```
Use `simp +arith` instead.

### Substitution recipes for core-only work
- `norm_num` on concrete numerals -> `decide` / `native_decide` / `simp +arith`.
- `linarith` -> **`omega` works for linear Nat/Int arithmetic** (best single win).
- `ring` -> no core equivalent; prove polynomial identities by hand or `decide` for numerals.
- `positivity` -> `omega` for simple bounds, else manual.
- `by_contra` -> absent; use `Classical.byContradiction` explicitly, or reason by `fun h => ...`.
- `push_neg` -> absent; reason manually or `by_cases`.
- `aesop` / `tauto` -> `simp_all` + `omega` only.

---

## 3. GOAL 2 — is Mathlib practical here? **NO. NOT USABLE NOW.**

### Toolchain MATCHES (the one thing that is fine)
`https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain`
returns exactly:
```
leanprover/lean4:v4.34.0-rc2
```
So mathlib4 master **does** match the installed toolchain. No second toolchain download
would be needed. That was not the blocker.

### Project prepared for the attempt
```
<repo>\lean-mathlib\lean-toolchain   # leanprover/lean4:v4.34.0-rc2
<repo>\lean-mathlib\lakefile.toml    # [[require]] mathlib, git = mathlib4, rev = master
<repo>\lean-mathlib\LeanMathlib.lean
<repo>\lean-mathlib\LeanMathlib\Basic.lean   # `import Mathlib` + norm_num + ring
```
`lake update` never got past cloning, so `.lake/` is **0 bytes** and no
`lake-manifest.json` was produced.

### Blocker 1 (fatal): `github.com:443` is unreachable/intermittent

`lake update` failed on the very first dependency, every attempt:
```
info: mathlib: cloning https://github.com/leanprover-community/mathlib4
Cloning into '<repo>\lean-mathlib\.lake\packages\mathlib'...
fatal: unable to access 'https://github.com/leanprover-community/mathlib4/':
  Failed to connect to github.com:443 after 21149 ms: Could not connect to server
error: external command 'git' exited with code 128
```
A second, independent failure mode was also seen:
```
error: RPC failed; curl 28 Failed to connect to github.com:443 after 21113 ms
fatal: expected flush after ref listing
```

Measured success rate of `git ls-remote https://github.com/leanprover-community/mathlib4 HEAD`,
8 sequential tries, 25 s timeout each:

```
try 1: FAIL   try 2: FAIL   try 3: FAIL   try 4: FAIL
try 5: FAIL   try 6: FAIL   try 7: FAIL   try 8: OK
RESULT: 1 ok / 7 fail  (~12.5% success, ~21 s wasted per failure)
```

A `git clone --depth 1` of mathlib4 was retried in a bounded loop; **no clone ever
completed** (see the clone-attempt log). Even at a 12.5% connect success rate, Mathlib
needs mathlib4 **plus ~8 transitive git dependencies**, and a transfer that connects can
still be dropped mid-stream (as the "expected flush after ref listing" error shows).
This is not a matter of patience; it is a lossy transport.

### Blocker 2: the olean cache is not reachable at usable speed

The cache is served from Azure Blob Storage (`lakecache` storage account, containers
`master` / `legacy` / `forks` / `nightly-testing` / `pr-toolchain-tests`).
`https://lakecache.blob.core.windows.net/` answers (HTTP 400 on a bare URI, 404 on a
guessed blob path — so the host resolves), but Mathlib's olean cache is **multiple GB**
and even the working hosts here are slow.

`lake exe cache get` was **never attempted**, because it requires the deps to be cloned
first, which never happened.

### Throughput measurements (the decisive numbers)

| Host | Result |
|------|--------|
| `codeload.github.com` (tarball) | **4,284,203 B/s (4.28 MB/s)** — 23,802,775 bytes in 5.56 s. Fast! |
| `raw.githubusercontent.com` | works, small files fine |
| `github.com:443` (git protocol) | **fails ~87% of the time** (1 ok / 8 tries) |
| `releases.lean-lang.org` | **128 B/s**; 0 bytes in 22 s, curl exit 28 (timeout) |
| `lakecache.blob.core.windows.net` | host resolves, no throughput test possible |

So the network is *selectively* broken: plain HTTPS file downloads from GitHub's CDN are
fast, but the **git smart-HTTP endpoint on `github.com` (needed by `lake update`) is
effectively unusable**, and the **Lean toolchain download host is dead**.

### Verdict, honestly stated

**Mathlib is NOT usable on this machine right now.** Evidence:
1. `lake update` failed on all attempts — 0 bytes downloaded, no manifest produced.
2. `github.com:443` git access succeeds only ~12.5% of the time with a ~21 s penalty per
   failure, and Mathlib needs 9+ git clones (mathlib4 plus batteries, aesop, Qq,
   proofwidgets, importGraph, Cli, LeanSearchClient, plausible, …).
3. The toolchain line matches, so nothing further can be fixed by picking a different
   Lean version — the blocker is the network, not version skew.
4. The Mathlib olean cache is multi-GB on an Azure host whose throughput could not even
   be measured, and it is unreachable without first cloning the deps.

**Recommended next steps (in order of promise):**
1. **Fix `github.com` access** — this is the single real blocker. Options: a VPN/proxy,
   or configure git to use a reachable mirror, e.g.
   `git config --global url."<mirror>/".insteadOf "https://github.com/"`.
   Some proxies make `github.com` git-over-HTTPS work even when direct TCP/443 fails.
2. If a proxy is available, set `HTTPS_PROXY`/`HTTP_PROXY` **and** git's
   `http.proxy`, then re-run `lake update` in `<repo>\lean-mathlib`.
3. Only then run `lake exe cache get` (it needs the deps cloned to build its own tool).
4. If `github.com` cannot be fixed, **use the core-only project** at
   `<repo>\lean` — it builds in <4 s with zero dependencies, and `omega` +
   `decide` + `simp` cover a surprising amount of Nat/Int arithmetic.
   Alternatively Mathlib's *source* is downloadable from `codeload.github.com` at
   4.28 MB/s, but its 8+ git dependencies still have to come from `github.com`, so
   hand-assembling it is not realistic.

---

## 4. Quick reference

```bash
# Core-Lean project (the one that works)
cd <repo>/lean
<elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lake.exe build

# Single file, no Lake
TC=<elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin
"$TC/lean.exe" -o /dev/null RationalDistance/Smoke.lean
```

- Toolchain dir: `<elan>\toolchains\leanprover--lean4---v4.34.0-rc2`
- elan home: `<elan>` (settings backup at `settings.toml.bak`)
- Working without Mathlib: `decide`, `native_decide`, `omega`, `simp`, `simp_all`,
  `rfl`, `trivial`, `intro`, `exact`, `rw`, `cases`, `induction`, `subst`, `by_cases`,
  `exfalso`, `calc`, `ext`, `funext`, `norm_cast`, `push_cast`.
- Missing: `norm_num`, `ring`, `linarith`, `positivity`, `push_neg`, `by_contra`,
  `aesop`, `tauto`, `abel`, `group`, `field_simp` (all -> `error: unknown tactic`).
