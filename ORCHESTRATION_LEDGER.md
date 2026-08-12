# Mathlib Proof-Orchestration Ledger

Autonomous orchestration of Lean 4 / Mathlib4 proof development.
All work lands on `claude/mathlib-proof-orchestration-6tqq8m`. **Upstream is never touched.**

*Everything in the tally below marked `VERIFIED` has been compiled by `lake build` against the
pinned toolchain (`leanprover/lean4:v4.34.0-rc1`). Nothing is claimed as proved on the strength of
a model's say-so.*

---

## Verification environment

| Item | Value |
|---|---|
| Toolchain | `leanprover/lean4:v4.34.0-rc1` |
| Build cache | `lake exe cache get` — 5480 / 8685 modules hit; ~3200 rebuilt locally (branch has diverged from master) |
| Cores / RAM | 4 / 15 GB |
| Verification command | `lake build <Module>` (exit 0, zero `error:`, zero `sorry`) |

---

## Tally

| # | Target | Area | Origin | Status | Verified | Commit |
|---|---|---|---|---|---|---|
| 1 | 6 × `proof_wanted` discharged (EReal, KrullDim, Congruence, SimpleModule) | mixed | `Wanted/` | landed | ⏳ baseline build | `ed7e6f7` |
| 2 | `variance_binomial` + conditional-variance fix | Probability | `Wanted/` | landed | ⏳ baseline build | `a53d4ad` |
| 3 | convex functions locally Lipschitz on intrinsic interior | Analysis/Convex | `Wanted/` | landed | ⏳ baseline build | `cab3ef1` |
| 4 | cone hull of an open set is open | Analysis/Convex/Cone | `Wanted/` | landed | ⏳ baseline build | `a3418e8` |
| 5 | edge count of `G(V,p)` is binomially distributed | Probability/Combinatorics | `Wanted/` | landed | ⏳ baseline build | `67dae0a` |
| 6 | Jacobson's lemma; left–right symmetry of `Ring.jacobson` | RingTheory/Jacobson | `Wanted/` | landed | ⏳ baseline build | `a194945` |
| 7 | `IsSemiprimaryRing.mulOpposite` | RingTheory/Wedderburn | `Wanted/` | landed | ⏳ baseline build | `1d547fb` |
| 8 | **`Face.iicOrderIso`** — the face lattice of a face is the down-set `Set.Iic F` | Geometry/Convex/Cone | frontier C | **landed** | ✅ **VERIFIED** (build + axioms) | `65dafd5` |

**Score: 1 verified · 7 awaiting baseline verification · 0 refuted**

### #8 verification record

```
=== [1/3] lake build Mathlib.Geometry.Convex.Cone.Face.Lattice   → OK: build clean
=== [2/3] sorry / admit / native_decide scan                     → OK: none
=== [3/3] axiom audit
'PointedCone.Face.iicOrderIso'            depends on axioms: [propext, Classical.choice, Quot.sound]
'PointedCone.Face.toPointedCone_iicOrderIso' depends on axioms: [propext, Classical.choice, Quot.sound]
'PointedCone.Face.mem_iicOrderIso'        depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. Run by the orchestrator independently of the prover's own claim.

---

## Open frontiers

| Frontier | Next target | Feasibility | Scout |
|---|---|---|---|
| A. Semiprimary / Artinian rings | `isSemiprimaryRing_mulOpposite_iff` (needs `RingEquiv` transfer of `IsSemiprimaryRing`) | high — prior commit left an explicit route | dispatched |
| B. Binomial random graphs | expected edge count + variance of edge count | **high — scouted, route confirmed** | ✅ reported |
| C. Pointed cone face lattice | `Face F ≃o Set.Iic F` — the face lattice of a face is a down-set | high — ingredients verified present | orchestrator |
| D. Hopkins–Levitzki | `IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite` | medium — depends on A | — |

### Frontier B route (scouted, all identifiers verified to exist)

The chain **compounds two results already on this branch**: `binomialRandom_map_ncard_edgeSet`
(`67dae0a`, the edge count is binomial) and `variance_of_hasLaw_binomial` / `integral_of_hasLaw_binomial`
(`a53d4ad`, the moments of a binomial). Neither alone says anything about graphs; together they give
the two most-quoted facts about `G(V, p)`.

| Step | Statement | Effort |
|---|---|---|
| A1 | `binomialRandom_hasLaw_ncard_edgeSet` — recast the edge-count law in `HasLaw` form | ~8 lines, enabler |
| A2 | `G(V,p)[fun G ↦ (G.edgeSet.ncard : ℝ)] = p * C(‖V‖, 2)` — **expected edge count** | ~2 lines after A1 |
| A3 | `Var[edge count] = p(1-p) · C(‖V‖, 2)` | ~2 lines after A1 |

Scout also found dead code: the private `ncard_diagSet_compl_eq` duplicates `Sym2.ncard_diagSet_compl`
(`Mathlib/Data/Sym/NatCard.lean:73`), invisible only because the file imports `Data.Sym.Card` rather
than `Data.Sym.NatCard`.

Deferred as genuinely too expensive for now (recorded so no cycle re-derives it): independence of
distinct edge indicators (needs `infinitePi`→`Measure.pi` bridging), the law of an induced subgraph
(needs a `setBernoulli` marginal lemma that does not exist), and monotone coupling in `p`.

### Frontier assessment: `Wanted/` is nearly exhausted

Of the 11 `Wanted/` files remaining, most are *not* realistic targets and are recorded here so no
future cycle wastes effort re-deriving that judgement:

| Statement | Verdict |
|---|---|
| `conway_99` (99-graph problem) | **open research problem** — not attemptable |
| Poincaré conjecture (3d top./smooth), exotic ℝ⁴, exotic 7-sphere | decades of theory absent from Mathlib |
| `chudnovskySum_eq_pi_inv` | needs modular-forms machinery Mathlib lacks |
| `MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing` | needs Noetherian dimension theory |
| `FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat` | heavy descent machinery |
| Jordan-theorem statements (`GroupAction/Jordan`) | hard; Wielandt-style combinatorial group theory |
| `preorder_of_cofiltered` family | known-hard; needs new category-theoretic construction |
| `TM2ComputableInPolyTime.comp` | self-contained but notoriously fiddly |
| `IsSmoothEmbedding.comp`, `Diffeomorph.isSmoothEmbedding` | **plausible** — hold as reserve targets |
| `addHaarScalarFactor_hausdorffMeasure_eq` | plausible-hard — reserve |
| `isSemiprimaryRing_mulOpposite_iff` (+ Artinian iff) | **active — frontier A** |

Consequence for direction: the cheap harvest is over. Growth now comes from *extending recently
opened areas outward* rather than from mining `Wanted/`.

---

## Donor artifact: `anthropics/zeta-23-lean`

A Lean 4 formalization of "More than two thirds of the zeros of the Riemann zeta function lie on the
critical line" (Anthropic, 2026), introduced into this effort as a source of portable mathematics.

| Property | Value |
|---|---|
| Size | 328 `.lean` files, ~103,000 lines |
| Pinned to | Mathlib `51e6992…` = tag `v4.33.0-rc2` — **our fork is `v4.34.0-rc1`** |
| Licence | Apache-2.0 (same as Mathlib; attribution required via `NOTICE`) |
| Its own audit | `sorry`-free outside deliberate statement placeholders; **0** declared axioms; `#print axioms` on all 27 headline theorems reports only `propext, Classical.choice, Quot.sound`; comparator-checked with an independent kernel |

### What this ledger does and does not claim

**Not claimed:** that the headline zeta theorems have been re-verified here. Doing so requires a
second Mathlib checkout at the pinned commit (~10 GB, many hours on 4 cores). That has not been run,
and the artifact's own audit is *not* being treated as a substitute for verification.

**Structural fact:** the artifact is a *downstream library*, not Mathlib-shaped content, and it is
pinned to a different Mathlib. It therefore cannot be merged into Mathlib wholesale — this is a
property of the artifact, not a scoping decision.

### What is actually being incorporated

`Zeta23/LinAlg/` — 7 files, ~1385 lines, namespace `RHLinalg`, documented in its own header as
"a self-contained development … they have no upstream outside this project". It contains:
Hermitian positive/negative parts, the positive index, Sylvester's law of inertia, von Neumann's
trace inequality, the rank–trace inequality, and Weyl's perturbation bound.

Gap check against our Mathlib (grep-verified):

| Notion | In our Mathlib? |
|---|---|
| Positive index / signature / Sylvester inertia for Hermitian matrices | **No.** The only `inertia` in Mathlib is `RamificationInertia`, which is number-theoretic and unrelated |
| Montgomery–Vaughan / generalized Hilbert inequality | **No** — nothing anywhere |
| `posIndex`, matrix signature | **No** |

These are classical results Mathlib genuinely lacks. The port therefore goes in as ordinary Mathlib
contributions, ported `v4.33.0-rc2 → v4.34.0-rc1`, and must clear the same gate as everything else
in this ledger: build + `sorry` scan + axiom audit, re-run by the orchestrator.

---

## Orchestration architecture

- **Scouts** — read-only (`Read`/`Grep`/`Glob`), run in parallel, forbidden from touching `lake`.
  They return verified identifier inventories and ranked candidate statements.
- **Provers** — hold the `lake` build lock, so they run **strictly serialized**. A prover writes
  Lean, compiles, iterates against real compiler errors, and may only report success on a clean
  build.
- **Orchestrator** — meta-analyses each returned result, re-aims the direction, commits, and keeps
  this ledger.

The serialization constraint is structural: `lake` takes an exclusive lock on `.lake/build`, so
concurrent provers queue rather than run. Parallelism therefore lives entirely in the scouting and
proof-writing phases; verification is a single-lane road.

**Prover claims are re-verified by the orchestrator.** A prover reporting a clean build is treated
as a hypothesis, not a result. Every entry marked `VERIFIED` above was re-run independently via
`verify.sh` before being committed.

---

## Meta-analysis: what is actually working

**1. The best targets are ones where the mathematics already exists unbundled.** `Face.iicOrderIso`
verified on the first attempt with *zero tactic proofs* — every field is `rfl`. That was not luck: the
target was selected because `IsFaceOf.trans` and `IsFaceOf.isFaceOf_iff_le` already carried the
entire mathematical content, and the only thing missing was the packaging into an `OrderIso`.
Generalised selection rule: **prefer gaps where the content exists in unbundled form and only the
bundling is absent** over gaps that need new mathematics. These verify fast and almost never fail.

**2. The binding constraint is the module system, not the mathematics.** The single obstacle in #8
was that `Face/Lattice.lean` uses a plain `public section`, so the new definition's body was invisible
to its own exported `rfl` lemmas until tagged `@[expose]`. Every prover prompt now warns about this
explicitly — it is a recurring, non-mathematical failure mode that costs a full build cycle each time
it is rediscovered.

**3. Negative scout results are as valuable as positive ones.** Scout A's most useful finding was
that noncommutative `Ideal.map_pow` *does not exist* (`Ideal.map_mul`/`map_pow` are confined to a
`CommRing` section, and `IsNilpotent.map` needs a `MonoidWithZero` that `Ideal R` lacks). That
converted an open-ended search into a bounded elementwise induction and let the prover be told
outright not to hunt for a lemma that isn't there.

**4. Compute triage matters more than proof cleverness.** Killing the full 8624-module build in
favour of the 1830-module verification closure recovered several hours. Verification cost is
governed by import-graph position, so target selection is partly a *build-cost* decision, not only a
mathematical one.
