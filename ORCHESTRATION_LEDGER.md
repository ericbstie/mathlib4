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

**Score: 0 verified · 7 awaiting baseline verification · 0 refuted**

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

## Orchestration architecture

- **Scouts** — read-only (`Read`/`Grep`/`Glob`), run in parallel, forbidden from touching `lake`.
  They return verified identifier inventories and ranked candidate statements.
- **Provers** — hold the `lake` build lock, so they run **strictly serialized**. A prover writes
  Lean, compiles, iterates against real compiler errors, and may only report success on a clean
  build.
- **Orchestrator** — meta-analyses each returned result, re-aims the direction, commits, and keeps
  this ledger.

The serialization constraint is structural: `lake` takes an exclusive lock on `.lake/build`, so
concurrent provers would deadlock. Parallelism therefore lives entirely in the scouting phase.
