# Working notes for Claude sessions in this repository

This is a **fork** of mathlib4 used to develop and verify new proofs. All work lands on `master`
(this fork's default branch; there is no `main`). Upstream `leanprover-community/mathlib4` is
never pushed to.

These notes were written by an agent session for later agent sessions. They record what cost time
to discover, not what is already obvious from the mathlib docs.

---

## 0. Read the unslop skill first

Before writing anything, read `.claude/skills/unslop/SKILL.md` and apply it. Do this at the start
of the session, not as a cleanup pass at the end. Text written without it and fixed later still
reads like text written without it.

It applies to **all** text you produce in this repository, with no exceptions:

* replies in the session
* commit messages, and pull request titles and bodies
* Lean docstrings, module docstrings and code comments
* this file, and anything else under `.claude/`
* notes to yourself, and prompts you write for subagents

The rules that catch the most mistakes here are: no em dashes (rule 13), sentence case headings
(17), plain words over fancy ones (31), active voice (29), and say what a thing does rather than
how it feels (27). Rule 27 matters most in commit messages. "Improves the API" says nothing.
"`Ideal.map_pow` requires a `CommSemiring` codomain, so the general route does not typecheck" says
what happened.

Scope: apply the rules to text you write. Do not rewrite mathlib text already in the tree, since
that text comes from upstream and reformatting it creates merge conflicts for no gain.

Where a rule collides with a mathlib convention, the mathlib convention wins for Lean source, and
unslop wins everywhere else. Mathlib requires a docstring on every public declaration and caps
lines at 100 characters. Those are not negotiable. Nothing in unslop asks you to break either.

The skill is vendored at `.claude/skills/unslop/`, copied from poteto's `pstack` under the MIT
licence. See `PROVENANCE.md` there.

---

## 1. Environment bootstrap (do this first, the container starts without Lean)

The container has **no Lean toolchain** and an **empty `.lake/`**. Both must be created before any
verification is possible. Budget ~15 minutes.

```bash
curl -sSfL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain "$(cat lean-toolchain)"
export PATH="$HOME/.elan/bin:$PATH"     # needed in EVERY shell; it does not persist
lake exe cache get                       # pulls the olean cache; several minutes
```

`lake exe cache get` will report fewer modules than the tree contains (e.g. 5,480 of 8,306).
That is expected and *not* a failure: files touched by earlier commits on this fork, plus
everything downstream of them, have no upstream cache entry. Do **not** try to "fix" it by
resetting to upstream.

### Build strategy

**Never run a bare `lake build`.** The uncached tail is thousands of modules on 4 cores.
Build only the module you need:

```bash
lake build Mathlib.RingTheory.SimpleModule.WedderburnArtin   # ~1,600 jobs, a few minutes
```

Job counts measured on this fork (the great majority are cache hits, so a build with a large job
count is not necessarily slow):

| Target | Jobs |
|---|---|
| `Mathlib.RingTheory.SimpleModule.WedderburnArtin` | 1,576 |
| `Mathlib.CategoryTheory.Limits.Constructions.Countable` | 890 |
| `Mathlib.RingTheory.Artinian.Opposite` | 2,051 |
| `Wanted` (whole target) | 3,391, **exceeds 10 min, background it** |

`lake` takes a lock, so concurrent builds queue rather than fail. Backgrounding a long build and
doing source work meanwhile is the right pattern.

Note: `lake build -j4` is **not** valid. There is no `-j` short option.

---

## 2. Verification harness

Elaborating a standalone file against the built Mathlib is far faster than `lake build`:

```bash
lake env lean path/to/file.lean
```

Keep scratch files **outside the repo tree** (a stop hook complains about untracked files).
Scratch files may use plain `import`; they do not need the `module` / `public import` syntax.

Wrap it so cheats cannot slip through. Reject any file containing `sorry`, `native_decide`,
`axiom`, `unsafe`, or emitting `declaration uses 'sorry'`.

**Before committing any proof, run `#print axioms` on every new declaration.** The only
acceptable output is `[propext, Classical.choice, Quot.sound]`.

---

## 3. Process rules (each of these was learned the hard way)

**R1. Re-verify every claim before acting on it.** Reconnaissance reports, whether from a
subagent or from your own memory, contain confident errors. Check signatures with `#check` against
the actual build first. A scout once reported `HasCountableProducts` is not `Prop`-valued. It is.
Lean infers `Prop` automatically when every field of a structure is a proposition.

**R2. Docstring dependency claims are not trustworthy, so re-derive the graph.**
`Wanted/CategoryTheory/Limits/Shapes/Countable.lean` stated that two of its `proof_wanted`s needed
the three above them ("given all of the above"). They did not, and were provable immediately. The
same file stated a hypothesis `[HasLimitsOfShape ℕ C]` that had to be `[HasColimitsOfShape ℕ C]`.
Statements in `Wanted/` can be wrong. Read them as leads, not specifications.

**R3. Prefer clusters that close today over headline items with long prerequisite chains.**
Reordering by "what is actually reachable now" produced four discharged `proof_wanted`s in one
round; the headline items would have produced none.

**R4. Route through general API, not the narrow requested statement.** The reusable transfer
lemma is the valuable object; the `proof_wanted` usually falls out of it in two lines. But check
the cost first. See R5.

**R5. Confirm the suggested route is the cheap one.** The `Wanted` comment for
`isSemiprimaryRing_mulOpposite_iff` sketched building a general `RingEquiv` transfer first. That
route is *harder*: it needs `Ideal.map`-of-powers API for noncommutative rings, which does not
exist (`Ideal.map_pow` and `Ideal.map_mul` both require a `CommSemiring` codomain). The direct
route, mirroring the adjacent `Ring.unop_mem_jacobson_pow`, was a dozen lines.

**R6. Use subagents for reconnaissance and keep proving and integrating in the main session.**
Subagent runs can die mid-flight (session limits). Scouting output is durable and survives such a
death; a half-finished proof does not, and proving needs consistent repo and build state anyway.

---

## 4. Mathlib conventions that bit

* The tree uses the **module system**: files start with `module`, then `public import ...`, then
  `@[expose] public section`. Match this in new files; scratch files need none of it.
* **Check whether section variables are implicit before reusing scratch code.** Scratch written
  with `variable (R : Type*)` will not paste into a file whose section has `{R : Type u}`. Symptom:
  `Function expected at <lemma> but this term has type ...`.
* **Instance-implicit binders must stay instance-implicit.** Writing `out J _ hJ :=` names the
  `CountableCategory` argument and removes it from instance search; `out _ _ _ :=` keeps it.
* `Countable (Sigma ...)` needs `Mathlib.Data.Countable.Basic`; `Countable (Finset α)` needs
  `Mathlib.Logic.Equiv.List`. Neither is in `Mathlib.Data.Countable.Defs`.
* Prefer `have` over `haveI` for propositions. A style linter checks this.
* **Placement:** when a result needs two modules that do not import each other, prefer a small new
  file over adding an import to either. Adding `HopkinsLevitzki` to `WedderburnArtin` (or the
  reverse) would push commutative-algebra weight onto every downstream consumer;
  `Mathlib/RingTheory/Artinian/Opposite.lean` costs nothing. Add the new file to `Mathlib.lean`,
  keeping the list alphabetical.
* When a `Wanted/` file's last `proof_wanted` is discharged, delete the file and remove its line
  from `Wanted.lean`. When only some are discharged, leave a comment saying where they went and
  correct any claim the file made that turned out to be false.

---

## 5. Frontier map

### Discharged on this fork

`Wanted/RingTheory/SimpleModule/WedderburnArtin.lean` (both, file removed);
`hasCountableLimits_of_hasFiniteLimits_and_hasSequentialLimits` and its colimit dual;
and, in earlier sessions, six statements plus results in Probability, Analysis/Convex and
RingTheory/Jacobson.

### Open and assessed

| Target | Verdict | Note |
|---|---|---|
| Noncommutative `Ideal.map_mul` / `Ideal.map_pow` | MEDIUM | Real infrastructure gap. Blocks `RingEquiv.isSemiprimaryRing` and a family of transfer lemmas. |
| `preorder_of_cofiltered` (Stacks 0032) | MEDIUM | Dualize `IsFiltered.exists_directed` in `Mathlib/CategoryTheory/Presentable/Directed.lean`, same Stacks tag, already proved. Friction is universes (`SmallCategory` vs `Category*`) and that `Jᵒᵖ` of a `Preorder` is not a `Preorder` (route via `orderDualEquivalence`). |
| `preorder_of_cofiltered_countable` | MEDIUM | Needs a `Countable (DiagramWithUniqueTerminal J ℵ₀)` instance. Countability bookkeeping, not new mathematics. |
| `hasCofilteredCountableLimits_of_hasSequentialLimits` | EASY *given* the above | Two lemma applications. |
| `IsSemisimpleRing → IsSemiprimaryRing` instance | EASY | The class currently has exactly one instance source (`IsArtinianRing`). Needs a diamond check; use `priority := low`. |
| `Ring.comap_jacobson_of_bijective` | EASY | The `Module.` versions exist; the `Ring.` namespace has only `map_jacobson_of_ker_le`. |
| Jordan / `Equiv.Perm` primitivity (3 statements) | HARD | Wielandt-style; claimed to follow existing methods but not yet attempted. |

### Do not attempt

* `conway_99`. The Conway 99-graph problem is **open**. The `Wanted` file says so.
* The five Poincaré-conjecture statements. Research-level.
* `MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing`. Substantial dimension theory.

---

## 6. Commits

Conventional-commit subject with the mathlib area, e.g.
`feat(RingTheory): semiprimary is left-right symmetric`. In the body, name each new declaration and
say *why* the proof goes the way it does, including routes rejected and any upstream statement
found to be wrong. Record the `#print axioms` result. Never put a model identifier in a commit
message, code comment, or any other artifact pushed to the repository.
