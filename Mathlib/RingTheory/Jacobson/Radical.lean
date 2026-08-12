/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Jacobson radical of modules and rings

## Main definitions

`Module.jacobson R M`: the Jacobson radical of a module `M` over a ring `R` is defined to be the
intersection of all maximal submodules of `M`.

`Ring.jacobson R`: the Jacobson radical of a ring `R` is the Jacobson radical of `R` as
an `R`-module, which is equal to the intersection of all maximal left ideals of `R`. It turns out
it is in fact a two-sided ideal, and equals the intersection of all maximal right ideals of `R`;
the latter is `Ring.mem_jacobson_op_iff`.

## Main results

* `IsUnit.one_sub_mul_comm` (**Jacobson's lemma**): `1 - a * b` is a unit iff `1 - b * a` is.
* `Ring.mem_jacobson_iff`: `x` lies in the Jacobson radical iff `1 - a * x` is a unit for all `a`.
* `Ring.mem_jacobson_iff_forall`: the same with the left-right symmetric condition
  `∀ a b, IsUnit (1 - a * x * b)`.
* `Ring.mem_jacobson_op_iff`: **the Jacobson radical is left-right symmetric**.

## Reference
* [F. Lorenz, *Algebra: Volume II: Fields with Structure, Algebras and Advanced Topics*][Lorenz2008]
-/

@[expose] public section

assert_not_exists Cardinal

namespace Module

open Submodule

variable (R R₂ M M₂ : Type*) [Ring R] [Ring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
variable (f : M →ₛₗ[τ₁₂] M₂)

/-- The Jacobson radical of an `R`-module `M` is the infimum of all maximal submodules in `M`. -/
def jacobson : Submodule R M :=
  sInf { m : Submodule R M | IsCoatom m }

variable {R R₂ M M₂}

theorem le_comap_jacobson : jacobson R M ≤ comap f (jacobson R₂ M₂) := by
  conv_rhs => rw [jacobson, sInf_eq_iInf', comap_iInf]
  refine le_iInf_iff.mpr fun S m hm ↦ ?_
  obtain h | h := isCoatom_comap_or_eq_top f S.2
  · exact mem_sInf.mp hm _ h
  · simpa only [h] using mem_top

theorem map_jacobson_le : map f (jacobson R M) ≤ jacobson R₂ M₂ :=
  map_le_iff_le_comap.mpr (le_comap_jacobson f)

theorem jacobson_eq_bot_of_injective (inj : Function.Injective f) (h : jacobson R₂ M₂ = ⊥) :
    jacobson R M = ⊥ :=
  le_bot_iff.mp <| (le_comap_jacobson f).trans <| by
    simp_rw [h, comap_bot, (LinearMap.ker_eq_bot.mpr inj).le]

variable {f}

theorem map_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f ≤ jacobson R M) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
  le_antisymm (map_jacobson_le f) <| by
    rw [jacobson, sInf_eq_iInf'] at le
    conv_rhs => rw [jacobson, sInf_eq_iInf', map_iInf_of_ker_le surj le]
    exact le_iInf fun m ↦ sInf_le (isCoatom_map_of_ker_le surj (le_iInf_iff.mp le m) m.2)

theorem comap_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f ≤ jacobson R M) :
    comap f (jacobson R₂ M₂) = jacobson R M := by
  rw [← map_jacobson_of_ker_le surj le, comap_map_eq_self le]

theorem map_jacobson_of_bijective (hf : Function.Bijective f) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
  map_jacobson_of_ker_le hf.2 <| by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]

theorem comap_jacobson_of_bijective (hf : Function.Bijective f) :
    comap f (jacobson R₂ M₂) = jacobson R M :=
  comap_jacobson_of_ker_le hf.2 <| by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]

theorem jacobson_quotient_of_le {N : Submodule R M} (le : N ≤ jacobson R M) :
    jacobson R (M ⧸ N) = map N.mkQ (jacobson R M) :=
  (map_jacobson_of_ker_le N.mkQ_surjective <| by rwa [ker_mkQ]).symm

theorem jacobson_le_of_eq_bot {N : Submodule R M} (h : jacobson R (M ⧸ N) = ⊥) :
    jacobson R M ≤ N := by
  simp_rw [← N.ker_mkQ, ← comap_bot, ← h, le_comap_jacobson]

variable (R M)

@[simp]
theorem jacobson_quotient_jacobson : jacobson R (M ⧸ jacobson R M) = ⊥ := by
  rw [jacobson_quotient_of_le le_rfl, mkQ_map_self]

theorem jacobson_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] : jacobson R M < ⊤ := by
  obtain ⟨m, hm, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R M)).resolve_left bot_ne_top
  exact (sInf_le <| Set.mem_ofPred.mpr hm).trans_lt hm.1.lt_top

example [Nontrivial M] [Module.Finite R M] : jacobson R M < ⊤ := jacobson_lt_top R M

variable {ι} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem jacobson_pi_le : jacobson R (Π i, M i) ≤ Submodule.pi Set.univ (jacobson R <| M ·) := by
  simp_rw [← iInf_comap_proj, jacobson, sInf_eq_iInf', comap_iInf, le_iInf_iff]
  intro i m
  exact iInf_le_of_le ⟨_, (isCoatom_comap_iff <| LinearMap.proj_surjective i).mpr m.2⟩ le_rfl

/-- A product of modules with trivial Jacobson radical (e.g. simple modules) also has trivial
Jacobson radical. -/
theorem jacobson_pi_eq_bot (h : ∀ i, jacobson R (M i) = ⊥) : jacobson R (Π i, M i) = ⊥ :=
  le_bot_iff.mp <| (jacobson_pi_le R M).trans <| by simp_rw [h, pi_univ_bot, le_rfl]

end Module

section

variable (R R₂ : Type*) [Ring R] [Ring R₂] (f : R →+* R₂) [RingHomSurjective f]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- **Jacobson's lemma**: `1 - a * b` is a unit if and only if `1 - b * a` is.

If `v` is the inverse of `1 - a * b`, then `1 + b * v * a` is the inverse of `1 - b * a`. -/
theorem IsUnit.one_sub_mul_comm {R : Type*} [Ring R] {a b : R} (h : IsUnit (1 - a * b)) :
    IsUnit (1 - b * a) := by
  obtain ⟨u, hu⟩ := h
  set v : R := ↑u⁻¹ with hv
  have h1 : (1 - a * b) * v = 1 := by rw [← hu]; exact u.mul_inv
  have h2 : v * (1 - a * b) = 1 := by rw [← hu]; exact u.inv_mul
  have e1 : a * b * v = v - 1 := by
    have h : v - a * b * v = 1 := by rw [← h1, sub_mul, one_mul]
    rw [← h]; abel
  have e2 : v * (a * b) = v - 1 := by
    have h : v - v * (a * b) = 1 := by rw [← h2, mul_sub, mul_one]
    rw [← h]; abel
  refine ⟨⟨1 - b * a, 1 + b * v * a, ?_, ?_⟩, rfl⟩
  · have key : (1 - b * a) * (1 + b * v * a) = 1 - b * a + (b * v * a - b * (a * b * v) * a) := by
      simp only [mul_add, mul_one, sub_mul, one_mul, mul_assoc]
    rw [key, e1]
    simp only [sub_mul, mul_sub, mul_one, mul_assoc]
    abel
  · have key : (1 + b * v * a) * (1 - b * a) = 1 + b * v * a - b * a - b * (v * (a * b)) * a := by
      simp only [mul_sub, mul_one, add_mul, one_mul, mul_assoc]
      abel
    rw [key, e2]
    simp only [sub_mul, mul_sub, mul_one, mul_assoc]
    abel

/-- **Jacobson's lemma**, `Iff` version of `IsUnit.one_sub_mul_comm`. -/
theorem isUnit_one_sub_mul_comm_iff {R : Type*} [Ring R] {a b : R} :
    IsUnit (1 - a * b) ↔ IsUnit (1 - b * a) :=
  ⟨IsUnit.one_sub_mul_comm, IsUnit.one_sub_mul_comm⟩

namespace Ring

/-- The Jacobson radical of a ring `R` is the Jacobson radical of `R` as an `R`-module. -/
-- TODO: replace all `Ideal.jacobson ⊥` by this.
abbrev jacobson : Ideal R := Module.jacobson R R

theorem jacobson_eq_sInf_isMaximal : jacobson R = sInf {I : Ideal R | I.IsMaximal} := by
  simp_rw [jacobson, Module.jacobson, Ideal.isMaximal_def]

instance : (jacobson R).IsTwoSided :=
  ⟨fun b ha ↦ Module.le_comap_jacobson (f := LinearMap.toSpanSingleton R R b) ha⟩

variable {R R₂}

lemma jacobson_le_of_isMaximal (m : Ideal R) [m.IsMaximal] : jacobson R ≤ m := by
  rw [Ring.jacobson_eq_sInf_isMaximal]
  exact sInf_le ‹_›

theorem le_comap_jacobson : jacobson R ≤ Ideal.comap f (jacobson R₂) :=
  Module.le_comap_jacobson f.toSemilinearMap

theorem map_jacobson_le : Submodule.map f.toSemilinearMap (jacobson R) ≤ jacobson R₂ :=
  Module.map_jacobson_le f.toSemilinearMap

variable {f} in
theorem map_jacobson_of_ker_le (le : RingHom.ker f ≤ jacobson R) :
    Submodule.map f.toSemilinearMap (jacobson R) = jacobson R₂ :=
  Module.map_jacobson_of_ker_le f.surjective le

theorem coe_jacobson_quotient (I : Ideal R) [I.IsTwoSided] :
    (jacobson (R ⧸ I) : Set (R ⧸ I)) = Module.jacobson R (R ⧸ I) := by
  let f : R ⧸ I →ₛₗ[Ideal.Quotient.mk I] R ⧸ I := ⟨AddHom.id _, fun _ _ ↦ rfl⟩
  rw [jacobson, ← Module.map_jacobson_of_ker_le (f := f) Function.surjective_id]
  · apply Set.image_id
  · rintro _ rfl; exact zero_mem _

theorem jacobson_quotient_of_le {I : Ideal R} [I.IsTwoSided] (le : I ≤ jacobson R) :
    jacobson (R ⧸ I) = Submodule.map (Ideal.Quotient.mk I).toSemilinearMap (jacobson R) :=
  .symm <| Module.map_jacobson_of_ker_le (by exact Ideal.Quotient.mk_surjective) <| by
    rwa [← I.ker_mkQ] at le

theorem jacobson_le_of_eq_bot {I : Ideal R} [I.IsTwoSided] (h : jacobson (R ⧸ I) = ⊥) :
    jacobson R ≤ I :=
  Module.jacobson_le_of_eq_bot <| by
    rw [← le_bot_iff, ← SetLike.coe_subset_coe] at h ⊢
    rwa [← coe_jacobson_quotient]

variable (R)

@[simp]
theorem jacobson_quotient_jacobson : jacobson (R ⧸ jacobson R) = ⊥ :=
  (jacobson_quotient_of_le le_rfl).trans <| SetLike.ext' <| by
    apply SetLike.ext'_iff.mp (jacobson R).mkQ_map_self

theorem jacobson_lt_top [Nontrivial R] : jacobson R < ⊤ := Module.jacobson_lt_top R R

theorem jacobson_smul_top_le : jacobson R • (⊤ : Submodule R M) ≤ Module.jacobson R M :=
  Submodule.smul_le.mpr fun _ hr m _ ↦ Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr

/-!
### Unit characterisation and left-right symmetry
-/

section Units

variable {R}

/-- Every element of the Jacobson radical `j` has `1 - j` left invertible: otherwise the left
ideal generated by `1 - j` would sit inside a maximal left ideal, which would then contain
`(1 - j) + j = 1`. -/
theorem exists_mul_eq_one_of_mem_jacobson {j : R} (hj : j ∈ jacobson R) :
    ∃ y : R, y * (1 - j) = 1 := by
  by_contra hcon
  push Not at hcon
  have hne : (Ideal.span {1 - j} : Ideal R) ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ Ideal.span ({1 - j} : Set R) := htop ▸ Submodule.mem_top
    rw [Submodule.mem_span_singleton] at h1
    obtain ⟨y, hy⟩ := h1
    exact hcon y (by rwa [smul_eq_mul] at hy)
  obtain h | ⟨m, hm, hle⟩ := IsCoatomic.eq_top_or_exists_le_coatom (Ideal.span ({1 - j} : Set R))
  · exact hne h
  · have h1 : (1 - j) ∈ m := hle (Submodule.mem_span_singleton_self _)
    have h2 : j ∈ m := Submodule.mem_sInf.1 hj m hm
    refine hm.1 (eq_top_iff.2 fun w _ ↦ ?_)
    have h3 : (1 : R) ∈ m := by simpa using m.add_mem h1 h2
    simpa using m.smul_mem w h3

/-- An element lies in the Jacobson radical exactly when `1 - a * x` is a unit for every `a`. -/
theorem mem_jacobson_iff {x : R} : x ∈ jacobson R ↔ ∀ a : R, IsUnit (1 - a * x) := by
  constructor
  · intro hx a
    have hax : a * x ∈ jacobson R := by simpa using (jacobson R).smul_mem a hx
    obtain ⟨y, hy⟩ := exists_mul_eq_one_of_mem_jacobson hax
    have hexp : y - y * (a * x) = 1 := by rw [← hy, mul_sub, mul_one]
    have hy2 : y = 1 + y * (a * x) := sub_eq_iff_eq_add.1 hexp
    have hj2 : -(y * (a * x)) ∈ jacobson R := by
      have hmul := (jacobson R).smul_mem y hax
      rw [smul_eq_mul] at hmul
      exact (jacobson R).neg_mem hmul
    obtain ⟨z, hz⟩ := exists_mul_eq_one_of_mem_jacobson hj2
    have hy' : (1 : R) - -(y * (a * x)) = y := by rw [sub_neg_eq_add, ← hy2]
    have hzy : z * y = 1 := by rwa [hy'] at hz
    have hzeq : z = 1 - a * x := by
      calc z = z * (y * (1 - a * x)) := by rw [hy, mul_one]
        _ = (z * y) * (1 - a * x) := by rw [mul_assoc]
        _ = 1 - a * x := by rw [hzy, one_mul]
    exact ⟨⟨1 - a * x, y, by rw [← hzeq]; exact hzy, hy⟩, rfl⟩
  · intro h
    rw [jacobson, Module.jacobson, Submodule.mem_sInf]
    rintro m hm
    by_contra hxm
    have hlt : m < m ⊔ Submodule.span R {x} :=
      lt_of_le_of_ne le_sup_left fun e ↦
        hxm (by rw [e]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
    have h1 : (1 : R) ∈ m ⊔ Submodule.span R {x} := hm.2 _ hlt ▸ Submodule.mem_top
    rw [Submodule.mem_sup] at h1
    obtain ⟨u, hu, v, hv, huv⟩ := h1
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨a, rfl⟩ := hv
    have hmem : (1 : R) - a * x ∈ m := by
      have he : (1 : R) - a * x = u := by rw [← huv, smul_eq_mul, add_sub_cancel_right]
      rwa [he]
    obtain ⟨w, hw⟩ := (h a).exists_left_inv
    refine hm.1 (eq_top_iff.2 fun t _ ↦ ?_)
    have hone : (1 : R) ∈ m := by simpa [hw] using m.smul_mem w hmem
    simpa using m.smul_mem t hone

/-- The membership condition of `Ring.mem_jacobson_iff` in its left-right symmetric form. -/
theorem mem_jacobson_iff_forall {x : R} :
    x ∈ jacobson R ↔ ∀ a b : R, IsUnit (1 - a * x * b) := by
  refine ⟨fun hx a b ↦ ?_, fun h ↦ mem_jacobson_iff.2 fun a ↦ by simpa using h a 1⟩
  have h := mem_jacobson_iff.1 hx (b * a)
  rw [mul_assoc] at h
  exact h.one_sub_mul_comm

/-- **The Jacobson radical is left-right symmetric**: `x` lies in the Jacobson radical of `R` if
and only if it lies in the Jacobson radical of `Rᵐᵒᵖ`, ie the intersection of the maximal right
ideals of `R`. -/
theorem mem_jacobson_op_iff {x : R} :
    MulOpposite.op x ∈ jacobson Rᵐᵒᵖ ↔ x ∈ jacobson R := by
  rw [mem_jacobson_iff_forall, mem_jacobson_iff_forall]
  constructor
  · intro h a b
    have h' := h (MulOpposite.op b) (MulOpposite.op a)
    rw [← MulOpposite.op_one, ← MulOpposite.op_mul, ← MulOpposite.op_mul, ← MulOpposite.op_sub,
      isUnit_op] at h'
    simpa [mul_assoc] using h'
  · intro h A B
    have h' := h B.unop A.unop
    rw [← isUnit_op] at h'
    rw [MulOpposite.op_sub, MulOpposite.op_one, MulOpposite.op_mul, MulOpposite.op_mul,
      MulOpposite.op_unop, MulOpposite.op_unop] at h'
    simpa [mul_assoc] using h'

end Units

end Ring

namespace Submodule

variable {R M}

theorem jacobson_smul_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] (N : Submodule R M) :
    Ring.jacobson R • N < ⊤ :=
  ((smul_mono_right _ le_top).trans <| Ring.jacobson_smul_top_le R M).trans_lt
    (Module.jacobson_lt_top R M)

theorem FG.jacobson_smul_lt {N : Submodule R M} (ne_bot : N ≠ ⊥) (fg : N.FG) :
    Ring.jacobson R • N < N := by
  rw [← Module.Finite.iff_fg] at fg
  rw [← nontrivial_iff_ne_bot] at ne_bot
  convert! map_strictMono_of_injective N.injective_subtype (jacobson_smul_lt_top ⊤)
  on_goal 1 => rw [map_smul'']
  all_goals rw [Submodule.map_top, range_subtype]

/-- A form of Nakayama's lemma for modules over noncommutative rings. -/
theorem FG.eq_bot_of_le_jacobson_smul {N : Submodule R M} (fg : N.FG)
    (le : N ≤ Ring.jacobson R • N) : N = ⊥ := by
  contrapose! le; exact (jacobson_smul_lt le fg).not_ge

end Submodule

end
