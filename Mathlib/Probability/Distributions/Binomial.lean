/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Etienne Marion
-/
module

public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.SetBernoulli

import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Probability.Notation

/-!
# Binomial random variables

This file defines the binomial distribution and binomial random variables,
and computes their expectation and variance. For `n : ℕ` and `p : I`,
the binomial distribution `Bin(n, p)` is defined as the cardinal of a random subset `U`
of `Set.Iic n` such that each `k ∈ Set.Iic n` belongs to `U` independently with probability `p`.

## Main definition

* `ProbabilityTheory.binomial`:
  Binomial distribution on an arbitrary semiring with parameters `n` and `p`.

## Implementation details

We provide the definition `binomial` with notation `Bin(n, P)` as the corresponding measure
over `ℕ`. We also introduce a notation `Bin(R, n p)` for the same measure but over a general
`AddMonoidWithOne R`, that stands for `Bin(n, p).map (Nat.cast : ℕ → R)`. This is in particular
useful if one is interested in the binomial distribution as a measure over `ℝ` or `ℤ`.
Results should be proven for both `Bin(n, p)` and `Bin(R, n, p)` when possible, using the first
one to prove the second. Note that results concerning `Bin(R, n, p)` may require
`[MeasurableSingletonClass R]` and/or `[CharZero R]`.

When referring to `Bin(n, p)` in names, use `binomial`. When referring to `Bin(R, n, p)`,
use `map_cast_binomial`.

## Notation

`Bin(n, p)` is the binomial distribution with parameters `n` and `p` in `ℕ`.
`Bin(R, n, p)` is the binomial distribution with parameters `n` and `p` in `R`.
-/

public section

open MeasureTheory Set Measure
open scoped NNReal ProbabilityTheory unitInterval ENNReal

namespace ProbabilityTheory
variable {R Ω : Type*} [MeasurableSpace R] [AddMonoidWithOne R] {m : MeasurableSpace Ω}
  {P : Measure Ω} {X : Ω → R} {n : ℕ} {p : I}

/-- The binomial probability distribution with parameter `p`. -/
@[expose]
noncomputable def binomial (n : ℕ) (p : I) : Measure ℕ := setBer(Iio n, p).map ncard

/-- The binomial probability distribution with parameter `p`. -/
scoped notation3 "Bin(" n ", " p ")" => binomial n p

/-- The binomial probability distribution with parameter `p` valued in the semiring `R`. -/
scoped notation3 "Bin(" R ", " n ", " p ")" => (binomial n p).map (Nat.cast : ℕ → R)

@[simp]
lemma binomial_nat : Bin(ℕ, n, p) = Bin(n, p) := map_id

lemma binomial_zero : Bin(0, p) = dirac 0 := by simp [binomial]

@[simp]
lemma map_cast_binomial_zero : Bin(R, 0, p) = dirac 0 := by
  simp [binomial, map_dirac' .of_discrete]

instance isProbabilityMeasure_binomial : IsProbabilityMeasure Bin(n, p) :=
  isProbabilityMeasure_map <| by fun_prop

instance isProbabilityMeasure_map_cast_binomial : IsProbabilityMeasure Bin(R, n, p) :=
  isProbabilityMeasure_map .of_discrete

lemma ae_le_of_hasLaw_binomial {X : Ω → ℕ} (hX : HasLaw X Bin(n, p) P) : ∀ᵐ ω ∂P, X ω ≤ n := by
  rw [hX.ae_iff (p := (· ≤ n)) <| by fun_prop, binomial,
    ae_map_iff (by fun_prop) (finite_Iic _).measurableSet]
  filter_upwards [setBernoulli_ae_subset] with s hs
  simpa using ncard_le_ncard hs

lemma binomial_real_singleton (n k : ℕ) (p : I) :
    Bin(n, p).real {k} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  rw [binomial, map_ncard_setBernoulli_real_singleton (finite_Iio n), ncard_Iio_nat]

lemma binomial_singleton (n k : ℕ) (p : I) :
    Bin(n, p) {k} = ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(n, p) _) (by simp), ← measureReal_def,
    binomial_real_singleton]

lemma map_cast_binomial_real_singleton [MeasurableSingletonClass R] [CharZero R] (n k : ℕ) (p : I) :
    Bin(R, n, p).real {(k : R)} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  rw [map_measureReal_apply (by fun_prop) (by measurability)]
  convert binomial_real_singleton n k p
  ext; simp

@[simp]
lemma binomial_nonneg {k : ℕ} : (0 : ℝ) ≤ (n.choose k) * p ^ k * (1 - p) ^ (n - k) :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by grind) _)) (pow_nonneg (by grind) _)

lemma map_cast_binomial_singleton [MeasurableSingletonClass R] [CharZero R] (n k : ℕ) (p : I) :
    Bin(R, n, p) {(k : R)} = ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(R, n, p) _) (by simp), ← measureReal_def,
    map_cast_binomial_real_singleton]

@[simp]
lemma binomial_real_zero (n : ℕ) (p : I) :
    Bin(n, p).real {0} = (1 - p) ^ n := by simp [binomial_real_singleton]

@[simp]
lemma map_cast_binomial_real_zero [MeasurableSingletonClass R] [CharZero R] (n : ℕ) (p : I) :
    Bin(R, n, p).real {0} = (1 - p) ^ n := by
  rw [← Nat.cast_zero, map_cast_binomial_real_singleton]
  simp

@[simp]
lemma binomial_real_self (n : ℕ) (p : I) :
    Bin(n, p).real {n} = p ^ n := by simp [binomial_real_singleton]

@[simp]
lemma map_cast_binomial_real_self [MeasurableSingletonClass R] [CharZero R] (n : ℕ) (p : I) :
    Bin(R, n, p).real {(n : R)} = p ^ n := by simp [map_cast_binomial_real_singleton]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma binomial_one_eq_bernoulliMeasure (p : I) :
    Bin(1, p) = Ber(1, 0, p) := by
  refine ext_of_measureReal_singleton fun k ↦ ?_
  match k with
  | 0 | 1 => simp
  | k + 2 => simp [binomial_real_singleton]

lemma binomial_eq_sum_dirac (n : ℕ) (p : I) :
    Bin(n, p) =
      ∑ k ∈ Finset.Iic n, ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) • dirac k := by
  refine ext_of_singleton fun k ↦ ?_
  rw [binomial_singleton, finsetSum_apply, Finset.sum_eq_single k]
  · simp
  · simp_all
  · simp_all [Nat.choose_eq_zero_of_lt]

lemma map_cast_binomial_eq_sum_dirac [MeasurableSingletonClass R] (n : ℕ) (p : I) :
    Bin(R, n, p) =
      ∑ k ∈ Finset.Iic n, ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) •
        dirac (k : R) := by
  rw [binomial_eq_sum_dirac, Measure.map_finset_sum .of_discrete]
  exact Finset.sum_congr rfl fun _ _ ↦ by rw [Measure.map_smul, map_dirac]

section Integral

variable {E : Type*} [NormedAddCommGroup E]

lemma integrable_map_cast_binomial [MeasurableSingletonClass R] (f : R → E) :
    Integrable f Bin(R, n, p) := by
  simp [map_cast_binomial_eq_sum_dirac, integrable_finsetSum_measure, integrable_dirac,
    Integrable.smul_measure]

lemma integrable_binomial (f : ℕ → E) :
    Integrable f Bin(n, p) := (integrable_map_cast_binomial f).comp_measurable .of_discrete

variable [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_binomial (f : ℕ → E) :
    ∫ x, f x ∂Bin(n, p) =
      ∑ k ∈ Finset.Iic n, (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [binomial_eq_sum_dirac, integral_finsetSum_measure]
  · simp
  exact fun _ _ ↦ (integrable_dirac (by simp)).smul_measure (by simp)

lemma integral_map_cast_binomial [MeasurableSingletonClass R] (f : R → E) :
    ∫ x, f x ∂Bin(R, n, p) =
      ∑ k ∈ Finset.Iic n, (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [integral_map .of_discrete (integrable_map_cast_binomial f).aestronglyMeasurable,
    integral_binomial]

end Integral

/-! ### Binomial random variables -/

variable {X : Ω → ℝ}

/-- The first moment of the binomial weights: `∑ k, C(N, k) a ^ k (1 - a) ^ (N - k) * k = a * N`. -/
private lemma sum_range_choose_mul_pow_mul_cast (N : ℕ) (a : ℝ) :
    ∑ k ∈ Finset.range (N + 1), ((N.choose k : ℝ) * a ^ k * (1 - a) ^ (N - k)) * (k : ℝ)
      = a * N := by
  rw [Finset.sum_range_succ']
  cases N with norm_num | succ N
  calc
    _ = a * ∑ x ∈ Finset.range (N + 1), (N + 1).choose (x + 1) * (x + 1) *
        a ^ x * (1 - a) ^ (N - x) := by grind [Finset.mul_sum]
    _ = a * ∑ x ∈ Finset.range (N + 1), N.choose x * (N + 1) * a ^ x * (1 - a) ^ (N - x) := by
      congrm a * ∑ x ∈ Finset.range (N + 1), ?_ * a ^ x * (1 - a) ^ (N - x)
      norm_cast
      rw [← Nat.add_one_mul_choose_eq N x, mul_comm]
    _ = a * (N + 1) * ∑ x ∈ Finset.range (N + 1), N.choose x * a ^ x * (1 - a) ^ (N - x) := by
      rw [mul_assoc, Finset.mul_sum (a := (N : ℝ) + 1)]
      group
    _ = a * (N + 1) := by grind [add_pow a (1 - a) N, one_pow]

/-- The second moment of the binomial weights:
`∑ k, C(N, k) a ^ k (1 - a) ^ (N - k) * k ^ 2 = a (1 - a) N + (a N) ^ 2`. -/
private lemma sum_range_choose_mul_pow_mul_cast_sq (N : ℕ) (a : ℝ) :
    ∑ k ∈ Finset.range (N + 1), ((N.choose k : ℝ) * a ^ k * (1 - a) ^ (N - k)) * (k : ℝ) ^ 2
      = a * (1 - a) * N + (a * N) ^ 2 := by
  rw [Finset.sum_range_succ']
  cases N with norm_num | succ N
  have hsum : ∑ x ∈ Finset.range (N + 1), ((N.choose x : ℝ) * a ^ x * (1 - a) ^ (N - x)) = 1 := by
    grind [add_pow a (1 - a) N, one_pow]
  have hfst := sum_range_choose_mul_pow_mul_cast N a
  calc
    _ = a * ∑ x ∈ Finset.range (N + 1), ((N + 1).choose (x + 1) * (x + 1)) * ((x : ℝ) + 1) *
        a ^ x * (1 - a) ^ (N - x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      simp only [Nat.succ_sub_succ]
      ring
    _ = a * ∑ x ∈ Finset.range (N + 1), (N.choose x * (N + 1)) * ((x : ℝ) + 1) *
        a ^ x * (1 - a) ^ (N - x) := by
      congrm a * ∑ x ∈ Finset.range (N + 1), ?_ * ((x : ℝ) + 1) * a ^ x * (1 - a) ^ (N - x)
      norm_cast
      rw [← Nat.add_one_mul_choose_eq N x, mul_comm]
    _ = a * (N + 1) * ∑ x ∈ Finset.range (N + 1),
          (((N.choose x : ℝ) * a ^ x * (1 - a) ^ (N - x)) * (x : ℝ)
            + ((N.choose x : ℝ) * a ^ x * (1 - a) ^ (N - x))) := by
      rw [mul_assoc, Finset.mul_sum (a := (N : ℝ) + 1)]
      exact congrArg _ (Finset.sum_congr rfl fun x _ ↦ by ring)
    _ = a * (N + 1) * (a * N + 1) := by rw [Finset.sum_add_distrib, hfst, hsum]
    _ = _ := by ring

/-- **Expectation of a binomial random variable**.

The expectation of a binomial random variable with parameters `n` and `p` is `pn`. -/
theorem integral_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) : P[X] = p.val * n := by
  rw [hX.integral_eq, integral_map_cast_binomial, ← n.range_succ_eq_Iic]
  simpa using sum_range_choose_mul_pow_mul_cast n p

/-- **Variance of a binomial random variable**.

The variance of a binomial random variable with parameters `n` and `p` is `p(1 - p)n`. -/
theorem variance_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) :
    Var[X; P] = p * (1 - p) * n := by
  have hmem : MemLp id 2 Bin(ℝ, n, p) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 (integrable_map_cast_binomial _)
  rw [hX.variance_eq, variance_eq_sub hmem, integral_of_hasLaw_binomial HasLaw.id,
    show ((id : ℝ → ℝ) ^ 2) = (fun x : ℝ ↦ x ^ 2) from rfl, integral_map_cast_binomial,
    ← n.range_succ_eq_Iic]
  simp only [smul_eq_mul]
  rw [sum_range_choose_mul_pow_mul_cast_sq n p]
  ring

/-- **Conditional variance of a Bernoulli random variable**.

The conditional variance of a `{0, 1}`-valued random variable is the product of the conditional
probabilities that it is equal to `1` and that it is equal to `0`.

This fails for `Bin(ℝ, n, p)` as soon as `n ≥ 2`: conditioning on the trivial σ-algebra it would
say `n * p * (1 - p) = n * p * (1 - n * p)`, which is false for `n = 2`, `p = 1 / 2`. -/
theorem condVar_of_hasLaw_binomial_one {m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    {P : Measure[m₀] Ω} (hX : HasLaw X Bin(ℝ, 1, p) P) :
    Var[X; P | m] =ᵐ[P] P[X | m] * P[1 - X | m] := by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have h01 : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1 := by
    refine (hX.ae_iff (p := fun x : ℝ ↦ x = 0 ∨ x = 1) (by fun_prop)).2 ?_
    rw [ae_map_iff (by fun_prop) (by measurability)]
    filter_upwards [ae_le_of_hasLaw_binomial (P := Bin(1, p)) HasLaw.id] with k hk
    simp only [id_eq] at hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl <;> norm_num
  refine condVar_eq_condExp_mul_condExp_one_sub hm ?_ ?_
  · exact memLp_of_bounded (a := 0) (b := 1)
      (by filter_upwards [h01] with ω hω; rcases hω with h | h <;> simp [h])
      hX.aemeasurable.aestronglyMeasurable 2
  · filter_upwards [h01] with ω hω
    rcases hω with h | h <;> simp [h]

end ProbabilityTheory
