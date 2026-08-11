/-
Copyright (c) 2024 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Set.Card
public import Mathlib.Order.KrullDimension

/-!
# Height and coheight in a linear order

In a linear order, every subset of `Set.Iio a` is a chain, so the height of `a` is simply the
number of elements strictly below `a`. Dually, the coheight of `a` is the number of elements
strictly above `a`.

## Main results

* `Order.height_of_linearOrder`: `height a = (Set.Iio a).encard` in a linear order.
* `Order.coheight_of_linearOrder`: `coheight a = (Set.Ioi a).encard` in a linear order.

These results are stated using `Set.encard`, hence live in a separate file from
`Mathlib/Order/KrullDimension.lean`, which does not import `Mathlib/Data/Set/Card.lean`.
-/

@[expose] public section

assert_not_exists Field

namespace Order

variable {α : Type*} [LinearOrder α]

/-- In a linear order, the height of `a` is the number of elements strictly below `a`. -/
theorem height_of_linearOrder (a : α) : height a = (Set.Iio a).encard := by
  refine le_antisymm (height_le_iff.2 fun p hp ↦ ?_) ?_
  · -- Every element of `p` except the last one lies strictly below `a`, and `p` is injective.
    have h : (Set.univ : Set (Fin p.length)).encard ≤ (Set.Iio a).encard :=
      Set.encard_le_encard_of_injOn (f := fun i ↦ p i.castSucc)
        (fun i _ ↦ (p.strictMono (by simp [Fin.castSucc_lt_last])).trans_le hp)
        fun i _ j _ h ↦ by simpa using p.strictMono.injective h
    simpa using h
  · -- Conversely, any `k` elements below `a`, together with `a`, form a chain of length `k`.
    refine ENat.forall_natCast_le_iff_le.1 fun k hk ↦ ?_
    obtain ⟨t, hts, htk⟩ := Set.exists_subset_encard_eq hk
    have hfin : t.Finite := Set.finite_of_encard_eq_coe htk
    have hane : a ∉ hfin.toFinset := fun h ↦ by simpa using hts (hfin.mem_toFinset.1 h)
    have hcard : (insert a hfin.toFinset).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hane]
      congr 1
      have h : (hfin.toFinset : Set α).encard = k := by rwa [hfin.coe_toFinset]
      rw [Set.encard_coe_eq_coe_finsetCard] at h
      exact_mod_cast h
    set f := Finset.orderEmbOfFin (insert a hfin.toFinset) hcard
    have hle : (LTSeries.mk k f f.strictMono).last ≤ a := by
      rcases Finset.mem_insert.1 (Finset.orderEmbOfFin_mem _ hcard (Fin.last k)) with h | h
      · exact h.le
      · exact (hts (hfin.mem_toFinset.1 h)).le
    simpa using length_le_height hle

/-- In a linear order, the coheight of `a` is the number of elements strictly above `a`. -/
theorem coheight_of_linearOrder (a : α) : coheight a = (Set.Ioi a).encard :=
  height_of_linearOrder (α := αᵒᵈ) a

end Order
