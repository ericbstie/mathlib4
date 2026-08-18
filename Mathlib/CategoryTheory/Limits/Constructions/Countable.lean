/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Data.Countable.Basic
public import Mathlib.Logic.Equiv.List

/-!
# Constructing countable limits from finite limits and sequential limits

We construct all countable limits from finite limits together with limits of shape `ℕᵒᵖ`, and
dually all countable colimits from finite colimits together with colimits of shape `ℕ`.

The route is the countable analogue of
`CategoryTheory.Limits.has_limits_of_finite_and_cofiltered`, and it is shorter than that name
suggests: the construction of `α`-indexed products out of finite products only ever needs limits
over the single cofiltered shape `(Finset (Discrete α))ᵒᵖ`. For countable `α` that shape is a
countable cofiltered preorder, so `IsCofiltered.sequentialFunctor` already reduces it to a limit
of shape `ℕᵒᵖ`. In particular no theory of general countable cofiltered categories is required.

## Main results

* `hasLimitsOfShape_of_countable_cofiltered_preorder`: limits over a countable cofiltered preorder
  reduce to limits of shape `ℕᵒᵖ`.
* `hasCountableProducts_of_hasFiniteProducts_and_hasSequentialLimits`: countable products from
  finite products and sequential limits.
* `hasCountableLimits_of_hasCountableProducts_and_hasEqualizers`: the countable analogue of
  `has_limits_of_hasEqualizers_and_products`.
* `hasCountableLimits_of_hasFiniteLimits_and_hasSequentialLimits`: the main result.

Each has a dual, proved directly rather than by passing to `Cᵒᵖ`.
-/

@[expose] public section

universe v u

open CategoryTheory Opposite

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/-- A limit over a countable cofiltered preorder is a sequential limit: `sequentialFunctor` is
initial, so `HasLimitsOfShape ℕᵒᵖ` suffices. -/
theorem hasLimitsOfShape_of_countable_cofiltered_preorder (J : Type*) [Preorder J] [Countable J]
    [IsCofiltered J] [HasLimitsOfShape ℕᵒᵖ C] : HasLimitsOfShape J C :=
  Functor.Initial.hasLimitsOfShape_of_initial (IsCofiltered.sequentialFunctor J)

/-- A colimit over a countable filtered preorder is a sequential colimit: `sequentialFunctor` is
final, so `HasColimitsOfShape ℕ` suffices. -/
theorem hasColimitsOfShape_of_countable_filtered_preorder (J : Type*) [Preorder J] [Countable J]
    [IsFiltered J] [HasColimitsOfShape ℕ C] : HasColimitsOfShape J C :=
  Functor.Final.hasColimitsOfShape_of_final (IsFiltered.sequentialFunctor J)

/-- Countable products can be built from finite products and sequential limits, by taking the
limit over the countable filtered preorder of finite subsets. -/
theorem hasCountableProducts_of_hasFiniteProducts_and_hasSequentialLimits
    [HasFiniteProducts C] [HasLimitsOfShape ℕᵒᵖ C] : HasCountableProducts C where
  out α :=
    have : HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C :=
      Functor.Initial.hasLimitsOfShape_of_initial
        (IsFiltered.sequentialFunctor (Finset (Discrete α))).op
    ⟨fun F => HasLimit.mk (ProductsFromFiniteCofiltered.liftToFinsetLimitCone F)⟩

/-- Countable coproducts can be built from finite coproducts and sequential colimits, by taking
the colimit over the countable filtered preorder of finite subsets. -/
theorem hasCountableCoproducts_of_hasFiniteCoproducts_and_hasSequentialColimits
    [HasFiniteCoproducts C] [HasColimitsOfShape ℕ C] : HasCountableCoproducts C where
  out α :=
    have : HasColimitsOfShape (Finset (Discrete α)) C :=
      Functor.Final.hasColimitsOfShape_of_final
        (IsFiltered.sequentialFunctor (Finset (Discrete α)))
    ⟨fun F => HasColimit.mk (CoproductsFromFiniteFiltered.liftToFinsetColimitCocone F)⟩

/-- The countable analogue of `has_limits_of_hasEqualizers_and_products`: a countable diagram has
countably many objects and countably many morphisms, so the two products appearing in
`hasLimit_of_equalizer_and_product` are both countable. -/
theorem hasCountableLimits_of_hasCountableProducts_and_hasEqualizers
    [HasCountableProducts C] [HasEqualizers C] : HasCountableLimits C where
  out _ _ _ := { has_limit := fun F => hasLimit_of_equalizer_and_product F }

/-- The countable analogue of `has_colimits_of_hasCoequalizers_and_coproducts`. -/
theorem hasCountableColimits_of_hasCountableCoproducts_and_hasCoequalizers
    [HasCountableCoproducts C] [HasCoequalizers C] : HasCountableColimits C where
  out _ _ _ := { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }

/-- A category with finite limits and sequential limits has all countable limits. -/
theorem hasCountableLimits_of_hasFiniteLimits_and_hasSequentialLimits
    [HasFiniteLimits C] [HasLimitsOfShape ℕᵒᵖ C] : HasCountableLimits C :=
  have := hasCountableProducts_of_hasFiniteProducts_and_hasSequentialLimits C
  hasCountableLimits_of_hasCountableProducts_and_hasEqualizers C

/-- A category with finite colimits and sequential colimits has all countable colimits. -/
theorem hasCountableColimits_of_hasFiniteColimits_and_hasSequentialColimits
    [HasFiniteColimits C] [HasColimitsOfShape ℕ C] : HasCountableColimits C :=
  have := hasCountableCoproducts_of_hasFiniteCoproducts_and_hasSequentialColimits C
  hasCountableColimits_of_hasCountableCoproducts_and_hasCoequalizers C

end CategoryTheory.Limits
