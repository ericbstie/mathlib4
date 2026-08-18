/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable

open CategoryTheory

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

namespace IsCofiltered

@[stacks 0032]
proof_wanted preorder_of_cofiltered (J : Type*) [Category* J] [IsCofiltered J] :
    ∃ (I : Type*) (_ : Preorder I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial

/--
The proof of `preorder_of_cofiltered` should give a countable `I` in the case that `J` is a
countable category.
-/
proof_wanted preorder_of_cofiltered_countable
    (J : Type*) [SmallCategory J] [IsCofiltered J] [CountableCategory J] :
    ∃ (I : Type) (_ : Preorder I) (_ : Countable I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial

/--
Put together `sequentialFunctor_initial` and `preorder_of_cofiltered_countable`.
-/
proof_wanted hasCofilteredCountableLimits_of_hasSequentialLimits [HasLimitsOfShape ℕᵒᵖ C] :
    ∀ (J : Type) [SmallCategory J] [IsCofiltered J] [CountableCategory J], HasLimitsOfShape J C

-- The two remaining statements of this section, on building all countable (co)limits out of
-- finite (co)limits and sequential (co)limits, are now proved in
-- `Mathlib/CategoryTheory/Limits/Constructions/Countable.lean`. They turned out not to depend on
-- the three statements above: building `α`-indexed products from finite products only ever needs
-- limits over the single cofiltered shape `(Finset (Discrete α))ᵒᵖ`, which for countable `α` is a
-- countable *preorder*, so `sequentialFunctor` already covers it. Note also that the colimit
-- statement was previously written with hypothesis `[HasLimitsOfShape ℕ C]`; that was a typo for
-- `[HasColimitsOfShape ℕ C]`, since sequential colimits, not limits, are what the construction
-- consumes.

end IsCofiltered

end CategoryTheory.Limits
