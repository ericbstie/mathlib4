/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Left-right symmetry of the Artinian and Noetherian conditions

Combining the Hopkins–Levitzki theorem (`IsSemiprimaryRing.isNoetherian_iff_isArtinian`) with the
left-right symmetry of the semiprimary condition (`isSemiprimaryRing_mulOpposite_iff`), we obtain
that over a left Artinian ring the *right* Noetherian and *right* Artinian conditions agree.

Note that a left Artinian ring need not be right Artinian, so this is not simply a restatement of
`instIsNoetherianRingOfIsArtinianRing`.

## Main results

* `IsArtinianRing.isNoetherianRing_mulOpposite_iff` : if `R` is left Artinian, then `Rᵐᵒᵖ` is
  Noetherian if and only if it is Artinian.
-/

@[expose] public section

variable (R : Type*) [Ring R]

/-- Over a left Artinian ring `R`, the right Noetherian and right Artinian conditions agree.
This is the Hopkins–Levitzki theorem applied to `Rᵐᵒᵖ`, which is semiprimary because `R` is. -/
theorem IsArtinianRing.isNoetherianRing_mulOpposite_iff [IsArtinianRing R] :
    IsNoetherianRing Rᵐᵒᵖ ↔ IsArtinianRing Rᵐᵒᵖ :=
  have : IsSemiprimaryRing Rᵐᵒᵖ := IsSemiprimaryRing.mulOpposite
  IsSemiprimaryRing.isNoetherian_iff_isArtinian
