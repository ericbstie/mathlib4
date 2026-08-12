/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

variable {R : Type*} [Ring R]

-- The element-level left-right symmetry of the Jacobson radical is now available as
-- `Ring.mem_jacobson_op_iff`. What is still missing is the ideal-level transport: an
-- identification of `Ring.jacobson Rᵐᵒᵖ` with the image of `Ring.jacobson R` under `op`,
-- carrying nilpotency and the ring equivalence `Rᵐᵒᵖ ⧸ jacobson Rᵐᵒᵖ ≃+* (R ⧸ jacobson R)ᵐᵒᵖ`
-- (then `isSemisimpleRing_mulOpposite_iff` finishes the job).
proof_wanted IsSemiprimaryRing.mulOpposite [IsSemiprimaryRing R] : IsSemiprimaryRing Rᵐᵒᵖ

proof_wanted isSemiprimaryRing_mulOpposite_iff : IsSemiprimaryRing Rᵐᵒᵖ ↔ IsSemiprimaryRing R

-- A left Artinian ring is right Noetherian iff it is right Artinian. To be left as an `example`.
proof_wanted IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite
    [IsArtinianRing R] : IsNoetherianRing Rᵐᵒᵖ ↔ IsArtinianRing Rᵐᵒᵖ
