/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

variable {R : Type*} [Ring R]

-- `IsSemiprimaryRing.mulOpposite` is now proved, using the left-right symmetry of the Jacobson
-- radical (`Ring.mem_jacobson_op_iff`). The `Iff` version below still needs a transfer of
-- `IsSemiprimaryRing` along a `RingEquiv` — apply `IsSemiprimaryRing.mulOpposite` to `Rᵐᵒᵖ` and
-- move back along `RingEquiv.opOp`, exactly as `isSemisimpleRing_mulOpposite_iff` does with
-- `RingEquiv.isSemisimpleRing`. That transfer needs `Ring.map_jacobson_of_ker_le` plus a
-- quotient equivalence, in the style of `Ring.jacobsonOpQuotEquiv`.
proof_wanted isSemiprimaryRing_mulOpposite_iff : IsSemiprimaryRing Rᵐᵒᵖ ↔ IsSemiprimaryRing R

-- A left Artinian ring is right Noetherian iff it is right Artinian. To be left as an `example`.
proof_wanted IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite
    [IsArtinianRing R] : IsNoetherianRing Rᵐᵒᵖ ↔ IsArtinianRing Rᵐᵒᵖ
