import Verified.Overlaps

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace FieldSpaceCheck

open Sector

/-! ## Candidate law FS-C02 (master-action reciprocity), in its simplest form

If the `i`–`j` pair coupling comes from a bilinear potential term `λ φ_i φ_j`, the
coefficient of `φ_j` in the `φ_i` equation equals the coefficient of `φ_i` in the `φ_j`
equation. -/
theorem bilinear_reciprocity (lam a b : ℝ) :
    HasDerivAt (fun x => lam * x * b) (lam * b) a ∧
    HasDerivAt (fun y => lam * a * y) (lam * a) b := by
  constructor
  · simpa using ((hasDerivAt_id a).const_mul lam).mul_const b
  · simpa using (hasDerivAt_id b).const_mul (lam * a)

end FieldSpaceCheck
