import Verified.Incidence

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace FieldSpaceCheck

open Sector

/-- Kind profile of a triplet: (has gravity, number of gauge sectors, number of scalars). -/
def profile (x : Finset Sector) : Bool × ℕ × ℕ :=
  (decide (E ∈ x), (x.filter (isGauge ·)).card, (x.filter (isScalar ·)).card)

/-- FS-T04: the six-class decomposition `56 + 56 + 28 + 16 + 8 + 1 = 165`. -/
theorem class_counts :
    (triplets.filter (profile · = (false, 0, 3))).card = 56 ∧
    (triplets.filter (profile · = (false, 1, 2))).card = 56 ∧
    (triplets.filter (profile · = (true, 0, 2))).card = 28 ∧
    (triplets.filter (profile · = (true, 1, 1))).card = 16 ∧
    (triplets.filter (profile · = (false, 2, 1))).card = 8 ∧
    (triplets.filter (profile · = (true, 2, 0))).card = 1 := by
  decide +kernel

/-- The six classes exhaust the atlas. -/
theorem classes_exhaustive : ∀ x ∈ triplets, profile x ∈
    ({(false, 0, 3), (false, 1, 2), (true, 0, 2), (true, 1, 1), (false, 2, 1), (true, 2, 0)} :
      Finset (Bool × ℕ × ℕ)) := by
  decide +kernel

end FieldSpaceCheck
