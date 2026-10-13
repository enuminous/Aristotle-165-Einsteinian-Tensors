import Verified.Sectors

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace FieldSpaceCheck

open Sector

/-- FS-T01: there are 165 triplets. -/
theorem triplets_card : triplets.card = 165 := by decide +kernel

/-- FS-T02: every sector lies in exactly 45 triplets. -/
theorem sector_incidence (s : Sector) : (triplets.filter (s ∈ ·)).card = 45 := by
  revert s; decide +kernel

/-- FS-T03: every pair of distinct sectors lies in exactly 9 triplets. -/
theorem pair_incidence (s t : Sector) (h : s ≠ t) :
    (triplets.filter (fun x => s ∈ x ∧ t ∈ x)).card = 9 := by
  revert s t; decide +kernel

end FieldSpaceCheck
