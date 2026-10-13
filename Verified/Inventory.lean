import Verified.Classes

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace FieldSpaceCheck

open Sector

/-- Expected statement count of a fully populated block under the source grammar:
one Einstein equation if `E` is present, two statements (dynamics + Bianchi) per gauge
sector, and one scalar equation per scalar sector. -/
def statements (x : Finset Sector) : ℕ :=
  (if E ∈ x then 1 else 0) + 2 * (x.filter (isGauge ·)).card + (x.filter (isScalar ·)).card

/-- FS-T05: the inventory `45 + 90 + 90 + 360 = 585`. -/
theorem statement_inventory :
    (triplets.filter (E ∈ ·)).card = 45 ∧
    (∑ x ∈ triplets, (x.filter (isGauge ·)).card) = 90 ∧
    (∑ x ∈ triplets, (x.filter (isScalar ·)).card) = 360 ∧
    (∑ x ∈ triplets, statements x) = 585 := by
  decide +kernel

end FieldSpaceCheck
