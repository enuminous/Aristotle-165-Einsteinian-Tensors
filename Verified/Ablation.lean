import Verified.Inventory

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace FieldSpaceCheck

open Sector

/-- FS-T06: deleting a set `D` of `k` sectors leaves `C(11-k,3)` triplets, all of which
are exactly the triplets of the remaining sectors (closure under vertex deletion). -/
theorem ablation (D : Finset Sector) :
    (triplets.filter (fun x => Disjoint x D)).card = Nat.choose (11 - D.card) 3 := by
  have : triplets.filter (fun x => Disjoint x D) = (Finset.univ \ D).powersetCard 3 := by
    ext x
    simp [triplets, Finset.mem_powersetCard, Finset.subset_sdiff, and_comm]
  rw [this, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  rfl

end FieldSpaceCheck
