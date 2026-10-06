import Mathlib
import RequestProject.Upstream.Structure

namespace FieldSpace

/-- Number of rank-3 blocks remaining after deleting k named sectors. -/
def remainingTriplets (removed : Nat) : Nat :=
  Nat.choose (11 - removed) 3

theorem remove_one_remaining : remainingTriplets 1 = 120 := by
  native_decide

theorem remove_two_remaining : remainingTriplets 2 = 84 := by
  native_decide

theorem remove_three_remaining : remainingTriplets 3 = 56 := by
  native_decide

theorem remove_one_deleted : 165 - remainingTriplets 1 = 45 := by
  native_decide

theorem remove_two_deleted : 165 - remainingTriplets 2 = 81 := by
  native_decide

theorem remove_three_deleted : 165 - remainingTriplets 3 = 109 := by
  native_decide

end FieldSpace
