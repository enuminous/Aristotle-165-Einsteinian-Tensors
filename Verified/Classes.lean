import Verified.Incidence

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace FieldSpaceCheck

open Sector

/-- Kind profile of a triplet: (has gravity, number of gauge sectors, number of scalars). -/
def profile (x : Finset Sector) : Bool × ℕ × ℕ :=
  (decide (E ∈ x), (x.filter (isGauge ·)).card, (x.filter (isScalar ·)).card)

private theorem count_three_scalars :
    (triplets.filter (profile · = (false, 0, 3))).card = 56 := by decide
private theorem count_gauge_two_scalars :
    (triplets.filter (profile · = (false, 1, 2))).card = 56 := by decide
private theorem count_gravity_two_scalars :
    (triplets.filter (profile · = (true, 0, 2))).card = 28 := by decide
private theorem count_gravity_gauge_scalar :
    (triplets.filter (profile · = (true, 1, 1))).card = 16 := by decide
private theorem count_two_gauges_scalar :
    (triplets.filter (profile · = (false, 2, 1))).card = 8 := by decide
private theorem count_gravity_two_gauges :
    (triplets.filter (profile · = (true, 2, 0))).card = 1 := by decide

/-- FS-T04: the six-class decomposition `56 + 56 + 28 + 16 + 8 + 1 = 165`. -/
theorem class_counts :
    (triplets.filter (profile · = (false, 0, 3))).card = 56 ∧
    (triplets.filter (profile · = (false, 1, 2))).card = 56 ∧
    (triplets.filter (profile · = (true, 0, 2))).card = 28 ∧
    (triplets.filter (profile · = (true, 1, 1))).card = 16 ∧
    (triplets.filter (profile · = (false, 2, 1))).card = 8 ∧
    (triplets.filter (profile · = (true, 2, 0))).card = 1 := by
  exact ⟨count_three_scalars, count_gauge_two_scalars, count_gravity_two_scalars,
    count_gravity_gauge_scalar, count_two_gauges_scalar, count_gravity_two_gauges⟩

/-- The six classes exhaust the atlas. -/
theorem classes_exhaustive : ∀ x ∈ triplets, profile x ∈
    ({(false, 0, 3), (false, 1, 2), (true, 0, 2), (true, 1, 1), (false, 2, 1), (true, 2, 0)} :
      Finset (Bool × ℕ × ℕ)) := by
  intro x hx
  have hx3 : x.card = 3 := (Finset.mem_powersetCard.mp hx).2
  have hg : (x.filter (isGauge ·)).card ≤ 2 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ x))).trans
      (by decide)
  have he : (x.filter (· = E)).card = (if E ∈ x then 1 else 0) := by
    by_cases h : E ∈ x <;> simp [Finset.filter_eq', h]
  have hsum : (if E ∈ x then 1 else 0) + (x.filter (isGauge ·)).card +
      (x.filter (isScalar ·)).card = 3 := by
    rw [← he, ← hx3]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    cases s <;> simp [isGauge, isScalar]
  by_cases hE : E ∈ x
  · simp only [if_pos hE] at hsum
    have hs : (x.filter (isScalar ·)).card = 2 - (x.filter (isGauge ·)).card := by omega
    interval_cases hgval : (x.filter (isGauge ·)).card <;> simp [profile, hE, hgval, hs]
  · simp only [if_neg hE] at hsum
    have hs : (x.filter (isScalar ·)).card = 3 - (x.filter (isGauge ·)).card := by omega
    interval_cases hgval : (x.filter (isGauge ·)).card <;> simp [profile, hE, hgval, hs]

end FieldSpaceCheck
