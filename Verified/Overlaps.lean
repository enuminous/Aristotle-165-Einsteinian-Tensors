import Verified.Ablation

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace FieldSpaceCheck

open Sector

/-- Choose the intersection inside a and the remainder outside a. This gives
the overlap count without enumerating the 27,060 ordered pairs. -/
private theorem overlap_row (a : Finset Sector) (ha : a ∈ triplets)
    (k : ℕ) (hk : k < 3) :
    (triplets.filter (fun b => a ≠ b ∧ (a ∩ b).card = k)).card =
      Nat.choose 3 k * Nat.choose 8 (3-k) := by
  have ha3 : a.card = 3 := (Finset.mem_powersetCard.mp ha).2
  have hcard : (triplets.filter (fun b => a ≠ b ∧ (a ∩ b).card = k)).card =
      (a.powersetCard k ×ˢ (Finset.univ \ a).powersetCard (3-k)).card := by
    apply Finset.card_bij (fun b _ => (a ∩ b, b \ a))
    · intro b hb
      rcases Finset.mem_filter.mp hb with ⟨hb, hne, hi⟩
      have hb3 : b.card = 3 := (Finset.mem_powersetCard.mp hb).2
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hi⟩
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro x hx
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
        · rw [Finset.card_sdiff, hb3, hi]
    · intro b hb c hc h
      have hi := congrArg Prod.fst h
      have hd := congrArg Prod.snd h
      have hrec (b : Finset Sector) : (b \ a) ∪ (a ∩ b) = b := by
        rw [Finset.inter_comm, Finset.sdiff_union_inter]
      calc
        b = (b \ a) ∪ (a ∩ b) := (hrec b).symm
        _ = (c \ a) ∪ (a ∩ c) := by rw [hi, hd]
        _ = c := hrec c
    · intro pair hp
      rcases Finset.mem_product.mp hp with ⟨hp1,hp2⟩
      rcases Finset.mem_powersetCard.mp hp1 with ⟨hca,hck⟩
      rcases Finset.mem_powersetCard.mp hp2 with ⟨hda,hdcard⟩
      have hdis : Disjoint pair.1 pair.2 := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        exact (Finset.mem_sdiff.mp (hda hy)).2 (hca hx)
      have hi : a ∩ (pair.1 ∪ pair.2) = pair.1 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxa, hxc | hxd⟩
          · exact hxc
          · exact False.elim ((Finset.mem_sdiff.mp (hda hxd)).2 hxa)
        · intro hxc
          exact ⟨hca hxc, Or.inl hxc⟩
      have hd : (pair.1 ∪ pair.2) \ a = pair.2 := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxc | hxd, hna⟩
          · exact False.elim (hna (hca hxc))
          · exact hxd
        · intro hxd
          exact ⟨Or.inr hxd, (Finset.mem_sdiff.mp (hda hxd)).2⟩
      refine ⟨pair.1 ∪ pair.2, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_powersetCard.mpr
          refine ⟨Finset.subset_univ _, ?_⟩
          rw [Finset.card_union_of_disjoint hdis, hck, hdcard]
          omega
        · constructor
          · intro heq
            have : (a ∩ (pair.1 ∪ pair.2)).card = 3 := by rw [← heq, Finset.inter_self, ha3]
            rw [hi,hck] at this
            omega
          · rw [hi,hck]
      · exact Prod.ext hi hd
  rw [hcard, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset (Finset.subset_univ a), ha3]
  rfl

/-- Count ordered overlaps by summing small fibers, avoiding a giant kernel
reduction over the materialized 27,060-element off-diagonal product. -/
private theorem overlap_count (k count : ℕ)
    (hrow : ∀ a ∈ triplets,
      (triplets.filter (fun b => a ≠ b ∧ (a ∩ b).card = k)).card = count) :
    (triplets.offDiag.filter (fun p => (p.1 ∩ p.2).card = k)).card = 165 * count := by
  have hoff : triplets.offDiag =
      (triplets ×ˢ triplets).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp [Finset.mem_offDiag, and_assoc]
  calc
    _ = ∑ a ∈ triplets,
        (triplets.filter (fun b => a ≠ b ∧ (a ∩ b).card = k)).card := by
      simp [hoff, Finset.filter_filter, Finset.card_eq_sum_ones,
        Finset.sum_filter, Finset.sum_product]
    _ = triplets.card * count := by simp [hrow]
    _ = 165 * count := by rw [triplets_card]

/-- FS-T07: overlap spectrum of ordered distinct pairs, twice the unordered counts. -/
theorem overlap_spectrum :
    let pairs := triplets.offDiag
    (pairs.filter (fun p => (p.1 ∩ p.2).card = 2)).card = 2 * 1980 ∧
    (pairs.filter (fun p => (p.1 ∩ p.2).card = 1)).card = 2 * 6930 ∧
    (pairs.filter (fun p => (p.1 ∩ p.2).card = 0)).card = 2 * 4620 ∧
    pairs.card = 2 * 13530 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact overlap_count 2 24 (fun a ha => by simpa using overlap_row a ha 2 (by decide))
  · exact overlap_count 1 84 (fun a ha => by simpa using overlap_row a ha 1 (by decide))
  · exact overlap_count 0 56 (fun a ha => by simpa using overlap_row a ha 0 (by decide))
  · rw [Finset.offDiag_card, triplets_card]
    norm_num

end FieldSpaceCheck
