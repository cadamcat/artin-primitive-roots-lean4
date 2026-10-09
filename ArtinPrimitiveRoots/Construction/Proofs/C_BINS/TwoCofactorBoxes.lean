import ArtinPrimitiveRoots.Construction.Defs

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Classical ArtinPrimitiveRoots.TypeII

/-- Two adjacent cofactor dyads cover every supported term in one prime dyad. -/
theorem two_cofactor_boxes_reindex
    (x H : ℝ) (q : ℕ) (f : ℕ → ℂ)
    (hx : 0 < x) (hH : 1 ≤ H)
    (hqlo : H ≤ (q : ℝ)) (hqhi : (q : ℝ) < 2 * H)
    (hSupport : ∀ m, f m ≠ 0 →
      x < ((m * q : ℕ) : ℝ) ∧ ((m * q : ℕ) : ℝ) < 2 * x) :
    (∑ m ∈ Finset.range (⌊2 * x⌋₊ + 1), f m) =
      (∑ m ∈ (dyadicIntegers (x / (2 * H))).filter
          (fun m : ℕ => (m : ℝ) < x / H), f m) +
      (∑ m ∈ (dyadicIntegers (x / H)).filter
          (fun m : ℕ => (m : ℝ) < 2 * (x / H)), f m) := by
  classical
  have hHpos : 0 < H := by linarith
  have hHne : H ≠ 0 := ne_of_gt hHpos
  have hqpos : 0 < (q : ℝ) := hHpos.trans_le hqlo
  have hFirstPos : 0 < x / (2 * H) := by positivity
  have hSecondPos : 0 < x / H := by positivity
  have hMiddle : 2 * (x / (2 * H)) = x / H := by
    field_simp [hHne]
  have hDyadic (V : ℝ) (hV : 0 ≤ V) (m : ℕ) :
      m ∈ dyadicIntegers V ↔ V ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * V := by
    unfold dyadicIntegers
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hm
      refine ⟨Nat.lt_succ_iff.mpr ?_, hm⟩
      exact (Nat.le_floor_iff (by positivity : 0 ≤ 2 * V)).mpr hm.2
  have hRange (m : ℕ) :
      m ∈ Finset.range (⌊2 * x⌋₊ + 1) ↔ (m : ℝ) ≤ 2 * x := by
    rw [Finset.mem_range, Nat.lt_succ_iff,
      Nat.le_floor_iff (by positivity : 0 ≤ 2 * x)]
  let A := (dyadicIntegers (x / (2 * H))).filter
    (fun m : ℕ => (m : ℝ) < x / H)
  let B := (dyadicIntegers (x / H)).filter
    (fun m : ℕ => (m : ℝ) < 2 * (x / H))
  have hXH : x / H ≤ x := by
    apply (div_le_iff₀ hHpos).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hH hx.le
  have hASub : A ⊆ Finset.range (⌊2 * x⌋₊ + 1) := by
    intro m hm
    apply (hRange m).mpr
    have hmhi : (m : ℝ) < x / H := (Finset.mem_filter.mp hm).2
    linarith
  have hBSub : B ⊆ Finset.range (⌊2 * x⌋₊ + 1) := by
    intro m hm
    apply (hRange m).mpr
    have hmhi : (m : ℝ) < 2 * (x / H) := (Finset.mem_filter.mp hm).2
    linarith
  have hDisjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro m hmA hmB
    have hmhi : (m : ℝ) < x / H := (Finset.mem_filter.mp hmA).2
    have hmlo : x / H ≤ (m : ℝ) :=
      ((hDyadic _ hSecondPos.le m).mp (Finset.mem_filter.mp hmB).1).1
    exact not_lt_of_ge hmlo hmhi
  have hCover (m : ℕ) (hm : f m ≠ 0) : m ∈ A ∪ B := by
    have hprod : x < (m : ℝ) * (q : ℝ) ∧ (m : ℝ) * (q : ℝ) < 2 * x := by
      simpa only [Nat.cast_mul] using hSupport m hm
    have hmpos : 0 < (m : ℝ) := by
      by_contra hbad
      have hmzero : (m : ℝ) = 0 :=
        le_antisymm (not_lt.mp hbad) (Nat.cast_nonneg m)
      rw [hmzero, zero_mul] at hprod
      linarith
    have hLower : x / (2 * H) < (m : ℝ) := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * H)).mpr
      exact hprod.1.trans (mul_lt_mul_of_pos_left hqhi hmpos)
    have hUpper : (m : ℝ) < 2 * (x / H) := by
      have hmul : (m : ℝ) * H < 2 * x :=
        (mul_le_mul_of_nonneg_left hqlo hmpos.le).trans_lt hprod.2
      have hdiv := (lt_div_iff₀ hHpos).mpr hmul
      simpa only [mul_div_assoc] using hdiv
    by_cases hMid : (m : ℝ) < x / H
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨(hDyadic _ hFirstPos.le m).mpr ⟨hLower.le, ?_⟩, hMid⟩
      rw [hMiddle]
      exact hMid.le
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr
        ⟨(hDyadic _ hSecondPos.le m).mpr ⟨le_of_not_gt hMid, hUpper.le⟩, hUpper⟩
  have hUnionSub : A ∪ B ⊆ Finset.range (⌊2 * x⌋₊ + 1) :=
    Finset.union_subset hASub hBSub
  have hSum : (∑ m ∈ A ∪ B, f m) =
      ∑ m ∈ Finset.range (⌊2 * x⌋₊ + 1), f m := by
    apply Finset.sum_subset hUnionSub
    intro m hmRange hmNot
    by_contra hmNZ
    exact hmNot (hCover m hmNZ)
  rw [← hSum, Finset.sum_union hDisjoint]

end ArtinPrimitiveRoots.Proofs.c_bins_sol
