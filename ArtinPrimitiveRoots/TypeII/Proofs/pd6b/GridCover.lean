import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.GridPredicates

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

private theorem enlarged_grid_interval_card (a b : ℝ) (hab : a ≤ b) :
    ((Finset.Icc (⌊a⌋ - 1) ⌈b⌉).card : ℝ) ≤ b - a + 4 := by
  have hfloor := Int.floor_le a
  have hceil := Int.le_ceil b
  have hfloor' := Int.lt_floor_add_one a
  have hceil' := Int.ceil_lt_add_one b
  have hlrR : ((⌊a⌋ - 1 : ℤ) : ℝ) ≤ ((⌈b⌉ + 1 : ℤ) : ℝ) := by push_cast; linarith
  have hlr : (⌊a⌋ - 1 : ℤ) ≤ ⌈b⌉ + 1 := by exact_mod_cast hlrR
  have hcardZ := Int.card_Icc_of_le (a := ⌊a⌋ - 1) (b := ⌈b⌉) hlr
  have hcardR : ((Finset.Icc (⌊a⌋ - 1) ⌈b⌉).card : ℝ) =
      ((⌈b⌉ + 1 - (⌊a⌋ - 1) : ℤ) : ℝ) := by exact_mod_cast hcardZ
  rw [hcardR]
  push_cast
  linarith

/-- The full closed-grid cover has at most 475/h³ cubes when h≤1. -/
theorem gridIndices_card_le (h : ℝ) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ((gridIndices h).card : ℝ) ≤ 475 / h ^ 3 := by
  have hInv : 1 ≤ 1 / h := (le_div_iff₀ hh).mpr (by simpa only [one_mul] using hh₁)
  have hI₁ := enlarged_grid_interval_card (1 / h) (16 / h) (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 16) hh.le)
  have hI₂ := enlarged_grid_interval_card (1 / h) (2 / h) (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hh.le)
  have hI₃ := enlarged_grid_interval_card 0 (1 / h) (by positivity : (0 : ℝ) ≤ 1 / h)
  have hb₁ : ((Finset.Icc (⌊1 / h⌋ - 1) ⌈16 / h⌉).card : ℝ) ≤ 19 / h := by
    have heq : 16 / h - 1 / h = 15 / h := by ring
    rw [heq] at hI₁
    have heq' : 19 / h = 15 / h + 4 * (1 / h) := by ring
    rw [heq']
    linarith
  have hb₂ : ((Finset.Icc (⌊1 / h⌋ - 1) ⌈2 / h⌉).card : ℝ) ≤ 5 / h := by
    have heq : 2 / h - 1 / h = 1 / h := by ring
    rw [heq] at hI₂
    have heq' : 5 / h = 1 / h + 4 * (1 / h) := by ring
    rw [heq']
    linarith
  have hb₃ : ((Finset.Icc (-1) ⌈1 / h⌉).card : ℝ) ≤ 5 / h := by
    norm_num only [Int.floor_zero, zero_sub, sub_zero] at hI₃
    have heq : 5 / h = 1 / h + 4 * (1 / h) := by ring
    rw [heq]
    linarith
  unfold gridIndices
  rw [Finset.card_product, Finset.card_product]
  push_cast
  calc
    _ ≤ (19 / h) * ((5 / h) * (5 / h)) := by
      apply mul_le_mul hb₁
      · exact mul_le_mul hb₂ hb₃ (Nat.cast_nonneg _) (by positivity)
      · positivity
      · positivity
    _ = _ := by field_simp; ring

/-- The normalized root region is covered by the frozen grid indices. -/
theorem normalizedRoot_mem_grid (h : ℝ) (hh : 0 < h) (y : ℝ × ℝ × ℝ)
    (hy : (1 ≤ y.1 ∧ y.1 ≤ 16) ∧ (1 ≤ y.2.1 ∧ y.2.1 ≤ 2) ∧ (0 ≤ y.2.2 ∧ y.2.2 ≤ 1)) :
    ∃ k ∈ gridIndices h, y ∈ gridCube h k := by
  let k : ℤ × ℤ × ℤ := (⌊y.1 / h⌋, ⌊y.2.1 / h⌋, ⌊y.2.2 / h⌋)
  have hbetween (a b v : ℝ) (hlo : a ≤ v) (hhi : v ≤ b) :
      (⌊a / h⌋ - 1 : ℤ) ≤ ⌊v / h⌋ ∧ ⌊v / h⌋ ≤ ⌈b / h⌉ := by
    have hleft : ⌊a / h⌋ ≤ ⌊v / h⌋ := Int.floor_mono (div_le_div_of_nonneg_right hlo hh.le)
    have hrightR : (⌊v / h⌋ : ℝ) ≤ (⌈b / h⌉ : ℝ) :=
      (Int.floor_le _).trans ((div_le_div_of_nonneg_right hhi hh.le).trans (Int.le_ceil _))
    have hright : ⌊v / h⌋ ≤ ⌈b / h⌉ := by exact_mod_cast hrightR
    exact ⟨by omega, hright⟩
  have hcell (v : ℝ) : (⌊v / h⌋ : ℝ) * h ≤ v ∧ v ≤ ((⌊v / h⌋ : ℝ) + 1) * h := by
    exact ⟨(le_div_iff₀ hh).mp (Int.floor_le _),
      (div_le_iff₀ hh).mp (Int.lt_floor_add_one _).le⟩
  refine ⟨k, ?_, ?_⟩
  · change k ∈ (Finset.Icc (⌊1 / h⌋ - 1) ⌈16 / h⌉) ×ˢ
      ((Finset.Icc (⌊1 / h⌋ - 1) ⌈2 / h⌉) ×ˢ (Finset.Icc (-1) ⌈1 / h⌉))
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hbetween 1 16 y.1 hy.1.1 hy.1.2),
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hbetween 1 2 y.2.1 hy.2.1.1 hy.2.1.2), ?_⟩⟩
    simpa only [Int.floor_zero, zero_div, zero_sub] using
      Finset.mem_Icc.mpr (hbetween 0 1 y.2.2 hy.2.2.1 hy.2.2.2)
  · exact ⟨(hcell y.1).1, (hcell y.1).2, (hcell y.2.1).1, (hcell y.2.1).2,
      (hcell y.2.2).1, (hcell y.2.2).2⟩

end
end ArtinPrimitiveRoots.TypeII.PD
