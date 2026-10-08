import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ArcReduction

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

lemma pd7d_arc_radius_bounds (M Y : ℝ) (hM : 1 ≤ M) (hY : 4 * M ^ 3 < Y) :
    0 < Y ∧ 0 ≤ 2 * M / Y ∧ 2 * M / Y < 1 / M ∧ 2 * M / Y < 1 / 2 := by
  have hMp : 0 < M := by linarith
  have hYp : 0 < Y := lt_trans (by positivity) hY
  have hpow : M ^ 2 ≤ M ^ 3 := by
    rw [pow_succ]
    nlinarith [sq_nonneg M]
  have hcube : M ≤ M ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hM (by norm_num : (1 : ℕ) ≤ 3)
  refine ⟨hYp, by positivity, ?_, ?_⟩
  · apply (div_lt_div_iff₀ hYp hMp).2
    nlinarith
  · apply (div_lt_iff₀ hYp).2
    linarith

lemma pd7d_nonzero_reduced_center_bounds (M Y : ℝ) (hM : 1 ≤ M) (hY : 4 * M ^ 3 < Y)
    (p : ℕ × ℕ) (hp : p ∈ pd7dReducedPairs M) (hne : p ≠ (0, 1)) :
    2 * M / Y < (p.1 : ℝ) / p.2 ∧ (p.1 : ℝ) / p.2 + 2 * M / Y < 1 := by
  obtain ⟨_, hkfloor, hk, hh, hcop⟩ := (pd7dReducedPairs_mem M p).1 hp
  have hkpos : 0 < (p.2 : ℝ) := by exact_mod_cast hk
  have hkM : (p.2 : ℝ) ≤ M :=
    (by exact_mod_cast hkfloor : (p.2 : ℝ) ≤ (⌊M⌋₊ : ℝ)) |>.trans (Nat.floor_le (by linarith))
  have hhpos : 1 ≤ p.1 := by
    by_contra hz
    have hzero : p.1 = 0 := by omega
    have hkone := hcop.gcd_eq_one
    rw [hzero, Nat.gcd_zero_left] at hkone
    exact hne (Prod.ext hzero hkone)
  have hcenter : 1 / (p.2 : ℝ) ≤ (p.1 : ℝ) / p.2 :=
    div_le_div_of_nonneg_right (by exact_mod_cast hhpos) hkpos.le
  have hupper : (p.1 : ℝ) / p.2 + 1 / p.2 ≤ 1 := by
    rw [← add_div]
    apply (div_le_one hkpos).2
    exact_mod_cast Nat.succ_le_iff.mpr hh
  have hR := (pd7d_arc_radius_bounds M Y hM hY).2.2.1
  have hInv : 1 / M ≤ 1 / (p.2 : ℝ) := one_div_le_one_div_of_le hkpos hkM
  constructor <;> linarith

lemma pd7d_nonzero_pair_arc_interval (M Y theta : ℝ) (hM : 1 ≤ M) (hY : 4 * M ^ 3 < Y)
    (p : ℕ × ℕ) (hp : p ∈ pd7dReducedPairs M) (hne : p ≠ (0, 1))
    (htheta : theta ∈ Set.Icc (0 : ℝ) 1) :
    pd7dPairArc M Y p theta ↔ theta ∈ Set.Icc
      ((p.1 : ℝ) / p.2 - 2 * M / Y) ((p.1 : ℝ) / p.2 + 2 * M / Y) := by
  obtain ⟨hcenter, hupper⟩ := pd7d_nonzero_reduced_center_bounds M Y hM hY p hp hne
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hlo, hhi⟩ := abs_le.mp hz
    have hzlo : (-1 : ℝ) < (z : ℝ) := by linarith [htheta.1]
    have hzhi : (z : ℝ) < 1 := by linarith [htheta.2]
    have hzloI : (-1 : ℤ) < z := by exact_mod_cast hzlo
    have hzhiI : z < (1 : ℤ) := by exact_mod_cast hzhi
    have hz0 : z = 0 := by omega
    rw [hz0, Int.cast_zero] at hlo hhi
    constructor <;> linarith
  · intro ht
    refine ⟨0, ?_⟩
    rw [Int.cast_zero, sub_zero]
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2]

lemma pd7d_zero_pair_arc_interval (M Y theta : ℝ) (hM : 1 ≤ M) (hY : 4 * M ^ 3 < Y)
    (htheta : theta ∈ Set.Icc (0 : ℝ) 1) :
    pd7dPairArc M Y (0, 1) theta ↔
      theta ∈ Set.Icc (0 : ℝ) (2 * M / Y) ∨ theta ∈ Set.Icc (1 - 2 * M / Y) 1 := by
  have hR := (pd7d_arc_radius_bounds M Y hM hY).2.2.2
  constructor
  · rintro ⟨z, hz⟩
    simp only [Nat.cast_zero, Nat.cast_one, zero_div, sub_zero] at hz
    obtain ⟨hlo, hhi⟩ := abs_le.mp hz
    have hzlo : (-1 : ℝ) < (z : ℝ) := by linarith [htheta.1]
    have hzhi : (z : ℝ) < 2 := by linarith [htheta.2]
    have hzloI : (-1 : ℤ) < z := by exact_mod_cast hzlo
    have hzhiI : z < (2 : ℤ) := by exact_mod_cast hzhi
    have hz01 : z = 0 ∨ z = 1 := by omega
    rcases hz01 with rfl | rfl
    · left
      constructor <;> simp only [Int.cast_zero] at hlo hhi <;> linarith [htheta.1]
    · right
      constructor <;> simp only [Int.cast_one] at hlo hhi <;> linarith [htheta.2]
  · rintro (ht | ht)
    · refine ⟨0, ?_⟩
      simp only [Nat.cast_zero, Nat.cast_one, zero_div, sub_zero, Int.cast_zero]
      exact abs_le.mpr ⟨by linarith [ht.1, ht.2], ht.2⟩
    · refine ⟨1, ?_⟩
      simp only [Nat.cast_zero, Nat.cast_one, zero_div, sub_zero, Int.cast_one]
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2]

end ArtinPrimitiveRoots.TypeII.PD
