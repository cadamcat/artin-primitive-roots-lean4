import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootIntervals

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_rootIntervalDensity (m a N : ℕ) (z : ZMod m) : ℂ :=
  ∑ n ∈ Finset.range N, if ((a + n : ℕ) : ZMod m) = z then 1 else 0

lemma pd2a_rootIntervalDensity_DFT (m a N : ℕ) [NeZero m] (h : ZMod m) :
    pd2a_rootDFT m (pd2a_rootIntervalDensity m a N) h =
      (m : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        ZMod.stdAddChar (-h * ((a + n : ℕ) : ZMod m)) := by
  unfold pd2a_rootDFT pd2a_rootIntervalDensity
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_eq_single ((a + n : ℕ) : ZMod m)]
  · simp
  · intro z hz hne
    rw [if_neg (Ne.symm hne), zero_mul]
  · simp

lemma pd2a_rootIntervalDensity_zero (m a N : ℕ) [NeZero m] :
    pd2a_rootDFT m (pd2a_rootIntervalDensity m a N) 0 = (N : ℂ) / (m : ℂ) := by
  rw [pd2a_rootIntervalDensity_DFT]
  simp only [neg_zero, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, div_eq_mul_inv]
  ring

lemma pd2a_rootIntervalDensity_coefficient_bound (m a N : ℕ) [NeZero m]
    (h : ZMod m) (hh : h ≠ 0) :
    ‖pd2a_rootDFT m (pd2a_rootIntervalDensity m a N) h‖ ≤
      2 / (min h.val (m - h.val) : ℕ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hneg : -h ≠ 0 := neg_ne_zero.mpr hh
  have hchar := pd2a_root_interval_character_bound m a N (-h) hneg
  letI : NeZero h := ⟨hh⟩
  have hVal : (-h).val = m - h.val := ZMod.val_neg_of_ne_zero h
  have hMin : min (-h).val (m - (-h).val) = min h.val (m - h.val) := by
    rw [hVal, Nat.sub_sub_self (ZMod.val_lt h).le, Nat.min_comm]
  rw [pd2a_rootIntervalDensity_DFT, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (m : ℝ)⁻¹ * (2 * (m : ℝ) / (min (-h).val (m - (-h).val) : ℕ)) :=
      mul_le_mul_of_nonneg_left hchar (by positivity)
    _ = _ := by rw [hMin]; field_simp

lemma pd2a_rootIntervalDensity_trivial_bound (m a N : ℕ) [NeZero m] (h : ZMod m) :
    ‖pd2a_rootDFT m (pd2a_rootIntervalDensity m a N) h‖ ≤ (N : ℝ) / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [pd2a_rootIntervalDensity_DFT, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖ZMod.stdAddChar (-h * ((a + n : ℕ) : ZMod m))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = _ := by simp [pd2a_root_character_norm, div_eq_mul_inv, mul_comm]

lemma pd2a_rootIntervalDensity_zero_norm (m a N : ℕ) [NeZero m] :
    ‖pd2a_rootDFT m (pd2a_rootIntervalDensity m a N) 0‖ = (N : ℝ) / (m : ℝ) := by
  rw [pd2a_rootIntervalDensity_zero, norm_div, Complex.norm_natCast, Complex.norm_natCast]

end ArtinPrimitiveRoots.TypeII.PD
