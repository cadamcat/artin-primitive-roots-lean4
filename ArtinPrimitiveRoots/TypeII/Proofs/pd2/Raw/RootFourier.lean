import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootArithmetic

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII
set_option maxHeartbeats 1000000

lemma pd2a_root_character_orthogonality (m : ℕ) [NeZero m] (t : ZMod m) :
    (∑ x : ZMod m, ZMod.stdAddChar (t * x)) = if t = 0 then (m : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar m ht)

lemma pd2a_root_character_norm (m : ℕ) [NeZero m] (t : ZMod m) :
    ‖ZMod.stdAddChar t‖ = 1 := by simp [ZMod.stdAddChar_apply]

noncomputable def pd2a_rootDFT (m : ℕ) [NeZero m] (f : ZMod m → ℂ) (h : ZMod m) : ℂ :=
  (m : ℂ)⁻¹ * ∑ z : ZMod m, f z * ZMod.stdAddChar (-h * z)

lemma pd2a_rootDFT_inversion (m : ℕ) [NeZero m] (f : ZMod m → ℂ) (z : ZMod m) :
    (∑ h : ZMod m, pd2a_rootDFT m f h * ZMod.stdAddChar (h * z)) = f z := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  simp only [pd2a_rootDFT, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hInner : ∀ y : ZMod m,
      (∑ h : ZMod m, ((m : ℂ)⁻¹ * (f y * ZMod.stdAddChar (-h * y))) * ZMod.stdAddChar (h * z)) =
      (m : ℂ)⁻¹ * f y * (if y = z then (m : ℂ) else 0) := by
    intro y
    calc
      _ = (m : ℂ)⁻¹ * f y * ∑ h : ZMod m, ZMod.stdAddChar ((z - y) * h) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h hh
        have harg : (z - y) * h = -h * y + h * z := by ring
        rw [harg, AddChar.map_add_eq_mul]
        ring
      _ = _ := by
        rw [pd2a_root_character_orthogonality]
        by_cases heq : y = z
        · simp [heq]
        · simp [heq, sub_ne_zero.mpr (Ne.symm heq)]
  simp_rw [hInner]
  rw [Finset.sum_eq_single z]
  · simp only [ite_true]
    calc
      (m : ℂ)⁻¹ * f z * m = f z * ((m : ℂ)⁻¹ * m) := by ring
      _ = f z := by rw [inv_mul_cancel₀ hm, mul_one]
  · intro y hy hyz
    simp [hyz]
  · simp

lemma pd2a_rootDFT_zero (m : ℕ) [NeZero m] (f : ZMod m → ℂ) :
    pd2a_rootDFT m f 0 = (m : ℂ)⁻¹ * ∑ z : ZMod m, f z := by simp [pd2a_rootDFT]

lemma pd2a_rootDFT_indicator_norm (m : ℕ) [NeZero m] (s : Finset (ZMod m)) (h : ZMod m) :
    ‖pd2a_rootDFT m (fun z => if z ∈ s then (1 : ℂ) else 0) h‖ ≤ 1 := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hnorm : ‖∑ z : ZMod m, (if z ∈ s then (1 : ℂ) else 0) * ZMod.stdAddChar (-h * z)‖ ≤ (s.card : ℝ) := by
    calc
      _ ≤ ∑ z : ZMod m, ‖(if z ∈ s then (1 : ℂ) else 0) * ZMod.stdAddChar (-h * z)‖ := norm_sum_le _ _
      _ = (s.card : ℝ) := by
        simp only [norm_mul, pd2a_root_character_norm, mul_one]
        simp only [apply_ite, norm_one, norm_zero]
        rw [← Finset.sum_filter]
        simp
  unfold pd2a_rootDFT
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (m : ℝ)⁻¹ * (s.card : ℝ) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ (m : ℝ)⁻¹ * m := mul_le_mul_of_nonneg_left (by
      have hc : s.card ≤ m := by simpa only [ZMod.card] using s.card_le_univ
      exact_mod_cast hc) (by positivity)
    _ = 1 := inv_mul_cancel₀ hm.ne'

noncomputable def pd2a_rootGraphTransform (m : ℕ) [NeZero m]
    (G : Finset (ZMod m × ZMod m)) (h k : ZMod m) : ℂ :=
  ∑ z ∈ G, ZMod.stdAddChar (h * z.1 + k * z.2)

lemma pd2a_root_graph_fourier_formula (m : ℕ) [NeZero m]
    (G : Finset (ZMod m × ZMod m)) (f g : ZMod m → ℂ) :
    (∑ z ∈ G, f z.1 * g z.2) =
      ∑ h : ZMod m, ∑ k : ZMod m,
        pd2a_rootDFT m f h * pd2a_rootDFT m g k * pd2a_rootGraphTransform m G h k := by
  have hf : ∀ z, f z = ∑ h : ZMod m, pd2a_rootDFT m f h * ZMod.stdAddChar (h * z) :=
    fun z => (pd2a_rootDFT_inversion m f z).symm
  have hg : ∀ z, g z = ∑ k : ZMod m, pd2a_rootDFT m g k * ZMod.stdAddChar (k * z) :=
    fun z => (pd2a_rootDFT_inversion m g z).symm
  simp_rw [hf, hg, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  unfold pd2a_rootGraphTransform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [AddChar.map_add_eq_mul]
  ring

lemma pd2a_rootGraphTransform_zero (m : ℕ) [NeZero m] (G : Finset (ZMod m × ZMod m)) :
    pd2a_rootGraphTransform m G 0 0 = G.card := by simp [pd2a_rootGraphTransform]

lemma pd2a_rootGraphTransform_norm (m : ℕ) [NeZero m] (G : Finset (ZMod m × ZMod m)) (h k : ZMod m) :
    ‖pd2a_rootGraphTransform m G h k‖ ≤ (G.card : ℝ) := by
  unfold pd2a_rootGraphTransform
  exact (norm_sum_le _ _).trans_eq (by simp [pd2a_root_character_norm])

lemma pd2a_root_graph_fourier_error (m : ℕ) [NeZero m]
    (G : Finset (ZMod m × ZMod m)) (f g : ZMod m → ℂ) :
    ‖(∑ z ∈ G, f z.1 * g z.2) - pd2a_rootDFT m f 0 * pd2a_rootDFT m g 0 * (G.card : ℂ)‖ ≤
      ∑ h : ZMod m, ∑ k : ZMod m,
        if h = 0 ∧ k = 0 then (0 : ℝ) else
          ‖pd2a_rootDFT m f h‖ * ‖pd2a_rootDFT m g k‖ * ‖pd2a_rootGraphTransform m G h k‖ := by
  let F := fun hk : ZMod m × ZMod m => pd2a_rootDFT m f hk.1 * pd2a_rootDFT m g hk.2 * pd2a_rootGraphTransform m G hk.1 hk.2
  have heq : (∑ hk : ZMod m × ZMod m, F hk) - F (0, 0) =
      ∑ hk : ZMod m × ZMod m, if hk = (0, 0) then 0 else F hk := by
    calc
      _ = ∑ hk : ZMod m × ZMod m, (F hk - if hk = (0, 0) then F (0, 0) else 0) := by
        rw [Finset.sum_sub_distrib]
        simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro hk hhk
        by_cases hzero : hk = (0, 0) <;> simp [hzero]
  rw [pd2a_root_graph_fourier_formula]
  have hzero : pd2a_rootDFT m f 0 * pd2a_rootDFT m g 0 * (G.card : ℂ) = F (0, 0) := by
    simp [F, pd2a_rootGraphTransform_zero]
  rw [hzero]
  change ‖(∑ h : ZMod m, ∑ k : ZMod m, F (h, k)) - F (0, 0)‖ ≤ _
  rw [← Fintype.sum_prod_type, heq]
  calc
    _ ≤ ∑ hk : ZMod m × ZMod m, ‖if hk = (0, 0) then 0 else F hk‖ := norm_sum_le _ _
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Prod.mk.injEq, apply_ite, norm_zero, F, norm_mul]
      by_cases hz : h = 0 ∧ k = 0 <;> simp [hz]

end ArtinPrimitiveRoots.TypeII.PD
