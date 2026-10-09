import ArtinPrimitiveRoots.Splitting.Defs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_MELLIN.Flatness

set_option autoImplicit false

open scoped Topology
open Filter MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting

/-- A smooth positive test has a uniformly bounded Mellin transform on each real-part strip. -/
theorem mellin_strip_bound (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0) (a b : ℝ) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖mellinTransform f s‖ ≤ C := by
  obtain ⟨r, hr⟩ := hf.2.1.isCompact.bddAbove
  let R : ℝ := max r 1
  have hRr : r ≤ R := le_max_left _ _
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  obtain ⟨N, hN⟩ := exists_nat_gt (1 - a)
  obtain ⟨B, hB, hflat⟩ := test_flat_bound f hf 0 N
  obtain ⟨D0, hD0⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) R)).bddAbove_image
      hf.1.continuous.abs.continuousOn
  let D : ℝ := max D0 0
  have hDnonneg : 0 ≤ D := le_max_right _ _
  have hD (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) R) : |f t| ≤ D :=
    (hD0 (Set.mem_image_of_mem (fun t => |f t|) ht)).trans (le_max_left _ _)
  let q : ℝ := max (b - 1) 0
  have hq : 0 ≤ q := le_max_right _ _
  have hRq : 0 ≤ R ^ q := Real.rpow_nonneg hRpos.le _
  have hDR : 0 ≤ D * R ^ q := mul_nonneg hDnonneg hRq
  let M : ℝ := B + D * R ^ q + 1
  have hM : 0 < M := by dsimp only [M]; linarith
  refine ⟨M * R, mul_pos hM hRpos, ?_⟩
  intro s ha hb
  let G : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * (f t : ℂ)
  have hnorm (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) R) : ‖G t‖ ≤ M := by
    have hnormG : ‖G t‖ = t ^ (s.re - 1) * |f t| := by
      dsimp only [G]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1 (s - 1),
        Complex.sub_re, Complex.one_re, Complex.norm_real, Real.norm_eq_abs]
    rw [hnormG]
    rcases le_or_gt t 1 with ht1 | ht1
    · have hflatT : |f t| ≤ B * t ^ N := by
        simpa only [iteratedDeriv_zero] using hflat t ⟨ht.1.le, ht1⟩
      have hexp : 0 ≤ s.re - 1 + (N : ℝ) := by linarith
      calc
        _ ≤ t ^ (s.re - 1) * (B * t ^ N) :=
          mul_le_mul_of_nonneg_left hflatT (Real.rpow_nonneg ht.1.le _)
        _ = B * t ^ (s.re - 1 + (N : ℝ)) := by
          rw [← Real.rpow_natCast t N, Real.rpow_add ht.1]
          ring
        _ ≤ B * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one ht.1.le ht1 hexp) hB
        _ = B := mul_one B
        _ ≤ M := by dsimp only [M]; linarith
    · have hexp : s.re - 1 ≤ q := by
        have h := le_max_left (b - 1) 0
        dsimp only [q]
        linarith
      have hweight : t ^ (s.re - 1) ≤ R ^ q :=
        (Real.rpow_le_rpow_of_exponent_le ht1.le hexp).trans
          (Real.rpow_le_rpow ht.1.le ht.2 hq)
      calc
        _ ≤ R ^ q * D := mul_le_mul hweight (hD t ⟨ht.1.le, ht.2⟩)
          (abs_nonneg _) hRq
        _ ≤ M := by rw [mul_comm]; dsimp only [M]; linarith
  have hEq : (∫ t : ℝ in Set.Ioi 0, G t) = ∫ t : ℝ in Set.Ioc 0 R, G t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Set.Ioc (0 : ℝ) R ⊆ Set.Ioi 0 from fun t ht => ht.1)
    intro t ht
    have htr : R < t := by
      apply lt_of_not_ge
      intro hle
      exact ht.2 ⟨Set.mem_Ioi.mp ht.1, hle⟩
    have hft : f t = 0 := by
      by_contra h
      have htr' : t ≤ r := hr (subset_tsupport f (show t ∈ Function.support f from h))
      exact (not_lt_of_ge (htr'.trans hRr)) htr
    simp only [G, hft, Complex.ofReal_zero, mul_zero]
  have hfin : volume (Set.Ioc (0 : ℝ) R) < ⊤ := by
    simp only [Real.volume_Ioc, ENNReal.ofReal_lt_top]
  have hvol : volume.real (Set.Ioc (0 : ℝ) R) = R := by
    rw [Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hRpos.le]
  change ‖∫ t : ℝ in Set.Ioi 0, G t‖ ≤ M * R
  rw [hEq]
  have h := norm_setIntegral_le_of_norm_le_const hfin hnorm
  simpa only [hvol] using h

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
