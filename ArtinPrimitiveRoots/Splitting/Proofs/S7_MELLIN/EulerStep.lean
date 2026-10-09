import ArtinPrimitiveRoots.Splitting.Defs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_MELLIN.Flatness
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

open scoped Topology
open Filter MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting

/-- The Euler derivative preserves positive tests and multiplies the Mellin transform by -s. -/
theorem mellin_euler_step (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0) :
    (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => t * deriv f t) ∧
      HasCompactSupport (fun t : ℝ => t * deriv f t) ∧
      Function.support (fun t : ℝ => t * deriv f t) ⊆ Set.Ioi 0) ∧
    (∀ s : ℂ, mellinTransform (fun t : ℝ => t * deriv f t) s =
      -s * mellinTransform f s) := by
  let Ef : ℝ → ℝ := fun t => t * deriv f t
  have hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ef ∧ HasCompactSupport Ef ∧
      Function.support Ef ⊆ Set.Ioi 0 := by
    refine ⟨?_, ?_, ?_⟩
    · exact contDiff_id.mul (contDiff_infty_iff_deriv.mp hf.1).2
    · change HasCompactSupport ((fun t : ℝ => t) * deriv f)
      exact hf.2.1.deriv.mul_left
    · intro t ht
      change t * deriv f t ≠ 0 at ht
      have ht0 : t ≠ 0 := left_ne_zero_of_mul ht
      by_contra hpos
      change ¬ 0 < t at hpos
      have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt hpos) ht0
      have heq : f =ᶠ[𝓝 t] fun _ : ℝ => 0 := by
        filter_upwards [isOpen_Iio.eventually_mem
          (show t ∈ Set.Iio (0 : ℝ) from htneg)] with y hy
        by_contra hfy
        have hypos : 0 < y := Set.mem_Ioi.mp (hf.2.2 hfy)
        exact (not_lt_of_ge (Set.mem_Iio.mp hy).le) hypos
      have hd : deriv f t = 0 := by
        rw [heq.deriv_eq]
        simp
      exact ht (by simp [hd])
  refine ⟨hE, ?_⟩
  have hconv (g : ℝ → ℝ)
      (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g ∧
        Function.support g ⊆ Set.Ioi 0) (z : ℂ) :
      MellinConvergent (fun t : ℝ => (g t : ℂ)) z := by
    let fc : ℝ → ℂ := fun t => (g t : ℂ)
    have hcont : Continuous fc := Complex.continuous_ofReal.comp hg.1.continuous
    have hloc : LocallyIntegrableOn fc (Set.Ioi 0) :=
      hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi
    obtain ⟨R, hR⟩ := hg.2.1.isCompact.bddAbove
    have hz : ∀ᶠ t : ℝ in atTop, g t = 0 := by
      refine eventually_atTop.mpr ⟨R + 1, ?_⟩
      intro t ht
      by_contra hft
      have htR : t ≤ R := hR (subset_tsupport g (show t ∈ Function.support g from hft))
      linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (-z.re)
    obtain ⟨B, hB, hbound⟩ := test_flat_bound g hg 0 N
    have htop : fc =O[atTop] (fun t : ℝ => t ^ (-(z.re + 1))) := by
      refine Asymptotics.isBigO_iff.mpr ⟨0, ?_⟩
      filter_upwards [hz] with t ht
      simp [fc, ht]
    have hIoc : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨1, by norm_num, Set.Subset.rfl⟩
    have hbot : fc =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-(-(N : ℝ)))) := by
      refine Asymptotics.isBigO_iff.mpr ⟨B, ?_⟩
      filter_upwards [hIoc] with t ht
      have h := hbound t ⟨ht.1.le, ht.2⟩
      simpa only [fc, iteratedDeriv_zero, neg_neg, Real.rpow_natCast,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1.le N)] using h
    exact mellinConvergent_of_isBigO_rpow hloc htop (by linarith) hbot (by linarith)

  intro s
  have hpow (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ s := by
    calc
      _ = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (t : ℂ) ^ ((s - 1) + 1) :=
        (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (Set.mem_Ioi.mp ht).ne')).symm
      _ = _ := by rw [sub_add_cancel]
  have hu (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ s) (s * (t : ℂ) ^ (s - 1)) t :=
    (Complex.hasStrictDerivAt_cpow_const (c := s)
      (Complex.ofReal_mem_slitPlane.mpr (Set.mem_Ioi.mp ht))).hasDerivAt.comp_ofReal
  have hv (t : ℝ) (_ht : t ∈ Set.Ioi (0 : ℝ)) :
      HasDerivAt (fun t : ℝ => (f t : ℂ)) ((deriv f t : ℝ) : ℂ) t :=
    ((hf.1.differentiable (by simp)) t).hasDerivAt.ofReal_comp
  have hcF : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * (f t : ℂ)) (Set.Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hconv f hf s
  have hu'v : IntegrableOn (fun t : ℝ =>
      (s * (t : ℂ) ^ (s - 1)) * (f t : ℂ)) (Set.Ioi 0) := by
    simpa only [IntegrableOn, mul_assoc] using hcF.const_mul s
  have heq : Set.EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * (Ef t : ℂ))
      (fun t : ℝ => (t : ℂ) ^ s * ((deriv f t : ℝ) : ℂ)) (Set.Ioi 0) := by
    intro t ht
    change (t : ℂ) ^ (s - 1) * ((t * deriv f t : ℝ) : ℂ) = _
    rw [Complex.ofReal_mul, ← mul_assoc, hpow t ht]
  have hcE : IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (s - 1) * (Ef t : ℂ)) (Set.Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hconv Ef hE s
  have huv' : IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ s * ((deriv f t : ℝ) : ℂ)) (Set.Ioi 0) :=
    (integrableOn_congr_fun heq measurableSet_Ioi).mp hcE
  obtain ⟨R, hR⟩ := hf.2.1.isCompact.bddAbove
  have hz : ∀ᶠ t : ℝ in atTop, f t = 0 := by
    refine eventually_atTop.mpr ⟨R + 1, ?_⟩
    intro t ht
    by_contra hft
    have htR : t ≤ R := hR (subset_tsupport f (show t ∈ Function.support f from hft))
    linarith
  have htop : Tendsto (fun t : ℝ => (t : ℂ) ^ s * (f t : ℂ)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hz] with t ht
    simp [ht]
  obtain ⟨N, hN⟩ := exists_nat_gt (-s.re)
  obtain ⟨B, hB, hflat⟩ := test_flat_bound f hf 0 N
  let p : ℝ := s.re + (N : ℝ)
  have hp : 0 < p := by dsimp [p]; linarith
  have hIoc : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨1, by norm_num, Set.Subset.rfl⟩
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ‖(t : ℂ) ^ s * (f t : ℂ)‖ ≤ B * t ^ p := by
    filter_upwards [hIoc] with t ht
    have hfbound : |f t| ≤ B * t ^ N := by
      simpa only [iteratedDeriv_zero] using hflat t ⟨ht.1.le, ht.2⟩
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1 s,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ t ^ s.re * (B * t ^ N) :=
        mul_le_mul_of_nonneg_left hfbound (Real.rpow_nonneg ht.1.le _)
      _ = B * t ^ p := by
        dsimp only [p]
        rw [← Real.rpow_natCast t N, Real.rpow_add ht.1]
        ring
  have hlim : Tendsto (fun t : ℝ => B * t ^ p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t ^ p) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ p)) :=
      ((Real.continuous_rpow_const hp.le).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [Real.zero_rpow hp.ne', mul_zero] using h.const_mul B
  have hzero : Tendsto (fun t : ℝ => (t : ℂ) ^ s * (f t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) hbound hlim)
  have hI := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℂ)) (b' := (0 : ℂ)) hu hv huv' hu'v hzero htop
  have hleft : mellinTransform Ef s =
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ s * ((deriv f t : ℝ) : ℂ) := by
    simp only [mellinTransform, mellin, smul_eq_mul]
    exact setIntegral_congr_fun measurableSet_Ioi heq
  have hright : (∫ t : ℝ in Set.Ioi 0,
      (s * (t : ℂ) ^ (s - 1)) * (f t : ℂ)) = s * mellinTransform f s := by
    simp only [mul_assoc, integral_const_mul, mellinTransform, mellin, smul_eq_mul]
  rw [← hleft, hright] at hI
  simpa only [sub_self, zero_sub, neg_mul] using hI

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
