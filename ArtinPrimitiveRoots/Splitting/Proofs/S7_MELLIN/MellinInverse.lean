import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_MELLIN.Flatness
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».LineIntegrability

set_option autoImplicit false

open scoped Topology
open Filter MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting

/-- Mellin inversion in the project's normalized vertical-integral notation. -/
theorem vertical_mellin_inverse (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0)
    (hentire : Differentiable ℂ (mellinTransform f))
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖mellinTransform f s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (y : ℝ) (hy : 0 < y) :
    verticalLineIntegral (fun s : ℂ =>
      Complex.cpow (y : ℂ) (-s) * mellinTransform f s) 2 = (f y : ℂ) := by
  let fc : ℝ → ℂ := fun t => (f t : ℂ)
  have hcont : Continuous fc := Complex.continuous_ofReal.comp hf.1.continuous
  have hloc : LocallyIntegrableOn fc (Set.Ioi 0) :=
    hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  obtain ⟨R, hR⟩ := hf.2.1.isCompact.bddAbove
  have hz : ∀ᶠ t : ℝ in atTop, f t = 0 := by
    refine eventually_atTop.mpr ⟨R + 1, ?_⟩
    intro t ht
    by_contra hft
    have htR : t ≤ R := hR (subset_tsupport f (show t ∈ Function.support f from hft))
    linarith
  obtain ⟨B, hB, hflat⟩ := test_flat_bound f hf 0 0
  have htop : fc =O[atTop] (fun t : ℝ => t ^ (-(3 : ℝ))) := by
    refine Asymptotics.isBigO_iff.mpr ⟨0, ?_⟩
    filter_upwards [hz] with t ht
    simp [fc, ht]
  have hIoc : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨1, by norm_num, Set.Subset.rfl⟩
  have hbot : fc =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    refine Asymptotics.isBigO_iff.mpr ⟨B, ?_⟩
    filter_upwards [hIoc] with t ht
    simpa only [fc, iteratedDeriv_zero, pow_zero, mul_one, neg_zero, Real.rpow_zero,
      Complex.norm_real, Real.norm_eq_abs, norm_one, abs_one] using hflat t ⟨ht.1.le, ht.2⟩
  have hconv : MellinConvergent fc (2 : ℂ) :=
    mellinConvergent_of_isBigO_rpow hloc htop (by norm_num) hbot (by norm_num)
  have hvert : Complex.VerticalIntegrable (mellin fc) (2 : ℝ) := by
    change Integrable (fun t : ℝ => mellinTransform f ((2 : ℂ) + t * Complex.I))
    obtain ⟨C, hC, hbound⟩ := hdecay 6 2 2 (by norm_num)
    have hcurve : Continuous (fun t : ℝ => (2 : ℂ) + t * Complex.I) := by fun_prop
    have hPhi : Continuous (fun t : ℝ => mellinTransform f ((2 : ℂ) + t * Complex.I)) :=
      hentire.continuous.comp hcurve
    have hgrowth (t : ℝ) : ‖(1 : ℂ)‖ ≤
        1 * Real.rpow (1 + |t|) (4 : ℝ) := by
      simp only [norm_one, one_mul, Real.rpow_eq_pow]
      exact Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
    have hdec (t : ℝ) : ‖mellinTransform f ((2 : ℂ) + t * Complex.I)‖ ≤
        C * Real.rpow (1 + |t|) (-6 : ℝ) := by
      simpa using hbound ((2 : ℂ) + t * Complex.I) (by simp) (by simp)
    have h := integrable_product_of_growth_decay
      (fun _ : ℝ => (1 : ℂ))
      (fun t : ℝ => mellinTransform f ((2 : ℂ) + t * Complex.I))
      aestronglyMeasurable_const hPhi.aestronglyMeasurable
      1 C (by norm_num) hC.le hgrowth hdec
    simpa only [one_mul] using h
  have hInv := ArtinPrimitiveRoots.Ext.SplittingInputs.ext_mellin_inversion
    (E := ℂ) 2 fc hy hconv hvert hcont.continuousAt
  simpa only [verticalLineIntegral, mellinInv, mellinTransform, fc,
    Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_inv, Complex.cpow_eq_pow, one_div, smul_eq_mul] using hInv

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
