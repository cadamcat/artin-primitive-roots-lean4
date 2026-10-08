import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».ComplexRadial
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.ComplexPolar
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false

open MeasureTheory Set
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_sheets

open ArtinPrimitiveRoots.A1

/-- Every complex radial derivative has weighted multiplicative L1 and a uniform weighted bound. -/
theorem complex_factor_weighted (δ σ : ℝ) (hσ : -δ < σ)
    (f : ℂ → ℂ) (hf : SheetHypC δ f) (j : ℕ) :
    Integrable (fun z => ‖normDeriv j f z‖ * Complex.normSq z ^ σ)
      (volume.withDensity fun z => ENNReal.ofReal (Complex.normSq z)⁻¹) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, z ≠ 0 →
      ‖normDeriv j f z‖ * Complex.normSq z ^ σ ≤ M := by
  let A : ℝ := max 0 σ + 1
  have hA : 0 < A := by dsimp [A]; have := le_max_left (0 : ℝ) σ; linarith
  have hσA : σ < A := by dsimp [A]; have := le_max_right (0 : ℝ) σ; linarith
  have hε : 0 < δ + σ := by linarith only [hσ]
  have hβ : σ - A < 0 := by linarith only [hσA]
  obtain ⟨C, hC⟩ := hf.2 j A hA
  let M : ℝ := max 0 C
  have hM : 0 ≤ M := le_max_left _ _
  let E : ℝ → ℝ := fun t => min (t ^ (δ + σ)) (t ^ (σ - A))
  let g : ℂ → ℝ := fun z => ‖normDeriv j f z‖ * Complex.normSq z ^ σ
  have ht (z : ℂ) (hz : z ≠ 0) : 0 < Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hEnonneg (t : ℝ) (ht : 0 < t) : 0 ≤ E t :=
    le_min (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _)
  have hEone (t : ℝ) (ht : 0 < t) : E t ≤ 1 := by
    by_cases htle : t ≤ 1
    · exact (min_le_left _ _).trans (Real.rpow_le_one ht.le htle hε.le)
    · exact (min_le_right _ _).trans
        (Real.rpow_le_one_of_one_le_of_nonpos (lt_of_not_ge htle).le hβ.le)
  have hEnv (z : ℂ) (hz : z ≠ 0) : g z ≤ M * E (Complex.normSq z) := by
    have hbase : ‖normDeriv j f z‖ ≤ M * min (Complex.normSq z ^ δ)
        (Complex.normSq z ^ (-A)) :=
      (hC z hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (le_min (Real.rpow_nonneg (Complex.normSq_nonneg z) _)
          (Real.rpow_nonneg (Complex.normSq_nonneg z) _)))
    have heq : min (Complex.normSq z ^ δ) (Complex.normSq z ^ (-A)) *
        Complex.normSq z ^ σ = E (Complex.normSq z) := by
      dsimp only [E]
      rw [min_mul_of_nonneg _ _ (Real.rpow_nonneg (Complex.normSq_nonneg z) σ),
        ← Real.rpow_add (ht z hz), ← Real.rpow_add (ht z hz)]
      rw [show -A + σ = σ - A by ring]
    calc
      g z ≤ (M * min (Complex.normSq z ^ δ) (Complex.normSq z ^ (-A))) *
          Complex.normSq z ^ σ :=
        mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (Complex.normSq_nonneg z) _)
      _ = M * (min (Complex.normSq z ^ δ) (Complex.normSq z ^ (-A)) *
          Complex.normSq z ^ σ) := mul_assoc _ _ _
      _ = _ := by rw [heq]
  have hgcont : ContinuousOn g {z | z ≠ 0} :=
    (complex_normDeriv_contDiff f hf.1 j).continuousOn.norm.mul
      (Complex.continuous_normSq.continuousOn.rpow_const fun z hz => Or.inl (ht z hz).ne')
  have hgmeas : Measurable g := measurable_of_continuousOn_compl_singleton (0 : ℂ) hgcont
  have hgnonneg (z : ℂ) : 0 ≤ g z :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Complex.normSq_nonneg z) _)
  have hEmeas : Measurable E :=
    (measurable_id.pow_const (δ + σ)).min (measurable_id.pow_const (σ - A))
  have hρ : Measurable (fun t : ℝ => ENNReal.ofReal t⁻¹) := measurable_inv.ennreal_ofReal
  have htoReal (t : ℝ) (ht : 0 < t) : (ENNReal.ofReal t⁻¹).toReal = t⁻¹ :=
    ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le)
  let L : ℝ → ℝ := fun t => E t * (ENNReal.ofReal t⁻¹).toReal
  have hLmeas : Measurable L := hEmeas.mul hρ.ennreal_toReal
  have hLnonneg (t : ℝ) (ht : 0 < t) : 0 ≤ L t := by
    dsimp only [L]
    rw [htoReal t ht]
    exact mul_nonneg (hEnonneg t ht) (inv_nonneg.mpr ht.le)
  have hiNear : IntegrableOn L (Ioc (0 : ℝ) 1) := by
    have hp : IntegrableOn (fun t : ℝ => t ^ (δ + σ - 1)) (Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith only [hε]))
    apply hp.mono' hLmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hLnonneg t ht.1)]
    change E t * (ENNReal.ofReal t⁻¹).toReal ≤ t ^ (δ + σ - 1)
    rw [htoReal t ht.1]
    calc
      _ ≤ t ^ (δ + σ) * t⁻¹ :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (inv_nonneg.mpr ht.1.le)
      _ = _ := by rw [← div_eq_mul_inv, ← Real.rpow_sub_one ht.1.ne']
  have hiFar : IntegrableOn L (Ioi (1 : ℝ)) := by
    have hp : IntegrableOn (fun t : ℝ => t ^ (σ - A - 1)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith only [hβ]) zero_lt_one
    apply hp.mono' hLmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hLnonneg t ht0)]
    change E t * (ENNReal.ofReal t⁻¹).toReal ≤ t ^ (σ - A - 1)
    rw [htoReal t ht0]
    calc
      _ ≤ t ^ (σ - A) * t⁻¹ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (inv_nonneg.mpr ht0.le)
      _ = _ := by rw [← div_eq_mul_inv, ← Real.rpow_sub_one ht0.ne']
  have hiL : IntegrableOn L (Ioi (0 : ℝ)) := by
    simpa only [Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using hiNear.union hiFar
  have hiE : Integrable E polarRadialMeasure := by
    change Integrable E ((volume.restrict (Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal t⁻¹)
    apply (integrable_withDensity_iff hρ
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
    exact hiL
  have : SigmaFinite polarRadialMeasure := by unfold polarRadialMeasure; infer_instance
  have hrpos : ∀ᵐ t ∂polarRadialMeasure, 0 < t :=
    (withDensity_absolutelyContinuous (volume.restrict (Ioi (0 : ℝ)))
      (fun t => ENNReal.ofReal t⁻¹)).ae_le (ae_restrict_mem measurableSet_Ioi)
  have hppos : ∀ᵐ p ∂polarRadialMeasure.prod (volume.restrict (Ioc (0 : ℝ) 1)), 0 < p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := polarRadialMeasure)
      (ν := volume.restrict (Ioc (0 : ℝ) 1))).ae hrpos
  have hiProd : Integrable (g ∘ complexPolarPoint)
      (polarRadialMeasure.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply ((hiE.const_mul M).comp_fst (volume.restrict (Ioc (0 : ℝ) 1))).mono'
      (hgmeas.comp complex_polar_measurePreserving.measurable).aestronglyMeasurable
    filter_upwards [hppos] with p hp
    rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hgnonneg _)]
    have hn : Complex.normSq (complexPolarPoint p) = p.1 := by
      unfold complexPolarPoint
      rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp]
      have hre : (2 * Real.pi * Complex.I * (p.2 : ℂ)).re = 0 := by simp
      rw [hre, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hp.le]
    have hz : complexPolarPoint p ≠ 0 := by
      unfold complexPolarPoint
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp).ne')
        (Complex.exp_ne_zero _)
    simpa only [hn] using hEnv (complexPolarPoint p) hz
  have hiG : Integrable g
      (volume.withDensity fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹) :=
    (complex_polar_measurePreserving.integrable_comp hgmeas.aestronglyMeasurable).mp
      (hiProd.smul_measure ENNReal.ofReal_ne_top)
  refine ⟨hiG, M, hM, ?_⟩
  intro z hz
  exact (hEnv z hz).trans ((mul_le_mul_of_nonneg_left (hEone _ (ht z hz)) hM).trans_eq (mul_one _))

end ArtinPrimitiveRoots.Proofs.thsol_sheets
