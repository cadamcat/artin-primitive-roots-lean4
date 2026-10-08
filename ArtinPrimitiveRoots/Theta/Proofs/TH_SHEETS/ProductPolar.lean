import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.RadialScaling

set_option autoImplicit false
open MeasureTheory Set
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_sheets

/-- Product Fubini with a free-coordinate-dependent squared-radius scale. -/
theorem polar_product_disintegration {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (B : α → ℝ) (hB : Measurable B)
    (hpos : ∀ᵐ p ∂μ, 0 < B p) (g : α × ℂ → ℂ)
    (hg : Integrable g (μ.prod
      (volume.withDensity fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹))) :
    IntegrableOn (fun u : ℝ =>
      (∫ p, ∫ θ in Ioc (0 : ℝ) 1, g (p, complexPolarPoint (u / B p, θ)) ∂volume ∂μ) / u)
      (Ioi 0) ∧
    (∫ q, g q ∂(μ.prod
      (volume.withDensity fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹))) =
      Real.pi * ∫ u in Ioi (0 : ℝ),
        (∫ p, ∫ θ in Ioc (0 : ℝ) 1, g (p, complexPolarPoint (u / B p, θ)) ∂volume ∂μ) / u := by
  let θμ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let νC : Measure ℂ := volume.withDensity fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹
  have : SigmaFinite polarRadialMeasure := by
    unfold polarRadialMeasure
    infer_instance
  have : SigmaFinite θμ := by dsimp [θμ]; infer_instance
  have hscale := (radial_product_scaling μ B hB hpos).prod (MeasurePreserving.id θμ)
  have hassoc := measurePreserving_prodAssoc μ polarRadialMeasure θμ
  have hpolar : MeasurePreserving
      (fun q : α × (ℝ × ℝ) => (q.1, complexPolarPoint q.2))
      (ENNReal.ofReal Real.pi • μ.prod (polarRadialMeasure.prod θμ)) (μ.prod νC) := by
    simpa only [Measure.prod_smul_right, Prod.map_def, id_eq] using
      (MeasurePreserving.id μ).prod complex_polar_measurePreserving
  have hmp : MeasurePreserving
      (fun q : (α × ℝ) × ℝ => (q.1.1, complexPolarPoint (q.1.2 / B q.1.1, q.2)))
      (ENNReal.ofReal Real.pi • (μ.prod polarRadialMeasure).prod θμ) (μ.prod νC) :=
    hpolar.comp ((hassoc.smul_measure (ENNReal.ofReal Real.pi)).comp
      (hscale.smul_measure (ENNReal.ofReal Real.pi)))
  let H : (α × ℝ) × ℝ → ℂ :=
    fun q => g (q.1.1, complexPolarPoint (q.1.2 / B q.1.1, q.2))
  have hiπ : Integrable H (ENNReal.ofReal Real.pi • (μ.prod polarRadialMeasure).prod θμ) :=
    hmp.integrable_comp_of_integrable hg
  have hi : Integrable H ((μ.prod polarRadialMeasure).prod θμ) :=
    (integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top).mp hiπ
  let K : α × ℝ → ℂ := fun q => ∫ θ, H (q, θ) ∂θμ
  have hiK : Integrable K (μ.prod polarRadialMeasure) := hi.integral_prod_left
  let L : ℝ → ℂ := fun u => ∫ p, K (p, u) ∂μ
  have hiL : Integrable L polarRadialMeasure := hiK.integral_prod_right
  have hFubini : (∫ q, H q ∂((μ.prod polarRadialMeasure).prod θμ)) =
      ∫ u, L u ∂polarRadialMeasure :=
    (integral_prod H hi).trans (integral_prod_symm K hiK)
  have hr : Measurable (fun u : ℝ => ENNReal.ofReal u⁻¹) := by fun_prop
  have hfinite : ∀ᵐ u : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ENNReal.ofReal u⁻¹ < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hweight : (fun u : ℝ => (ENNReal.ofReal u⁻¹).toReal • L u)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun u => L u / u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hu.le)]
    simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  have hiWeighted : IntegrableOn (fun u : ℝ => L u / u) (Ioi 0) :=
    ((integrable_withDensity_iff_integrable_smul' hr hfinite).mp hiL).congr hweight
  have hradial : (∫ u, L u ∂polarRadialMeasure) = ∫ u in Ioi (0 : ℝ), L u / u :=
    (integral_withDensity_eq_integral_toReal_smul hr hfinite L).trans (integral_congr_ae hweight)
  refine ⟨hiWeighted, ?_⟩
  calc
    _ = ∫ q, g q ∂Measure.map
        (fun q : (α × ℝ) × ℝ => (q.1.1, complexPolarPoint (q.1.2 / B q.1.1, q.2)))
        (ENNReal.ofReal Real.pi • (μ.prod polarRadialMeasure).prod θμ) := by rw [hmp.map_eq]
    _ = ∫ q, H q ∂(ENNReal.ofReal Real.pi • (μ.prod polarRadialMeasure).prod θμ) :=
      integral_map hmp.aemeasurable (by simpa only [hmp.map_eq] using hg.aestronglyMeasurable)
    _ = Real.pi • ∫ q, H q ∂((μ.prod polarRadialMeasure).prod θμ) := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal Real.pi_pos.le]
    _ = Real.pi • ∫ u, L u ∂polarRadialMeasure := by rw [hFubini]
    _ = Real.pi • ∫ u in Ioi (0 : ℝ), L u / u := by rw [hradial]
    _ = _ := rfl

end ArtinPrimitiveRoots.Proofs.thsol_sheets
