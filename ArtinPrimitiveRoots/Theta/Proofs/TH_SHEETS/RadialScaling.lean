import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.ComplexPolar

set_option autoImplicit false
open MeasureTheory Set
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_sheets

private theorem radial_constant_scaling (b : ℝ) (hb : 0 < b) :
    MeasurePreserving (fun u : ℝ => u / b) polarRadialMeasure polarRadialMeasure := by
  have hm : Measurable (fun u : ℝ => u / b) := by fun_prop
  have hr : Measurable (fun t : ℝ => ENNReal.ofReal t⁻¹) := by fun_prop
  have hs : (fun u : ℝ => u / b) ⁻¹' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext u
    simp only [mem_preimage, mem_Ioi, div_pos_iff_of_pos_right hb]
  have hvol : Measure.map (fun u : ℝ => u / b) volume = ENNReal.ofReal b • volume := by
    simpa only [div_eq_mul_inv, inv_inv, abs_of_pos hb] using
      (Real.map_volume_mul_right (a := b⁻¹) (inv_ne_zero hb.ne'))
  have hmap : Measure.map (fun u : ℝ => u / b) (volume.restrict (Ioi (0 : ℝ))) =
      ENNReal.ofReal b • volume.restrict (Ioi (0 : ℝ)) := by
    calc
      _ = (Measure.map (fun u : ℝ => u / b) volume).restrict (Ioi (0 : ℝ)) := by
        rw [Measure.restrict_map hm measurableSet_Ioi, hs]
      _ = _ := by rw [hvol, Measure.restrict_smul]
  refine ⟨hm, Measure.ext_of_lintegral _ ?_⟩
  intro f hf
  rw [lintegral_map hf hm]
  unfold polarRadialMeasure
  have hfm : Measurable (fun u : ℝ => f (u / b)) := hf.comp hm
  rw [lintegral_withDensity_eq_lintegral_mul _ hr hfm,
    lintegral_withDensity_eq_lintegral_mul _ hr hf]
  have hweight (u : ℝ) : ENNReal.ofReal u⁻¹ =
      ENNReal.ofReal b⁻¹ * ENNReal.ofReal (u / b)⁻¹ := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hb.le)]
    congr 1
    simp [div_eq_mul_inv, mul_inv_rev, hb.ne']
  calc
    _ = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal b⁻¹ *
        (ENNReal.ofReal (u / b)⁻¹ * f (u / b)) := by
      apply lintegral_congr
      intro u
      dsimp only [Pi.mul_apply, Function.comp_apply]
      rw [hweight u, mul_assoc]
    _ = ENNReal.ofReal b⁻¹ *
        ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u / b)⁻¹ * f (u / b) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal b⁻¹ *
        ∫⁻ t, ENNReal.ofReal t⁻¹ * f t
          ∂(Measure.map (fun u : ℝ => u / b) (volume.restrict (Ioi (0 : ℝ)))) := by
      congr 1
      exact (lintegral_map (show Measurable (fun t : ℝ => ENNReal.ofReal t⁻¹ * f t)
        from hr.mul hf) hm).symm
    _ = _ := by
      rw [hmap, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hb.le), inv_mul_cancel₀ hb.ne',
        ENNReal.ofReal_one, one_mul]
      rfl

/-- A positive measurable scale depending on the free coordinates preserves the radial measure. -/
theorem radial_product_scaling {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (B : α → ℝ) (hB : Measurable B)
    (hpos : ∀ᵐ p ∂μ, 0 < B p) :
    MeasurePreserving (fun q : α × ℝ => (q.1, q.2 / B q.1))
      (μ.prod polarRadialMeasure) (μ.prod polarRadialMeasure) := by
  have : SigmaFinite polarRadialMeasure := by
    unfold polarRadialMeasure
    infer_instance
  apply (MeasurePreserving.id μ).skew_product
    (g := fun p u => u / B p) (μc := polarRadialMeasure) (μd := polarRadialMeasure)
  · exact measurable_snd.div (hB.comp measurable_fst)
  · filter_upwards [hpos] with p hp
    exact (radial_constant_scaling (B p) hp).map_eq

end ArtinPrimitiveRoots.Proofs.thsol_sheets
