import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
open MeasureTheory Set
open scoped Classical Real Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_sheets

def squarePolarChart (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.sqrt p.1 * Real.cos (2 * Real.pi * p.2),
    Real.sqrt p.1 * Real.sin (2 * Real.pi * p.2))

def squarePolarDerivative (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![Real.cos (2 * Real.pi * p.2) / (2 * Real.sqrt p.1),
      -(2 * Real.pi * Real.sqrt p.1 * Real.sin (2 * Real.pi * p.2));
      Real.sin (2 * Real.pi * p.2) / (2 * Real.sqrt p.1),
      2 * Real.pi * Real.sqrt p.1 * Real.cos (2 * Real.pi * p.2)]).toContinuousLinearMap

def complexPolarPoint (p : ℝ × ℝ) : ℂ :=
  (Real.sqrt p.1 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * p.2)

/-- The radial measure dt/t on positive real numbers. -/
def polarRadialMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal t⁻¹

private theorem square_polar_geometry :
    let D : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1
    InjOn squarePolarChart D ∧
    (∀ p ∈ D, HasFDerivAt squarePolarChart (squarePolarDerivative p) p) ∧
    (∀ p ∈ D, (squarePolarDerivative p).det = Real.pi) ∧
    squarePolarChart '' D =ᵐ[volume] (univ : Set (ℝ × ℝ)) ∧
    (∀ p, Complex.measurableEquivRealProd.symm (squarePolarChart p) = complexPolarPoint p) := by
  let D : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1
  have hrot (p : ℝ × ℝ) : squarePolarChart p =
      -polarCoord.symm (Real.sqrt p.1, 2 * Real.pi * p.2 - Real.pi) := by
    ext <;> simp [squarePolarChart, polarCoord_symm_apply, Real.cos_sub, Real.sin_sub]
  have htarget (p : ℝ × ℝ) (hp : p ∈ D) :
      (Real.sqrt p.1, 2 * Real.pi * p.2 - Real.pi) ∈ polarCoord.target := by
    change 0 < Real.sqrt p.1 ∧ -Real.pi < 2 * Real.pi * p.2 - Real.pi ∧
      2 * Real.pi * p.2 - Real.pi < Real.pi
    refine ⟨Real.sqrt_pos.mpr hp.1, ?_, ?_⟩ <;> nlinarith [Real.pi_pos, hp.2.1, hp.2.2]
  have hinj : InjOn squarePolarChart D := by
    intro p hp q hq heq
    rw [hrot p, hrot q, neg_inj] at heq
    have h := polarCoord.symm.injOn (htarget p hp) (htarget q hq) heq
    have hr := congrArg Prod.fst h
    have hθ := congrArg Prod.snd h
    dsimp only at hr hθ
    apply Prod.ext
    · calc
        p.1 = Real.sqrt p.1 ^ 2 := (Real.sq_sqrt hp.1.le).symm
        _ = Real.sqrt q.1 ^ 2 := by rw [hr]
        _ = q.1 := Real.sq_sqrt hq.1.le
    · nlinarith [Real.pi_pos]
  have hderiv (p : ℝ × ℝ) (hp : p ∈ D) :
      HasFDerivAt squarePolarChart (squarePolarDerivative p) p := by
    have hs := (Real.hasDerivAt_sqrt hp.1.ne').comp_hasFDerivAt p
      (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ))
    have ha := (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)).const_mul (2 * Real.pi)
    have hc := (Real.hasDerivAt_cos (2 * Real.pi * p.2)).comp_hasFDerivAt p ha
    have hn := (Real.hasDerivAt_sin (2 * Real.pi * p.2)).comp_hasFDerivAt p ha
    convert (hs.mul hc).prodMk (hs.mul hn) using 1 <;>
      first
      | rfl
      | (ext x <;> simp [squarePolarChart, squarePolarDerivative,
          Matrix.toLin_finTwoProd_toContinuousLinearMap, div_eq_mul_inv, smul_smul,
          mul_comm, mul_left_comm, mul_assoc, add_comm, neg_smul, smul_neg])
  have hdet (p : ℝ × ℝ) (hp : p ∈ D) : (squarePolarDerivative p).det = Real.pi := by
    unfold squarePolarDerivative
    simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
      Matrix.det_fin_two_of]
    have hs : Real.sqrt p.1 ≠ 0 := (Real.sqrt_pos.mpr hp.1).ne'
    field_simp [hs]
    nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * p.2)]
  have hsurj (q : ℝ × ℝ) (hq : -q ∈ polarCoord.source) : q ∈ squarePolarChart '' D := by
    let r := (polarCoord (-q)).1
    let θ := (polarCoord (-q)).2
    have ht := polarCoord.map_source' hq
    change 0 < r ∧ -Real.pi < θ ∧ θ < Real.pi at ht
    let p : ℝ × ℝ := (r ^ 2, (θ + Real.pi) / (2 * Real.pi))
    refine ⟨p, ?_, ?_⟩
    · change 0 < r ^ 2 ∧ 0 < (θ + Real.pi) / (2 * Real.pi) ∧
        (θ + Real.pi) / (2 * Real.pi) < 1
      refine ⟨sq_pos_of_pos ht.1, div_pos (by linarith) (by positivity), ?_⟩
      apply (div_lt_one (by positivity)).mpr
      linarith
    · rw [hrot p]
      have ha : 2 * Real.pi * ((θ + Real.pi) / (2 * Real.pi)) - Real.pi = θ := by
        field_simp [Real.pi_ne_zero]
        ring
      dsimp only [p, Prod.fst, Prod.snd]
      rw [Real.sqrt_sq ht.1.le, ha]
      change -polarCoord.symm (polarCoord (-q)) = q
      rw [polarCoord.left_inv hq, neg_neg]
  have hconull : squarePolarChart '' D =ᵐ[volume] (univ : Set (ℝ × ℝ)) := by
    have hk : volume (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) : Set (ℝ × ℝ)) = 0 := by
      apply Measure.addHaar_submodule
      rw [Ne, LinearMap.ker_eq_top]
      intro h
      have he := congrArg (fun f : (ℝ × ℝ) →ₗ[ℝ] ℝ => f (0, 1)) h
      simp at he
    have hb : ∀ᵐ q : ℝ × ℝ ∂volume, q.2 ≠ 0 := by
      have hks : (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) : Set (ℝ × ℝ)) =
          {q : ℝ × ℝ | q.2 = 0} := by
        ext q
        simp
      rw [hks] at hk
      simpa only [ae_iff, not_not] using hk
    filter_upwards [hb] with q hq
    have hq' : -q ∈ polarCoord.source := by
      change 0 < (-q).1 ∨ (-q).2 ≠ 0
      exact Or.inr (neg_ne_zero.mpr hq)
    exact propext (iff_of_true (hsurj q hq') (mem_univ q))
  have hC (p : ℝ × ℝ) : Complex.measurableEquivRealProd.symm (squarePolarChart p) = complexPolarPoint p := by
    have ha : (2 * Real.pi * Complex.I * (p.2 : ℂ)) =
        ((2 * Real.pi * p.2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    change Complex.equivRealProd.symm (squarePolarChart p) = _
    rw [Complex.equivRealProd_symm_apply]
    dsimp only [squarePolarChart, Prod.fst, Prod.snd]
    dsimp only [complexPolarPoint]
    rw [ha, Complex.exp_ofReal_mul_I]
    push_cast
    ring
  exact ⟨hinj, hderiv, hdet, hconull, hC⟩

/-- The polar parameter map sends pi times (dt/t)dtheta to the complex multiplicative measure. -/
theorem complex_polar_measurePreserving :
    MeasurePreserving complexPolarPoint
      (ENNReal.ofReal Real.pi • polarRadialMeasure.prod (volume.restrict (Ioc (0 : ℝ) 1)))
      (volume.withDensity fun z => ENNReal.ofReal (Complex.normSq z)⁻¹) := by
  let D : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1
  obtain ⟨hinj, hderiv, hdet, hconull, hC⟩ := square_polar_geometry
  have hm : Measurable complexPolarPoint := by
    unfold complexPolarPoint
    fun_prop
  have hr : Measurable (fun t : ℝ => ENNReal.ofReal t⁻¹) := by fun_prop
  have hw : Measurable (fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹) := by fun_prop
  have hnorm (p : ℝ × ℝ) (hp : p ∈ D) : Complex.normSq (complexPolarPoint p) = p.1 := by
    unfold complexPolarPoint
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (p.2 : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hp.1.le]
  have hd (p : ℝ × ℝ) (hp : p ∈ D) :
      HasFDerivWithinAt squarePolarChart (squarePolarDerivative p) D p :=
    (hderiv p hp).hasFDerivWithinAt
  refine ⟨hm, Measure.ext_of_lintegral _ ?_⟩
  intro f hf
  have htarget : (∫⁻ z, f z ∂(volume.withDensity fun z => ENNReal.ofReal (Complex.normSq z)⁻¹)) =
      ∫⁻ p in D, ENNReal.ofReal Real.pi * ENNReal.ofReal p.1⁻¹ * f (complexPolarPoint p) := by
    calc
      _ = ∫⁻ z, ENNReal.ofReal (Complex.normSq z)⁻¹ * f z :=
        lintegral_withDensity_eq_lintegral_mul volume hw hf
      _ = ∫⁻ q : ℝ × ℝ,
          ENNReal.ofReal (Complex.normSq (Complex.measurableEquivRealProd.symm q))⁻¹ *
            f (Complex.measurableEquivRealProd.symm q) :=
        (Complex.volume_preserving_equiv_real_prod.symm.lintegral_comp_emb
          Complex.measurableEquivRealProd.symm.measurableEmbedding _).symm
      _ = ∫⁻ q in squarePolarChart '' D,
          ENNReal.ofReal (Complex.normSq (Complex.measurableEquivRealProd.symm q))⁻¹ *
            f (Complex.measurableEquivRealProd.symm q) := by
        rw [← setLIntegral_univ]
        exact setLIntegral_congr hconull.symm
      _ = ∫⁻ p in D, ENNReal.ofReal |(squarePolarDerivative p).det| *
          (ENNReal.ofReal (Complex.normSq
            (Complex.measurableEquivRealProd.symm (squarePolarChart p)))⁻¹ *
            f (Complex.measurableEquivRealProd.symm (squarePolarChart p))) :=
        lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
          (measurableSet_Ioi.prod measurableSet_Ioo) hd hinj _
      _ = _ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
        rw [hC p, hdet p hp, abs_of_pos Real.pi_pos, hnorm p hp, mul_assoc]
  rw [lintegral_map hf hm, lintegral_smul_measure]
  change ENNReal.ofReal Real.pi *
    (∫⁻ p, f (complexPolarPoint p) ∂polarRadialMeasure.prod (volume.restrict (Ioc (0 : ℝ) 1))) = _
  rw [polarRadialMeasure, prod_withDensity_left hr]
  have hpw : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1⁻¹) := by fun_prop
  have hpf : Measurable (fun p : ℝ × ℝ => f (complexPolarPoint p)) := hf.comp hm
  rw [lintegral_withDensity_eq_lintegral_mul
    ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) 1))) hpw hpf]
  rw [← restrict_Ioo_eq_restrict_Ioc, Measure.prod_restrict]
  change ENNReal.ofReal Real.pi *
    (∫⁻ p in D, ENNReal.ofReal p.1⁻¹ * f (complexPolarPoint p)) = _
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simpa only [mul_assoc] using htarget.symm

/-- The normalized complex polar formula for the real reciprocal density used by theta sheets. -/
theorem complex_polar (g : ℂ → ℂ)
    (hg : Integrable g (volume.withDensity fun z => ENNReal.ofReal (Complex.normSq z)⁻¹)) :
    IntegrableOn (fun t : ℝ =>
      (∫ θ in Ioc (0 : ℝ) 1,
        g ((Real.sqrt t : ℂ) * Complex.exp (2 * Real.pi * Complex.I * θ))) / t)
      (Ioi 0) ∧
    ∫ z, g z ∂(volume.withDensity fun z => ENNReal.ofReal (Complex.normSq z)⁻¹) =
      Real.pi * ∫ t in Ioi (0 : ℝ),
        (∫ θ in Ioc (0 : ℝ) 1,
          g ((Real.sqrt t : ℂ) * Complex.exp (2 * Real.pi * Complex.I * θ))) / t := by
  let C := complexPolarPoint
  let D : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1
  have hchart (k : ℂ → ℂ) :
      (Integrable k volume ↔ IntegrableOn (fun p => Real.pi • k (C p)) D) ∧
      (∫ z, k z) = ∫ p in D, Real.pi • k (C p) := by
    obtain ⟨hinj, hderiv, hdet, hconull, hC⟩ := square_polar_geometry
    have hdiff (p : ℝ × ℝ) (hp : p ∈ D) :
        HasFDerivWithinAt squarePolarChart (squarePolarDerivative p) D p :=
      (hderiv p hp).hasFDerivWithinAt
    have hmap := Complex.volume_preserving_equiv_real_prod.symm
    have hgi : Integrable k volume ↔
        Integrable (fun q : ℝ × ℝ => k (Complex.measurableEquivRealProd.symm q)) volume :=
      (hmap.integrable_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding).symm
    have hseti := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      (measurableSet_Ioi.prod measurableSet_Ioo) hdiff hinj
      (fun q => k (Complex.measurableEquivRealProd.symm q))
    have hseteq := integral_image_eq_integral_abs_det_fderiv_smul volume
      (measurableSet_Ioi.prod measurableSet_Ioo) hdiff hinj
      (fun q => k (Complex.measurableEquivRealProd.symm q))
    have heq : (fun p => |(squarePolarDerivative p).det| •
        k (Complex.measurableEquivRealProd.symm (squarePolarChart p))) =ᵐ[volume.restrict D]
        (fun p => Real.pi • k (C p)) := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
      rw [hdet p hp, abs_of_pos Real.pi_pos, hC p]
    refine ⟨?_, ?_⟩
    · rw [hgi, ← integrableOn_univ, ← integrableOn_congr_set_ae hconull]
      exact hseti.trans (integrableOn_congr_fun_ae heq)
    · calc
        _ = ∫ q : ℝ × ℝ, k (Complex.measurableEquivRealProd.symm q) :=
          (hmap.integral_comp Complex.measurableEquivRealProd.symm.measurableEmbedding k).symm
        _ = ∫ q in squarePolarChart '' D, k (Complex.measurableEquivRealProd.symm q) := by
          rw [← setIntegral_univ]
          exact setIntegral_congr_set hconull.symm
        _ = _ := hseteq.trans (integral_congr_ae heq)
  have hmeas : Measurable (fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹) := by
    fun_prop
  have hfinite : ∀ᵐ z : ℂ ∂volume, ENNReal.ofReal (Complex.normSq z)⁻¹ < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hweight (z : ℂ) : (ENNReal.ofReal (Complex.normSq z)⁻¹).toReal =
      (Complex.normSq z)⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.mpr (Complex.normSq_nonneg z))
  have hg' : Integrable (fun z => (Complex.normSq z)⁻¹ • g z) volume := by
    simpa only [hweight] using (integrable_withDensity_iff_integrable_smul' hmeas hfinite).mp hg
  have hnorm (p : ℝ × ℝ) (hp : p ∈ D) : Complex.normSq (C p) = p.1 := by
    dsimp [C, complexPolarPoint]
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (p.2 : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hp.1.le]
  have heq : (fun p => Real.pi • ((Complex.normSq (C p))⁻¹ • g (C p))) =ᵐ[volume.restrict D]
      (fun p => Real.pi • (g (C p) / p.1)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
    rw [hnorm p hp]
    simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm (g (C p))]
  have hi : IntegrableOn (fun p => Real.pi • (g (C p) / p.1)) D :=
    ((hchart _).1.mp hg').congr heq
  have hj : IntegrableOn (fun p => g (C p) / p.1) D := by
    have h := Integrable.smul Real.pi⁻¹ hi
    change IntegrableOn (fun p => Real.pi⁻¹ • (Real.pi • (g (C p) / p.1))) D at h
    simpa only [smul_smul, inv_mul_cancel₀ Real.pi_ne_zero, one_smul] using h
  have hp : Integrable (fun p : ℝ × ℝ => g (C p) / p.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    simpa only [IntegrableOn, D, Measure.volume_eq_prod, ← Measure.prod_restrict] using hj
  have hfubini : (∫ p in D, g (C p) / p.1) =
      ∫ t in Ioi (0 : ℝ), (∫ θ in Ioc (0 : ℝ) 1, g (C (t, θ))) / t := by
    change (∫ p, g (C p) / p.1 ∂((volume.prod volume).restrict D)) = _
    rw [← Measure.prod_restrict]
    rw [integral_prod _ hp]
    simp only [restrict_Ioo_eq_restrict_Ioc, integral_div]
  have hinner : IntegrableOn (fun t : ℝ => (∫ θ in Ioc (0 : ℝ) 1, g (C (t, θ))) / t)
      (Ioi 0) := by
    simpa only [IntegrableOn, restrict_Ioo_eq_restrict_Ioc, integral_div]
      using hp.integral_prod_left
  refine ⟨hinner, ?_⟩
  calc
    _ = ∫ z, (Complex.normSq z)⁻¹ • g z := by
      simpa only [hweight] using
        (integral_withDensity_eq_integral_toReal_smul hmeas hfinite g)
    _ = ∫ p in D, Real.pi • ((Complex.normSq (C p))⁻¹ • g (C p)) := (hchart _).2
    _ = ∫ p in D, Real.pi • (g (C p) / p.1) := integral_congr_ae heq
    _ = Real.pi • ∫ p in D, g (C p) / p.1 := integral_smul _ _
    _ = _ := by rw [hfubini]; rfl

end ArtinPrimitiveRoots.Proofs.thsol_sheets
