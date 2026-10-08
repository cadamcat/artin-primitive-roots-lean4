import ArtinPrimitiveRoots.A2.Proofs.A2_RF_FORWARD.IntegralSeries

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Filter
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol

theorem integral_kernel_series {ι : Type} [Countable ι]
    (q : ι → ℝ) (hq : ∀ i, 0 < q i) (a : ι → ℂ)
    (V : ℝ → ℂ) (hV : Measurable V) (K : ℝ → ℂ)
    (hK : AEStronglyMeasurable K (volume.restrict (Set.Ioi (0 : ℝ))))
    (hSeries : ∀ l : ℝ, 0 < l → Summable (fun i => ‖a i * V (q i * l)‖))
    (G : ℝ → ℂ)
    (hEval : ∀ u : ℝ, 0 < u →
      (∫ t in Set.Ioi (0 : ℝ), K t * V (u * t) / (t : ℂ)) = G u)
    (Z : ℝ) (hZ : 0 < Z)
    (hAbs : IntegrableOn (fun t : ℝ => ‖K t‖ *
      (∑' i, ‖a i * V (q i * t / Z)‖) / t) (Set.Ioi 0)) :
    IntegrableOn (fun t : ℝ => K t *
      (∑' i, a i * V (q i * t / Z)) / (t : ℂ)) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), K t *
      (∑' i, a i * V (q i * t / Z)) / (t : ℂ)) =
        ∑' i, a i * G (q i / Z) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let f : ι → ℝ → ℂ := fun i t => K t * (a i * V (q i * t / Z)) / (t : ℂ)
  have hVt (i : ι) : Measurable (fun t : ℝ => V (q i * t / Z)) :=
    hV.comp ((measurable_const.mul measurable_id).div_const Z)
  have hInv : Measurable (fun t : ℝ => (t : ℂ)⁻¹) :=
    Complex.continuous_ofReal.measurable.inv
  have hf (i : ι) : AEStronglyMeasurable (f i) ν := by
    have h := (hK.mul ((hVt i).aestronglyMeasurable.const_mul (a i))).mul
      hInv.aestronglyMeasurable
    have heq : f i = (fun t : ℝ => K t * (a i * V (q i * t / Z))) *
        (fun t : ℝ => (t : ℂ)⁻¹) := by
      funext t
      simp only [f, Pi.mul_apply, div_eq_mul_inv]
    rw [heq]
    exact h
  have hPositive : ∀ᵐ t ∂ν, 0 < t := by
    exact ae_restrict_mem measurableSet_Ioi
  have hNorm (t : ℝ) (ht : 0 < t) (i : ι) :
      ‖f i t‖ = (‖K t‖ / t) * ‖a i * V (q i * t / Z)‖ := by
    simp only [f, norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht.le]
    ring
  have hTerm (t : ℝ) (ht : 0 < t) :
      Summable (fun i => ‖a i * V (q i * t / Z)‖) := by
    simpa only [mul_div_assoc] using hSeries (t / Z) (div_pos ht hZ)
  have hSum : ∀ᵐ t ∂ν, Summable (fun i => ‖f i t‖) := by
    filter_upwards [hPositive] with t ht
    have heq : (fun i => ‖f i t‖) =
        fun i => (‖K t‖ / t) * ‖a i * V (q i * t / Z)‖ := funext (hNorm t ht)
    rw [heq]
    exact (hTerm t ht).mul_left _
  have hNormEq : (fun t => ∑' i, ‖f i t‖) =ᵐ[ν]
      fun t : ℝ => ‖K t‖ * (∑' i, ‖a i * V (q i * t / Z)‖) / t := by
    filter_upwards [hPositive] with t ht
    calc
      _ = ∑' i, (‖K t‖ / t) * ‖a i * V (q i * t / Z)‖ :=
        tsum_congr (hNorm t ht)
      _ = (‖K t‖ / t) * ∑' i, ‖a i * V (q i * t / Z)‖ := tsum_mul_left
      _ = _ := by ring
  have hAbs' : Integrable (fun t : ℝ => ‖K t‖ *
      (∑' i, ‖a i * V (q i * t / Z)‖) / t) ν := hAbs
  have hData := integral_tsum_of_norm_sum ν f hf hSum (hAbs'.congr hNormEq.symm)
  have hFEq : (fun t => ∑' i, f i t) =
      fun t : ℝ => K t * (∑' i, a i * V (q i * t / Z)) / (t : ℂ) := by
    funext t
    dsimp only [f]
    rw [tsum_div_const, tsum_mul_left]
  have hEach (i : ι) : (∫ t, f i t ∂ν) = a i * G (q i / Z) := by
    calc
      _ = ∫ t, a i * (K t * V ((q i / Z) * t) / (t : ℂ)) ∂ν := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro t
        have harg : q i * t / Z = (q i / Z) * t := by ring
        dsimp only [f]
        rw [harg]
        ring
      _ = a i * ∫ t, K t * V ((q i / Z) * t) / (t : ℂ) ∂ν :=
        integral_const_mul _ _
      _ = a i * G (q i / Z) := by
        rw [hEval _ (div_pos (hq i) hZ)]
  constructor
  · rw [← hFEq]
    exact hData.1
  · calc
      _ = ∫ t, ∑' i, f i t ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => (congrFun hFEq t).symm)
      _ = ∑' i, ∫ t, f i t ∂ν := hData.2
      _ = _ := tsum_congr hEach

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
