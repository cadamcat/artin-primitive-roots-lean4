import ArtinPrimitiveRoots.Theta.AnalysisS
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal Topology
noncomputable section

namespace ArtinPrimitiveRoots.A2

theorem bridgeWithDensity_openPos_of_nonzero_dense
    {E : Type} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] [Zero E]
    (μ : Measure E) [Measure.IsOpenPosMeasure μ] (f : E → ℝ≥0∞)
    (hf : Measurable f) (hcont : ∀ x, x ≠ 0 → ContinuousAt f x)
    (hpos : ∀ x, x ≠ 0 → f x ≠ 0)
    (hdense : ∀ U : Set E, IsOpen U → U.Nonempty → ∃ x ∈ U, x ≠ 0) :
    Measure.IsOpenPosMeasure (μ.withDensity f) := by
  constructor
  intro U hU hUne
  obtain ⟨x, hxU, hx0⟩ := hdense U hU hUne
  have hTarget : IsOpen ({z : ℝ≥0∞ | z ≠ 0}) := isOpen_ne
  have hpre : f ⁻¹' {z | z ≠ 0} ∈ 𝓝 x :=
    (hcont x hx0).preimage_mem_nhds (hTarget.mem_nhds (hpos x hx0))
  have hmem : Function.support f ∩ U ∈ 𝓝 x := by
    have hsupport : Function.support f ∈ 𝓝 x := by
      simpa [Function.support] using hpre
    exact Filter.inter_mem hsupport (hU.mem_nhds hxU)
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hmem
  have hmeasure : 0 < μ (Function.support f ∩ U) :=
    lt_of_lt_of_le (hVopen.measure_pos μ ⟨x, hxV⟩) (measure_mono hVsub)
  have hlin : 0 < ∫⁻ y in U, f y ∂μ := (setLIntegral_pos_iff hf).2 hmeasure
  rw [withDensity_apply _ hU.measurableSet]
  exact ne_of_gt hlin

private theorem bridgeComplex_nonzero_dense :
    ∀ U : Set ℂ, IsOpen U → U.Nonempty → ∃ z ∈ U, z ≠ 0 := by
  intro U hU ⟨z, hz⟩
  by_cases hz0 : z ≠ 0
  · exact ⟨z, hz, hz0⟩
  · have hzEq : z = 0 := not_ne_iff.mp hz0
    subst z
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
    have hr2 : 0 < r / 2 := by linarith
    let z : ℂ := (r / 2 : ℝ)
    have hzmem : z ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_pos hr2]
      linarith
    have hz' : z ≠ 0 := by
      dsimp [z]
      exact Complex.ofReal_ne_zero.mpr hr2.ne'
    exact ⟨z, hball hzmem, hz'⟩

theorem bridgeComplex_mulHaar_openPos :
    Measure.IsOpenPosMeasure (ArtinPrimitiveRoots.A1.Theta.mulHaarC) := by
  let f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ((Complex.normSq z)⁻¹)
  have hf : Measurable f := by fun_prop
  have hcont : ∀ z, z ≠ 0 → ContinuousAt f z := by
    intro z hz
    have hp : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
    dsimp [f]
    exact ENNReal.continuous_ofReal.continuousAt.comp
      (ContinuousAt.inv₀ Complex.continuous_normSq.continuousAt hp.ne')
  have hpos : ∀ z, z ≠ 0 → f z ≠ 0 := by
    intro z hz
    have hp : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
    dsimp [f]
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hp)).ne'
  letI : Measure.IsOpenPosMeasure (volume : Measure ℂ) := inferInstance
  simpa [ArtinPrimitiveRoots.A1.Theta.mulHaarC, f] using
    (bridgeWithDensity_openPos_of_nonzero_dense (volume : Measure ℂ) f hf hcont hpos
      bridgeComplex_nonzero_dense)

/-- A radial complex-place majorant with the same small-radius order as the sheet hypotheses
and more than enough decay at infinity. -/
def bridgeComplexMajorant (δ : ℝ) (z : ℂ) : ℝ :=
  if z = 0 then 0 else
    Complex.normSq z ^ δ / (1 + Complex.normSq z) ^ (δ + 3)

theorem bridgeComplexMajorant_measurable (δ : ℝ) : Measurable (bridgeComplexMajorant δ) := by
  unfold bridgeComplexMajorant
  apply Measurable.ite (measurableSet_singleton 0)
  · exact measurable_const
  · fun_prop

theorem bridgeComplexMajorant_nonneg (δ : ℝ) (z : ℂ) :
    0 ≤ bridgeComplexMajorant δ z := by
  by_cases hz : z = 0
  · simp [bridgeComplexMajorant, hz]
  · rw [bridgeComplexMajorant, if_neg hz]
    have hq : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
    positivity

theorem bridgeComplex_sixthPower_range_closed :
    IsClosed (Set.range (fun z : ℂ => z ^ 6)) := by
  simpa only [Set.image_univ] using (isClosedMap_pow ℂ 6) Set.univ isClosed_univ

theorem bridgeSheetHypC_measurable (δ : ℝ) (f : ℂ → ℂ)
    (hf : ArtinPrimitiveRoots.A1.SheetHypC δ f) : Measurable f := by
  refine measurable_of_continuousOn_compl_singleton (0 : ℂ) ?_
  convert hf.1.continuousOn using 1
  ext z
  simp

theorem bridgeComplexMajorant_pos (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : z ≠ 0) :
    0 < bridgeComplexMajorant δ z := by
  rw [bridgeComplexMajorant, if_neg hz]
  have hq : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  positivity

theorem bridgeComplexMajorant_scale (δ : ℝ) (hδ : 0 < δ) (c : ℂ) (hc : c ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, bridgeComplexMajorant δ (c * z) ≤ C * bridgeComplexMajorant δ z := by
  let d : ℝ := Complex.normSq c
  let A : ℝ := max 1 d⁻¹
  let p : ℝ := δ + 3
  let C : ℝ := d ^ δ * A ^ p
  have hd : 0 < d := by dsimp [d]; exact Complex.normSq_pos.mpr hc
  have hA1 : 1 ≤ A := by dsimp [A]; exact le_max_left _ _
  have hAd : d⁻¹ ≤ A := by dsimp [A]; exact le_max_right _ _
  have hAdmul : 1 ≤ A * d := by
    have := mul_le_mul_of_nonneg_right hAd hd.le
    have hcancel : d⁻¹ * d = 1 := inv_mul_cancel₀ hd.ne'
    nlinarith
  have hp : 0 < p := by dsimp [p]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro z
  by_cases hz : z = 0
  · simp [bridgeComplexMajorant, hz]
  · let q : ℝ := Complex.normSq z
    have hq : 0 < q := by dsimp [q]; exact Complex.normSq_pos.mpr hz
    have hbase : 1 + q ≤ A * (1 + d * q) := by
      have hdecomp : A * (1 + d * q) - (1 + q) = (A - 1) + (A * d - 1) * q := by ring
      have hdiff : 0 ≤ A * (1 + d * q) - (1 + q) := by
        rw [hdecomp]
        exact add_nonneg (sub_nonneg.mpr hA1)
          (mul_nonneg (sub_nonneg.mpr hAdmul) hq.le)
      linarith
    have hden : 0 < 1 + d * q := by positivity
    have hratio : (1 + q) / (1 + d * q) ≤ A := (div_le_iff₀ hden).2 (by nlinarith [hbase])
    have hratioPow :
        (1 + q) ^ p / (1 + d * q) ^ p ≤ A ^ p := by
      have h := Real.rpow_le_rpow (by positivity : 0 ≤ (1 + q) / (1 + d * q)) hratio hp.le
      rw [Real.div_rpow (by positivity) (by positivity)] at h
      exact h
    have hquot : q ^ δ / (1 + d * q) ^ p ≤ A ^ p * (q ^ δ / (1 + q) ^ p) := by
      calc
        q ^ δ / (1 + d * q) ^ p =
            (q ^ δ / (1 + q) ^ p) * ((1 + q) ^ p / (1 + d * q) ^ p) := by
              field_simp <;> ring
        _ ≤ (q ^ δ / (1 + q) ^ p) * A ^ p :=
          mul_le_mul_of_nonneg_left hratioPow (by positivity)
        _ = A ^ p * (q ^ δ / (1 + q) ^ p) := by ring
    calc
      bridgeComplexMajorant δ (c * z) = d ^ δ * (q ^ δ / (1 + d * q) ^ p) := by
        simp [bridgeComplexMajorant, d, q, p, hz, hc, Complex.normSq_mul,
          Real.mul_rpow hd.le hq.le]
        ring
      _ ≤ d ^ δ * (A ^ p * (q ^ δ / (1 + q) ^ p)) :=
        mul_le_mul_of_nonneg_left hquot (Real.rpow_nonneg hd.le δ)
      _ = C * bridgeComplexMajorant δ z := by
        simp [bridgeComplexMajorant, C, d, q, p, hz]
        ring

private def bridgeComplexDensityMajorant (δ : ℝ) (z : ℂ) : ℝ :=
  if z = 0 then 0 else
    Complex.normSq z ^ (δ - 1) / (1 + Complex.normSq z) ^ (δ + 3)

theorem bridgeComplexMajorant_integrable (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun z : ℂ => bridgeComplexMajorant δ z)
      (ArtinPrimitiveRoots.A1.Theta.mulHaarC) := by
  let g : ℂ → ℝ := bridgeComplexDensityMajorant δ
  let s : Set ℂ := {z | z ≠ 0}
  have hs : MeasurableSet s := by
    dsimp [s]
    exact (measurableSet_singleton (0 : ℂ)).compl
  have hqcont : ContinuousOn (fun z : ℂ => Complex.normSq z) s :=
    Complex.continuous_normSq.continuousOn
  have hqpos : ∀ z ∈ s, Complex.normSq z ≠ 0 := by
    intro z hz
    exact (Complex.normSq_pos.mpr hz).ne'
  have hnumcont : ContinuousOn (fun z : ℂ => Complex.normSq z ^ (δ - 1)) s :=
    hqcont.rpow_const (fun z hz => Or.inl (hqpos z hz))
  have hdencont : ContinuousOn (fun z : ℂ => (1 + Complex.normSq z) ^ (δ + 3)) s := by
    apply (continuousOn_const.add hqcont).rpow_const
    intro z hz
    have hq : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
    have hbase : 0 < 1 + Complex.normSq z := by linarith
    exact Or.inl hbase.ne'
  have hg_cont : ContinuousOn g s := by
    have hraw : ContinuousOn
        (fun z : ℂ => Complex.normSq z ^ (δ - 1) / (1 + Complex.normSq z) ^ (δ + 3)) s := by
      apply hnumcont.div hdencont
      intro z hz
      have hq : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
      have hbase : 0 < 1 + Complex.normSq z := by linarith
      exact (Real.rpow_pos_of_pos hbase _).ne'
    apply hraw.congr
    intro z hz
    have hz0 : z ≠ 0 := hz
    simp [g, bridgeComplexDensityMajorant, hz0]
  have hg_aemeas_s : AEMeasurable g (volume.restrict s) := hg_cont.aemeasurable hs
  have hs_ae : s =ᵐ[volume] univ := by
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    simp [s, hz]
  have hrestrict : volume.restrict s = volume := by
    rw [Measure.restrict_congr_set hs_ae]
    simp
  have hg_meas : AEStronglyMeasurable g volume := by
    rw [← hrestrict]
    exact hg_aemeas_s.aestronglyMeasurable
  have hnear : IntegrableOn g (Metric.ball (0 : ℂ) 1) volume := by
    exact MeasureTheory.integrableOn_ball_of_norm_le_rpow
      (E := ℂ) (F := ℝ) (μ := volume) (f := g) (C := 1) (r := 1)
      (α := 2 - δ)
      (hd := by norm_num [Complex.finrank_real_complex])
      (hα := by simpa [Complex.finrank_real_complex] using (sub_lt_self (2 : ℝ) hδ))
      (h_decay := by
        have h0ae : ∀ᵐ z : ℂ ∂volume.restrict (Metric.ball (0 : ℂ) 1), z ≠ 0 :=
          ae_restrict_of_ae (volume.ae_ne (0 : ℂ))
        filter_upwards [ae_restrict_mem measurableSet_ball, h0ae] with z hzball hz0
        have hq : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
        have hbase1 : 1 ≤ 1 + Complex.normSq z := by linarith [Complex.normSq_nonneg z]
        have hexp : 0 ≤ δ + 3 := by linarith [hδ]
        have hden : 1 ≤ (1 + Complex.normSq z) ^ (δ + 3) := Real.one_le_rpow hbase1 hexp
        have hpow : Complex.normSq z ^ (δ - 1) = ‖z‖ ^ (2 * (δ - 1)) := by
          rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast (‖z‖) 2]
          exact (Real.rpow_mul (norm_nonneg z) 2 (δ - 1)).symm
        have hnormlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hzball
        have hpowle : ‖z‖ ^ (2 * (δ - 1)) ≤ ‖z‖ ^ (δ - 2) := by
          exact Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hz0) hnormlt.le
            (by linarith [hδ])
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · calc
            g z = Complex.normSq z ^ (δ - 1) / (1 + Complex.normSq z) ^ (δ + 3) := by
              simp [g, bridgeComplexDensityMajorant, hz0]
            _ ≤ Complex.normSq z ^ (δ - 1) := div_le_self (by positivity) hden
            _ = ‖z‖ ^ (2 * (δ - 1)) := hpow
            _ ≤ ‖z‖ ^ (δ - 2) := hpowle
            _ = 1 * ‖z‖ ^ (-(2 - δ)) := by
              rw [show δ - 2 = -(2 - δ) by ring]
              simp
        · simp [g, bridgeComplexDensityMajorant, hz0]
          positivity)
      (h_meas := hg_meas)
  have hfar : IntegrableOn g ((Metric.ball (0 : ℂ) 1)ᶜ) volume := by
    have hbase : Integrable (fun z : ℂ => (1 + ‖z‖ ^ 2) ^ (-3 : ℝ)) volume := by
      simpa only [show (-6 : ℝ) / 2 = -3 by norm_num] using
        (integrable_rpow_neg_one_add_norm_sq (E := ℂ)
          (μ := (volume : Measure ℂ)) (r := 6)
          (by norm_num [Complex.finrank_real_complex]))
    refine (hbase.mono_measure Measure.restrict_le_self).mono' ?_ ?_
    · exact hg_meas.restrict
    · filter_upwards [ae_restrict_mem (show MeasurableSet ((Metric.ball (0 : ℂ) 1)ᶜ) from measurableSet_ball.compl)] with z hz
      have hn : 1 ≤ ‖z‖ := by simpa [Metric.mem_ball, dist_zero_right] using hz
      have hz0 : z ≠ 0 := by
        intro h
        subst z
        norm_num at hn
      have hq : 1 ≤ Complex.normSq z := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
      have hnum : Complex.normSq z ^ (δ - 1) ≤ (1 + Complex.normSq z) ^ δ := by
        calc
          Complex.normSq z ^ (δ - 1) ≤ Complex.normSq z ^ δ :=
            Real.rpow_le_rpow_of_exponent_le hq (by linarith)
          _ ≤ (1 + Complex.normSq z) ^ δ :=
            Real.rpow_le_rpow (by positivity) (by linarith) hδ.le
      have hpow : (1 + Complex.normSq z) ^ (-3 : ℝ) =
          (1 + Complex.normSq z) ^ δ / (1 + Complex.normSq z) ^ (δ + 3) := by
        rw [show (-3 : ℝ) = δ - (δ + 3) by ring, Real.rpow_sub (by positivity)]
      calc
        ‖g z‖ = Complex.normSq z ^ (δ - 1) / (1 + Complex.normSq z) ^ (δ + 3) := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          · simp [g, bridgeComplexDensityMajorant, hz0]
          · simp [g, bridgeComplexDensityMajorant, hz0]; positivity
        _ ≤ (1 + Complex.normSq z) ^ δ / (1 + Complex.normSq z) ^ (δ + 3) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (by positivity))
        _ = (1 + Complex.normSq z) ^ (-3 : ℝ) := hpow.symm
        _ = (1 + ‖z‖ ^ 2) ^ (-3 : ℝ) := by rw [Complex.normSq_eq_norm_sq]
  have hg_int : Integrable g volume := by
    have hsplit : Metric.ball (0 : ℂ) 1 ∪ (Metric.ball (0 : ℂ) 1)ᶜ = univ :=
      Set.union_compl_self _
    rw [← integrableOn_univ, ← hsplit]
    exact hnear.union hfar
  have hden_meas : Measurable fun z : ℂ => ENNReal.ofReal ((Complex.normSq z)⁻¹) := by
    fun_prop
  have hden_finite : ∀ᵐ (z : ℂ) ∂volume,
      ENNReal.ofReal ((Complex.normSq z)⁻¹) < ⊤ := by
    filter_upwards with z
    exact ENNReal.ofReal_lt_top
  have hweight : (fun z : ℂ => bridgeComplexMajorant δ z *
      (ENNReal.ofReal ((Complex.normSq z)⁻¹)).toReal) =ᵐ[volume] g := by
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    have hq : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
    dsimp [bridgeComplexMajorant, g, bridgeComplexDensityMajorant]
    simp only [if_neg hz, ENNReal.toReal_ofReal (by positivity : 0 ≤ (Complex.normSq z)⁻¹)]
    have hpow : Complex.normSq z ^ δ * (Complex.normSq z)⁻¹ =
        Complex.normSq z ^ (δ - 1) := by
      calc
        Complex.normSq z ^ δ * (Complex.normSq z)⁻¹ =
            Complex.normSq z ^ δ / Complex.normSq z := by rw [div_eq_mul_inv]
        _ = Complex.normSq z ^ (δ - 1) := by
          rw [Real.rpow_sub hq δ 1, Real.rpow_one]
    rw [div_mul_eq_mul_div, hpow]
  have hmul : Integrable (bridgeComplexMajorant δ)
      (volume.withDensity fun z : ℂ => ENNReal.ofReal ((Complex.normSq z)⁻¹)) :=
    (integrable_withDensity_iff (μ := volume) hden_meas hden_finite).2
      (hg_int.congr hweight.symm)
  simpa [ArtinPrimitiveRoots.A1.Theta.mulHaarC] using hmul

private theorem bridgeComplexMin_bound (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : z ≠ 0) :
    min (Complex.normSq z ^ δ) (Complex.normSq z ^ (-4 : ℝ)) ≤
      2 ^ (δ + 3) * bridgeComplexMajorant δ z := by
  let q : ℝ := Complex.normSq z
  let p : ℝ := δ + 3
  have hqpos : 0 < q := by dsimp [q]; exact Complex.normSq_pos.mpr hz
  have hqnonneg : 0 ≤ q := le_of_lt hqpos
  have hdenpos : 0 < (1 + q) ^ p := Real.rpow_pos_of_pos (by linarith) p
  by_cases hq : q ≤ 1
  · have hden : (1 + q) ^ p ≤ (2 : ℝ) ^ p :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by dsimp [p]; linarith [hδ])
    have hfac : 1 ≤ (2 : ℝ) ^ p / (1 + q) ^ p :=
      (le_div_iff₀ hdenpos).2 (by simpa using hden)
    calc
      min (q ^ δ) (q ^ (-4 : ℝ)) ≤ q ^ δ := min_le_left _ _
      _ = q ^ δ * 1 := by ring
      _ ≤ q ^ δ * ((2 : ℝ) ^ p / (1 + q) ^ p) :=
        mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg hqnonneg δ)
      _ = (2 : ℝ) ^ p * (q ^ δ / (1 + q) ^ p) := by ring
      _ = (2 : ℝ) ^ p * bridgeComplexMajorant δ z := by
        simp [bridgeComplexMajorant, q, p, hz]
  · have hq1 : 1 ≤ q := le_of_not_ge hq
    have hden : (1 + q) ^ p ≤ (2 : ℝ) ^ p * q ^ p := by
      calc
        (1 + q) ^ p ≤ (2 * q) ^ p :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) (by dsimp [p]; linarith [hδ])
        _ = (2 : ℝ) ^ p * q ^ p := Real.mul_rpow (by norm_num) hqnonneg
    have hfac : 1 ≤ ((2 : ℝ) ^ p * q ^ p) / (1 + q) ^ p :=
      (le_div_iff₀ hdenpos).2 (by simpa using hden)
    have hsmallpow : q ^ (-4 : ℝ) ≤ q ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    calc
      min (q ^ δ) (q ^ (-4 : ℝ)) ≤ q ^ (-4 : ℝ) := min_le_right _ _
      _ ≤ q ^ (-3 : ℝ) := hsmallpow
      _ = q ^ (-3 : ℝ) * 1 := by ring
      _ ≤ q ^ (-3 : ℝ) * (((2 : ℝ) ^ p * q ^ p) / (1 + q) ^ p) :=
        mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg hqnonneg _)
      _ = (2 : ℝ) ^ p * (q ^ δ / (1 + q) ^ p) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        calc
          q ^ (-3 : ℝ) * ((2 : ℝ) ^ p * q ^ p * ((1 + q) ^ p)⁻¹) =
              (2 : ℝ) ^ p * (q ^ (-3 : ℝ) * q ^ p) * ((1 + q) ^ p)⁻¹ := by ring
          _ = (2 : ℝ) ^ p * q ^ δ * ((1 + q) ^ p)⁻¹ := by
            rw [← Real.rpow_add hqpos (-3 : ℝ) p]
            dsimp [p]
            congr 2 <;> ring
          _ = (2 : ℝ) ^ p * (q ^ δ / (1 + q) ^ p) := by ring
      _ = (2 : ℝ) ^ p * bridgeComplexMajorant δ z := by
        simp [bridgeComplexMajorant, q, p, hz]

theorem bridgeSheetHypC_radial_bound (δ : ℝ) (hδ : 0 < δ) (f : ℂ → ℂ)
    (hf : ArtinPrimitiveRoots.A1.SheetHypC δ f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ≠ 0,
      ‖f z‖ ≤ C * bridgeComplexMajorant δ z := by
  rcases hf with ⟨hcont, hbounds⟩
  obtain ⟨C, hC⟩ := hbounds 0 4 (by norm_num)
  let C' := max C 0
  refine ⟨C' * 2 ^ (δ + 3), mul_nonneg (le_max_right _ _) (by positivity), ?_⟩
  intro z hz
  have hq : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have hmin := hC z hz
  have hbound : ‖f z‖ ≤ C * min (Complex.normSq z ^ δ) (Complex.normSq z ^ (-4 : ℝ)) := by
    simpa [A1.normDeriv] using hmin
  have hC : C ≤ C' := le_max_left C 0
  have hmin_nonneg : 0 ≤ min (Complex.normSq z ^ δ) (Complex.normSq z ^ (-4 : ℝ)) := by
    exact le_min (Real.rpow_nonneg hq δ) (Real.rpow_nonneg hq _)
  calc
    ‖f z‖ ≤ C' * min (Complex.normSq z ^ δ) (Complex.normSq z ^ (-4 : ℝ)) :=
      hbound.trans (mul_le_mul_of_nonneg_right hC hmin_nonneg)
    _ ≤ C' * (2 ^ (δ + 3) * bridgeComplexMajorant δ z) :=
      mul_le_mul_of_nonneg_left (bridgeComplexMin_bound δ hδ z hz) (le_max_right C 0)
    _ = (C' * 2 ^ (δ + 3)) * bridgeComplexMajorant δ z := by ring

end ArtinPrimitiveRoots.A2
