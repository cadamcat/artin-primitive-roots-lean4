import ArtinPrimitiveRoots.Construction.Proofs.C_TYPEII.UniformTransfer
import ArtinPrimitiveRoots.Construction.Proofs.C_TYPEII.Twisting
import ArtinPrimitiveRoots.Construction.Proofs.C_TYPEII.FourierBounds
import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.TypeII.Rough
import ArtinPrimitiveRoots.Ext.TypeIIInputs
import ArtinPrimitiveRoots.Construction.Proofs.c1.SupportHelpers

namespace ArtinPrimitiveRoots.Proofs.c_typeii_sol

open Classical MeasureTheory Filter
open ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.Rough
open ArtinPrimitiveRoots.Construction

/-- The common bilinear estimate needed after character expansion and before Fourier inversion. -/
def TwistedEstimate (δ γ sMin sMax c₁ c₂ : ℝ) (M K : ℕ) (a : Fin K → ℝ) : Prop :=
  ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ,
      Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
      Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
      ∀ I : Set ℕ, IsNatInterval I →
        I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
      ∀ v : ℝ, |v| ≤ Real.log x → ∀ χM : DirichletCharacter ℂ M,
      ∀ beta : ℕ → ℂ,
        (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers Hn ∧ roughAbove n (roughCutoff x)) →
        (∀ n ∈ dyadicIntegers Hn, ‖beta n‖ ≤ Real.rpow (Real.log x) 2) →
      ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
        ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
          ∑ n ∈ dyadicIntegers Hn,
            (roughCoefficient x γ v m * χM (m : ZMod M)) *
              (beta n * χM (n : ZMod M)) * F (m * n - 1) *
                (markedWeight x K a (1 / 2 : ℝ) (m * n - 1) : ℂ)‖ ≤
          C' * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ)

private structure RoughPoint (ρ γ sMin sMax c₁ c₂ : ℝ) (M : ℕ) where
  x : ℝ
  Hm : ℝ
  Hn : ℝ
  I : Set ℕ
  interval : IsNatInterval I
  m_lower : Real.rpow x ρ ≤ Hm
  n_lower : Real.rpow x ρ ≤ Hn
  product_lower : c₁ * x ≤ Hm * Hn
  product_upper : Hm * Hn ≤ c₂ * x
  window_lower : Real.log Hm / Real.log x ∈ Set.Icc sMin sMax
  window_upper : Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax
  interval_bounds : I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm}
  v : ℝ
  v_bound : |v| ≤ Real.log x
  χM : DirichletCharacter ℂ M

/-- One common threshold and cancellation witness for all one-point rough families. -/
private structure RoughFamilySystem (ρ γ sMin sMax c₁ c₂ : ℝ) (M : ℕ) where
  threshold : ℝ
  threshold_ge_two : 2 ≤ threshold
  family : (P : RoughPoint ρ γ sMin sMax c₁ c₂ M) → threshold ≤ P.x →
    CoefficientFamily ρ 2 c₁ c₂
  start : ∀ P hP, (family P hP).xMin ≤ threshold
  Hm_at : ∀ P hP, (family P hP).Hm P.x = P.Hm
  Hn_at : ∀ P hP, (family P hP).Hn P.x = P.Hn
  interval_at : ∀ P hP, (family P hP).interval P.x = P.I
  alpha_at : ∀ P hP, (family P hP).alpha P.x = fun m =>
    if m ∈ P.I then roughCoefficient P.x γ P.v m * P.χM (m : ZMod M) else 0
  witness : LongCancellationWitness ρ 2 c₁ c₂ threshold
  cancellation : ∀ P hP, HasLongCancellationWith (family P hP) witness

private theorem roughDensity_divisor_bound (γ sMin sMax : ℝ)
    (hγ : 0 < γ) (hγs : γ < sMin) (hs : sMin < sMax) :
    ∃ B x₀ : ℝ, 0 < B ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ w ∈ Set.Icc sMin sMax,
        |ArtinPrimitiveRoots.TypeII.Rough.roughDensity γ w /
          (Real.log x * ArtinPrimitiveRoots.TypeII.roughSieveProduct
            (ArtinPrimitiveRoots.TypeII.roughCutoff x))| ≤ B := by
  obtain ⟨hDcont, _, _⟩ := ArtinPrimitiveRoots.TypeII.Rough.density_regularity
  have hcurve : ContinuousOn (fun w : ℝ => (γ, w)) (Set.Icc sMin sMax) := by
    fun_prop
  have hmaps : Set.MapsTo (fun w : ℝ => (γ, w)) (Set.Icc sMin sMax)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
    intro w hw
    exact ⟨hγ, lt_of_lt_of_le hγs hw.1⟩
  have hD : ContinuousOn (fun w : ℝ => ArtinPrimitiveRoots.TypeII.Rough.roughDensity γ w)
      (Set.Icc sMin sMax) := by
    simpa [ArtinPrimitiveRoots.TypeII.Rough.roughDensity, Function.comp_def] using
      hDcont.comp hcurve hmaps
  obtain ⟨D₀, hD₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  let D : ℝ := max D₀ 1
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hDbound : ∀ w ∈ Set.Icc sMin sMax,
      |ArtinPrimitiveRoots.TypeII.Rough.roughDensity γ w| ≤ D := by
    intro w hw
    have h := hD₀ w hw
    simpa [Real.norm_eq_abs, D] using h.trans (le_max_left D₀ 1)
  let e₀ : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  have he₀ : 0 < e₀ := Real.exp_pos _
  obtain ⟨y₀, hy₀, hmertens⟩ := ArtinPrimitiveRoots.Ext.TypeIIInputs.mertens.2
    (e₀ / 2) (by positivity)
  have hcut : Tendsto ArtinPrimitiveRoots.TypeII.roughCutoff atTop atTop := by
    change Tendsto (fun x : ℝ => Real.exp
      (Real.rpow (Real.log x) (24 / 100 : ℝ))) atTop atTop
    exact Real.tendsto_exp_atTop.comp
      ((tendsto_rpow_atTop (by norm_num : 0 < (24 / 100 : ℝ))).comp
        Real.tendsto_log_atTop)
  have hev : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ y₀ ≤ ArtinPrimitiveRoots.TypeII.roughCutoff x ∧ 1 ≤ Real.log x := by
    exact (eventually_ge_atTop 2).and
      ((hcut.eventually_ge_atTop y₀).and
        (Real.tendsto_log_atTop.eventually_ge_atTop 1))
  obtain ⟨x₀, hx₀⟩ := hev.exists_forall_of_atTop
  refine ⟨2 * D / e₀, x₀, by positivity, (hx₀ x₀ le_rfl).1, ?_⟩
  intro x hx w hw
  have hprops := hx₀ x hx
  have hlogx : 1 ≤ Real.log x := hprops.2.2
  have hlogW : Real.log (ArtinPrimitiveRoots.TypeII.roughCutoff x) =
      Real.rpow (Real.log x) (24 / 100 : ℝ) := by
    simp [ArtinPrimitiveRoots.TypeII.roughCutoff]
  have hlogWpos : 0 < Real.log (ArtinPrimitiveRoots.TypeII.roughCutoff x) := by
    rw [hlogW]
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlogx) _
  have hlogWle : Real.log (ArtinPrimitiveRoots.TypeII.roughCutoff x) ≤ Real.log x := by
    rw [hlogW]
    exact Real.rpow_le_self_of_one_le hlogx (by norm_num)
  have hratio : 1 ≤ Real.log x / Real.log (ArtinPrimitiveRoots.TypeII.roughCutoff x) :=
    (le_div_iff₀ hlogWpos).2 (by simpa using hlogWle)
  have hV := hmertens (ArtinPrimitiveRoots.TypeII.roughCutoff x) hprops.2.1
  have hprod : e₀ / 2 ≤ ArtinPrimitiveRoots.TypeII.roughSieveProduct
      (ArtinPrimitiveRoots.TypeII.roughCutoff x) *
        Real.log (ArtinPrimitiveRoots.TypeII.roughCutoff x) := by
    have h := abs_le.mp hV
    dsimp [e₀] at h ⊢
    linarith
  have hdenEq : Real.log x * ArtinPrimitiveRoots.TypeII.roughSieveProduct
        (ArtinPrimitiveRoots.TypeII.roughCutoff x) =
      (Real.log x / Real.log (ArtinPrimitiveRoots.TypeII.roughCutoff x)) *
        (ArtinPrimitiveRoots.TypeII.roughSieveProduct
          (ArtinPrimitiveRoots.TypeII.roughCutoff x) *
            Real.log (ArtinPrimitiveRoots.TypeII.roughCutoff x)) := by
    field_simp [ne_of_gt hlogWpos]
  have hden : e₀ / 2 ≤ Real.log x * ArtinPrimitiveRoots.TypeII.roughSieveProduct
      (ArtinPrimitiveRoots.TypeII.roughCutoff x) := by
    rw [hdenEq]
    calc
      e₀ / 2 ≤ ArtinPrimitiveRoots.TypeII.roughSieveProduct
          (ArtinPrimitiveRoots.TypeII.roughCutoff x) *
            Real.log (ArtinPrimitiveRoots.TypeII.roughCutoff x) := hprod
      _ ≤ (Real.log x / Real.log (ArtinPrimitiveRoots.TypeII.roughCutoff x)) *
          (ArtinPrimitiveRoots.TypeII.roughSieveProduct
            (ArtinPrimitiveRoots.TypeII.roughCutoff x) *
              Real.log (ArtinPrimitiveRoots.TypeII.roughCutoff x)) :=
        le_mul_of_one_le_left (by linarith) hratio
  have hdenpos : 0 < Real.log x * ArtinPrimitiveRoots.TypeII.roughSieveProduct
      (ArtinPrimitiveRoots.TypeII.roughCutoff x) := by
    linarith
  have hdensity := hDbound w hw
  have hscaled : D ≤ (2 * D / e₀) *
      (Real.log x * ArtinPrimitiveRoots.TypeII.roughSieveProduct
        (ArtinPrimitiveRoots.TypeII.roughCutoff x)) := by
    calc
      D = (2 * D / e₀) * (e₀ / 2) := by field_simp [ne_of_gt he₀]
      _ ≤ (2 * D / e₀) *
          (Real.log x * ArtinPrimitiveRoots.TypeII.roughSieveProduct
            (ArtinPrimitiveRoots.TypeII.roughCutoff x)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
  rw [abs_div, abs_of_pos hdenpos]
  apply (div_le_iff₀ hdenpos).2
  exact le_trans hdensity hscaled

private theorem norm_complex_log_phase (v t : ℝ) :
    ‖Complex.exp (Complex.I * (v : ℂ) * (t : ℂ))‖ = 1 := by
  have he : Complex.I * (v : ℂ) * (t : ℂ) = Complex.I * ((v * t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal]

private theorem roughCoefficient_eq_factor (x γ v : ℝ) (m : ℕ) :
    roughCoefficient x γ v m =
      Complex.exp (Complex.I * v * Real.log (m : ℝ)) *
        ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) := by
  by_cases hr : roughAbove m (roughCutoff x)
  · simp [roughCoefficient, roughIndicator, roughProxy, hr, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_div]
  · simp [roughCoefficient, roughIndicator, roughProxy, hr, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_div]

private theorem roughCoefficient_norm (x γ v : ℝ) (m : ℕ) :
    ‖roughCoefficient x γ v m‖ = |roughIndicator x γ m - roughProxy x γ m| := by
  rw [roughCoefficient_eq_factor, norm_mul, norm_complex_log_phase, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

private theorem coefficient_preparation (γ sMin sMax : ℝ)
    (hγ : 0 < γ) (hγs : γ < sMin) (hs : sMin < sMax) :
    ∃ B T : ℝ, 0 < B ∧ 2 ≤ T ∧ ∀ x : ℝ, T ≤ x →
      roughCutoff x ≤ Real.rpow x γ ∧ B ≤ Real.rpow (Real.log x) 2 ∧
      ∀ Hm : ℝ, 0 < Hm →
        Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
        Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
        ∀ m : ℕ, Hm ≤ (m : ℝ) → (m : ℝ) ≤ 2 * Hm →
          |roughIndicator x γ m - roughProxy x γ m| ≤ B := by
  obtain ⟨Bproxy, xProxy, hBproxy, hxProxy, hProxy⟩ :=
    roughDensity_divisor_bound γ sMin sMax hγ hγs hs
  let B : ℝ := 1 + Bproxy
  have hB : 0 < B := by dsimp [B]; linarith
  have hL₂ : Tendsto (fun x : ℝ => Real.rpow (Real.log x) 2) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (2 : ℝ))).comp Real.tendsto_log_atTop
  have hLcut : Tendsto (fun x : ℝ =>
      Real.rpow (Real.log x) (1 - (24 / 100 : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 - (24 / 100 : ℝ)))).comp
      Real.tendsto_log_atTop
  have hev : ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧ xProxy ≤ x ∧ 1 ≤ Real.log x ∧
      B ≤ Real.rpow (Real.log x) 2 ∧
      γ⁻¹ ≤ Real.rpow (Real.log x) (1 - (24 / 100 : ℝ)) :=
    (eventually_ge_atTop 2).and ((eventually_ge_atTop xProxy).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
        ((hL₂.eventually_ge_atTop B).and (hLcut.eventually_ge_atTop γ⁻¹))))
  obtain ⟨T, hT⟩ := hev.exists_forall_of_atTop
  refine ⟨B, T, hB, (hT T le_rfl).1, ?_⟩
  intro x hx
  obtain ⟨hx2, hxProxy, hL, hBL, hcutpow⟩ := hT x hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL
  have hcutpowpos : 0 < Real.rpow (Real.log x) (24 / 100 : ℝ) :=
    Real.rpow_pos_of_pos hlogpos _
  have hratio : γ⁻¹ ≤ Real.log x / Real.rpow (Real.log x) (24 / 100 : ℝ) := by
    change γ⁻¹ ≤ (Real.log x) ^ (1 - (24 / 100 : ℝ)) at hcutpow
    rw [Real.rpow_sub hlogpos, Real.rpow_one] at hcutpow
    exact hcutpow
  have hcutlog : Real.rpow (Real.log x) (24 / 100 : ℝ) ≤ γ * Real.log x := by
    have hmul := mul_le_mul_of_nonneg_left ((le_div_iff₀ hcutpowpos).mp hratio) hγ.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul] using hmul
  have hcut : roughCutoff x ≤ Real.rpow x γ := by
    calc
      roughCutoff x = Real.exp (Real.rpow (Real.log x) (24 / 100 : ℝ)) := rfl
      _ ≤ Real.exp (γ * Real.log x) := Real.exp_le_exp.mpr hcutlog
      _ = Real.rpow x γ := by
        change Real.exp (γ * Real.log x) = x ^ γ
        rw [Real.rpow_def_of_pos hxpos]
        congr 1
        ring
  refine ⟨hcut, hBL, ?_⟩
  intro Hm hHm hw₁ hw₂ m hm₁ hm₂
  have hmpos : 0 < (m : ℝ) := hHm.trans_le hm₁
  have hwindow : Real.log (m : ℝ) / Real.log x ∈ Set.Icc sMin sMax := by
    constructor
    · exact hw₁.1.trans
        (div_le_div_of_nonneg_right (Real.log_le_log hHm hm₁) hlogpos.le)
    · exact (div_le_div_of_nonneg_right (Real.log_le_log hmpos hm₂) hlogpos.le).trans hw₂.2
  have hIndicator : |roughIndicator x γ m| ≤ 1 := by
    unfold roughIndicator
    split_ifs <;> norm_num
  have hProxyBound : |roughProxy x γ m| ≤ Bproxy := by
    by_cases hr : roughAbove m (roughCutoff x)
    · simpa only [roughProxy, if_pos hr, mul_one] using
        hProxy x hxProxy _ hwindow
    · simp only [roughProxy, if_neg hr, mul_zero, abs_zero]
      exact hBproxy.le
  calc
    |roughIndicator x γ m - roughProxy x γ m| ≤
        |roughIndicator x γ m| + |roughProxy x γ m| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (roughIndicator x γ m) (roughProxy x γ m)
    _ ≤ 1 + Bproxy := add_le_add hIndicator hProxyBound
    _ = B := rfl

private theorem fallback_preparation (ρ c₁ : ℝ) (hρhalf : ρ < 1 / 2) (hc₁ : 0 < c₁) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ y : ℝ, T ≤ y →
      Real.rpow y ρ ≤ c₁ * Real.rpow y (1 - ρ) ∧
      Real.rpow y ρ * (c₁ * Real.rpow y (1 - ρ)) = c₁ * y := by
  have hpower : 0 < 1 - 2 * ρ := by linarith
  have htend : Tendsto (fun y : ℝ => Real.rpow y (1 - 2 * ρ)) atTop atTop :=
    tendsto_rpow_atTop hpower
  obtain ⟨T, hT⟩ := ((eventually_ge_atTop 2).and
    (htend.eventually_ge_atTop c₁⁻¹)).exists_forall_of_atTop
  refine ⟨T, (hT T le_rfl).1, ?_⟩
  intro y hy
  obtain ⟨hy2, hpow⟩ := hT y hy
  have hypos : 0 < y := by linarith
  have hyρ : 0 < Real.rpow y ρ := Real.rpow_pos_of_pos hypos _
  have hratio : c₁⁻¹ ≤ Real.rpow y (1 - ρ) / Real.rpow y ρ := by
    change c₁⁻¹ ≤ y ^ (1 - 2 * ρ) at hpow
    rw [show 1 - 2 * ρ = (1 - ρ) - ρ by ring, Real.rpow_sub hypos] at hpow
    exact hpow
  have hlower : Real.rpow y ρ ≤ c₁ * Real.rpow y (1 - ρ) := by
    have hmul := mul_le_mul_of_nonneg_left ((le_div_iff₀ hyρ).mp hratio) hc₁.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hc₁.ne', one_mul] using hmul
  refine ⟨hlower, ?_⟩
  change y ^ ρ * (c₁ * y ^ (1 - ρ)) = c₁ * y
  calc
    _ = c₁ * (y ^ ρ * y ^ (1 - ρ)) := by ring
    _ = c₁ * y ^ (ρ + (1 - ρ)) := by rw [Real.rpow_add hypos]
    _ = c₁ * y := by rw [show ρ + (1 - ρ) = 1 by ring, Real.rpow_one]

private noncomputable def roughPointFamily
    {ρ γ sMin sMax c₁ c₂ : ℝ} {M : ℕ} (B T : ℝ) (hT : 2 ≤ T)
    (hbase : ∀ y : ℝ, T ≤ y → Real.rpow y ρ ≤ c₁ * Real.rpow y (1 - ρ) ∧
      Real.rpow y ρ * (c₁ * Real.rpow y (1 - ρ)) = c₁ * y)
    (hprep : ∀ x : ℝ, T ≤ x →
      roughCutoff x ≤ Real.rpow x γ ∧ B ≤ Real.rpow (Real.log x) 2 ∧
      ∀ Hm : ℝ, 0 < Hm →
        Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
        Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
        ∀ m : ℕ, Hm ≤ (m : ℝ) → (m : ℝ) ≤ 2 * Hm →
          |roughIndicator x γ m - roughProxy x γ m| ≤ B)
    (hc₁₂ : c₁ ≤ c₂) (P : RoughPoint ρ γ sMin sMax c₁ c₂ M) (hP : T ≤ P.x) :
    CoefficientFamily ρ 2 c₁ c₂ := by
  classical
  refine {
    xMin := T, xMin_ge_two := hT
    Hm := fun y => if y = P.x then P.Hm else Real.rpow y ρ
    Hn := fun y => if y = P.x then P.Hn else c₁ * Real.rpow y (1 - ρ)
    interval := fun y => if y = P.x then P.I else ∅
    alpha := fun y m => if y = P.x then
      (if m ∈ P.I then roughCoefficient P.x γ P.v m * P.χM (m : ZMod M) else 0) else 0
    interval_property := ?_
    scales := ?_
    interval_bounds := ?_
    rough_support := ?_
    coefficient_bound := ?_ }
  · intro y
    by_cases hy : y = P.x
    · simpa only [if_pos hy] using P.interval
    · intro m n k hm hn hk₁ hk₂
      simp only [if_neg hy, Set.mem_empty_iff_false] at hm
  · intro y hyT
    by_cases hy : y = P.x
    · simpa only [if_pos hy, hy, ite_true] using
        (show Real.rpow P.x ρ ≤ P.Hm ∧ Real.rpow P.x ρ ≤ P.Hn ∧
          c₁ * P.x ≤ P.Hm * P.Hn ∧ P.Hm * P.Hn ≤ c₂ * P.x from
          ⟨P.m_lower, P.n_lower, P.product_lower, P.product_upper⟩)
    · obtain ⟨hlower, hprod⟩ := hbase y hyT
      simp only [if_neg hy]
      refine ⟨le_rfl, hlower, by rw [hprod], ?_⟩
      rw [hprod]
      exact mul_le_mul_of_nonneg_right hc₁₂ (by linarith [hT.trans hyT])
  · intro y hyT m hm
    by_cases hy : y = P.x
    · have hmI : m ∈ P.I := by simpa only [if_pos hy] using hm
      simpa only [if_pos hy, Set.mem_setOf_eq] using P.interval_bounds hmI
    · simp only [if_neg hy, Set.mem_empty_iff_false] at hm
  · intro y hyT m hm
    by_cases hy : y = P.x
    · subst y
      simp only [if_pos rfl, ite_true] at hm ⊢
      have hmI : m ∈ P.I := by
        by_contra hnot
        exact hm (by simp only [if_neg hnot])
      rw [if_pos hmI] at hm
      refine ⟨hmI, ?_⟩
      by_contra hnot
      have hcut := (hprep P.x hP).1
      have hnotBig : ¬ roughAbove m (Real.rpow P.x γ) := by
        intro hbig
        apply hnot
        intro p hp hdiv
        exact lt_of_le_of_lt hcut (hbig p hp hdiv)
      apply hm
      simp only [roughCoefficient, if_neg hnotBig, if_neg hnot, mul_zero, sub_zero,
        Complex.ofReal_zero, zero_mul]
    · simp only [if_neg hy] at hm
      exact (hm rfl).elim
  · intro y hyT m hm
    by_cases hy : y = P.x
    · subst y
      simp only [if_pos rfl, ite_true] at hm ⊢
      rw [if_pos hm]
      have hxpos : 0 < P.x := by linarith [hT.trans hP]
      have hHm : 0 < P.Hm := (Real.rpow_pos_of_pos hxpos ρ).trans_le P.m_lower
      have hbox := P.interval_bounds hm
      have hdiff := (hprep P.x hP).2.2 P.Hm hHm P.window_lower P.window_upper m hbox.1 hbox.2
      calc
        ‖roughCoefficient P.x γ P.v m * P.χM (m : ZMod M)‖ =
            ‖roughCoefficient P.x γ P.v m‖ * ‖P.χM (m : ZMod M)‖ := norm_mul _ _
        _ ≤ ‖roughCoefficient P.x γ P.v m‖ * 1 :=
          mul_le_mul_of_nonneg_left (P.χM.norm_le_one _) (norm_nonneg _)
        _ = |roughIndicator P.x γ m - roughProxy P.x γ m| := by
          rw [mul_one, roughCoefficient_norm]
        _ ≤ B := hdiff
        _ ≤ Real.rpow (Real.log P.x) 2 := (hprep P.x hP).2.1
    · simp only [if_neg hy, Set.mem_empty_iff_false] at hm

private def RoughPointCancellation
    (ρ γ sMin sMax c₁ c₂ : ℝ) (M : ℕ) (A₀ B A C U : ℝ) : Prop :=
  ∀ P : RoughPoint ρ γ sMin sMax c₁ c₂ M, U ≤ P.x →
    ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log P.x) A₀ →
      ∀ χk : DirichletCharacter ℂ k, ∀ t : ℝ,
        |t| ≤ 2 * (P.Hm * P.Hn) * Real.rpow (Real.log P.x) B →
          ‖∑ m ∈ (dyadicIntegers P.Hm).filter (fun m => m ∈ P.I),
            (roughCoefficient P.x γ P.v m * P.χM (m : ZMod M)) *
              χk (m : ZMod k) * Complex.exp (Complex.I * t * Real.log (m : ℝ))‖ / P.Hm ≤
            C * Real.rpow (Real.log P.x) (-A)

private theorem makeRoughFamilySystem
    (ρ γ sMin sMax c₁ c₂ : ℝ) (M : ℕ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hγ : 0 < γ)
    (hγs : γ < sMin) (hs : sMin < sMax) (hsMax : sMax < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁₂ : c₁ ≤ c₂) (hM : 0 < M) :
    Nonempty (RoughFamilySystem ρ γ sMin sMax c₁ c₂ M) := by
  obtain ⟨Bcoef, Tcoef, hBcoef, hTcoef, hCoef⟩ :=
    coefficient_preparation γ sMin sMax hγ hγs hs
  obtain ⟨Tscale, hTscale, hScale⟩ := fallback_preparation ρ c₁ hρhalf hc₁
  let T : ℝ := max Tcoef Tscale
  have hT : 2 ≤ T := hTcoef.trans (le_max_left _ _)
  have hbase : ∀ y : ℝ, T ≤ y → Real.rpow y ρ ≤ c₁ * Real.rpow y (1 - ρ) ∧
      Real.rpow y ρ * (c₁ * Real.rpow y (1 - ρ)) = c₁ * y :=
    fun y hy => hScale y ((le_max_right _ _).trans hy)
  have hprep : ∀ x : ℝ, T ≤ x →
      roughCutoff x ≤ Real.rpow x γ ∧ Bcoef ≤ Real.rpow (Real.log x) 2 ∧
      ∀ Hm : ℝ, 0 < Hm →
        Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
        Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
        ∀ m : ℕ, Hm ≤ (m : ℝ) → (m : ℝ) ≤ 2 * Hm →
          |roughIndicator x γ m - roughProxy x γ m| ≤ Bcoef :=
    fun x hx => hCoef x ((le_max_left _ _).trans hx)
  let families := fun (P : RoughPoint ρ γ sMin sMax c₁ c₂ M) (hP : T ≤ P.x) =>
    roughPointFamily Bcoef T hT hbase hprep hc₁₂ P hP
  have hcommon : ∀ A₀ B A : ℝ, ∃ C U : ℝ, 0 < C ∧ T ≤ U ∧
      (0 < A₀ → 0 < B → 0 < A →
        RoughPointCancellation ρ γ sMin sMax c₁ c₂ M A₀ B A C U) := by
    intro A₀ B A
    by_cases hp : 0 < A₀ ∧ 0 < B ∧ 0 < A
    · obtain ⟨C, U, hC, hU, hCancel⟩ :=
        twisted_rough_long_cancellation ρ γ sMin sMax c₂ M
          hρ hγ hγs hs hsMax hc₂ hM A₀ B A hp.1 hp.2.1 hp.2.2
      refine ⟨C, max T U, hC, le_max_left _ _, ?_⟩
      intro hA₀ hB hA P hP k hk hkbound χk t ht
      exact hCancel P.x ((le_max_right _ _).trans hP) P.Hm P.Hn
        P.m_lower P.n_lower P.product_upper P.window_lower P.window_upper
        P.I P.interval P.interval_bounds P.v P.v_bound P.χM k hk hkbound χk t ht
    · refine ⟨1, T, by norm_num, le_rfl, ?_⟩
      intro hA₀ hB hA
      exact (hp ⟨hA₀, hB, hA⟩).elim
  choose constants thresholds hpositive hthreshold hcancellation using hcommon
  let W : LongCancellationWitness ρ 2 c₁ c₂ T := {
    constant := constants
    threshold := thresholds
    positive := fun A₀ B A _ _ _ => hpositive A₀ B A
    threshold_ge_base := fun A₀ B A _ _ _ => hthreshold A₀ B A }
  refine ⟨{
    threshold := T, threshold_ge_two := hT, family := families
    start := ?_, Hm_at := ?_, Hn_at := ?_, interval_at := ?_, alpha_at := ?_
    witness := W, cancellation := ?_ }⟩
  · intro P hP
    exact le_rfl
  · intro P hP
    simp only [families, roughPointFamily, if_pos rfl, ite_true]
  · intro P hP
    simp only [families, roughPointFamily, if_pos rfl, ite_true]
  · intro P hP
    simp only [families, roughPointFamily, if_pos rfl, ite_true]
  · intro P hP
    funext m
    simp only [families, roughPointFamily, if_pos rfl, ite_true]
  · intro P hP A₀ B A hA₀ hB hA y hy k hk hkbound χk t ht
    by_cases hyP : y = P.x
    · subst y
      have hfrequency : |t| ≤ 2 * (P.Hm * P.Hn) * Real.rpow (Real.log P.x) B := by
        simpa only [families, roughPointFamily, if_pos rfl, ite_true] using ht
      have hsource := hcancellation A₀ B A hA₀ hB hA P hy k hk hkbound χk t hfrequency
      have hsum :
          (∑ m ∈ familyTerms (families P hP) P.x,
            (families P hP).alpha P.x m * χk (m : ZMod k) *
              Complex.exp (Complex.I * t * Real.log (m : ℝ))) =
          ∑ m ∈ (dyadicIntegers P.Hm).filter (fun m => m ∈ P.I),
            (roughCoefficient P.x γ P.v m * P.χM (m : ZMod M)) * χk (m : ZMod k) *
              Complex.exp (Complex.I * t * Real.log (m : ℝ)) := by
        simp only [familyTerms, families, roughPointFamily, if_pos rfl, ite_true]
        apply Finset.sum_congr rfl
        intro m hm
        have hmI := (Finset.mem_filter.mp hm).2
        rw [if_pos hmI]
      rw [hsum]
      simpa only [W, families, roughPointFamily, if_pos rfl, ite_true] using hsource
    · have hsum :
          (∑ m ∈ familyTerms (families P hP) y,
            (families P hP).alpha y m * χk (m : ZMod k) *
              Complex.exp (Complex.I * t * Real.log (m : ℝ))) = 0 := by
        simp [familyTerms, families, roughPointFamily, hyP]
      rw [hsum, norm_zero, zero_div]
      have hy2 : 2 ≤ y := hT.trans ((hthreshold A₀ B A).trans hy)
      exact mul_nonneg (hpositive A₀ B A).le
        (Real.rpow_pos_of_pos (Real.log_pos (by linarith [hy2])) (-A)).le

/-- Character twisting and common cancellation witnesses preserve the transfer's common K₀. -/
theorem twisted_rough_type_ii
    (δ γ sMin sMax c₁ c₂ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hγs : γ < sMin) (hs : sMin < sMax) (hsMax : sMax < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁₂ : c₁ ≤ c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ M : ℕ, 0 < M →
      ∀ a : Fin K → ℝ, ValidBands K a → TwistedEstimate δ γ sMin sMax c₁ c₂ M K a := by
  let ρ : ℝ := min δ (1 - sMax) / 2
  have hmin : 0 < min δ (1 - sMax) := lt_min hδ (by linarith)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρδ : ρ ≤ δ := by
    dsimp [ρ]
    nlinarith [min_le_left δ (1 - sMax)]
  have hsMaxpos : 0 < sMax := lt_trans hγ (lt_trans hγs hs)
  have hρhalf : ρ < 1 / 2 := by
    dsimp [ρ]
    nlinarith [min_le_right δ (1 - sMax)]
  obtain ⟨K₀, hTransfer⟩ := marked_coefficient_transfer_uniform ρ 2 6 (1 / 2 : ℝ) c₁ c₂
    hρ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc₁ hc₂ hc₁₂
  refine ⟨K₀, ?_⟩
  intro K hK M hM a ha
  obtain ⟨S⟩ := makeRoughFamilySystem ρ γ sMin sMax c₁ c₂ M
    hρ hρhalf hγ hγs hs hsMax hc₁ hc₂ hc₁₂ hM
  obtain ⟨C', x₀, hC', hx₀, hBound⟩ :=
    hTransfer K hK a ha S.threshold S.threshold_ge_two S.witness
  refine ⟨C', x₀, hC', S.threshold_ge_two.trans hx₀, ?_⟩
  intro x hx Hm Hn hm hn hprod₁ hprod₂ hw₁ hw₂ I hI hbox v hv χM beta hb₀ hb₁ F hF
  have hx2 : 2 ≤ x := S.threshold_ge_two.trans (hx₀.trans hx)
  have hxone : 1 ≤ x := by linarith
  let P : RoughPoint ρ γ sMin sMax c₁ c₂ M := {
    x := x, Hm := Hm, Hn := Hn, I := I, interval := hI
    m_lower := (Real.rpow_le_rpow_of_exponent_le hxone hρδ).trans hm
    n_lower := (Real.rpow_le_rpow_of_exponent_le hxone hρδ).trans hn
    product_lower := hprod₁, product_upper := hprod₂
    window_lower := hw₁, window_upper := hw₂, interval_bounds := hbox
    v := v, v_bound := hv, χM := χM }
  have hP : S.threshold ≤ P.x := hx₀.trans hx
  let family := S.family P hP
  have hHm : family.Hm x = Hm := S.Hm_at P hP
  have hHn : family.Hn x = Hn := S.Hn_at P hP
  have hIeq : family.interval x = I := S.interval_at P hP
  have hα : family.alpha x = fun m =>
      if m ∈ I then roughCoefficient x γ v m * χM (m : ZMod M) else 0 := S.alpha_at P hP
  let β : ℕ → ℂ := fun n => beta n * χM (n : ZMod M)
  have hβ₀ : ∀ n, β n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
      roughAbove n (roughCutoff x) := by
    intro n hn
    rw [hHn]
    apply hb₀ n
    intro hz
    apply hn
    simp [β, hz]
  have hβ₁ : ∀ n ∈ dyadicIntegers (family.Hn x),
      ‖β n‖ ≤ Real.rpow (Real.log x) 2 := by
    intro n hn
    rw [hHn] at hn
    calc
      ‖β n‖ = ‖beta n‖ * ‖χM (n : ZMod M)‖ := norm_mul _ _
      _ ≤ ‖beta n‖ * 1 := mul_le_mul_of_nonneg_left (χM.norm_le_one _) (norm_nonneg _)
      _ ≤ Real.rpow (Real.log x) 2 := by simpa only [mul_one] using hb₁ n hn
  have hbilinear := hBound family (S.start P hP) (S.cancellation P hP)
    x hx β hβ₀ hβ₁ F hF
  have hsum : markedBilinearSum x K a (1 / 2 : ℝ) F
      (family.Hm x) (family.Hn x) (family.interval x) (family.alpha x) β =
      ∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
        ∑ n ∈ dyadicIntegers Hn,
          (roughCoefficient x γ v m * χM (m : ZMod M)) *
            (beta n * χM (n : ZMod M)) * F (m * n - 1) *
              (markedWeight x K a (1 / 2 : ℝ) (m * n - 1) : ℂ) := by
    unfold markedBilinearSum
    rw [hHm, hHn, hIeq, hα]
    apply Finset.sum_congr rfl
    intro m hm
    have hmI := (Finset.mem_filter.mp hm).2
    simp only [if_pos hmI, β]
  rw [hsum, hHm, hHn] at hbilinear
  exact hbilinear

private theorem dyadic_card_le_three (H : ℝ) (hH : 1 ≤ H) :
    ((dyadicIntegers H).card : ℝ) ≤ 3 * H := by
  have hNat : (dyadicIntegers H).card ≤ ⌊2 * H⌋₊ + 1 := by
    dsimp [dyadicIntegers]
    calc
      _ ≤ (Finset.range (⌊2 * H⌋₊ + 1)).card := Finset.card_filter_le _ _
      _ = _ := by simp
  have hcast : ((dyadicIntegers H).card : ℝ) ≤ (⌊2 * H⌋₊ : ℝ) + 1 := by
    exact_mod_cast hNat
  have hfloor : (⌊2 * H⌋₊ : ℝ) ≤ 2 * H := Nat.floor_le (by positivity)
  linarith

/-- Fourier inversion and character orthogonality turn the common twisted estimate into
an estimate for the actual construction weight. -/
theorem fourier_progression
    (δ γ sMin sMax c₁ c₂ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hγs : γ < sMin) (hs : sMin < sMax) (hsMax : sMax < 1)
    (M c K : ℕ) (u : ℤ) (a : Fin K → ℝ) (ha : ValidBands K a)
    (hM : 0 < M) (hc : c = 2 ∨ c = 4) (hu : Int.gcd u M = 1)
    (Ψ : ℝ → ℝ) (hΨ₀ : ∀ y, 0 ≤ Ψ y) (hΨ₁ : ∀ y, Ψ y ≤ 1)
    (hsupp : Function.support Ψ ⊆ Set.Ioo 1 2)
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (htw : TwistedEstimate δ γ sMin sMax c₁ c₂ M K a) :
    ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Hm Hn : ℝ,
              Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
              c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
              Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
              Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
              ∀ I : Set ℕ, IsNatInterval I →
                I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
                ∀ b : ℕ → ℂ,
                  (∀ n, b n ≠ 0 → n ∈ dyadicIntegers Hn ∧
                    roughAbove n (roughCutoff x)) →
                  (∀ n ∈ dyadicIntegers Hn, ‖b n‖ ≤ 1) →
                  ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
                    ∑ n ∈ dyadicIntegers Hn,
                      ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) *
                        b n * (conWeight x M c u K a Ψ (m * n) : ℂ)‖ ≤
                    C₀ * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ) := by
  obtain ⟨CType, XType, hCType, hXType, hType⟩ := htw
  obtain ⟨Bcoef, XCoef, hBcoef, hXCoef, hCoef⟩ :=
    coefficient_preparation γ sMin sMax hγ hγs hs
  obtain ⟨XMarked, hXMarked, hMass⟩ := bandMass_lower_all ha
  obtain ⟨CFT, hCFT, hFT⟩ := log_fourier_bilinear_bound Ψ hsmooth hsupp
  let Bmarked : ℝ := (4 / Real.log 2) ^ K
  have hBmarked : 0 ≤ Bmarked := by dsimp [Bmarked]; positivity
  let Rcard : ℝ := (Fintype.card (DirichletCharacter ℂ M) : ℝ)
  have hRcard : 0 ≤ Rcard := by dsimp [Rcard]; positivity
  let D : ℝ := CFT * (Rcard * CType + 9 * Rcard * Bcoef * Bmarked)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let x₀ : ℝ := max XType (max XCoef (max XMarked (Real.exp 1)))
  have hx₀ : 2 ≤ x₀ := hXType.trans (le_max_left _ _)
  refine ⟨D + 1, x₀, by positivity, hx₀, ?_⟩
  intro x hx Hm Hn hm hn hprod₁ hprod₂ hw₁ hw₂ I hI hbox b hb₀ hb₁
  have hxType : XType ≤ x := (le_max_left _ _).trans hx
  have hxCoef : XCoef ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxMarked : XMarked ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hxExp : Real.exp 1 ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hx2 : 2 ≤ x := hx₀.trans hx
  have hxgt : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxExp
    simpa using h
  have hLpos : 0 < Real.log x := by linarith
  have hPow : 0 ≤ Real.rpow (Real.log x) (-6 : ℝ) :=
    (Real.rpow_pos_of_pos hLpos _).le
  have hScal : 1 < Real.rpow x δ := Real.one_lt_rpow hxgt hδ
  have hHmgt : 1 < Hm := hScal.trans_le hm
  have hHngt : 1 < Hn := hScal.trans_le hn
  have hHmpos : 0 < Hm := by linarith
  have hHnpos : 0 < Hn := by linarith
  have hP : 0 < Hm * Hn := mul_pos hHmpos hHnpos
  have hcne : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  have hφ : 1 ≤ (Nat.totient M : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.totient_pos.mpr hM)
  have hRecip : ‖(1 / (Nat.totient M : ℂ))‖ ≤ 1 := by
    rw [norm_div, norm_one, Complex.norm_natCast]
    exact (div_le_one (by linarith : 0 < (Nat.totient M : ℝ))).2 hφ
  have huUnit : IsUnit (u : ZMod M) :=
    (ZMod.coe_int_isUnit_iff_isCoprime u M).mpr
      ((Int.isCoprime_iff_gcd_eq_one.mpr hu).symm)
  let Dm : Finset ℕ := (dyadicIntegers Hm).filter (fun m => m ∈ I)
  let Dn : Finset ℕ := dyadicIntegers Hn
  have hDm (m : ℕ) (hmm : m ∈ Dm) : 1 < m := by
    have hmb : Hm ≤ (m : ℝ) :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hmm).1).2.1
    exact_mod_cast hHmgt.trans_le hmb
  have hDn (n : ℕ) (hnn : n ∈ Dn) : 1 < n := by
    have hnb : Hn ≤ (n : ℝ) := (Finset.mem_filter.mp hnn).2.1
    exact_mod_cast hHngt.trans_le hnb
  let F : ℕ → ℂ := fun h => (conFactor x c K a h : ℂ)
  have hF : IsMarkedInvariant x K a F := by
    constructor
    · intro h
      dsimp [F, conFactor]
      split_ifs <;> norm_num
    · intro p h hp hprime
      exact congrArg (fun y : ℝ => (y : ℂ)) (conFactor_mul_marked hcne hp hprime)
  let β : ℝ → ℕ → ℂ := fun v n =>
    b n * Complex.exp (Complex.I * v * Real.log (n : ℝ))
  have hβ₀ (v : ℝ) : ∀ n, β v n ≠ 0 →
      n ∈ dyadicIntegers Hn ∧ roughAbove n (roughCutoff x) := by
    intro n hne
    apply hb₀ n
    intro hz
    apply hne
    simp [β, hz]
  have hβ₁ (v : ℝ) : ∀ n ∈ Dn, ‖β v n‖ ≤ 1 := by
    intro n hnn
    simpa only [β, norm_mul, norm_complex_log_phase, mul_one] using hb₁ n hnn
  have hβ₂ (v : ℝ) : ∀ n ∈ dyadicIntegers Hn,
      ‖β v n‖ ≤ Real.rpow (Real.log x) 2 := by
    intro n hnn
    exact (hβ₁ v n hnn).trans (Real.one_le_rpow hL (by norm_num))
  have hMarked (h : ℕ) : ‖(markedWeight x K a (1 / 2 : ℝ) h : ℂ)‖ ≤ Bmarked := by
    have h := markedWeight_nonneg_le (hMass x hxMarked) (h := h)
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have hα (v : ℝ) (m : ℕ) (hmm : m ∈ Dm) : ‖roughCoefficient x γ v m‖ ≤ Bcoef := by
    have hmb := (Finset.mem_filter.mp (Finset.mem_filter.mp hmm).1).2
    rw [roughCoefficient_norm]
    exact (hCoef x hxCoef).2.2 Hm hHmpos hw₁ hw₂ m hmb.1 hmb.2
  let Q : ℝ → DirichletCharacter ℂ M → ℂ := fun v χ =>
    ∑ m ∈ Dm, ∑ n ∈ Dn,
      (roughCoefficient x γ v m * χ (m : ZMod M)) *
        (β v n * χ (n : ZMod M)) * F (m * n - 1) *
        (markedWeight x K a (1 / 2 : ℝ) (m * n - 1) : ℂ)
  let S : ℝ → ℂ := progressionBilinear x γ M c K u a Dm Dn b
  have hSeq (v : ℝ) : S v =
      (1 / (Nat.totient M : ℂ)) * ∑ χ : DirichletCharacter ℂ M,
        star (χ (u : ZMod M)) * Q v χ := rfl
  have hQnear (v : ℝ) (hv : |v| ≤ Real.log x) (χ : DirichletCharacter ℂ M) :
      ‖Q v χ‖ ≤ CType * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ) := by
    exact hType x hxType Hm Hn hm hn hprod₁ hprod₂ hw₁ hw₂ I hI hbox
      v hv χ (β v) (hβ₀ v) (hβ₂ v) F hF
  have hSnear (v : ℝ) (hv : |v| ≤ Real.log x) :
      ‖S v‖ ≤ (Rcard * CType * (Hm * Hn)) * Real.rpow (Real.log x) (-6 : ℝ) := by
    rw [hSeq, norm_mul]
    calc
      _ ≤ 1 * ‖∑ χ : DirichletCharacter ℂ M, star (χ (u : ZMod M)) * Q v χ‖ :=
        mul_le_mul_of_nonneg_right hRecip (norm_nonneg _)
      _ = ‖∑ χ : DirichletCharacter ℂ M, star (χ (u : ZMod M)) * Q v χ‖ := by ring
      _ ≤ ∑ χ : DirichletCharacter ℂ M, ‖star (χ (u : ZMod M)) * Q v χ‖ :=
        norm_sum_le _ _
      _ ≤ ∑ χ : DirichletCharacter ℂ M,
          CType * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ) := by
        apply Finset.sum_le_sum
        intro χ hχ
        rw [norm_mul, norm_star]
        calc
          _ ≤ 1 * (CType * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ)) :=
            mul_le_mul (χ.norm_le_one _) (hQnear v hv χ) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      _ = _ := by simp [Rcard, mul_assoc]
  have hTerm (v : ℝ) (χ : DirichletCharacter ℂ M)
      (m : ℕ) (hmm : m ∈ Dm) (n : ℕ) (hnn : n ∈ Dn) :
      ‖(roughCoefficient x γ v m * χ (m : ZMod M)) *
          (β v n * χ (n : ZMod M)) * F (m * n - 1) *
          (markedWeight x K a (1 / 2 : ℝ) (m * n - 1) : ℂ)‖ ≤ Bcoef * Bmarked := by
    simp only [norm_mul]
    calc
      _ ≤ (Bcoef * 1) * (1 * 1) * 1 * Bmarked := by
        gcongr
        · exact hα v m hmm
        · exact χ.norm_le_one _
        · exact hβ₁ v n hnn
        · exact χ.norm_le_one _
        · exact hF.1 _
        · exact hMarked _
      _ = _ := by ring
  have hCardm : (Dm.card : ℝ) ≤ 3 * Hm := by
    have hc : Dm.card ≤ (dyadicIntegers Hm).card := Finset.card_filter_le _ _
    have hc' : (Dm.card : ℝ) ≤ ((dyadicIntegers Hm).card : ℝ) := by exact_mod_cast hc
    exact hc'.trans (dyadic_card_le_three Hm hHmgt.le)
  have hCardn : (Dn.card : ℝ) ≤ 3 * Hn := dyadic_card_le_three Hn hHngt.le
  have hQglobal (v : ℝ) (χ : DirichletCharacter ℂ M) :
      ‖Q v χ‖ ≤ 9 * Bcoef * Bmarked * (Hm * Hn) := by
    calc
      _ ≤ ∑ m ∈ Dm, ∑ n ∈ Dn, Bcoef * Bmarked := by
        dsimp [Q]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro m hmm
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun n hnn => hTerm v χ m hmm n hnn)
      _ = (Dm.card : ℝ) * (Dn.card : ℝ) * Bcoef * Bmarked := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ (3 * Hm) * (3 * Hn) * Bcoef * Bmarked := by gcongr
      _ = _ := by ring
  have hSglobal (v : ℝ) : ‖S v‖ ≤
      (9 * Rcard * Bcoef * Bmarked) * (Hm * Hn) := by
    rw [hSeq, norm_mul]
    calc
      _ ≤ 1 * ‖∑ χ : DirichletCharacter ℂ M, star (χ (u : ZMod M)) * Q v χ‖ :=
        mul_le_mul_of_nonneg_right hRecip (norm_nonneg _)
      _ = ‖∑ χ : DirichletCharacter ℂ M, star (χ (u : ZMod M)) * Q v χ‖ := by ring
      _ ≤ ∑ χ : DirichletCharacter ℂ M, ‖star (χ (u : ZMod M)) * Q v χ‖ :=
        norm_sum_le _ _
      _ ≤ ∑ χ : DirichletCharacter ℂ M, 9 * Bcoef * Bmarked * (Hm * Hn) := by
        apply Finset.sum_le_sum
        intro χ hχ
        rw [norm_mul, norm_star]
        calc
          _ ≤ 1 * (9 * Bcoef * Bmarked * (Hm * Hn)) :=
            mul_le_mul (χ.norm_le_one _) (hQglobal v χ) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      _ = _ := by simp [Rcard]; ring
  have hαcont (m : ℕ) : Continuous (fun v : ℝ => roughCoefficient x γ v m) := by
    dsimp [roughCoefficient]
    fun_prop
  have hβcont (n : ℕ) : Continuous (fun v : ℝ => β v n) := by
    dsimp [β]
    fun_prop
  have hQcont (χ : DirichletCharacter ℂ M) : Continuous (fun v : ℝ => Q v χ) := by
    apply continuous_finsetSum Dm
    intro m hmm
    apply continuous_finsetSum Dn
    intro n hnn
    exact ((((hαcont m).mul continuous_const).mul
      ((hβcont n).mul continuous_const)).mul continuous_const).mul continuous_const
  have hScont : Continuous S := by
    have heq : S = fun v => (1 / (Nat.totient M : ℂ)) *
        ∑ χ : DirichletCharacter ℂ M, star (χ (u : ZMod M)) * Q v χ := by
      funext v
      exact hSeq v
    rw [heq]
    apply continuous_const.mul
    apply continuous_finsetSum Finset.univ
    intro χ hχ
    exact continuous_const.mul (hQcont χ)
  have hIntegrated := hFT (Real.log x) hL x
    (Rcard * CType * (Hm * Hn)) ((9 * Rcard * Bcoef * Bmarked) * (Hm * Hn))
    (by positivity) (by positivity) S hScont hSglobal hSnear
  have hIdentity := progression_fourier_identity x γ M c K u a hxpos hM huUnit
    Ψ hsupp hsmooth Dm Dn hDm hDn b
  rw [hIdentity]
  calc
    _ ≤ CFT * ((Rcard * CType * (Hm * Hn)) +
          ((9 * Rcard * Bcoef * Bmarked) * (Hm * Hn))) *
          Real.rpow (Real.log x) (-6 : ℝ) := hIntegrated
    _ = D * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ) := by dsimp [D]; ring
    _ ≤ (D + 1) * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hPow
      exact mul_le_mul_of_nonneg_right (by linarith) hP.le


theorem construction_type_ii
    (δ γ sMin sMax c₁ c₂ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hγs : γ < sMin) (hs : sMin < sMax) (hsMax : sMax < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁₂ : c₁ ≤ c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ M c : ℕ, ∀ u : ℤ,
      ∀ a : Fin K → ℝ, ValidBands K a →
      0 < M → 8 ∣ M → (c = 2 ∨ c = 4) → c ∣ M →
      Int.gcd u M = 1 → (c : ℤ) ∣ u - 1 →
      Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1 →
      ∀ Ψ : ℝ → ℝ, (∀ y, 0 ≤ Ψ y) → (∀ y, Ψ y ≤ 1) →
        Function.support Ψ ⊆ Set.Ioo 1 2 →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → 0 < ∫ y in (1 : ℝ)..2, Ψ y →
        ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Hm Hn : ℝ,
              Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
              c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
              Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
              Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
              ∀ I : Set ℕ, IsNatInterval I →
                I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
                ∀ b : ℕ → ℂ,
                  (∀ n, b n ≠ 0 → n ∈ dyadicIntegers Hn ∧
                    roughAbove n (roughCutoff x)) →
                  (∀ n ∈ dyadicIntegers Hn, ‖b n‖ ≤ 1) →
                  ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
                    ∑ n ∈ dyadicIntegers Hn,
                      ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) *
                        b n * (conWeight x M c u K a Ψ (m * n) : ℂ)‖ ≤
                    C₀ * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ) := by
  obtain ⟨K₀, htw⟩ := twisted_rough_type_ii δ γ sMin sMax c₁ c₂
    hδ hγ hγs hs hsMax hc₁ hc₂ hc₁₂
  refine ⟨K₀, ?_⟩
  intro K hK M c u a ha hM hM8 hc hcM hu hcu hcu' Ψ hΨ₀ hΨ₁ hsupp hsmooth hint
  exact fourier_progression δ γ sMin sMax c₁ c₂ hδ hγ hγs hs hsMax M c K u a ha hM hc hu
    Ψ hΨ₀ hΨ₁ hsupp hsmooth (htw K hK M hM a ha)

end ArtinPrimitiveRoots.Proofs.c_typeii_sol
