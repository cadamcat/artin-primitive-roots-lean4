import ArtinPrimitiveRoots.Theta.LocalInt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_sheets

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]

/-- Normalized additive mass of a local ball at a realized positive radius. -/
theorem finite_ball_mass {v : FinPlace F} (μ : LocHaar v) (y : (v.adicCompletion F)ˣ) :
    μ.μ.real (Metric.closedBall (0 : v.adicCompletion F) (absFin v y)) = absFin v y := by
  let K := v.adicCompletion F
  let B := Metric.closedBall (0 : K) (absFin v y)
  let O := Metric.closedBall (0 : K) 1
  have hO : O = (v.adicCompletionIntegers F : Set K) :=
    (Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)).symm
  have hnorm : 0 < ‖(y : K)‖ := norm_pos_iff.mpr y.ne_zero
  have hpre (x : K) : (y : K) * x ∈ B ↔ x ∈ O := by
    simp only [B, O, Metric.mem_closedBall, dist_zero_right, norm_mul, absFin_eq_norm]
    constructor
    · intro hx
      nlinarith
    · intro hx
      nlinarith
  have hind (x : K) : B.indicator (fun _ => (1 : ℝ)) ((y : K) * x) =
      O.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ O
    · rw [Set.indicator_of_mem ((hpre x).mpr hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx ((hpre x).mp h)), Set.indicator_of_notMem hx]
  have hmass : (absFin v y)⁻¹ * μ.μ.real B = 1 := by
    calc
      _ = ∫ x, B.indicator (fun _ => (1 : ℝ)) ((y : K) * x) ∂μ.μ := by
        rw [μ.integral_comp_mul,
          integral_indicator_const (1 : ℝ) (show MeasurableSet B from measurableSet_closedBall)]
        simp only [smul_eq_mul, mul_one]
      _ = ∫ x, O.indicator (fun _ => (1 : ℝ)) x ∂μ.μ := by
        simp only [hind]
      _ = μ.μ.real O := by
        simpa only [smul_eq_mul, mul_one] using
          (integral_indicator_const (μ := μ.μ) (1 : ℝ)
            (show MeasurableSet O from measurableSet_closedBall))
      _ = 1 := by rw [hO, measureReal_def, μ.norm_O]; simp
  change μ.μ.real B = absFin v y
  have hy : absFin v y ≠ 0 := (absFin_pos y.ne_zero).ne'
  calc
    _ = (absFin v y * (absFin v y)⁻¹) * μ.μ.real B := by rw [mul_inv_cancel₀ hy, one_mul]
    _ = absFin v y * 1 := by rw [mul_assoc, hmass]
    _ = _ := mul_one _

/-- Positive powers are integrable against the local reciprocal-norm density near zero. -/
theorem finite_power_integrable {v : FinPlace F} (μ : LocHaar v)
    (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun y : v.adicCompletion F => absFin v y ^ (ε - 1))
      {y | absFin v y ≤ 1} μ.μ := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let _ : Finite (IsLocalRing.ResidueField O) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  let _ : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing O),
        inferInstanceAs (Finite (IsLocalRing.ResidueField O))⟩
  let _ : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (WithZero (Multiplicative ℤ))
  obtain ⟨a, ha, ha1⟩ := NormedField.exists_norm_lt_one K
  let c : ℝ := ‖a‖
  have hc : 0 < c := ha
  have hc1 : c < 1 := ha1
  let u : Kˣ := Units.mk0 a (norm_pos_iff.mp ha)
  let s : ℕ → Set K := fun n => {x | c ^ (n + 1) ≤ ‖x‖ ∧ ‖x‖ ≤ c ^ n}
  let g : K → ℝ := fun x => ‖x‖ ^ (ε - 1)
  let M : ℝ := max 1 (c ^ (ε - 1))
  let b : ℕ → ℝ := fun n => M * (c ^ n) ^ (ε - 1)
  have hscompact (n : ℕ) : IsCompact (s n) := by
    have hs : s n = Metric.closedBall (0 : K) (c ^ n) ∩
        {x : K | c ^ (n + 1) ≤ ‖x‖} := by
      ext x
      simp only [s, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall,
        dist_zero_right, and_comm]
    rw [hs]
    exact (isCompact_closedBall (0 : K) (c ^ n)).inter_right
      (isClosed_le continuous_const continuous_norm)
  have hgcont (n : ℕ) : ContinuousOn g (s n) := by
    apply continuous_norm.continuousOn.rpow_const
    intro x hx
    exact Or.inl ((pow_pos hc (n + 1)).trans_le hx.1).ne'
  have hgint (n : ℕ) : IntegrableOn g (s n) μ.μ :=
    ContinuousOn.integrableOn_compact (hscompact n) (hgcont n)
  have hb (n : ℕ) : 0 ≤ b n := by
    exact mul_nonneg ((zero_le_one.trans (le_max_left _ _)) : 0 ≤ M)
      (Real.rpow_nonneg (pow_nonneg hc.le n) _)
  have hgbound (n : ℕ) (x : K) (hx : x ∈ s n) : ‖g x‖ ≤ b n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    change ‖x‖ ^ (ε - 1) ≤ M * (c ^ n) ^ (ε - 1)
    by_cases he : 0 ≤ ε - 1
    · exact (Real.rpow_le_rpow (norm_nonneg x) hx.2 he).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg (pow_nonneg hc.le n) _) (le_max_left _ _))
    · have he' : ε - 1 ≤ 0 := le_of_lt (lt_of_not_ge he)
      calc
        _ ≤ (c ^ (n + 1)) ^ (ε - 1) :=
          Real.rpow_le_rpow_of_nonpos (pow_pos hc _) hx.1 he'
        _ = c ^ (ε - 1) * (c ^ n) ^ (ε - 1) := by
          rw [pow_succ, Real.mul_rpow (pow_nonneg hc.le _) hc.le, mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (pow_nonneg hc.le n) _)
  have hmass (n : ℕ) : μ.μ.real (s n) ≤ c ^ n := by
    have hsub : s n ⊆ Metric.closedBall (0 : K) (c ^ n) := by
      intro x hx
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2
    have hrad : absFin v ((u ^ n : Kˣ) : K) = c ^ n := by
      simp only [absFin_eq_norm, Units.val_pow_eq_pow_val, norm_pow, u, Units.val_mk0, c]
    calc
      _ ≤ μ.μ.real (Metric.closedBall (0 : K) (c ^ n)) :=
        measureReal_mono hsub (isCompact_closedBall (0 : K) (c ^ n)).measure_ne_top
      _ = c ^ n := by simpa only [hrad] using finite_ball_mass μ (u ^ n)
  have hprod : c ^ (ε - 1) * c = c ^ ε := by
    calc
      _ = c ^ (ε - 1) * c ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = c ^ (ε - 1 + 1) := (Real.rpow_add hc _ _).symm
      _ = _ := by congr 1; ring
  have hgeom (n : ℕ) : b n * c ^ n = M * (c ^ ε) ^ n := by
    calc
      _ = M * ((c ^ n) ^ (ε - 1) * c ^ n) := mul_assoc _ _ _
      _ = M * ((c ^ (ε - 1)) ^ n * c ^ n) := by
        rw [Real.rpow_pow_comm hc.le]
      _ = M * (c ^ (ε - 1) * c) ^ n := by rw [mul_pow]
      _ = _ := by rw [hprod]
  have hibound (n : ℕ) : (∫ x in s n, ‖g x‖ ∂μ.μ) ≤ M * (c ^ ε) ^ n := by
    have hnorm : ‖∫ x in s n, ‖g x‖ ∂μ.μ‖ ≤ b n * μ.μ.real (s n) := by
      apply norm_setIntegral_le_of_norm_le_const_ae (hscompact n).measure_lt_top
      filter_upwards [ae_restrict_mem (hscompact n).measurableSet] with x hx
      simpa only [norm_norm] using hgbound n x hx
    calc
      _ ≤ ‖∫ x in s n, ‖g x‖ ∂μ.μ‖ := le_abs_self _
      _ ≤ b n * μ.μ.real (s n) := hnorm
      _ ≤ b n * c ^ n := mul_le_mul_of_nonneg_left (hmass n) (hb n)
      _ = _ := hgeom n
  have hsum : Summable (fun n : ℕ => ∫ x in s n, ‖g x‖ ∂μ.μ) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) hibound
      ((summable_geometric_of_lt_one (Real.rpow_nonneg hc.le _)
        (Real.rpow_lt_one hc.le hc1 hε)).mul_left M)
  have hi := integrableOn_iUnion_of_summable_integral_norm hgint hsum
  have htotal : IntegrableOn g {x : K | ‖x‖ ≤ 1} μ.μ := by
    apply (hi.union (integrableOn_singleton (μ := μ.μ) (f := g) (x := (0 : K))
      (hx := (isCompact_singleton : IsCompact ({(0 : K)} : Set K)).measure_lt_top))).mono_set
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inr (Set.mem_singleton_iff.mpr hx0)
    · obtain ⟨n, hn, hn'⟩ :=
        exists_nat_pow_near_of_lt_one (norm_pos_iff.mpr hx0) hx hc hc1
      exact Or.inl (Set.mem_iUnion.mpr ⟨n, hn.le, hn'⟩)
  simpa only [g, absFin_eq_norm] using htotal

end ArtinPrimitiveRoots.Proofs.thsol_sheets
