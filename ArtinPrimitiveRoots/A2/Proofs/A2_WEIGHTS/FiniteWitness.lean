import ArtinPrimitiveRoots.Theta.LocalInt
import ArtinPrimitiveRoots.Theta.AnalysisS

set_option autoImplicit false
set_option maxHeartbeats 800000
open ArtinPrimitiveRoots A1 A2 NumberField IsDedekindDomain MeasureTheory Filter
open scoped Classical Valued Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_weights_sol

theorem exists_finite_unit_factor
    {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) :
    ∃ f : v.adicCompletion F → ℂ,
      Continuous f ∧ HasCompactSupport f ∧ IsLocallyConstant f ∧
      (∀ x ∈ tsupport f, x ≠ 0) ∧ f 1 = 1 ∧
      (∫ x, f x * (absFin v x : ℂ) ^ (1 - (1 / 6 : ℂ))
        ∂Theta.mulHaarFin μ) ≠ 0 := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  letI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  letI : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  let B : Set K := Theta.ball v 1
  have hBopen : IsOpen B :=
    v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  let U : AddSubgroup K := Valued.v.leAddSubgroup (WithZero.exp (-1 : ℤ))
  have hBclosed : IsClosed B := AddSubgroup.isClosed_of_isOpen U hBopen
  have hBbound : B ⊆ Metric.closedBall (0 : K) 1 := by
    intro x hx
    have hle : Valued.v x ≤ Valued.v (1 : K) := by
      have h1 : Valued.v (1 : K) = WithZero.exp (0 : ℤ) := by simp
      rw [h1]
      exact hx.trans ((WithZero.exp_le_exp).2 (by norm_num : (-1 : ℤ) ≤ 0))
    have hnorm : ‖x‖ ≤ ‖(1 : K)‖ := Valued.toNormedField.norm_le_iff.mpr hle
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_one] using hnorm
  have hBcompact : IsCompact B :=
    (isCompact_closedBall (0 : K) 1).of_isClosed_subset hBclosed hBbound
  let C : Set K := {x | x - 1 ∈ B}
  have hCeq : C = (fun x : K => x + 1) '' B := by
    ext x
    constructor
    · intro hx
      exact ⟨x - 1, hx, sub_add_cancel x 1⟩
    · rintro ⟨x, hx, rfl⟩
      change x + 1 - 1 ∈ B
      simpa only [add_sub_cancel_right] using hx
  have hCcompact : IsCompact C := by
    rw [hCeq]
    exact hBcompact.image (by fun_prop)
  have hCopen : IsOpen C := hBopen.preimage (by fun_prop)
  have hCmeas : MeasurableSet C := hCopen.measurableSet
  have h1C : (1 : K) ∈ C := by
    change Valued.v ((1 : K) - 1) ≤ WithZero.exp (-1 : ℤ)
    rw [sub_self, map_zero]
    exact zero_le
  let f : K → ℂ := C.indicator (fun _ => (1 : ℂ))
  have hflc : IsLocallyConstant f :=
    ((LocallyConstant.const K (1 : ℂ)).indicator
      ⟨hCcompact.isClosed, hCopen⟩).isLocallyConstant
  have hsupport : Function.support f ⊆ C := by
    intro x hx
    by_contra hxC
    exact (Function.mem_support.mp hx) (by simp [f, hxC])
  have htsupport : tsupport f ⊆ C := closure_minimal hsupport hCcompact.isClosed
  have hfc : HasCompactSupport f :=
    hCcompact.of_isClosed_subset (isClosed_tsupport f) htsupport
  have hAbs (x : K) (hx : x ∈ C) : absFin v x = 1 := by
    have hsub : Valued.v (x - 1) ≤ WithZero.exp (-1 : ℤ) := hx
    have h1 : Valued.v (1 : K) = WithZero.exp (0 : ℤ) := by simp
    have hlt : Valued.v (x - 1) < Valued.v (1 : K) := by
      rw [h1]
      exact lt_of_le_of_lt hsub ((WithZero.exp_lt_exp).2 (by norm_num : (-1 : ℤ) < 0))
    have hval : Valued.v x = Valued.v (1 : K) := by
      rw [show x = (1 : K) + (x - 1) by abel]
      exact Valued.v.map_add_eq_of_lt_left hlt
    have hnorm : ‖x‖ = ‖(1 : K)‖ := by
      rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hval]
    simpa only [Theta.absFin_eq_norm, norm_one] using hnorm
  have hmassPos : 0 < μ.μ C := IsOpen.measure_pos μ.μ hCopen ⟨1, h1C⟩
  have hmassFinite : μ.μ C < ⊤ := hCcompact.measure_lt_top
  have hmassReal : 0 < μ.μ.real C :=
    ENNReal.toReal_pos hmassPos.ne' hmassFinite.ne
  have hdensity : (fun x : K => ENNReal.ofReal (absFin v x)⁻¹) =ᵐ[μ.μ.restrict C]
      fun _ => (1 : ENNReal) := by
    filter_upwards [ae_restrict_mem hCmeas] with x hx
    rw [hAbs x hx]
    simp
  have hrestrict : (Theta.mulHaarFin μ).restrict C = μ.μ.restrict C := by
    calc
      (Theta.mulHaarFin μ).restrict C = (μ.μ.restrict C).withDensity
          (fun x => ENNReal.ofReal (absFin v x)⁻¹) := restrict_withDensity hCmeas _
      _ = (μ.μ.restrict C).withDensity (fun _ => (1 : ENNReal)) :=
        withDensity_congr_ae hdensity
      _ = μ.μ.restrict C := by simp
  have hweighted :
      (fun x : K => f x * (absFin v x : ℂ) ^ (1 - (1 / 6 : ℂ))) = f := by
    funext x
    by_cases hx : x ∈ C
    · simp [f, hx, hAbs x hx]
    · simp [f, hx]
  have hmoment :
      (∫ x, f x * (absFin v x : ℂ) ^ (1 - (1 / 6 : ℂ)) ∂Theta.mulHaarFin μ) =
        (μ.μ.real C : ℂ) := by
    rw [hweighted]
    change (∫ x, C.indicator (fun _ => (1 : ℂ)) x ∂Theta.mulHaarFin μ) = _
    rw [integral_indicator hCmeas, hrestrict]
    simp [integral_const, Complex.real_smul]
  refine ⟨f, hflc.continuous, hfc, hflc, ?_, ?_, ?_⟩
  · intro x hx hx0
    have habs := hAbs x (htsupport hx)
    rw [hx0, Theta.absFin_eq_norm, norm_zero] at habs
    exact zero_ne_one habs
  · simp [f, h1C]
  · rw [hmoment]
    exact Complex.ofReal_ne_zero.mpr hmassReal.ne'

end ArtinPrimitiveRoots.Proofs.a2_weights_sol
