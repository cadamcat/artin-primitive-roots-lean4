import ArtinPrimitiveRoots.Theta.LocalInt
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Classical Valued

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1

/-- Multiplication by an inverse unit scales finite additive Haar measure by
the absolute value of the original unit. -/
theorem finiteHaar_map_unit_inverse
    {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : (v.adicCompletion F)ˣ) :
    Measure.map (fun x : v.adicCompletion F => x * (k⁻¹ : (v.adicCompletion F)ˣ).val)
        μ.μ =
      ENNReal.ofReal (absFin v (k : v.adicCompletion F)) • μ.μ := by
  let K := v.adicCompletion F
  letI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  letI : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  letI : Measure.IsAddHaarMeasure μ.μ := μ.isHaar
  letI : Measure.Regular μ.μ := inferInstance
  let e : K ≃ₜ K := Homeomorph.mulRight₀ (k⁻¹ : Kˣ).val (Units.ne_zero _)
  letI : Measure.Regular (Measure.map e μ.μ) := Measure.Regular.map e
  letI : Measure.Regular (ENNReal.ofReal (absFin v (k : K)) • μ.μ) :=
    Measure.Regular.smul ENNReal.ofReal_ne_top
  change Measure.map e μ.μ = ENNReal.ofReal (absFin v (k : K)) • μ.μ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  calc
    ∫ x, f x ∂Measure.map e μ.μ = ∫ x, f (e x) ∂μ.μ :=
      integral_map_equiv e.toMeasurableEquiv f
    _ = (absFin v (k : K)) • ∫ x, f x ∂μ.μ := by
      have h := μ.integral_comp_mul (k⁻¹) (fun x : K => f x)
      simpa [e, mul_comm, Theta.absFin_eq_norm] using h
    _ = ∫ x, f x ∂(ENNReal.ofReal (absFin v (k : K)) • μ.μ) := by
      rw [integral_smul_measure,
        ENNReal.toReal_ofReal (by rw [Theta.absFin_eq_norm]; positivity)]

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
