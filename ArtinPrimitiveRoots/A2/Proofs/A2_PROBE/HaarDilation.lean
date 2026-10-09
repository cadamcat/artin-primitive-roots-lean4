import ArtinPrimitiveRoots.Theta.LocalInt
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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

/-- Multiplication by an inverse complex unit scales volume by its norm square. -/
theorem complex_volume_map_unit_inverse (k : ℂˣ) :
    Measure.map (fun x : ℂ => x * (k⁻¹ : ℂˣ).val) (volume : Measure ℂ) =
      ENNReal.ofReal (Complex.normSq (k : ℂ)) • (volume : Measure ℂ) := by
  let a : ℂ := (k⁻¹ : ℂˣ).val
  let f : ℂ →ₗ[ℝ] ℂ := LinearMap.mul ℝ ℂ a
  have hmatrix : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI f =
      !![a.re, -a.im; a.im, a.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [f, LinearMap.toMatrix_apply, Complex.mul_re, Complex.mul_im]
  have hdet : LinearMap.det f = Complex.normSq a := by
    rw [← LinearMap.det_toMatrix Complex.basisOneI, hmatrix,
      Matrix.det_fin_two_of, Complex.normSq_apply]
    ring
  have hne : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact ne_of_gt (Complex.normSq_pos.mpr (Units.ne_zero (k⁻¹)))
  have hcoef : |(LinearMap.det f)⁻¹| = Complex.normSq (k : ℂ) := by
    simp [hdet, a, Complex.normSq_inv,
      abs_of_nonneg (Complex.normSq_nonneg (k : ℂ))]
  have hfun : (fun x : ℂ => x * (k⁻¹ : ℂˣ).val) = (f : ℂ → ℂ) := by
    funext x
    exact mul_comm x a
  rw [hfun, Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hne,
    hcoef]

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
