import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Adapt OAI.ringComplex_conjO with arbitrary embedding: a complex cubic root has norm one, and conjugation sends omega to its square.
Uses: Definitions. -/
theorem eisenstein_embedding_conjugation (σ : E →+* ℂ) (a : OE) :
    integerComplex σ (OAI.ActualEisensteinCubic.conjO a) =
      (starRingEnd ℂ) (integerComplex σ a) := by
  have : IsCyclotomicExtension {3} ℚ E := CyclotomicField.isCyclotomicExtension 3 ℚ
  let z := integerComplex σ omega
  have hz3 : z ^ 3 = 1 := by
    change integerComplex σ omega ^ 3 = 1
    rw [← map_pow, OAI.ActualEisensteinCubic.omega_primitive.pow_eq_one, map_one]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz3
    exact zero_ne_one hz3
  have hznorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz3 (by decide)
  have hzstar : star z = z ^ 2 := by
    apply mul_left_cancel₀ hz0
    calc
      z * star z = 1 := by
        rw [← starRingEnd_apply, Complex.mul_conj', hznorm]
        norm_num
      _ = z * z ^ 2 := by rw [← pow_succ', hz3]
  have hhom :
      (integerComplex σ).comp OAI.ActualEisensteinCubic.conjO.toRingHom =
        (starRingEnd ℂ).comp (integerComplex σ) := by
    apply RingHom.toIntAlgHom_injective
    apply (IsCyclotomicExtension.zeta_spec 3 ℚ E).integralPowerBasis.algHom_ext
    rw [(IsCyclotomicExtension.zeta_spec 3 ℚ E).integralPowerBasis_gen]
    change integerComplex σ (OAI.ActualEisensteinCubic.conjO omega) =
      star (integerComplex σ omega)
    rw [OAI.ActualEisensteinCubic.conjO_omega, map_pow]
    exact hzstar.symm
  have hx := congrArg (fun f : OE →+* ℂ => f a) hhom
  exact hx

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
