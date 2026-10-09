import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.PrimaryPrimeSpec
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.EmbeddingConjugation

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

-- Preserve the cyclotomic instance used by the frozen Eisenstein interfaces.
attribute [local instance 2000] CyclotomicField.instNumberField
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Map OAI.primary_generator_mul_conj_eq_card through σ, use embedding conjugation, and identify quotient cardinal with absNorm.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: PrimaryPrimeSpec, EmbeddingConjugation. -/
theorem primary_prime_norm_sq (σ : E →+* ℂ) (v : FinPlace E)
    (hv : lambda ∉ v.asIdeal) :
    ‖integerComplex σ (primary v.asIdeal)‖ ^ 2 = (Ideal.absNorm v.asIdeal : ℝ) := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨_, hspan, hprimary⟩ := primary_prime_spec v hv
  have hmul := OAI.ActualEisensteinCubic.primary_generator_mul_conj_eq_card
    v.asIdeal hv (primary v.asIdeal) hspan hprimary
  let z := integerComplex σ (primary v.asIdeal)
  have hcardC : z * star z = (Nat.card (OE ⧸ v.asIdeal) : ℂ) := by
    have h := congrArg (integerComplex σ) hmul
    rw [map_mul, eisenstein_embedding_conjugation, map_natCast] at h
    simpa [z] using h
  have hcard : Nat.card (OE ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hnormC : (‖z‖ : ℂ) ^ 2 = (Ideal.absNorm v.asIdeal : ℂ) := by
    calc
      (‖z‖ : ℂ) ^ 2 = z * star z := (Complex.mul_conj' z).symm
      _ = (Nat.card (OE ⧸ v.asIdeal) : ℂ) := hcardC
      _ = (Ideal.absNorm v.asIdeal : ℂ) := by exact_mod_cast hcard
  have hnormR : ‖z‖ ^ 2 = (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast hnormC
  simpa [z] using hnormR

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
