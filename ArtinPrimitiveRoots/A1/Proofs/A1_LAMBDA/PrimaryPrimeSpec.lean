import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

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

/-- A1-LAMBDA IMPL: Use normalizedFactors_irreducible to reduce to primaryPrime, then OAI primaryPrime_ne_zero and primaryGenerator_spec.
Uses: Definitions. -/
theorem primary_prime_spec (v : FinPlace E) (hv : lambda ∉ v.asIdeal) :
    primary v.asIdeal ≠ 0 ∧ v.asIdeal = Ideal.span {primary v.asIdeal} ∧
      lambda ^ 2 ∣ primary v.asIdeal - 1 := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  have hP : Prime v.asIdeal := (Ideal.prime_iff_isPrime v.ne_bot).2 v.isPrime
  have hfac : UniqueFactorizationMonoid.normalizedFactors v.asIdeal = {v.asIdeal} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP.irreducible]
    simp
  have hprimary : primary v.asIdeal = OAI.CompletedGauss.primaryPrime v.asIdeal := by
    change OAI.CompletedGauss.primaryGenerator v.asIdeal = _
    rw [OAI.CompletedGauss.primaryGenerator]
    simp [v.ne_bot, hfac]
  have hp0 : OAI.CompletedGauss.primaryPrime v.asIdeal ≠ 0 :=
    OAI.CompletedGauss.primaryPrime_ne_zero v.asIdeal hv
  have hspec := OAI.CompletedGauss.primaryPrime_spec v.asIdeal hp0
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hprimary] using hp0
  · rw [hprimary]
    exact hspec.2.2.1.symm
  · rw [hprimary]
    exact hspec.2.2.2

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
