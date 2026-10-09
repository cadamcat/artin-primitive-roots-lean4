import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.AngularCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.PrimaryIdealCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseLocalConstruction
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.LocalCharacterDescent

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

/-- A1-LAMBDA IMPL: Obtain angular and primary ideal characters, build BaseLocalData, descend, and unfold unramifiedAt/primeValue with the single-place formulas.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: AngularCharacter, PrimaryIdealCharacter, BaseLocalConstruction, LocalCharacterDescent. -/
theorem base_character_exists (σ : E →+* ℂ) :
    ∃ χ : LambdaChar E, unitary χ ∧ simpleAngularType χ ∧
      ∀ v : FinPlace E, lambda ∉ v.asIdeal →
        unramifiedAt χ v ∧ primeValue χ v = eisensteinPrimeValue σ v := by
  obtain ⟨a, ha⟩ := angular_character_exists
  obtain ⟨φ, hφ⟩ := primary_ideal_character_exists σ
  obtain ⟨B⟩ := base_local_data_exists σ φ hφ a ha
  obtain ⟨χ, hunit, hfin, hinf⟩ := local_character_descent B.toLocalCharacterData
  refine ⟨χ, hunit, ?_, ?_⟩
  · intro w hw
    obtain ⟨m, hm, hz⟩ := B.angular w hw
    refine ⟨m, hm, fun z => ?_⟩
    rw [hinf]
    exact hz z
  · intro v hv
    have hunram : unramifiedAt χ v := by
      intro x hx1 hx2
      rw [hfin]
      exact B.exterior_units v hv x ⟨hx1, hx2⟩
    refine ⟨hunram, ?_⟩
    dsimp only [primeValue, KummerProofs.primeValue]
    simp only [hunram, ↓reduceIte]
    rw [hfin]
    exact B.prime_formula v hv

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
