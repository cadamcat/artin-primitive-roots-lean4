import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_generators_exists
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_residues_exists
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_additive_characters_exists

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The dual additive large sieve for the exact residue fractions on one exterior
dyad, uniform in the chosen primitive additive characters. Balancing uses the actual
number-field degree and both real and complex places. The norm-one dyad is T=1.
Guide: sol-thin-a2zf/PROOFS.md:720–732 (general-field extension of lem_additive_sieve).
Uses balanced generator compactness and distinct reduced fractions; feeds exterior dyad glue. -/
theorem conductor_additive_sieve_apply (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (ρ : ConductorResidues S)
    (Ψ : ConductorAdditiveCharacters S) :
    ∃ C : ℝ, 0 < C ∧ ∀ T V : ℝ, 1 ≤ T → 2 ≤ V →
      ∀ b : S.ExtIdeal → ℂ,
        (∑ q ∈ conductorExteriorCutoff S V,
          ∑ d : (ConductorResidueRing q)ˣ,
            ‖∑ I ∈ conductorExteriorDyad S T,
              b I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2) ≤
          C * (T + V ^ 2) * ∑ I ∈ conductorExteriorDyad S T, ‖b I‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots.A2
