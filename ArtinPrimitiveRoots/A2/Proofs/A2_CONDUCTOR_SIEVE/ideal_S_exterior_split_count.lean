import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Exact supported/exterior factorization, uniqueness, norm bounds, logarithmic
count, and square-mass partition. Guide: sol-thin-a2zf/PROOFS.md:652–657.
Uses the normalized ideal factorization API; feeds conductor_sieve_assemble and the bridge. -/
theorem ideal_S_exterior_split_count (S : A1.SData F CE condη) :
    (∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      ConductorSupportedAtS S (conductorSPart S I) ∧
      S.IsExterior (conductorExteriorPart S I) ∧
      I = conductorSPart S I * conductorExteriorPart S I ∧
      Ideal.absNorm (conductorSPart S I) ≤ Ideal.absNorm I ∧
      Ideal.absNorm (conductorExteriorPart S I) ≤ Ideal.absNorm I ∧
      (∀ J E : Ideal (𝓞 F), ConductorSupportedAtS S J → S.IsExterior E →
        I = J * E → J = conductorSPart S I ∧ E = conductorExteriorPart S I)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 2 ≤ N →
      ((conductorSPieces S N).card : ℝ) ≤ C * (1 + Real.log N) ^ S.Sf.card) ∧
    (∀ (N : ℝ) (b : Ideal (𝓞 F) → ℂ),
      (∑ J ∈ conductorSPieces S N,
        ∑ I ∈ ((conductorIdealCutoff F N).filter (fun I => I ≠ ⊥ ∧ conductorSPart S I = J)),
          ‖b I‖ ^ 2) =
      ∑ I ∈ ((conductorIdealCutoff F N).filter (fun I => I ≠ ⊥)), ‖b I‖ ^ 2) := by
  sorry

end ArtinPrimitiveRoots.A2
