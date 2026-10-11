import ArtinPrimitiveRoots.Proofs.a2_cond_lead_p.ConductorAdditiveCharacters

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Primitive additive characters on every finite ideal residue ring, including
O_F/O_F. Use the trace/different pairing or finite Frobenius duality.
Uses exact nonzero exterior ideals; feeds the finite Fourier and additive estimates. -/
theorem conductor_additive_characters_exists (S : A1.SData F CE condη) :
    Nonempty (ConductorAdditiveCharacters S) := by
  classical
  let ψ : ∀ q : S.ExtIdeal, AddChar (ConductorResidueRing q) ℂ :=
    fun q => Classical.choose (conductor_primitive_addChar_exists S q)
  refine ⟨⟨ψ, ?_⟩⟩
  intro q
  exact Classical.choose_spec (conductor_primitive_addChar_exists S q)

end ArtinPrimitiveRoots.A2
