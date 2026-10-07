import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Localization away from S identifies R/qR with O_F/q; include the unit
modulus and do not choose a junk residue for an element with a denominator.
Guide: sol-thin-a2zf/PROOFS.md:666–677.
Uses exterior coprimality; feeds primitive_conductor_residue_bridge. -/
theorem conductor_residues_exists (S : A1.SData F CE condη) :
    Nonempty (ConductorResidues S) := by
  sorry

end ArtinPrimitiveRoots.A2
