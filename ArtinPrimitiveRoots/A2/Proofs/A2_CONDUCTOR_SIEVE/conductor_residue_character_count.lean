import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs
import Mathlib.NumberTheory.MulChar.Duality

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Finite abelian duality bounds any set of residue multiplicative characters
by the unit-group order and hence by the ring order. Works for the unit ring.
Uses MulChar/Duality; feeds the bottom-ideal family count. -/
theorem conductor_residue_character_count {R : Type*} [CommRing R] [Fintype R]
    (𝓧 : Finset (MulChar R ℂ)) :
    𝓧.card ≤ Fintype.card Rˣ ∧ Fintype.card Rˣ ≤ Fintype.card R := by
  constructor
  · classical
    let e : MulChar R ℂ ≃ Rˣ := (MulChar.mulEquiv_units (M := R) (R := ℂ)).some.toEquiv
    letI : Fintype (MulChar R ℂ) := Fintype.ofEquiv Rˣ e.symm
    calc
      𝓧.card ≤ Fintype.card (MulChar R ℂ) := Finset.card_le_univ _
      _ = Fintype.card Rˣ := Fintype.card_congr e
  · exact Fintype.card_le_of_injective (fun u : Rˣ => (u : R)) (fun _ _ h => Units.ext h)

end ArtinPrimitiveRoots.A2
