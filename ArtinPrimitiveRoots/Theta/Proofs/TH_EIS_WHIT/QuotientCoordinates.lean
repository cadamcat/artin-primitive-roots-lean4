import ArtinPrimitiveRoots.Theta.Proofs.«TH-GLOBAL-DATUM».CubicQuotient

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

/-- Cube containment makes every local Lagrangian quotient finite. -/
theorem whit_alag_quotient_finite {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (T : TorusRep D H v) [Nontrivial T.V]
    (L : Subgroup (v.adicCompletion F)ˣ)
    (hcubes : ∀ t : (v.adicCompletion F)ˣ, t ^ 3 ∈ L) :
    Finite ((v.adicCompletion F)ˣ ⧸ L) := by
  let K := (v.adicCompletion F)ˣ
  let C : Subgroup K := (powMonoidHom 3 : K →* K).range
  letI : Finite (K ⧸ C) := (torusRep_cube_control T).finite
  have hCL : C ≤ L.comap (MonoidHom.id K) := by
    intro x hx
    obtain ⟨t, rfl⟩ := hx
    exact hcubes t
  have hsurj : Function.Surjective (QuotientGroup.map C L (MonoidHom.id K) hCL) :=
    QuotientGroup.map_surjective_of_surjective C L (MonoidHom.id K)
      QuotientGroup.mk_surjective hCL
  exact Finite.of_surjective _ hsurj

end ArtinPrimitiveRoots.A1.Theta
