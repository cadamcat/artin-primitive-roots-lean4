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

variable {F : Type} [Field F] [NumberField F]

/-- Rational units lying in every specified local subgroup. -/
def whitRationalAlag (L : ∀ v : FinPlace F, Subgroup (v.adicCompletion F)ˣ) :
    Subgroup Fˣ :=
  ⨅ v : FinPlace F, (L v).comap (toLoc v)

/-- The coordinate of a rational quotient class in a local subgroup quotient. -/
def whitAlagCoordinate (L : ∀ v : FinPlace F, Subgroup (v.adicCompletion F)ˣ)
    (v : FinPlace F) :
    Fˣ ⧸ whitRationalAlag L →* (v.adicCompletion F)ˣ ⧸ L v :=
  QuotientGroup.map (whitRationalAlag L) (L v) (toLoc v)
    (iInf_le (fun w : FinPlace F => (L w).comap (toLoc w)) v)

/-- The intersection subgroup is exactly the kernel of all local quotient coordinates. -/
theorem whit_alag_coordinates_injective
    (L : ∀ v : FinPlace F, Subgroup (v.adicCompletion F)ˣ) :
    Function.Injective (fun q : Fˣ ⧸ whitRationalAlag L =>
      fun v : FinPlace F => whitAlagCoordinate L v q) := by
  intro q q' h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
  apply QuotientGroup.eq_iff_div_mem.mpr
  change a / b ∈ ⨅ v : FinPlace F, (L v).comap (toLoc v)
  rw [Subgroup.mem_iInf]
  intro v
  change toLoc v (a / b) ∈ L v
  rw [map_div]
  apply QuotientGroup.eq_iff_div_mem.mp
  have hv := congrFun h v
  change (QuotientGroup.mk (toLoc v a) : (v.adicCompletion F)ˣ ⧸ L v) =
    QuotientGroup.mk (toLoc v b) at hv
  exact hv

end ArtinPrimitiveRoots.A1.Theta
