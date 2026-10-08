import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Every adelic point has a classical component representation at the prescribed common
level. This isolates the geometric covering step from the analytic independence proof.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:797–800`; component input: lines 786–796.
Uses `ContinuedEisComponents.detect` from frozen `exists_classical_components` and
archimedean Iwasawa coordinates. Consumed by component reconstruction and torus charts. -/
theorem continuedEis_component_representatives {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I) :
    ∀ g : P.tc.G, ∃ (j : C.J) (γ : GL (Fin 2) F)
      (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ)
      (kinf k : P.tc.G), (∀ w, 0 < y w) ∧ kinf ∈ infCompact P ∧
        k ∈ levelSet P I.T0 C.hsub C.m ∧
        g = P.tc.rat γ * (nInf P x * aInf P y * j) * kinf * k := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
