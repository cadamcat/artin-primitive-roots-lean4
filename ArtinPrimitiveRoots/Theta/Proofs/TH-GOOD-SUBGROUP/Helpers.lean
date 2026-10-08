import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Helpers
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GOOD-SUBGROUP».ProjectedCongruence
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GOOD-SUBGROUP».FiniteRational
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GOOD-SUBGROUP».LevelHom
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GOOD-SUBGROUP».Multiplier

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Finite-level lifting followed by the kernel of the central multiplier and a free congruence
subgroup. The resulting group is only required to have finite index. -/
theorem th_good_finite_level (P : CoverPackage D S H A)
    (T0 : Finset (FinPlace F)) (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v) (j : P.RP) :
    ∃ Γ : Subgroup (SL(2, 𝓞 F)), Γ.FiniteIndex ∧ Spec.FreeAction F Γ ∧
      ∀ γ ∈ Γ, ∃ k : P.RP, th_classical_finiteLevel P T0 hT0 m k ∧
        th_classical_finiteEq P
          (P.ratRP (Matrix.SpecialLinearGroup.toGL (Spec.toSLF F γ)) * j) (j * k) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
