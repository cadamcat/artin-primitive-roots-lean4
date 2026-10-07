import ArtinPrimitiveRoots.Spec.Reduction

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- The point in the destination cusp chart for an integral transition.
Guide: sol-thin-spec/PROOFS.md:203–205. Used by the low/high overlap parts and R9. -/
def siegelTransition (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (i j : d.ι) (γ : Γ) (z : X F) : X F :=
  (d.σ j)⁻¹ • ((γ : SL(2,𝓞 F)) • ((d.σ i) • z))

/-- Siegel overlaps whose source and destination chart heights are at most `A`.
Guide: sol-thin-spec/PROOFS.md:204. Used by low-height finiteness and R9. -/
def siegelLowOverlap (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) : Set Γ :=
  {γ | ∃ (i j : d.ι) (z : X F), z ∈ SiegelData.setAt F d i ∧
    siegelTransition Γ d i j γ z ∈ SiegelData.setAt F d j ∧
    normHeight F z ≤ A ∧ normHeight F (siegelTransition Γ d i j γ z) ≤ A}

/-- Siegel overlaps whose source or destination chart height exceeds `A`.
Guide: sol-thin-spec/PROOFS.md:205. Used by high-height finiteness and R9. -/
def siegelHighOverlap (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) : Set Γ :=
  {γ | ∃ (i j : d.ι) (z : X F), z ∈ SiegelData.setAt F d i ∧
    siegelTransition Γ d i j γ z ∈ SiegelData.setAt F d j ∧
    (A < normHeight F z ∨ A < normHeight F (siegelTransition Γ d i j γ z))}
end ArtinPrimitiveRoots.A1.Spec
