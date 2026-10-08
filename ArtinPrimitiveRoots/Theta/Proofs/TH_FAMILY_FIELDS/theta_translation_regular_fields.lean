import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Retain torus continuity and both root smoothness fields through the iterated derivative of the actual common-family residue.
Guide: sol-thin-thglobal/PROOFS.md:1200–1204.
Uses ThetaCommonSections.C, ContinuedEis.jointRoots and mixed derivative estimates; the formal Rderiv_spec alone does not supply these fields. -/
theorem theta_translation_regular_fields {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛)
    (L : SChar S) (hL : L ∈ 𝓛) :
    (∀ g h, Continuous fun y : S.FSˣ => thetaFamilyTheta B L (g * P.tc.aS y * h)) ∧
    (∀ (g : P.tc.G) (w : InfinitePlace F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ =>
        thetaFamilyTheta B L (g * P.tc.nS
          (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))))) ∧
    JointRootSmooth P (thetaFamilyTheta B L) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
