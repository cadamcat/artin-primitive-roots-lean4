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

/-- The scalar dividing the normalized residue and coefficients is nonzero.
Guide: sol-thin-thglobal/PROOFS.md:1180–1190.
Uses ThetaNormalizationInput.eval_ne_zero, besselConst and positivity of Gamma at 4/3. -/
theorem theta_normalizationScalar_ne_zero {P : CoverPackage D S H A}
    (N : ThetaNormalizationInput P) : thetaNormalizationScalar N ≠ 0 := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
