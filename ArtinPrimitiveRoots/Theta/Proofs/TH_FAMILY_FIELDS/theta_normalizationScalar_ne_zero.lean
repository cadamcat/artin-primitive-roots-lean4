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
Uses ThetaNormalizationInput.eval_ne_zero, besselConst and positivity of Gamma at 4/3. -/
theorem theta_normalizationScalar_ne_zero {P : CoverPackage D S H A}
    (N : ThetaNormalizationInput P) : thetaNormalizationScalar N ≠ 0 := by
  have hbessel : besselConst ≠ 0 := by
    have hgamma : 0 < Real.Gamma (4 / 3 : ℝ) := by
      apply Real.Gamma_pos_of_pos
      norm_num
    have hpow : 0 < (2 * Real.pi) ^ ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hconst : 0 < besselConst := by
      unfold besselConst
      apply mul_pos
      · exact div_pos (by positivity) hgamma
      · exact hpow
    exact ne_of_gt hconst
  have hfactor : ∀ w : InfinitePlace F,
      (-(4 * Real.pi * Complex.I) * besselConst : ℂ) ≠ 0 := by
    intro w
    apply mul_ne_zero
    · apply neg_ne_zero.mpr
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact_mod_cast Real.pi_pos.ne'
      · exact Complex.I_ne_zero
    · exact_mod_cast hbessel
  unfold thetaNormalizationScalar
  apply mul_ne_zero N.eval_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro w hw
  exact hfactor w
end ArtinPrimitiveRoots.A1.Theta
