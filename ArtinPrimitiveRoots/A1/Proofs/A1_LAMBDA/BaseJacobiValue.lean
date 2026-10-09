import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.PrimaryPrimeNorm
import OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

-- Preserve the cyclotomic instance used by the frozen Eisenstein interfaces.
attribute [local instance 2000] CyclotomicField.instNumberField
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Map cubicJacobi_eq_neg_primary_generator_of_principal by jacobiSum_ringHomComp. Rewrite the real normalization using the positive generator norm and norm-square formula.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: PrimaryPrimeNorm. -/
theorem base_jacobi_value (σ : E →+* ℂ) (v : FinPlace E)
    (hv : lambda ∉ v.asIdeal) :
    normalizedJacobi v (baseCubicChar σ v hv) = -eisensteinPrimeValue σ v := by
  classical
  letI : v.asIdeal.IsMaximal := v.isMaximal
  have hspec := primary_prime_spec v hv
  have hJ : jacobiSum (baseCubicChar σ v hv) (baseCubicChar σ v hv) =
      -(integerComplex σ (primary v.asIdeal)) := by
    rw [baseCubicChar, jacobiSum_ringHomComp]
    have hOAI := OAI.ActualEisensteinCubic.cubicJacobi_eq_neg_primary_generator_of_principal
      v.asIdeal hv (primary v.asIdeal) hspec.2.1 hspec.2.2
    simpa only [map_neg] using congrArg (integerComplex σ) hOAI
  let z := integerComplex σ (primary v.asIdeal)
  have hnorm : ‖z‖ ^ 2 = (Ideal.absNorm v.asIdeal : ℝ) := by
    simpa [z] using primary_prime_norm_sq σ v hv
  have hNatPos : 0 < Ideal.absNorm v.asIdeal := by
    apply Nat.pos_iff_ne_zero.mpr
    exact (Ideal.absNorm_ne_zero_iff v.asIdeal).mpr
      (inferInstance : Finite (OE ⧸ v.asIdeal))
  have hAbsPos : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast hNatPos
  have hzpos : 0 < ‖z‖ := by
    have hsquare : 0 < ‖z‖ ^ 2 := by rw [hnorm]; exact hAbsPos
    have hzne : ‖z‖ ≠ 0 := by
      intro hz
      rw [hz] at hsquare
      norm_num at hsquare
    exact lt_of_le_of_ne (norm_nonneg z) (Ne.symm hzne)
  have hscale : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) = ‖z‖⁻¹ := by
    calc
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) =
          (‖z‖ ^ 2) ^ (-(1 / 2 : ℝ)) := by rw [hnorm]
      _ = ‖z‖ ^ ((2 : ℝ) * (-(1 / 2 : ℝ))) :=
        (Real.rpow_natCast_mul (norm_nonneg z) 2 (-(1 / 2 : ℝ))).symm
      _ = ‖z‖ ^ (-1 : ℝ) := by congr 1 <;> norm_num
      _ = ‖z‖⁻¹ := by rw [Real.rpow_neg_one]
  change (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ) : ℝ) : ℝ) : ℂ) *
      jacobiSum (baseCubicChar σ v hv) (baseCubicChar σ v hv) =
        -(z / ‖z‖)
  have hscaleC :
      (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ) : ℝ) : ℝ) : ℂ) =
        (‖z‖⁻¹ : ℂ) := by
    exact_mod_cast hscale
  rw [hscaleC, hJ]
  simp only [div_eq_mul_inv]
  ring

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
