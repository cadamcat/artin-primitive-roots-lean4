import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.prod_one_sub_character
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.finite_euler_correction_analytic

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke
open ArtinPrimitiveRoots.Ext.SplittingInputs

/-- General abelian Euler factorization with the actual deleted-prime correction.
Guide: ../sol-thin-s7/PROOFS.md:366–434. Uses `ext_cft_artin`,
`prod_one_sub_character`, `finite_euler_correction_analytic`, the Hecke Euler
product, residue Frobenius order, and convergent regrouping by contraction.
Feeds `sp_upstairs_factor` and `quotient_factor_of_euler_identity`. -/
theorem upstairs_rhp_euler_identity (B T : Type*)
    [Field B] [NumberField B] [Field T] [NumberField T]
    [Algebra B T] [IsAbelianGalois B T] :
    ∃ (m : RayClassModulus B) (Art : RayClassGroup m →* (T ≃ₐ[B] T)),
      Function.Surjective Art ∧ FrobeniusNormalizedArtinMap m Art ∧
      AnalyticOn ℂ (s7UpstairsCorrection B T m) {s : ℂ | 0 < s.re} ∧
      (∀ s : ℂ, 0 < s.re → s7UpstairsCorrection B T m s ≠ 0) ∧
      (∀ s : ℂ, 1 < s.re →
        NumberField.dedekindZeta T s = s7UpstairsCorrection B T m s *
          ∏ χ : (T ≃ₐ[B] T) →* ℂˣ, LSeriesRay (χ.comp Art) s) := by
  sorry

end ArtinPrimitiveRoots.Splitting
end
