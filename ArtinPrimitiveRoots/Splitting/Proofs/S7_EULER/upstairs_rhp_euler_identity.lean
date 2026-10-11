import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.prod_one_sub_character
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.finite_euler_correction_analytic
import ArtinPrimitiveRoots.Proofs.s7_euler_b.LocalFrobenius

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke
open ArtinPrimitiveRoots.Ext.SplittingInputs

/-- General abelian Euler factorization with the actual deleted-prime correction.
Uses `ext_cft_artin`,
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
  classical
  letI : Algebra (𝓞 B) (𝓞 T) := inferInstance
  letI : IsScalarTower (𝓞 B) (𝓞 T) T := inferInstance
  obtain ⟨m, Art, hsurj, hFrob⟩ :=
    ext_cft_artin (K := B) (L := T)
  have hc := finite_euler_correction_analytic T (s7BadTopPrimes B T m)
  refine ⟨m, Art, hsurj, hFrob, ?_, ?_, ?_⟩
  · change AnalyticOn ℂ (fun s : ℂ =>
      ∏ w ∈ s7BadTopPrimes B T m,
        (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹) {s : ℂ | 0 < s.re}
    exact hc.1
  · change ∀ s : ℂ, 0 < s.re →
      (∏ w ∈ s7BadTopPrimes B T m,
        (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹) ≠ 0
    exact hc.2
  · intro s hs
    exact upstairs_euler_product_identity m Art hFrob hs

end ArtinPrimitiveRoots.Splitting
end
