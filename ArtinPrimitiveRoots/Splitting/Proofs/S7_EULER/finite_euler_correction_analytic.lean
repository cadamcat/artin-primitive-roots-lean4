import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.Defs

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- Finite deleted-prime corrections are analytic and nonzero on `Re s > 0`.
Guide: ../sol-thin-s7/PROOFS.md:398–417. Uses positive prime norms and complex
powers; feeds `upstairs_rhp_euler_identity` and `quotient_factor_of_euler_identity`. -/
theorem finite_euler_correction_analytic (T : Type*) [Field T] [NumberField T]
    (S : Finset (HeightOneSpectrum (𝓞 T))) :
    AnalyticOn ℂ (fun s : ℂ =>
      ∏ w ∈ S, (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹)
      {s : ℂ | 0 < s.re} ∧
    (∀ s : ℂ, 0 < s.re →
      (∏ w ∈ S, (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹) ≠ 0) := by
  sorry

end ArtinPrimitiveRoots.Splitting
end
