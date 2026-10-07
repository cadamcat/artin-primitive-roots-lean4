import ArtinPrimitiveRoots.Hecke.Boundary
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.dedekindZetaSharp_meromorphic
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.dedekindZetaSharp_eq

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke
open ArtinPrimitiveRoots.HeckeBoundary

/-- Zero-free Hecke continuations transfer through a finite Euler factorization.
Guide: ../sol-thin-s7/PROOFS.md:435–474. Uses `thm_hecke_zero_free`, the sharp-zeta
dictionary, and the meromorphic identity principle. Feeds `sp_upstairs_factor`.
No pointwise equality at poles is asserted. -/
theorem upstairs_continuation_nonvanishing (a : ℤ) (q : ℕ)
    [NeZero q] [NeZero (12 * q)]
    [AbelianExtensionData (heckeBaseField q) (compositumField a q)]
    (m : RayClassModulus (heckeBaseField q))
    (Art : RayClassGroup m →*
      (compositumField a q ≃ₐ[heckeBaseField q] compositumField a q))
    (E : ℂ → ℂ)
    (X : Finset ((compositumField a q ≃ₐ[heckeBaseField q]
      compositumField a q) →* ℂˣ))
    (hE : AnalyticOn ℂ E {s : ℂ | 0 < s.re})
    (hEne : ∀ s : ℂ, 0 < s.re → E s ≠ 0)
    (hEuler : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta (compositumField a q) s =
        E s * ∏ χ ∈ X, LSeriesRay (χ.comp Art) s) :
    (∀ χ : (compositumField a q ≃ₐ[heckeBaseField q] compositumField a q) →* ℂˣ,
      χ ∈ X → ∃ U : Set ℂ, ∃ Λ : ℂ → ℂ,
        IsOpen U ∧ {s : ℂ | 1 - δ₀ < s.re} ⊆ U ∧ MeromorphicOn Λ U ∧
        (∀ s : ℂ, 1 < s.re → Λ s = LSeriesRay (χ.comp Art) s) ∧
        (∀ s : ℂ, 1 - δ₀ < s.re → meromorphicOrderAt Λ s ≤ 0)) ∧
    (∀ s : ℂ, 1 - δ₀ < s.re →
      meromorphicOrderAt (dedekindZetaSharp (compositumField a q)) s ≤ 0) := by
  sorry

end ArtinPrimitiveRoots.Splitting
end
