import ArtinPrimitiveRoots.Splitting.Algebraic
import ArtinPrimitiveRoots.Hecke.Boundary

/-!
# §7 descent of the zero-free region

Blueprint nodes `sp:upstairs-factor`, `sp:quotient-factor`, and `spl:kummer-zero-free`;
source `07-splitting.tex:70-99`.
-/

set_option autoImplicit false

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Splitting

open ArtinPrimitiveRoots.Ext.SplittingInputs
open ArtinPrimitiveRoots.Hecke
open ArtinPrimitiveRoots.HeckeBoundary
open ClassFieldTheory

/-- A meromorphic function has no zero in the zero-free half-plane when its order is nonpositive.
This is the blueprint's N10 convention, which remains meaningful at poles. -/
def HasNoZeroInHalfPlane (G : ℂ → ℂ) (δ : ℝ) : Prop :=
  ∀ s : ℂ, 1 - δ < s.re → meromorphicOrderAt G s ≤ 0

/-- **`sp:upstairs-factor`**, `07-splitting.tex:78-95`. CFT supplies the ray-class Artin map;
the Hecke boundary supplies a zero-free continuation for every pulled-back character. The
correction `E` is recorded by the analytic and nonvanishing properties used in the descent;
`LSeriesRay_change_modulus` and the Hecke Euler product supply its finite-factor bookkeeping, so no
new Euler-factor external node is introduced. -/
theorem sp_upstairs_factor (a : ℤ) (q : ℕ) [NeZero q] [NeZero (12 * q)]
    (hq : q.Prime) (hq5 : 5 ≤ q)
    [AbelianExtensionData (heckeBaseField q) (compositumField a q)] :
    ∃ (m : RayClassModulus (heckeBaseField q))
      (Art : RayClassGroup m →* (compositumField a q ≃ₐ[heckeBaseField q] compositumField a q))
      (E : ℂ → ℂ)
      (X : Finset ((compositumField a q ≃ₐ[heckeBaseField q] compositumField a q) →* ℂˣ)),
      Function.Surjective Art ∧ FrobeniusNormalizedArtinMap m Art ∧
      AnalyticOn ℂ E {s : ℂ | 0 < s.re} ∧
      (∀ s : ℂ, 0 < s.re → E s ≠ 0) ∧
      (∀ s : ℂ, 1 < s.re →
        NumberField.dedekindZeta (compositumField a q) s =
          E s * ∏ χ ∈ X, LSeriesRay (χ.comp Art) s) ∧
      (∀ χ : (compositumField a q ≃ₐ[heckeBaseField q] compositumField a q) →* ℂˣ,
        χ ∈ X) ∧
      (∀ χ : (compositumField a q ≃ₐ[heckeBaseField q] compositumField a q) →* ℂˣ,
        χ ∈ X →
        ∃ U : Set ℂ, ∃ Λ : ℂ → ℂ,
          IsOpen U ∧ {s : ℂ | 1 - δ₀ < s.re} ⊆ U ∧ MeromorphicOn Λ U ∧
          (∀ s : ℂ, 1 < s.re → Λ s = LSeriesRay (χ.comp Art) s) ∧
          (∀ s : ℂ, 1 - δ₀ < s.re → meromorphicOrderAt Λ s ≤ 0)) ∧
    HasNoZeroInHalfPlane (dedekindZetaSharp (compositumField a q)) δ₀ := by
  sorry

/-- **`sp:quotient-factor`**, `07-splitting.tex:83-97`. For the abelian extension over `K_q`,
the nontrivial characters are quadratic. H1 (`LSeriesRay_entire`) makes their Hecke factors
holomorphic; the Euler-factor identity and change-of-modulus formula give a holomorphic quotient
`Q = ζ_{K̃_q}^♮/ζ_{K_q}^♮` on the zero-free half-plane. -/
theorem sp_quotient_factor (a : ℤ) (q : ℕ) [NeZero q] [NeZero (12 * q)]
    (hq : q.Prime) (hq5 : 5 ≤ q)
    [IsTotallyComplex (kummerField a q)]
    [AbelianExtensionData (kummerField a q) (compositumField a q)] :
    ∃ Q : ℂ → ℂ,
      DifferentiableOn ℂ Q {s : ℂ | 1 - δ₀ < s.re} ∧
      (∀ s : ℂ, 1 - δ₀ < s.re →
        dedekindZetaSharp (compositumField a q) s =
          dedekindZetaSharp (kummerField a q) s * Q s) := by
  sorry

/-- **`spl:kummer-zero-free`**, `07-splitting.tex:70-98`. Descend the zero-free region through
the holomorphic quotient: a zero of `ζ_{K_q}^♮` would be a zero of the upstairs function. The
statement uses meromorphic orders so that poles carry no misleading point values. -/
theorem spl_kummer_zero_free (a : ℤ) (q : ℕ) [NeZero q] [NeZero (12 * q)]
    (hq : q.Prime) (hq5 : 5 ≤ q)
    (hTop : HasNoZeroInHalfPlane (dedekindZetaSharp (compositumField a q)) δ₀)
    (Q : ℂ → ℂ) (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 - δ₀ < s.re})
    (hfactor : ∀ s : ℂ, 1 - δ₀ < s.re →
      dedekindZetaSharp (compositumField a q) s =
        dedekindZetaSharp (kummerField a q) s * Q s) :
    HasNoZeroInHalfPlane (dedekindZetaSharp (kummerField a q)) δ₀ := by
  sorry

end ArtinPrimitiveRoots.Splitting

end
