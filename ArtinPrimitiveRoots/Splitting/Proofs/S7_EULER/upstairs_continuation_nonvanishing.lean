import ArtinPrimitiveRoots.Hecke.Boundary
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.dedekindZetaSharp_meromorphic
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.dedekindZetaSharp_eq

set_option autoImplicit false
open scoped NumberField BigOperators
open scoped Topology
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke
open ArtinPrimitiveRoots.HeckeBoundary
open Filter

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
  classical
  let H : Set ℂ := {s | 1 - δ₀ < s.re}
  have hδpos : 0 < δ₀ := by norm_num [δ₀]
  have hδlt : δ₀ < 1 := by norm_num [δ₀]
  have hHpos : H ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    dsimp [H] at hs ⊢
    linarith
  have hpre : IsPreconnected H := by
    exact (convex_halfSpace_re_gt (1 - δ₀)).isPreconnected
  have htwo : (2 : ℂ) ∈ H := by
    dsimp [H]
    norm_num [δ₀]

  have hboundary : ∀ (χ : (compositumField a q ≃ₐ[heckeBaseField q]
      compositumField a q) →* ℂˣ), ∃ U : Set ℂ, ∃ Λ : ℂ → ℂ,
      IsOpen U ∧ H ⊆ U ∧ MeromorphicOn Λ U ∧
      (∀ s : ℂ, 1 < s.re → Λ s = LSeriesRay (χ.comp Art) s) ∧
      (∀ s : ℂ, 1 - δ₀ < s.re → meromorphicOrderAt Λ s ≤ 0) := by
    intro χ
    simpa only [heckeBaseField] using
      (ArtinPrimitiveRoots.HeckeBoundary.thm_hecke_zero_free (12 * q)
        (dvd_mul_right 12 q) m (χ.comp Art))
  choose U Λ hUopen hUsub hΛmer hΛeq hΛord using hboundary

  let Z : ℂ → ℂ := fun s => E s * ∏ χ ∈ X, Λ χ s
  have hEanalytic : ∀ s ∈ H, AnalyticAt ℂ E s := by
    intro s hs
    apply hE.analyticAt
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hHpos hs)
  have hΛprod : MeromorphicOn (fun s => ∏ χ ∈ X, Λ χ s) H := by
    apply MeromorphicOn.fun_prod
    intro χ hχ
    exact (hΛmer χ).mono_set (fun s hs => hUsub χ hs)
  have hZmer : MeromorphicOn Z H := by
    change MeromorphicOn (fun s => E s * ∏ χ ∈ X, Λ χ s) H
    exact fun s hs => (hEanalytic s hs).meromorphicAt.mul (hΛprod s hs)
  have hsharp : Meromorphic (dedekindZetaSharp (compositumField a q)) :=
    dedekindZetaSharp_meromorphic (compositumField a q)
  have hDmer : MeromorphicOn
      (fun s => Z s - dedekindZetaSharp (compositumField a q) s) H := by
    exact hZmer.sub (fun s _ => hsharp s)

  have hDtwo : meromorphicOrderAt
      (fun s => Z s - dedekindZetaSharp (compositumField a q) s) 2 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hnear : (fun s : ℂ => Z s - dedekindZetaSharp (compositumField a q) s) =ᶠ[𝓝 2] 0 := by
      filter_upwards [
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)]
        with s hs
      have hprod : (∏ χ ∈ X, Λ χ s) =
          ∏ χ ∈ X, LSeriesRay (χ.comp Art) s := by
        apply Finset.prod_congr rfl
        intro χ hχ
        exact hΛeq χ s hs
      have hsharp_eq := dedekindZetaSharp_eq (compositumField a q) hs
      change E s * (∏ χ ∈ X, Λ χ s) - dedekindZetaSharp (compositumField a q) s = 0
      rw [hprod, hsharp_eq, hEuler s hs]
      ring
    exact hnear.filter_mono nhdsWithin_le_nhds

  have hDorder : ∀ s ∈ H,
      meromorphicOrderAt
        (fun z => Z z - dedekindZetaSharp (compositumField a q) z) s = ⊤ := by
    intro s hs
    exact hDmer.meromorphicOrderAt_eq_top_of_isPreconnected hpre htwo hs hDtwo

  refine ⟨?_, ?_⟩
  · intro χ hχ
    exact ⟨U χ, Λ χ, hUopen χ, hUsub χ, hΛmer χ, hΛeq χ, hΛord χ⟩
  · intro s hs
    have hsH : s ∈ H := hs
    have hDnear : (fun z => Z z - dedekindZetaSharp (compositumField a q) z) =ᶠ[𝓝[≠] s] 0 :=
      meromorphicOrderAt_eq_top_iff.mp (hDorder s hsH)
    have hloc : Z =ᶠ[𝓝[≠] s] dedekindZetaSharp (compositumField a q) := by
      filter_upwards [hDnear] with z hz
      exact sub_eq_zero.mp hz
    have horder := meromorphicOrderAt_congr hloc
    have hEne' : E s ≠ 0 := hEne s (hHpos hsH)
    have hEord : meromorphicOrderAt E s = 0 := by
      rw [(hEanalytic s hsH).meromorphicOrderAt_eq,
        (analyticOrderAt_eq_zero).mpr (Or.inr hEne')]
      simp
    have hsum : (∑ χ ∈ X, meromorphicOrderAt (Λ χ) s) ≤ 0 := by
      apply Finset.sum_nonpos
      intro χ hχ
      exact hΛord χ s hs
    have hZorder : meromorphicOrderAt Z s =
        meromorphicOrderAt E s + ∑ χ ∈ X, meromorphicOrderAt (Λ χ) s := by
      calc
        meromorphicOrderAt Z s =
            meromorphicOrderAt (E * (fun z => ∏ χ ∈ X, Λ χ z)) s := rfl
        _ = meromorphicOrderAt E s +
            meromorphicOrderAt (fun z => ∏ χ ∈ X, Λ χ z) s :=
          meromorphicOrderAt_mul (hEanalytic s hsH).meromorphicAt (hΛprod s hsH)
        _ = meromorphicOrderAt E s + ∑ χ ∈ X, meromorphicOrderAt (Λ χ) s := by
          rw [meromorphicOrderAt_fun_prod (fun χ hχ => hΛmer χ s (hUsub χ hsH))]
    rw [← horder, hZorder, hEord]
    simpa using hsum

end ArtinPrimitiveRoots.Splitting
end
