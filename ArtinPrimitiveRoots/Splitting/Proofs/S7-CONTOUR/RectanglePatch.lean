import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpPrincipalParts
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroWindows
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».FinitePatch

set_option autoImplicit false

open scoped NumberField Topology BigOperators
open Filter NumberField

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting

/-- Subtract the endpoint and nontrivial-zero principal parts on the closed shifted rectangle. -/
theorem sharp_weighted_rectangle_patch (K : Type*) [Field K] [NumberField K]
    (W : ℂ → ℂ) (hW : Differentiable ℂ W) (a b : ℝ) :
    ∃ (S : Finset ℂ) (G : ℂ → ℂ),
      (∀ p : ℂ, p ∈ S ↔ p = 0 ∨ p = 1 ∨
        (p ∈ nontrivialZeros K ∧ a ≤ p.im ∧ p.im ≤ b)) ∧
      AnalyticOnNhd ℂ G {s : ℂ | (-1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 2 ∧
        a ≤ s.im ∧ s.im ≤ b} ∧
      (∀ s : ℂ, s ∉ S → G s = dedekindZetaLogDerivative K s * W s -
        ∑ p ∈ S, (if p = 1 then W 1 else if p = 0 then
          -((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) * W 0
          else -(zeroMultiplicity K p : ℂ) * W p) / (s - p)) := by
  classical
  let Z : Set ℂ := {ρ | ρ ∈ nontrivialZeros K ∧ a ≤ ρ.im ∧ ρ.im ≤ b}
  have hZ : Z.Finite := zero_strip_finite K a b
  have hfinite : (({0} : Set ℂ) ∪ {1} ∪ Z).Finite :=
    ((Set.finite_singleton 0).union (Set.finite_singleton 1)).union hZ
  let S : Finset ℂ := hfinite.toFinset
  have hS (p : ℂ) : p ∈ S ↔ p = 0 ∨ p = 1 ∨
      (p ∈ nontrivialZeros K ∧ a ≤ p.im ∧ p.im ≤ b) := by
    change p ∈ hfinite.toFinset ↔ _
    rw [hfinite.mem_toFinset]
    simp only [Set.mem_union, Set.mem_singleton_iff, or_assoc, Z, Set.mem_setOf_eq]
  let U : Set ℂ := {s | (-1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 2 ∧ a ≤ s.im ∧ s.im ≤ b}
  let H : ℂ → ℂ := fun s => dedekindZetaLogDerivative K s * W s
  let c : ℂ → ℂ := fun p => if p = 1 then W 1 else if p = 0 then
    -((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) * W 0
    else -(zeroMultiplicity K p : ℂ) * W p
  have hreg : ∀ s ∈ U, s ∉ S → AnalyticAt ℂ H s := by
    intro s hsU hsS
    have hs₀ : s ≠ 0 := by
      intro heq
      exact hsS ((hS s).mpr (Or.inl heq))
    have hs₁ : s ≠ 1 := by
      intro heq
      exact hsS ((hS s).mpr (Or.inr (Or.inl heq)))
    have hxi : dedekindXi K s ≠ 0 := by
      intro hzero
      have hz : s ∈ nontrivialZeros K := (xi_zero_dictionary K).1 s |>.mp hzero
      exact hsS ((hS s).mpr (Or.inr (Or.inr ⟨hz, hsU.2.2.1, hsU.2.2.2⟩)))
    have hsre : -1 < s.re := by linarith only [hsU.1]
    exact (sharp_regular_of_re_gt_neg_one K s hsre hs₀ hs₁ hxi).2.2.mul (hW.analyticAt s)
  have hcoef := sharp_weighted_principal_parts K W hW
  have hpart : ∀ p ∈ S, ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧
      ∀ᶠ s in 𝓝[≠] p, H s = c p / (s - p) + R s := by
    intro p hp
    rcases (hS p).mp hp with hp₀ | hp₁ | hpz
    · subst p
      obtain ⟨R, hR, hlocal⟩ := hcoef.2.1
      refine ⟨R, hR, ?_⟩
      filter_upwards [hlocal] with s hs
      simpa [H, c] using hs
    · subst p
      obtain ⟨R, hR, hlocal⟩ := hcoef.1
      refine ⟨R, hR, ?_⟩
      filter_upwards [hlocal] with s hs
      simpa [H, c] using hs
    · have hp₀ : p ≠ 0 := by
        intro heq
        have hpos := hpz.1.1
        simp only [heq, Complex.zero_re, lt_self_iff_false] at hpos
      have hp₁ : p ≠ 1 := by
        intro heq
        have hlt := hpz.1.2.1
        simp only [heq, Complex.one_re, lt_self_iff_false] at hlt
      obtain ⟨R, hR, hlocal⟩ := hcoef.2.2 p hpz.1
      refine ⟨R, hR, ?_⟩
      filter_upwards [hlocal] with s hs
      simpa only [H, c, if_neg hp₁, if_neg hp₀] using hs
  obtain ⟨G, hG, hEq⟩ := finite_principal_parts_patch H S c U hreg hpart
  refine ⟨S, G, hS, hG, ?_⟩
  intro s hs
  exact hEq s hs

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
