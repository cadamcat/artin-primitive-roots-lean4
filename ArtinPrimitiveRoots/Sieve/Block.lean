import Mathlib

/-!
# A block sieve with bounded coefficients (paper: Lemma `lem:block`)

Source: `11-sieve.tex`, lines 9–144 (statement 16–49). Squarefree products `d` of primes in `P` are
indexed by the subsets `D ⊆ P` with `d = ∏_{p ∈ D} p`; the multiplicative `g` enters only through
`g(d) = ∏_{p ∈ D} g(p)`, and `A(d) = X' g(d) + E(d)` defines `E`.
-/

namespace ArtinPrimitiveRoots.Sieve

open Classical in
/-- **Lemma `lem:block`.** Let `A` be a finite set with nonnegative weights, `P` a finite set of
primes at most `z ≥ 2`, and for each `p ∈ P` a bad condition on `A`. For `D ⊆ P` let `A(D)` be the
weight of the objects bad at every `p ∈ D`, and `E(D) = A(D) - X' ∏_{p∈D} g(p)`. If
`0 ≤ g(p) ≤ 1 - η₀` on `P` and `∑_{p ∈ P, v < p ≤ v²} g(p) ≤ C₀` for every `v > 1`, then the
weight `S` of the objects avoiding all bad conditions satisfies, for every sufficiently large even
`H`, `S = X' ∏_{p∈P} (1 - g(p)) (1 + O(e^{-H})) + O(∑_{D, ∏ D ≤ z^{4H+2}} |E(D)|)`, and
`S ≪ X' ∏_{p∈P} (1 - g(p)) + ∑_{D, ∏ D ≤ z^{10}} |E(D)|`; the constants and the lower bound on
`H` depend only on `η₀, C₀`. -/
theorem lem_block (η₀ C₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ H₀ : ℕ, ∀ (α : Type) (A : Finset α) (wt : α → ℝ), (∀ a ∈ A, 0 ≤ wt a) →
      ∀ (z : ℝ), 2 ≤ z → ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) →
      ∀ (bad : ℕ → α → Prop) (X' : ℝ) (g : ℕ → ℝ), 0 ≤ X' →
      (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 - η₀) →
      (∀ v : ℝ, 1 < v → ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀) →
      let S : ℝ := ∑ a ∈ A with ∀ p ∈ P, ¬ bad p a, wt a
      let main : ℝ := X' * ∏ p ∈ P, (1 - g p)
      let E : Finset ℕ → ℝ := fun D => (∑ a ∈ A with ∀ p ∈ D, bad p a, wt a) - X' * ∏ p ∈ D, g p
      (∀ H : ℕ, Even H → H₀ ≤ H →
        |S - main| ≤ K * Real.exp (-(H : ℝ)) * main +
          K * ∑ D ∈ P.powerset with ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2), |E D|) ∧
      S ≤ K * main + K * ∑ D ∈ P.powerset with ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10, |E D| := by
  sorry

end ArtinPrimitiveRoots.Sieve
