import Mathlib

/-!
# A uniform bound for complete splitting (paper: Proposition `prop:splitting`)

Source: `01a-reduction.tex`, lines 50–63; proved in `07-splitting.tex` from Theorem
`thm:hecke-zero-free`. Frozen interface, consumed by `thm_main`.

The paper counts primes `p` that split completely in `K_q = ℚ(μ_q, a^{1/q})`. This interface uses
the elementary condition `q ∣ p - 1 ∧ a^{(p-1)/q} ≡ 1 (mod p)`, which by the splitting test
(`alg:splitting-test`) implies complete splitting in `K_q` (the condition already forces `p ∤ a q`),
so the statement below follows from the paper's.
-/

namespace ArtinPrimitiveRoots

/-- **Proposition `prop:splitting`**, elementary form. Fix an integer `a` with `|a| > 1` and put
`δ₀ = 10⁻⁶`. There are `C`, `q₀` and `X` such that for every real `x ≥ X` and every prime
`q ≥ q₀` with `q ≤ exp((log x)^0.3)`, the number of primes `p ∈ (x, 2x]` with `q ∣ p - 1` and
`a^{(p-1)/q} ≡ 1 (mod p)` is at most `C (x / (q (q - 1) log x) + x^{1-δ₀})`. -/
theorem prop_splitting (a : ℤ) (ha : 1 < |a|) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, q.Prime → q₀ ≤ q →
      (q : ℝ) ≤ Real.exp (Real.log x ^ (3 / 10 : ℝ)) →
        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ q ∣ p - 1 ∧
            (a : ZMod p) ^ ((p - 1) / q) = 1} : Set ℕ).ncard : ℝ) ≤
          C * (x / ((q : ℝ) * ((q : ℝ) - 1) * Real.log x) + x ^ (1 - (1 / 1000000 : ℝ))) := by
  sorry

end ArtinPrimitiveRoots
