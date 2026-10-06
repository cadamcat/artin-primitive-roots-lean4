import Mathlib

/-!
# Primes with controlled predecessors (paper: Proposition `prop:controlled`)

Source: `01a-reduction.tex`, lines 18–41; proved in `12-construction.tex`.
Frozen interface: the statement below is consumed by `thm_main`.
-/

namespace ArtinPrimitiveRoots

/-- **Proposition `prop:controlled`.** Let `M` be a positive multiple of `8`, `c ∈ {2, 4}`, and `u`
an integer with `(u, M) = 1`, `c ∣ u - 1` and `((u - 1)/c, M/c) = 1`. For every sufficiently large
real `x` there are `≫_{M,c,u} x / (log x)²` primes `p ∈ (x, 2x)` with `p ≡ u (mod M)` and
`p - 1 = c r Q`, where `Q > x^0.9` is prime and every prime divisor of the positive integer `r` lies
in `(exp((log x)^0.1), exp((log x)^0.3))`. -/
theorem prop_controlled (M : ℕ) (hM0 : 0 < M) (hM : 8 ∣ M) (c : ℕ) (hc : c = 2 ∨ c = 4)
    (u : ℤ) (hu : Int.gcd u M = 1) (hcu : (c : ℤ) ∣ u - 1)
    (hcu' : Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      C * x / Real.log x ^ 2 ≤
        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ (p : ℤ) ≡ u [ZMOD M] ∧
            ∃ r Q : ℕ, p - 1 = c * r * Q ∧ Q.Prime ∧ x ^ (9 / 10 : ℝ) < (Q : ℝ) ∧ 0 < r ∧
              ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ r →
                Real.exp (Real.log x ^ (1 / 10 : ℝ)) < (ℓ : ℝ) ∧
                  (ℓ : ℝ) < Real.exp (Real.log x ^ (3 / 10 : ℝ))} : Set ℕ).ncard : ℝ) := by
  sorry

end ArtinPrimitiveRoots
