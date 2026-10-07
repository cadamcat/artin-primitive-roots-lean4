import ArtinPrimitiveRoots.Splitting.Analytic

/-!
# §7 transfer from prime ideals to rational primes

Blueprint node `sp:count-from-theta`; source `07-splitting.tex:227-246`.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Splitting

/-- **`sp:count-from-theta`**, `07-splitting.tex:227-246`. The smooth estimate and `spl:field-bounds`
bound primes that split completely in `K_q`, with constants independent of `q` in the range
`q ≤ exp((log x)^(3/10))`. The frozen elementary proposition follows by `alg:splitting-test` and
the short exclusion of primes dividing `a q`. -/
theorem sp_count_from_theta (a : ℤ) (ha : 1 < |a|) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, 5 ≤ q₀ ∧ ∃ X : ℝ, 2 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ (q : ℕ) [NeZero q], q.Prime → q₀ ≤ q →
        (q : ℝ) ≤ Real.exp (Real.log x ^ (3 / 10 : ℝ)) →
          (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
              splitsCompletely (kummerField a q) p} : Set ℕ).ncard : ℝ) ≤
            C * (x / ((q : ℝ) * ((q : ℝ) - 1) * Real.log x) +
              x ^ (1 - ArtinPrimitiveRoots.HeckeBoundary.δ₀)) := by
  sorry

end ArtinPrimitiveRoots.Splitting

end
