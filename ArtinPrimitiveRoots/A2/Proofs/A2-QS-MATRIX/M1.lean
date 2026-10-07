import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».Defs

/-!
# A2-QS-MATRIX, part M1: uniform ideal counts, divisor bounds, squarefree parts, tails

Guide: `runs/lanes/sol-thin-found/PROOFS.md:307-326`.  Hints: Mathlib
`Ideal.finite_setOfPred_absNorm_le`, the ideal-count asymptotic
`NumberField.Ideal.tendsto_norm_le_div_atTop` (`M/NumberTheory/NumberField/Ideal/Asymptotics.lean`)
may replace the Euler-factor comparison for `qs_ideal_count_M1`; divisor bound by
`τ(I) = ∏(e_P + 1)` with finitely many small primes.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- M1 (IMPL): `#{I : N I ≤ X} ≪_η X^{1+η}` for `X ≥ 1` (found:309-310). -/
theorem qs_ideal_count_M1 (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      (((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊).toFinset.card : ℕ) : ℝ) ≤
        C * X ^ (1 + η) := by
  sorry

/-- M1 (IMPL): divisor bound `τ(I) ≪_η (N I)^η` (found:311-313). -/
theorem qs_divisor_bound_M1 (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 K), I ≠ ⊥ →
      (((qsDivisors I).card : ℕ) : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ η := by
  sorry

/-- M1 (IMPL): unique squarefree decomposition `I = a₀ b²` (found:314-316). -/
theorem qs_squarefree_decomposition_M1 (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃! p : Ideal (𝓞 K) × Ideal (𝓞 K), Squarefree p.1 ∧ I = p.1 * p.2 ^ 2 := by
  sorry

/-- M1 (IMPL): `qsSfNorm` is the norm of the squarefree part (consistency with
`qs_squarefree_decomposition_M1`). -/
theorem qs_sfNorm_eq_M1 (a₀ b : Ideal (𝓞 K)) (ha₀ : Squarefree a₀) (hb : b ≠ ⊥) :
    qsSfNorm (a₀ * b ^ 2) = Ideal.absNorm a₀ := by
  sorry

/-- M1 (IMPL): rapid-decay tails over ideals (found:320-324): if `‖h x‖ ≤ C_A x^{-A}` for
`x ≥ 1` and `A > 1 + η`, then `Σ_{N I > T} ‖h(N I / X)‖ ≪ C_A X^A T^{1+η-A}` for
`T ≥ max 1 X`; the constant depends only on `K, η, A`. -/
theorem qs_tail_bound_M1 (η A : ℝ) (hη : 0 < η) (hA : 1 + η < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℂ) (CA X T : ℝ), 0 ≤ CA → 0 < X → max 1 X ≤ T →
      (∀ x : ℝ, 1 ≤ x → ‖h x‖ ≤ CA * x ^ (-A)) →
        Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ T < (Ideal.absNorm I : ℝ)} =>
          ‖h ((Ideal.absNorm I.1 : ℝ) / X)‖) ∧
        ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ T < (Ideal.absNorm I : ℝ)},
            ‖h ((Ideal.absNorm I.1 : ℝ) / X)‖ ≤
          C * CA * X ^ A * T ^ (1 + η - A) := by
  sorry

end ArtinPrimitiveRoots.A2
