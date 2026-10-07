import ArtinPrimitiveRoots.TypeII.Defs
import ArtinPrimitiveRoots.Ext.TypeIIInputs

/-! The abstract marked coefficient transfer from `08-type-ii.tex:99-251`. -/

namespace ArtinPrimitiveRoots.TypeII

open Classical

/-- `t2:band-mass`, 08-type-ii.tex:54-56 and 12-construction.tex:29-31. For each fixed
exponent `a∈(0,1)`, the reciprocal-prime mass of its band tends to `log 2`. -/
theorem band_mass (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |bandMass x a - Real.log 2| ≤ ε ∧ 0 < bandMass x a := by
  sorry

/-- A scale-varying family of first-variable coefficients, as in the hypothesis
`eq:type-ii-long-coefficient-interface`. -/
structure CoefficientFamily (δ C c₁ c₂ : ℝ) where
  Hm : ℝ → ℝ
  Hn : ℝ → ℝ
  interval : ℝ → Set ℕ
  alpha : ℝ → ℕ → ℂ
  scales : ∀ x, 2 ≤ x → Real.rpow x δ ≤ Hm x ∧ Real.rpow x δ ≤ Hn x ∧
    c₁ * x ≤ Hm x * Hn x ∧ Hm x * Hn x ≤ c₂ * x
  interval_bounds : ∀ x, 2 ≤ x → ∀ m ∈ interval x, Hm x ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm x
  rough_support : ∀ x, 2 ≤ x → ∀ m, alpha x m ≠ 0 →
    m ∈ interval x ∧ roughAbove m (roughCutoff x)
  coefficient_bound : ∀ x, 2 ≤ x → ∀ m ∈ interval x,
    ‖alpha x m‖ ≤ Real.rpow (Real.log x) C

/-- Finite interpretation of the interval in a coefficient family. -/
noncomputable def familyTerms {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x : ℝ) : Finset ℕ :=
  (dyadicIntegers (family.Hm x)).filter (fun m => m ∈ family.interval x)

/-- The long Dirichlet-polynomial hypothesis on the first-variable coefficients. -/
def HasLongCoefficientCancellation {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) : Prop :=
  ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
    ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
          ∀ χ : DirichletCharacter ℂ k, ∀ t : ℝ,
            |t| ≤ 2 * (family.Hm x * family.Hn x) * Real.rpow (Real.log x) B →
              ‖∑ m ∈ familyTerms family x,
                family.alpha x m * χ (m : ZMod k) *
                  Complex.exp (Complex.I * t * Real.log (m : ℝ))‖ /
                  family.Hm x ≤ C' * Real.rpow (Real.log x) (-A)

/-- The Type II bilinear form with marked weight.  All sums are over the explicitly bounded
dyadic ranges. -/
noncomputable def markedBilinearSum (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (q_d : ℝ)
    (F : ℕ → ℂ) (Hm Hn : ℝ) (I : Set ℕ) (alpha beta : ℕ → ℂ) : ℂ :=
  ∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
    ∑ n ∈ dyadicIntegers Hn,
      alpha m * beta n * F (m * n - 1) *
        (markedWeight x K a q_d (m * n - 1) : ℂ)

/-- `lem:marked-coefficient-transfer` — `08-type-ii.tex:99-251`. For any coefficient
family satisfying the long Dirichlet-polynomial interface, the marked bilinear form has arbitrary
logarithmic saving once the number of marked bands is sufficiently large. The lower bound on `K`
is chosen before the band exponents and is independent of those exponents and the family. -/
theorem marked_coefficient_transfer
    (δ C Dstar q_d : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
      ∀ family : CoefficientFamily δ C c₁ c₂,
        HasLongCoefficientCancellation family →
        ∀ a : Fin K → ℝ, ValidBands K a →
      ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ β : ℕ → ℂ,
            (∀ n, β n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
              roughAbove n (roughCutoff x)) →
            (∀ n ∈ dyadicIntegers (family.Hn x),
              ‖β n‖ ≤ Real.rpow (Real.log x) C) →
            ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
              ‖markedBilinearSum x K a q_d F (family.Hm x) (family.Hn x)
                (family.interval x) (family.alpha x) β‖ ≤
                  C' * (family.Hm x * family.Hn x) *
          Real.rpow (Real.log x) (-Dstar) := by
  sorry

end ArtinPrimitiveRoots.TypeII
