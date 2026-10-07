import ArtinPrimitiveRoots.TypeII.Defs
import ArtinPrimitiveRoots.Ext.TypeIIInputs

/-! The abstract marked coefficient transfer from `08-type-ii.tex:99-251`. -/

namespace ArtinPrimitiveRoots.TypeII

open Classical

/-- Convexity in the natural order, expressing that a set of natural numbers is an interval.
This is correction 2 from review lane `rev-b`. -/
def IsNatInterval (I : Set ℕ) : Prop :=
  ∀ ⦃m n k : ℕ⦄, m ∈ I → n ∈ I → min m n ≤ k → k ≤ max m n → k ∈ I

/-- `t2:band-mass`, 08-type-ii.tex:54-56 and 12-construction.tex:29-31. For each fixed
exponent `a∈(0,1)`, the reciprocal-prime mass of its band tends to `log 2`. -/
theorem band_mass (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |bandMass x a - Real.log 2| ≤ ε ∧ 0 < bandMass x a := by
  sorry

/-- A scale-varying family of first-variable coefficients, as in the hypothesis
`eq:type-ii-long-coefficient-interface`. Correction 2 from review lane `rev-b` records that the
first-variable set is an interval. The family-specific asymptotic threshold is the correction from
refutation lane `sol-gate-b`. -/
structure CoefficientFamily (δ C c₁ c₂ : ℝ) where
  /-- First scale at which the family is required to satisfy its asymptotic bounds. -/
  xMin : ℝ := 2
  xMin_ge_two : 2 ≤ xMin := by norm_num
  Hm : ℝ → ℝ
  Hn : ℝ → ℝ
  interval : ℝ → Set ℕ
  alpha : ℝ → ℕ → ℂ
  interval_property : ∀ x, IsNatInterval (interval x)
  scales : ∀ x, xMin ≤ x → Real.rpow x δ ≤ Hm x ∧ Real.rpow x δ ≤ Hn x ∧
    c₁ * x ≤ Hm x * Hn x ∧ Hm x * Hn x ≤ c₂ * x
  interval_bounds : ∀ x, xMin ≤ x → ∀ m ∈ interval x, Hm x ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm x
  rough_support : ∀ x, xMin ≤ x → ∀ m, alpha x m ≠ 0 →
    m ∈ interval x ∧ roughAbove m (roughCutoff x)
  coefficient_bound : ∀ x, xMin ≤ x → ∀ m ∈ interval x,
    ‖alpha x m‖ ≤ Real.rpow (Real.log x) C

/-- Finite interpretation of the interval in a coefficient family. -/
noncomputable def familyTerms {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x : ℝ) : Finset ℕ :=
  (dyadicIntegers (family.Hm x)).filter (fun m => m ∈ family.interval x)

/-- The long Dirichlet-polynomial hypothesis on the first-variable coefficients. Its interval
domain is the one in correction 2 from review lane `rev-b`; its threshold is the asymptotic
correction from refutation lane `sol-gate-b`. -/
def HasLongCoefficientCancellation {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) : Prop :=
  ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
    ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧ family.xMin ≤ x₀ ∧
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


end ArtinPrimitiveRoots.TypeII
