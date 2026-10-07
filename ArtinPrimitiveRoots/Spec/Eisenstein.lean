import ArtinPrimitiveRoots.Spec.Defs

/-! Eisenstein-series nodes E1--E7. This first stage states E1--E2. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- E1 `spec:eis-def` — P-SPEC.md:237. The representative formula for an Eisenstein term and
injectivity of its bottom-row unit orbit map. -/
theorem E1_eis_def :
    (∀ (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (s : ℂ) (z : X F) (γ : Γ),
      eisTerm F Γ σ s z (Quotient.mk _ γ) =
        ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ (1 + 2 * s)) ∧
    (∀ (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ σ' : SL(2,F)),
      ∃ D : ℕ, 0 < D ∧
        (∀ q : CuspCosets F Γ σ,
          let r := bottomRow F (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * σ')
          r ≠ (0, 0) ∧ HasDenominatorBound F D r.1 ∧ HasDenominatorBound F D r.2) ∧
        ∀ q q' : CuspCosets F Γ σ,
          unitAssociatedRows F
            (bottomRow F (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * σ'))
            (bottomRow F (σ⁻¹ * toSLF F ((q'.out : Γ) : SL(2,𝓞 F)) * σ')) → q = q') := by
  sorry

/-- E2 `spec:eis-converge` — P-SPEC.md:238, 379–383. The frozen locally uniform majorant and
invariance statements, together with holomorphy in the normalized parameter on `Re s > 1/2`. -/
theorem E2_eis_converge (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) :
    (∀ (K : Set (X F)), IsCompact K → ∀ σ₀ σ₁ : ℝ, 1 / 2 < σ₀ →
      ∃ m : CuspCosets F Γ σ → ℝ, Summable m ∧
        ∀ z ∈ K, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → ∀ q,
          ‖eisTerm F Γ σ s z q‖ ≤ m q) ∧
    (∀ (s : ℂ), 1 / 2 < s.re → ∀ (γ : SL(2,𝓞 F)), γ ∈ Γ → ∀ z : X F,
      eisSeries F Γ σ s (γ • z) = eisSeries F Γ σ s z) ∧
    (∀ z : X F,
      AnalyticOnNhd ℂ (fun s => eisSeries F Γ σ s z) {s : ℂ | 1 / 2 < s.re}) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
