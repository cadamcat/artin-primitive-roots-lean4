import ArtinPrimitiveRoots.Spec.Smoothing
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_API.Existence
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_API.Uniqueness
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CUSP.ResidueLinearCombination

/-! Consumer API nodes C2--C3. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- C2 `spec:api` — P-SPEC.md:249, 431–433. The consumer continuation exists, is unique on a
common continuation domain, and restricts to any smaller positive radius. -/
theorem C2_api (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (σ : SL(2,F)) (s₁ : ℝ)
    (h₀ : 0 < s₁) (h₁ : s₁ ≤ 1 / 2) :
    Nonempty (ContinuedEisenstein F Γ σ s₁) ∧
    (∀ d d' : ContinuedEisenstein F Γ σ s₁,
      (∀ s ∈ contDomain s₁ (min d.ε d'.ε), d.E s = d'.E s) ∧ d.res = d'.res) ∧
    (∀ d : ContinuedEisenstein F Γ σ s₁, ∀ ε' : ℝ, 0 < ε' → ε' ≤ d.ε →
      ∃ d' : ContinuedEisenstein F Γ σ s₁,
        d'.ε = ε' ∧ d'.E = d.E ∧ d'.res = d.res) := by
  refine ⟨exists_continuedEisenstein_core Γ hfree σ s₁ h₀ h₁, ?_⟩
  constructor
  · intro d d'
    exact continuedEisenstein_E_eq d d' h₁
  · intro d ε' hε hle
    exact ContinuedEisenstein.exists_restrict F d ε' hε hle

/-- C3 `spec:cuspidal` — P-SPEC.md:250, 435–440. A finite linear combination of continued
Eisenstein residues with every cusp constant term zero vanishes identically. -/
theorem C3_cuspidal (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (s₁ : ℝ) (h₀ : 0 < s₁) (h₁ : s₁ ≤ 1 / 2)
    {ι : Type} [Fintype ι] (σ : ι → SL(2,F))
    (d : ∀ i, ContinuedEisenstein F Γ (σ i) s₁) (c : ι → ℂ)
    (hct : ∀ (τ : SL(2,F)) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
      ∃ P : Set (InfinitePlace F → ℂ),
        IsAddFundamentalDomain (cuspTranslations F Γ τ) P ∧
          ∫ x in P, (∑ i, c i * (d i).res (τ • ptX' F x y)) = 0) :
    ∀ z, ∑ i, c i * (d i).res z = 0 := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
