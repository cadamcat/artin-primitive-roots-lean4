import ArtinPrimitiveRoots.Construction.Proofs.C_TYPEII.UniformTransfer
import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.TypeII.Rough
import ArtinPrimitiveRoots.Ext.TypeIIInputs
import ArtinPrimitiveRoots.Construction.Proofs.c1.SupportHelpers

namespace ArtinPrimitiveRoots.Proofs.c_typeii_sol

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.Rough
open ArtinPrimitiveRoots.Construction

/-- The common bilinear estimate needed after character expansion and before Fourier inversion. -/
def TwistedEstimate (δ γ sMin sMax c₁ c₂ : ℝ) (M K : ℕ) (a : Fin K → ℝ) : Prop :=
  ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ,
      Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
      Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
      ∀ I : Set ℕ, IsNatInterval I →
        I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
      ∀ v : ℝ, |v| ≤ Real.log x → ∀ χM : DirichletCharacter ℂ M,
      ∀ beta : ℕ → ℂ,
        (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers Hn ∧ roughAbove n (roughCutoff x)) →
        (∀ n ∈ dyadicIntegers Hn, ‖beta n‖ ≤ Real.rpow (Real.log x) 2) →
      ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
        ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
          ∑ n ∈ dyadicIntegers Hn,
            (roughCoefficient x γ v m * χM (m : ZMod M)) *
              (beta n * χM (n : ZMod M)) * F (m * n - 1) *
                (markedWeight x K a (1 / 2 : ℝ) (m * n - 1) : ℂ)‖ ≤
          C' * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ)

/-- Character twisting and common cancellation witnesses preserve the transfer's common K₀. -/
theorem twisted_rough_type_ii
    (δ γ sMin sMax c₁ c₂ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hγs : γ < sMin) (hs : sMin < sMax) (hsMax : sMax < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁₂ : c₁ ≤ c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ M : ℕ, 0 < M →
      ∀ a : Fin K → ℝ, ValidBands K a → TwistedEstimate δ γ sMin sMax c₁ c₂ M K a := by
  sorry

/-- Fourier inversion and character orthogonality turn the common twisted estimate into
an estimate for the actual construction weight. -/
theorem fourier_progression
    (δ γ sMin sMax c₁ c₂ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hγs : γ < sMin) (hs : sMin < sMax) (hsMax : sMax < 1)
    (M c K : ℕ) (u : ℤ) (a : Fin K → ℝ) (ha : ValidBands K a)
    (hM : 0 < M) (hc : c = 2 ∨ c = 4) (hu : Int.gcd u M = 1)
    (Ψ : ℝ → ℝ) (hΨ₀ : ∀ y, 0 ≤ Ψ y) (hΨ₁ : ∀ y, Ψ y ≤ 1)
    (hsupp : Function.support Ψ ⊆ Set.Ioo 1 2)
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (htw : TwistedEstimate δ γ sMin sMax c₁ c₂ M K a) :
    ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Hm Hn : ℝ,
              Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
              c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
              Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
              Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
              ∀ I : Set ℕ, IsNatInterval I →
                I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
                ∀ b : ℕ → ℂ,
                  (∀ n, b n ≠ 0 → n ∈ dyadicIntegers Hn ∧
                    roughAbove n (roughCutoff x)) →
                  (∀ n ∈ dyadicIntegers Hn, ‖b n‖ ≤ 1) →
                  ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
                    ∑ n ∈ dyadicIntegers Hn,
                      ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) *
                        b n * (conWeight x M c u K a Ψ (m * n) : ℂ)‖ ≤
                    C₀ * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ) := by
  sorry

theorem construction_type_ii
    (δ γ sMin sMax c₁ c₂ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hγs : γ < sMin) (hs : sMin < sMax) (hsMax : sMax < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁₂ : c₁ ≤ c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ M c : ℕ, ∀ u : ℤ,
      ∀ a : Fin K → ℝ, ValidBands K a →
      0 < M → 8 ∣ M → (c = 2 ∨ c = 4) → c ∣ M →
      Int.gcd u M = 1 → (c : ℤ) ∣ u - 1 →
      Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1 →
      ∀ Ψ : ℝ → ℝ, (∀ y, 0 ≤ Ψ y) → (∀ y, Ψ y ≤ 1) →
        Function.support Ψ ⊆ Set.Ioo 1 2 →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → 0 < ∫ y in (1 : ℝ)..2, Ψ y →
        ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Hm Hn : ℝ,
              Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
              c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
              Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
              Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
              ∀ I : Set ℕ, IsNatInterval I →
                I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
                ∀ b : ℕ → ℂ,
                  (∀ n, b n ≠ 0 → n ∈ dyadicIntegers Hn ∧
                    roughAbove n (roughCutoff x)) →
                  (∀ n ∈ dyadicIntegers Hn, ‖b n‖ ≤ 1) →
                  ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
                    ∑ n ∈ dyadicIntegers Hn,
                      ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) *
                        b n * (conWeight x M c u K a Ψ (m * n) : ℂ)‖ ≤
                    C₀ * (Hm * Hn) * Real.rpow (Real.log x) (-6 : ℝ) := by
  obtain ⟨K₀, htw⟩ := twisted_rough_type_ii δ γ sMin sMax c₁ c₂
    hδ hγ hγs hs hsMax hc₁ hc₂ hc₁₂
  refine ⟨K₀, ?_⟩
  intro K hK M c u a ha hM hM8 hc hcM hu hcu hcu' Ψ hΨ₀ hΨ₁ hsupp hsmooth hint
  exact fourier_progression δ γ sMin sMax c₁ c₂ hδ hγ hγs hs hsMax M c K u a ha hM hc hu
    Ψ hΨ₀ hΨ₁ hsupp hsmooth (htw K hK M hM a ha)

end ArtinPrimitiveRoots.Proofs.c_typeii_sol
