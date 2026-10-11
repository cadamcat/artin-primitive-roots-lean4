import ArtinPrimitiveRoots.TypeII.PD.MajorArcs

/-!
# The marked coefficient transfer (`lem:marked-coefficient-transfer`)

Moved here from `TypeII/Marked.lean` on 2026-10-07 (statement unchanged): it is proved from the PoissonDirichlet chain
(`PD.completion`), which imports `Marked.lean`, so it must come after that chain.
-/

namespace ArtinPrimitiveRoots.TypeII

open Classical

/-- `lem:marked-coefficient-transfer` — `08-type-ii.tex:99-251`. For any coefficient
family satisfying the long Dirichlet-polynomial interface, the marked bilinear form has arbitrary
logarithmic saving once the number of marked bands is sufficiently large. The lower bound on `K`
is chosen after the fixed scale constants `c₁ ≤ c₂` and before the band exponents and the family (2026-10-07: the
earlier form chose it before `c₁, c₂`, which the PD chain does not provide and no consumer needs). Requires ordered scale constants and an interval coefficient domain. -/
theorem marked_coefficient_transfer
    (δ C Dstar q_d c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁₂ : c₁ ≤ c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
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
  obtain ⟨K₀, hcompletion⟩ :=
    PD.completion δ C Dstar q_d c₁ c₂ hδ hC hD hqd₀ hqd₁ hc₁ hc₂
  refine ⟨K₀, ?_⟩
  intro K hK family hfamily a ha
  exact hcompletion K hK a ha family hfamily

end ArtinPrimitiveRoots.TypeII
