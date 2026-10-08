import ArtinPrimitiveRoots.Sieve.Block

/-! A small interface wrapper for applying the upper half of `lem_block` when a pointwise
approximation to each sieve intersection is already available. -/

namespace ArtinPrimitiveRoots.Construction.Proofs.C4

open Classical

theorem blockSieve_upper_of_error_bound {α : Type} [DecidableEq α]
    (A : Finset α) (wt : α → ℝ) (P : Finset ℕ) (bad : ℕ → α → Prop)
    (X z η C₀ : ℝ) (g : ℕ → ℝ) (err : Finset ℕ → ℝ)
    (hwt : ∀ a ∈ A, 0 ≤ wt a)
    (hz : 2 ≤ z)
    (hprime : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z)
    (hX : 0 ≤ X)
    (hη : 0 < η) (hC₀ : 0 < C₀)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 - η)
    (hblock : ∀ v : ℝ, 1 < v →
      ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀)
    (hErr : ∀ D ∈ P.powerset.filter
        (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
      |(∑ a ∈ A with ∀ p ∈ D, bad p a, wt a) - X * ∏ p ∈ D, g p| ≤ err D) :
    ∃ K : ℝ, 0 < K ∧
      (∑ a ∈ A with ∀ p ∈ P, ¬ bad p a, wt a) ≤
        K * (X * ∏ p ∈ P, (1 - g p)) +
        K * ∑ D ∈ P.powerset.filter
          (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10), err D := by
  obtain ⟨K, hK, H₀, hBlock⟩ := ArtinPrimitiveRoots.Sieve.lem_block η C₀ hη
  refine ⟨K, hK, ?_⟩
  have hUpper := (hBlock α A wt hwt z hz P hprime bad X g hX hg hblock).2
  calc
    (∑ a ∈ A with ∀ p ∈ P, ¬ bad p a, wt a) ≤
        K * (X * ∏ p ∈ P, (1 - g p)) +
          K * ∑ D ∈ P.powerset.filter
            (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
              |(∑ a ∈ A with ∀ p ∈ D, bad p a, wt a) - X * ∏ p ∈ D, g p| := hUpper
    _ ≤ K * (X * ∏ p ∈ P, (1 - g p)) +
          K * ∑ D ∈ P.powerset.filter
            (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10), err D := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ hK.le
      apply Finset.sum_le_sum
      intro D hD
      exact hErr D hD

end ArtinPrimitiveRoots.Construction.Proofs.C4
