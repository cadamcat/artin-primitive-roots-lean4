import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

/-- Summing ordered batches with m prescribed coordinates pays one atom and one creation
factor per prescription. This upper bound drops the stronger individual performed-index flags. -/
theorem pd5_batch_length_atom_bound (B m : ℕ) (c Δ s : ℝ)
    (hc : 0 ≤ c) (hΔ : 0 ≤ Δ) (hs : 0 ≤ s) :
    (∑ l ∈ Finset.range (B + 1),
      if m ≤ l then c ^ l * Δ ^ m * s ^ (l - m) / (l.factorial : ℝ) else 0) ≤
        (c * Δ) ^ m * Real.exp (c * s) := by
  let g : ℕ → ℝ := fun k => (c * s) ^ k / (k.factorial : ℝ)
  have hg (k : ℕ) : 0 ≤ g k := by dsimp [g]; positivity
  have hterm (l : ℕ) (hml : m ≤ l) :
      c ^ l * Δ ^ m * s ^ (l - m) / (l.factorial : ℝ) ≤ (c * Δ) ^ m * g (l - m) := by
    have hfac : ((l - m).factorial : ℝ) ≤ (l.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.sub_le l m)
    have hpos : (0 : ℝ) < (l - m).factorial := by positivity
    have hnum : 0 ≤ c ^ l * Δ ^ m * s ^ (l - m) := by positivity
    calc
      _ ≤ c ^ l * Δ ^ m * s ^ (l - m) / ((l - m).factorial : ℝ) :=
        div_le_div_of_nonneg_left hnum hpos hfac
      _ = (c * Δ) ^ m * g (l - m) := by
        dsimp [g]
        have hpow : c ^ l = c ^ m * c ^ (l - m) := by
          have he : m + (l - m) = l := by omega
          simpa only [he] using pow_add c m (l - m)
        rw [hpow, mul_pow, mul_pow]
        ring
  have hreindex :
      (∑ l ∈ (Finset.range (B + 1)).filter (fun l => m ≤ l), g (l - m)) =
        ∑ k ∈ Finset.range (B + 1 - m), g k := by
    apply Finset.sum_bij (fun l _ => l - m)
    · intro l hl
      simp only [Finset.mem_filter, Finset.mem_range] at hl ⊢
      omega
    · intro l hl k hk he
      simp only [Finset.mem_filter, Finset.mem_range] at hl hk
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      refine ⟨k + m, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · omega
    · intro l hl
      rfl
  have hexp : (∑ k ∈ Finset.range (B + 1 - m), g k) ≤ Real.exp (c * s) := by
    have hsum : Summable g := Real.summable_pow_div_factorial (c * s)
    have he : (∑' k, g k) = Real.exp (c * s) := by
      dsimp [g]
      rw [Real.exp_eq_exp_ℝ]
      exact (NormedSpace.expSeries_div_hasSum_exp (c * s)).tsum_eq
    rw [← he]
    exact hsum.sum_le_tsum (Finset.range (B + 1 - m)) (fun k _ => hg k)
  calc
    _ ≤ ∑ l ∈ Finset.range (B + 1), if m ≤ l then (c * Δ) ^ m * g (l - m) else 0 := by
      apply Finset.sum_le_sum
      intro l hl
      by_cases hm : m ≤ l
      · simpa only [if_pos hm] using hterm l hm
      · simp [hm]
    _ = (c * Δ) ^ m * ∑ l ∈ (Finset.range (B + 1)).filter (fun l => m ≤ l), g (l - m) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      split_ifs <;> simp
    _ = (c * Δ) ^ m * ∑ k ∈ Finset.range (B + 1 - m), g k := by rw [hreindex]
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

end
end ArtinPrimitiveRoots.TypeII.PD
