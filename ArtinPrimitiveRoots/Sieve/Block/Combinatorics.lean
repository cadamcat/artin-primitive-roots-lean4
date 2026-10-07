import Mathlib

namespace ArtinPrimitiveRoots.Sieve.Block

open Finset

/-- The even truncated inclusion-exclusion polynomial on a set of events. -/
def blockU {α : Type*} [DecidableEq α] (b : Finset α) (h : ℕ) : ℝ :=
  ∑ J ∈ b.powerset with J.card ≤ h, (-1 : ℝ) ^ J.card

/-- The unsigned next-degree correction in one block. -/
def blockT {α : Type*} [DecidableEq α] (b : Finset α) (h : ℕ) : ℝ :=
  (b.powersetCard (h + 1)).card

/-- Grouping the terms of `blockU` by their cardinality gives a binomial sum. -/
theorem blockU_eq_sum_choose {α : Type*} [DecidableEq α] (b : Finset α) (h : ℕ) :
    blockU b h =
      ∑ k ∈ Finset.range (b.card + 1),
        if k ≤ h then (b.card.choose k : ℝ) * (-1 : ℝ) ^ k else 0 := by
  classical
  simp only [blockU, Finset.sum_filter]
  rw [Finset.sum_powerset_apply_card
    (fun k : ℕ => if k ≤ h then (-1 : ℝ) ^ k else 0)]
  simp [nsmul_eq_mul]

/-- The partial alternating binomial sum for a nonempty set of events. -/
theorem alternating_choose_partial (n m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ) ^ k * (n + 1).choose k)) =
      (-1 : ℝ) ^ m * n.choose m := by
  have h := Int.alternating_sum_range_choose_eq_choose (n := n) (m := m)
  exact_mod_cast h

/-- Truncated inclusion-exclusion is nonnegative for an even truncation. -/
theorem alternating_choose_partial_nonneg {n m : ℕ} (hm : Even m) :
    0 ≤ ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ) ^ k * (n + 1).choose k) := by
  rw [alternating_choose_partial]
  rcases hm with ⟨q, rfl⟩
  simp

/-- The cardinality-grouped truncation, including the complete-sum case. -/
theorem sum_choose_cutoff (n h : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      if k ≤ h then (n.choose k : ℝ) * (-1 : ℝ) ^ k else 0) =
      if h < n then (-1 : ℝ) ^ h * ((n - 1).choose h : ℝ)
      else if n = 0 then 1 else 0 := by
  classical
  by_cases hlt : h < n
  · have hn : 1 ≤ n := by omega
    have hrange : (Finset.range (n + 1)).filter (fun k => k ≤ h) =
        Finset.range (h + 1) := by
      ext k
      simp
      omega
    rw [← Finset.sum_filter, hrange]
    have halt := alternating_choose_partial (n - 1) h
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simpa [hsub, mul_comm, hlt] using halt
  · have hrange : (Finset.range (n + 1)).filter (fun k => k ≤ h) =
        Finset.range (n + 1) := by
      ext k
      simp
      omega
    rw [← Finset.sum_filter, hrange]
    have halt : (∑ k ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ k * (n.choose k : ℝ))) = (if n = 0 then 1 else 0) := by
      exact_mod_cast (Int.alternating_sum_range_choose (n := n))
    simpa [mul_comm, hlt] using halt

/-- Closed form for a block's even Bonferroni polynomial. -/
theorem blockU_eq_closed {α : Type*} [DecidableEq α] (b : Finset α) {h : ℕ}
    (hh : Even h) :
    blockU b h = if b.card = 0 then 1
      else if h < b.card then ((b.card - 1).choose h : ℝ) else 0 := by
  rw [blockU_eq_sum_choose, sum_choose_cutoff]
  rcases hh with ⟨q, rfl⟩
  by_cases hzero : b.card = 0 <;> simp [hzero]

/-- The next-degree correction is the corresponding binomial coefficient. -/
theorem blockT_eq_choose {α : Type*} [DecidableEq α] (b : Finset α) (h : ℕ) :
    blockT b h = (b.card.choose (h + 1) : ℝ) := by
  simp [blockT, Finset.card_powersetCard]

/-- A block's even truncated inclusion-exclusion polynomial is nonnegative. -/
theorem blockU_nonneg {α : Type*} [DecidableEq α] (b : Finset α) {h : ℕ}
    (hh : Even h) : 0 ≤ blockU b h := by
  rw [blockU_eq_closed b hh]
  split_ifs <;> positivity

/-- A block's even truncation bounds its exact avoidance indicator from above. -/
theorem blockU_ge_avoid {α : Type*} [DecidableEq α] (b : Finset α) {h : ℕ}
    (hh : Even h) : (if b.card = 0 then (1 : ℝ) else 0) ≤ blockU b h := by
  rw [blockU_eq_closed b hh]
  split_ifs <;> norm_num

/-- The gap between the block polynomial and the exact avoidance indicator is bounded by
the degree-`h+1` correction. -/
theorem blockU_sub_avoid_le_T {α : Type*} [DecidableEq α] (b : Finset α) {h : ℕ}
    (hh : Even h) :
    blockU b h - (if b.card = 0 then (1 : ℝ) else 0) ≤ blockT b h := by
  rw [blockU_eq_closed b hh, blockT_eq_choose]
  by_cases hz : b.card = 0
  · simp [hz]
  · have hn : 1 ≤ b.card := Nat.pos_of_ne_zero hz
    by_cases hlt : h < b.card
    ·
      have hchoose : (b.card - 1).choose h ≤ b.card.choose (h + 1) := by
        have hrec := Nat.choose_succ_succ' (b.card - 1) h
        have hsub : b.card - 1 + 1 = b.card := Nat.sub_add_cancel hn
        rw [hsub] at hrec
        rw [hrec]
        exact Nat.le_add_right _ _
      have hchooseR : ((b.card - 1).choose h : ℝ) ≤ (b.card.choose (h + 1) : ℝ) := by
        exact_mod_cast hchoose
      simpa [hz, hlt] using hchooseR
    · simp [hz, hlt]

end ArtinPrimitiveRoots.Sieve.Block
