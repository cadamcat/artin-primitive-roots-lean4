import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.AbsoluteSquares
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.IntervalCounting

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

def commonPredecessorQuads (M N : Finset ℕ) (a b H : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((M ×ˢ N) ×ˢ (M ×ˢ N)).filter fun q =>
    ∃ h ∈ Finset.range (H + 1), q.1.1 * q.1.2 = 1 + a * h ∧ q.2.1 * q.2.2 = 1 + b * h

/-- Common-predecessor quadruples are covered by a finite union of pairs of factor sets. -/
theorem commonPredecessorQuad_card_le (M N : Finset ℕ) (a b H : ℕ) :
    (commonPredecessorQuads M N a b H).card ≤
      ∑ h ∈ Finset.range (H + 1), tau (1 + a * h) * tau (1 + b * h) := by
  let T (c h : ℕ) := (M ×ˢ N).filter fun mn => mn.1 * mn.2 = 1 + c * h
  let Q := commonPredecessorQuads M N a b H
  have hsub : Q ⊆ (Finset.range (H + 1)).biUnion (fun h => T a h ×ˢ T b h) := by
    intro q hq
    have hq' : q ∈ (M ×ˢ N) ×ˢ (M ×ˢ N) ∧
        ∃ h ∈ Finset.range (H + 1), q.1.1 * q.1.2 = 1 + a * h ∧ q.2.1 * q.2.2 = 1 + b * h := by
      simpa only [Q, commonPredecessorQuads, Finset.mem_filter] using hq
    obtain ⟨hqProd, h, hh, hqa, hqb⟩ := hq'
    obtain ⟨hqaProd, hqbProd⟩ := Finset.mem_product.mp hqProd
    exact Finset.mem_biUnion.mpr ⟨h, hh, Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hqaProd, hqa⟩, Finset.mem_filter.mpr ⟨hqbProd, hqb⟩⟩⟩
  change Q.card ≤ _
  calc
    _ ≤ ((Finset.range (H + 1)).biUnion (fun h => T a h ×ˢ T b h)).card := Finset.card_le_card hsub
    _ ≤ ∑ h ∈ Finset.range (H + 1), (T a h ×ˢ T b h).card := Finset.card_biUnion_le
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro h hh
      rw [Finset.card_product]
      exact Nat.mul_le_mul
        (factorPair_card_le_tau M N (1 + a * h) (by omega))
        (factorPair_card_le_tau M N (1 + b * h) (by omega))

/-- A bounded endpoint product costs its supremum times the finite quadruple count. -/
theorem coefficientQuad_norm_sum_le (M N : Finset ℕ) (Q : Finset ((ℕ × ℕ) × (ℕ × ℕ)))
    (hQ : Q ⊆ (M ×ˢ N) ×ˢ (M ×ˢ N)) (alpha beta : ℕ → ℂ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (halpha : ∀ m ∈ M, ‖alpha m‖ ≤ A)
    (hbeta : ∀ n ∈ N, ‖beta n‖ ≤ B) :
    (∑ q ∈ Q, ‖alpha q.1.1 * star (alpha q.2.1) * beta q.1.2 * star (beta q.2.2)‖) ≤
      (Q.card : ℝ) * (A ^ 2 * B ^ 2) := by
  calc
    _ ≤ ∑ q ∈ Q, A ^ 2 * B ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp (hQ hq)
      obtain ⟨hm, hn⟩ := Finset.mem_product.mp h₁
      obtain ⟨hr, hs⟩ := Finset.mem_product.mp h₂
      have haPair : ‖alpha q.1.1‖ * ‖alpha q.2.1‖ ≤ A ^ 2 := by
        simpa only [pow_two] using mul_le_mul (halpha _ hm) (halpha _ hr) (norm_nonneg _) hA
      have hbPair : ‖beta q.1.2‖ * ‖beta q.2.2‖ ≤ B ^ 2 := by
        simpa only [pow_two] using mul_le_mul (hbeta _ hn) (hbeta _ hs) (norm_nonneg _) hB
      simp only [norm_mul, norm_star]
      calc
        _ = (‖alpha q.1.1‖ * ‖alpha q.2.1‖) * (‖beta q.1.2‖ * ‖beta q.2.2‖) := by ring
        _ ≤ _ := mul_le_mul haPair hbPair (by positivity) (sq_nonneg _)
    _ = _ := by simp

/-- The common predecessor of supported coefficient products lies in the required divisor range. -/
theorem commonPredecessor_witness_bound (a m n h : ℕ) (Hm Hn Y : ℝ)
    (hHm : 0 < Hm) (hHn : 0 < Hn) (hY : 0 < Y)
    (ha : Y ≤ (a : ℝ)) (hm : (m : ℝ) ≤ 2 * Hm) (hn : (n : ℝ) ≤ 2 * Hn)
    (hprod : 1 ≤ m * n) (heq : m * n - 1 = a * h) :
    h ≤ ⌊4 * (Hm * Hn) / Y⌋₊ := by
  have heqR : (m : ℝ) * (n : ℝ) - 1 = (a : ℝ) * (h : ℝ) := by
    have hcast := congrArg (fun z : ℕ => (z : ℝ)) heq
    simpa only [Nat.cast_sub hprod, Nat.cast_mul, Nat.cast_one] using hcast
  have hmn : (m : ℝ) * (n : ℝ) ≤ 4 * (Hm * Hn) := by
    have h := mul_le_mul hm hn (Nat.cast_nonneg n) (by positivity : 0 ≤ 2 * Hm)
    nlinarith
  apply (Nat.le_floor_iff (div_nonneg (by positivity) hY.le)).mpr
  apply (le_div_iff₀ hY).mpr
  have hmul := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg h)
  nlinarith


/-- The product relation underlying a comparison sum is controlled by a divisor second moment. -/
theorem comparison_divisor_relation_bound (Z : Finset ℕ) (a b : ℕ) (Y R : ℝ)
    (hY : 0 < Y) (hR : 0 ≤ R) (ha : Y ≤ (a : ℝ)) (hb : Y ≤ (b : ℝ)) :
    (∑ k ∈ Z, ∑ l ∈ Z,
      if |(b : ℝ) * k - (a : ℝ) * l| ≤ R * Y then (tau k : ℝ) * (tau l : ℝ) else 0) ≤
      ((⌈2 * R⌉₊ + 2 : ℕ) : ℝ) * ∑ k ∈ Z, (tau k : ℝ) ^ 2 := by
  have hrow (k : ℕ) (hk : k ∈ Z) :
      (((Z.filter fun l : ℕ => |(b : ℝ) * k - (a : ℝ) * l| ≤ R * Y).card) : ℝ) ≤
        ((⌈2 * R⌉₊ + 2 : ℕ) : ℝ) := by
    exact_mod_cast comparisonRelation_row_card_le Z a b k Y R hY hR ha
  have hcol (l : ℕ) (hl : l ∈ Z) :
      (((Z.filter fun k : ℕ => |(b : ℝ) * k - (a : ℝ) * l| ≤ R * Y).card) : ℝ) ≤
        ((⌈2 * R⌉₊ + 2 : ℕ) : ℝ) := by
    have h := comparisonRelation_row_card_le Z b a l Y R hY hR hb
    have hsets : (Z.filter fun k : ℕ => |(b : ℝ) * k - (a : ℝ) * l| ≤ R * Y) =
        (Z.filter fun k : ℕ => |(a : ℝ) * l - (b : ℝ) * k| ≤ R * Y) := by
      ext k
      simp only [Finset.mem_filter, abs_sub_comm]
    rw [hsets]
    exact_mod_cast h
  have hbound := boundedDegree_square_bound Z Z
    (fun k l => |(b : ℝ) * k - (a : ℝ) * l| ≤ R * Y)
    (fun k => (tau k : ℝ)) (fun l => (tau l : ℝ))
    (((⌈2 * R⌉₊ + 2 : ℕ) : ℝ)) hrow hcol
  have hRhs : (((⌈2 * R⌉₊ + 2 : ℕ) : ℝ)) / 2 *
      ((∑ k ∈ Z, (tau k : ℝ) ^ 2) + ∑ k ∈ Z, (tau k : ℝ) ^ 2) =
      (((⌈2 * R⌉₊ + 2 : ℕ) : ℝ)) * ∑ k ∈ Z, (tau k : ℝ) ^ 2 := by ring
  rwa [hRhs] at hbound


def rawCommonQuads (M N : Finset ℕ) (a b : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((M ×ˢ N) ×ˢ (M ×ˢ N)).filter fun q =>
    ∃ h : ℕ, q.1.1 * q.1.2 - 1 = a * h ∧ q.2.1 * q.2.2 - 1 = b * h

/-- A per-pair absolute raw sum is bounded by the mixed progression divisor estimate. -/
theorem rawCommon_norm_sum_bound (M N : Finset ℕ) (a b : ℕ) (Hm Hn Y D A B : ℝ)
    (hHm : 0 < Hm) (hHn : 0 < Hn) (hY : 0 < Y) (ha : Y ≤ (a : ℝ))
    (hM : ∀ m ∈ M, 0 < m ∧ (m : ℝ) ≤ 2 * Hm)
    (hN : ∀ n ∈ N, 0 < n ∧ (n : ℝ) ≤ 2 * Hn)
    (alpha beta : ℕ → ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (halpha : ∀ m ∈ M, ‖alpha m‖ ≤ A) (hbeta : ∀ n ∈ N, ‖beta n‖ ≤ B)
    (hDiv : (∑ h ∈ Finset.range (⌊4 * (Hm * Hn) / Y⌋₊ + 1),
      (tau (1 + a * h) : ℝ) * (tau (1 + b * h) : ℝ)) ≤ D) :
    (∑ q ∈ rawCommonQuads M N a b,
      ‖alpha q.1.1 * star (alpha q.2.1) * beta q.1.2 * star (beta q.2.2)‖) ≤ D * (A ^ 2 * B ^ 2) := by
  let H := ⌊4 * (Hm * Hn) / Y⌋₊
  have hsub : rawCommonQuads M N a b ⊆ commonPredecessorQuads M N a b H := by
    intro q hq
    have hq' : q ∈ (M ×ˢ N) ×ˢ (M ×ˢ N) ∧
        ∃ h : ℕ, q.1.1 * q.1.2 - 1 = a * h ∧ q.2.1 * q.2.2 - 1 = b * h := by
      simpa only [rawCommonQuads, Finset.mem_filter] using hq
    obtain ⟨hprod, h, hqa, hqb⟩ := hq'
    obtain ⟨hMN, hRS⟩ := Finset.mem_product.mp hprod
    obtain ⟨hm, hn⟩ := Finset.mem_product.mp hMN
    obtain ⟨hr, hs⟩ := Finset.mem_product.mp hRS
    have hmn : 1 ≤ q.1.1 * q.1.2 := Nat.succ_le_of_lt (Nat.mul_pos (hM _ hm).1 (hN _ hn).1)
    have hrs : 1 ≤ q.2.1 * q.2.2 := Nat.succ_le_of_lt (Nat.mul_pos (hM _ hr).1 (hN _ hs).1)
    have hh : h ≤ H := commonPredecessor_witness_bound a q.1.1 q.1.2 h Hm Hn Y
      hHm hHn hY ha (hM _ hm).2 (hN _ hn).2 hmn hqa
    have heqa : q.1.1 * q.1.2 = 1 + a * h := by omega
    have heqb : q.2.1 * q.2.2 = 1 + b * h := by omega
    have hmem : q ∈ (M ×ˢ N) ×ˢ (M ×ˢ N) ∧
        ∃ h ∈ Finset.range (H + 1), q.1.1 * q.1.2 = 1 + a * h ∧ q.2.1 * q.2.2 = 1 + b * h :=
      ⟨hprod, h, Finset.mem_range.mpr (Nat.lt_succ_of_le hh), heqa, heqb⟩
    simpa only [commonPredecessorQuads, Finset.mem_filter] using hmem
  have hcard : (rawCommonQuads M N a b).card ≤
      ∑ h ∈ Finset.range (H + 1), tau (1 + a * h) * tau (1 + b * h) :=
    (Finset.card_le_card hsub).trans (commonPredecessorQuad_card_le M N a b H)
  have hcardR : ((rawCommonQuads M N a b).card : ℝ) ≤
      ∑ h ∈ Finset.range (H + 1), (tau (1 + a * h) : ℝ) * (tau (1 + b * h) : ℝ) := by
    exact_mod_cast hcard
  have hOuter : rawCommonQuads M N a b ⊆ (M ×ˢ N) ×ˢ (M ×ˢ N) := by
    intro q hq
    have hq' := hq
    simp only [rawCommonQuads, Finset.mem_filter] at hq'
    exact hq'.1
  calc
    _ ≤ ((rawCommonQuads M N a b).card : ℝ) * (A ^ 2 * B ^ 2) :=
      coefficientQuad_norm_sum_le M N _ hOuter alpha beta A B hA hB halpha hbeta
    _ ≤ D * (A ^ 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_right (hcardR.trans hDiv) (mul_nonneg (sq_nonneg _) (sq_nonneg _))


end
end ArtinPrimitiveRoots.TypeII.PD
