import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.RawCounting
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.GroupedCounting

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

def comparisonQuads (M N : Finset ℕ) (a b : ℕ) (Y R : ℝ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((M ×ˢ N) ×ˢ (M ×ˢ N)).filter fun q =>
    |(b : ℝ) * (q.1.1 * q.1.2 : ℕ) - (a : ℝ) * (q.2.1 * q.2.2 : ℕ)| ≤ R * Y

/-- Grouping by the two products bounds comparison quadruples by a divisor relation sum. -/
theorem comparisonQuad_card_le (M N Z : Finset ℕ) (a b : ℕ) (Y R : ℝ)
    (hZpos : ∀ k ∈ Z, 0 < k) (hprod : ∀ m ∈ M, ∀ n ∈ N, m * n ∈ Z) :
    ((comparisonQuads M N a b Y R).card : ℝ) ≤
      ∑ k ∈ Z, ∑ l ∈ Z,
        if |(b : ℝ) * k - (a : ℝ) * l| ≤ R * Y then (tau k : ℝ) * (tau l : ℝ) else 0 := by
  let T := comparisonQuads M N a b Y R
  let key (q : (ℕ × ℕ) × (ℕ × ℕ)) := (q.1.1 * q.1.2, q.2.1 * q.2.2)
  have hkey (q : (ℕ × ℕ) × (ℕ × ℕ)) (hq : q ∈ T) : key q ∈ Z ×ˢ Z := by
    have hp := (Finset.mem_filter.mp hq).1
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
    obtain ⟨hm, hn⟩ := Finset.mem_product.mp h₁
    obtain ⟨hr, hs⟩ := Finset.mem_product.mp h₂
    exact Finset.mem_product.mpr ⟨hprod _ hm _ hn, hprod _ hr _ hs⟩
  have hfiber (kl : ℕ × ℕ) (hkl : kl ∈ Z ×ˢ Z) :
      ((T.filter fun q => key q = kl).card : ℝ) ≤
        if |(b : ℝ) * kl.1 - (a : ℝ) * kl.2| ≤ R * Y then (tau kl.1 : ℝ) * (tau kl.2 : ℝ) else 0 := by
    by_cases hc : |(b : ℝ) * kl.1 - (a : ℝ) * kl.2| ≤ R * Y
    · rw [if_pos hc]
      let Fk := (M ×ˢ N).filter fun mn => mn.1 * mn.2 = kl.1
      let Fl := (M ×ˢ N).filter fun mn => mn.1 * mn.2 = kl.2
      have hsub : T.filter (fun q => key q = kl) ⊆ Fk ×ˢ Fl := by
        intro q hq
        obtain ⟨hqT, hqkey⟩ := Finset.mem_filter.mp hq
        have hp := (Finset.mem_filter.mp hqT).1
        have hk := congrArg Prod.fst hqkey
        have hl := congrArg Prod.snd hqkey
        exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hp).1, hk⟩,
          Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hp).2, hl⟩⟩
      have hpairs : (Fk ×ˢ Fl).card ≤ tau kl.1 * tau kl.2 := by
        rw [Finset.card_product]
        exact Nat.mul_le_mul (factorPair_card_le_tau M N kl.1 (hZpos _ (Finset.mem_product.mp hkl).1))
          (factorPair_card_le_tau M N kl.2 (hZpos _ (Finset.mem_product.mp hkl).2))
      have hf := (Finset.card_le_card hsub).trans hpairs
      exact_mod_cast hf
    · rw [if_neg hc]
      have he : T.filter (fun q => key q = kl) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro q hq hqkey
        have ht := (Finset.mem_filter.mp hq).2
        have hk : q.1.1 * q.1.2 = kl.1 := congrArg Prod.fst hqkey
        have hl : q.2.1 * q.2.2 = kl.2 := congrArg Prod.snd hqkey
        exact hc (by simpa only [hk, hl] using ht)
      rw [he, Finset.card_empty, Nat.cast_zero]
  have hgroup := grouped_weight_sum T (Z ×ˢ Z) key hkey (fun kl => (1 : ℝ))
  have hcount : (T.card : ℝ) = ∑ kl ∈ Z ×ˢ Z, ((T.filter fun q => key q = kl).card : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hgroup
  rw [hcount]
  calc
    _ ≤ ∑ kl ∈ Z ×ˢ Z,
        if |(b : ℝ) * kl.1 - (a : ℝ) * kl.2| ≤ R * Y then (tau kl.1 : ℝ) * (tau kl.2 : ℝ) else 0 :=
      Finset.sum_le_sum hfiber
    _ = _ := Finset.sum_product _ _ _

/-- The per-pair comparison absolute sum follows from a divisor second moment. -/
theorem comparisonQuad_norm_sum_bound (M N Z : Finset ℕ) (a b : ℕ) (Y R D A B : ℝ)
    (hY : 0 < Y) (hR : 0 ≤ R) (ha : Y ≤ (a : ℝ)) (hb : Y ≤ (b : ℝ))
    (hZpos : ∀ k ∈ Z, 0 < k) (hprod : ∀ m ∈ M, ∀ n ∈ N, m * n ∈ Z)
    (alpha beta : ℕ → ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (halpha : ∀ m ∈ M, ‖alpha m‖ ≤ A) (hbeta : ∀ n ∈ N, ‖beta n‖ ≤ B)
    (hDiv : (((⌈2 * R⌉₊ + 2 : ℕ) : ℝ)) * (∑ k ∈ Z, (tau k : ℝ) ^ 2) ≤ D) :
    (∑ q ∈ comparisonQuads M N a b Y R,
      ‖alpha q.1.1 * star (alpha q.2.1) * beta q.1.2 * star (beta q.2.2)‖) ≤ D * (A ^ 2 * B ^ 2) := by
  have hOuter : comparisonQuads M N a b Y R ⊆ (M ×ˢ N) ×ˢ (M ×ˢ N) := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hcard := (comparisonQuad_card_le M N Z a b Y R hZpos hprod).trans
    ((comparison_divisor_relation_bound Z a b Y R hY hR ha hb).trans hDiv)
  exact (coefficientQuad_norm_sum_le M N _ hOuter alpha beta A B hA hB halpha hbeta).trans
    (mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

end
end ArtinPrimitiveRoots.TypeII.PD
