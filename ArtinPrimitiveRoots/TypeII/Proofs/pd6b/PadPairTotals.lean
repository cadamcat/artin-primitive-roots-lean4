import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadGlobalBounds

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII Classical
noncomputable section

private theorem etaPair_support_data {K : ℕ} (F : PDFix K) (hF : F.Valid) (x Y : ℝ)
    (hY : 0 < Y) (f : (Fin K → ℕ) → (Fin K → ℕ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hZero : ∀ ta tb, F.eta ((tupleProduct ta : ℝ) / Y) = 0 ∨
      F.eta ((tupleProduct tb : ℝ) / Y) = 0 → f ta tb = 0)
    (hNorm : ∀ ta tb, IsMarkedPrimeTuple x K F.a ta → IsMarkedPrimeTuple x K F.a tb →
      F.eta ((tupleProduct ta : ℝ) / Y) ≠ 0 → F.eta ((tupleProduct tb : ℝ) / Y) ≠ 0 → ‖f ta tb‖ ≤ B) :
    (∀ ta ∈ markedTupleChoices x F.a, ∀ tb ∈ markedTupleChoices x F.a, f ta tb ≠ 0 →
      ta ∈ supportedTupleChoices x Y F.a ∧ tb ∈ supportedTupleChoices x Y F.a) ∧
    (∀ ta ∈ supportedTupleChoices x Y F.a, ∀ tb ∈ supportedTupleChoices x Y F.a, ‖f ta tb‖ ≤ B) := by
  constructor
  · intro ta hta tb htb hf
    have hηa : F.eta ((tupleProduct ta : ℝ) / Y) ≠ 0 := fun hz => hf (hZero ta tb (Or.inl hz))
    have hηb : F.eta ((tupleProduct tb : ℝ) / Y) ≠ 0 := fun hz => hf (hZero ta tb (Or.inr hz))
    exact ⟨markedTuple_mem_supported_of_eta F hF x Y hY ta (mem_markedTupleChoices.mp hta) hηa,
      markedTuple_mem_supported_of_eta F hF x Y hY tb (mem_markedTupleChoices.mp htb) hηb⟩
  · intro ta hta tb htb
    by_cases hηa : F.eta ((tupleProduct ta : ℝ) / Y) = 0
    · rw [hZero ta tb (Or.inl hηa), norm_zero]
      exact hB
    by_cases hηb : F.eta ((tupleProduct tb : ℝ) / Y) = 0
    · rw [hZero ta tb (Or.inr hηb), norm_zero]
      exact hB
    exact hNorm ta tb (mem_markedTupleChoices.mp (Finset.mem_filter.mp hta).1)
      (mem_markedTupleChoices.mp (Finset.mem_filter.mp htb).1) hηa hηb

/-- At most 25Y² supported marked pairs contribute to any absolute pair sum. -/
theorem etaPair_norm_total_le {K : ℕ} (F : PDFix K) (hF : F.Valid) (x Y : ℝ) (hY : 1 ≤ Y)
    (hBands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (F.a i)) (primeBand x (F.a j)))
    (condition : (Fin K → ℕ) → (Fin K → ℕ) → Prop)
    (f : (Fin K → ℕ) → (Fin K → ℕ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hZero : ∀ ta tb, F.eta ((tupleProduct ta : ℝ) / Y) = 0 ∨
      F.eta ((tupleProduct tb : ℝ) / Y) = 0 → f ta tb = 0)
    (hNorm : ∀ ta tb, IsMarkedPrimeTuple x K F.a ta → IsMarkedPrimeTuple x K F.a tb →
      F.eta ((tupleProduct ta : ℝ) / Y) ≠ 0 → F.eta ((tupleProduct tb : ℝ) / Y) ≠ 0 → ‖f ta tb‖ ≤ B) :
    (∑ ta ∈ markedTupleChoices x F.a, ∑ tb ∈ markedTupleChoices x F.a,
      if condition ta tb then ‖f ta tb‖ else 0) ≤ 25 * Y ^ 2 * B := by
  let T := markedTupleChoices x F.a
  let T₀ := supportedTupleChoices x Y F.a
  have hs := etaPair_support_data F hF x Y (lt_of_lt_of_le (by norm_num) hY) f B hB hZero hNorm
  have hb := finitePair_norm_sum_filtered_bound T T₀ condition f B (Finset.filter_subset _ _) hB hs.1 hs.2
  have hc : ((((T₀ ×ˢ T₀).filter fun ab => condition ab.1 ab.2).card : ℕ) : ℝ) ≤ 25 * Y ^ 2 := by
    have hcard := markedTupleChoices_card_le (a := F.a) hY hBands
    have hsub := Finset.card_le_card (Finset.filter_subset (fun ab => condition ab.1 ab.2) (T₀ ×ˢ T₀))
    have hsubR : ((((T₀ ×ˢ T₀).filter fun ab => condition ab.1 ab.2).card : ℕ) : ℝ) ≤ (T₀.card : ℝ) ^ 2 := by
      rw [Finset.card_product] at hsub
      have hh : ((T₀ ×ˢ T₀).filter fun ab => condition ab.1 ab.2).card ≤ T₀.card ^ 2 := by
        simpa only [pow_two] using hsub
      exact_mod_cast hh
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) T₀.card) hcard 2
    exact hsubR.trans (by convert hpow using 1 <;> ring)
  exact hb.trans (mul_le_mul_of_nonneg_right hc hB)

/-- The same per-pair comparison bound restricted to noncoprime pairs gains the prime collision mass. -/
theorem etaPair_noncop_norm_total_le {K : ℕ} (F : PDFix K) (hF : F.Valid) (x Y : ℝ) (hY : 1 ≤ Y)
    (hBands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (F.a i)) (primeBand x (F.a j)))
    (f : (Fin K → ℕ) → (Fin K → ℕ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hZero : ∀ ta tb, F.eta ((tupleProduct ta : ℝ) / Y) = 0 ∨
      F.eta ((tupleProduct tb : ℝ) / Y) = 0 → f ta tb = 0)
    (hNorm : ∀ ta tb, IsMarkedPrimeTuple x K F.a ta → IsMarkedPrimeTuple x K F.a tb →
      F.eta ((tupleProduct ta : ℝ) / Y) ≠ 0 → F.eta ((tupleProduct tb : ℝ) / Y) ≠ 0 → ‖f ta tb‖ ≤ B) :
    (∑ ta ∈ markedTupleChoices x F.a, ∑ tb ∈ markedTupleChoices x F.a,
      if Nat.Coprime (tupleProduct ta) (tupleProduct tb) then 0 else ‖f ta tb‖) ≤
      (16 * Y ^ 2 * ∑ p ∈ markedPrimes x K F.a, ((p : ℝ)⁻¹) ^ 2) * B := by
  have hs := etaPair_support_data F hF x Y (lt_of_lt_of_le (by norm_num) hY) f B hB hZero hNorm
  have hb := finitePair_norm_sum_filtered_bound (markedTupleChoices x F.a) (supportedTupleChoices x Y F.a)
    (fun ta tb => ¬ Nat.Coprime (tupleProduct ta) (tupleProduct tb)) f B
    (Finset.filter_subset _ _) hB hs.1 hs.2
  have hcount := supportedTuple_noncoprime_count_le (a := F.a) hY hBands
  have hbound :
      (∑ ta ∈ markedTupleChoices x F.a, ∑ tb ∈ markedTupleChoices x F.a,
        if Nat.Coprime (tupleProduct ta) (tupleProduct tb) then 0 else ‖f ta tb‖) ≤
      ((((supportedTupleChoices x Y F.a) ×ˢ (supportedTupleChoices x Y F.a)).filter
        fun ab => ¬ Nat.Coprime (tupleProduct ab.1) (tupleProduct ab.2)).card : ℝ) * B := by
    convert hb using 1
    · apply Finset.sum_congr rfl
      intro ta hta
      apply Finset.sum_congr rfl
      intro tb htb
      by_cases hc : Nat.Coprime (tupleProduct ta) (tupleProduct tb) <;> simp [hc]
    · congr 1
      apply congrArg (fun E : Finset ((Fin K → ℕ) × (Fin K → ℕ)) => (E.card : ℝ))
      ext ab
      simp only [Finset.mem_filter]
  exact hbound.trans (mul_le_mul_of_nonneg_right hcount hB)

end
end ArtinPrimitiveRoots.TypeII.PD
