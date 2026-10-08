import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyFinite
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyPartition
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyWeights

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII Filter
set_option maxHeartbeats 1000000

lemma pd1c_dyadicPiece_entry_sum
    {δ C c₁ c₂ x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (F : ℕ → ℂ) (eta : ℝ → ℝ) (q : ℝ)
    (hHm : 0 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x) (hY : 0 < Y)
    (hEta : Function.support eta ⊆ Set.Icc 1 4) :
    dyadicCauchyPiece x K a q Y family beta F eta =
      ∑ i ∈ pd1c_cauchyEntrySet x K a family,
        pd1c_cauchyDamping x K a q F (pd1c_cauchyQuotient i) *
          pd1c_cauchyEntryWeight x K a Y family beta eta i := by
  rw [pd1c_dyadicPiece_finite family beta F eta q hHm hHn hY hEta]
  unfold pd1c_cauchyFiber
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hz : pd1c_cauchyEntryWeight x K a Y family beta eta i = 0
  · simp [hz]
  · have hk := pd1c_cauchy_entry_quotient_bound family beta eta hHm hHn hY hEta i hi hz
    rw [Finset.sum_eq_single (pd1c_cauchyQuotient i)]
    · simp
    · intro h hh hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).elim

lemma pd1c_dyadicPiece_replaced_sum
    {δ C c₁ c₂ x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (F : ℕ → ℂ) (eta : ℝ → ℝ) (q : ℝ)
    (hF : IsMarkedInvariant x K a F)
    (hHm : 0 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x) (hY : 0 < Y)
    (hEta : Function.support eta ⊆ Set.Icc 1 4)
    (hmn : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), 0 < m * n - 1) :
    dyadicCauchyPiece x K a q Y family beta F eta =
      ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
        family.alpha x m * beta n * F (m * n - 1) *
          (((∏ i : Fin K, (bandMass x (a i))⁻¹) *
            ∑ t ∈ pd1c_markedTupleSet x K a,
              eta ((tupleProduct t : ℕ) / Y) *
                (if tupleProduct t ∣ m * n - 1 then q ^ markedOmega x K a ((m * n - 1) / tupleProduct t) else 0) : ℝ) : ℂ) := by
  rw [pd1c_dyadicPiece_entry_sum family beta F eta q hHm hHn hY hEta]
  simp only [pd1c_cauchyEntrySet, Finset.product_eq_sprod, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := (pd1c_markedTuple_mem _ _ _ _).mp ht
  by_cases hd : tupleProduct t ∣ m * n - 1
  · have hpos : 0 < (m * n - 1) / tupleProduct t :=
      Nat.div_pos (Nat.le_of_dvd (hmn m hm n hn) hd) (pd1c_tupleProduct_pos ht')
    have hFeq : F (m * n - 1) = F ((m * n - 1) / tupleProduct t) := by
      calc
        F (m * n - 1) = F (tupleProduct t * ((m * n - 1) / tupleProduct t)) := congrArg F (Nat.mul_div_cancel' hd).symm
        _ = _ := pd1c_marked_invariant_tuple_mul F hF t ht' _
    simp only [pd1c_cauchyEntryWeight, pd1c_cauchyQuotient, pd1c_cauchyDamping,
      hd, hpos, ite_true, Complex.ofReal_pow]
    rw [hFeq]
    ring
  · simp [pd1c_cauchyEntryWeight, hd]

lemma pd1c_dyadicPiece_sum_eq_replacement
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (F : ℕ → ℂ) (eta : ℝ → ℝ) (q : ℝ)
    (hF : IsMarkedInvariant x K a F)
    (hHm : 0 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x)
    (hEta : Function.support eta ⊆ Set.Icc 1 4) (hpart : IsDyadicPartition eta)
    (hL : 0 ≤ Real.log x)
    (hmn : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), 0 < m * n - 1)
    (hRange : ∀ t : Fin K → ℕ, IsMarkedPrimeTuple x K a t →
      (1 / 20 : ℝ) * (Real.log x) ^ (1 / 10 : ℝ) ≤ Real.log (tupleProduct t : ℝ) - Real.log 4 ∧
        Real.log (tupleProduct t : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * (Real.log x) ^ (1 / 5 : ℝ)) :
    (∑ Y ∈ dyadicScales x K, dyadicCauchyPiece x K a q Y family beta F eta) =
      ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
        family.alpha x m * beta n * F (m * n - 1) * (pd1c_replacedWeight x K a q (m * n - 1) : ℂ) := by
  have hYpos : ∀ Y ∈ dyadicScales x K, 0 < Y := by
    intro Y hY
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hY).1
    positivity
  simp_rw [Finset.sum_congr rfl (fun Y hY => pd1c_dyadicPiece_replaced_sum family beta F eta q hF hHm hHn
    (hYpos Y hY) hEta hmn)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [pd1c_replacedWeight, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := (pd1c_markedTuple_mem _ _ _ _).mp ht
  have hp := pd1c_partition_finite_dyads eta hEta hpart (tupleProduct t : ℝ)
    (by exact_mod_cast pd1c_tupleProduct_pos ht') (hRange t ht').1 (hRange t ht').2 hL
  by_cases hd : tupleProduct t ∣ m * n - 1
  · simp only [hd, ite_true, Complex.ofReal_mul, Complex.ofReal_pow]
    have hpC : (∑ Y ∈ dyadicScales x K, (eta ((tupleProduct t : ℕ) / Y) : ℂ)) = 1 := by exact_mod_cast hp
    calc
      _ = (family.alpha x m * beta n * F (m * n - 1) *
          ((∏ i : Fin K, (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
          (q ^ markedOmega x K a ((m * n - 1) / tupleProduct t) : ℂ)) *
            ∑ Y ∈ dyadicScales x K, (eta ((tupleProduct t : ℕ) / Y) : ℂ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro Y hY
              ring
      _ = _ := by rw [hpC]; ring
  · simp [hd]

end ArtinPrimitiveRoots.TypeII.PD
