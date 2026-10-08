import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchySquare

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII
set_option maxHeartbeats 1000000

lemma pd1c_quotient_eq (A B h : ℕ) (hB : 0 < B) :
    A = B * h ↔ B ∣ A ∧ A / B = h := by
  constructor
  · intro heq
    rw [heq]
    simp [Nat.mul_div_cancel_left _ hB]
  · rintro ⟨hd, hq⟩
    rw [← hq]
    exact (Nat.mul_div_cancel' hd).symm

lemma pd1c_cauchy_entry_quotient_bound
    {δ C c₁ c₂ x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (eta : ℝ → ℝ)
    (hHm : 0 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x) (hY : 0 < Y)
    (hEta : Function.support eta ⊆ Set.Icc 1 4)
    (i : pd1c_CauchyEntry K) (hi : i ∈ pd1c_cauchyEntrySet x K a family)
    (hz : pd1c_cauchyEntryWeight x K a Y family beta eta i ≠ 0) :
    pd1c_cauchyQuotient i ≤ ⌊4 * (family.Hm x * family.Hn x) / Y⌋₊ := by
  have hmem := Finset.mem_product.mp hi
  have hmn := Finset.mem_product.mp hmem.2
  have hm := (Finset.mem_filter.mp (Finset.mem_filter.mp hmn.1).1).2
  have hn := (Finset.mem_filter.mp hmn.2).2
  have hdiv : tupleProduct i.1 ∣ i.2.1 * i.2.2 - 1 := by
    by_contra hd
    simp [pd1c_cauchyEntryWeight, hd] at hz
  have hη : eta ((tupleProduct i.1 : ℕ) / Y) ≠ 0 := by
    intro hzero
    simp [pd1c_cauchyEntryWeight, hzero] at hz
  have hSupport := hEta hη
  have hBY : Y ≤ (tupleProduct i.1 : ℝ) := by simpa only [one_mul] using (le_div_iff₀ hY).mp hSupport.1
  have hEq : tupleProduct i.1 * pd1c_cauchyQuotient i = i.2.1 * i.2.2 - 1 :=
    Nat.mul_div_cancel' hdiv
  have hEqR : (tupleProduct i.1 : ℝ) * (pd1c_cauchyQuotient i : ℝ) =
      ((i.2.1 * i.2.2 - 1 : ℕ) : ℝ) := by exact_mod_cast hEq
  have hSub : ((i.2.1 * i.2.2 - 1 : ℕ) : ℝ) ≤ (i.2.1 : ℝ) * (i.2.2 : ℝ) := by
    exact_mod_cast Nat.sub_le (i.2.1 * i.2.2) 1
  have hProd : (i.2.1 : ℝ) * (i.2.2 : ℝ) ≤ 4 * (family.Hm x * family.Hn x) := by
    calc
      _ ≤ (2 * family.Hm x) * (2 * family.Hn x) :=
        mul_le_mul hm.2 hn.2 (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hHm)
      _ = _ := by ring
  have hMul : (pd1c_cauchyQuotient i : ℝ) * Y ≤ 4 * (family.Hm x * family.Hn x) := by
    calc
      _ ≤ (pd1c_cauchyQuotient i : ℝ) * (tupleProduct i.1 : ℝ) :=
        mul_le_mul_of_nonneg_left hBY (Nat.cast_nonneg _)
      _ = ((i.2.1 * i.2.2 - 1 : ℕ) : ℝ) := by simpa only [mul_comm] using hEqR
      _ ≤ _ := hSub.trans hProd
  apply (Nat.le_floor_iff (by positivity : 0 ≤ 4 * (family.Hm x * family.Hn x) / Y)).mpr
  exact (le_div_iff₀ hY).mpr hMul

lemma pd1c_cauchy_fiber_zero_outside_range
    {δ C c₁ c₂ x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (eta : ℝ → ℝ)
    (hHm : 0 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x) (hY : 0 < Y)
    (hEta : Function.support eta ⊆ Set.Icc 1 4) (h : ℕ)
    (hh : h ∉ Finset.range (⌊4 * (family.Hm x * family.Hn x) / Y⌋₊ + 1)) :
    pd1c_cauchyFiber x K a Y family beta eta h = 0 := by
  unfold pd1c_cauchyFiber
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hq : pd1c_cauchyQuotient i = h
  · rw [if_pos hq]
    by_contra hz
    have hb := pd1c_cauchy_entry_quotient_bound family beta eta hHm hHn hY hEta i hi hz
    rw [hq] at hb
    exact hh (Finset.mem_range.mpr (Nat.lt_succ_of_le hb))
  · simp [hq]

lemma pd1c_cauchy_fiber_zero_outside_image
    {δ C c₁ c₂ x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (eta : ℝ → ℝ) (h : ℕ)
    (hh : h ∉ (pd1c_cauchyEntrySet x K a family).image pd1c_cauchyQuotient) :
    pd1c_cauchyFiber x K a Y family beta eta h = 0 := by
  unfold pd1c_cauchyFiber
  apply Finset.sum_eq_zero
  intro i hi
  have hnot : pd1c_cauchyQuotient i ≠ h := by
    intro heq
    exact hh (Finset.mem_image.mpr ⟨i, hi, heq⟩)
  simp [hnot]

lemma pd1c_cauchySquare_range_gram
    {δ C c₁ c₂ x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (eta : ℝ → ℝ)
    (hHm : 0 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x) (hY : 0 < Y)
    (hEta : Function.support eta ⊆ Set.Icc 1 4) :
    cauchySquare x K a Y family beta eta =
      ∑ h ∈ Finset.range (⌊4 * (family.Hm x * family.Hn x) / Y⌋₊ + 1),
        ‖pd1c_cauchyFiber x K a Y family beta eta h‖ ^ 2 := by
  rw [pd1c_cauchySquare_fiber_gram]
  calc
    _ = ∑' h : ℕ, ‖pd1c_cauchyFiber x K a Y family beta eta h‖ ^ 2 := by
      symm
      apply tsum_eq_sum
      intro h hh
      rw [pd1c_cauchy_fiber_zero_outside_image family beta eta h hh]
      simp
    _ = _ := by
      apply tsum_eq_sum
      intro h hh
      rw [pd1c_cauchy_fiber_zero_outside_range family beta eta hHm hHn hY hEta h hh]
      simp


lemma pd1c_cauchyFiber_tuple_sum (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) (h : ℕ) :
    pd1c_cauchyFiber x K a Y family beta eta h =
      ∑ t ∈ pd1c_markedTupleSet x K a,
        ((∏ i : Fin K, (bandMass x (a i))⁻¹ : ℝ) : ℂ) * (eta ((tupleProduct t : ℕ) / Y) : ℂ) *
          ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
            if m * n - 1 = tupleProduct t * h then family.alpha x m * beta n else 0 := by
  simp only [pd1c_cauchyFiber, pd1c_cauchyEntrySet, Finset.product_eq_sprod, Finset.sum_product,
    pd1c_cauchyQuotient, pd1c_cauchyEntryWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hB := pd1c_tupleProduct_pos ((pd1c_markedTuple_mem x K a t).mp ht)
  simp only [pd1c_quotient_eq _ _ _ hB]
  by_cases hd : tupleProduct t ∣ m * n - 1 <;>
    by_cases hq : (m * n - 1) / tupleProduct t = h <;> simp [hd, hq]

lemma pd1c_cauchyFiber_tuple_tsum (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) (h : ℕ) :
    pd1c_cauchyFiber x K a Y family beta eta h =
      ∑' t : Fin K → ℕ, if IsMarkedPrimeTuple x K a t then
        ((∏ i : Fin K, (bandMass x (a i))⁻¹ : ℝ) : ℂ) * (eta ((tupleProduct t : ℕ) / Y) : ℂ) *
          ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
            if m * n - 1 = tupleProduct t * h then family.alpha x m * beta n else 0
      else 0 := by
  rw [pd1c_cauchyFiber_tuple_sum]
  symm
  rw [tsum_eq_sum (s := pd1c_markedTupleSet x K a)]
  · apply Finset.sum_congr rfl
    intro t ht
    simp only [(pd1c_markedTuple_mem x K a t).mp ht, ite_true]
  · intro t ht
    have hnot : ¬IsMarkedPrimeTuple x K a t := mt (pd1c_markedTuple_mem x K a t).mpr ht
    simp [hnot]

noncomputable def pd1c_cauchyDamping (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (q : ℝ) (F : ℕ → ℂ) (h : ℕ) : ℂ :=
  if 0 < h then F h * (q ^ markedOmega x K a h : ℂ) else 0

lemma pd1c_dyadicPiece_fiber_tsum (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (q Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (F : ℕ → ℂ) (eta : ℝ → ℝ) :
    dyadicCauchyPiece x K a q Y family beta F eta =
      ∑' h : ℕ, pd1c_cauchyDamping x K a q F h * pd1c_cauchyFiber x K a Y family beta eta h := by
  unfold dyadicCauchyPiece
  apply tsum_congr
  intro h
  by_cases hh : 0 < h
  · simp only [pd1c_cauchyDamping, hh, ite_true]
    rw [pd1c_cauchyFiber_tuple_tsum]
    simp only [Complex.ofReal_prod, Complex.ofReal_inv]
  · simp [pd1c_cauchyDamping, hh]

lemma pd1c_dyadicPiece_finite
    {δ C c₁ c₂ x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (F : ℕ → ℂ) (eta : ℝ → ℝ) (q : ℝ)
    (hHm : 0 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x) (hY : 0 < Y)
    (hEta : Function.support eta ⊆ Set.Icc 1 4) :
    dyadicCauchyPiece x K a q Y family beta F eta =
      ∑ h ∈ Finset.range (⌊4 * (family.Hm x * family.Hn x) / Y⌋₊ + 1),
        pd1c_cauchyDamping x K a q F h * pd1c_cauchyFiber x K a Y family beta eta h := by
  rw [pd1c_dyadicPiece_fiber_tsum]
  apply tsum_eq_sum
  intro h hh
  rw [pd1c_cauchy_fiber_zero_outside_range family beta eta hHm hHn hY hEta h hh, mul_zero]

lemma pd1c_cauchyDamping_norm_le (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (q : ℝ)
    (F : ℕ → ℂ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hF : ∀ h, ‖F h‖ ≤ 1) (h : ℕ) :
    ‖pd1c_cauchyDamping x K a q F h‖ ≤ 1 := by
  by_cases hh : 0 < h
  · simp only [pd1c_cauchyDamping, hh, ite_true, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hq₀]
    have hp : q ^ markedOmega x K a h ≤ 1 := pow_le_one₀ hq₀ hq₁
    exact (mul_le_mul (hF h) hp (pow_nonneg hq₀ _) (by norm_num)).trans (by norm_num)
  · simp [pd1c_cauchyDamping, hh]

lemma pd1c_dyadicCauchyPiece_norm_bound
    {δ C c₁ c₂ x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (F : ℕ → ℂ) (eta : ℝ → ℝ) (q : ℝ)
    (hHm : 0 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x) (hY : 0 < Y)
    (hXY : 1 ≤ (family.Hm x * family.Hn x) / Y)
    (hEta : Function.support eta ⊆ Set.Icc 1 4)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hF : ∀ h, ‖F h‖ ≤ 1) :
    ‖dyadicCauchyPiece x K a q Y family beta F eta‖ ^ 2 ≤
      5 * ((family.Hm x * family.Hn x) / Y) * cauchySquare x K a Y family beta eta := by
  let N := ⌊4 * (family.Hm x * family.Hn x) / Y⌋₊
  have hCS := pd1c_finite_weighted_cauchy (Finset.range (N + 1))
    (pd1c_cauchyDamping x K a q F) (pd1c_cauchyFiber x K a Y family beta eta)
    (fun h hh => pd1c_cauchyDamping_norm_le x K a q F hq₀ hq₁ hF h)
  rw [← pd1c_dyadicPiece_finite family beta F eta q hHm hHn hY hEta,
    ← pd1c_cauchySquare_range_gram family beta eta hHm hHn hY hEta] at hCS
  have hCard : ((Finset.range (N + 1)).card : ℝ) ≤ 5 * ((family.Hm x * family.Hn x) / Y) := by
    have hfloor : (N : ℝ) ≤ 4 * (family.Hm x * family.Hn x) / Y := Nat.floor_le (by positivity)
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_one]
    calc
      (N : ℝ) + 1 ≤ 4 * (family.Hm x * family.Hn x) / Y + (family.Hm x * family.Hn x) / Y := add_le_add hfloor hXY
      _ = _ := by ring
  exact hCS.trans (mul_le_mul_of_nonneg_right hCard (pd1c_cauchySquare_nonneg x K a Y family beta eta))

end ArtinPrimitiveRoots.TypeII.PD
