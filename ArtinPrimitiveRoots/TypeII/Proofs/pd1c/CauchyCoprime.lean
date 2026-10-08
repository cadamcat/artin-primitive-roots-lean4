import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyFibers
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyPairs
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyPartition

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII
set_option maxHeartbeats 1000000

lemma pd1c_if_sum {ι M : Type*} [AddCommMonoid M] (P : Prop) [Decidable P]
    (I : Finset ι) (f : ι → M) :
    (if P then ∑ i ∈ I, f i else 0) = ∑ i ∈ I, if P then f i else 0 := by
  by_cases h : P <;> simp [h]

lemma pd1c_gram_discard (P Q : Prop) [Decidable P] [Decidable Q] (v : ℝ) :
    (if Q then v else 0) - (if P ∧ Q then v else 0) =
      if ¬P then (if Q then v else 0) else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

lemma pd1c_coprimeCauchySquare_finite_sum (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) :
    coprimeCauchySquare x K a Y family beta eta =
      ∑ ta ∈ pd1c_markedTupleSet x K a, ∑ tb ∈ pd1c_markedTupleSet x K a,
        if Nat.Coprime (tupleProduct ta) (tupleProduct tb) then
        (∏ i : Fin K, (bandMass x (a i))⁻¹) ^ 2 *
          (∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
            ∑ r ∈ familyTerms family x, ∑ s ∈ dyadicIntegers (family.Hn x),
              if ∃ h : ℕ, m * n - 1 = tupleProduct ta * h ∧
                  r * s - 1 = tupleProduct tb * h then
                eta ((tupleProduct ta : ℕ) / Y) * eta ((tupleProduct tb : ℕ) / Y) *
                  (family.alpha x m * star (family.alpha x r) * beta n * star (beta s)).re
              else 0) else 0 := by
  unfold coprimeCauchySquare
  rw [tsum_eq_sum (s := pd1c_markedTupleSet x K a)]
  · apply Finset.sum_congr rfl
    intro ta hta
    have ha := (pd1c_markedTuple_mem x K a ta).mp hta
    rw [tsum_eq_sum (s := pd1c_markedTupleSet x K a)]
    · apply Finset.sum_congr rfl
      intro tb htb
      have hb := (pd1c_markedTuple_mem x K a tb).mp htb
      simp only [ha, hb, true_and, ite_true]
    · intro tb htb
      have hb : ¬ IsMarkedPrimeTuple x K a tb := by
        exact mt (pd1c_markedTuple_mem x K a tb).mpr htb
      simp [hb]
  · intro ta hta
    have ha : ¬ IsMarkedPrimeTuple x K a ta := by
      exact mt (pd1c_markedTuple_mem x K a ta).mpr hta
    simp [ha]


lemma pd1c_coprimeCauchySquare_entry_gram (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) :
    coprimeCauchySquare x K a Y family beta eta =
      ∑ i ∈ pd1c_cauchyEntrySet x K a family, ∑ j ∈ pd1c_cauchyEntrySet x K a family,
        if Nat.Coprime (tupleProduct i.1) (tupleProduct j.1) ∧ pd1c_cauchyQuotient i = pd1c_cauchyQuotient j then
          (pd1c_cauchyEntryWeight x K a Y family beta eta i *
            star (pd1c_cauchyEntryWeight x K a Y family beta eta j)).re else 0 := by
  let T := pd1c_markedTupleSet x K a
  let M := familyTerms family x
  let N := dyadicIntegers (family.Hn x)
  let W : ℝ := ∏ i : Fin K, (bandMass x (a i))⁻¹
  let s := T.product (M.product N)
  let k (i : pd1c_CauchyEntry K) := (i.2.1 * i.2.2 - 1) / tupleProduct i.1
  let z (i : pd1c_CauchyEntry K) : ℂ :=
    (W : ℂ) * (eta ((tupleProduct i.1 : ℕ) / Y) : ℂ) *
      if tupleProduct i.1 ∣ i.2.1 * i.2.2 - 1 then family.alpha x i.2.1 * beta i.2.2 else 0
  change coprimeCauchySquare x K a Y family beta eta =
    ∑ i ∈ s, ∑ j ∈ s, if Nat.Coprime (tupleProduct i.1) (tupleProduct j.1) ∧ k i = k j then (z i * star (z j)).re else 0
  rw [pd1c_coprimeCauchySquare_finite_sum]
  simp only [Finset.mul_sum]
  simp_rw [pd1c_if_sum]
  dsimp only [s, k, z]
  simp only [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro ta hta
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro tb htb
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro v hv
  have ha := pd1c_tupleProduct_pos ((pd1c_markedTuple_mem x K a ta).mp hta)
  have hb := pd1c_tupleProduct_pos ((pd1c_markedTuple_mem x K a tb).mp htb)
  by_cases hc : Nat.Coprime (tupleProduct ta) (tupleProduct tb)
  · rw [if_pos hc]
    simp only [and_iff_right hc]
    rw [pd1c_common_quotient _ _ _ _ ha hb]
    by_cases hA : tupleProduct ta ∣ m * n - 1
    · by_cases hB : tupleProduct tb ∣ r * v - 1
      · by_cases hEq : (m * n - 1) / tupleProduct ta = (r * v - 1) / tupleProduct tb
        · simp only [hA, hB, hEq, and_self, ite_true]
          have hprod :
              ((W : ℂ) * (eta ((tupleProduct ta : ℕ) / Y) : ℂ) * (family.alpha x m * beta n)) *
                star ((W : ℂ) * (eta ((tupleProduct tb : ℕ) / Y) : ℂ) * (family.alpha x r * beta v)) =
              ((W ^ 2 * eta ((tupleProduct ta : ℕ) / Y) * eta ((tupleProduct tb : ℕ) / Y) : ℝ) : ℂ) *
                (family.alpha x m * star (family.alpha x r) * beta n * star (beta v)) := by
            simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_pow]
            ring
          rw [hprod, Complex.re_ofReal_mul]
          dsimp only [W]
          ring
        · simp [hA, hB, hEq]
      · simp [hB]
    · simp [hA]
  · have hn : ¬(Nat.Coprime (tupleProduct ta) (tupleProduct tb) ∧
        (m * n - 1) / tupleProduct ta = (r * v - 1) / tupleProduct tb) := fun h => hc h.1
    rw [if_neg hc, if_neg hn]


noncomputable def pd1c_cauchyBlock (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) (t s : Fin K → ℕ) : ℝ :=
  ∑ mn ∈ (familyTerms family x).product (dyadicIntegers (family.Hn x)),
    ∑ rs ∈ (familyTerms family x).product (dyadicIntegers (family.Hn x)),
      if pd1c_cauchyQuotient (t, mn) = pd1c_cauchyQuotient (s, rs) then
        (pd1c_cauchyEntryWeight x K a Y family beta eta (t, mn) *
          star (pd1c_cauchyEntryWeight x K a Y family beta eta (s, rs))).re else 0

lemma pd1c_cauchy_difference_blocks (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) :
    cauchySquare x K a Y family beta eta - coprimeCauchySquare x K a Y family beta eta =
      ∑ t ∈ pd1c_markedTupleSet x K a, ∑ s ∈ pd1c_markedTupleSet x K a,
        if ¬Nat.Coprime (tupleProduct t) (tupleProduct s) then
          pd1c_cauchyBlock x K a Y family beta eta t s else 0 := by
  rw [pd1c_cauchySquare_entry_gram, pd1c_coprimeCauchySquare_entry_gram]
  simp only [← Finset.sum_sub_distrib]
  have hpoint : ∀ i j : pd1c_CauchyEntry K,
      (if pd1c_cauchyQuotient i = pd1c_cauchyQuotient j then
          (pd1c_cauchyEntryWeight x K a Y family beta eta i * star (pd1c_cauchyEntryWeight x K a Y family beta eta j)).re else 0) -
      (if Nat.Coprime (tupleProduct i.1) (tupleProduct j.1) ∧ pd1c_cauchyQuotient i = pd1c_cauchyQuotient j then
          (pd1c_cauchyEntryWeight x K a Y family beta eta i * star (pd1c_cauchyEntryWeight x K a Y family beta eta j)).re else 0) =
      if ¬Nat.Coprime (tupleProduct i.1) (tupleProduct j.1) then
        (if pd1c_cauchyQuotient i = pd1c_cauchyQuotient j then
          (pd1c_cauchyEntryWeight x K a Y family beta eta i * star (pd1c_cauchyEntryWeight x K a Y family beta eta j)).re else 0) else 0 := by
    intro i j
    exact pd1c_gram_discard _ _ _
  simp_rw [hpoint]
  simp only [pd1c_cauchyEntrySet, pd1c_cauchyBlock, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro t ht
  simp_rw [Finset.sum_comm (s := dyadicIntegers (family.Hn x)) (t := pd1c_markedTupleSet x K a),
    Finset.sum_comm (s := familyTerms family x) (t := pd1c_markedTupleSet x K a)]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hc : Nat.Coprime (tupleProduct t) (tupleProduct s) <;> simp [hc]

lemma pd1c_tuple_fiber_identity (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) (t : Fin K → ℕ)
    (ht : IsMarkedPrimeTuple x K a t) (h : ℕ) :
    (∑ mn ∈ (familyTerms family x).product (dyadicIntegers (family.Hn x)),
      if pd1c_cauchyQuotient (t, mn) = h then pd1c_cauchyEntryWeight x K a Y family beta eta (t, mn) else 0) =
    (((∏ i : Fin K, (bandMass x (a i))⁻¹) : ℝ) : ℂ) * (eta ((tupleProduct t : ℕ) / Y) : ℂ) *
      ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
        if m * n - 1 = tupleProduct t * h then family.alpha x m * beta n else 0 := by
  simp only [Finset.product_eq_sprod, Finset.sum_product, pd1c_cauchyQuotient, pd1c_cauchyEntryWeight,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  simp only [pd1c_quotient_eq _ _ _ (pd1c_tupleProduct_pos ht)]
  by_cases hd : tupleProduct t ∣ m * n - 1 <;> by_cases hq : (m * n - 1) / tupleProduct t = h <;> simp [hd, hq]

lemma pd1c_real_scaled_gram (c e f : ℝ) (u v : ℂ) :
    ((c : ℂ) * (e : ℂ) * u * star ((c : ℂ) * (f : ℂ) * v)).re =
      c ^ 2 * e * f * (u * star v).re := by
  have heq : (c : ℂ) * (e : ℂ) * u * star ((c : ℂ) * (f : ℂ) * v) =
      ((c ^ 2 * e * f : ℝ) : ℂ) * (u * star v) := by
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  rw [heq, Complex.re_ofReal_mul]

lemma pd1c_cauchyBlock_fibers
    {δ C c₁ c₂ x Y : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (eta : ℝ → ℝ)
    (hHm : 0 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x) (hY : 0 < Y)
    (hEta : Function.support eta ⊆ Set.Icc 1 4)
    (t s : Fin K → ℕ) (ht : IsMarkedPrimeTuple x K a t) (hs : IsMarkedPrimeTuple x K a s) :
    pd1c_cauchyBlock x K a Y family beta eta t s =
      ∑ h ∈ Finset.range (⌊4 * (family.Hm x * family.Hn x) / Y⌋₊ + 1),
        (∏ i : Fin K, (bandMass x (a i))⁻¹) ^ 2 *
          eta ((tupleProduct t : ℕ) / Y) * eta ((tupleProduct s : ℕ) / Y) *
            ((∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
              if m * n - 1 = tupleProduct t * h then family.alpha x m * beta n else 0) *
              star (∑ r ∈ familyTerms family x, ∑ v ∈ dyadicIntegers (family.Hn x),
                if r * v - 1 = tupleProduct s * h then family.alpha x r * beta v else 0)).re := by
  let I := (familyTerms family x).product (dyadicIntegers (family.Hn x))
  let H := Finset.range (⌊4 * (family.Hm x * family.Hn x) / Y⌋₊ + 1)
  have hSupport : ∀ v : Fin K → ℕ, IsMarkedPrimeTuple x K a v → ∀ mn ∈ I,
      pd1c_cauchyEntryWeight x K a Y family beta eta (v, mn) ≠ 0 →
        pd1c_cauchyQuotient (v, mn) ∈ H := by
    intro v hv mn hmn hz
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    exact pd1c_cauchy_entry_quotient_bound family beta eta hHm hHn hY hEta (v, mn)
      (Finset.mem_product.mpr ⟨(pd1c_markedTuple_mem _ _ _ _).mpr hv, hmn⟩) hz
  have hGram := pd1c_finite_cross_gram I I H
    (fun mn => pd1c_cauchyQuotient (t, mn)) (fun rs => pd1c_cauchyQuotient (s, rs))
    (fun mn => pd1c_cauchyEntryWeight x K a Y family beta eta (t, mn))
    (fun rs => pd1c_cauchyEntryWeight x K a Y family beta eta (s, rs)) (hSupport t ht) (hSupport s hs)
  have hr := congrArg Complex.re hGram
  simp only [Complex.re_sum, apply_ite, Complex.zero_re] at hr
  unfold pd1c_cauchyBlock
  rw [hr]
  apply Finset.sum_congr rfl
  intro h hh
  rw [pd1c_tuple_fiber_identity x K a Y family beta eta t ht,
    pd1c_tuple_fiber_identity x K a Y family beta eta s hs]
  exact pd1c_real_scaled_gram _ _ _ _ _

lemma pd1c_cauchyBlock_zero_left (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) (t s : Fin K → ℕ)
    (hz : eta ((tupleProduct t : ℕ) / Y) = 0) :
    pd1c_cauchyBlock x K a Y family beta eta t s = 0 := by
  simp [pd1c_cauchyBlock, pd1c_cauchyEntryWeight, hz]

lemma pd1c_cauchyBlock_zero_right (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) (t s : Fin K → ℕ)
    (hz : eta ((tupleProduct s : ℕ) / Y) = 0) :
    pd1c_cauchyBlock x K a Y family beta eta t s = 0 := by
  simp [pd1c_cauchyBlock, pd1c_cauchyEntryWeight, hz]

lemma pd1c_cauchyBlock_bound
    {δ C c₁ c₂ x Y T CDiv : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (eta : ℝ → ℝ)
    (hHm : 0 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x) (hY : 0 < Y) (hT : 0 ≤ T)
    (hEta : Function.support eta ⊆ Set.Icc 1 4) (hEta₀ : ∀ y, 0 ≤ eta y) (hEta₁ : ∀ y, eta y ≤ 1)
    (hAlpha : ∀ m ∈ familyTerms family x, ‖family.alpha x m‖ ≤ T)
    (hBeta : ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ T)
    (hPos : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ m * n)
    (hDiv : ∀ l : ℕ, (l : ℝ) ≤ 4 * Y →
      (∑ h ∈ Finset.range (⌊4 * (family.Hm x * family.Hn x) / Y⌋₊ + 1), (tau (1 + l * h) : ℝ) ^ 2) ≤
        CDiv * ((family.Hm x * family.Hn x) / Y) * (Real.log x) ^ (3 : ℝ))
    (t s : Fin K → ℕ) (ht : IsMarkedPrimeTuple x K a t) (hs : IsMarkedPrimeTuple x K a s)
    (htη : eta ((tupleProduct t : ℕ) / Y) ≠ 0) (hsη : eta ((tupleProduct s : ℕ) / Y) ≠ 0) :
    |pd1c_cauchyBlock x K a Y family beta eta t s| ≤
      (∏ i : Fin K, (bandMass x (a i))⁻¹) ^ 2 * T ^ 4 *
        CDiv * ((family.Hm x * family.Hn x) / Y) * (Real.log x) ^ (3 : ℝ) := by
  let W := ∏ i : Fin K, (bandMass x (a i))⁻¹
  let H := Finset.range (⌊4 * (family.Hm x * family.Hn x) / Y⌋₊ + 1)
  let R := fun b h : ℕ => ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
    if m * n - 1 = b * h then family.alpha x m * beta n else 0
  have htBound : (tupleProduct t : ℝ) ≤ 4 * Y := (div_le_iff₀ hY).mp (hEta htη).2
  have hsBound : (tupleProduct s : ℝ) ≤ 4 * Y := (div_le_iff₀ hY).mp (hEta hsη).2
  have hRt := fun h => pd1c_product_fiber_norm family beta (tupleProduct t) h hT hAlpha hBeta hPos
  have hRs := fun h => pd1c_product_fiber_norm family beta (tupleProduct s) h hT hAlpha hBeta hPos
  have hpoint : ∀ h : ℕ,
      |W ^ 2 * eta ((tupleProduct t : ℕ) / Y) * eta ((tupleProduct s : ℕ) / Y) *
        (R (tupleProduct t) h * star (R (tupleProduct s) h)).re| ≤
        W ^ 2 * T ^ 4 * (((tau (1 + tupleProduct t * h) : ℝ) ^ 2 +
          (tau (1 + tupleProduct s * h) : ℝ) ^ 2) / 2) := by
    intro h
    have hη : 0 ≤ W ^ 2 * eta ((tupleProduct t : ℕ) / Y) * eta ((tupleProduct s : ℕ) / Y) := by
      exact mul_nonneg (mul_nonneg (sq_nonneg W) (hEta₀ _)) (hEta₀ _)
    have hηle : W ^ 2 * eta ((tupleProduct t : ℕ) / Y) * eta ((tupleProduct s : ℕ) / Y) ≤ W ^ 2 := by
      calc
        _ ≤ W ^ 2 * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left (hEta₁ _) (sq_nonneg W)) (hEta₁ _) (hEta₀ _) (by positivity)
        _ = _ := by ring
    have hR : ‖R (tupleProduct t) h * star (R (tupleProduct s) h)‖ ≤
        T ^ 4 * ((tau (1 + tupleProduct t * h) : ℝ) * tau (1 + tupleProduct s * h)) := by
      rw [norm_mul, norm_star]
      have h := mul_le_mul (hRt h) (hRs h) (norm_nonneg _) (by positivity)
      exact h.trans_eq (by ring)
    rw [abs_mul, abs_of_nonneg hη]
    calc
      _ ≤ (W ^ 2 * eta ((tupleProduct t : ℕ) / Y) * eta ((tupleProduct s : ℕ) / Y)) *
          ‖R (tupleProduct t) h * star (R (tupleProduct s) h)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hη
      _ ≤ W ^ 2 * (T ^ 4 * ((tau (1 + tupleProduct t * h) : ℝ) * tau (1 + tupleProduct s * h))) :=
        mul_le_mul hηle hR (norm_nonneg _) (sq_nonneg W)
      _ ≤ _ := by
        have hsq := sq_nonneg ((tau (1 + tupleProduct t * h) : ℝ) - tau (1 + tupleProduct s * h))
        have hcoef : 0 ≤ W ^ 2 * T ^ 4 := by positivity
        have hmul := mul_le_mul_of_nonneg_left (show
            (tau (1 + tupleProduct t * h) : ℝ) * tau (1 + tupleProduct s * h) ≤
              ((tau (1 + tupleProduct t * h) : ℝ) ^ 2 + (tau (1 + tupleProduct s * h) : ℝ) ^ 2) / 2 by nlinarith only [hsq]) hcoef
        nlinarith only [hmul]
  rw [pd1c_cauchyBlock_fibers family beta eta hHm hHn hY hEta t s ht hs]
  change |∑ h ∈ H, W ^ 2 * eta ((tupleProduct t : ℕ) / Y) * eta ((tupleProduct s : ℕ) / Y) *
    (R (tupleProduct t) h * star (R (tupleProduct s) h)).re| ≤ _
  calc
    _ ≤ ∑ h ∈ H, |W ^ 2 * eta ((tupleProduct t : ℕ) / Y) * eta ((tupleProduct s : ℕ) / Y) *
        (R (tupleProduct t) h * star (R (tupleProduct s) h)).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ H, W ^ 2 * T ^ 4 * (((tau (1 + tupleProduct t * h) : ℝ) ^ 2 +
          (tau (1 + tupleProduct s * h) : ℝ) ^ 2) / 2) := Finset.sum_le_sum (fun h hh => hpoint h)
    _ = W ^ 2 * T ^ 4 * ((∑ h ∈ H, (tau (1 + tupleProduct t * h) : ℝ) ^ 2) +
        (∑ h ∈ H, (tau (1 + tupleProduct s * h) : ℝ) ^ 2)) / 2 := by
      rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib]
      ring
    _ ≤ W ^ 2 * T ^ 4 * (2 * (CDiv * ((family.Hm x * family.Hn x) / Y) * (Real.log x) ^ (3 : ℝ))) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [H, two_mul] using add_le_add (hDiv (tupleProduct t) htBound) (hDiv (tupleProduct s) hsBound)
    _ = _ := by dsimp [W]; ring

lemma pd1c_coprime_error_bound
    {δ C c₁ c₂ x Y T CDiv : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (eta : ℝ → ℝ)
    (hHm : 0 ≤ family.Hm x) (hHn : 0 ≤ family.Hn x) (hY : 0 < Y) (hT : 0 ≤ T)
    (hCDiv : 0 ≤ CDiv) (hL : 0 ≤ Real.log x)
    (hEta : Function.support eta ⊆ Set.Icc 1 4) (hEta₀ : ∀ y, 0 ≤ eta y) (hEta₁ : ∀ y, eta y ≤ 1)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (hAlpha : ∀ m ∈ familyTerms family x, ‖family.alpha x m‖ ≤ T)
    (hBeta : ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ T)
    (hPos : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ m * n)
    (hDiv : ∀ l : ℕ, (l : ℝ) ≤ 4 * Y →
      (∑ h ∈ Finset.range (⌊4 * (family.Hm x * family.Hn x) / Y⌋₊ + 1), (tau (1 + l * h) : ℝ) ^ 2) ≤
        CDiv * ((family.Hm x * family.Hn x) / Y) * (Real.log x) ^ (3 : ℝ)) :
    |cauchySquare x K a Y family beta eta - coprimeCauchySquare x K a Y family beta eta| ≤
      16 * (∏ i : Fin K, (bandMass x (a i))⁻¹) ^ 2 * CDiv * T ^ 4 *
        (family.Hm x * family.Hn x) * Y * (Real.log x) ^ (3 : ℝ) *
          (∑ i : Fin K, ∑ p ∈ primeBand x (a i), (1 / (p : ℝ)) ^ 2) := by
  let S := pd1c_markedTupleSet x K a
  let Tset := S.filter (fun t => eta ((tupleProduct t : ℕ) / Y) ≠ 0)
  let D := (∏ i : Fin K, (bandMass x (a i))⁻¹) ^ 2 * T ^ 4 *
    CDiv * ((family.Hm x * family.Hn x) / Y) * (Real.log x) ^ (3 : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hTset : ∀ t ∈ Tset, IsMarkedPrimeTuple x K a t := fun t ht =>
    (pd1c_markedTuple_mem _ _ _ _).mp (Finset.mem_filter.mp ht).1
  have hbound : ∀ t ∈ Tset, (tupleProduct t : ℝ) ≤ 4 * Y := fun t ht =>
    (div_le_iff₀ hY).mp (hEta (Finset.mem_filter.mp ht).2).2
  have heq : cauchySquare x K a Y family beta eta - coprimeCauchySquare x K a Y family beta eta =
      ∑ t ∈ Tset, ∑ s ∈ Tset, if ¬Nat.Coprime (tupleProduct t) (tupleProduct s) then
        pd1c_cauchyBlock x K a Y family beta eta t s else 0 := by
    rw [pd1c_cauchy_difference_blocks]
    simp only [Tset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hz : eta ((tupleProduct t : ℕ) / Y) = 0
    · simp [hz, pd1c_cauchyBlock_zero_left x K a Y family beta eta t _ hz]
    · try rw [if_pos hz]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hs0 : eta ((tupleProduct s : ℕ) / Y) = 0
      · simp [hs0, pd1c_cauchyBlock_zero_right x K a Y family beta eta t s hs0]
      · simp [hs0]
  rw [heq]
  calc
    _ ≤ ∑ t ∈ Tset, ∑ s ∈ Tset, |if ¬Nat.Coprime (tupleProduct t) (tupleProduct s) then
        pd1c_cauchyBlock x K a Y family beta eta t s else 0| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t ht => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ t ∈ Tset, ∑ s ∈ Tset, D * (if ¬Nat.Coprime (tupleProduct t) (tupleProduct s) then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro s hs
      by_cases hc : Nat.Coprime (tupleProduct t) (tupleProduct s)
      · simp [hc]
      · simp only [hc, not_false_eq_true, ite_true, mul_one]
        exact pd1c_cauchyBlock_bound family beta eta hHm hHn hY hT hEta hEta₀ hEta₁ hAlpha hBeta hPos hDiv
          t s (hTset t ht) (hTset s hs) (Finset.mem_filter.mp ht).2 (Finset.mem_filter.mp hs).2
    _ = D * (∑ t ∈ Tset, ∑ s ∈ Tset, if ¬Nat.Coprime (tupleProduct t) (tupleProduct s) then (1 : ℝ) else 0) := by simp only [Finset.mul_sum]
    _ ≤ D * (16 * Y ^ 2 * (∑ i : Fin K, ∑ p ∈ primeBand x (a i), (1 / (p : ℝ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left (pd1c_non_coprime_tuple_count Tset hY hTset hbound hSep) hD
    _ = _ := by dsimp [D]; field_simp

end ArtinPrimitiveRoots.TypeII.PD
