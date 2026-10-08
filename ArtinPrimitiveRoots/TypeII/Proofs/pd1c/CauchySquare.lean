import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical ArtinPrimitiveRoots.TypeII

set_option maxHeartbeats 1000000

lemma pd1c_finite_gram_identity {α : Type*} [DecidableEq α]
    (s : Finset α) (k : α → ℕ) (z : α → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, if k i = k j then (z i * star (z j)).re else 0) =
      ∑ h ∈ s.image k, ‖∑ i ∈ s, if k i = h then z i else 0‖ ^ 2 := by
  have hc : (∑ h ∈ s.image k,
      (∑ i ∈ s, if k i = h then z i else 0) *
        star (∑ j ∈ s, if k j = h then z j else 0)) =
      ∑ i ∈ s, ∑ j ∈ s, if k i = k j then z i * star (z j) else 0 := by
    simp only [star_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : k i = k j
    · rw [if_pos hij]
      rw [Finset.sum_eq_single (k i)]
      · simp [hij]
      · intro h hh hne
        have : k i ≠ h := Ne.symm hne
        simp [this]
      · intro hnot
        exact (hnot (Finset.mem_image.mpr ⟨i, hi, rfl⟩)).elim
    · rw [if_neg hij]
      apply Finset.sum_eq_zero
      intro h hh
      by_cases hih : k i = h
      · have hjh : k j ≠ h := by
          intro hjh
          exact hij (hih.trans hjh.symm)
        simp [hjh]
      · simp [hih]
  have hr := congrArg Complex.re hc
  simp only [Complex.re_sum, apply_ite, Complex.zero_re] at hr
  rw [← hr]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.mul_re, Complex.normSq_apply]

lemma pd1c_finite_gram_nonneg {α : Type*} [DecidableEq α]
    (s : Finset α) (k : α → ℕ) (z : α → ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, if k i = k j then (z i * star (z j)).re else 0 := by
  rw [pd1c_finite_gram_identity]
  exact Finset.sum_nonneg fun h hh => sq_nonneg _


noncomputable def pd1c_markedTupleSet (x : ℝ) (K : ℕ) (a : Fin K → ℝ) :
    Finset (Fin K → ℕ) := Fintype.piFinset fun i => primeBand x (a i)

lemma pd1c_markedTuple_mem (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (t : Fin K → ℕ) :
    t ∈ pd1c_markedTupleSet x K a ↔ IsMarkedPrimeTuple x K a t := by
  simp only [pd1c_markedTupleSet, Fintype.mem_piFinset, IsMarkedPrimeTuple]

lemma pd1c_tupleProduct_pos {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {t : Fin K → ℕ}
    (ht : IsMarkedPrimeTuple x K a t) : 0 < tupleProduct t := by
  apply Finset.prod_pos
  intro i hi
  have hprime : (t i).Prime := (Finset.mem_filter.mp (ht i)).2.1
  exact hprime.pos

lemma pd1c_common_quotient (A B a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∃ h : ℕ, A = a * h ∧ B = b * h) ↔
      a ∣ A ∧ b ∣ B ∧ A / a = B / b := by
  constructor
  · rintro ⟨h, rfl, rfl⟩
    simp [Nat.mul_div_cancel_left _ ha, Nat.mul_div_cancel_left _ hb]
  · rintro ⟨hA, hB, heq⟩
    refine ⟨A / a, (Nat.mul_div_cancel' hA).symm, ?_⟩
    rw [heq]
    exact (Nat.mul_div_cancel' hB).symm

lemma pd1c_cauchySquare_finite_sum (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) :
    cauchySquare x K a Y family beta eta =
      ∑ ta ∈ pd1c_markedTupleSet x K a, ∑ tb ∈ pd1c_markedTupleSet x K a,
        (∏ i : Fin K, (bandMass x (a i))⁻¹) ^ 2 *
          (∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
            ∑ r ∈ familyTerms family x, ∑ s ∈ dyadicIntegers (family.Hn x),
              if ∃ h : ℕ, m * n - 1 = tupleProduct ta * h ∧
                  r * s - 1 = tupleProduct tb * h then
                eta ((tupleProduct ta : ℕ) / Y) * eta ((tupleProduct tb : ℕ) / Y) *
                  (family.alpha x m * star (family.alpha x r) * beta n * star (beta s)).re
              else 0) := by
  unfold cauchySquare
  rw [tsum_eq_sum (s := pd1c_markedTupleSet x K a)]
  · apply Finset.sum_congr rfl
    intro ta hta
    have ha := (pd1c_markedTuple_mem x K a ta).mp hta
    rw [tsum_eq_sum (s := pd1c_markedTupleSet x K a)]
    · apply Finset.sum_congr rfl
      intro tb htb
      have hb := (pd1c_markedTuple_mem x K a tb).mp htb
      simp only [ha, hb, and_self, ite_true]
    · intro tb htb
      have hb : ¬ IsMarkedPrimeTuple x K a tb := by
        exact mt (pd1c_markedTuple_mem x K a tb).mpr htb
      simp [hb]
  · intro ta hta
    have ha : ¬ IsMarkedPrimeTuple x K a ta := by
      exact mt (pd1c_markedTuple_mem x K a ta).mpr hta
    simp [ha]


abbrev pd1c_CauchyEntry (K : ℕ) := (Fin K → ℕ) × (ℕ × ℕ)

noncomputable def pd1c_cauchyEntrySet (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) : Finset (pd1c_CauchyEntry K) :=
  (pd1c_markedTupleSet x K a).product ((familyTerms family x).product (dyadicIntegers (family.Hn x)))

noncomputable def pd1c_cauchyQuotient {K : ℕ} (i : pd1c_CauchyEntry K) : ℕ :=
  (i.2.1 * i.2.2 - 1) / tupleProduct i.1

noncomputable def pd1c_cauchyEntryWeight (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) (i : pd1c_CauchyEntry K) : ℂ :=
  ((∏ j : Fin K, (bandMass x (a j))⁻¹ : ℝ) : ℂ) * (eta ((tupleProduct i.1 : ℕ) / Y) : ℂ) *
    if tupleProduct i.1 ∣ i.2.1 * i.2.2 - 1 then family.alpha x i.2.1 * beta i.2.2 else 0

noncomputable def pd1c_cauchyFiber (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) (h : ℕ) : ℂ :=
  ∑ i ∈ pd1c_cauchyEntrySet x K a family,
    if pd1c_cauchyQuotient i = h then pd1c_cauchyEntryWeight x K a Y family beta eta i else 0

lemma pd1c_cauchySquare_entry_gram (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) :
    cauchySquare x K a Y family beta eta =
      ∑ i ∈ pd1c_cauchyEntrySet x K a family, ∑ j ∈ pd1c_cauchyEntrySet x K a family,
        if pd1c_cauchyQuotient i = pd1c_cauchyQuotient j then
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
  change cauchySquare x K a Y family beta eta =
    ∑ i ∈ s, ∑ j ∈ s, if k i = k j then (z i * star (z j)).re else 0
  rw [pd1c_cauchySquare_finite_sum]
  simp only [Finset.mul_sum]
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


lemma pd1c_cauchySquare_nonneg (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) : 0 ≤ cauchySquare x K a Y family beta eta := by
  rw [pd1c_cauchySquare_entry_gram]
  exact pd1c_finite_gram_nonneg _ _ _

lemma pd1c_cauchySquare_fiber_gram (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) :
    cauchySquare x K a Y family beta eta =
      ∑ h ∈ (pd1c_cauchyEntrySet x K a family).image pd1c_cauchyQuotient,
        ‖pd1c_cauchyFiber x K a Y family beta eta h‖ ^ 2 := by
  rw [pd1c_cauchySquare_entry_gram]
  simpa only [pd1c_cauchyFiber] using pd1c_finite_gram_identity
    (pd1c_cauchyEntrySet x K a family) pd1c_cauchyQuotient
    (pd1c_cauchyEntryWeight x K a Y family beta eta)


lemma pd1c_finite_weighted_cauchy {ι : Type*} (s : Finset ι) (b z : ι → ℂ)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∑ i ∈ s, b i * z i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  have htri : ‖∑ i ∈ s, b i * z i‖ ≤ ∑ i ∈ s, ‖z i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖b i * z i‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        simpa using mul_le_mul_of_nonneg_right (hb i hi) (norm_nonneg (z i))
  calc
    _ ≤ (∑ i ∈ s, ‖z i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ _ := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖z i‖)

end ArtinPrimitiveRoots.TypeII.PD
