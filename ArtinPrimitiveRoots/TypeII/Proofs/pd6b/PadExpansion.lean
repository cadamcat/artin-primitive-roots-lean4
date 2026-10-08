import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.TupleCounting
import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII Classical
noncomputable section

private theorem star_real (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  apply Complex.ext <;> simp [Complex.star_def]

private theorem realMul_re (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

def coefficientQuadProduct {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (x : ℝ) (beta : ℕ → ℂ) (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  family.alpha x q.1.1 * star (family.alpha x q.2.1) * beta q.1.2 * star (beta q.2.2)

def coefficientQuadChoices {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (x : ℝ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((familyTerms family x) ×ˢ (dyadicIntegers (family.Hn x))) ×ˢ
    ((familyTerms family x) ×ˢ (dyadicIntegers (family.Hn x)))

def rawPairSum {K : ℕ} (F : PDFix K) (x Y : ℝ) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (ta tb : Fin K → ℕ) : ℂ :=
  (((∏ i : Fin K, (bandMass x (F.a i))⁻¹ : ℝ) : ℂ)) ^ 2 *
    ∑ q ∈ coefficientQuadChoices family x,
      if ∃ h : ℕ, q.1.1 * q.1.2 - 1 = tupleProduct ta * h ∧
          q.2.1 * q.2.2 - 1 = tupleProduct tb * h then
        (F.eta ((tupleProduct ta : ℝ) / Y) : ℂ) *
          (F.eta ((tupleProduct tb : ℝ) / Y) : ℂ) * coefficientQuadProduct family x beta q
      else 0

def comparisonPairSum {K : ℕ} (F : PDFix K) (x Y : ℝ) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (ta tb : Fin K → ℕ) : ℂ :=
  (((∏ i : Fin K, (bandMass x (F.a i))⁻¹ : ℝ) : ℂ)) ^ 2 *
    ∑ q ∈ coefficientQuadChoices family x,
      (F.eta ((tupleProduct ta : ℝ) / Y) : ℂ) * (F.eta ((tupleProduct tb : ℝ) / Y) : ℂ) *
        majorKernel x Y F.A₀
          ((tupleProduct tb : ℝ) * (q.1.1 * q.1.2 : ℕ) - (tupleProduct ta : ℝ) * (q.2.1 * q.2.2 : ℕ))
          (tupleProduct ta) (tupleProduct tb) F.psi * coefficientQuadProduct family x beta q

/-- Tuple sums in the major-arc definition have finite band support. -/
theorem majorArcSum_eq_finitePairSum {K : ℕ} (F : PDFix K) (x Y : ℝ) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) :
    majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi =
      ∑ ta ∈ markedTupleChoices x F.a, ∑ tb ∈ markedTupleChoices x F.a,
        comparisonPairSum F x Y family beta ta tb := by
  unfold majorArcSum
  rw [tsum_eq_sum (s := markedTupleChoices x F.a)]
  · apply Finset.sum_congr rfl
    intro ta hta
    rw [tsum_eq_sum (s := markedTupleChoices x F.a)]
    · apply Finset.sum_congr rfl
      intro tb htb
      rw [if_pos ⟨mem_markedTupleChoices.mp hta, mem_markedTupleChoices.mp htb⟩]
      unfold comparisonPairSum coefficientQuadChoices coefficientQuadProduct
      simp only [Finset.sum_product, Nat.cast_mul]
      congr 1
      · norm_cast
      · apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        simp only [mul_assoc]
        ring
    · intro tb htb
      have hn := mt mem_markedTupleChoices.mpr htb
      simp [hn]
  · intro ta hta
    have hn := mt mem_markedTupleChoices.mpr hta
    simp [hn]

/-- Taking real parts gives exactly the frozen coprime Cauchy square. -/
theorem coprimeCauchySquare_eq_real_finitePairSum {K : ℕ} (F : PDFix K) (x Y : ℝ) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) :
    coprimeCauchySquare x K F.a Y family beta F.eta =
      (∑ ta ∈ markedTupleChoices x F.a, ∑ tb ∈ markedTupleChoices x F.a,
        if Nat.Coprime (tupleProduct ta) (tupleProduct tb) then rawPairSum F x Y family beta ta tb else 0).re := by
  unfold coprimeCauchySquare
  rw [tsum_eq_sum (s := markedTupleChoices x F.a)]
  · simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro ta hta
    rw [tsum_eq_sum (s := markedTupleChoices x F.a)]
    · apply Finset.sum_congr rfl
      intro tb htb
      simp only [mem_markedTupleChoices.mp hta, mem_markedTupleChoices.mp htb, true_and]
      by_cases hcop : Nat.Coprime (tupleProduct ta) (tupleProduct tb)
      · simp only [if_pos hcop]
        unfold rawPairSum coefficientQuadChoices coefficientQuadProduct
        simp only [Finset.sum_product, ← Complex.ofReal_pow, realMul_re, Complex.re_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        split_ifs <;> simp only [mul_assoc, realMul_re, Complex.zero_re]

      · simp [hcop]
    · intro tb htb
      have hn := mt mem_markedTupleChoices.mpr htb
      simp [hn]
  · intro ta hta
    have hn := mt mem_markedTupleChoices.mpr hta
    simp [hn]


/-- Swapping the two product pairs conjugates the coefficient product. -/
theorem coefficientQuadProduct_swap_star {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x : ℝ) (beta : ℕ → ℂ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) :
    coefficientQuadProduct family x beta q.swap = star (coefficientQuadProduct family x beta q) := by
  simp only [coefficientQuadProduct, Prod.fst_swap, Prod.snd_swap, star_mul, star_star]
  ring

/-- The raw pair sum is Hermitian under exchanging its marked tuples. -/
theorem rawPairSum_swap_star {K : ℕ} (F : PDFix K) (x Y : ℝ) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (ta tb : Fin K → ℕ) :
    rawPairSum F x Y family beta tb ta = star (rawPairSum F x Y family beta ta tb) := by
  let f (u v : Fin K → ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
    if ∃ h : ℕ, q.1.1 * q.1.2 - 1 = tupleProduct u * h ∧
        q.2.1 * q.2.2 - 1 = tupleProduct v * h then
      (F.eta ((tupleProduct u : ℝ) / Y) : ℂ) * (F.eta ((tupleProduct v : ℝ) / Y) : ℂ) *
        coefficientQuadProduct family x beta q else 0
  have hsum : (∑ q ∈ coefficientQuadChoices family x, f tb ta q) =
      ∑ q ∈ coefficientQuadChoices family x, star (f ta tb q) := by
    apply Finset.sum_bij (fun q hq => q.swap)
    · intro q hq
      exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hq).2, (Finset.mem_product.mp hq).1⟩
    · intro q hq q' hq' heq
      exact Prod.swap_injective heq
    · intro q hq
      exact ⟨q.swap, Finset.mem_product.mpr ⟨(Finset.mem_product.mp hq).2, (Finset.mem_product.mp hq).1⟩, rfl⟩
    · intro q hq
      have hi : (∃ h : ℕ, q.2.1 * q.2.2 - 1 = tupleProduct ta * h ∧
          q.1.1 * q.1.2 - 1 = tupleProduct tb * h) ↔
          (∃ h : ℕ, q.1.1 * q.1.2 - 1 = tupleProduct tb * h ∧
            q.2.1 * q.2.2 - 1 = tupleProduct ta * h) := by
        constructor <;> rintro ⟨h, hh₁, hh₂⟩ <;> exact ⟨h, hh₂, hh₁⟩
      have hs := coefficientQuadProduct_swap_star family x beta q
      dsimp [f]
      simp only [hi]
      split_ifs
      · change (F.eta ((tupleProduct tb : ℝ) / Y) : ℂ) * (F.eta ((tupleProduct ta : ℝ) / Y) : ℂ) *
          coefficientQuadProduct family x beta q =
            star ((F.eta ((tupleProduct ta : ℝ) / Y) : ℂ) * (F.eta ((tupleProduct tb : ℝ) / Y) : ℂ) *
              coefficientQuadProduct family x beta q.swap)
        rw [hs, star_mul, star_mul, star_star, star_real, star_real]
        ring
      · change (0 : ℂ) = star (0 : ℂ)
        exact (star_zero ℂ).symm
  unfold rawPairSum
  change (((∏ i : Fin K, (bandMass x (F.a i))⁻¹ : ℝ) : ℂ)) ^ 2 *
    (∑ q ∈ coefficientQuadChoices family x, f tb ta q) =
      star ((((∏ i : Fin K, (bandMass x (F.a i))⁻¹ : ℝ) : ℂ)) ^ 2 *
        (∑ q ∈ coefficientQuadChoices family x, f ta tb q))
  rw [hsum]
  simp only [star_mul, star_pow, star_sum, star_real]
  ring

/-- The total coprime raw sum is real, by the tuple-swap involution. -/
theorem rawCoprimeSum_star {K : ℕ} (F : PDFix K) (x Y : ℝ) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) :
    star (∑ ta ∈ markedTupleChoices x F.a, ∑ tb ∈ markedTupleChoices x F.a,
      if Nat.Coprime (tupleProduct ta) (tupleProduct tb) then rawPairSum F x Y family beta ta tb else 0) =
      ∑ ta ∈ markedTupleChoices x F.a, ∑ tb ∈ markedTupleChoices x F.a,
        if Nat.Coprime (tupleProduct ta) (tupleProduct tb) then rawPairSum F x Y family beta ta tb else 0 := by
  simp only [star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ta hta
  apply Finset.sum_congr rfl
  intro tb htb
  by_cases hc : Nat.Coprime (tupleProduct ta) (tupleProduct tb)
  · have hc' : Nat.Coprime (tupleProduct tb) (tupleProduct ta) := hc.symm
    simp only [if_pos hc, if_pos hc']
    change star (rawPairSum F x Y family beta tb ta) = rawPairSum F x Y family beta ta tb
    exact (rawPairSum_swap_star F x Y family beta tb ta).symm
  · have hc' : ¬ Nat.Coprime (tupleProduct tb) (tupleProduct ta) := fun h => hc h.symm
    simp only [if_neg hc, if_neg hc', star_zero]

/-- The frozen real Cauchy square casts to the complex coprime raw sum. -/
theorem coprimeCauchySquare_cast_eq_finitePairSum {K : ℕ} (F : PDFix K) (x Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) :
    (coprimeCauchySquare x K F.a Y family beta F.eta : ℂ) =
      ∑ ta ∈ markedTupleChoices x F.a, ∑ tb ∈ markedTupleChoices x F.a,
        if Nat.Coprime (tupleProduct ta) (tupleProduct tb) then rawPairSum F x Y family beta ta tb else 0 := by
  rw [coprimeCauchySquare_eq_real_finitePairSum]
  have hs := rawCoprimeSum_star F x Y family beta
  have hi := congrArg Complex.im hs
  simp only [Complex.star_def, Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith


/-- The pad-independent signed contribution of one coefficient quadruple. -/
def padQuadCore {K : ℕ} (F : PDFix K) (x Y : ℝ) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) (ta tb : Fin K → ℕ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  (F.eta ((tupleProduct ta : ℝ) / Y) : ℂ) * (F.eta ((tupleProduct tb : ℝ) / Y) : ℂ) *
    ((if ∃ h : ℕ, q.1.1 * q.1.2 - 1 = tupleProduct ta * h ∧
        q.2.1 * q.2.2 - 1 = tupleProduct tb * h then 1 else 0) -
      majorKernel x Y F.A₀
        ((tupleProduct tb : ℝ) * (q.1.1 * q.1.2 : ℕ) - (tupleProduct ta : ℝ) * (q.2.1 * q.2.2 : ℕ))
        (tupleProduct ta) (tupleProduct tb) F.psi) * coefficientQuadProduct family x beta q

theorem rawPairSum_sub_comparisonPairSum_eq_core {K : ℕ} (F : PDFix K) (x Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (ta tb : Fin K → ℕ) :
    rawPairSum F x Y family beta ta tb - comparisonPairSum F x Y family beta ta tb =
      (((∏ i : Fin K, (bandMass x (F.a i))⁻¹ : ℝ) : ℂ)) ^ 2 *
        ∑ q ∈ coefficientQuadChoices family x, padQuadCore F x Y family beta ta tb q := by
  unfold rawPairSum comparisonPairSum padQuadCore
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs <;> ring

end
end ArtinPrimitiveRoots.TypeII.PD
