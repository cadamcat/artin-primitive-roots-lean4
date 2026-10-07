import ArtinPrimitiveRoots.TypeII.PD.Defs

/-! Determinant and root-counting statements, PD `03-determinant.tex:68-737`. -/

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
open ArtinPrimitiveRoots.TypeII

set_option maxHeartbeats 1000000

/-- `t2:pd.cauchy` — PD `03-determinant.tex:68-169`. The dyadic decomposition, Cauchy square,
coprime reduction, and progression-divisor estimate used to reduce the marked bilinear form to
the determinant moment. Fixed parameters precede all asymptotic constants. Correction: `sol-gate-b`
restricted the arithmetic equivalence to positive products and aligned the dyadic cutoff with PD's
source exponent `1/5`. -/
theorem cauchy_decomposition
    (δ C Dstar q_d c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : ValidBands K a) :
    ∀ A : ℝ, 0 < A →
      ∃ C_A Cscale Cmain CDiv x₀ : ℝ,
        0 < C_A ∧ 0 < Cscale ∧ 0 < Cmain ∧ 0 < CDiv ∧ 2 ≤ x₀ ∧
          ∀ family : CoefficientFamily δ C c₁ c₂,
            HasLongCoefficientCancellation family →
            ∀ x : ℝ, x₀ ≤ x → family.xMin ≤ x →
              ∀ eta : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta →
                Function.support eta ⊆ Set.Icc 1 4 →
                (∀ y, 0 ≤ eta y) → IsDyadicPartition eta →
                ∀ beta : ℕ → ℂ,
                  (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                    roughAbove n (roughCutoff x)) →
                  (∀ n ∈ dyadicIntegers (family.Hn x),
                    ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
                  ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                    let X := family.Hm x * family.Hn x
                    let Sigma := coefficientBilinearSum x K a q_d family beta F
                    (‖Sigma - ∑ Y ∈ dyadicScales x K,
                        dyadicCauchyPiece x K a q_d Y family beta F eta‖ ≤
                      C_A * X * Real.rpow (Real.log x) (-A)) ∧
                    (∀ Y ∈ dyadicScales x K,
                      0 ≤ cauchySquare x K a Y family beta eta ∧
                      ‖dyadicCauchyPiece x K a q_d Y family beta F eta‖ ^ 2 ≤
                        Cmain * (X / Y) * cauchySquare x K a Y family beta eta ∧
                      |cauchySquare x K a Y family beta eta -
                        coprimeCauchySquare x K a Y family beta eta| ≤
                        C_A * X * Y * Real.rpow (Real.log x) (-A)) ∧
                    (∀ ta tb : Fin K → ℕ,
                      IsMarkedPrimeTuple x K a ta → IsMarkedPrimeTuple x K a tb →
                      Nat.Coprime (tupleProduct ta) (tupleProduct tb) →
                      ∀ m n r s : ℕ,
                        1 ≤ m * n → 1 ≤ r * s →
                        ((∃ h : ℕ, m * n - 1 = tupleProduct ta * h ∧
                          r * s - 1 = tupleProduct tb * h) ↔
                          ((tupleProduct tb : ℕ) : ℤ) * (m : ℤ) * (n : ℤ) -
                            ((tupleProduct ta : ℕ) : ℤ) * (r : ℤ) * (s : ℤ) =
                              (tupleProduct tb : ℤ) - (tupleProduct ta : ℤ))) ∧
                    (∀ Y ∈ dyadicScales x K, ∀ l : ℕ,
                      Y / 2 ≤ (l : ℝ) → (l : ℝ) ≤ 2 * Y →
                        (∑ h ∈ Finset.range (⌊X / Y⌋₊ + 1),
                          (tau (1 + l * h) : ℝ) ^ 2) ≤
                          CDiv * (X / Y) * Real.rpow (Real.log x) 3) ∧
                    (Finset.card (dyadicScales x K) : ℝ) ≤ Cscale * Real.log x ∧
                    (∀ Y ∈ dyadicScales x K,
                      (1 / 20 : ℝ) * Real.rpow (Real.log x) (1 / 10 : ℝ) ≤
                        Real.log Y ∧ Real.log Y ≤ Cscale * Real.rpow (Real.log x) (1 / 5 : ℝ)) := by
  sorry

/-- `det:good-state` — PD `03-determinant.tex:269-293`. For fixed valid marked lists, the
Lebesgue measure of ratios failing either physical-position test is exponentially small. -/
theorem good_state
    (K : ℕ) (a : Fin K → ℝ) (ha : ValidBands K a) :
    ∃ c x₀ : ℝ, 0 < c ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ d₀ : ℕ, d₀ ∈ padScales x K →
          ∀ Y ∈ dyadicScales x K,
            ∀ p : PrimeLists x K, ValidPrimeLists x K a p →
              (∫ r in (0 : ℝ)..1,
                if IsGoodRatio x Y (d₀ : ℝ) K a p r then (0 : ℝ) else 1) ≤
                Real.exp (-c * Real.rpow (Real.log x) (1 / 10 : ℝ)) := by
  sorry

private lemma endpoint_second_mem_dyadic
    {x Hn : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm : ℝ}
    (P : PhysicalState x K a H' Hm Hn) :
    P.second ∈ dyadicIntegers Hn := by
  have hHn : 0 ≤ Hn := by
    have hs : (0 : ℝ) ≤ (P.second : ℝ) := Nat.cast_nonneg P.second
    linarith [P.second_upper, hs]
  have hfloor : P.second ≤ ⌊2 * Hn⌋₊ :=
    (Nat.le_floor_iff (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hHn)).2 P.second_upper
  simp only [dyadicIntegers, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hfloor, ⟨P.second_lower, P.second_upper⟩⟩

private lemma endpointF_pointwise_bound
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (hx : 2 ≤ x)
    (beta : ℕ → ℂ)
    (hbeta : ∀ n ∈ dyadicIntegers (family.Hn x),
      ‖beta n‖ ≤ Real.rpow (Real.log x) C)
    {H' : ℝ} (P : PhysicalState x K a H' (family.Hm x) (family.Hn x)) :
    ‖endpointF x K a family beta P‖ ≤
      Real.rpow (Real.log x) C * Real.rpow (Real.log x) C := by
  classical
  have hlog : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  have hα :
    ‖family.alpha x (P.first / groupLabelProduct P)‖ ≤ Real.rpow (Real.log x) C := by
    by_cases hzero : family.alpha x (P.first / groupLabelProduct P) = 0
    · simpa [hzero] using (Real.rpow_nonneg (le_of_lt hlog) C)
    · exact family.coefficient_bound x hx _
        (family.rough_support x hx _ hzero).1
  have hβ : ‖beta P.second‖ ≤ Real.rpow (Real.log x) C :=
    hbeta P.second (endpoint_second_mem_dyadic P)
  by_cases hG : Squarefree (groupLabelProduct P)
  · simp only [endpointF, hG, ↓reduceIte, norm_mul, norm_star]
    exact mul_le_mul hα hβ (norm_nonneg _) (Real.rpow_nonneg (le_of_lt hlog) C)
  · simpa [endpointF, hG] using
      mul_nonneg (Real.rpow_nonneg (le_of_lt hlog) C) (Real.rpow_nonneg (le_of_lt hlog) C)

private lemma endpointG_pointwise_bound
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (hx : 2 ≤ x)
    (beta : ℕ → ℂ)
    (hbeta : ∀ n ∈ dyadicIntegers (family.Hn x),
      ‖beta n‖ ≤ Real.rpow (Real.log x) C)
    {H' : ℝ} (P : PhysicalState x K a H' (family.Hm x) (family.Hn x)) :
    ‖endpointG x K a family beta P‖ ≤
      Real.rpow (Real.log x) C * Real.rpow (Real.log x) C := by
  classical
  have hlog : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  have hα :
    ‖family.alpha x (P.first / groupLabelProduct P)‖ ≤ Real.rpow (Real.log x) C := by
    by_cases hzero : family.alpha x (P.first / groupLabelProduct P) = 0
    · simpa [hzero] using (Real.rpow_nonneg (le_of_lt hlog) C)
    · exact family.coefficient_bound x hx _
        (family.rough_support x hx _ hzero).1
  have hβ : ‖beta P.second‖ ≤ Real.rpow (Real.log x) C :=
    hbeta P.second (endpoint_second_mem_dyadic P)
  by_cases hG : Squarefree (groupLabelProduct P)
  · simp only [endpointG, hG, ↓reduceIte, norm_mul, norm_star]
    exact mul_le_mul hα hβ (norm_nonneg _) (Real.rpow_nonneg (le_of_lt hlog) C)
  · simpa [endpointG, hG] using
      mul_nonneg (Real.rpow_nonneg (le_of_lt hlog) C) (Real.rpow_nonneg (le_of_lt hlog) C)

private lemma endpointF_sup_bound
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (hx : 2 ≤ x)
    (beta : ℕ → ℂ)
    (hbeta : ∀ n ∈ dyadicIntegers (family.Hn x),
      ‖beta n‖ ≤ Real.rpow (Real.log x) C)
    (H' : ℝ) :
    physicalSupNorm x K a
        (endpointFVector x K a H' (family.Hm x) (family.Hn x) family beta) ≤
      Real.rpow (Real.log x) C * Real.rpow (Real.log x) C := by
  classical
  have hlog : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  unfold physicalSupNorm
  refine Real.sSup_le ?_ ?_
  · intro y hy
    rcases hy with ⟨P, rfl⟩
    exact endpointF_pointwise_bound family hx beta hbeta P
  · exact mul_nonneg (Real.rpow_nonneg (le_of_lt hlog) C)
      (Real.rpow_nonneg (le_of_lt hlog) C)

private lemma endpointG_sup_bound
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (hx : 2 ≤ x)
    (beta : ℕ → ℂ)
    (hbeta : ∀ n ∈ dyadicIntegers (family.Hn x),
      ‖beta n‖ ≤ Real.rpow (Real.log x) C)
    (H' : ℝ) :
    physicalSupNorm x K a
        (endpointGVector x K a H' (family.Hm x) (family.Hn x) family beta) ≤
      Real.rpow (Real.log x) C * Real.rpow (Real.log x) C := by
  classical
  have hlog : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  unfold physicalSupNorm
  refine Real.sSup_le ?_ ?_
  · intro y hy
    rcases hy with ⟨P, rfl⟩
    exact endpointG_pointwise_bound family hx beta hbeta P
  · exact mul_nonneg (Real.rpow_nonneg (le_of_lt hlog) C)
      (Real.rpow_nonneg (le_of_lt hlog) C)

private lemma groupLabelProduct_pos
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn) : 0 < groupLabelProduct P := by
  unfold groupLabelProduct
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  exact (P.label_prime i j).pos

private lemma groupLabelProduct_dvd_first
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn)
    (hSq : Squarefree (groupLabelProduct P)) :
    groupLabelProduct P ∣ P.first := by
  have hG : groupLabelProduct P ≠ 0 := (groupLabelProduct_pos P).ne'
  have hfirst : P.first ≠ 0 := by
    have hrange := P.completion_range
    have hpos : (0 : ℤ) < (P.first : ℤ) := lt_of_le_of_lt hrange.1 hrange.2
    have hn : 0 < P.first := by exact_mod_cast hpos
    omega
  apply (Nat.factorization_le_iff_dvd hG hfirst).1
  intro p
  by_cases hp : p.Prime
  · by_cases hpg : p ∣ groupLabelProduct P
    · have hfactorG := Nat.factorization_eq_one_of_squarefree hSq hp hpg
      have hpf : p ∣ P.first := by
        have hprod : p ∣ ∏ i : Fin K, ∏ j : Fin (slotCount x), P.labels i j := by
          simpa [groupLabelProduct] using hpg
        rcases (hp.prime.dvd_finsetProd_iff _).1 hprod with ⟨i, hi, hinner⟩
        rcases (hp.prime.dvd_finsetProd_iff _).1 hinner with ⟨j, hj, hlabel⟩
        have hEq : p = P.labels i j :=
          (Nat.prime_dvd_prime_iff_eq hp (P.label_prime i j)).1 hlabel
        rw [hEq]
        exact P.label_divides i j
      rw [hfactorG]
      exact (hp.dvd_iff_one_le_factorization hfirst).1 hpf
    · rw [Nat.factorization_eq_zero_of_not_dvd hpg]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

private lemma physicalState_eq_of_positions_labels
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P Q : PhysicalState x K a H' Hm Hn)
    (hfirst : P.first = Q.first) (hsecond : P.second = Q.second)
    (hlabels : P.labels = Q.labels) : P = Q := by
  have hfirstPos : 0 < P.first := by
    have hrange := P.completion_range
    have hpos : (0 : ℤ) < (P.first : ℤ) := lt_of_le_of_lt hrange.1 hrange.2
    exact_mod_cast hpos
  have hcop : Int.gcd (P.first : ℤ) (P.second : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact P.primitive.gcd_eq_one
  have hfirstZ : (P.first : ℤ) = (Q.first : ℤ) := by exact_mod_cast hfirst
  have hsecondZ : (P.second : ℤ) = (Q.second : ℤ) := by exact_mod_cast hsecond
  have hdiv : (P.first : ℤ) ∣ (P.completionC - Q.completionC) * (P.second : ℤ) := by
    have hQdet : (P.first : ℤ) * Q.completionD -
        (P.second : ℤ) * Q.completionC = 1 := by
      simpa [hfirstZ.symm, hsecondZ.symm] using Q.det_one
    refine ⟨P.completionD - Q.completionD, ?_⟩
    calc
      (P.completionC - Q.completionC) * (P.second : ℤ) =
          (1 + (P.second : ℤ) * P.completionC) -
            (1 + (P.second : ℤ) * Q.completionC) := by ring
      _ = (((P.first : ℤ) * P.completionD - (P.second : ℤ) * P.completionC) +
            (P.second : ℤ) * P.completionC) -
          (((P.first : ℤ) * Q.completionD - (P.second : ℤ) * Q.completionC) +
            (P.second : ℤ) * Q.completionC) := by rw [P.det_one, hQdet]
      _ = (P.first : ℤ) * (P.completionD - Q.completionD) := by ring
  have hcdiv : (P.first : ℤ) ∣ P.completionC - Q.completionC :=
    Int.dvd_of_dvd_mul_left_of_gcd_one hdiv hcop
  have hQupper : Q.completionC < (P.first : ℤ) := by
    calc
      Q.completionC < (Q.first : ℤ) := Q.completion_range.2
      _ = (P.first : ℤ) := hfirstZ.symm
  have hcabs : |P.completionC - Q.completionC| < (P.first : ℤ) := by
    rw [abs_lt]
    constructor
    · have h := P.completion_range.1
      have h' := Q.completion_range.1
      omega
    · have h := P.completion_range.2
      have h' := Q.completion_range.1
      omega
  have hC : P.completionC = Q.completionC := by
    have hz := Int.eq_zero_of_abs_lt_dvd hcdiv hcabs
    exact sub_eq_zero.mp hz
  have hDmul : (P.first : ℤ) * P.completionD = (P.first : ℤ) * Q.completionD := by
    have hQdet : (P.first : ℤ) * Q.completionD -
        (P.second : ℤ) * Q.completionC = 1 := by
      simpa [hfirstZ.symm, hsecondZ.symm] using Q.det_one
    calc
      (P.first : ℤ) * P.completionD =
          ((P.first : ℤ) * P.completionD - (P.second : ℤ) * P.completionC) +
            (P.second : ℤ) * P.completionC := by ring
      _ = ((P.first : ℤ) * Q.completionD - (P.second : ℤ) * Q.completionC) +
            (P.second : ℤ) * Q.completionC := by rw [P.det_one, hQdet, hC]
      _ = (P.first : ℤ) * Q.completionD := by ring
  have hD : P.completionD = Q.completionD :=
    mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hfirstPos)) hDmul
  cases P
  cases Q
  simp_all

private abbrev EndpointLabelChoice (x : ℝ) (K : ℕ) (a : Fin K → ℝ) :=
  ∀ i : Fin K, Fin (slotCount x) → {p : ℕ // p ∈ primeBand x (a i)}

private noncomputable def endpointLabelChoiceOfState
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn) : EndpointLabelChoice x K a :=
  fun i j => ⟨P.labels i j, P.label_in_band i j⟩

private noncomputable def endpointLabelChoiceProduct
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p : EndpointLabelChoice x K a) : ℕ :=
  ∏ i : Fin K, ∏ j : Fin (slotCount x), (p i j).val

private lemma endpointLabelChoiceProduct_eq
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn) :
    endpointLabelChoiceProduct (endpointLabelChoiceOfState P) = groupLabelProduct P := by
  rfl

private abbrev EndpointStateCoordinates
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (H' Hm Hn : ℝ) :=
  EndpointLabelChoice x K a ×
    (Fin (⌊16 * H' * Hm⌋₊ + 1) × Fin (⌊2 * Hn⌋₊ + 1))

private noncomputable def endpointStateCoordinates
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn) : EndpointStateCoordinates x K a H' Hm Hn :=
  (endpointLabelChoiceOfState P,
    (⟨P.first, Nat.lt_succ_of_le <| (Nat.le_floor_iff <|
        le_trans (Nat.cast_nonneg P.first) P.first_upper).2 P.first_upper⟩,
     ⟨P.second, Nat.lt_succ_of_le <| (Nat.le_floor_iff <|
        le_trans (Nat.cast_nonneg P.second) P.second_upper).2 P.second_upper⟩))

private lemma endpointStateCoordinates_injective
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ} :
    Function.Injective (@endpointStateCoordinates x K a H' Hm Hn) := by
  intro P Q h
  have hlabels' : endpointLabelChoiceOfState P = endpointLabelChoiceOfState Q :=
    congrArg Prod.fst h
  have hfirst : P.first = Q.first := by
    simpa [endpointStateCoordinates] using
      congrArg (fun z : EndpointStateCoordinates x K a H' Hm Hn => z.2.1.val) h
  have hsecond : P.second = Q.second := by
    simpa [endpointStateCoordinates] using
      congrArg (fun z : EndpointStateCoordinates x K a H' Hm Hn => z.2.2.val) h
  have hlabels : P.labels = Q.labels := by
    funext i j
    exact congrArg Subtype.val (congrArg (fun p => p i j) hlabels')
  exact physicalState_eq_of_positions_labels P Q hfirst hsecond hlabels

private abbrev EndpointSquarefreeCoordinates
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (H' Hm Hn : ℝ) :=
  Σ l : EndpointLabelChoice x K a,
    Fin (⌊16 * H' * Hm / (endpointLabelChoiceProduct l : ℝ)⌋₊) ×
      Fin (⌊2 * Hn⌋₊)

private def endpointSquarefreeCoordinates_first
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (z : EndpointSquarefreeCoordinates x K a H' Hm Hn) : ℕ := z.2.1.val

private def endpointSquarefreeCoordinates_second
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (z : EndpointSquarefreeCoordinates x K a H' Hm Hn) : ℕ := z.2.2.val

private noncomputable def endpointSquarefreeCoordinates
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (hHn : 0 < Hn)
    (P : {P : PhysicalState x K a H' Hm Hn // Squarefree (groupLabelProduct P)}) :
    EndpointSquarefreeCoordinates x K a H' Hm Hn := by
  classical
  let l := endpointLabelChoiceOfState P.val
  let G := groupLabelProduct P.val
  let k := P.val.first / G
  have hGpos : 0 < G := groupLabelProduct_pos P.val
  have hGreal : 0 < (G : ℝ) := Nat.cast_pos.mpr hGpos
  have hdiv : G ∣ P.val.first := groupLabelProduct_dvd_first P.val P.property
  have hfirstEq : G * k = P.val.first := Nat.mul_div_cancel' hdiv
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    rw [hk0, mul_zero] at hfirstEq
    have hrange := P.val.completion_range
    have hfirstpos : 0 < P.val.first := by
      have h : (0 : ℤ) < (P.val.first : ℤ) := lt_of_le_of_lt hrange.1 hrange.2
      exact_mod_cast h
    omega
  have hnum : 0 ≤ 16 * H' * Hm := le_trans (Nat.cast_nonneg P.val.first) P.val.first_upper
  have hkreal : (k : ℝ) ≤ 16 * H' * Hm / (G : ℝ) := by
    rw [le_div_iff₀ hGreal]
    have heq : (G : ℝ) * (k : ℝ) = (P.val.first : ℝ) := by exact_mod_cast hfirstEq
    calc
      (k : ℝ) * (G : ℝ) = (G : ℝ) * (k : ℝ) := by ring
      _ = (P.val.first : ℝ) := heq
      _ ≤ 16 * H' * Hm := P.val.first_upper
  have hkfloor : k ≤ ⌊16 * H' * Hm / (G : ℝ)⌋₊ :=
    (Nat.le_floor_iff (div_nonneg hnum (le_of_lt hGreal))).2 hkreal
  have hsecpos : 0 < P.val.second := by
    have h : (0 : ℝ) < (P.val.second : ℝ) := lt_of_lt_of_le hHn P.val.second_lower
    exact_mod_cast h
  have hsecnum : 0 ≤ 2 * Hn := le_trans (Nat.cast_nonneg P.val.second) P.val.second_upper
  have hsecfloor : P.val.second ≤ ⌊2 * Hn⌋₊ :=
    (Nat.le_floor_iff hsecnum).2 P.val.second_upper
  have hlprod : endpointLabelChoiceProduct l = G := endpointLabelChoiceProduct_eq P.val
  have hkfloor' : k ≤ ⌊16 * H' * Hm / (endpointLabelChoiceProduct l : ℝ)⌋₊ := by
    simpa [hlprod] using hkfloor
  refine ⟨l, (⟨k - 1, ?_⟩, ⟨P.val.second - 1, ?_⟩)⟩
  · omega
  · omega

private lemma endpointSquarefreeCoordinates_injective
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ} (hHn : 0 < Hn) :
    Function.Injective (@endpointSquarefreeCoordinates x K a H' Hm Hn hHn) := by
  classical
  intro P Q h
  have hlabels' : endpointLabelChoiceOfState P.val = endpointLabelChoiceOfState Q.val :=
    congrArg Sigma.fst h
  have hquotMinus : P.val.first / groupLabelProduct P.val - 1 =
      Q.val.first / groupLabelProduct Q.val - 1 :=
    by simpa [endpointSquarefreeCoordinates_first, endpointSquarefreeCoordinates] using
      congrArg endpointSquarefreeCoordinates_first h
  have hsecondMinus : P.val.second - 1 = Q.val.second - 1 :=
    by simpa [endpointSquarefreeCoordinates_second, endpointSquarefreeCoordinates] using
      congrArg endpointSquarefreeCoordinates_second h
  have hquot : P.val.first / groupLabelProduct P.val =
      Q.val.first / groupLabelProduct Q.val := by
    have hp : 0 < P.val.first / groupLabelProduct P.val := by
      by_contra hnot
      have hk0 := Nat.eq_zero_of_not_pos hnot
      have heq := Nat.mul_div_cancel' (groupLabelProduct_dvd_first P.val P.property)
      rw [hk0, mul_zero] at heq
      have hrange := P.val.completion_range
      have hfirst : 0 < P.val.first := by
        have h : (0 : ℤ) < (P.val.first : ℤ) := lt_of_le_of_lt hrange.1 hrange.2
        exact_mod_cast h
      omega
    have hq : 0 < Q.val.first / groupLabelProduct Q.val := by
      by_contra hnot
      have hk0 := Nat.eq_zero_of_not_pos hnot
      have heq := Nat.mul_div_cancel' (groupLabelProduct_dvd_first Q.val Q.property)
      rw [hk0, mul_zero] at heq
      have hrange := Q.val.completion_range
      have hfirst : 0 < Q.val.first := by
        have h : (0 : ℤ) < (Q.val.first : ℤ) := lt_of_le_of_lt hrange.1 hrange.2
        exact_mod_cast h
      omega
    omega
  have hsecond : P.val.second = Q.val.second := by
    have hp : 0 < P.val.second := by
      have h : (0 : ℝ) < (P.val.second : ℝ) :=
        lt_of_lt_of_le hHn P.val.second_lower
      exact_mod_cast h
    have hq : 0 < Q.val.second := by
      have h : (0 : ℝ) < (Q.val.second : ℝ) :=
        lt_of_lt_of_le hHn Q.val.second_lower
      exact_mod_cast h
    omega
  have hG : groupLabelProduct P.val = groupLabelProduct Q.val := by
    rw [← endpointLabelChoiceProduct_eq P.val, ← endpointLabelChoiceProduct_eq Q.val]
    exact congrArg endpointLabelChoiceProduct hlabels'
  have hdivP := groupLabelProduct_dvd_first P.val P.property
  have hdivQ := groupLabelProduct_dvd_first Q.val Q.property
  have hfirst : P.val.first = Q.val.first := by
    calc
      P.val.first = groupLabelProduct P.val * (P.val.first / groupLabelProduct P.val) :=
        (Nat.mul_div_cancel' hdivP).symm
      _ = groupLabelProduct Q.val * (Q.val.first / groupLabelProduct Q.val) := by rw [hquot, hG]
      _ = Q.val.first := Nat.mul_div_cancel' hdivQ
  have hlabels : P.val.labels = Q.val.labels := by
    funext i j
    exact congrArg Subtype.val (congrArg (fun p => p i j) hlabels')
  apply Subtype.ext
  exact physicalState_eq_of_positions_labels P.val Q.val hfirst hsecond hlabels

private lemma endpointLabelChoice_reciprocal_sum
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ) :
    (∑ l : EndpointLabelChoice x K a,
      ((endpointLabelChoiceProduct l : ℕ) : ℝ)⁻¹) =
      ∏ i : Fin K, (bandMass x (a i)) ^ slotCount x := by
  classical
  let Band (i : Fin K) := {p : ℕ // p ∈ primeBand x (a i)}
  let GroupChoice (i : Fin K) := Fin (slotCount x) → Band i
  let weight (i : Fin K) (g : GroupChoice i) :=
    ∏ j : Fin (slotCount x), ((g j).val : ℝ)⁻¹
  have hprod_inv (l : EndpointLabelChoice x K a) :
      ((endpointLabelChoiceProduct l : ℕ) : ℝ)⁻¹ = ∏ i : Fin K, weight i (l i) := by
    simp [weight, endpointLabelChoiceProduct, Band, Nat.cast_prod, Finset.prod_inv_distrib]
  have hinner (i : Fin K) :
      (∑ g : GroupChoice i, weight i g) = (bandMass x (a i)) ^ slotCount x := by
    calc
      (∑ g : GroupChoice i, weight i g) =
          ∏ j : Fin (slotCount x), ∑ p : Band i, ((p.val : ℝ)⁻¹) := by
        symm
        simpa only [Fintype.piFinset_univ] using
          (Finset.prod_univ_sum
            (t := fun _ : Fin (slotCount x) => (Finset.univ : Finset (Band i)))
            (f := fun _ p => (p.val : ℝ)⁻¹))
      _ = (bandMass x (a i)) ^ slotCount x := by
        have hsub : (∑ p : Band i, ((p.val : ℝ)⁻¹)) = bandMass x (a i) := by
          unfold bandMass
          simpa [Band] using
            (Finset.sum_attach (primeBand x (a i)) (fun p => ((p : ℝ)⁻¹)))
        rw [hsub]
        simp
  calc
    (∑ l : EndpointLabelChoice x K a,
        ((endpointLabelChoiceProduct l : ℕ) : ℝ)⁻¹) =
      ∑ l : EndpointLabelChoice x K a, ∏ i : Fin K, weight i (l i) := by
        apply Finset.sum_congr rfl
        intro l hl
        exact hprod_inv l
    _ = ∏ i : Fin K, ∑ g : GroupChoice i, weight i g := by
      symm
      simpa only [Fintype.piFinset_univ] using
        (Finset.prod_univ_sum
          (t := fun i : Fin K => (Finset.univ : Finset (GroupChoice i)))
          (f := fun i g => weight i g))
    _ = ∏ i : Fin K, (bandMass x (a i)) ^ slotCount x := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hinner i

private lemma endpointSquarefreeCoordinates_card
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (H' Hm Hn : ℝ) :
    Fintype.card (EndpointSquarefreeCoordinates x K a H' Hm Hn) =
      ∑ l : EndpointLabelChoice x K a,
        (⌊16 * H' * Hm / (endpointLabelChoiceProduct l : ℝ)⌋₊) * ⌊2 * Hn⌋₊ := by
  classical
  simp [EndpointSquarefreeCoordinates, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]

private lemma endpointSquarefreeSupport_card_le
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (hHn : 0 < Hn) (s : Finset (PhysicalState x K a H' Hm Hn))
    (hs : ∀ P ∈ s, Squarefree (groupLabelProduct P)) :
    s.card ≤ Fintype.card (EndpointSquarefreeCoordinates x K a H' Hm Hn) := by
  classical
  let embed (P : ↥s.attach) : EndpointSquarefreeCoordinates x K a H' Hm Hn :=
    endpointSquarefreeCoordinates hHn ⟨P.val.val, hs P.val.val P.val.property⟩
  have hinj : Function.Injective embed := by
    intro P Q h
    have hstate : P.val.val = Q.val.val := by
      exact congrArg
        (fun z : {R : PhysicalState x K a H' Hm Hn // Squarefree (groupLabelProduct R)} => z.val)
        (endpointSquarefreeCoordinates_injective hHn h)
    exact Subtype.ext (Subtype.ext hstate)
  have hcard := Fintype.card_le_of_injective embed hinj
  simpa [embed] using hcard

private lemma endpointLabelChoiceProduct_pos
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (l : EndpointLabelChoice x K a) : 0 < endpointLabelChoiceProduct l := by
  unfold endpointLabelChoiceProduct
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  have hp : (l i j).val.Prime := (Finset.mem_filter.mp (l i j).property).2.1
  exact hp.pos

private lemma endpointSquarefreeCoordinates_card_real_bound
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (H' Hm Hn : ℝ)
    (hU : 0 ≤ 16 * H' * Hm) (hV : 0 ≤ Hn) :
    (Fintype.card (EndpointSquarefreeCoordinates x K a H' Hm Hn) : ℝ) ≤
      32 * (H' * Hm) * Hn *
        ∏ i : Fin K, (bandMass x (a i)) ^ slotCount x := by
  classical
  rw [endpointSquarefreeCoordinates_card]
  push_cast
  calc
    (∑ l : EndpointLabelChoice x K a,
        (⌊16 * H' * Hm / (endpointLabelChoiceProduct l : ℝ)⌋₊ : ℝ) *
          (⌊2 * Hn⌋₊ : ℝ)) ≤
      ∑ l : EndpointLabelChoice x K a,
        32 * (H' * Hm) * Hn * ((endpointLabelChoiceProduct l : ℝ)⁻¹) := by
          apply Finset.sum_le_sum
          intro l hl
          have hG := endpointLabelChoiceProduct_pos x K a l
          have h1 := Nat.floor_le (div_nonneg hU (le_of_lt (Nat.cast_pos.mpr hG)))
          have h2 := Nat.floor_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hV)
          have hfloor1 :
              (⌊16 * H' * Hm / (endpointLabelChoiceProduct l : ℝ)⌋₊ : ℝ) ≤
                16 * H' * Hm / (endpointLabelChoiceProduct l : ℝ) := h1
          have hfloor2 : (⌊2 * Hn⌋₊ : ℝ) ≤ 2 * Hn := h2
          calc
            (⌊16 * H' * Hm / (endpointLabelChoiceProduct l : ℝ)⌋₊ : ℝ) *
                (⌊2 * Hn⌋₊ : ℝ) ≤
              (16 * H' * Hm / (endpointLabelChoiceProduct l : ℝ)) * (2 * Hn) :=
                mul_le_mul hfloor1 hfloor2 (by positivity)
                  (div_nonneg hU (le_of_lt (Nat.cast_pos.mpr hG)))
            _ = 32 * (H' * Hm) * Hn * ((endpointLabelChoiceProduct l : ℝ)⁻¹) := by
              field_simp
              ring
    _ = 32 * (H' * Hm) * Hn *
        (∑ l : EndpointLabelChoice x K a,
          ((endpointLabelChoiceProduct l : ℕ) : ℝ)⁻¹) := by
          symm
          rw [Finset.mul_sum]
    _ = 32 * (H' * Hm) * Hn *
        ∏ i : Fin K, (bandMass x (a i)) ^ slotCount x := by
          rw [endpointLabelChoice_reciprocal_sum]

private lemma endpointPhysicalMeasure_cancel
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hMass : ∀ i : Fin K, 0 < bandMass x (a i)) :
    physicalMeasure x K a *
      ∏ i : Fin K, (bandMass x (a i)) ^ slotCount x = 1 := by
  classical
  unfold physicalMeasure
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  calc
    Real.rpow (bandMass x (a i)) (-(slotCount x : ℝ)) *
        (bandMass x (a i)) ^ slotCount x =
      Real.rpow (bandMass x (a i)) (-(slotCount x : ℝ)) *
        Real.rpow (bandMass x (a i)) (slotCount x : ℝ) := by
          congr 1
          exact (Real.rpow_natCast (bandMass x (a i)) (slotCount x)).symm
    _ = Real.rpow (bandMass x (a i))
          (-(slotCount x : ℝ) + (slotCount x : ℝ)) :=
        (Real.rpow_add (hMass i) (-(slotCount x : ℝ)) (slotCount x : ℝ)).symm
    _ = 1 := by simp

private lemma endpoint_finite_tsum_norm_sq_le
    {α : Type*} [Fintype α] (f : α → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (support : Finset α) (hsupport : ∀ a, f a ≠ 0 ↔ a ∈ support)
    (hbound : ∀ a, ‖f a‖ ≤ B) :
    (∑' a, ‖f a‖ ^ 2) ≤ B ^ 2 * (support.card : ℝ) := by
  classical
  rw [tsum_fintype]
  calc
    (∑ a, ‖f a‖ ^ 2) = ∑ a, if a ∈ support then ‖f a‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hs : a ∈ support
      · simp [hs]
      · have hz : f a = 0 := by
          by_contra hne
          exact hs ((hsupport a).1 hne)
        simp [hs, hz]
    _ = ∑ a ∈ support, ‖f a‖ ^ 2 := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ a ∈ support, B ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      have hnorm := hbound a
      have hpos := norm_nonneg (f a)
      have hprod := mul_nonneg (sub_nonneg.mpr hnorm) (add_nonneg hB hpos)
      nlinarith [hprod]
    _ = B ^ 2 * (support.card : ℝ) := by simp [mul_comm]

/-- `t2:pd.endpoints` — PD `03-determinant.tex:295-341`. The endpoint vectors are supported on
lists with exactly `M_J` distinct marked primes in every group, have the indicated coordinates,
and satisfy the norm and pointwise bounds uniform in `K,J`.
The constant `B` was added on 2026-10-07: without it the bound fails at small `x` (lane `pd1`). -/
theorem endpoint_bounds
    (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ C_e B : ℝ, 0 < C_e ∧ 0 < B ∧
      ∀ K : ℕ, ∀ a : Fin K → ℝ, ValidBands K a →
      ∀ family : CoefficientFamily δ C c₁ c₂, ∀ x : ℝ, 2 ≤ x → family.xMin ≤ x →
        ∀ d₀ : ℕ, d₀ ∈ padScales x K →
          ∀ Y, Y ∈ dyadicScales x K →
          ∀ beta : ℕ → ℂ,
            (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
              roughAbove n (roughCutoff x)) →
            (∀ n ∈ dyadicIntegers (family.Hn x),
              ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
            Real.sqrt (physicalNormSq x K a
              (endpointFVector x K a ((d₀ : ℝ) * Y)
                (family.Hm x) (family.Hn x) family beta)) ≤
                Real.rpow ((d₀ : ℝ) * Y * family.Hm x * family.Hn x)
                  (1 / 2 : ℝ) * (B * Real.rpow (Real.log x) C_e) ∧
            Real.sqrt (physicalNormSq x K a
              (endpointGVector x K a ((d₀ : ℝ) * Y)
                (family.Hm x) (family.Hn x) family beta)) ≤
                Real.rpow ((d₀ : ℝ) * Y * family.Hm x * family.Hn x)
                  (1 / 2 : ℝ) * (B * Real.rpow (Real.log x) C_e) ∧
            physicalSupNorm x K a
                (endpointFVector x K a ((d₀ : ℝ) * Y)
                  (family.Hm x) (family.Hn x) family beta) +
              physicalSupNorm x K a
                (endpointGVector x K a ((d₀ : ℝ) * Y)
                  (family.Hm x) (family.Hn x) family beta) ≤
              (B * Real.rpow (Real.log x) C_e) := by
  classical
  refine ⟨2 * C, 6, by positivity, by norm_num, ?_⟩
  intro K a ha family x hx d₀ hd₀ Y hY beta hbetaSupport hbetaBound
  let H' : ℝ := (d₀ : ℝ) * Y
  let Hm : ℝ := family.Hm x
  let Hn : ℝ := family.Hn x
  let T : ℝ := Real.rpow (Real.log x) C
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  have hTpos : 0 < T := Real.rpow_pos_of_pos hlog C
  have hTnonneg : 0 ≤ T := le_of_lt hTpos
  have hT2 : T * T = Real.rpow (Real.log x) (2 * C) := by
    dsimp [T]
    rw [← Real.rpow_add hlog C C]
    congr 1
    ring
  have hd0pos : 0 < d₀ := by
    unfold padScales at hd₀
    rcases Finset.mem_image.mp hd₀ with ⟨k, hk, rfl⟩
    positivity
  have hYpos : 0 < Y := by
    unfold dyadicScales at hY
    rcases Finset.mem_filter.mp hY with ⟨hY, _⟩
    rcases Finset.mem_image.mp hY with ⟨k, hk, rfl⟩
    positivity
  have hH'pos : 0 < H' := by dsimp [H']; positivity
  have hscale := family.scales x hx
  have hxδ : 0 < Real.rpow x δ := Real.rpow_pos_of_pos hxpos δ
  have hHmpos : 0 < Hm := by
    dsimp [Hm]
    exact lt_of_lt_of_le hxδ hscale.1
  have hHnpos : 0 < Hn := by
    dsimp [Hn]
    exact lt_of_lt_of_le hxδ hscale.2.1
  have hbase : 0 < H' * Hm * Hn := by positivity
  letI : Fintype (PhysicalState x K a H' Hm Hn) :=
    Fintype.ofInjective
      (@endpointStateCoordinates x K a H' Hm Hn)
      (@endpointStateCoordinates_injective x K a H' Hm Hn)
  let Fvec : PhysicalState x K a H' Hm Hn → ℂ :=
    endpointFVector x K a H' Hm Hn family beta
  let Gvec : PhysicalState x K a H' Hm Hn → ℂ :=
    endpointGVector x K a H' Hm Hn family beta
  let SF : Finset (PhysicalState x K a H' Hm Hn) :=
    Finset.univ.filter fun P => endpointF x K a family beta P ≠ 0
  let SG : Finset (PhysicalState x K a H' Hm Hn) :=
    Finset.univ.filter fun P => endpointG x K a family beta P ≠ 0
  have hSupF := endpointF_sup_bound (K := K) (a := a) family hx beta hbetaBound H'
  have hSupG := endpointG_sup_bound (K := K) (a := a) family hx beta hbetaBound H'
  have hSupF' : physicalSupNorm x K a Fvec ≤ T * T := by
    simpa [Fvec, Hm, Hn, T] using hSupF
  have hSupG' : physicalSupNorm x K a Gvec ≤ T * T := by
    simpa [Gvec, Hm, Hn, T] using hSupG
  have hSup :
      physicalSupNorm x K a Fvec + physicalSupNorm x K a Gvec ≤
        6 * Real.rpow (Real.log x) (2 * C) := by
    calc
      physicalSupNorm x K a Fvec + physicalSupNorm x K a Gvec ≤ T * T + T * T :=
        add_le_add hSupF' hSupG'
      _ = 2 * (T * T) := by ring
      _ = 2 * Real.rpow (Real.log x) (2 * C) := by rw [hT2]
      _ ≤ 6 * Real.rpow (Real.log x) (2 * C) := by nlinarith
  have hMassNonneg : ∀ i : Fin K, 0 ≤ bandMass x (a i) := by
    intro i
    unfold bandMass
    apply Finset.sum_nonneg
    intro p hp
    positivity
  have hMeasureNonneg : 0 ≤ physicalMeasure x K a := by
    unfold physicalMeasure
    apply Finset.prod_nonneg
    intro i hi
    exact Real.rpow_nonneg (hMassNonneg i) _
  have hNumNonneg : 0 ≤ 16 * H' * Hm := by positivity
  have hCoordBound := endpointSquarefreeCoordinates_card_real_bound
    x K a H' Hm Hn hNumNonneg (le_of_lt hHnpos)
  have hSquareF : ∀ P ∈ SF, Squarefree (groupLabelProduct P) := by
    intro P hP
    by_contra hSq
    have hzero : endpointF x K a family beta P = 0 := by simp [endpointF, hSq]
    exact (Finset.mem_filter.mp hP).2 hzero
  have hSquareG : ∀ P ∈ SG, Squarefree (groupLabelProduct P) := by
    intro P hP
    by_contra hSq
    have hzero : endpointG x K a family beta P = 0 := by simp [endpointG, hSq]
    exact (Finset.mem_filter.mp hP).2 hzero
  have hCardFNat := endpointSquarefreeSupport_card_le hHnpos SF hSquareF
  have hCardGNat := endpointSquarefreeSupport_card_le hHnpos SG hSquareG
  have hCardF : (SF.card : ℝ) ≤
      32 * (H' * Hm) * Hn * ∏ i : Fin K, (bandMass x (a i)) ^ slotCount x := by
    calc
      (SF.card : ℝ) ≤ Fintype.card (EndpointSquarefreeCoordinates x K a H' Hm Hn) := by
        exact_mod_cast hCardFNat
      _ ≤ 32 * (H' * Hm) * Hn * ∏ i : Fin K, (bandMass x (a i)) ^ slotCount x := hCoordBound
  have hCardG : (SG.card : ℝ) ≤
      32 * (H' * Hm) * Hn * ∏ i : Fin K, (bandMass x (a i)) ^ slotCount x := by
    calc
      (SG.card : ℝ) ≤ Fintype.card (EndpointSquarefreeCoordinates x K a H' Hm Hn) := by
        exact_mod_cast hCardGNat
      _ ≤ 32 * (H' * Hm) * Hn * ∏ i : Fin K, (bandMass x (a i)) ^ slotCount x := hCoordBound
  have hSupportF : ∀ P, Fvec P ≠ 0 ↔ P ∈ SF := by
    intro P
    simp [Fvec, SF, endpointFVector]
  have hSupportG : ∀ P, Gvec P ≠ 0 ↔ P ∈ SG := by
    intro P
    simp [Gvec, SG, endpointGVector]
  have hPointF : ∀ P, ‖Fvec P‖ ≤ T * T := by
    intro P
    exact endpointF_pointwise_bound family hx beta hbetaBound P
  have hPointG : ∀ P, ‖Gvec P‖ ≤ T * T := by
    intro P
    exact endpointG_pointwise_bound family hx beta hbetaBound P
  have hSqSumF := endpoint_finite_tsum_norm_sq_le Fvec (T * T)
    (mul_nonneg hTnonneg hTnonneg) SF hSupportF hPointF
  have hSqSumG := endpoint_finite_tsum_norm_sq_le Gvec (T * T)
    (mul_nonneg hTnonneg hTnonneg) SG hSupportG hPointG
  let RHS : ℝ := Real.rpow (H' * Hm * Hn) (1 / 2 : ℝ) *
    (6 * Real.rpow (Real.log x) (2 * C))
  have hRHSnonneg : 0 ≤ RHS := by
    change 0 ≤ Real.rpow (H' * Hm * Hn) (1 / 2 : ℝ) *
      (6 * Real.rpow (Real.log x) (2 * C))
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hbase) _)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hlog) _))
  have hRHSfactor :
      Real.rpow (H' * Hm * Hn) (1 / 2 : ℝ) *
          (6 * Real.rpow (Real.log x) (2 * C)) =
        Real.sqrt (H' * Hm * Hn) * (6 * (T * T)) := by
    calc
      Real.rpow (H' * Hm * Hn) (1 / 2 : ℝ) *
          (6 * Real.rpow (Real.log x) (2 * C)) =
        Real.rpow (H' * Hm * Hn) (1 / 2 : ℝ) * (6 * (T * T)) :=
          congrArg (fun z : ℝ => Real.rpow (H' * Hm * Hn) (1 / 2 : ℝ) * (6 * z)) hT2.symm
      _ = Real.sqrt (H' * Hm * Hn) * (6 * (T * T)) :=
        congrArg (fun z : ℝ => z * (6 * (T * T))) (Real.sqrt_eq_rpow (H' * Hm * Hn)).symm
  have hRHSsq : RHS ^ 2 = 36 * (H' * Hm * Hn) * T ^ 4 := by
    dsimp [RHS]
    calc
      (Real.rpow (H' * Hm * Hn) (1 / 2 : ℝ) *
          (6 * Real.rpow (Real.log x) (2 * C))) ^ 2 =
        (Real.sqrt (H' * Hm * Hn) * (6 * (T * T))) ^ 2 :=
          congrArg (fun z : ℝ => z ^ 2) hRHSfactor
      _ = 36 * (H' * Hm * Hn) * T ^ 4 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hbase)]
        ring
  have hT4nonneg : 0 ≤ T ^ 4 := by positivity
  have hprodNonneg : 0 ≤ (H' * Hm * Hn) * T ^ 4 :=
    mul_nonneg (le_of_lt hbase) hT4nonneg
  by_cases hMass : ∀ i : Fin K, 0 < bandMass x (a i)
  · have hcancel := endpointPhysicalMeasure_cancel x K a hMass
    have normSqBound (f : PhysicalState x K a H' Hm Hn → ℂ)
        (s : Finset (PhysicalState x K a H' Hm Hn))
        (hsum : (∑' P, ‖f P‖ ^ 2) ≤ (T * T) ^ 2 * (s.card : ℝ))
        (hcard : (s.card : ℝ) ≤
          32 * (H' * Hm) * Hn * ∏ i : Fin K, (bandMass x (a i)) ^ slotCount x) :
        physicalNormSq x K a f ≤ 32 * (H' * Hm) * Hn * T ^ 4 := by
      unfold physicalNormSq
      calc
        physicalMeasure x K a * (∑' P, ‖f P‖ ^ 2) ≤
            physicalMeasure x K a * ((T * T) ^ 2 * (s.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum hMeasureNonneg
        _ ≤ physicalMeasure x K a * ((T * T) ^ 2 *
            (32 * (H' * Hm) * Hn * ∏ i : Fin K,
              (bandMass x (a i)) ^ slotCount x)) := by
          have hh := mul_le_mul_of_nonneg_left hcard (sq_nonneg (T * T))
          exact mul_le_mul_of_nonneg_left (by nlinarith [hh]) hMeasureNonneg
        _ = 32 * (H' * Hm) * Hn * T ^ 4 := by
          calc
            physicalMeasure x K a * ((T * T) ^ 2 *
                (32 * (H' * Hm) * Hn * ∏ i : Fin K,
                  (bandMass x (a i)) ^ slotCount x)) =
              32 * (H' * Hm) * Hn * (T * T) ^ 2 *
                (physicalMeasure x K a *
                  ∏ i : Fin K, (bandMass x (a i)) ^ slotCount x) := by ring
            _ = 32 * (H' * Hm) * Hn * (T * T) ^ 2 := by rw [hcancel]; ring
            _ = 32 * (H' * Hm) * Hn * T ^ 4 := by ring
    have hNormSqF := normSqBound Fvec SF hSqSumF hCardF
    have hNormSqG := normSqBound Gvec SG hSqSumG hCardG
    refine ⟨?_, ?_, ?_⟩
    · apply Real.sqrt_le_iff.mpr
      exact ⟨hRHSnonneg, by rw [hRHSsq]; nlinarith [hNormSqF, hprodNonneg]⟩
    · apply Real.sqrt_le_iff.mpr
      exact ⟨hRHSnonneg, by rw [hRHSsq]; nlinarith [hNormSqG, hprodNonneg]⟩
    · simpa [Fvec, Gvec, RHS, H', Hm, Hn] using hSup
  · push_neg at hMass
    rcases hMass with ⟨i, hi⟩
    have hzero : bandMass x (a i) = 0 := le_antisymm hi (hMassNonneg i)
    have hslot : 0 < slotCount x := by simp [slotCount]
    have hexp : -(slotCount x : ℝ) ≠ 0 := by
      have hM : 0 < (slotCount x : ℝ) := Nat.cast_pos.mpr hslot
      linarith
    have hmeasure : physicalMeasure x K a = 0 := by
      unfold physicalMeasure
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hzero]
      exact Real.zero_rpow hexp
    have hNormSqF : physicalNormSq x K a Fvec = 0 := by
      unfold physicalNormSq
      rw [hmeasure]
      simp only [zero_mul]
    have hNormSqG : physicalNormSq x K a Gvec = 0 := by
      unfold physicalNormSq
      rw [hmeasure]
      simp only [zero_mul]
    have hNormSqFraw : physicalNormSq x K a
        (endpointFVector x K a ((d₀ : ℝ) * Y)
          (family.Hm x) (family.Hn x) family beta) = 0 := by
      simpa [Fvec, H', Hm, Hn] using hNormSqF
    have hNormSqGraw : physicalNormSq x K a
        (endpointGVector x K a ((d₀ : ℝ) * Y)
          (family.Hm x) (family.Hn x) family beta) = 0 := by
      simpa [Gvec, H', Hm, Hn] using hNormSqG
    refine ⟨?_, ?_, ?_⟩
    · rw [hNormSqFraw, Real.sqrt_zero]
      simpa [RHS, H', Hm, Hn] using hRHSnonneg
    · rw [hNormSqGraw, Real.sqrt_zero]
      simpa [RHS, H', Hm, Hn] using hRHSnonneg
    · simpa [Fvec, Gvec, H', Hm, Hn] using hSup

/-! The reduced residue classes modulo `m` reindex as the units of `ZMod m`. -/
private abbrev ReducedResidues (m : ℕ) :=
  {y : ℕ // y ∈ (Finset.range m).filter (fun y => Nat.Coprime y m)}

private noncomputable def reducedResiduesEquivUnits (m : ℕ) (hm : 0 < m) :
    ReducedResidues m ≃ (ZMod m)ˣ := by
  letI : NeZero m := ⟨by omega⟩
  refine
    { toFun := fun y => ZMod.unitOfCoprime y.val (Finset.mem_filter.mp y.property).2
      invFun := fun u => ⟨(u.val).val,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt u.val),
          ZMod.val_coe_unit_coprime u⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    apply Subtype.ext
    have hylt : y.val < m := Finset.mem_range.mp (Finset.mem_filter.mp y.property).1
    simp [ZMod.unitOfCoprime, ZMod.val_natCast_of_lt hylt]
  · intro u
    apply Units.ext
    simp [ZMod.unitOfCoprime, ZMod.natCast_zmod_val]

private lemma additiveCharacter_nat_div_eq_stdAddChar
    {m t : ℕ} [NeZero m] :
    ArtinPrimitiveRoots.TypeII.additiveCharacter ((t : ℝ) / (m : ℝ)) =
      ZMod.stdAddChar (t : ZMod m) := by
  have hcast : (t : ZMod m) = ((t : ℤ) : ZMod m) := by norm_cast
  rw [hcast, ZMod.stdAddChar_coe]
  unfold ArtinPrimitiveRoots.TypeII.additiveCharacter
  congr 1
  push_cast
  ring

private lemma kloostermanSum_eq_unit_sum
    (m h k : ℕ) [NeZero m] [Fintype (ZMod m)ˣ] :
    kloostermanSum m h k =
      ∑ u : (ZMod m)ˣ,
        ZMod.stdAddChar ((h : ZMod m) * (u : ZMod m) +
          (k : ZMod m) * (u⁻¹ : ZMod m)) := by
  classical
  have hm : 0 < m := NeZero.pos m
  let S : Finset ℕ := (Finset.range m).filter (fun y => Nat.Coprime y m)
  let e := reducedResiduesEquivUnits m hm
  let f (y : ReducedResidues m) :=
    ArtinPrimitiveRoots.TypeII.additiveCharacter
      (((h * y.val + k * ((y.val : ZMod m)⁻¹).val : ℕ) : ℝ) / (m : ℝ))
  let g (u : (ZMod m)ˣ) :=
    ZMod.stdAddChar ((h : ZMod m) * (u : ZMod m) + (k : ZMod m) * (u⁻¹ : ZMod m))
  have hsum : (∑ y ∈ S,
      ArtinPrimitiveRoots.TypeII.additiveCharacter
        (((h * y + k * ((y : ZMod m)⁻¹).val : ℕ) : ℝ) / (m : ℝ))) =
      ∑ y : ReducedResidues m, f y := by
    simpa [ReducedResidues, S, f] using
      (Finset.sum_attach S (fun y =>
        ArtinPrimitiveRoots.TypeII.additiveCharacter
          (((h * y + k * ((y : ZMod m)⁻¹).val : ℕ) : ℝ) / (m : ℝ)))).symm
  calc
    kloostermanSum m h k = ∑ y ∈ S,
        ArtinPrimitiveRoots.TypeII.additiveCharacter
          (((h * y + k * ((y : ZMod m)⁻¹).val : ℕ) : ℝ) / (m : ℝ)) := by
      simp [kloostermanSum, S]
    _ = ∑ y : ReducedResidues m, f y := hsum
    _ = ∑ u : (ZMod m)ˣ, g u := by
      apply Fintype.sum_equiv e f g
      intro y
      dsimp [f, g]
      rw [additiveCharacter_nat_div_eq_stdAddChar (m := m)
        (t := h * y.val + k * ((y.val : ZMod m)⁻¹).val)]
      congr 1
      simp [e, reducedResiduesEquivUnits, ZMod.unitOfCoprime,
        ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]

private noncomputable def unitKloosterman
    (m : ℕ) [NeZero m] [Fintype (ZMod m)ˣ]
    (h k : ZMod m) : ℂ :=
  ∑ u : (ZMod m)ˣ, ZMod.stdAddChar (h * (u : ZMod m) + k * (u⁻¹ : ZMod m))

private lemma stdAddChar_orthogonality
    (m : ℕ) [NeZero m] (t : ZMod m) :
    (∑ x : ZMod m, ZMod.stdAddChar (t * x)) =
      if t = 0 then (m : ℂ) else 0 := by
  classical
  split_ifs with ht
  · simp [ht]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar m ht)

private lemma stdAddChar_star
    (m : ℕ) [NeZero m] (z : ZMod m) :
    star (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  simp only [ZMod.stdAddChar_apply, Complex.star_def, ← Circle.coe_inv_eq_conj,
    Circle.coe_inv, AddChar.map_neg_eq_inv]

private lemma zmod_scaled_inverse
    (m : ℕ) [NeZero m] (s u : (ZMod m)ˣ) :
    ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * ((s⁻¹ : (ZMod m)ˣ) : ZMod m) =
      ((s : ZMod m) * (u : ZMod m))⁻¹ := by
  calc
    ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * ((s⁻¹ : (ZMod m)ˣ) : ZMod m) =
        (((u⁻¹ * s⁻¹ : (ZMod m)ˣ) : ZMod m)) := by simp [Units.val_mul]
    _ = (((s * u)⁻¹ : (ZMod m)ˣ) : ZMod m) := by
      congr 1
    _ = ((s : ZMod m) * (u : ZMod m))⁻¹ := by
      simpa only [Units.val_mul] using (ZMod.inv_coe_unit (s * u)).symm

private lemma unitKloosterman_scale
    (m : ℕ) [NeZero m] [Fintype (ZMod m)ˣ]
    (h k : ZMod m) (s : (ZMod m)ˣ) :
    unitKloosterman m (h * (s : ZMod m)) (k * (s⁻¹ : ZMod m)) =
      unitKloosterman m h k := by
  classical
  unfold unitKloosterman
  let e : (ZMod m)ˣ ≃ (ZMod m)ˣ :=
    { toFun := fun u => s * u
      invFun := fun u => s⁻¹ * u
      left_inv := by intro u; group
      right_inv := by intro u; group }
  calc
    (∑ u : (ZMod m)ˣ,
        ZMod.stdAddChar
          ((h * (s : ZMod m)) * (u : ZMod m) +
            (k * (s⁻¹ : ZMod m)) * (u⁻¹ : ZMod m))) =
      ∑ u : (ZMod m)ˣ,
        ZMod.stdAddChar
          (h * ((s * u : (ZMod m)ˣ) : ZMod m) +
            k * (((s * u : (ZMod m)ˣ)⁻¹ : (ZMod m)ˣ) : ZMod m)) := by
          apply Finset.sum_congr rfl
          intro u hu
          congr 1
          have hInv : (s⁻¹ : ZMod m) * (u⁻¹ : ZMod m) =
              ((s : ZMod m) * (u : ZMod m))⁻¹ := by
            rw [mul_comm, ZMod.inv_coe_unit u, ZMod.inv_coe_unit s]
            exact zmod_scaled_inverse m s u
          simp only [mul_assoc]
          rw [hInv]
          rw [← ZMod.inv_coe_unit (s * u)]
          simp only [Units.val_mul]
    _ = ∑ u : (ZMod m)ˣ, ZMod.stdAddChar
        (h * (u : ZMod m) + k * (u⁻¹ : ZMod m)) := by
          apply Fintype.sum_equiv e
          intro u
          dsimp [e]
          rw [(ZMod.inv_coe_unit (s * u)).symm]
          simp only [Units.val_mul]

private lemma stdAddChar_norm_eq_one
    (m : ℕ) [NeZero m] (x : ZMod m) : ‖ZMod.stdAddChar x‖ = 1 := by
  simp [ZMod.stdAddChar_apply]

private lemma unitKloosterman_norm_le_modulus
    (m : ℕ) [NeZero m] [Fintype (ZMod m)ˣ] (h k : ZMod m) :
    ‖unitKloosterman m h k‖ ≤ (m : ℝ) := by
  unfold unitKloosterman
  calc
    ‖∑ u : (ZMod m)ˣ, ZMod.stdAddChar (h * (u : ZMod m) + k * (u⁻¹ : ZMod m))‖ ≤
        ∑ u : (ZMod m)ˣ,
          ‖ZMod.stdAddChar (h * (u : ZMod m) + k * (u⁻¹ : ZMod m))‖ := norm_sum_le _ _
    _ = (Fintype.card (ZMod m)ˣ : ℝ) := by simp [stdAddChar_norm_eq_one]
    _ ≤ (m : ℝ) := by
      have hcard : Fintype.card (ZMod m)ˣ ≤ Fintype.card (ZMod m) :=
        Fintype.card_le_of_injective (fun u : (ZMod m)ˣ => (u : ZMod m))
          (fun u v h => Units.ext h)
      exact_mod_cast (by simpa using hcard)

private lemma unitKloosterman_normSq_pairSum
    (m : ℕ) [NeZero m] [Fintype (ZMod m)ˣ] (h k : ZMod m) :
    (Complex.normSq (unitKloosterman m h k) : ℂ) =
      ∑ u : (ZMod m)ˣ, ∑ v : (ZMod m)ˣ,
        ZMod.stdAddChar
          (h * ((v : ZMod m) - (u : ZMod m)) +
            k * ((v⁻¹ : ZMod m) - (u⁻¹ : ZMod m))) := by
  classical
  let arg (u : (ZMod m)ˣ) := h * (u : ZMod m) + k * (u⁻¹ : ZMod m)
  have hstar : star (unitKloosterman m h k) =
      ∑ u : (ZMod m)ˣ, ZMod.stdAddChar (-arg u) := by
    simp [unitKloosterman, arg, stdAddChar_star]
  calc
    (Complex.normSq (unitKloosterman m h k) : ℂ) =
        star (unitKloosterman m h k) * unitKloosterman m h k := by
      exact Complex.normSq_eq_conj_mul_self
    _ = (∑ u : (ZMod m)ˣ, ZMod.stdAddChar (-arg u)) *
          (∑ v : (ZMod m)ˣ, ZMod.stdAddChar (arg v)) := by
      rw [hstar]
      rfl
    _ = ∑ u : (ZMod m)ˣ, ∑ v : (ZMod m)ˣ,
        ZMod.stdAddChar (h * ((v : ZMod m) - (u : ZMod m)) +
          k * ((v⁻¹ : ZMod m) - (u⁻¹ : ZMod m))) := by
      rw [Fintype.sum_mul_sum]
      apply Fintype.sum_congr
      intro u
      apply Fintype.sum_congr
      intro v
      have harg :
          h * ((v : ZMod m) - (u : ZMod m)) + k * ((v⁻¹ : ZMod m) - (u⁻¹ : ZMod m)) =
            -arg u + arg v := by
        dsimp [arg]
        ring
      rw [harg]
      exact (AddChar.map_add_eq_mul ZMod.stdAddChar (-arg u) (arg v)).symm

private abbrev UnitPair (m : ℕ) := (ZMod m)ˣ × (ZMod m)ˣ

private abbrev UnitQuad (m : ℕ) := UnitPair m × UnitPair m

private def unitPairAddDelta {m : ℕ} (p : UnitPair m) : ZMod m :=
  (p.2 : ZMod m) - (p.1 : ZMod m)

private def unitPairInvDelta {m : ℕ} (p : UnitPair m) : ZMod m :=
  (p.2⁻¹ : ZMod m) - (p.1⁻¹ : ZMod m)

private def unitQuadAddDelta {m : ℕ} (q : UnitQuad m) : ZMod m :=
  unitPairAddDelta q.1 + unitPairAddDelta q.2

private def unitQuadInvDelta {m : ℕ} (q : UnitQuad m) : ZMod m :=
  unitPairInvDelta q.1 + unitPairInvDelta q.2

private def unitQuadPhase {m : ℕ} (h k : ZMod m) (q : UnitQuad m) : ZMod m :=
  h * unitQuadAddDelta q + k * unitQuadInvDelta q

private def unitQuadSolution {m : ℕ} (q : UnitQuad m) : Prop :=
  unitQuadAddDelta q = 0 ∧ unitQuadInvDelta q = 0

private noncomputable def unitQuadSolutions
    (m : ℕ) [Fintype (ZMod m)ˣ] : Finset (UnitQuad m) :=
  Finset.univ.filter unitQuadSolution

private lemma unitKloosterman_norm_fourth_cast
    (m : ℕ) [NeZero m] [Fintype (ZMod m)ˣ] (h k : ZMod m) :
    ((‖unitKloosterman m h k‖ ^ 4 : ℝ) : ℂ) =
      ∑ q : UnitQuad m, ZMod.stdAddChar (unitQuadPhase h k q) := by
  classical
  have hnorm : ‖unitKloosterman m h k‖ ^ 4 =
      (Complex.normSq (unitKloosterman m h k)) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    ring
  have hpair : (Complex.normSq (unitKloosterman m h k) : ℂ) =
      ∑ p : UnitPair m,
        ZMod.stdAddChar (h * unitPairAddDelta p + k * unitPairInvDelta p) := by
    calc
      (Complex.normSq (unitKloosterman m h k) : ℂ) =
          ∑ u : (ZMod m)ˣ, ∑ v : (ZMod m)ˣ,
            ZMod.stdAddChar
              (h * ((v : ZMod m) - (u : ZMod m)) +
                k * ((v⁻¹ : ZMod m) - (u⁻¹ : ZMod m))) :=
        unitKloosterman_normSq_pairSum m h k
      _ = ∑ p : UnitPair m,
          ZMod.stdAddChar (h * unitPairAddDelta p + k * unitPairInvDelta p) := by
        symm
        exact Fintype.sum_prod_type (fun p : UnitPair m =>
          ZMod.stdAddChar (h * unitPairAddDelta p + k * unitPairInvDelta p))
  have hquad :
      (∑ p : UnitPair m,
        ZMod.stdAddChar (h * unitPairAddDelta p + k * unitPairInvDelta p)) ^ 2 =
        ∑ q : UnitQuad m, ZMod.stdAddChar (unitQuadPhase h k q) := by
    rw [pow_two, Fintype.sum_mul_sum]
    calc
      (∑ p : UnitPair m, ∑ q : UnitPair m,
          ZMod.stdAddChar (h * unitPairAddDelta p + k * unitPairInvDelta p) *
            ZMod.stdAddChar (h * unitPairAddDelta q + k * unitPairInvDelta q)) =
        ∑ p : UnitPair m, ∑ q : UnitPair m,
          ZMod.stdAddChar (unitQuadPhase h k (p, q)) := by
            apply Fintype.sum_congr
            intro p
            apply Fintype.sum_congr
            intro q
            have harg : unitQuadPhase h k (p, q) =
                (h * unitPairAddDelta p + k * unitPairInvDelta p) +
                  (h * unitPairAddDelta q + k * unitPairInvDelta q) := by
              dsimp [unitQuadPhase, unitQuadAddDelta, unitQuadInvDelta,
                unitPairAddDelta, unitPairInvDelta]
              ring_nf
            rw [harg]
            exact (AddChar.map_add_eq_mul ZMod.stdAddChar
              (h * unitPairAddDelta p + k * unitPairInvDelta p)
              (h * unitPairAddDelta q + k * unitPairInvDelta q)).symm
      _ = ∑ q : UnitQuad m, ZMod.stdAddChar (unitQuadPhase h k q) := by
            symm
            exact Fintype.sum_prod_type (fun q : UnitQuad m =>
              ZMod.stdAddChar (unitQuadPhase h k q))
  have hnormCast :
      ((‖unitKloosterman m h k‖ ^ 4 : ℝ) : ℂ) =
        (Complex.normSq (unitKloosterman m h k) : ℂ) ^ 2 := by
    exact_mod_cast hnorm
  calc
    ((‖unitKloosterman m h k‖ ^ 4 : ℝ) : ℂ) =
        (Complex.normSq (unitKloosterman m h k) : ℂ) ^ 2 := hnormCast
    _ = _ := by rw [hpair, hquad]

private lemma unitKloosterman_global_fourthMoment
    (m : ℕ) [NeZero m] [Fintype (ZMod m)ˣ] :
    (∑ h : ZMod m, ∑ k : ZMod m, ‖unitKloosterman m h k‖ ^ 4) =
      (m : ℝ) ^ 2 * (unitQuadSolutions m).card := by
  classical
  have hcollapse (q : UnitQuad m) :
      (∑ h : ZMod m, ZMod.stdAddChar (h * unitQuadAddDelta q)) *
        (∑ k : ZMod m, ZMod.stdAddChar (k * unitQuadInvDelta q)) =
          if unitQuadSolution q then (m : ℂ) ^ 2 else 0 := by
    have h1 : (∑ h : ZMod m, ZMod.stdAddChar (h * unitQuadAddDelta q)) =
        if unitQuadAddDelta q = 0 then (m : ℂ) else 0 := by
      simpa [mul_comm] using stdAddChar_orthogonality m (unitQuadAddDelta q)
    have h2 : (∑ k : ZMod m, ZMod.stdAddChar (k * unitQuadInvDelta q)) =
        if unitQuadInvDelta q = 0 then (m : ℂ) else 0 := by
      simpa [mul_comm] using stdAddChar_orthogonality m (unitQuadInvDelta q)
    rw [h1, h2]
    by_cases ha : unitQuadAddDelta q = 0 <;>
      by_cases hb : unitQuadInvDelta q = 0 <;>
      simp [unitQuadSolution, ha, hb] <;> ring
  have hsumComplex :
      (∑ h : ZMod m, ∑ k : ZMod m,
        ((‖unitKloosterman m h k‖ ^ 4 : ℝ) : ℂ)) =
        (m : ℂ) ^ 2 * (unitQuadSolutions m).card := by
    simp_rw [unitKloosterman_norm_fourth_cast]
    calc
      (∑ h : ZMod m, ∑ k : ZMod m,
          ∑ q : UnitQuad m, ZMod.stdAddChar (unitQuadPhase h k q)) =
        ∑ q : UnitQuad m, ∑ h : ZMod m, ∑ k : ZMod m,
          ZMod.stdAddChar (unitQuadPhase h k q) := by
            calc
              (∑ h : ZMod m, ∑ k : ZMod m, ∑ q : UnitQuad m,
                  ZMod.stdAddChar (unitQuadPhase h k q)) =
                ∑ h : ZMod m, ∑ q : UnitQuad m, ∑ k : ZMod m,
                  ZMod.stdAddChar (unitQuadPhase h k q) := by
                    apply Finset.sum_congr rfl
                    intro h hh
                    exact Finset.sum_comm
              _ = ∑ q : UnitQuad m, ∑ h : ZMod m, ∑ k : ZMod m,
                  ZMod.stdAddChar (unitQuadPhase h k q) := Finset.sum_comm
      _ = ∑ q : UnitQuad m,
          (∑ h : ZMod m, ZMod.stdAddChar (h * unitQuadAddDelta q)) *
            (∑ k : ZMod m, ZMod.stdAddChar (k * unitQuadInvDelta q)) := by
            apply Finset.sum_congr rfl
            intro q hq
            have hfactor : ∀ h k : ZMod m,
                ZMod.stdAddChar (unitQuadPhase h k q) =
                  ZMod.stdAddChar (h * unitQuadAddDelta q) *
                    ZMod.stdAddChar (k * unitQuadInvDelta q) := by
              intro h k
              simp [unitQuadPhase, AddChar.map_add_eq_mul]
            simp_rw [hfactor]
            rw [Fintype.sum_mul_sum]
      _ = ∑ q : UnitQuad m, if unitQuadSolution q then (m : ℂ) ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            exact hcollapse q
      _ = (m : ℂ) ^ 2 * (unitQuadSolutions m).card := by
            rw [← Finset.sum_filter]
            simp [unitQuadSolutions, mul_comm]
  have hreal :
      (∑ h : ZMod m, ∑ k : ZMod m, ‖unitKloosterman m h k‖ ^ 4) =
        (m : ℝ) ^ 2 * (unitQuadSolutions m).card := by
    exact_mod_cast hsumComplex
  exact hreal

/-- `t2:pd.weak-kloosterman` — PD `03-determinant.tex:445-480`. -/

theorem weak_kloosterman (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧
      ∀ m h k : ℕ, 1 ≤ m →
        ‖kloostermanSum m h k‖ ≤
          Cε * Real.rpow m (3 / 4 + ε) * Real.rpow (Nat.gcd (Nat.gcd h k) m) (1 / 4 : ℝ) := by
  sorry

/-- `lem:root-residue` — PD `03-determinant.tex:413-591`. Primitive roots of determinant-one
matrices are equidistributed in boxes and residue classes modulo squarefree `S`, with the stated
uniform power-saving error. -/
theorem root_residue
    (δ C_K : ℝ) (hδ : 0 < δ) (hCK : 0 < C_K) :
    ∃ cδ C₀ x₀ : ℝ, cδ = δ / 1000 ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ U V : ℝ, Real.rpow x δ ≤ U → Real.rpow x δ ≤ V →
        ∀ S : ℕ, Squarefree S → ∀ hS : 0 < S, (S : ℝ) ≤
          Real.exp (C_K * Real.rpow (Real.log x) (98 / 100 : ℝ)) →
          ∀ g₀ : Matrix (Fin 2) (Fin 2) (ZMod S),
            Matrix.det g₀ = 1 →
            ∀ l₁ r₁ l₂ r₂ l₃ r₃ : ℝ,
              1 ≤ l₁ → l₁ ≤ r₁ → r₁ ≤ 16 →
              1 ≤ l₂ → l₂ ≤ r₂ → r₂ ≤ 2 →
              0 ≤ l₃ → l₃ ≤ r₃ → r₃ ≤ 1 →
              |rootResidueCount U V S g₀
                  l₁ r₁ l₂ r₂ l₃ r₃ -
                U * V * (r₁ - l₁) * (r₂ - l₂) * (r₃ - l₃) /
                    ((Real.pi ^ 2 / 6) * sl2Card S hS)| ≤
                C₀ * U * V * Real.rpow x (-cδ) := by
  sorry

end ArtinPrimitiveRoots.TypeII.PD
