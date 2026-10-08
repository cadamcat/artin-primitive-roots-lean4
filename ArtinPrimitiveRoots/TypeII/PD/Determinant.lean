import ArtinPrimitiveRoots.TypeII.PD.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.Circle
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyArithmetic
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchySquare
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyFinite
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyPrimes
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyMain
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyDivisor
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootArithmetic
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootCRTModel
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootAsymptotic
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootReversal
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootRestrictedFourier
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootMainTerm
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootFinish
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.Goodness
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.BandGeometry

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
  exact pd1c_cauchy_decomposition δ C Dstar q_d c₁ c₂ K a hδ hC hD hqd₀ hqd₁ hc₁ hc₂ ha

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
  obtain ⟨c, x₀, hc, hx₀, hbound⟩ := pd1c_good_state_bound K a ha
  refine ⟨c, x₀, hc, hx₀, ?_⟩
  intro x hx d₀ hd₀ Y hY p hp
  exact hbound x hx Y hY (d₀ : ℝ) p hp

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
    (family : CoefficientFamily δ C c₁ c₂) (hx : 2 ≤ x) (hMin : family.xMin ≤ x)
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
    · exact family.coefficient_bound x hMin _
        (family.rough_support x hMin _ hzero).1
  have hβ : ‖beta P.second‖ ≤ Real.rpow (Real.log x) C :=
    hbeta P.second (endpoint_second_mem_dyadic P)
  by_cases hG : Squarefree (groupLabelProduct P)
  · simp only [endpointF, hG, ↓reduceIte, norm_mul, norm_star]
    exact mul_le_mul hα hβ (norm_nonneg _) (Real.rpow_nonneg (le_of_lt hlog) C)
  · simpa [endpointF, hG] using
      mul_nonneg (Real.rpow_nonneg (le_of_lt hlog) C) (Real.rpow_nonneg (le_of_lt hlog) C)

private lemma endpointG_pointwise_bound
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (hx : 2 ≤ x) (hMin : family.xMin ≤ x)
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
    · exact family.coefficient_bound x hMin _
        (family.rough_support x hMin _ hzero).1
  have hβ : ‖beta P.second‖ ≤ Real.rpow (Real.log x) C :=
    hbeta P.second (endpoint_second_mem_dyadic P)
  by_cases hG : Squarefree (groupLabelProduct P)
  · simp only [endpointG, hG, ↓reduceIte, norm_mul, norm_star]
    exact mul_le_mul hα hβ (norm_nonneg _) (Real.rpow_nonneg (le_of_lt hlog) C)
  · simpa [endpointG, hG] using
      mul_nonneg (Real.rpow_nonneg (le_of_lt hlog) C) (Real.rpow_nonneg (le_of_lt hlog) C)

private lemma endpointF_sup_bound
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (hx : 2 ≤ x) (hMin : family.xMin ≤ x)
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
    exact endpointF_pointwise_bound family hx hMin beta hbeta P
  · exact mul_nonneg (Real.rpow_nonneg (le_of_lt hlog) C)
      (Real.rpow_nonneg (le_of_lt hlog) C)

private lemma endpointG_sup_bound
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (hx : 2 ≤ x) (hMin : family.xMin ≤ x)
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
    exact endpointG_pointwise_bound family hx hMin beta hbeta P
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
  intro K a ha family x hx hMin d₀ hd₀ Y hY beta hbetaSupport hbetaBound
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
  have hscale := family.scales x hMin
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
  have hSupF := endpointF_sup_bound (K := K) (a := a) family hx hMin beta hbetaBound H'
  have hSupG := endpointG_sup_bound (K := K) (a := a) family hx hMin beta hbetaBound H'
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
    exact endpointF_pointwise_bound family hx hMin beta hbetaBound P
  have hPointG : ∀ P, ‖Gvec P‖ ≤ T * T := by
    intro P
    exact endpointG_pointwise_bound family hx hMin beta hbetaBound P
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

private def factorTriples (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 m) ×ˢ ((Finset.Icc 1 m) ×ˢ (Finset.Icc 1 m))).filter
    (fun t => t.1 * t.2.1 * t.2.2 = m)

private noncomputable def tau3 (m : ℕ) : ℕ := (factorTriples m).card

private lemma tau3_le_cardDivisors_sq (m : ℕ) (hm : 1 ≤ m) :
    tau3 m ≤ (m.divisors.card) ^ 2 := by
  classical
  letI : Fintype {t // t ∈ factorTriples m} :=
    Fintype.ofFinset (factorTriples m) (by intro t; rfl)
  letI : Fintype (m.divisors) := Fintype.ofFinset m.divisors (by intro d; rfl)
  let f : {t // t ∈ factorTriples m} → m.divisors × m.divisors := fun t =>
    (⟨t.1.1, by
        have ht := Finset.mem_filter.mp t.2
        have hp := Finset.mem_product.mp ht.1
        have hq := Finset.mem_product.mp hp.2
        apply Nat.mem_divisors.mpr
        refine ⟨?_, by omega⟩
        exact ⟨t.1.2.1 * t.1.2.2, by nlinarith [ht.2]⟩⟩,
     ⟨t.1.2.1, by
        have ht := Finset.mem_filter.mp t.2
        have hp := Finset.mem_product.mp ht.1
        have hq := Finset.mem_product.mp hp.2
        apply Nat.mem_divisors.mpr
        refine ⟨?_, by omega⟩
        exact ⟨t.1.1 * t.1.2.2, by nlinarith [ht.2]⟩⟩)
  have hf : Function.Injective f := by
    intro t u h
    apply Subtype.ext
    have h₁ := congrArg (fun z => z.1.val) h
    have h₂ := congrArg (fun z => z.2.val) h
    simp [f] at h₁ h₂
    rcases t with ⟨⟨a, b, c⟩, ht⟩
    rcases u with ⟨⟨a', b', c'⟩, hu⟩
    have hprod : a * b * c = m := (Finset.mem_filter.mp ht).2
    have hprod' : a' * b' * c' = m := (Finset.mem_filter.mp hu).2
    have haa : a = a' := h₁
    have hbb : b = b' := h₂
    subst a
    subst b
    have hprod_eq : a' * b' * c = a' * b' * c' := hprod.trans hprod'.symm
    have hab : 0 < a' * b' := by
      have hp := Finset.mem_product.mp (Finset.mem_filter.mp ht).1
      have hq := Finset.mem_product.mp hp.2
      have ha0 : 0 < a' := (Finset.mem_Icc.mp hp.1).1
      have hb0 : 0 < b' := (Finset.mem_Icc.mp hq.1).1
      exact Nat.mul_pos ha0 hb0
    have hc_eq : c = c' := Nat.mul_left_cancel hab hprod_eq
    subst c
    rfl
  have hc := Fintype.card_le_of_injective f hf
  simpa [tau3, Fintype.card_coe, Fintype.card_prod, pow_two] using hc

private lemma one_add_mul_le_pow (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    1 + (n : ℝ) * t ≤ (1 + t) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : 0 ≤ (n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) ht
      calc
        1 + ((n + 1 : ℕ) : ℝ) * t = 1 + (n : ℝ) * t + t := by simp [Nat.cast_add]; ring
        _ ≤ (1 + (n : ℝ) * t) * (1 + t) := by nlinarith [mul_nonneg hn ht]
        _ ≤ (1 + t) ^ n * (1 + t) := by gcongr
        _ = (1 + t) ^ (n + 1) := by rw [pow_succ]

private lemma succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      calc
        n + 1 + 1 ≤ (n + 1) + (n + 1) := by omega
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ih ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

private noncomputable def divisorLocalConstant (η : ℝ) (P p : ℕ) : ℝ :=
  if 2 ≤ p ∧ p ≤ P then 1 + 2 / ((p : ℝ) ^ η - 1) else 1

private lemma divisor_local_factor_bound (η : ℝ) (hη : 0 < η) (P : ℕ)
    (hP : 2 ≤ (P : ℝ) ^ η) {p e : ℕ} (hp : 2 ≤ p) :
    ((e + 1 : ℕ) : ℝ) ≤ divisorLocalConstant η P p *
      (p : ℝ) ^ (η * (e : ℝ)) := by
  by_cases hsmall : p ≤ P
  · have hp1 : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have ht : 0 < (p : ℝ) ^ η - 1 := sub_pos.mpr (Real.one_lt_rpow hp1 hη)
    have hbern := one_add_mul_le_pow ((p : ℝ) ^ η - 1) (le_of_lt ht) e
    have hpow : (p : ℝ) ^ (η * (e : ℝ)) = ((p : ℝ) ^ η) ^ e :=
      Real.rpow_mul_natCast (by positivity) η e
    have hmain : 1 + (e : ℝ) * ((p : ℝ) ^ η - 1) ≤
        (p : ℝ) ^ (η * (e : ℝ)) := by simpa [hpow] using hbern
    have hCpos : 0 < 1 + 2 / ((p : ℝ) ^ η - 1) := by positivity
    have hnum : (e : ℝ) + 1 ≤
        (1 + 2 / ((p : ℝ) ^ η - 1)) *
          (1 + (e : ℝ) * ((p : ℝ) ^ η - 1)) := by
      by_cases he : e = 0
      · subst e
        have ht' : 0 ≤ 2 / ((p : ℝ) ^ η - 1) := le_of_lt (by positivity)
        nlinarith
      · have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
        have heR : 1 ≤ (e : ℝ) := by exact_mod_cast he1
        have htwo : 2 / ((p : ℝ) ^ η - 1) ≤
            1 + 2 / ((p : ℝ) ^ η - 1) := by linarith
        have heterm : (e : ℝ) + 1 ≤ 2 * (e : ℝ) := by nlinarith
        have hmul : 2 * (e : ℝ) =
            (2 / ((p : ℝ) ^ η - 1)) * ((e : ℝ) * ((p : ℝ) ^ η - 1)) := by
          field_simp [ne_of_gt ht]
        have hle := mul_le_mul htwo
          (show (e : ℝ) * ((p : ℝ) ^ η - 1) ≤
            1 + (e : ℝ) * ((p : ℝ) ^ η - 1) by linarith)
          (by positivity) (by positivity)
        rw [← hmul] at hle
        exact heterm.trans hle
    unfold divisorLocalConstant
    rw [if_pos ⟨hp, hsmall⟩]
    calc
      ((e + 1 : ℕ) : ℝ) ≤
          (1 + 2 / ((p : ℝ) ^ η - 1)) *
            (1 + (e : ℝ) * ((p : ℝ) ^ η - 1)) := by exact_mod_cast hnum
      _ ≤ (1 + 2 / ((p : ℝ) ^ η - 1)) * (p : ℝ) ^ (η * (e : ℝ)) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt hCpos)
  · have hpP : (P : ℝ) ≤ p := by
      have hpPnat : P ≤ p := by omega
      exact_mod_cast hpPnat
    have hpη : 2 ≤ (p : ℝ) ^ η := by
      calc
        2 ≤ (P : ℝ) ^ η := hP
        _ ≤ (p : ℝ) ^ η := Real.rpow_le_rpow (by positivity) hpP hη.le
    have htwo : ((e + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ e := by
      exact_mod_cast succ_le_two_pow e
    have hpowbase : (2 : ℝ) ^ e ≤ ((p : ℝ) ^ η) ^ e := by gcongr
    have hpow : ((p : ℝ) ^ η) ^ e = (p : ℝ) ^ (η * (e : ℝ)) :=
      (Real.rpow_mul_natCast (by positivity) η e).symm
    simpa [divisorLocalConstant, hsmall, hpow] using htwo.trans hpowbase

private theorem divisor_card_rpow_bound (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ η := by
  classical
  let P : ℕ := Nat.ceil ((2 : ℝ) ^ η⁻¹)
  let localC : ℕ → ℝ := divisorLocalConstant η P
  let C : ℝ := ∏ p ∈ Finset.Icc 2 P, localC p
  have htarget : 1 < (2 : ℝ) ^ η⁻¹ := Real.one_lt_rpow (by norm_num) (inv_pos.mpr hη)
  have hceil : (2 : ℝ) ^ η⁻¹ ≤ (P : ℝ) := by
    exact Nat.le_ceil ((2 : ℝ) ^ η⁻¹)
  have hPgt : 1 < P := by exact_mod_cast htarget.trans_le hceil
  have hP : 2 ≤ P := by omega
  have hPη : 2 ≤ (P : ℝ) ^ η := by
    calc
      2 = ((2 : ℝ) ^ η⁻¹) ^ η := by rw [Real.rpow_inv_rpow (by norm_num) hη.ne']
      _ ≤ (P : ℝ) ^ η := Real.rpow_le_rpow (by positivity) hceil hη.le
  have hlocal1 : ∀ p, 1 ≤ localC p := by
    intro p
    by_cases hp2 : 2 ≤ p
    · by_cases hpP : p ≤ P
      · simp [localC, divisorLocalConstant, hp2, hpP]
        have hp1 : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
        have ht : 0 < (p : ℝ) ^ η - 1 := sub_pos.mpr (Real.one_lt_rpow hp1 hη)
        positivity
      · simp [localC, divisorLocalConstant, hp2, hpP]
    · simp [localC, divisorLocalConstant, hp2]
  have hCpos : 0 < C := Finset.prod_pos fun p hp =>
    lt_of_lt_of_le zero_lt_one (hlocal1 p)
  refine ⟨C, hCpos, ?_⟩
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hcard : (m.divisors.card : ℝ) =
      ∏ p ∈ m.primeFactors, ((m.factorization p + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.card_divisors hm0)
  have hlocal : ∀ p ∈ m.primeFactors,
      ((m.factorization p + 1 : ℕ) : ℝ) ≤
        localC p * (p : ℝ) ^ (η * (m.factorization p : ℝ)) := by
    intro p hp
    exact divisor_local_factor_bound η hη P hPη
      ((Nat.prime_of_mem_primeFactors hp).two_le)
  have hprod := Finset.prod_le_prod₀
    (fun p hp => by positivity) hlocal
  have hpow : (∏ p ∈ m.primeFactors,
      (p : ℝ) ^ (η * (m.factorization p : ℝ))) = (m : ℝ) ^ η := by
    have hterm (p : ℕ) : (p : ℝ) ^ (η * (m.factorization p : ℝ)) =
        ((p : ℝ) ^ m.factorization p) ^ η := by
      rw [Real.rpow_mul_natCast (by positivity) η (m.factorization p)]
      exact Real.rpow_pow_comm (by positivity) η (m.factorization p)
    calc
      _ = ∏ p ∈ m.primeFactors, ((p : ℝ) ^ m.factorization p) ^ η := by
        apply Finset.prod_congr rfl
        intro p hp
        exact hterm p
      _ = (∏ p ∈ m.primeFactors, (p : ℝ) ^ m.factorization p) ^ η := by
        exact Real.finsetProd_rpow _ _ (by intro p hp; positivity) η
      _ = (m : ℝ) ^ η := by
        have hfac : ∏ p ∈ m.primeFactors, p ^ m.factorization p = m :=
          Nat.prod_factorization_pow_eq_self hm0
        exact_mod_cast congrArg (fun z : ℕ => (z : ℝ) ^ η) hfac
  have hsmallProduct : (∏ p ∈ m.primeFactors, localC p) ≤ C := by
    let s := m.primeFactors.filter (fun p => p ≤ P)
    have heq : (∏ p ∈ m.primeFactors, localC p) = ∏ p ∈ s, localC p := by
      rw [show s = m.primeFactors.filter (fun p => p ≤ P) from rfl, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p hp
      by_cases h : p ≤ P <;> simp [localC, divisorLocalConstant, h]
    rw [heq]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp'.1).two_le, hp'.2⟩
    · intro p hp
      exact le_trans zero_le_one (hlocal1 p)
    · intro p hp hnot
      exact hlocal1 p
  calc
    (m.divisors.card : ℝ) = ∏ p ∈ m.primeFactors,
        ((m.factorization p + 1 : ℕ) : ℝ) := hcard
    _ ≤ (∏ p ∈ m.primeFactors, localC p) *
        (∏ p ∈ m.primeFactors,
          (p : ℝ) ^ (η * (m.factorization p : ℝ))) := by
      calc
        _ ≤ ∏ p ∈ m.primeFactors,
            (localC p * (p : ℝ) ^ (η * (m.factorization p : ℝ))) := hprod
        _ = _ := Finset.prod_mul_distrib
    _ ≤ C * (m : ℝ) ^ η := by rw [hpow]; exact mul_le_mul hsmallProduct le_rfl (by positivity) (by positivity)

private theorem tau3_rpow_bound (η : ℝ) (hη : 0 < η) :
    ∃ Cτ : ℝ, 0 < Cτ ∧ ∀ m : ℕ, 1 ≤ m →
      (tau3 m : ℝ) ≤ Cτ * (m : ℝ) ^ η := by
  obtain ⟨C, hC, hdiv⟩ := divisor_card_rpow_bound (η / 2) (by linarith)
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro m hm
  have hcard := tau3_le_cardDivisors_sq m hm
  have hdivm := hdiv m hm
  have hpow : ((m : ℝ) ^ (η / 2)) ^ 2 = (m : ℝ) ^ η := by
    rw [← Real.rpow_mul_natCast (by positivity) (η / 2) 2]
    congr 1
    ring
  have hmul : (C * (m : ℝ) ^ (η / 2)) ^ 2 ≤
      (C ^ 2) * (m : ℝ) ^ η := by rw [mul_pow, hpow]
  have hmain : (m.divisors.card : ℝ) ^ 2 ≤
      (C * (m : ℝ) ^ (η / 2)) ^ 2 := by
    have hdivm' : 0 ≤ (m.divisors.card : ℝ) := Nat.cast_nonneg _
    have hright : 0 ≤ C * (m : ℝ) ^ (η / 2) := by positivity
    nlinarith [hdivm]
  calc
    (tau3 m : ℝ) ≤ (m.divisors.card : ℝ) ^ 2 := by exact_mod_cast hcard
    _ ≤ (C * (m : ℝ) ^ (η / 2)) ^ 2 := hmain
    _ ≤ C ^ 2 * (m : ℝ) ^ η := hmul

private noncomputable def totientLocalConstant (η : ℝ) (P p : ℕ) : ℝ :=
  if 2 ≤ p ∧ p ≤ P then (p : ℝ) / ((p : ℝ) - 1) else 1

private theorem inverse_totient_rpow_bound (η : ℝ) (hη : 0 < η) :
    ∃ Cφ : ℝ, 0 < Cφ ∧ ∀ m : ℕ, 1 ≤ m →
      (m : ℝ) / (Nat.totient m : ℝ) ≤ Cφ * (m : ℝ) ^ η := by
  classical
  let P : ℕ := Nat.ceil ((2 : ℝ) ^ η⁻¹)
  let localC : ℕ → ℝ := totientLocalConstant η P
  let Cφ : ℝ := ∏ p ∈ Finset.Icc 2 P, localC p
  have htarget : 1 < (2 : ℝ) ^ η⁻¹ := Real.one_lt_rpow (by norm_num) (inv_pos.mpr hη)
  have hceil : (2 : ℝ) ^ η⁻¹ ≤ (P : ℝ) := by exact Nat.le_ceil ((2 : ℝ) ^ η⁻¹)
  have hPgt : 1 < P := by exact_mod_cast htarget.trans_le hceil
  have hP : 2 ≤ P := by omega
  have hPη : 2 ≤ (P : ℝ) ^ η := by
    calc
      2 = ((2 : ℝ) ^ η⁻¹) ^ η := by rw [Real.rpow_inv_rpow (by norm_num) hη.ne']
      _ ≤ (P : ℝ) ^ η := Real.rpow_le_rpow (by positivity) hceil hη.le
  have hlocal1 : ∀ p, 1 ≤ localC p := by
    intro p
    by_cases hp2 : 2 ≤ p
    · by_cases hpP : p ≤ P
      · simp [localC, totientLocalConstant, hp2, hpP]
        have hp1 : 1 ≤ (p : ℝ) := by
          exact_mod_cast (le_trans (by decide : 1 ≤ 2) hp2)
        have hpReal : 1 < (p : ℝ) := by
          exact_mod_cast (show 1 < p by omega)
        have hden : 0 < (p : ℝ) - 1 := by linarith
        rw [le_div_iff₀ hden]
        nlinarith
      · simp [localC, totientLocalConstant, hp2, hpP]
    · simp [localC, totientLocalConstant, hp2]
  have hCpos : 0 < Cφ := Finset.prod_pos fun p hp =>
    lt_of_lt_of_le zero_lt_one (hlocal1 p)
  refine ⟨Cφ, hCpos, ?_⟩
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hphi : 0 < Nat.totient m := Nat.totient_pos.mpr (by omega)
  have hratio : (m : ℝ) / (Nat.totient m : ℝ) =
      ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    have hformNat := Nat.totient_mul_prod_primeFactors m
    have hform : (Nat.totient m : ℝ) *
          (∏ p ∈ m.primeFactors, (p : ℝ)) =
        ((m * ∏ p ∈ m.primeFactors, (p - 1) : ℕ) : ℝ) := by
      have hcast := congrArg (fun z : ℕ => (z : ℝ)) hformNat
      simpa only [Nat.cast_mul, Nat.cast_prod] using hcast
    have hform' : (Nat.totient m : ℝ) *
          (∏ p ∈ m.primeFactors, (p : ℝ)) =
        (m : ℝ) * ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
      calc
        _ = (m : ℝ) * ∏ p ∈ m.primeFactors, ((p - 1 : ℕ) : ℝ) := by
          rw [hform]
          simp only [Nat.cast_mul, Nat.cast_prod]
        _ = (m : ℝ) * ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
          congr 1
          apply Finset.prod_congr rfl
          intro p hp
          have hp1 : 1 ≤ p :=
            Nat.le_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
          rw [Nat.cast_sub hp1, Nat.cast_one]
    have hprodRatio :
        (∏ p ∈ m.primeFactors, (p : ℝ)) /
            (∏ p ∈ m.primeFactors, ((p : ℝ) - 1)) =
          ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
      rw [← Finset.prod_div_distrib]
    have hden : (∏ p ∈ m.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
      apply ne_of_gt
      apply Finset.prod_pos
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hpReal : 1 < (p : ℝ) := by exact_mod_cast hprime.one_lt
      exact sub_pos.mpr hpReal
    rw [← hprodRatio]
    apply (div_eq_div_iff (by positivity) hden).2
    nlinarith [hform']
  have hlocal : ∀ p ∈ m.primeFactors,
      (p : ℝ) / ((p : ℝ) - 1) ≤ localC p * (p : ℝ) ^ η := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hp1 : 1 ≤ (p : ℝ) := by
      exact_mod_cast (le_trans (by decide : 1 ≤ 2) hp2)
    by_cases hpP : p ≤ P
    · have hpη : 1 ≤ (p : ℝ) ^ η := by
        apply Real.one_le_rpow
        · exact hp1
        · exact hη.le
      simp [localC, totientLocalConstant, hp2, hpP]
      have hratio_nonneg : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) := by positivity
      simpa using mul_le_mul_of_nonneg_left hpη hratio_nonneg
    · have hpPcast : (P : ℝ) ≤ p := by
        have hnat : P ≤ p := by omega
        exact_mod_cast hnat
      have hpη : 2 ≤ (p : ℝ) ^ η := by
        calc
          2 ≤ (P : ℝ) ^ η := hPη
          _ ≤ (p : ℝ) ^ η := Real.rpow_le_rpow (by positivity) hpPcast hη.le
      have hratio2 : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
        have hpReal : 1 < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
        have hpReal2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp2
        have hden : 0 < (p : ℝ) - 1 := by linarith
        rw [div_le_iff₀ hden]
        nlinarith [hpReal2]
      simpa [localC, totientLocalConstant, hp2, hpP] using hratio2.trans hpη
  have hprod := Finset.prod_le_prod₀
    (fun p hp => by
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hpReal : 1 < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
      positivity) hlocal
  have hsmallProduct : (∏ p ∈ m.primeFactors, localC p) ≤ Cφ := by
    let s := m.primeFactors.filter (fun p => p ≤ P)
    have heq : (∏ p ∈ m.primeFactors, localC p) = ∏ p ∈ s, localC p := by
      rw [show s = m.primeFactors.filter (fun p => p ≤ P) from rfl, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p hp
      by_cases h : p ≤ P <;> simp [localC, totientLocalConstant, h]
    rw [heq]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp'.1).two_le, hp'.2⟩
    · intro p hp
      exact le_trans zero_le_one (hlocal1 p)
    · intro p hp hnot
      exact hlocal1 p
  have hrad_dvd : (∏ p ∈ m.primeFactors, p) ∣ m := Nat.prod_primeFactors_dvd m
  have hrad_le : (∏ p ∈ m.primeFactors, p) ≤ m :=
    Nat.le_of_dvd (by omega) hrad_dvd
  have hpow : (∏ p ∈ m.primeFactors, (p : ℝ) ^ η) ≤ (m : ℝ) ^ η := by
    rw [Real.finsetProd_rpow _ _ (by intro p hp; positivity) η]
    have hcastprod : (∏ p ∈ m.primeFactors, (p : ℝ)) =
        ((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) := by
      exact (Nat.cast_prod (fun p : ℕ => p) m.primeFactors).symm
    rw [hcastprod]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hrad_le) hη.le
  calc
    (m : ℝ) / (Nat.totient m : ℝ) =
        ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := hratio
    _ ≤ (∏ p ∈ m.primeFactors, localC p) *
        (∏ p ∈ m.primeFactors, (p : ℝ) ^ η) := by
      calc
        _ ≤ ∏ p ∈ m.primeFactors, (localC p * (p : ℝ) ^ η) := hprod
        _ = _ := Finset.prod_mul_distrib
    _ ≤ Cφ * (m : ℝ) ^ η := by
      exact mul_le_mul hsmallProduct hpow (by positivity) (by positivity)

private lemma card_fin_divisible_le (m d : ℕ) (hd : 0 < d) (hdm : d ∣ m) :
    (Finset.univ.filter fun i : Fin m => d ∣ i.val).card ≤ m / d := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter fun i => d ∣ i.val
  letI : Fintype {i // i ∈ S} := Fintype.ofFinset S (by intro i; rfl)
  let f : {i // i ∈ S} → Fin (m / d) := fun i =>
    ⟨i.1.val / d, by
      rw [Nat.div_lt_iff_lt_mul hd]
      have hmd : m / d * d = m := Nat.div_mul_cancel hdm
      rw [hmd]
      exact i.1.isLt⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hq : i.1.val / d = j.1.val / d := congrArg Fin.val hij
    have hi : d * (i.1.val / d) = i.1.val := by
      calc
        d * (i.1.val / d) = (i.1.val / d) * d := Nat.mul_comm _ _
        _ = i.1.val := Nat.div_mul_cancel (Finset.mem_filter.mp i.2).2
    have hj : d * (j.1.val / d) = j.1.val := by
      calc
        d * (j.1.val / d) = (j.1.val / d) * d := Nat.mul_comm _ _
        _ = j.1.val := Nat.div_mul_cancel (Finset.mem_filter.mp j.2).2
    rw [← hi, ← hj, hq]
  have hc := Fintype.card_le_of_injective f hf
  calc
    (Finset.univ.filter fun i : Fin m => d ∣ i.val).card = S.card := rfl
    _ = Fintype.card {i // i ∈ S} := (Fintype.card_coe S).symm
    _ ≤ Fintype.card (Fin (m / d)) := hc
    _ = m / d := Fintype.card_fin _

private lemma sum_gcd_fin_le (m : ℕ) (hm : 0 < m) :
    (∑ i : Fin m, Nat.gcd m i.val) ≤ m * m.divisors.card := by
  classical
  have hpoint (i : Fin m) :
      Nat.gcd m i.val ≤
        ∑ d ∈ m.divisors.filter (fun d => d ∣ i.val), d := by
    have hmem : Nat.gcd m i.val ∈ m.divisors.filter (fun d => d ∣ i.val) :=
      Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left m i.val, hm.ne'⟩,
          Nat.gcd_dvd_right m i.val⟩
    exact Finset.single_le_sum (fun d hd => Nat.zero_le d) hmem
  have hswap :
      (∑ i : Fin m, ∑ d ∈ m.divisors.filter (fun d => d ∣ i.val), d) =
        ∑ d ∈ m.divisors,
          d * (Finset.univ.filter fun i : Fin m => d ∣ i.val).card := by
    calc
      _ = ∑ i : Fin m, ∑ d ∈ m.divisors, if d ∣ i.val then d else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_filter]
      _ = ∑ d ∈ m.divisors, ∑ i : Fin m, if d ∣ i.val then d else 0 :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [← Finset.sum_filter]
        simp [Finset.sum_const, mul_comm]
  calc
    (∑ i : Fin m, Nat.gcd m i.val) ≤
        ∑ i : Fin m, ∑ d ∈ m.divisors.filter (fun d => d ∣ i.val), d :=
      Finset.sum_le_sum fun i hi => hpoint i
    _ = _ := hswap
    _ ≤ ∑ d ∈ m.divisors, m := by
      apply Finset.sum_le_sum
      intro d hd
      have hdiv : d ∣ m := Nat.dvd_of_mem_divisors hd
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv hm
      have hcard := card_fin_divisible_le m d hpos hdiv
      calc
        d * (Finset.univ.filter fun i : Fin m => d ∣ i.val).card ≤ d * (m / d) :=
          Nat.mul_le_mul_left d hcard
        _ = m := by simpa [Nat.mul_comm] using Nat.div_mul_cancel hdiv
    _ = m * m.divisors.card := by simp [Finset.sum_const, mul_comm]

private lemma zmod_mul_zero_card (m d : ℕ) [NeZero m] :
    Fintype.card {c : ZMod m // (d : ZMod m) * c = 0} = Nat.gcd m d := by
  classical
  let φ : ZMod m →+ ZMod m := nsmulAddMonoidHom d
  have hφ (c : ZMod m) : φ c = (d : ZMod m) * c := by
    simp [φ, nsmulAddMonoidHom_apply, nsmul_eq_mul]
  let e : {c : ZMod m // (d : ZMod m) * c = 0} ≃ φ.ker :=
    { toFun := fun c => (⟨c.1, by
          change φ c.1 = 0
          rw [hφ c.1]
          exact c.2⟩ : φ.ker)
      invFun := fun c => (⟨c.1, by
          change (d : ZMod m) * c.1 = 0
          rw [← hφ c.1]
          exact c.2⟩ : {c : ZMod m // (d : ZMod m) * c = 0})
      left_inv := by intro c; apply Subtype.ext; rfl
      right_inv := by intro c; apply Subtype.ext; rfl }
  calc
    Fintype.card {c : ZMod m // (d : ZMod m) * c = 0} = Fintype.card φ.ker :=
      Fintype.card_congr e
    _ = Nat.card φ.ker := Nat.card_eq_fintype_card.symm
    _ = Nat.gcd (Nat.card (ZMod m)) d :=
      IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) d
    _ = Nat.gcd m d := by simp

private noncomputable def zmodEquivFin (m : ℕ) [NeZero m] : ZMod m ≃ Fin m where
  toFun a := ⟨a.val, a.val_lt⟩
  invFun i := (i.val : ZMod m)
  left_inv := ZMod.natCast_zmod_val
  right_inv := by
    intro i
    apply Fin.ext
    simp [ZMod.val_natCast_of_lt i.isLt]

private lemma sum_zmod_gcd_val_le (m : ℕ) [NeZero m] :
    (∑ a : ZMod m, Nat.gcd m a.val) ≤ m * m.divisors.card := by
  calc
    (∑ a : ZMod m, Nat.gcd m a.val) =
        ∑ i : Fin m, Nat.gcd m i.val := by
          apply Fintype.sum_equiv (zmodEquivFin m)
          intro a
          rfl
    _ ≤ m * m.divisors.card := sum_gcd_fin_le m (NeZero.pos m)

private lemma zmod_mul_zero_card_of_residues {m : ℕ} [NeZero m] (a b : ZMod m) :
    Fintype.card {c : ZMod m // a * b * c = 0} =
      Nat.gcd m (a * b).val := by
  simpa only [ZMod.natCast_zmod_val] using zmod_mul_zero_card m (a * b).val

private lemma zero_product_zmod_card_eq (m : ℕ) [NeZero m] :
    Fintype.card {t : ZMod m × ZMod m × ZMod m // t.1 * t.2.1 * t.2.2 = 0} =
      ∑ a : ZMod m, ∑ b : ZMod m, Nat.gcd m (a * b).val := by
  classical
  let T := {t : ZMod m × ZMod m × ZMod m // t.1 * t.2.1 * t.2.2 = 0}
  let E := Σ a : ZMod m, Σ b : ZMod m, {c : ZMod m // a * b * c = 0}
  let e :
      {t : ZMod m × ZMod m × ZMod m // t.1 * t.2.1 * t.2.2 = 0} ≃
        (Σ a : ZMod m, Σ b : ZMod m, {c : ZMod m // a * b * c = 0}) :=
    { toFun := fun t => ⟨t.1.1, ⟨t.1.2.1, ⟨t.1.2.2, t.2⟩⟩⟩
      invFun := fun z => ⟨(z.1, (z.2.1, z.2.2.1)), by simpa using z.2.2.2⟩
      left_inv := by
        intro t
        apply Subtype.ext
        rcases t with ⟨⟨a, b, c⟩, ht⟩
        rfl
      right_inv := by
        intro z
        rcases z with ⟨a, ⟨b, ⟨c, hc⟩⟩⟩
        rfl }
  calc
    Fintype.card T = Fintype.card E := Fintype.card_congr e
    _ = ∑ a : ZMod m, ∑ b : ZMod m,
          Fintype.card {c : ZMod m // a * b * c = 0} := by
      simp [E, Fintype.card_sigma]
    _ = ∑ a : ZMod m, ∑ b : ZMod m, Nat.gcd m (a * b).val := by
      apply Fintype.sum_congr
      intro a
      apply Fintype.sum_congr
      intro b
      exact zmod_mul_zero_card_of_residues a b

private lemma zero_product_zmod_card_le (m : ℕ) [NeZero m] :
    Fintype.card {t : ZMod m × ZMod m × ZMod m // t.1 * t.2.1 * t.2.2 = 0} ≤
      m ^ 2 * (m.divisors.card) ^ 2 := by
  classical
  have hpoint (a b : ZMod m) :
      Nat.gcd m (a * b).val ≤ Nat.gcd m a.val * Nat.gcd m b.val := by
    have hval : (a * b).val = a.val * b.val % m := ZMod.val_mul a b
    let g := Nat.gcd m (a * b).val
    have hgM : g ∣ m := Nat.gcd_dvd_left m (a * b).val
    have hgval : g ∣ (a * b).val := Nat.gcd_dvd_right m (a * b).val
    have hgmod : g ∣ a.val * b.val % m := by rw [← hval]; exact hgval
    have hmodAdd : a.val * b.val % m + m * (a.val * b.val / m) =
        a.val * b.val := Nat.mod_add_div _ _
    have hgprod : g ∣ a.val * b.val := by
      rw [← hmodAdd]
      exact Nat.dvd_add hgmod (dvd_mul_of_dvd_left hgM _)
    have hdvd := (Nat.dvd_gcd hgM hgprod).trans
      (gcd_mul_dvd_mul_gcd m a.val b.val)
    exact Nat.le_of_dvd
      (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (NeZero.pos m))
        (Nat.gcd_pos_of_pos_left _ (NeZero.pos m))) hdvd
  have hsum : (∑ a : ZMod m, ∑ b : ZMod m, Nat.gcd m (a * b).val) ≤
      (∑ a : ZMod m, Nat.gcd m a.val) ^ 2 := by
    calc
      _ ≤ ∑ a : ZMod m, ∑ b : ZMod m, Nat.gcd m a.val * Nat.gcd m b.val := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        exact hpoint a b
      _ = (∑ a : ZMod m, Nat.gcd m a.val) *
          (∑ b : ZMod m, Nat.gcd m b.val) := by rw [Fintype.sum_mul_sum]
      _ = (∑ a : ZMod m, Nat.gcd m a.val) ^ 2 := by ring
  have hgcdsum := sum_zmod_gcd_val_le m
  have hpow : (∑ a : ZMod m, Nat.gcd m a.val) ^ 2 ≤
      (m * m.divisors.card) ^ 2 := Nat.pow_le_pow_left hgcdsum 2
  have hcard := zero_product_zmod_card_eq m
  calc
    Fintype.card {t : ZMod m × ZMod m × ZMod m // t.1 * t.2.1 * t.2.2 = 0}
        = ∑ a : ZMod m, ∑ b : ZMod m, Nat.gcd m (a * b).val := hcard
    _ ≤ (∑ a : ZMod m, Nat.gcd m a.val) ^ 2 := hsum
    _ ≤ (m * m.divisors.card) ^ 2 := hpow
    _ = m ^ 2 * (m.divisors.card) ^ 2 := by ring

private def linearForms {m : ℕ} (t : ZMod m × ZMod m × ZMod m) :
    ZMod m × ZMod m × ZMod m :=
  (t.1 + t.2.1, (t.2.2 - t.1, t.2.2 - t.2.1))

private lemma linearForms_fiber_card_le_two (m : ℕ) [NeZero m]
    (v : ZMod m × ZMod m × ZMod m) :
    Fintype.card {t : ZMod m × ZMod m × ZMod m // linearForms t = v} ≤ 2 := by
  classical
  by_cases hne : Nonempty {t : ZMod m × ZMod m × ZMod m // linearForms t = v}
  · let t₀ := Classical.choice hne
    let f : {t : ZMod m × ZMod m × ZMod m // linearForms t = v} →
        {w : ZMod m // (2 : ZMod m) * w = 0} := fun t =>
      ⟨t.1.1 - t₀.1.1, by
        have hsame : linearForms t.1 = linearForms t₀.1 := t.2.trans t₀.2.symm
        have h₁ : t.1.1 + t.1.2.1 = t₀.1.1 + t₀.1.2.1 :=
          congrArg Prod.fst hsame
        have h₂ : t.1.2.2 - t.1.1 = t₀.1.2.2 - t₀.1.1 :=
          congrArg (fun z => z.2.1) hsame
        have h₃ : t.1.2.2 - t.1.2.1 = t₀.1.2.2 - t₀.1.2.1 :=
          congrArg (fun z => z.2.2) hsame
        have hid (x y z : ZMod m) : 2 * x = (x + y) - (z - x) + (z - y) := by ring
        calc
          2 * (t.1.1 - t₀.1.1) = 2 * t.1.1 - 2 * t₀.1.1 := by ring
          _ = ((t.1.1 + t.1.2.1) - (t.1.2.2 - t.1.1) +
                (t.1.2.2 - t.1.2.1)) -
              ((t₀.1.1 + t₀.1.2.1) - (t₀.1.2.2 - t₀.1.1) +
                (t₀.1.2.2 - t₀.1.2.1)) := by rw [hid, hid]
          _ = 0 := by rw [h₁, h₂, h₃]; ring⟩
    have hf : Function.Injective f := by
      intro t u h
      apply Subtype.ext
      have hfirst : t.1.1 = u.1.1 := by
        have h' := congrArg (fun w : ZMod m => w + t₀.1.1) (congrArg Subtype.val h)
        simpa [f, sub_add_cancel] using h'
      have hsame : linearForms t.1 = linearForms u.1 := t.2.trans u.2.symm
      have hsum : t.1.1 + t.1.2.1 = u.1.1 + u.1.2.1 :=
        congrArg Prod.fst hsame
      have hsecond : t.1.2.1 = u.1.2.1 := by
        calc
          t.1.2.1 = (t.1.1 + t.1.2.1) - t.1.1 := by ring
          _ = (u.1.1 + u.1.2.1) - t.1.1 := by rw [hsum]
          _ = u.1.2.1 := by rw [hfirst]; ring
      have hthird' : t.1.2.2 - t.1.1 = u.1.2.2 - u.1.1 :=
        congrArg (fun z => z.2.1) hsame
      have hthird : t.1.2.2 = u.1.2.2 := by
        calc
          t.1.2.2 = (t.1.2.2 - t.1.1) + t.1.1 := (sub_add_cancel _ _).symm
          _ = (u.1.2.2 - u.1.1) + u.1.1 := by rw [hthird', hfirst]
          _ = u.1.2.2 := sub_add_cancel _ _
      exact Prod.ext hfirst (Prod.ext hsecond hthird)
    have hcard := Fintype.card_le_of_injective f hf
    have hker := zmod_mul_zero_card m 2
    have hle : Nat.gcd m 2 ≤ 2 :=
      Nat.gcd_le_right m (by norm_num : 0 < (2 : ℕ))
    have hker' : Fintype.card {w : ZMod m // (2 : ZMod m) * w = 0} =
        Nat.gcd m 2 := by simpa using hker
    calc
      Fintype.card {t : ZMod m × ZMod m × ZMod m // linearForms t = v} ≤
          Fintype.card {w : ZMod m // (2 : ZMod m) * w = 0} := hcard
      _ = Nat.gcd m 2 := hker'
      _ ≤ 2 := hle
  · letI : IsEmpty {t : ZMod m × ZMod m × ZMod m // linearForms t = v} :=
      ⟨fun t => hne ⟨t⟩⟩
    simp

private def unitQuadTriple {m : ℕ} (q : UnitQuad m) :
    ZMod m × ZMod m × ZMod m :=
  ((q.1.1 : ZMod m), ((q.2.1 : ZMod m), (q.1.2 : ZMod m)))

private lemma unitQuad_add_relation {m : ℕ} (q : UnitQuad m)
    (hq : unitQuadSolution q) :
    (q.1.1 : ZMod m) + (q.2.1 : ZMod m) =
      (q.1.2 : ZMod m) + (q.2.2 : ZMod m) := by
  have h : ((q.1.2 : ZMod m) - q.1.1) +
      ((q.2.2 : ZMod m) - q.2.1) = 0 := by
    simpa [unitQuadSolution, unitQuadAddDelta, unitPairAddDelta] using hq.1
  have hz : ((q.1.2 : ZMod m) + q.2.2) -
      ((q.1.1 : ZMod m) + q.2.1) = 0 := by
    calc
      _ = ((q.1.2 : ZMod m) - q.1.1) +
          ((q.2.2 : ZMod m) - q.2.1) := by ring
      _ = 0 := h
  exact (sub_eq_zero.mp hz).symm

private lemma unitQuad_inverse_relation {m : ℕ} (q : UnitQuad m)
    (hq : unitQuadSolution q) :
    ((q.1.1 : ZMod m)⁻¹ + (q.2.1 : ZMod m)⁻¹) =
      ((q.1.2 : ZMod m)⁻¹ + (q.2.2 : ZMod m)⁻¹) := by
  have h : ((q.1.2 : ZMod m)⁻¹ - (q.1.1 : ZMod m)⁻¹) +
      ((q.2.2 : ZMod m)⁻¹ - (q.2.1 : ZMod m)⁻¹) = 0 := by
    simpa [unitQuadSolution, unitQuadInvDelta, unitPairInvDelta,
      Units.val_inv_eq_inv_val] using hq.2
  have hz : ((q.1.1 : ZMod m)⁻¹ + (q.2.1 : ZMod m)⁻¹) -
      ((q.1.2 : ZMod m)⁻¹ + (q.2.2 : ZMod m)⁻¹) = 0 := by
    calc
      _ = -(((q.1.2 : ZMod m)⁻¹ - (q.1.1 : ZMod m)⁻¹) +
          ((q.2.2 : ZMod m)⁻¹ - (q.2.1 : ZMod m)⁻¹)) := by ring
      _ = 0 := by rw [h]; ring
  exact sub_eq_zero.mp hz

private lemma unitQuad_solution_poly_zero {m : ℕ} [NeZero m] (q : UnitQuad m)
    (hq : unitQuadSolution q) :
    (linearForms (unitQuadTriple q)).1 *
      (linearForms (unitQuadTriple q)).2.1 *
      (linearForms (unitQuadTriple q)).2.2 = 0 := by
  let y1 : ZMod m := q.1.1
  let y2 : ZMod m := q.2.1
  let z1 : ZMod m := q.1.2
  let z2 : ZMod m := q.2.2
  have hadd : y1 + y2 = z1 + z2 := by
    simpa [y1, y2, z1, z2] using unitQuad_add_relation q hq
  have hinv : y1⁻¹ + y2⁻¹ = z1⁻¹ + z2⁻¹ := by
    simpa [y1, y2, z1, z2] using unitQuad_inverse_relation q hq
  have hy1cancel : y1 * y1⁻¹ = 1 := by
    simpa [y1, Units.val_inv_eq_inv_val] using q.1.1.val_inv
  have hy2cancel : y2 * y2⁻¹ = 1 := by
    simpa [y2, Units.val_inv_eq_inv_val] using q.2.1.val_inv
  have hz1cancel : z1 * z1⁻¹ = 1 := by
    simpa [z1, Units.val_inv_eq_inv_val] using q.1.2.val_inv
  have hz2cancel : z2 * z2⁻¹ = 1 := by
    simpa [z2, Units.val_inv_eq_inv_val] using q.2.2.val_inv
  let P : ZMod m := y1 * y2 * z1 * z2
  have hleft : P * (y1⁻¹ + y2⁻¹) = (y1 + y2) * z1 * z2 := by
    dsimp [P]
    rw [mul_add]
    have ht₁ : y1 * y2 * z1 * z2 * y1⁻¹ = y2 * z1 * z2 := by
      calc
        _ = (y1 * y1⁻¹) * (y2 * z1 * z2) := by ring
        _ = _ := by rw [hy1cancel]; ring
    have ht₂ : y1 * y2 * z1 * z2 * y2⁻¹ = y1 * z1 * z2 := by
      calc
        _ = (y2 * y2⁻¹) * (y1 * z1 * z2) := by ring
        _ = _ := by rw [hy2cancel]; ring
    rw [ht₁, ht₂]
    ring
  have hright : P * (z1⁻¹ + z2⁻¹) = y1 * y2 * (z1 + z2) := by
    dsimp [P]
    rw [mul_add]
    have ht₁ : y1 * y2 * z1 * z2 * z1⁻¹ = y1 * y2 * z2 := by
      calc
        _ = (z1 * z1⁻¹) * (y1 * y2 * z2) := by ring
        _ = _ := by rw [hz1cancel]; ring
    have ht₂ : y1 * y2 * z1 * z2 * z2⁻¹ = y1 * y2 * z1 := by
      calc
        _ = (z2 * z2⁻¹) * (y1 * y2 * z1) := by ring
        _ = _ := by rw [hz2cancel]; ring
    rw [ht₁, ht₂]
    ring
  have hEq : (y1 + y2) * z1 * z2 = y1 * y2 * (z1 + z2) := by
    calc
      _ = P * (y1⁻¹ + y2⁻¹) := hleft.symm
      _ = P * (z1⁻¹ + z2⁻¹) := congrArg (fun w : ZMod m => P * w) hinv
      _ = _ := hright
  have hS : (y1 + y2) * z1 * z2 = y1 * y2 * (y1 + y2) := by
    simpa [hadd] using hEq
  have hprod : (y1 + y2) * (y1 * y2 - z1 * z2) = 0 := by
    calc
      _ = y1 * y2 * (y1 + y2) - (y1 + y2) * z1 * z2 := by ring
      _ = 0 := by rw [hS]; ring
  have hfactor : (z1 - y1) * (z1 - y2) = y1 * y2 - z1 * z2 := by
    calc
      _ = z1 * z1 - z1 * (y1 + y2) + y1 * y2 := by ring
      _ = z1 * z1 - z1 * (z1 + z2) + y1 * y2 := by rw [hadd]
      _ = _ := by ring
  have htarget : (y1 + y2) * (z1 - y1) * (z1 - y2) = 0 := by
    calc
      _ = (y1 + y2) * ((z1 - y1) * (z1 - y2)) := by ring
      _ = (y1 + y2) * (y1 * y2 - z1 * z2) := by rw [hfactor]
      _ = 0 := hprod
  simpa [linearForms, unitQuadTriple, y1, y2, z1, z2] using htarget

private lemma unitQuadTriple_injective_on_solutions {m : ℕ}
    (q r : UnitQuad m) (hq : unitQuadSolution q) (hr : unitQuadSolution r)
    (h : unitQuadTriple q = unitQuadTriple r) : q = r := by
  apply Prod.ext
  · apply Prod.ext
    · apply Units.ext
      exact congrArg Prod.fst h
    · apply Units.ext
      exact congrArg (fun z => z.2.2) h
  · apply Prod.ext
    · apply Units.ext
      exact congrArg (fun z => z.2.1) h
    · apply Units.ext
      have hqadd := unitQuad_add_relation q hq
      have hradd := unitQuad_add_relation r hr
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg (fun z => z.2.1) h
      have h₃ := congrArg (fun z => z.2.2) h
      have h₁' : (q.1.1 : ZMod m) = r.1.1 := by simpa [unitQuadTriple] using h₁
      have h₂' : (q.2.1 : ZMod m) = r.2.1 := by simpa [unitQuadTriple] using h₂
      have h₃' : (q.1.2 : ZMod m) = r.1.2 := by simpa [unitQuadTriple] using h₃
      have hqform : (q.2.2 : ZMod m) =
          (q.1.1 : ZMod m) + (q.2.1 : ZMod m) - q.1.2 := by
        calc
          (q.2.2 : ZMod m) =
              ((q.1.2 : ZMod m) + q.2.2) - q.1.2 := by ring
          _ = ((q.1.1 : ZMod m) + q.2.1) - q.1.2 := by rw [← hqadd]
      have hrform : (r.2.2 : ZMod m) =
          (r.1.1 : ZMod m) + (r.2.1 : ZMod m) - r.1.2 := by
        calc
          (r.2.2 : ZMod m) =
              ((r.1.2 : ZMod m) + r.2.2) - r.1.2 := by ring
          _ = ((r.1.1 : ZMod m) + r.2.1) - r.1.2 := by rw [← hradd]
      rw [hqform, hrform, h₁', h₂', h₃']

private lemma unitQuadSolutions_card_le (m : ℕ) [NeZero m] :
    (unitQuadSolutions m).card ≤
      2 * (Finset.univ.filter
        (fun t : ZMod m × ZMod m × ZMod m => t.1 * t.2.1 * t.2.2 = 0)).card := by
  classical
  let α := {q : UnitQuad m // q ∈ unitQuadSolutions m}
  let f : α → ZMod m × ZMod m × ZMod m :=
    fun q => linearForms (unitQuadTriple q.1)
  let e : α ≃ Σ t : ZMod m × ZMod m × ZMod m, {q : α // f q = t} :=
    { toFun := fun q => ⟨f q, ⟨q, rfl⟩⟩
      invFun := fun z => z.2.1
      left_inv := by intro q; rfl
      right_inv := by
        rintro ⟨t, ⟨q, hq⟩⟩
        cases hq
        rfl }
  have hfiber (t : ZMod m × ZMod m × ZMod m) :
      Fintype.card {q : α // f q = t} ≤
        if t.1 * t.2.1 * t.2.2 = 0 then 2 else 0 := by
    by_cases ht : t.1 * t.2.1 * t.2.2 = 0
    · let g : {q : α // f q = t} →
          {s : ZMod m × ZMod m × ZMod m // linearForms s = t} :=
        fun q => ⟨unitQuadTriple q.1.1, q.2⟩
      have hg : Function.Injective g := by
        intro q r h
        have htriple : unitQuadTriple q.1.1 = unitQuadTriple r.1.1 :=
          congrArg Subtype.val h
        have hq : unitQuadSolution q.1.1 := by
          simpa [unitQuadSolutions] using q.1.2
        have hr : unitQuadSolution r.1.1 := by
          simpa [unitQuadSolutions] using r.1.2
        have hα : q.1 = r.1 := by
          apply Subtype.ext
          exact unitQuadTriple_injective_on_solutions q.1.1 r.1.1 hq hr htriple
        exact Subtype.ext hα
      have hcard := Fintype.card_le_of_injective g hg
      simpa [ht] using hcard.trans (linearForms_fiber_card_le_two m t)
    · letI : IsEmpty {q : α // f q = t} := ⟨fun q =>
        ht (by
          have hq : unitQuadSolution q.1.1 := by
            simpa [unitQuadSolutions] using q.1.2
          have hz := unitQuad_solution_poly_zero q.1.1 hq
          simpa [f, q.2] using hz)⟩
      simp [ht]
  have hsum : Fintype.card α =
      ∑ t : ZMod m × ZMod m × ZMod m, Fintype.card {q : α // f q = t} := by
    calc
      Fintype.card α = Fintype.card
          (Σ t : ZMod m × ZMod m × ZMod m, {q : α // f q = t}) :=
        Fintype.card_congr e
      _ = _ := Fintype.card_sigma
  have hsumle :
      (∑ t : ZMod m × ZMod m × ZMod m, Fintype.card {q : α // f q = t}) ≤
        2 * (Finset.univ.filter
          (fun t : ZMod m × ZMod m × ZMod m => t.1 * t.2.1 * t.2.2 = 0)).card := by
    calc
      _ ≤ ∑ t : ZMod m × ZMod m × ZMod m,
          if t.1 * t.2.1 * t.2.2 = 0 then 2 else 0 := by
        apply Finset.sum_le_sum
        intro t ht
        exact hfiber t
      _ = _ := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact Nat.mul_comm _ _
  calc
    (unitQuadSolutions m).card = Fintype.card α := by
      simp [α, Fintype.card_coe]
    _ = _ := hsum
    _ ≤ _ := hsumle

private def kloostermanScalePoint {m : ℕ} (h k : ZMod m)
    (s : (ZMod m)ˣ) : ZMod m × ZMod m :=
  (h * (s : ZMod m), k * ((s⁻¹ : (ZMod m)ˣ) : ZMod m))

private lemma kloostermanStabilizer_card_le (m h k : ℕ) [NeZero m] :
    Fintype.card
      {s : (ZMod m)ˣ // kloostermanScalePoint (h : ZMod m) (k : ZMod m) s =
        ((h : ZMod m), (k : ZMod m))} ≤ Nat.gcd (Nat.gcd h k) m := by
  classical
  let d := Nat.gcd h k
  let g := Nat.gcd d m
  let S := {s : (ZMod m)ˣ //
    kloostermanScalePoint (h : ZMod m) (k : ZMod m) s = ((h : ZMod m), (k : ZMod m))}
  let K := {x : ZMod m // (g : ZMod m) * x = 0}
  have hdInt : (d : ℤ) =
      (h : ℤ) * (Nat.gcdA h k : ℤ) + (k : ℤ) * (Nat.gcdB h k : ℤ) :=
    Nat.gcd_eq_gcd_ab h k
  have hgInt : (g : ℤ) =
      (d : ℤ) * (Nat.gcdA d m : ℤ) + (m : ℤ) * (Nat.gcdB d m : ℤ) :=
    Nat.gcd_eq_gcd_ab d m
  have hdZ : (d : ZMod m) =
      (Nat.gcdA h k : ZMod m) * h + (Nat.gcdB h k : ZMod m) * k := by
    have hh := congrArg (fun z : ℤ => (z : ZMod m)) hdInt
    simpa [Int.cast_mul, Int.cast_add, Int.cast_natCast,
      mul_comm, mul_left_comm, mul_assoc] using hh
  have hgZ : (g : ZMod m) =
      (Nat.gcdA d m : ZMod m) * d + (Nat.gcdB d m : ZMod m) * m := by
    have hh := congrArg (fun z : ℤ => (z : ZMod m)) hgInt
    simpa [Int.cast_mul, Int.cast_add, Int.cast_natCast,
      mul_comm, mul_left_comm, mul_assoc] using hh
  let f : S → K := fun s =>
    ⟨(s.1 : ZMod m) - 1, by
      have hfirst : (h : ZMod m) * ((s.1 : ZMod m) - 1) = 0 := by
        calc
          _ = (h : ZMod m) * (s.1 : ZMod m) - h := by ring
          _ = 0 := by
            have hs := congrArg Prod.fst s.2
            dsimp [kloostermanScalePoint] at hs
            rw [hs]
            ring
      have hinv : (k : ZMod m) * (s.1⁻¹ : ZMod m) = k := by
        simpa [kloostermanScalePoint] using congrArg Prod.snd s.2
      have hsecondMul : (k : ZMod m) * (s.1 : ZMod m) = k := by
        have hmul := congrArg (fun z : ZMod m => z * (s.1 : ZMod m)) hinv
        simpa [mul_assoc, Units.val_inv_eq_inv_val] using hmul.symm
      have hsecond : (k : ZMod m) * ((s.1 : ZMod m) - 1) = 0 := by
        calc
          _ = (k : ZMod m) * (s.1 : ZMod m) - k := by ring
          _ = 0 := by rw [hsecondMul]; ring
      have hdx : (d : ZMod m) * ((s.1 : ZMod m) - 1) = 0 := by
        calc
          _ = (Nat.gcdA h k : ZMod m) *
                ((h : ZMod m) * ((s.1 : ZMod m) - 1)) +
              (Nat.gcdB h k : ZMod m) *
                ((k : ZMod m) * ((s.1 : ZMod m) - 1)) := by rw [hdZ]; ring
          _ = 0 := by rw [hfirst, hsecond]; ring
      calc
        (g : ZMod m) * ((s.1 : ZMod m) - 1) =
            (Nat.gcdA d m : ZMod m) *
                ((d : ZMod m) * ((s.1 : ZMod m) - 1)) +
              (Nat.gcdB d m : ZMod m) *
                ((m : ZMod m) * ((s.1 : ZMod m) - 1)) := by rw [hgZ]; ring
        _ = 0 := by rw [hdx]; simp⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    apply Units.ext
    have hval := congrArg Subtype.val hst
    have hval' : (s.1 : ZMod m) - 1 = (t.1 : ZMod m) - 1 := by
      simpa [f] using hval
    calc
      (s.1 : ZMod m) = ((s.1 : ZMod m) - 1) + 1 := by ring
      _ = ((t.1 : ZMod m) - 1) + 1 := by rw [hval']
      _ = (t.1 : ZMod m) := by ring
  have hcard := Fintype.card_le_of_injective f hf
  have hker : Fintype.card K = g := by
    dsimp [K]
    rw [zmod_mul_zero_card m g]
    exact Nat.gcd_eq_right (Nat.gcd_dvd_right d m)
  calc
    Fintype.card S ≤ Fintype.card K := hcard
    _ = g := hker
    _ = Nat.gcd (Nat.gcd h k) m := rfl

private lemma kloostermanScaleFiber_card_le (m h k : ℕ) [NeZero m]
    (s₀ : (ZMod m)ˣ) :
    Fintype.card
      {s : (ZMod m)ˣ //
        kloostermanScalePoint (h : ZMod m) (k : ZMod m) s =
          kloostermanScalePoint (h : ZMod m) (k : ZMod m) s₀} ≤
      Nat.gcd (Nat.gcd h k) m := by
  classical
  let Stab := {s : (ZMod m)ˣ //
    kloostermanScalePoint (h : ZMod m) (k : ZMod m) s = ((h : ZMod m), (k : ZMod m))}
  let f :
      {s : (ZMod m)ˣ //
        kloostermanScalePoint (h : ZMod m) (k : ZMod m) s =
          kloostermanScalePoint (h : ZMod m) (k : ZMod m) s₀} → Stab :=
    fun s =>
      ⟨s.1 * s₀⁻¹, by
        have hfirst : (h : ZMod m) * (s.1 : ZMod m) =
            (h : ZMod m) * (s₀ : ZMod m) := by
          simpa [kloostermanScalePoint] using congrArg Prod.fst s.2
        have hsecond : (k : ZMod m) * ((s.1⁻¹ : (ZMod m)ˣ) : ZMod m) =
            (k : ZMod m) * ((s₀⁻¹ : (ZMod m)ˣ) : ZMod m) := by
          simpa [kloostermanScalePoint] using congrArg Prod.snd s.2
        change ((h : ZMod m) * ((s.1 * s₀⁻¹ : (ZMod m)ˣ) : ZMod m),
            (k : ZMod m) * (((s.1 * s₀⁻¹)⁻¹ : (ZMod m)ˣ) : ZMod m)) =
          ((h : ZMod m), (k : ZMod m))
        apply Prod.ext
        · rw [Units.val_mul]
          have hs₀ : (s₀ : ZMod m) * ((s₀⁻¹ : (ZMod m)ˣ) : ZMod m) = 1 := by
            simpa using s₀.val_inv
          calc
            _ = (h : ZMod m) * (s.1 : ZMod m) * ((s₀⁻¹ : (ZMod m)ˣ) : ZMod m) := by ring
            _ = (h : ZMod m) * (s₀ : ZMod m) * ((s₀⁻¹ : (ZMod m)ˣ) : ZMod m) := by rw [hfirst]
            _ = (h : ZMod m) := by rw [mul_assoc, hs₀, mul_one]
        · let w : (ZMod m)ˣ := s.1 * s₀⁻¹
          have hu : w⁻¹ = s₀ * s.1⁻¹ := by dsimp [w]; group
          have hcastInv : ((w⁻¹ : (ZMod m)ˣ) : ZMod m) =
              (s₀ : ZMod m) * ((s.1⁻¹ : (ZMod m)ˣ) : ZMod m) := by
            calc
              _ = ((s₀ * s.1⁻¹ : (ZMod m)ˣ) : ZMod m) :=
                congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hu
              _ = _ := by simp [Units.val_mul]
          have hs₀ : ((s₀⁻¹ : (ZMod m)ˣ) : ZMod m) * (s₀ : ZMod m) = 1 := by
            simpa using s₀.inv_val
          have htarget : (k : ZMod m) *
              ((s₀ : ZMod m) * ((s.1⁻¹ : (ZMod m)ˣ) : ZMod m)) = k := by
            calc
              _ = (k : ZMod m) * ((s.1⁻¹ : (ZMod m)ˣ) : ZMod m) * (s₀ : ZMod m) := by ring
              _ = (k : ZMod m) * ((s₀⁻¹ : (ZMod m)ˣ) : ZMod m) * (s₀ : ZMod m) := by rw [hsecond]
              _ = (k : ZMod m) * (((s₀⁻¹ : (ZMod m)ˣ) : ZMod m) * (s₀ : ZMod m)) := by ring
              _ = (k : ZMod m) := by rw [hs₀]; simp
          change (k : ZMod m) * ((w⁻¹ : (ZMod m)ˣ) : ZMod m) = k
          rw [hcastInv]
          exact htarget⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    have hunit : s.1 * s₀⁻¹ = t.1 * s₀⁻¹ := congrArg Subtype.val hst
    calc
      s.1 = (s.1 * s₀⁻¹) * s₀ := by group
      _ = (t.1 * s₀⁻¹) * s₀ := by rw [hunit]
      _ = t.1 := by group
  have hcard := Fintype.card_le_of_injective f hf
  exact hcard.trans (kloostermanStabilizer_card_le m h k)

private lemma kloostermanScaleOrbit_card_lower (m h k : ℕ) [NeZero m] :
    Nat.totient m ≤ Nat.gcd (Nat.gcd h k) m *
      (Finset.univ.image
        (kloostermanScalePoint (h : ZMod m) (k : ZMod m))).card := by
  classical
  let U : Finset (ZMod m)ˣ := Finset.univ
  let ψ : (ZMod m)ˣ → ZMod m × ZMod m :=
    kloostermanScalePoint (h : ZMod m) (k : ZMod m)
  let O := U.image ψ
  have hmaps : (U : Set (ZMod m)ˣ).MapsTo ψ O := by
    intro s hs
    exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
  have hcard :
      U.card = ∑ y ∈ O, (U.filter fun s => ψ s = y).card := by
    simpa [U, O] using
      (Finset.card_eq_sum_card_fiberwise (f := ψ) (s := U) (t := O) hmaps)
  have hfiber : ∀ y ∈ O, (U.filter fun s => ψ s = y).card ≤
      Nat.gcd (Nat.gcd h k) m := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨s₀, hs₀, rfl⟩
    let T : Finset (ZMod m)ˣ := U.filter fun s => ψ s = ψ s₀
    letI : Fintype T := Fintype.ofFinset T (by intro s; rfl)
    let e : {s : (ZMod m)ˣ // ψ s = ψ s₀} ≃ ↥T :=
      { toFun := fun s => ⟨s.1, by
          change s.1 ∈ U.filter (fun s => ψ s = ψ s₀)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.2⟩⟩
        invFun := fun s => ⟨s.1, (Finset.mem_filter.mp s.2).2⟩
        left_inv := by intro s; apply Subtype.ext; rfl
        right_inv := by intro s; apply Subtype.ext; rfl }
    have hcardT : T.card =
        Fintype.card {s : (ZMod m)ˣ // ψ s = ψ s₀} := by
      rw [← Fintype.card_coe T]
      exact (Fintype.card_congr e).symm
    have hT := kloostermanScaleFiber_card_le m h k s₀
    exact hcardT.trans_le hT
  have hU : U.card = Nat.totient m := by
    simpa [U] using (ZMod.card_units_eq_totient m)
  calc
    Nat.totient m = U.card := hU.symm
    _ = ∑ y ∈ O, (U.filter fun s => ψ s = y).card := hcard
    _ ≤ ∑ y ∈ O, Nat.gcd (Nat.gcd h k) m := by
      apply Finset.sum_le_sum
      intro y hy
      exact hfiber y hy
    _ = Nat.gcd (Nat.gcd h k) m * O.card := by simp [Finset.sum_const, mul_comm]
    _ = _ := by rfl

theorem weak_kloosterman (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧
      ∀ m h k : ℕ, 1 ≤ m →
        ‖kloostermanSum m h k‖ ≤
          Cε * Real.rpow m (3 / 4 + ε) * Real.rpow (Nat.gcd (Nat.gcd h k) m) (1 / 4 : ℝ) := by
  classical
  obtain ⟨Cτ, hCτ, hdiv⟩ := divisor_card_rpow_bound ε hε
  obtain ⟨Cφ, hCφ, hphiRatio⟩ :=
    inverse_totient_rpow_bound (2 * ε) (by positivity)
  let A : ℝ := 2 * Cτ ^ 2 * Cφ
  let Cε : ℝ := Real.sqrt (Real.sqrt A)
  have hA : 0 < A := by dsimp [A]; positivity
  have hCε : 0 < Cε := by dsimp [Cε]; positivity
  have hCε4 : Cε ^ 4 = A := by
    dsimp [Cε]
    calc
      (Real.sqrt (Real.sqrt A)) ^ 4 =
          ((Real.sqrt (Real.sqrt A)) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt A) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg A)]
      _ = A := Real.sq_sqrt (le_of_lt hA)
  refine ⟨Cε, hCε, ?_⟩
  intro m h k hm
  have hmpos : 0 < m := by omega
  letI : NeZero m := ⟨by omega⟩
  let H : ZMod m := (h : ZMod m)
  let K : ZMod m := (k : ZMod m)
  let g : ℕ := Nat.gcd (Nat.gcd h k) m
  let O : Finset (ZMod m × ZMod m) :=
    Finset.univ.image (kloostermanScalePoint H K)
  let KS : ℂ := unitKloosterman m H K
  let Base : ℝ := ‖KS‖ ^ 4
  let τ : ℝ := (m.divisors.card : ℝ)
  have hOrbitNat : Nat.totient m ≤ g * O.card := by
    simpa [g, O, H, K] using kloostermanScaleOrbit_card_lower m h k
  have hOrbitReal : (Nat.totient m : ℝ) ≤ (g : ℝ) * (O.card : ℝ) := by
    exact_mod_cast hOrbitNat
  have hscaleSum :
      (∑ p ∈ O, ‖unitKloosterman m p.1 p.2‖ ^ 4) = (O.card : ℝ) * Base := by
    calc
      _ = ∑ p ∈ O, Base := by
        apply Finset.sum_congr rfl
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨s, hs, rfl⟩
        have hscale := unitKloosterman_scale m H K s
        have hnorm := congrArg (fun z : ℂ => ‖z‖ ^ 4) hscale
        simpa [Base, KS, H, K, kloostermanScalePoint] using hnorm
      _ = _ := by simp [Base, Finset.sum_const, mul_comm]
  have hglobal :
      (∑ p : ZMod m × ZMod m, ‖unitKloosterman m p.1 p.2‖ ^ 4) =
        (m : ℝ) ^ 2 * (unitQuadSolutions m).card := by
    calc
      _ = ∑ u : ZMod m, ∑ v : ZMod m, ‖unitKloosterman m u v‖ ^ 4 :=
        Fintype.sum_prod_type _
      _ = _ := unitKloosterman_global_fourthMoment m
  have hOrbitGlobal :
      (O.card : ℝ) * Base ≤ (m : ℝ) ^ 2 * (unitQuadSolutions m).card := by
    calc
      _ = ∑ p ∈ O, ‖unitKloosterman m p.1 p.2‖ ^ 4 := hscaleSum.symm
      _ ≤ ∑ p : ZMod m × ZMod m, ‖unitKloosterman m p.1 p.2‖ ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ O)
          (by intro p hp hnot; positivity)
      _ = _ := hglobal
  let Z₀ : Finset (ZMod m × ZMod m × ZMod m) :=
    Finset.univ.filter fun t => t.1 * t.2.1 * t.2.2 = 0
  have hZ₀ : Z₀.card =
      Fintype.card {t : ZMod m × ZMod m × ZMod m // t.1 * t.2.1 * t.2.2 = 0} := by
    simpa [Z₀] using
      (Fintype.card_subtype
        (fun t : ZMod m × ZMod m × ZMod m => t.1 * t.2.1 * t.2.2 = 0)).symm
  have hquadNat : (unitQuadSolutions m).card ≤
      2 * (m ^ 2 * (m.divisors.card) ^ 2) := by
    calc
      _ ≤ 2 * Z₀.card := by simpa [Z₀] using unitQuadSolutions_card_le m
      _ = 2 * Fintype.card
          {t : ZMod m × ZMod m × ZMod m // t.1 * t.2.1 * t.2.2 = 0} := by rw [hZ₀]
      _ ≤ 2 * (m ^ 2 * (m.divisors.card) ^ 2) :=
        Nat.mul_le_mul_left 2 (zero_product_zmod_card_le m)
  have hquadReal : ((unitQuadSolutions m).card : ℝ) ≤
      2 * ((m : ℝ) ^ 2 * τ ^ 2) := by
    dsimp [τ]
    exact_mod_cast hquadNat
  have hglobalBound :
      (m : ℝ) ^ 2 * (unitQuadSolutions m).card ≤
        2 * (m : ℝ) ^ 4 * τ ^ 2 := by
    calc
      _ ≤ (m : ℝ) ^ 2 * (2 * ((m : ℝ) ^ 2 * τ ^ 2)) :=
        mul_le_mul_of_nonneg_left hquadReal (sq_nonneg (m : ℝ))
      _ = _ := by ring
  have hphiPos : 0 < (Nat.totient m : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hmpos)
  have hBasePhi :
      (Nat.totient m : ℝ) * Base ≤ (g : ℝ) *
        (2 * (m : ℝ) ^ 4 * τ ^ 2) := by
    calc
      _ ≤ ((g : ℝ) * (O.card : ℝ)) * Base :=
        mul_le_mul_of_nonneg_right hOrbitReal (by positivity)
      _ = (g : ℝ) * ((O.card : ℝ) * Base) := by ring
      _ ≤ (g : ℝ) * ((m : ℝ) ^ 2 * (unitQuadSolutions m).card) :=
        mul_le_mul_of_nonneg_left hOrbitGlobal (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hglobalBound (by positivity)
  have hBaseDiv : Base ≤
      ((g : ℝ) * (2 * (m : ℝ) ^ 4 * τ ^ 2)) / (Nat.totient m : ℝ) :=
    (le_div_iff₀ hphiPos).2 (by
      calc
        Base * (Nat.totient m : ℝ) = (Nat.totient m : ℝ) * Base := by ring
        _ ≤ _ := hBasePhi)
  have hτ : τ ≤ Cτ * (m : ℝ) ^ ε := by
    dsimp [τ]
    exact hdiv m hm
  have hτSq : τ ^ 2 ≤ Cτ ^ 2 * (m : ℝ) ^ (2 * ε) := by
    have hpow : ((m : ℝ) ^ ε) ^ 2 = (m : ℝ) ^ (2 * ε) := by
      rw [← Real.rpow_mul_natCast (by positivity) ε 2]
      congr 1
      ring
    have hleft : 0 ≤ τ := Nat.cast_nonneg _
    have hright : 0 ≤ Cτ * (m : ℝ) ^ ε := by positivity
    calc
      τ ^ 2 ≤ (Cτ * (m : ℝ) ^ ε) ^ 2 := by nlinarith [hτ]
      _ = Cτ ^ 2 * (m : ℝ) ^ (2 * ε) := by rw [mul_pow, hpow]
  have hφratio : (m : ℝ) / (Nat.totient m : ℝ) ≤
      Cφ * (m : ℝ) ^ (2 * ε) := hphiRatio m (by omega)
  have hfrac :
      ((g : ℝ) * (2 * (m : ℝ) ^ 4 * τ ^ 2)) / (Nat.totient m : ℝ) =
        2 * (g : ℝ) * (m : ℝ) ^ 3 * τ ^ 2 *
          ((m : ℝ) / (Nat.totient m : ℝ)) := by
    field_simp [hphiPos.ne', (show (m : ℝ) ≠ 0 by positivity)]
  have hBaseRaw : Base ≤
      2 * (g : ℝ) * (m : ℝ) ^ 3 * τ ^ 2 *
        ((m : ℝ) / (Nat.totient m : ℝ)) := by
    rw [hfrac] at hBaseDiv
    exact hBaseDiv
  have hpow₂ : (m : ℝ) ^ (2 * ε) * (m : ℝ) ^ (2 * ε) =
      (m : ℝ) ^ (4 * ε) := by
    rw [← Real.rpow_add (by positivity) (2 * ε) (2 * ε)]
    congr 1
    ring
  have hpow₃ : (m : ℝ) ^ 3 * (m : ℝ) ^ (4 * ε) =
      (m : ℝ) ^ (3 + 4 * ε) := by
    have hmposR : 0 < (m : ℝ) := by positivity
    have hrpowNat : Real.rpow (m : ℝ) (3 : ℝ) = (m : ℝ) ^ 3 :=
      Real.rpow_natCast _ _
    rw [← hrpowNat]
    change Real.rpow (m : ℝ) (3 : ℝ) * Real.rpow (m : ℝ) (4 * ε) =
      Real.rpow (m : ℝ) (3 + 4 * ε)
    exact (Real.rpow_add hmposR 3 (4 * ε)).symm
  have hfinal : Base ≤ A * (g : ℝ) * (m : ℝ) ^ (3 + 4 * ε) := by
    have hmult :
        τ ^ 2 * ((m : ℝ) / (Nat.totient m : ℝ)) ≤
          (Cτ ^ 2 * (m : ℝ) ^ (2 * ε)) * (Cφ * (m : ℝ) ^ (2 * ε)) :=
      mul_le_mul hτSq hφratio (by positivity) (by positivity)
    have hBaseRaw' : Base ≤
        (2 * (g : ℝ) * (m : ℝ) ^ 3) *
          (τ ^ 2 * ((m : ℝ) / (Nat.totient m : ℝ))) := by
      calc
        Base ≤ 2 * (g : ℝ) * (m : ℝ) ^ 3 * τ ^ 2 *
            ((m : ℝ) / (Nat.totient m : ℝ)) := hBaseRaw
        _ = _ := by ring
    calc
      _ ≤ (2 * (g : ℝ) * (m : ℝ) ^ 3) *
          ((Cτ ^ 2 * (m : ℝ) ^ (2 * ε)) * (Cφ * (m : ℝ) ^ (2 * ε))) := by
        calc
          Base ≤ (2 * (g : ℝ) * (m : ℝ) ^ 3) *
              (τ ^ 2 * ((m : ℝ) / (Nat.totient m : ℝ))) := hBaseRaw'
          _ ≤ (2 * (g : ℝ) * (m : ℝ) ^ 3) *
              ((Cτ ^ 2 * (m : ℝ) ^ (2 * ε)) * (Cφ * (m : ℝ) ^ (2 * ε))) := by
            exact mul_le_mul_of_nonneg_left hmult (by positivity)
          _ = _ := by ring
      _ = 2 * Cτ ^ 2 * Cφ * (g : ℝ) * (m : ℝ) ^ 3 *
            ((m : ℝ) ^ (2 * ε) * (m : ℝ) ^ (2 * ε)) := by ring
      _ = A * (g : ℝ) * (m : ℝ) ^ 3 * (m : ℝ) ^ (4 * ε) := by
        rw [hpow₂]
      _ = A * (g : ℝ) * (m : ℝ) ^ (3 + 4 * ε) := by
        calc
          _ = A * (g : ℝ) * ((m : ℝ) ^ 3 * (m : ℝ) ^ (4 * ε)) := by ring
          _ = _ := by rw [hpow₃]
  have hMpow : (Real.rpow (m : ℝ) (3 / 4 + ε)) ^ 4 =
      Real.rpow (m : ℝ) (3 + 4 * ε) := by
    calc
      _ = Real.rpow (m : ℝ) (3 / 4 + ε) ^ (4 : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = Real.rpow (m : ℝ) ((3 / 4 + ε) * 4) :=
        (Real.rpow_mul (by positivity) (3 / 4 + ε) 4).symm
      _ = Real.rpow (m : ℝ) (3 + 4 * ε) := by congr 1 <;> ring
  have hGpow : (Real.rpow (g : ℝ) (1 / 4 : ℝ)) ^ 4 = (g : ℝ) := by
    calc
      _ = Real.rpow (g : ℝ) (1 / 4 : ℝ) ^ (4 : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = Real.rpow (g : ℝ) ((1 / 4 : ℝ) * 4) :=
        (Real.rpow_mul (Nat.cast_nonneg g) (1 / 4 : ℝ) 4).symm
      _ = (g : ℝ) := by norm_num [Real.rpow_one]
  let RHS : ℝ := Cε * Real.rpow (m : ℝ) (3 / 4 + ε) *
    Real.rpow (g : ℝ) (1 / 4 : ℝ)
  have hRHS4 : RHS ^ 4 =
      A * (g : ℝ) * Real.rpow (m : ℝ) (3 + 4 * ε) := by
    change (Cε * Real.rpow (m : ℝ) (3 / 4 + ε) *
      Real.rpow (g : ℝ) (1 / 4 : ℝ)) ^ 4 =
        A * (g : ℝ) * Real.rpow (m : ℝ) (3 + 4 * ε)
    calc
      _ = Cε ^ 4 * (Real.rpow (m : ℝ) (3 / 4 + ε)) ^ 4 *
          (Real.rpow (g : ℝ) (1 / 4 : ℝ)) ^ 4 := by ring
      _ = _ := by rw [hCε4, hMpow, hGpow]; ring
  have hpowBound : ‖KS‖ ^ 4 ≤ RHS ^ 4 := by
    dsimp [Base] at hfinal
    calc
      _ ≤ A * (g : ℝ) * (m : ℝ) ^ (3 + 4 * ε) := hfinal
      _ = _ := hRHS4.symm
  have hRHSnonneg : 0 ≤ RHS := by dsimp [RHS]; positivity
  have hbound := (pow_le_pow_iff_left₀ (norm_nonneg KS) hRHSnonneg
      (by decide : 4 ≠ 0)).mp hpowBound
  have hsumEq : kloostermanSum m h k = KS := by
    simpa [KS, H, K, unitKloosterman] using (kloostermanSum_eq_unit_sum m h k)
  rw [hsumEq]
  simpa [RHS, g] using hbound

lemma pd1c_physicalState_finite
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (H' Hm Hn : ℝ) :
    Finite (PhysicalState x K a H' Hm Hn) :=
  Finite.of_injective endpointStateCoordinates endpointStateCoordinates_injective

lemma pd1c_residue_indicator (m : ℕ) [NeZero m] (hm : 0 < m) (u v : ZMod m) :
    (if u = v then (1 : ℂ) else 0) =
      (m : ℂ)⁻¹ * ∑ j : ZMod m, ZMod.stdAddChar (j * (u - v)) := by
  letI : NeZero m := ⟨hm.ne'⟩
  have horth := stdAddChar_orthogonality m (u - v)
  simp only [mul_comm (u - v)] at horth
  rw [horth]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  by_cases h : u = v
  · simp [h, hmC]
  · simp [h, sub_ne_zero.mpr h]

lemma pd1c_residue_fourier_expansion {ι : Type*} (s : Finset ι)
    (m : ℕ) [NeZero m] (hm : 0 < m) (r : ι → ZMod m) (a : ZMod m) (f : ι → ℂ) :
    (∑ i ∈ s, if r i = a then f i else 0) =
      (m : ℂ)⁻¹ * ∑ j : ZMod m,
        ∑ i ∈ s, ZMod.stdAddChar (j * (r i - a)) * f i := by
  letI : NeZero m := ⟨hm.ne'⟩
  calc
    _ = ∑ i ∈ s, (if r i = a then (1 : ℂ) else 0) * f i := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : r i = a <;> simp [h]
    _ = ∑ i ∈ s, ((m : ℂ)⁻¹ *
        ∑ j : ZMod m, ZMod.stdAddChar (j * (r i - a))) * f i := by
      simp_rw [pd1c_residue_indicator m hm]
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma pd1c_groupLabelProduct_pos
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn) : 0 < groupLabelProduct P :=
  groupLabelProduct_pos P

lemma pd1c_groupLabelProduct_dvd_first
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn) (hSq : Squarefree (groupLabelProduct P)) :
    groupLabelProduct P ∣ P.first := groupLabelProduct_dvd_first P hSq

lemma pd1c_endpointG_pointwise_general
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (hx : 2 ≤ x) (hMin : family.xMin ≤ x)
    (beta : ℕ → ℂ) (hbeta : ∀ n ∈ dyadicIntegers Hn, ‖beta n‖ ≤ Real.rpow (Real.log x) C)
    (P : PhysicalState x K a H' Hm Hn) :
    ‖endpointG x K a family beta P‖ ≤ Real.rpow (Real.log x) (2 * C) := by
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hα : ‖family.alpha x (P.first / groupLabelProduct P)‖ ≤ Real.rpow (Real.log x) C := by
    by_cases hz : family.alpha x (P.first / groupLabelProduct P) = 0
    · simpa [hz] using Real.rpow_nonneg hlog.le C
    · exact family.coefficient_bound x hMin _ (family.rough_support x hMin _ hz).1
  have hβ := hbeta P.second (endpoint_second_mem_dyadic P)
  by_cases hSq : Squarefree (groupLabelProduct P)
  · simp only [endpointG, hSq, ite_true, norm_mul, norm_star]
    calc
      _ ≤ Real.rpow (Real.log x) C * Real.rpow (Real.log x) C :=
        mul_le_mul hα hβ (norm_nonneg _) (Real.rpow_nonneg hlog.le _)
      _ = _ := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add hlog]
        congr 1
        ring
  · simpa [endpointG, hSq] using Real.rpow_nonneg hlog.le (2 * C)

lemma pd1c_rootCountingInputs_exists : Nonempty pd1c_RootCountingInputs := by
  obtain ⟨CK, hCK, hK⟩ := weak_kloosterman (1 / 100) (by norm_num)
  obtain ⟨CT, hCT, hτ⟩ := divisor_card_rpow_bound (1 / 100) (by norm_num)
  refine ⟨⟨CK, CT, hCK, hCT, ?_, hτ⟩⟩
  intro m hi Ft H K
  letI : NeZero m := hi
  letI : Fintype (ZMod m)ˣ := Ft
  have hm : 1 ≤ m := NeZero.pos m
  have heq := kloostermanSum_eq_unit_sum m H.val K.val
  simp only [ZMod.natCast_zmod_val, ZMod.inv_coe_unit] at heq
  change kloostermanSum m H.val K.val = @pd1c_rootKSum m hi Ft H K at heq
  rw [← heq]
  simpa only [Real.rpow_eq_pow] using hK m H.val K.val hm

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
  obtain ⟨inputs⟩ := pd1c_rootCountingInputs_exists
  exact pd1c_root_residue_from_inputs inputs δ C_K hδ hCK

end ArtinPrimitiveRoots.TypeII.PD
