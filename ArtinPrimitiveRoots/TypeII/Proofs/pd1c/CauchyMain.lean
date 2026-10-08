import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyAsymptotic

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII
set_option maxHeartbeats 1000000

theorem pd1c_cauchy_decomposition
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
  intro A hA
  obtain ⟨Bcount, hBcount, hCount⟩ := pd1c_geometric_count_bound q_d hqd₀ hqd₁
  obtain ⟨xMass, hxMass, hMass⟩ := pd1c_bandMass_uniform K a ha
  obtain ⟨xBands, hxBands, hBands⟩ := pd1c_eventual_bands_separated K a ha
  obtain ⟨CDiv, xDiv, hCDiv, hxDiv, hDiv⟩ := pd1c_progression_divisor_uniform c₁ c₂ K hc₁ hc₂
  obtain ⟨xSmall, hxSmall, hSmall⟩ := pd1c_dyadic_small_relative_to_X K c₁ hc₁
  obtain ⟨xSquare, hxSquare, hSquare⟩ := pd1c_marked_square_small_eventual δ hδ K a ha
  obtain ⟨xRange, hxRange, hRange⟩ := pd1c_tuple_log_range_eventual K a ha
  obtain ⟨Lerror₁, hLerror₁, hError₁⟩ := pd1c_cauchy_logPower_expDecay A (2 * C) 1 (by norm_num)
  obtain ⟨Lerror₂, hLerror₂, hError₂⟩ := pd1c_cauchy_logPower_expDecay A (4 * C + 3) 1 (by norm_num)
  let v := Real.log 2 / 2
  let BW := (Bcount / v) ^ K
  let Wmax := v⁻¹ ^ K
  let Etail := 2 * K * Real.log 2
  let C₁ := 9 * BW * Etail
  let C₂ := 16 * Wmax ^ 2 * CDiv * Etail
  let C_A := max C₁ C₂ + 1
  let Cscale := (((K + 1 : ℕ) : ℝ) / Real.log 2 + 1) + ((K + 1 : ℕ) : ℝ)
  let x₀ := max xMass (max xBands (max xDiv (max xSmall
    (max xSquare (max xRange (Real.exp (max Lerror₁ Lerror₂)))))))
  have hv : 0 < v := by dsimp [v]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hBW : 0 ≤ BW := by dsimp [BW]; positivity
  have hWmax : 0 ≤ Wmax := by dsimp [Wmax]; positivity
  have hEtail : 0 ≤ Etail := by dsimp [Etail]; positivity
  have hCA : 0 < C_A := by dsimp [C_A, C₁]; positivity
  have hCscale : 0 < Cscale := by dsimp [Cscale]; positivity
  refine ⟨C_A, Cscale, 5, CDiv, x₀, hCA, hCscale, by norm_num, hCDiv,
    hxMass.trans (le_max_left _ _), ?_⟩
  intro family hCancel x hx hMin eta hSmooth hEta hEta₀ hPartition beta hBetaSupport hBeta F hF
  have hxM : xMass ≤ x := (le_max_left _ _).trans hx
  have hxB : xBands ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxD : xDiv ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hxSm : xSmall ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx)))
  have hxSq : xSquare ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))))
  have hxR : xRange ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx)))))
  have hxErr : Real.exp (max Lerror₁ Lerror₂) ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx)))))
  have hx2 : 2 ≤ x := hxMass.trans hxM
  have hxpos : 0 < x := by linarith
  have hScales := family.scales x hMin
  let X := family.Hm x * family.Hn x
  let L := Real.log x
  let T := L ^ C
  obtain ⟨hL1, hX1, hYs⟩ := hSmall x hxSm X hScales.2.2.1
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hSq := hSquare x hxSq
  have hHm : 2 ≤ family.Hm x := hSq.1.trans hScales.1
  have hHn : 2 ≤ family.Hn x := hSq.1.trans hScales.2.1
  have hAlpha : ∀ m ∈ familyTerms family x, ‖family.alpha x m‖ ≤ T :=
    fun m hm => family.coefficient_bound x hMin m (Finset.mem_filter.mp hm).2
  have hPos : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), 0 < m * n - 1 := by
    intro m hm n hn
    have hm2 : 2 ≤ m := by
      exact_mod_cast hHm.trans (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2.1
    have hn2 : 2 ≤ n := by exact_mod_cast hHn.trans (Finset.mem_filter.mp hn).2.1
    have hp : 4 ≤ m * n := by nlinarith
    omega
  have hPos1 : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ m * n := by
    intro m hm n hn
    have h := hPos m hm n hn
    omega
  have hSep := (hBands x hxB).1
  have hMv : ∀ i : Fin K, v ≤ bandMass x (a i) := fun i => (hMass x hxM i).1
  have hMnonneg : ∀ i : Fin K, 0 ≤ bandMass x (a i) := fun i => hv.le.trans (hMv i)
  have hWt : ∀ z, markedWeight x K a q_d z ≤ BW :=
    fun z => pd1c_markedWeight_bound hqd₀.le hv hBcount.le hCount hMv z
  have hTail : (∑ i : Fin K, ∑ p ∈ primeBand x (a i), (1 / (p : ℝ)) ^ 2) ≤
      Etail * Real.exp (-L ^ (1 / 10 : ℝ)) :=
    pd1c_all_band_square_tail ha hL1 (fun i => (hMass x hxM i).2)
  have hNormNonneg : 0 ≤ ∏ i : Fin K, (bandMass x (a i))⁻¹ :=
    Finset.prod_nonneg fun i hi => inv_nonneg.mpr (hMnonneg i)
  have hNormMax : (∏ i : Fin K, (bandMass x (a i))⁻¹) ≤ Wmax := by
    calc
      _ ≤ ∏ i : Fin K, v⁻¹ := Finset.prod_le_prod₀ (fun i hi => inv_nonneg.mpr (hMnonneg i))
        (fun i hi => by simpa only [one_div] using one_div_le_one_div_of_le hv (hMv i))
      _ = _ := by simp [Wmax]
  have hNormSq := pow_le_pow_left₀ hNormNonneg hNormMax 2
  have hErrL : max Lerror₁ Lerror₂ ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hxErr
  have hErr₁ : L ^ (2 * C) * Real.exp (-L ^ (1 / 10 : ℝ)) ≤ L ^ (-A) := by
    simpa only [Real.rpow_eq_pow, neg_one_mul] using hError₁ L ((le_max_left _ _).trans hErrL)
  have hErr₂ : L ^ (4 * C + 3) * Real.exp (-L ^ (1 / 10 : ℝ)) ≤ L ^ (-A) := by
    simpa only [Real.rpow_eq_pow, neg_one_mul] using hError₂ L ((le_max_right _ _).trans hErrL)
  have hTtwo : T ^ 2 = L ^ (2 * C) := by
    dsimp [T]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le]
    congr 1
    ring
  have hTfour : T ^ 4 * L ^ (3 : ℝ) = L ^ (4 * C + 3) := by
    dsimp [T]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le, ← Real.rpow_add hLp]
    congr 1
    ring
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pd1c_dyadicPiece_sum_eq_replacement family beta F eta q_d hF
      (by linarith) (by linarith) hEta hPartition hLp.le hPos (hRange x hxR)]
    have hb := pd1c_replacement_error_bound family beta F hqd₀.le hqd₁.le hT hBW hMnonneg hSep hWt hAlpha hBeta hF.1
      (by linarith) (by linarith) hPos1 (fun i p hp => (hSq.2 i p hp).trans hScales.2.1)
    calc
      _ ≤ 9 * BW * T ^ 2 * X * (∑ i : Fin K, ∑ p ∈ primeBand x (a i), (1 / (p : ℝ)) ^ 2) := hb
      _ ≤ 9 * BW * T ^ 2 * X * (Etail * Real.exp (-L ^ (1 / 10 : ℝ))) :=
        mul_le_mul_of_nonneg_left hTail (by positivity)
      _ = C₁ * X * (L ^ (2 * C) * Real.exp (-L ^ (1 / 10 : ℝ))) := by rw [hTtwo]; dsimp [C₁]; ring
      _ ≤ C₁ * X * L ^ (-A) := mul_le_mul_of_nonneg_left hErr₁ (by dsimp [C₁]; positivity)
      _ ≤ C_A * X * L ^ (-A) := by
        have hC₁ : C₁ ≤ C_A := by dsimp [C_A]; linarith [le_max_left C₁ C₂]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ (by positivity)) (by positivity)
  · intro Y hY
    obtain ⟨hYp, hYX⟩ := hYs Y hY
    have hYleX : Y ≤ X := hYX.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (1 / 4 : ℝ) ≤ 1))
    have hXY : 1 ≤ X / Y := (le_div_iff₀ hYp).mpr (by simpa using hYleX)
    have hDV : ∀ l : ℕ, (l : ℝ) ≤ 4 * Y →
        (∑ h ∈ Finset.range (⌊4 * X / Y⌋₊ + 1), (tau (1 + l * h) : ℝ) ^ 2) ≤ CDiv * (X / Y) * L ^ (3 : ℝ) := by
      intro l hl
      simpa only [L, Real.rpow_ofNat] using hDiv x hxD X hScales.2.2.1 hScales.2.2.2 Y hY l hl
    refine ⟨pd1c_cauchySquare_nonneg x K a Y family beta eta,
      pd1c_dyadicCauchyPiece_norm_bound family beta F eta q_d (by linarith) (by linarith) hYp hXY hEta hqd₀.le hqd₁.le hF.1, ?_⟩
    have hb := pd1c_coprime_error_bound family beta eta (by linarith) (by linarith) hYp hT hCDiv.le hLp.le
      hEta hEta₀ (pd1c_partition_eta_le_one eta hEta hEta₀ hPartition) hSep hAlpha hBeta hPos1 hDV
    calc
      _ ≤ 16 * (∏ i : Fin K, (bandMass x (a i))⁻¹) ^ 2 * CDiv * T ^ 4 * X * Y * L ^ (3 : ℝ) *
          (∑ i : Fin K, ∑ p ∈ primeBand x (a i), (1 / (p : ℝ)) ^ 2) := hb
      _ ≤ 16 * Wmax ^ 2 * CDiv * T ^ 4 * X * Y * L ^ (3 : ℝ) *
          (Etail * Real.exp (-L ^ (1 / 10 : ℝ))) := by
        apply mul_le_mul _ hTail (by positivity) (by positivity)
        gcongr
      _ = C₂ * X * Y * (L ^ (4 * C + 3) * Real.exp (-L ^ (1 / 10 : ℝ))) := by
        dsimp [C₂]
        rw [← hTfour]
        ring
      _ ≤ C₂ * X * Y * L ^ (-A) := mul_le_mul_of_nonneg_left hErr₂ (by dsimp [C₂]; positivity)
      _ ≤ C_A * X * Y * L ^ (-A) := by
        have hC₂ : C₂ ≤ C_A := by dsimp [C_A]; linarith [le_max_right C₁ C₂]
        gcongr
  · intro ta tb hta htb hc m n r s hmn hrs
    exact pd1c_cauchy_arithmetic hta htb hc hmn hrs
  · intro Y hY l hlo hhi
    have hYp := (hYs Y hY).1
    have hle : ⌊X / Y⌋₊ ≤ ⌊4 * X / Y⌋₊ := Nat.floor_le_floor (by
      have hXpos : 0 ≤ X := by linarith
      have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 4 by norm_num) hXpos
      exact div_le_div_of_nonneg_right (by simpa using h) hYp.le)
    have hSub : Finset.range (⌊X / Y⌋₊ + 1) ⊆ Finset.range (⌊4 * X / Y⌋₊ + 1) :=
      Finset.range_mono (by omega)
    have hStrong := hDiv x hxD X hScales.2.2.1 hScales.2.2.2 Y hY l (by linarith)
    exact (Finset.sum_le_sum_of_subset_of_nonneg hSub (fun h hh hn => sq_nonneg _)).trans
      (by simpa only [X, Real.rpow_eq_pow, Real.rpow_ofNat] using hStrong)
  · have hCard := pd1c_dyadicScales_card_bound K hL1
    refine hCard.trans ?_
    apply mul_le_mul_of_nonneg_right _ hLp.le
    dsimp [Cscale]
    linarith [show (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) by positivity, show (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) / Real.log 2 + 1 by positivity]
  · intro Y hY
    obtain ⟨hl, hu⟩ := pd1c_dyadicScale_log_bounds hY
    refine ⟨hl, hu.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLp.le _)
    dsimp [Cscale]
    linarith [show (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) by positivity, show (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) / Real.log 2 + 1 by positivity]

end ArtinPrimitiveRoots.TypeII.PD
