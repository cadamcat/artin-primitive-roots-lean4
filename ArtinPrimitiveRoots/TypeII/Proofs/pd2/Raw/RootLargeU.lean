import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootMainTerm

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_rootCountConstant (inputs : pd2a_RootCountingInputs) : ℝ :=
  1536 * (16 * (40804 * inputs.CK * inputs.CT) + 32) + 15 * pd2a_rootAverageConstant

lemma pd2a_rootCountConstant_pos (inputs : pd2a_RootCountingInputs) : 0 < pd2a_rootCountConstant inputs := by
  have hCK := inputs.CK_pos
  have hCT := inputs.CT_pos
  have hA := pd2a_rootAverageConstant_pos
  dsimp [pd2a_rootCountConstant]
  positivity

lemma pd2a_rootResidueCount_small_first (inputs : pd2a_RootCountingInputs)
    (U V : ℝ) (hU : 2 ≤ U) (hUV : U ≤ V) (S : ℕ) (hS : 0 < S) (hSq : Squarefree S)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hdet : Matrix.det g₀ = 1)
    (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ)
    (hl₁ : 1 ≤ l₁) (hlr₁ : l₁ ≤ r₁) (hr₁ : r₁ ≤ 16)
    (hl₂ : 1 ≤ l₂) (hlr₂ : l₂ ≤ r₂) (hr₂ : r₂ ≤ 16)
    (hl₃ : 0 ≤ l₃) (hlr₃ : l₃ ≤ r₃) (hr₃ : r₃ ≤ 1) :
    |rootResidueCount U V S g₀ l₁ r₁ l₂ r₂ l₃ r₃ -
      U * V * (r₁ - l₁) * (r₂ - l₂) * (r₃ - l₃) / ((Real.pi ^ 2 / 6) * (sl2Card S hS : ℝ))| ≤
      pd2a_rootCountConstant inputs * U * V *
        (U ^ (-(1 / 100 : ℝ)) * (S : ℝ) ^ 2 + Real.log (2 * U) / U) := by
  let I := pd2a_natClosedInterval (l₁ * U) (r₁ * U)
  let M := V * (r₂ - l₂) * (r₃ - l₃) / (S : ℝ) ^ 2
  let DF := 16 * (40804 * inputs.CK * inputs.CT) + 32
  let B := DF * 16 * U ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ) * (V / U + 5)
  have hUp : 0 < U := by linarith
  have hVp : 0 < V := by linarith
  have hV1 : 1 ≤ V := by linarith
  have hSp : 0 < (S : ℝ) := by exact_mod_cast hS
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hU1 : 1 ≤ U := by linarith
  have hDF : 0 < DF := by
    have hCK := inputs.CK_pos
    have hCT := inputs.CT_pos
    dsimp [DF]
    positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBounds : ∀ u ∈ I, U ≤ (u : ℝ) ∧ (u : ℝ) ≤ 16 * U := by
    intro u hu
    obtain ⟨hlo, hhi⟩ := (pd2a_natClosedInterval_mem _ _ (by nlinarith : 0 ≤ r₁ * U) u).mp hu
    constructor <;> nlinarith
  have hCard : (I.card : ℝ) ≤ 16 * U := by
    rw [pd2a_natClosedInterval_card]
    have herr := pd2a_intervalLength_error (l₁ * U) (r₁ * U) (by positivity)
      (mul_le_mul_of_nonneg_right hlr₁ hUp.le)
    have hwidth : r₁ - l₁ ≤ 15 := by linarith
    have hh := (abs_le.mp herr).2
    nlinarith [mul_le_mul_of_nonneg_right hwidth hUp.le]
  have hpoint : ∀ u ∈ I,
      |(if (u : ZMod S) = g₀ 0 0 then pd2a_fixedRootCount u V S g₀ l₂ r₂ l₃ r₃ else 0) -
        M * (if (u : ZMod S) = g₀ 0 0 then pd2a_rootEulerFactor u S else 0)| ≤ B := by
    intro u huI
    obtain ⟨hulo, huhi⟩ := hBounds u huI
    have hur : 0 < (u : ℝ) := hUp.trans_le hulo
    have hup : 0 < u := by exact_mod_cast hur
    letI : NeZero (u * S) := ⟨(mul_pos hup hS).ne'⟩
    by_cases hu₀ : (u : ZMod S) = g₀ 0 0
    · rw [if_pos hu₀, if_pos hu₀]
      have hMain : M * pd2a_rootEulerFactor u S = V * (r₂ - l₂) * (r₃ - l₃) * pd2a_rootEulerFactor u S / (S : ℝ) ^ 2 := by dsimp [M]; ring
      rw [hMain]
      have he := pd2a_fixedRootCount_estimate inputs u V S hup hV1 hS hSq g₀ hdet hu₀ l₂ r₂ l₃ r₃ hl₂ hlr₂ hr₂ hl₃ hlr₃ hr₃
      have hpow : (u : ℝ) ^ (99 / 100 : ℝ) ≤ 16 * U ^ (99 / 100 : ℝ) := by
        calc
          _ ≤ (16 * U) ^ (99 / 100 : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg u) huhi (by norm_num)
          _ = (16 : ℝ) ^ (99 / 100 : ℝ) * U ^ (99 / 100 : ℝ) := Real.mul_rpow (by norm_num) hUp.le
          _ ≤ _ := by
            have h16 : (16 : ℝ) ^ (99 / 100 : ℝ) ≤ 16 := by
              simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16) (by norm_num : (99 / 100 : ℝ) ≤ 1)
            exact mul_le_mul_of_nonneg_right h16 (Real.rpow_nonneg hUp.le _)
      have hRatio : V / (u : ℝ) ≤ V / U := div_le_div_of_nonneg_left hVp.le hUp hulo
      refine he.trans ?_
      have hCoef : DF * (u : ℝ) ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ) ≤
          DF * (16 * U ^ (99 / 100 : ℝ)) * (S : ℝ) ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hDF.le) (by positivity)
      have hb := mul_le_mul hCoef (add_le_add_right hRatio 5) (by positivity) (by positivity)
      simpa only [B, DF, mul_assoc, Real.rpow_ofNat, add_comm] using hb
    · simp only [hu₀, ite_false, mul_zero, sub_self, abs_zero]
      exact hB
  have hFinite : |rootResidueCount U V S g₀ l₁ r₁ l₂ r₂ l₃ r₃ -
      M * (∑ u ∈ I, if (u : ZMod S) = g₀ 0 0 then pd2a_rootEulerFactor u S else 0)| ≤
        1536 * DF * U * V * U ^ (-(1 / 100 : ℝ)) * (S : ℝ) ^ 2 := by
    rw [pd2a_rootResidueCount_rows U V hUp hVp S g₀ l₁ r₁ l₂ r₂ l₃ r₃ (by linarith) hlr₁ (by linarith) hlr₂,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ u ∈ I, |(if (u : ZMod S) = g₀ 0 0 then pd2a_fixedRootCount u V S g₀ l₂ r₂ l₃ r₃ else 0) -
        M * (if (u : ZMod S) = g₀ 0 0 then pd2a_rootEulerFactor u S else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ I, B := Finset.sum_le_sum fun u hu => hpoint u hu
      _ = (I.card : ℝ) * B := by simp
      _ ≤ 16 * U * B := mul_le_mul_of_nonneg_right hCard hB
      _ ≤ 16 * U * (DF * 16 * U ^ (99 / 100 : ℝ) * (S : ℝ) ^ (2 : ℝ) * (6 * (V / U))) := by
        have hVU : 1 ≤ V / U := (le_div_iff₀ hUp).mpr (by simpa using hUV)
        dsimp [B]
        gcongr
        linarith
      _ = _ := by
        have hUP : U * U ^ (-(1 / 100 : ℝ)) = U ^ (99 / 100 : ℝ) := by
          calc
            _ = U ^ (1 : ℝ) * U ^ (-(1 / 100 : ℝ)) := by rw [Real.rpow_one]
            _ = U ^ ((1 : ℝ) + -(1 / 100 : ℝ)) := (Real.rpow_add hUp _ _).symm
            _ = _ := by congr 1; norm_num
        rw [← hUP]
        simp only [Real.rpow_ofNat]
        field_simp <;> ring
  have hMMax : M ≤ 15 * V := by
    have hwidth : r₂ - l₂ ≤ 15 := by linarith
    have hbr : 0 ≤ r₃ - l₃ := by linarith
    have hbr1 : r₃ - l₃ ≤ 1 := by linarith
    have hTop : V * (r₂ - l₂) * (r₃ - l₃) ≤ 15 * V := by
      have h1 := mul_le_mul_of_nonneg_right hwidth hVp.le
      have h2 := mul_le_mul_of_nonneg_left hbr1 (mul_nonneg hVp.le (sub_nonneg.mpr hlr₂))
      nlinarith
    have hS2 : 1 ≤ (S : ℝ) ^ 2 := by nlinarith
    have hDiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ V * (r₂ - l₂) * (r₃ - l₃))
      (by norm_num : (0 : ℝ) < 1) hS2
    have hDiv' : M ≤ V * (r₂ - l₂) * (r₃ - l₃) := by simpa only [div_one, M] using hDiv
    exact hDiv'.trans hTop
  have hMain := pd2a_root_main_term_identity U V S hS hSq (r₁ - l₁) (r₂ - l₂) (r₃ - l₃)
  have hAvg := pd2a_rootEuler_scaled_average U hU S hS (g₀ 0 0) l₁ r₁ hl₁ hlr₁ hr₁
  have hAverageError : |M * (∑ u ∈ I, if (u : ZMod S) = g₀ 0 0 then pd2a_rootEulerFactor u S else 0) -
      M * ((U * (r₁ - l₁) / S) * pd2a_rootEulerConstant S)| ≤ 15 * pd2a_rootAverageConstant * U * V * (Real.log (2 * U) / U) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hM]
    have hlog : 0 ≤ Real.log (2 * U) := Real.log_nonneg (by linarith)
    have hm := mul_le_mul hMMax hAvg (abs_nonneg _) (by positivity : 0 ≤ 15 * V)
    exact hm.trans_eq (by field_simp)
  rw [← hMain]
  have htri := abs_sub_le (rootResidueCount U V S g₀ l₁ r₁ l₂ r₂ l₃ r₃)
    (M * ∑ u ∈ I, if (u : ZMod S) = g₀ 0 0 then pd2a_rootEulerFactor u S else 0)
    (M * ((U * (r₁ - l₁) / S) * pd2a_rootEulerConstant S))
  refine htri.trans ((add_le_add hFinite hAverageError).trans ?_)
  have hTerm1 : 0 ≤ U ^ (-(1 / 100 : ℝ)) * (S : ℝ) ^ 2 := by positivity
  have hTerm2 : 0 ≤ Real.log (2 * U) / U := by
    exact div_nonneg (Real.log_nonneg (by linarith)) hUp.le
  have hC1 : 0 ≤ 1536 * DF := by positivity
  have hC2 : 0 ≤ 15 * pd2a_rootAverageConstant := mul_nonneg (by norm_num) pd2a_rootAverageConstant_pos.le
  have hCross := add_nonneg (mul_nonneg hC1 hTerm2) (mul_nonneg hC2 hTerm1)
  dsimp [pd2a_rootCountConstant, DF]
  have hCrossUV := mul_nonneg hCross (mul_nonneg hUp.le hVp.le)
  nlinarith only [hCrossUV]

end ArtinPrimitiveRoots.TypeII.PD
