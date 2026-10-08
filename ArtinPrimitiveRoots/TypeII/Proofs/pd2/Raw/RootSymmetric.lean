import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootLargeU
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootSandwich

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_rootSymmetricConstant (inputs : pd2a_RootCountingInputs) : ℝ :=
  pd2a_rootCountConstant inputs + 225 / (Real.pi ^ 2 / 6)

lemma pd2a_rootSymmetricConstant_pos (inputs : pd2a_RootCountingInputs) : 0 < pd2a_rootSymmetricConstant inputs := by
  have hC := pd2a_rootCountConstant_pos inputs
  have hZ : 0 < Real.pi ^ 2 / 6 := by positivity
  dsimp [pd2a_rootSymmetricConstant]
  positivity

lemma pd2a_reflected_interval (l r e : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) (he : 0 ≤ e) :
    0 ≤ max 0 (1 - r - e) ∧ max 0 (1 - r - e) ≤ 1 - l ∧ 1 - l ≤ 1 ∧
      0 ≤ ((1 - l) - max 0 (1 - r - e)) - (r - l) ∧
        ((1 - l) - max 0 (1 - r - e)) - (r - l) ≤ e := by
  have hL : 0 ≤ max 0 (1 - r - e) := le_max_left _ _
  have hLR : max 0 (1 - r - e) ≤ 1 - l := max_le (by linarith) (by linarith)
  refine ⟨hL, hLR, by linarith, ?_, ?_⟩
  all_goals
    rcases le_total 0 (1 - r - e) with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h]
      linarith

lemma pd2a_rootResidueCount_large_first (inputs : pd2a_RootCountingInputs)
    (U V : ℝ) (hV : 2 ≤ V) (hVU : V ≤ U) (S : ℕ) (hS : 0 < S) (hSq : Squarefree S)
    (g : Matrix (Fin 2) (Fin 2) (ZMod S)) (hdet : Matrix.det g = 1)
    (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ)
    (hl₁ : 1 ≤ l₁) (hlr₁ : l₁ ≤ r₁) (hr₁ : r₁ ≤ 16)
    (hl₂ : 1 ≤ l₂) (hlr₂ : l₂ ≤ r₂) (hr₂ : r₂ ≤ 16)
    (hl₃ : 0 ≤ l₃) (hlr₃ : l₃ ≤ r₃) (hr₃ : r₃ ≤ 1) :
    |rootResidueCount U V S g l₁ r₁ l₂ r₂ l₃ r₃ -
      U * V * (r₁ - l₁) * (r₂ - l₂) * (r₃ - l₃) / ((Real.pi ^ 2 / 6) * (sl2Card S hS : ℝ))| ≤
      pd2a_rootSymmetricConstant inputs * U * V *
        (V ^ (-(1 / 100 : ℝ)) * (S : ℝ) ^ 2 + Real.log (2 * V) / V + 1 / (U * V)) := by
  have hU : 2 ≤ U := hV.trans hVU
  have hUp : 0 < U := by linarith
  have hVp : 0 < V := by linarith
  have hZ : 0 < Real.pi ^ 2 / 6 := by positivity
  have hCard : (1 : ℝ) ≤ sl2Card S hS := by exact_mod_cast pd2a_sl2Card_pos S hS
  have hCardp : 0 < (sl2Card S hS : ℝ) := by linarith
  let A := U * V * (r₁ - l₁) * (r₂ - l₂) / ((Real.pi ^ 2 / 6) * (sl2Card S hS : ℝ))
  let w := r₃ - l₃
  let e := 1 / (U * V)
  let T := V ^ (-(1 / 100 : ℝ)) * (S : ℝ) ^ 2 + Real.log (2 * V) / V
  let E := pd2a_rootCountConstant inputs * U * V * T
  let K := 225 / (Real.pi ^ 2 / 6)
  let C := rootResidueCount U V S g l₁ r₁ l₂ r₂ l₃ r₃
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hT : 0 ≤ T := by dsimp [T]; exact add_nonneg (by positivity) (div_nonneg (Real.log_nonneg (by linarith)) hVp.le)
  have hE : 0 ≤ E := by dsimp [E]; exact mul_nonneg (mul_nonneg (mul_nonneg (pd2a_rootCountConstant_pos inputs).le hUp.le) hVp.le) hT
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hShift : A * e ≤ K := by
    have hW₁ : 0 ≤ r₁ - l₁ := by linarith
    have hW₂ : 0 ≤ r₂ - l₂ := by linarith
    have hProd : (r₁ - l₁) * (r₂ - l₂) ≤ 225 := by
      have h := mul_le_mul (by linarith : r₁ - l₁ ≤ 15) (by linarith : r₂ - l₂ ≤ 15) hW₂ (by norm_num : (0 : ℝ) ≤ 15)
      norm_num at h ⊢
      exact h
    have hDen : Real.pi ^ 2 / 6 ≤ (Real.pi ^ 2 / 6) * (sl2Card S hS : ℝ) := by nlinarith
    calc
      A * e = (r₁ - l₁) * (r₂ - l₂) / ((Real.pi ^ 2 / 6) * (sl2Card S hS : ℝ)) := by dsimp [A, e]; field_simp
      _ ≤ 225 / (Real.pi ^ 2 / 6) := div_le_div₀ (by norm_num) hProd hZ hDen
  have hDetSwap := pd2a_rootSwapMatrix_det g hdet
  obtain ⟨hL, hLR, hR, hDelta0, hDelta1⟩ := pd2a_reflected_interval l₃ r₃ e hl₃ hlr₃ hr₃ he
  have hUpperCount := pd2a_rootCount_swap_upper U V hU hV S g l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hlr₁ hl₂ hlr₂
  have hUpperEst := pd2a_rootResidueCount_small_first inputs V U hV hVU S hS hSq (pd2a_rootSwapMatrix g) hDetSwap
    l₂ r₂ l₁ r₁ (max 0 (1 - r₃ - e)) (1 - l₃) hl₂ hlr₂ hr₂ hl₁ hlr₁ hr₁ hL hLR hR
  have hUpperMean : V * U * (r₂ - l₂) * (r₁ - l₁) * ((1 - l₃) - max 0 (1 - r₃ - e)) /
      ((Real.pi ^ 2 / 6) * (sl2Card S hS : ℝ)) = A * ((1 - l₃) - max 0 (1 - r₃ - e)) := by dsimp [A]; ring
  rw [hUpperMean] at hUpperEst
  have hUpperE : pd2a_rootCountConstant inputs * V * U * T = E := by dsimp [E]; ring
  have hUpper : C - A * w ≤ E + K := by
    have hh := (abs_le.mp hUpperEst).2
    have hMul := mul_le_mul_of_nonneg_left hDelta1 hA
    have hCount : C ≤ rootResidueCount V U S (pd2a_rootSwapMatrix g) l₂ r₂ l₁ r₁ (max 0 (1 - r₃ - e)) (1 - l₃) := hUpperCount
    change _ ≤ pd2a_rootCountConstant inputs * V * U * T at hh
    rw [hUpperE] at hh
    dsimp [w] at ⊢
    nlinarith [hShift]
  have hLower : -(E + K) ≤ C - A * w := by
    by_cases hWidth : e ≤ w
    · have hLo : 0 ≤ 1 - r₃ := by linarith
      have hLRm : 1 - r₃ ≤ 1 - l₃ - e := by dsimp [w] at hWidth; linarith
      have hRm : 1 - l₃ - e ≤ 1 := by linarith
      have hLowerCount := pd2a_rootCount_swap_lower U V hU hV S g l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hlr₁ hl₂ hlr₂ hl₃
      have hLowerEst := pd2a_rootResidueCount_small_first inputs V U hV hVU S hS hSq (pd2a_rootSwapMatrix g) hDetSwap
        l₂ r₂ l₁ r₁ (1 - r₃) (1 - l₃ - e) hl₂ hlr₂ hr₂ hl₁ hlr₁ hr₁ hLo hLRm hRm
      have hMean : V * U * (r₂ - l₂) * (r₁ - l₁) * ((1 - l₃ - e) - (1 - r₃)) /
          ((Real.pi ^ 2 / 6) * (sl2Card S hS : ℝ)) = A * (w - e) := by dsimp [A, w]; ring
      rw [hMean] at hLowerEst
      have hh := (abs_le.mp hLowerEst).1
      change _ ≤ _ at hh
      have hCE : pd2a_rootCountConstant inputs * V * U * T = E := hUpperE
      change -(pd2a_rootCountConstant inputs * V * U * T) ≤ _ at hh
      rw [hCE] at hh
      have hCount : rootResidueCount V U S (pd2a_rootSwapMatrix g) l₂ r₂ l₁ r₁ (1 - r₃) (1 - l₃ - e) ≤ C := hLowerCount
      nlinarith [hShift]
    · have hWidth' : w ≤ e := le_of_lt (lt_of_not_ge hWidth)
      have hC : 0 ≤ C := pd2a_rootCount_nonneg U V S g l₁ r₁ l₂ r₂ l₃ r₃
      have hMul := mul_le_mul_of_nonneg_left hWidth' hA
      linarith
  have hMeanOrig : U * V * (r₁ - l₁) * (r₂ - l₂) * (r₃ - l₃) /
      ((Real.pi ^ 2 / 6) * (sl2Card S hS : ℝ)) = A * w := by dsimp [A, w]; ring
  rw [hMeanOrig]
  have hAbs : |C - A * w| ≤ E + K := abs_le.mpr ⟨hLower, hUpper⟩
  refine hAbs.trans ?_
  have hUV : U * V ≠ 0 := (mul_pos hUp hVp).ne'
  have hExtra : 0 ≤ K * U * V * T + pd2a_rootCountConstant inputs := by
    exact add_nonneg (by positivity) (pd2a_rootCountConstant_pos inputs).le
  have hRight : pd2a_rootSymmetricConstant inputs * U * V * (T + 1 / (U * V)) =
      E + K + (K * U * V * T + pd2a_rootCountConstant inputs) := by
    dsimp [E, K, pd2a_rootSymmetricConstant]
    field_simp
    ring
  change E + K ≤ pd2a_rootSymmetricConstant inputs * U * V * (T + 1 / (U * V))
  rw [hRight]
  exact le_add_of_nonneg_right hExtra

lemma pd2a_rootResidueCount_uniform (inputs : pd2a_RootCountingInputs)
    (U V : ℝ) (hU : 2 ≤ U) (hV : 2 ≤ V) (S : ℕ) (hS : 0 < S) (hSq : Squarefree S)
    (g : Matrix (Fin 2) (Fin 2) (ZMod S)) (hdet : Matrix.det g = 1)
    (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ)
    (hl₁ : 1 ≤ l₁) (hlr₁ : l₁ ≤ r₁) (hr₁ : r₁ ≤ 16)
    (hl₂ : 1 ≤ l₂) (hlr₂ : l₂ ≤ r₂) (hr₂ : r₂ ≤ 16)
    (hl₃ : 0 ≤ l₃) (hlr₃ : l₃ ≤ r₃) (hr₃ : r₃ ≤ 1) :
    |rootResidueCount U V S g l₁ r₁ l₂ r₂ l₃ r₃ -
      U * V * (r₁ - l₁) * (r₂ - l₂) * (r₃ - l₃) / ((Real.pi ^ 2 / 6) * (sl2Card S hS : ℝ))| ≤
      pd2a_rootSymmetricConstant inputs * U * V *
        ((min U V) ^ (-(1 / 100 : ℝ)) * (S : ℝ) ^ 2 + Real.log (2 * min U V) / min U V + 1 / (U * V)) := by
  have hUp : 0 < U := by linarith
  have hVp : 0 < V := by linarith
  have hC : pd2a_rootCountConstant inputs ≤ pd2a_rootSymmetricConstant inputs := by
    dsimp [pd2a_rootSymmetricConstant]
    exact le_add_of_nonneg_right (by positivity)
  have hCs : 0 ≤ pd2a_rootSymmetricConstant inputs := pd2a_rootSymmetricConstant_pos inputs |>.le
  by_cases hUV : U ≤ V
  · rw [min_eq_left hUV]
    have he := pd2a_rootResidueCount_small_first inputs U V hU hUV S hS hSq g hdet
      l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hlr₁ hr₁ hl₂ hlr₂ hr₂ hl₃ hlr₃ hr₃
    have hT : 0 ≤ U ^ (-(1 / 100 : ℝ)) * (S : ℝ) ^ 2 + Real.log (2 * U) / U :=
      add_nonneg (by positivity) (div_nonneg (Real.log_nonneg (by linarith)) hUp.le)
    calc
      _ ≤ pd2a_rootCountConstant inputs * U * V * (U ^ (-(1 / 100 : ℝ)) * (S : ℝ) ^ 2 + Real.log (2 * U) / U) := he
      _ ≤ pd2a_rootSymmetricConstant inputs * U * V * (U ^ (-(1 / 100 : ℝ)) * (S : ℝ) ^ 2 + Real.log (2 * U) / U) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hUp.le) hVp.le) hT
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
  · have hVU : V ≤ U := le_of_lt (lt_of_not_ge hUV)
    rw [min_eq_right hVU]
    exact pd2a_rootResidueCount_large_first inputs U V hV hVU S hS hSq g hdet
      l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hlr₁ hr₁ hl₂ hlr₂ hr₂ hl₃ hlr₃ hr₃

end ArtinPrimitiveRoots.TypeII.PD
