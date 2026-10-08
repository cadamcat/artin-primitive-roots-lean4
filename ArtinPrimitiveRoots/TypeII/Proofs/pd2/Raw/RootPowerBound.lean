import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootSymmetric
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootInputs

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd2a_raw_bracket_bound (U V : ℝ) (hU : 2 ≤ U) (hV : 2 ≤ V)
    (S : ℕ) (hS : 0<S) :
    (min U V)^(-(1/100:ℝ))*(S:ℝ)^2+Real.log (2*min U V)/min U V+1/(U*V) ≤
      5*(min U V)^(-(1/200:ℝ))*(S:ℝ)^2 := by
  let W := min U V
  have hW2 : 2 ≤ W := le_min hU hV
  have hW1 : 1 ≤ W := by linarith
  have hWp : 0<W := by linarith
  have hS1 : (1:ℝ) ≤ S := by exact_mod_cast hS
  have hSsq : (1:ℝ) ≤ (S:ℝ)^2 := one_le_pow₀ hS1
  have hHalf : 1 ≤ W^(1/2:ℝ) := Real.one_le_rpow hW1 (by norm_num)
  have hLogW : Real.log W ≤ 2*W^(1/2:ℝ) := by
    have h := Real.log_le_rpow_div hWp.le (by norm_num : (0:ℝ)<1/2)
    exact h.trans_eq (by ring)
  have hLog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num only at h
    exact h
  have hLog : Real.log (2*W) ≤ 3*W^(1/2:ℝ) := by
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hWp.ne']
    linarith
  have hDiv : W^(1/2:ℝ)/W=W^(-(1/2:ℝ)) := by
    calc
      _ = W^(1/2:ℝ)/W^(1:ℝ) := by rw [Real.rpow_one]
      _ = W^((1/2:ℝ)-1) := (Real.rpow_sub hWp _ _).symm
      _ = _ := by congr 1;norm_num
  have hPL : W^(-(1/2:ℝ)) ≤ W^(-(1/200:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  have hLogP : Real.log (2*W)/W ≤ 3*W^(-(1/200:ℝ)) := by
    have h := div_le_div_of_nonneg_right hLog hWp.le
    have he : 3*W^(1/2:ℝ)/W=3*W^(-(1/2:ℝ)) := by rw [mul_div_assoc,hDiv]
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left hPL (by norm_num))
  have hP1 : W^(-(1/100:ℝ)) ≤ W^(-(1/200:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  have hWsq : W^2 ≤ U*V := by
    have h := mul_le_mul (min_le_left U V) (min_le_right U V) hWp.le (by linarith : (0:ℝ)≤U)
    simpa only [pow_two] using h
  have hInv : 1/(U*V) ≤ W^(-(1/200:ℝ)) := by
    calc
      _ ≤ 1/W^2 := one_div_le_one_div_of_le (sq_pos_of_pos hWp) hWsq
      _ = W^(-2:ℝ) := by rw [Real.rpow_neg hWp.le,Real.rpow_two,one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  have hP0 : 0 ≤ W^(-(1/200:ℝ)) := Real.rpow_nonneg hWp.le _
  have hFirst := mul_le_mul_of_nonneg_right hP1 (sq_nonneg (S:ℝ))
  have hSecond := mul_le_mul_of_nonneg_left hSsq (mul_nonneg (by norm_num : (0:ℝ)≤3) hP0)
  have hThird := mul_le_mul_of_nonneg_left hSsq hP0
  simp only [mul_one] at hSecond hThird
  change W^(-(1/100:ℝ))*(S:ℝ)^2+Real.log (2*W)/W+1/(U*V) ≤ _
  nlinarith

lemma pd2a_root_residue_power_bound :
    ∃ C : ℝ,0<C ∧ ∀ U V : ℝ,2 ≤ U → 2 ≤ V → ∀ S : ℕ,Squarefree S → ∀ hS : 0<S,
      ∀ g₀ : Matrix (Fin 2) (Fin 2) (ZMod S),g₀.det=1 →
      ∀ l₁ r₁ l₂ r₂ l₃ r₃ : ℝ,
      1 ≤ l₁ → l₁ ≤ r₁ → r₁ ≤ 16 → 1 ≤ l₂ → l₂ ≤ r₂ → r₂ ≤ 16 →
      0 ≤ l₃ → l₃ ≤ r₃ → r₃ ≤ 1 →
      |rootResidueCount U V S g₀ l₁ r₁ l₂ r₂ l₃ r₃-
        U*V*(r₁-l₁)*(r₂-l₂)*(r₃-l₃)/((Real.pi^2/6)*(sl2Card S hS:ℝ))| ≤
        C*U*V*(min U V)^(-(1/200:ℝ))*(S:ℝ)^2 := by
  obtain ⟨inputs⟩ := pd2a_counting_inputs_exists
  let C := pd2a_rootSymmetricConstant inputs
  have hC : 0<C := pd2a_rootSymmetricConstant_pos inputs
  refine ⟨5*C,by positivity,?_⟩
  intro U V hU hV S hSq hS g₀ hdet l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hle₁ hr₁ hl₂ hle₂ hr₂ hl₃ hle₃ hr₃
  have ht := pd2a_rootResidueCount_uniform inputs U V hU hV S hS hSq g₀ hdet
    l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hle₁ hr₁ hl₂ hle₂ hr₂ hl₃ hle₃ hr₃
  have hb := pd2a_raw_bracket_bound U V hU hV S hS
  have hc := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ)≤C*U*V)
  apply ht.trans
  exact hc.trans_eq (by ring)

end ArtinPrimitiveRoots.TypeII.PD
