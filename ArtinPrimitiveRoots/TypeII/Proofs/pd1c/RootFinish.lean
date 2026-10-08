import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootSymmetric
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootAsymptotic

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

theorem pd1c_root_residue_from_inputs (inputs : pd1c_RootCountingInputs)
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
  obtain ⟨xAbs, hxAbs, hAbs⟩ := pd1c_root_error_absorb δ C_K hδ hCK
  let xTwo := max 2 (Real.exp (Real.log 2 / δ))
  let x₀ := max xAbs xTwo
  let C := pd1c_rootSymmetricConstant inputs
  refine ⟨δ / 1000, 6 * C, x₀, rfl, by dsimp [C]; exact mul_pos (by norm_num) (pd1c_rootSymmetricConstant_pos inputs),
    hxAbs.trans (le_max_left _ _), ?_⟩
  intro x hx U V hU hV S hSq hS hSBound g₀ hdet l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hlr₁ hr₁ hl₂ hlr₂ hr₂ hl₃ hlr₃ hr₃
  have hxA : xAbs ≤ x := (le_max_left _ _).trans hx
  have hxT : xTwo ≤ x := (le_max_right _ _).trans hx
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hxT
  have hxp : 0 < x := by linarith
  have hLog : Real.log 2 / δ ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hxT)
  have hPower2 : 2 ≤ x ^ δ := by
    rw [Real.rpow_def_of_pos hxp]
    calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have h := (div_le_iff₀ hδ).mp hLog
        nlinarith)
  have hU2 : 2 ≤ U := hPower2.trans hU
  have hV2 : 2 ≤ V := hPower2.trans hV
  have hUp : 0 < U := by linarith
  have hVp : 0 < V := by linarith
  let W := min U V
  have hW : x ^ δ ≤ W := le_min hU hV
  have hW2 : 2 ≤ W := le_min hU2 hV2
  have hWp : 0 < W := by linarith
  have hWsq : W ^ 2 ≤ U * V := by
    have h : W * W ≤ U * V := mul_le_mul (min_le_left U V) (min_le_right U V) hWp.le hUp.le
    simpa only [pow_two] using h
  have hInv : 1 / (U * V) ≤ W ^ (-2 : ℝ) := by
    calc
      _ ≤ 1 / W ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos hWp) hWsq
      _ = _ := by rw [Real.rpow_neg, Real.rpow_ofNat, one_div] <;> positivity
  have hDecay := hAbs x hxA W S hW (Nat.cast_nonneg S) hSBound
  have hErr := pd1c_rootResidueCount_uniform inputs U V hU2 hV2 S hS hSq g₀ hdet
    l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hlr₁ hr₁ hl₂ hlr₂ (by linarith) hl₃ hlr₃ hr₃
  have hC : 0 < C := pd1c_rootSymmetricConstant_pos inputs
  have hCoef : 0 ≤ C * U * V := by positivity
  calc
    _ ≤ C * U * V * (W ^ (-(1 / 100 : ℝ)) * (S : ℝ) ^ 2 + Real.log (2 * W) / W + 1 / (U * V)) := hErr
    _ ≤ C * U * V * (W ^ (-(1 / 100 : ℝ)) * (S : ℝ) ^ 2 + Real.log (2 * W) / W + W ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hInv _) hCoef
    _ ≤ C * U * V * (6 * x ^ (-(δ / 1000))) := mul_le_mul_of_nonneg_left hDecay hCoef
    _ = _ := by simp only [Real.rpow_eq_pow]; ring

end ArtinPrimitiveRoots.TypeII.PD
