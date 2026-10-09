import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.LocalParameterNorms

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

theorem normalize_bad (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (p : Triple)
    (hE : EulerHypotheses R η) (hp : eulerNeighborhood p) (hQ : (2 : ℝ) ^ (2000 : ℕ) < qI v.asIdeal)
    (hdev : ‖localEuler R η U u v hv (p 0) (p 1) (p 2) - 1‖ ≤
      16 * qI v.asIdeal ^ (-1 / 4000 : ℝ)) :
    ‖normalizedLocal R η U u v hv (p 0) (p 1) (p 2) - 1‖ ≤
    128 * qI v.asIdeal ^ (-1 / 4000 : ℝ) := by
  classical
  let Q : ℝ := qI v.asIdeal
  let V : ℂ := localV v (p 2)
  let W : ℂ := localWvar η U u v (p 1)
  let D1 : ℂ := localDvar η U u v (p 0)
  let E : ℂ := localEuler R η U u v hv (p 0) (p 1) (p 2)
  let M : ℂ := (1 - V) * (1 - W) / (1 - D1)
  let b : ℝ := Q ^ (-1 / 4000 : ℝ)
  change ‖M * E - 1‖ ≤ 128 * b
  have hq : 1 < Q := by
    dsimp [Q]
    exact qI_prime_gt_one v
  have hq4 : (4 : ℝ) < Q := by
    dsimp [Q]
    have hpow4 : (4 : ℝ) ≤ (2 : ℝ) ^ (2000 : ℕ) := by
      calc
        (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
        _ ≤ (2 : ℝ) ^ (2000 : ℕ) :=
          pow_le_pow_right₀ (by norm_num) (by norm_num)
    exact lt_of_le_of_lt hpow4 hQ
  have hhalf : Q ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
    calc
      Q ^ (-(1 / 2 : ℝ)) ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hq4.le (by norm_num)
      _ = 1 / 2 := by
        rw [Real.rpow_neg (by norm_num : 0 ≤ (4 : ℝ)) (1 / 2 : ℝ)]
        rw [← Real.sqrt_eq_rpow]
        norm_num
  have hξhalf : (1 / 2 : ℝ) < (p 0).re := by
    rcases hp with ⟨hξ, hw, hz⟩ | ⟨hξ, hw, hz⟩ <;> linarith
  have hwpos : 0 < (p 1).re := by
    rcases hp with ⟨hξ, hw, hz⟩ | ⟨hξ, hw, hz⟩ <;> linarith
  have hwdelta : (1 / 4000 : ℝ) < (p 1).re := by
    rcases hp with ⟨hξ, hw, hz⟩ | ⟨hξ, hw, hz⟩ <;> linarith
  have hzhalf : (1 / 2 : ℝ) < 6 * (p 2).re := by
    rcases hp with ⟨hξ, hw, hz⟩ | ⟨hξ, hw, hz⟩ <;> linarith
  have hpars := local_parameter_norms R η U hE u v hv (p 0) (p 1) (p 2)
  have hV0 : ‖V‖ ≤ Q ^ (-6 * (p 2).re) := by
    simpa [V, Q] using hpars.1
  have hW0 : ‖W‖ ≤ Q ^ (-(p 1).re) := by
    simpa [W, Q] using hpars.2.1
  have hD0 : ‖D1‖ ≤ Q ^ (-(p 0).re) := by
    simpa [D1, Q] using hpars.2.2.1
  have hVhalf : ‖V‖ ≤ 1 / 2 := by
    calc
      ‖V‖ ≤ Q ^ (-6 * (p 2).re) := hV0
      _ ≤ Q ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hq.le (by linarith [hzhalf])
      _ ≤ 1 / 2 := hhalf
  have hDhalf : ‖D1‖ ≤ 1 / 2 := by
    calc
      ‖D1‖ ≤ Q ^ (-(p 0).re) := hD0
      _ ≤ Q ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hq.le (by linarith [hξhalf])
      _ ≤ 1 / 2 := hhalf
  have hWone : ‖W‖ ≤ 1 := by
    calc
      ‖W‖ ≤ Q ^ (-(p 1).re) := hW0
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq.le (by linarith [hwpos])
  have hVb : ‖V‖ ≤ b := by
    calc
      ‖V‖ ≤ Q ^ (-6 * (p 2).re) := hV0
      _ ≤ Q ^ (-1 / 4000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq.le (by linarith [hzhalf])
      _ = b := rfl
  have hWb : ‖W‖ ≤ b := by
    calc
      ‖W‖ ≤ Q ^ (-(p 1).re) := hW0
      _ ≤ Q ^ (-1 / 4000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq.le (by linarith [hwdelta])
      _ = b := rfl
  have hDb : ‖D1‖ ≤ b := by
    calc
      ‖D1‖ ≤ Q ^ (-(p 0).re) := hD0
      _ ≤ Q ^ (-1 / 4000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq.le (by linarith [hξhalf])
      _ = b := rfl
  have hQpos : 0 < Q := lt_trans zero_lt_one hq
  have hbnonneg : 0 ≤ b := by
    dsimp [b]
    exact Real.rpow_nonneg hQpos.le _
  have hVW : ‖V‖ * ‖W‖ ≤ b := by
    calc
      ‖V‖ * ‖W‖ ≤ ‖V‖ * b :=
        mul_le_mul_of_nonneg_left hWb (norm_nonneg V)
      _ ≤ (1 / 2) * b :=
        mul_le_mul_of_nonneg_right hVhalf hbnonneg
      _ ≤ b := by nlinarith [hbnonneg]
  have hdenlow : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - D1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) D1
    simp only [norm_one] at h
    linarith [hDhalf]
  have hdenpos : 0 < ‖(1 : ℂ) - D1‖ := by linarith [hdenlow]
  have hdenne : (1 : ℂ) - D1 ≠ 0 := norm_pos_iff.mp hdenpos
  have hInv : ‖((1 : ℂ) - D1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hmul : (1 : ℝ) * ‖(1 : ℂ) - D1‖⁻¹ ≤ 2 :=
      (mul_inv_le_iff₀ hdenpos).2 (by linarith [hdenlow])
    simpa using hmul
  have hVtri : ‖(1 : ℂ) - V‖ ≤ 3 / 2 := by
    calc
      ‖(1 : ℂ) - V‖ ≤ 1 + ‖V‖ := by simpa using norm_sub_le (1 : ℂ) V
      _ ≤ 1 + 1 / 2 := by linarith [hVhalf]
      _ = 3 / 2 := by norm_num
  have hWtri : ‖(1 : ℂ) - W‖ ≤ 2 := by
    calc
      ‖(1 : ℂ) - W‖ ≤ 1 + ‖W‖ := by simpa using norm_sub_le (1 : ℂ) W
      _ ≤ 1 + 1 := by linarith [hWone]
      _ = 2 := by norm_num
  have hMnorm : ‖M‖ ≤ 6 := by
    calc
      ‖M‖ = ‖(1 : ℂ) - V‖ * ‖(1 : ℂ) - W‖ * ‖((1 : ℂ) - D1)⁻¹‖ := by
        simp [M, div_eq_mul_inv, norm_mul]
      _ ≤ (3 / 2) * 2 * 2 := by gcongr
      _ = 6 := by norm_num
  have hMminus : M - 1 = (D1 - V - W + V * W) / ((1 : ℂ) - D1) := by
    dsimp [M]
    field_simp [hdenne]
    ring
  have hDV : ‖D1 - V‖ ≤ ‖D1‖ + ‖V‖ := norm_sub_le D1 V
  have hDVW : ‖D1 - V - W‖ ≤ ‖D1‖ + ‖V‖ + ‖W‖ := by
    calc
      ‖D1 - V - W‖ ≤ ‖D1 - V‖ + ‖W‖ := norm_sub_le _ _
      _ ≤ (‖D1‖ + ‖V‖) + ‖W‖ := add_le_add_left hDV ‖W‖
  have hnum : ‖D1 - V - W + V * W‖ ≤ 4 * b := by
    calc
      ‖D1 - V - W + V * W‖ ≤ ‖D1 - V - W‖ + ‖V * W‖ := norm_add_le _ _
      _ ≤ (‖D1‖ + ‖V‖ + ‖W‖) + (‖V‖ * ‖W‖) := by
        rw [norm_mul]
        gcongr
      _ ≤ 4 * b := by nlinarith [hDb, hVb, hWb, hVW]
  have hInvNorm : ‖(1 : ℂ) - D1‖⁻¹ ≤ 2 := by simpa [norm_inv] using hInv
  have hMdev : ‖M - 1‖ ≤ 8 * b := by
    rw [hMminus, norm_div, div_eq_mul_inv]
    calc
      ‖D1 - V - W + V * W‖ * ‖(1 : ℂ) - D1‖⁻¹ ≤ (4 * b) * 2 := by
        gcongr
      _ = 8 * b := by ring
  have hdevE : ‖E - 1‖ ≤ 16 * b := by simpa [E, b, Q] using hdev
  have hsplit : M * E - 1 = M * (E - 1) + (M - 1) := by ring
  calc
    ‖M * E - 1‖ = ‖M * (E - 1) + (M - 1)‖ := by rw [hsplit]
    _ ≤ ‖M * (E - 1)‖ + ‖M - 1‖ := norm_add_le _ _
    _ = ‖M‖ * ‖E - 1‖ + ‖M - 1‖ := by rw [norm_mul]
    _ ≤ 6 * (16 * b) + 8 * b := by gcongr
    _ ≤ 128 * b := by nlinarith [hbnonneg]

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
