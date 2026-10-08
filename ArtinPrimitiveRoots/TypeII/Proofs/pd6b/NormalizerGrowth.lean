import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadProbability

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical

noncomputable section

/-- The grouped edge normalizer grows only subexponentially in the logarithmic scale. -/
theorem bandNormalizer_growth {x : ℝ} {K N : ℕ} (a : Fin K → ℝ)
    (hL : 1 ≤ Real.log x) (hV : ∀ i, Real.log 2 / 2 ≤ bandMass x (a i))
    (hN : (N : ℝ) ≤ 3 * Real.rpow (Real.log x) (1 / 100 : ℝ)) :
    (∏ i : Fin K, (bandMass x (a i))⁻¹ ^ N) ≤
      Real.exp ((3 * (K : ℝ) * Real.log ((Real.log 2 / 2)⁻¹)) * Real.rpow (Real.log x) (1 / 100 : ℝ)) := by
  let c := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hcOne : c < 1 := by dsimp [c]; linarith
  have hInvOne : 1 ≤ c⁻¹ := (one_le_inv₀ hc).mpr hcOne.le
  have hLogInv : 0 ≤ Real.log (c⁻¹) := Real.log_nonneg hInvOne
  have hPoint (i : Fin K) : (bandMass x (a i))⁻¹ ^ N ≤ c⁻¹ ^ N := by
    have hpos : 0 < bandMass x (a i) := hc.trans_le (hV i)
    have hInv : (bandMass x (a i))⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hpos hc).mpr (hV i)
    exact pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) hInv N
  have hProd : (∏ i : Fin K, (bandMass x (a i))⁻¹ ^ N) ≤ (c⁻¹ ^ N) ^ K := by
    calc
      _ ≤ ∏ i : Fin K, c⁻¹ ^ N := Finset.prod_le_prod₀ (fun i hi => by
        have hp := hc.trans_le (hV i); positivity) (fun i hi => hPoint i)
      _ = _ := by simp
  have hcInvPos : 0 < c⁻¹ := inv_pos.mpr hc
  have hPowEq : (c⁻¹ ^ N) ^ K = Real.exp (((K : ℝ) * (N : ℝ)) * Real.log (c⁻¹)) := by
    calc
      _ = Real.exp (Real.log ((c⁻¹ ^ N) ^ K)) := (Real.exp_log (pow_pos (pow_pos hcInvPos _) _)).symm
      _ = _ := by rw [Real.log_pow, Real.log_pow]; ring
  apply hProd.trans
  rw [hPowEq]
  apply Real.exp_le_exp.mpr
  have hBound : (K : ℝ) * (N : ℝ) * Real.log (c⁻¹) ≤
      (K : ℝ) * (3 * Real.rpow (Real.log x) (1 / 100 : ℝ)) * Real.log (c⁻¹) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg K)) hLogInv
  calc
    _ ≤ (K : ℝ) * (3 * Real.rpow (Real.log x) (1 / 100 : ℝ)) * Real.log (c⁻¹) := hBound
    _ = _ := by dsimp [c]; ring

theorem physicalMeasure_fresh_eq_groupedNormalizer {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hV : ∀ i : Fin K, 0 < bandMass x (a i)) :
    physicalMeasure x K a * (∏ i : Fin K, (bandMass x (a i))⁻¹) =
      ∏ i : Fin K, (bandMass x (a i))⁻¹ ^ (momentJ x + 2) := by
  classical
  unfold physicalMeasure
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  let V := bandMass x (a i)
  have hVpos : 0 < V := hV i
  have hslot : slotCount x = momentJ x + 1 := rfl
  calc
    Real.rpow V (-(slotCount x : ℝ)) * V⁻¹ =
        V⁻¹ ^ slotCount x * V⁻¹ := by
      have hp : Real.rpow V (-(slotCount x : ℝ)) = V⁻¹ ^ slotCount x := by
        calc
          _ = (Real.rpow V (slotCount x : ℝ))⁻¹ := Real.rpow_neg hVpos.le _
          _ = (V ^ slotCount x)⁻¹ := congrArg Inv.inv (Real.rpow_natCast V _)
          _ = V⁻¹ ^ slotCount x := by simp only [inv_pow]
      rw [hp]
    _ = V⁻¹ ^ (momentJ x + 2) := by
      calc
        V⁻¹ ^ slotCount x * V⁻¹ = V⁻¹ ^ (slotCount x + 1) :=
          (pow_succ (V⁻¹) (slotCount x)).symm
        _ = V⁻¹ ^ (momentJ x + 2) := by simp [hslot]

end
end ArtinPrimitiveRoots.TypeII.PD
