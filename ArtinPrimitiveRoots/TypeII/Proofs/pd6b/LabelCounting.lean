import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.UnionLabels

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical

noncomputable section

theorem primeBand_card_upper {x a : ℝ} (hL : 1 ≤ Real.log x) (ha : 0 < a) :
    ((primeBand x a).card : ℝ) ≤ 2 * Real.exp (2 * Real.rpow (Real.log x) a) := by
  have hsub : primeBand x a ⊆ Finset.range (⌊Real.exp (2 * Real.rpow (Real.log x) a)⌋₊ + 1) :=
    Finset.filter_subset _ _
  have hn := Finset.card_le_card hsub
  have hcard : ((primeBand x a).card : ℝ) ≤ (⌊Real.exp (2 * Real.rpow (Real.log x) a)⌋₊ : ℝ) + 1 := by
    exact_mod_cast (by simpa only [Finset.card_range] using hn)
  have hExp : 1 ≤ Real.exp (2 * Real.rpow (Real.log x) a) := Real.one_le_exp_iff.mpr
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [hL]) a))
  have hf := Nat.floor_le (Real.exp_pos (2 * Real.rpow (Real.log x) a)).le
  linarith

/-- The number of unrestricted edge-union label choices is subexponential. -/
theorem unionLineChoice_card_upper {x : ℝ} {K N : ℕ} (a : Fin K → ℝ) (ha : ValidBands K a)
    (hL : 1 ≤ Real.log x) (hN : (N : ℝ) ≤ 3 * Real.rpow (Real.log x) (1 / 100 : ℝ)) :
    (Fintype.card (UnionLineChoice x a N) : ℝ) ≤
      Real.exp (9 * (K : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ)) := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hcard : (Fintype.card (UnionLineChoice x a N) : ℝ) =
      ∏ q : Fin K × Fin N, ((primeBand x (a q.1)).card : ℝ) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro q hq
    congr 1
    exact Fintype.card_coe _
  have hpoint (q : Fin K × Fin N) : ((primeBand x (a q.1)).card : ℝ) ≤
      Real.exp (3 * Real.rpow (Real.log x) (1 / 5 : ℝ)) := by
    have haPos : 0 < a q.1 := (by norm_num : (0 : ℝ) < 1 / 10).trans (ha.2.1 q.1).1
    have hband := primeBand_card_upper hL haPos
    have hpow : Real.rpow (Real.log x) (a q.1) ≤ Real.rpow (Real.log x) (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (ha.2.1 q.1).2.le
    have hOne : 1 ≤ Real.rpow (Real.log x) (1 / 5 : ℝ) := Real.one_le_rpow hL (by norm_num)
    have hLog2 : Real.log 2 ≤ 1 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hEq : 2 * Real.exp (2 * Real.rpow (Real.log x) (a q.1)) =
        Real.exp (Real.log 2 + 2 * Real.rpow (Real.log x) (a q.1)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact hband.trans (hEq.trans_le (Real.exp_le_exp.mpr (by nlinarith)))
  have hprod : (Fintype.card (UnionLineChoice x a N) : ℝ) ≤
      Real.exp (((K : ℝ) * (N : ℝ)) * (3 * Real.rpow (Real.log x) (1 / 5 : ℝ))) := by
    rw [hcard]
    calc
      _ ≤ ∏ q : Fin K × Fin N, Real.exp (3 * Real.rpow (Real.log x) (1 / 5 : ℝ)) :=
        Finset.prod_le_prod₀ (fun q hq => Nat.cast_nonneg _) (fun q hq => hpoint q)
      _ = _ := by rw [← Real.exp_sum]; simp [mul_assoc]
  have hjoin : Real.rpow (Real.log x) (1 / 100 : ℝ) * Real.rpow (Real.log x) (1 / 5 : ℝ) =
      Real.rpow (Real.log x) (21 / 100 : ℝ) := by
    calc
      _ = Real.rpow (Real.log x) ((1 / 100 : ℝ) + (1 / 5 : ℝ)) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by norm_num
  apply hprod.trans
  apply Real.exp_le_exp.mpr
  have hbound : (K : ℝ) * (N : ℝ) * (3 * Real.rpow (Real.log x) (1 / 5 : ℝ)) ≤
      (K : ℝ) * (3 * Real.rpow (Real.log x) (1 / 100 : ℝ)) *
        (3 * Real.rpow (Real.log x) (1 / 5 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg K))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Real.rpow_nonneg hLpos.le (1 / 5 : ℝ)))
  calc
    _ ≤ (K : ℝ) * (3 * Real.rpow (Real.log x) (1 / 100 : ℝ)) *
        (3 * Real.rpow (Real.log x) (1 / 5 : ℝ)) := hbound
    _ = _ := by rw [← hjoin]; ring

end
end ArtinPrimitiveRoots.TypeII.PD
