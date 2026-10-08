import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootMobius

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_rootEulerCoefficient (S n : ℕ) : ℝ :=
  if Nat.Coprime n S then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0
noncomputable def pd2a_rootEulerConstant (S : ℕ) : ℝ := ∑' n : ℕ, pd2a_rootEulerCoefficient S n

lemma pd2a_principal_character_nat (S : ℕ) [NeZero S] (n : ℕ) :
    (1 : DirichletCharacter ℂ S) (n : ZMod S) = if Nat.Coprime n S then 1 else 0 := by
  by_cases hc : Nat.Coprime n S
  · rw [if_pos hc]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n S).mpr hc)
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n S).mp h))

lemma pd2a_rootEuler_term (S : ℕ) [NeZero S] (n : ℕ) :
    LSeries.term (fun j : ℕ => (1 : DirichletCharacter ℂ S) (j : ZMod S) *
      (ArithmeticFunction.moebius j : ℂ)) 2 n = (pd2a_rootEulerCoefficient S n : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [pd2a_rootEulerCoefficient, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_ofNat, pd2a_principal_character_nat]
    unfold pd2a_rootEulerCoefficient
    by_cases hc : Nat.Coprime n S <;> simp [Nat.Coprime, hc] <;> push_cast <;> rfl

lemma pd2a_rootEuler_summable (S : ℕ) (hS : 0 < S) : Summable (pd2a_rootEulerCoefficient S) := by
  letI : NeZero S := ⟨hS.ne'⟩
  have hμ : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) 2 :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by norm_num)
  have hχ := DirichletCharacter.LSeriesSummable_mul (1 : DirichletCharacter ℂ S) hμ
  apply Complex.summable_ofReal.mp
  exact hχ.congr (fun n => by convert pd2a_rootEuler_term S n using 1 <;> congr!)

lemma pd2a_rootEuler_LSeries (S : ℕ) [NeZero S] :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ S) (n : ZMod S) * (ArithmeticFunction.moebius n : ℂ)) 2 =
      (pd2a_rootEulerConstant S : ℂ) := by
  unfold LSeries pd2a_rootEulerConstant
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  exact pd2a_rootEuler_term S n

lemma pd2a_principal_LSeries_two (S : ℕ) [NeZero S] :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ S) (n : ZMod S)) 2 =
      (((∏ p ∈ S.primeFactors, (1 - 1 / (p : ℝ) ^ 2)) * (Real.pi ^ 2 / 6) : ℝ) : ℂ) := by
  rw [← DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ S) (by norm_num)]
  change DirichletCharacter.LFunctionTrivChar S 2 = _
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (by norm_num), riemannZeta_two]
  simp only [Complex.cpow_neg, Complex.cpow_ofNat]
  push_cast
  simp only [one_div]

lemma pd2a_rootEulerConstant_value (S : ℕ) (hS : 0 < S) :
    pd2a_rootEulerConstant S = (Real.pi ^ 2 / 6)⁻¹ *
      (∏ p ∈ S.primeFactors, (1 - 1 / (p : ℝ) ^ 2))⁻¹ := by
  letI : NeZero S := ⟨hS.ne'⟩
  let P := ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℝ) ^ 2)
  have hP : 0 < P := by
    apply Finset.prod_pos
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    have hpR : 1 < (p : ℝ) := by exact_mod_cast hpp.one_lt
    have hp2 : 1 < (p : ℝ) ^ 2 := by nlinarith
    apply sub_pos.mpr
    exact (div_lt_one (by positivity : 0 < (p : ℝ) ^ 2)).mpr hp2
  have hZ : 0 < Real.pi ^ 2 / 6 := by positivity
  have hΦ : (((P * (Real.pi ^ 2 / 6) : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (mul_pos hP hZ).ne'
  have hprod := DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ S) (s := 2) (by norm_num)
  change LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ S) (n : ZMod S)) 2 *
      LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ S) (n : ZMod S) * (ArithmeticFunction.moebius n : ℂ)) 2 = 1 at hprod
  rw [pd2a_principal_LSeries_two, pd2a_rootEuler_LSeries] at hprod
  have hEq : (pd2a_rootEulerConstant S : ℂ) = ((P * (Real.pi ^ 2 / 6) : ℝ) : ℂ)⁻¹ := by
    apply mul_left_cancel₀ hΦ
    exact hprod.trans (mul_inv_cancel₀ hΦ).symm
  have hReal : pd2a_rootEulerConstant S = (P * (Real.pi ^ 2 / 6))⁻¹ := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_inv] using hEq
  rw [hReal, mul_inv]
  dsimp [P]
  ring

end ArtinPrimitiveRoots.TypeII.PD
