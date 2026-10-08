import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open scoped ArithmeticFunction.Moebius

noncomputable section

private lemma moebius_term_two (n : ℕ) :
    LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) 2 n =
      (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [LSeries.term_of_ne_zero hn, Complex.cpow_two]
    push_cast
    rfl

lemma moebius_reciprocal_square_summable :
    Summable (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) := by
  have hc : Summable (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) 2) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by norm_num)
  have hr := (Complex.hasSum_re hc.hasSum).summable
  simpa only [moebius_term_two, Complex.ofReal_re] using hr

lemma moebius_reciprocal_square_sum :
    (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) = 6 / Real.pi ^ 2 := by
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius
    (s := (2 : ℂ)) (by norm_num : (1 : ℝ) < (2 : ℂ).re)
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by norm_num), riemannZeta_two] at hmul
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2 =
      (6 / Real.pi ^ 2 : ℝ) := by
    have hz : (Real.pi : ℂ) ^ 2 / 6 ≠ 0 := div_ne_zero (pow_ne_zero 2 hpi) (by norm_num)
    calc
      _ = 1 / ((Real.pi : ℂ) ^ 2 / 6) := (eq_div_iff hz).mpr (by simpa [mul_comm] using hmul)
      _ = _ := by push_cast; field_simp [hpi] <;> ring
  have hc : Summable (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) 2) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by norm_num)
  have hsum : HasSum (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) 2)
      (6 / Real.pi ^ 2 : ℝ) := by
    rw [← heq]
    exact hc.hasSum
  have hr := (Complex.hasSum_re hsum).tsum_eq
  simpa only [moebius_term_two, Complex.ofReal_re] using hr

private lemma principal_character_value (S n : ℕ) :
    (1 : DirichletCharacter ℂ S) (n : ZMod S) = if n.Coprime S then 1 else 0 := by
  classical
  by_cases hc : n.Coprime S
  · simp [hc, MulChar.one_apply ((ZMod.isUnit_iff_coprime n S).2 hc)]
  · have hu : ¬ IsUnit (n : ZMod S) := fun h => hc ((ZMod.isUnit_iff_coprime n S).1 h)
    simp [hc, MulChar.map_nonunit _ hu]

lemma principal_lseries_two (S : ℕ) (hS : 0 < S) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ S) (n : ZMod S)) 2 =
      ((Real.pi : ℂ) ^ 2 / 6) * ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℂ) ^ 2) := by
  letI : NeZero S := ⟨hS.ne'⟩
  have hc := DirichletCharacter.LSeries_changeLevel (Nat.one_dvd S)
    (1 : DirichletCharacter ℂ 1) (s := 2) (by norm_num)
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  rw [DirichletCharacter.changeLevel_one, DirichletCharacter.modOne_eq_one,
    LSeries_one_eq_riemannZeta (by norm_num), riemannZeta_two] at hc
  simpa only [hchar, one_mul, Complex.cpow_neg, Complex.cpow_two, one_div] using hc

private lemma restricted_moebius_term_two (S n : ℕ) :
    LSeries.term
      (fun n : ℕ => (1 : DirichletCharacter ℂ S) (n : ZMod S) * (ArithmeticFunction.moebius n : ℂ)) 2 n =
      ((if n.Coprime S then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0 : ℝ) : ℂ) := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_two]
    change ((1 : DirichletCharacter ℂ S) (n : ZMod S) *
      (ArithmeticFunction.moebius n : ℂ)) / (n : ℂ) ^ 2 = _
    rw [principal_character_value]
    by_cases hc : n.Coprime S
    · simp only [if_pos hc, one_mul]
      push_cast
      rfl
    · simp only [if_neg hc, zero_mul, zero_div, Complex.ofReal_zero]

lemma restricted_moebius_reciprocal_square_summable (S : ℕ) :
    Summable (fun n : ℕ => if n.Coprime S then
      (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0) := by
  classical
  have hc := DirichletCharacter.LSeriesSummable_mul (1 : DirichletCharacter ℂ S)
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by norm_num : (1 : ℝ) < (2 : ℂ).re))
  have hcomplex : Summable (LSeries.term
      (fun n : ℕ => (1 : DirichletCharacter ℂ S) (n : ZMod S) * (ArithmeticFunction.moebius n : ℂ)) 2) := hc
  have hr := (Complex.hasSum_re hcomplex.hasSum).summable
  simpa only [restricted_moebius_term_two, Complex.ofReal_re] using hr

lemma restricted_moebius_reciprocal_square_sum (S : ℕ) (hS : 0 < S) :
    (∑' n : ℕ, if n.Coprime S then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0) =
      (6 / Real.pi ^ 2) * ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
  classical
  let χ : DirichletCharacter ℂ S := 1
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hz := DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
  have hvalue : LSeries
      (fun n : ℕ => χ (n : ZMod S) * (ArithmeticFunction.moebius n : ℂ)) 2 =
      (((6 / Real.pi ^ 2) * ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
    calc
      _ = 1 / LSeries (fun n : ℕ => χ (n : ZMod S)) 2 :=
        (eq_div_iff hz).mpr (by rw [mul_comm]; exact hmul)
      _ = 1 / (((Real.pi : ℂ) ^ 2 / 6) * ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℂ) ^ 2)) := by
        rw [show χ = 1 from rfl, principal_lseries_two S hS]
      _ = _ := by
        push_cast
        rw [one_div, mul_inv, Finset.prod_inv_distrib]
        congr 1
        field_simp [show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero] <;> ring
  have hcomplex : Summable (LSeries.term
      (fun n : ℕ => (1 : DirichletCharacter ℂ S) (n : ZMod S) * (ArithmeticFunction.moebius n : ℂ)) 2) :=
    DirichletCharacter.LSeriesSummable_mul (1 : DirichletCharacter ℂ S)
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hsum : HasSum (LSeries.term
      (fun n : ℕ => χ (n : ZMod S) * (ArithmeticFunction.moebius n : ℂ)) 2)
      (((6 / Real.pi ^ 2) * ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [← hvalue]
    exact hcomplex.hasSum
  have hr := (Complex.hasSum_re hsum).tsum_eq
  simpa only [χ, restricted_moebius_term_two, Complex.ofReal_re] using hr

end
end ArtinPrimitiveRoots.TypeII.PD
