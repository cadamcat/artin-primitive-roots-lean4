import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ArcGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
open scoped Topology
set_option autoImplicit false

lemma pd7d_log_polynomial_below_stretched_exp (A s c B : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ B*Real.rpow L A < Real.exp (c*Real.rpow L s) := by
  have heps : 0 < c/(2*(|A|+1)) := by positivity
  have hlittle := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hs).bound heps
  have hgrow := (tendsto_rpow_atTop hs).eventually_ge_atTop (2*(|Real.log (max 1 B)|+1)/c)
  filter_upwards [hlittle,hgrow,eventually_ge_atTop (1 : ℝ)] with L hl hg hL
  have hLp : 0 < L := by linarith
  have hLlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hPow : 0 < Real.rpow L s := Real.rpow_pos_of_pos hLp _
  change 2*(|Real.log (max 1 B)|+1)/c ≤ Real.rpow L s at hg
  have hl' : Real.log L ≤ (c/(2*(|A|+1)))*Real.rpow L s := by
    change ‖Real.rpow (Real.log L) 1‖ ≤ (c/(2*(|A|+1)))*‖Real.rpow L s‖ at hl
    have hone : Real.rpow (Real.log L) 1 = Real.log L := Real.rpow_one _
    rw [hone] at hl
    simpa only [Real.norm_eq_abs,abs_of_nonneg hLlog,abs_of_pos hPow] using hl
  have hbpos : 0 < max 1 B := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
  have hlog : Real.log (max 1 B) + A*Real.log L < c*Real.rpow L s := by
    have hmul := mul_le_mul_of_nonneg_left hl' (abs_nonneg A)
    have hAg := mul_le_mul_of_nonneg_right (le_abs_self A) hLlog
    have hbound : |A| *(c/(2*(|A|+1))) ≤ c/2 := by
      have hden : 0 < 2*(|A|+1) := by positivity
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).2
      nlinarith [abs_nonneg A]
    have hbound' := mul_le_mul_of_nonneg_right hbound hPow.le
    have hG := (div_le_iff₀ hc).mp hg
    nlinarith [le_abs_self (Real.log (max 1 B))]
  refine ⟨hL, ?_⟩
  calc
    _ ≤ (max 1 B)*Real.rpow L A := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hLp.le A)
    _ = Real.exp (Real.log (max 1 B)+A*Real.log L) := by
      rw [Real.exp_add,Real.exp_log hbpos]
      have hp : Real.rpow L A = Real.exp (A*Real.log L) := by
        convert Real.rpow_def_of_pos hLp A using 1 <;> congr 1 <;> ring
      exact congrArg (fun z : ℝ => (max 1 B)*z) hp
    _ < _ := Real.exp_lt_exp.mpr hlog

lemma pd7d_arc_thresholds (A₀ : ℝ) (K : ℕ) (a : Fin K → ℝ) (ha : ValidBands K a) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x ∧
      (∀ i : Fin K, Real.rpow (Real.log x) A₀ < Real.exp (Real.rpow (Real.log x) (a i))) ∧
      Real.rpow (Real.log x) A₀ ≤ roughCutoff x ∧
      ∀ Y ∈ dyadicScales x K, 4*(Real.rpow (Real.log x) A₀)^3 < Y := by
  have hmarked : ∀ᶠ L : ℝ in atTop, ∀ i : Fin K,
      Real.rpow L A₀ < Real.exp (Real.rpow L (a i)) := by
    apply Filter.eventually_all.mpr
    intro i
    have hh := pd7d_log_polynomial_below_stretched_exp A₀ (a i) 1 1 (by have hi := ha.2.1 i; linarith) (by norm_num)
    simpa only [one_mul] using hh.mono (fun L h => h.2)
  have hrough := pd7d_log_polynomial_below_stretched_exp A₀ (24/100 : ℝ) 1 1 (by norm_num) (by norm_num)
  have harcs := pd7d_log_polynomial_below_stretched_exp (3*A₀) (1/10 : ℝ) (1/20 : ℝ) 4 (by norm_num) (by norm_num)
  have hall : ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ (∀ i : Fin K,
      Real.rpow L A₀ < Real.exp (Real.rpow L (a i))) ∧
      Real.rpow L A₀ ≤ Real.exp (Real.rpow L (24/100 : ℝ)) ∧
      4*(Real.rpow L A₀)^3 < Real.exp ((1/20 : ℝ)*Real.rpow L (1/10 : ℝ)) := by
    filter_upwards [hmarked,hrough,harcs] with L hm hr ha'
    refine ⟨hr.1,hm,by simpa only [one_mul] using hr.2.le,?_⟩
    have hLpos : 0 < L := by linarith [hr.1]
    have hp : (Real.rpow L A₀)^3 = Real.rpow L (3*A₀) := by
      calc
        _ = Real.rpow (Real.rpow L A₀) (3 : ℝ) := (Real.rpow_natCast _ 3).symm
        _ = Real.rpow L (A₀*3) := (Real.rpow_mul hLpos.le _ _).symm
        _ = _ := by congr 1; ring
    rw [hp]
    exact ha'.2
  filter_upwards [Real.tendsto_log_atTop.eventually hall] with x hx
  refine ⟨hx.1,hx.2.1,hx.2.2.1,?_⟩
  intro Y hY
  have hb := (Finset.mem_filter.mp hY).2.1
  have hYp : 0 < Y := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hY).1
    positivity
  have hh := Real.exp_le_exp.mpr hb
  rw [Real.exp_log hYp] at hh
  exact hx.2.2.2.trans_le hh
end ArtinPrimitiveRoots.TypeII.PD
