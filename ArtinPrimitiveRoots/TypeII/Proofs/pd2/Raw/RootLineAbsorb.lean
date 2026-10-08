import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootPowerBound

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

private lemma pd2a_exp_pow_nat (a : ℝ) (n : ℕ) :
    (Real.exp a)^n=Real.exp (a*(n:ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ih,←Real.exp_add]
    congr 1
    push_cast
    ring

lemma pd2a_line_error_absorb (δ CK : ℝ) (hδ : 0<δ) (hCK : 0<CK) :
    ∃ x₀ : ℝ,2 ≤ x₀ ∧ ∀ x : ℝ,x₀ ≤ x → ∀ M : ℝ,Real.rpow x δ ≤ M →
      ∀ S : ℕ,(S:ℝ) ≤ Real.exp (CK*Real.rpow (Real.log x) (98/100:ℝ)) →
      Real.rpow M (-(1/200:ℝ))*(S:ℝ)^6 ≤ Real.rpow x (-(δ/1000)) := by
  obtain ⟨L₁,hGrowth⟩ := Filter.tendsto_atTop_atTop.mp
    (_root_.tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/50)) (1500*CK/δ)
  let L₀ := max 1 L₁
  let x₀ := max 2 (Real.exp L₀)
  refine ⟨x₀,le_max_left _ _,?_⟩
  intro x hx M hM S hS
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hxp : 0<x := by linarith
  have hL₀ : L₀ ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxp).2 ((le_max_right _ _).trans hx)
  have hL1 : 1 ≤ Real.log x := (le_max_left _ _).trans hL₀
  have hLpos : 0<Real.log x := by linarith
  have hL₁ : L₁ ≤ Real.log x := (le_max_right _ _).trans hL₀
  have hD : 1500*CK/δ ≤ Real.rpow (Real.log x) (1/50:ℝ) := hGrowth _ hL₁
  have hSum : Real.rpow (Real.log x) (1/50:ℝ)*Real.rpow (Real.log x) (98/100:ℝ)=Real.log x := by
    calc
      _ = Real.rpow (Real.log x) ((1/50:ℝ)+98/100) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by norm_num
  have hNon : 0 ≤ Real.rpow (Real.log x) (98/100:ℝ) := Real.rpow_nonneg hLpos.le _
  have hProd := mul_le_mul_of_nonneg_right hD hNon
  rw [hSum] at hProd
  have hGap : 6*CK*Real.rpow (Real.log x) (98/100:ℝ) ≤ (δ/250)*Real.log x := by
    have hm := mul_le_mul_of_nonneg_left hProd (by positivity : (0:ℝ)≤δ/250)
    have he : (δ/250)*(1500*CK/δ)=6*CK := by field_simp;ring
    rw [←mul_assoc,he] at hm
    exact hm
  have hS6 : (S:ℝ)^6 ≤ Real.exp (6*CK*Real.rpow (Real.log x) (98/100:ℝ)) := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg S) hS 6
    apply hp.trans_eq
    rw [pd2a_exp_pow_nat]
    congr 1
    norm_num
    ring
  have hxpow : 0<Real.rpow x δ := Real.rpow_pos_of_pos hxp _
  have hMp : 0<M := hxpow.trans_le hM
  have hNeg : Real.rpow M (-(1/200:ℝ)) ≤ Real.rpow x (-(δ/200)) := by
    calc
      _ ≤ Real.rpow (Real.rpow x δ) (-(1/200:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hxpow hM (by norm_num)
      _ = Real.rpow x (δ*(-(1/200:ℝ))) := (Real.rpow_mul hxp.le _ _).symm
      _ = _ := by congr 1;ring
  have hm := mul_le_mul hNeg hS6 (pow_nonneg (Nat.cast_nonneg S) 6)
    (Real.rpow_nonneg hxp.le (-(δ/200)))
  apply hm.trans
  have he1 : Real.rpow x (-(δ/200))=Real.exp (Real.log x*(-(δ/200))) := Real.rpow_def_of_pos hxp _
  have he2 : Real.rpow x (-(δ/1000))=Real.exp (Real.log x*(-(δ/1000))) := Real.rpow_def_of_pos hxp _
  rw [he1,he2,←Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

end ArtinPrimitiveRoots.TypeII.PD
