import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions

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

theorem good_rational_error (Q : ℝ) (ξ w z : ℂ) (V W D1 E1 : ℂ)
    (hQ : (2 : ℝ) ^ (2000 : ℕ) < Q)
    (hp : eulerNeighborhood ![ξ, w, z])
    (hV : ‖V‖ ≤ Q ^ (-6 * z.re)) (hW : ‖W‖ ≤ Q ^ (-w.re))
    (hD : ‖D1‖ ≤ Q ^ (-ξ.re))
    (hE : ‖E1‖ ≤ Q ^ (4 - 6 * ξ.re - 6 * z.re)) :
    ‖(1 - V) * (1 - W) / (1 - D1) * eulerGoodClosed (Q : ℂ) V W D1 E1 - 1‖ ≤
      128 * Q ^ (-1 - 1 / 4000 : ℝ) := by
  classical
  have hQone : 1 < Q := lt_trans (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by decide : (2000 : ℕ) ≠ 0)) hQ
  have hQpos : 0 < Q := lt_trans zero_lt_one hQone
  have hr : 1 / 2000 ≤ ξ.re ∧ 1 / 2000 ≤ w.re ∧ 1 / 2000 ≤ 6 * z.re ∧
      1 / 2000 ≤ 6 * ξ.re + 6 * z.re - 4 ∧
      -6 * z.re - w.re ≤ -1 - 1 / 4000 ∧
      -ξ.re - 6 * z.re ≤ -1 - 1 / 4000 ∧
      -ξ.re - w.re ≤ -1 - 1 / 4000 ∧
      4 - 6 * ξ.re - 6 * z.re ≤ -1 - 1 / 4000 ∧
      -ξ.re + 1 - w.re - 6 * z.re ≤ -1 - 1 / 4000 := by
    change (998 / 1000 - 1 / 100000 < ξ.re ∧ 3 / 1000 - 1 / 100000 < w.re ∧
      4 / 10 - 1 / 100000 < z.re) ∨
      (998 / 1000 - 1 / 100000 < ξ.re ∧ 95 / 100 - 1 / 100000 < w.re ∧
      16 / 100 - 1 / 100000 < z.re) at hp
    rcases hp with ⟨hx, hw, hz⟩ | ⟨hx, hw, hz⟩ <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hx, hw, hz]
  have hroot : 2 < Q ^ (1 / 2000 : ℝ) := by
    calc
      2 = ((2 : ℝ) ^ (2000 : ℕ)) ^ (1 / 2000 : ℝ) := by
        rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ < _ := Real.rpow_lt_rpow (by positivity) hQ (by norm_num)
  have hsmall : Q ^ (-1 / 2000 : ℝ) < 1 / 2 := by
    calc
      Q ^ (-1 / 2000 : ℝ) = (Q ^ (1 / 2000 : ℝ))⁻¹ := by
        rw [show (-1 / 2000 : ℝ) = -(1 / 2000 : ℝ) by ring, Real.rpow_neg hQpos.le]
      _ < (2 : ℝ)⁻¹ :=
        (inv_lt_inv₀ (Real.rpow_pos_of_pos hQpos _) (by norm_num)).2 hroot
      _ = 1 / 2 := by norm_num
  have hsmallbound (a : ℂ) (s : ℝ) (ha : ‖a‖ ≤ Q ^ s) (hs : s ≤ -1 / 2000) :
      ‖a‖ < 1 / 2 :=
    lt_of_le_of_lt (ha.trans (Real.rpow_le_rpow_of_exponent_le hQone.le hs)) hsmall
  have hVs : ‖V‖ < 1 / 2 := hsmallbound V _ hV (by linarith [hr.2.2.1])
  have hWs : ‖W‖ < 1 / 2 := hsmallbound W _ hW (by linarith [hr.2.1])
  have hDs : ‖D1‖ < 1 / 2 := hsmallbound D1 _ hD (by linarith [hr.1])
  have hEs : ‖E1‖ < 1 / 2 := hsmallbound E1 _ hE (by linarith [hr.2.2.2.1])
  have hVne : 1 - V ≠ 0 := by
    intro h; have heq : V = 1 := (sub_eq_zero.mp h).symm
    norm_num [heq] at hVs
  have hWne : 1 - W ≠ 0 := by
    intro h; have heq : W = 1 := (sub_eq_zero.mp h).symm
    norm_num [heq] at hWs
  have hDne : 1 - D1 ≠ 0 := by
    intro h; have heq : D1 = 1 := (sub_eq_zero.mp h).symm
    norm_num [heq] at hDs
  have hEne : 1 - E1 ≠ 0 := by
    intro h; have heq : E1 = 1 := (sub_eq_zero.mp h).symm
    norm_num [heq] at hEs
  let t : ℝ := Q ^ (-1 - 1 / 4000 : ℝ)
  have ht : 0 ≤ t := Real.rpow_nonneg hQpos.le _
  have hmul (a b : ℂ) (s r : ℝ) (ha : ‖a‖ ≤ Q ^ s) (hb : ‖b‖ ≤ Q ^ r) :
      ‖a * b‖ ≤ Q ^ (s + r) := by
    rw [norm_mul]
    calc
      _ ≤ Q ^ s * Q ^ r := mul_le_mul ha hb (norm_nonneg _) (Real.rpow_nonneg hQpos.le _)
      _ = _ := (Real.rpow_add hQpos _ _).symm
  have hto (a : ℂ) (s : ℝ) (ha : ‖a‖ ≤ Q ^ s) (hs : s ≤ -1 - 1 / 4000) :
      ‖a‖ ≤ t := ha.trans (Real.rpow_le_rpow_of_exponent_le hQone.le hs)
  have hVW : ‖V * W‖ ≤ t := hto _ _ (hmul V W _ _ hV hW) (by linarith only [hr.2.2.2.2.1])
  have hDV : ‖D1 * V‖ ≤ t := hto _ _ (hmul D1 V _ _ hD hV) (by linarith only [hr.2.2.2.2.2.1])
  have hDW : ‖D1 * W‖ ≤ t := hto _ _ (hmul D1 W _ _ hD hW) (by linarith only [hr.2.2.2.2.2.2.1])
  have hEt : ‖E1‖ ≤ t := hto _ _ hE hr.2.2.2.2.2.2.2.1
  have hQm : ‖(Q : ℂ) - 1‖ ≤ Q ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    have heq : (Q : ℂ) - 1 = ((Q - 1 : ℝ) : ℂ) := by simp
    rw [heq, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hQone.le)]
    linarith
  have hDQWV : ‖D1 * ((Q : ℂ) - 1) * W * V‖ ≤ t :=
    hto _ _ (hmul _ V _ _ (hmul _ W _ _ (hmul D1 _ _ _ hD hQm) hW) hV)
      (by linarith only [hr.2.2.2.2.2.2.2.2])
  have hQi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hQpos.le]
    exact (inv_le_one₀ hQpos).2 hQone.le
  have hEQ : ‖E1 * (Q : ℂ)⁻¹‖ ≤ t := by
    rw [norm_mul]
    calc
      _ ≤ t * 1 := mul_le_mul hEt hQi (norm_nonneg _) ht
      _ = t := mul_one t
  have hWpow : ‖W ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg W) (by linarith only [hWs])
  have hEW : ‖E1 * W ^ 2‖ ≤ t := by
    rw [norm_mul]
    calc
      _ ≤ t * 1 := mul_le_mul hEt hWpow (norm_nonneg _) ht
      _ = t := mul_one t
  have hDVW : ‖(D1 * V) * W‖ ≤ t := by
    rw [norm_mul]
    calc
      _ ≤ t * 1 := mul_le_mul hDV (by linarith : ‖W‖ ≤ 1) (norm_nonneg _) ht
      _ = t := mul_one t
  have hDE : ‖D1 * E1‖ ≤ t := by
    rw [norm_mul]
    calc
      _ ≤ 1 * t := mul_le_mul (by linarith : ‖D1‖ ≤ 1) hEt (norm_nonneg _) (by norm_num)
      _ = t := one_mul t
  have h1V : ‖1 - V‖ ≤ 2 := (norm_sub_le _ _).trans (by simpa using (show 1 + ‖V‖ ≤ 2 by linarith))
  have h1W : ‖1 - W‖ ≤ 2 := (norm_sub_le _ _).trans (by simpa using (show 1 + ‖W‖ ≤ 2 by linarith))
  have htail (a b : ℂ) (ha : ‖a‖ ≤ t) (hb : ‖b‖ ≤ 2) : ‖-(a * b)‖ ≤ 2 * t := by
    rw [norm_neg, norm_mul]
    calc
      _ ≤ t * 2 := mul_le_mul ha hb (norm_nonneg _) ht
      _ = _ := by ring
  let f : Fin 9 → ℂ := ![-(V * W), E1, -((E1 * (Q : ℂ)⁻¹) * (1 - W)),
    -((E1 * W ^ 2) * (1 - V)), D1 * V, D1 * W, -((D1 * V) * W),
    -(D1 * E1), -((D1 * ((Q : ℂ) - 1) * W * V) * (1 - W))]
  have hf : ∀ i, ‖f i‖ ≤ 2 * t := by
    intro i
    fin_cases i
    · change ‖-(V * W)‖ ≤ 2 * t
      rw [norm_neg]
      exact hVW.trans (by linarith only [ht])
    · change ‖E1‖ ≤ 2 * t
      exact hEt.trans (by linarith only [ht])
    · change ‖-((E1 * (Q : ℂ)⁻¹) * (1 - W))‖ ≤ 2 * t
      exact htail _ _ hEQ h1W
    · change ‖-((E1 * W ^ 2) * (1 - V))‖ ≤ 2 * t
      exact htail _ _ hEW h1V
    · change ‖D1 * V‖ ≤ 2 * t
      exact hDV.trans (by linarith only [ht])
    · change ‖D1 * W‖ ≤ 2 * t
      exact hDW.trans (by linarith only [ht])
    · change ‖-((D1 * V) * W)‖ ≤ 2 * t
      rw [norm_neg]
      exact hDVW.trans (by linarith only [ht])
    · change ‖-(D1 * E1)‖ ≤ 2 * t
      rw [norm_neg]
      exact hDE.trans (by linarith only [ht])
    · change ‖-((D1 * ((Q : ℂ) - 1) * W * V) * (1 - W))‖ ≤ 2 * t
      exact htail _ _ hDQWV h1W
  have hsum : ‖∑ i, f i‖ ≤ 18 * t := by
    calc
      _ ≤ ∑ i : Fin 9, ‖f i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 9, 2 * t := Finset.sum_le_sum (fun i _ => hf i)
      _ = _ := by simp; ring
  have halg : (1 - V) * (1 - W) / (1 - D1) * eulerGoodClosed (Q : ℂ) V W D1 E1 - 1 =
      (∑ i, f i) / ((1 - D1) * (1 - E1)) := by
    simp [Fin.sum_univ_succ, f, eulerGoodClosed]
    field_simp [hVne, hWne, hDne, hEne, Complex.ofReal_ne_zero.mpr hQpos.ne']
    <;> ring
  have hdenD : 1 / 2 ≤ ‖1 - D1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) D1
    norm_num only [norm_one] at h
    linarith
  have hdenE : 1 / 2 ≤ ‖1 - E1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) E1
    norm_num only [norm_one] at h
    linarith
  have hden : 1 / 4 ≤ ‖(1 - D1) * (1 - E1)‖ := by
    rw [norm_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hdenD) (sub_nonneg.mpr hdenE)]
  have hdenpos : 0 < ‖(1 - D1) * (1 - E1)‖ := by linarith
  rw [halg, norm_div]
  apply (div_le_iff₀ hdenpos).2
  change ‖∑ i, f i‖ ≤ 128 * t * ‖(1 - D1) * (1 - E1)‖
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hden)]


end ArtinPrimitiveRoots.Proofs.a2_euler_sol
