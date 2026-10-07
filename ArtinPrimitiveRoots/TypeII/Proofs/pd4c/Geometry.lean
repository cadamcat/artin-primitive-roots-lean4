import ArtinPrimitiveRoots.TypeII.PD.Memory
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Finset Int MeasureTheory

local instance decidableOfProposition (p : Prop) : Decidable p := Classical.propDecidable p

private theorem int_abs_bound_mem_Icc_floor (A : ℝ) (_hA : 1 ≤ A) (q : ℤ)
    (hq : |(q : ℝ)| ≤ A) : q ∈ Finset.Icc (-⌊A⌋) ⌊A⌋ := by
  have hqlo : -A ≤ (q : ℝ) := (abs_le.mp hq).1
  have hqhi : (q : ℝ) ≤ A := (abs_le.mp hq).2
  have hqneg : ((-q : ℤ) : ℝ) ≤ A := by simpa using (show -(q : ℝ) ≤ A by linarith)
  have hqfloor : q ≤ ⌊A⌋ := Int.le_floor.mpr hqhi
  have hqnegfloor : -q ≤ ⌊A⌋ := Int.le_floor.mpr hqneg
  exact Finset.mem_Icc.mpr ⟨by omega, hqfloor⟩

private theorem int_floor_box_card_le (A : ℝ) (hA : 1 ≤ A) :
    ((Finset.Icc (-⌊A⌋) ⌊A⌋).card : ℝ) ≤ 2 * A + 1 := by
  have hfloor : (⌊A⌋ : ℝ) ≤ A := Int.floor_le A
  have hA' : ((1 : ℤ) : ℝ) ≤ A := by exact_mod_cast hA
  have hfloor_pos : 1 ≤ ⌊A⌋ := Int.le_floor.mpr hA'
  have hinterval : -⌊A⌋ ≤ ⌊A⌋ + 1 := by linarith [hfloor_pos]
  have hcard : (((Finset.Icc (-⌊A⌋) ⌊A⌋).card : ℕ) : ℤ) =
      ⌊A⌋ + 1 - (-⌊A⌋) := by
    exact Int.card_Icc_of_le (-⌊A⌋) ⌊A⌋ hinterval
  have hcast : ((Finset.Icc (-⌊A⌋) ⌊A⌋).card : ℝ) = 2 * (⌊A⌋ : ℝ) + 1 := by
    have h := congrArg (fun n : ℤ => (n : ℝ)) hcard
    push_cast at h
    nlinarith
  rw [hcast]
  nlinarith

private theorem int_floor_box_modEq_card_le (D : ℝ) (hD : 1 ≤ D)
    (p : ℕ) (hp : p.Prime) (r : ℤ) :
    ((Finset.Icc (-⌊D⌋) ⌊D⌋).filter (fun y => y ≡ r [ZMOD p])).card ≤
      2 * D / (p : ℝ) + 3 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hn : 0 ≤ (⌊D⌋ : ℤ) := by
    have hDcast : ((0 : ℤ) : ℝ) ≤ D := le_trans (by norm_num) hD
    exact Int.le_floor.mpr hDcast
  have hnUpper : (⌊D⌋ : ℝ) ≤ D := Int.floor_le D
  have hIccIoc : (Finset.Icc (-⌊D⌋) ⌊D⌋).filter
        (fun y => y ≡ r [ZMOD p]) =
      (Finset.Ioc (-⌊D⌋ - 1) ⌊D⌋).filter
        (fun y => y ≡ r [ZMOD p]) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor <;> intro h
    · exact ⟨by omega, h.2⟩
    · exact ⟨by omega, h.2⟩
  have hpInt : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hformula := @Int.Ioc_filter_modEq_card (-⌊D⌋ - 1) ⌊D⌋ (p : ℤ) hpInt r
  have hformulaR :
      (((Finset.Ioc (-⌊D⌋ - 1) ⌊D⌋).filter
          (fun y => y ≡ r [ZMOD p])).card : ℝ) =
        ((max
          (⌊((⌊D⌋ : ℤ) - r : ℚ) / (p : ℚ)⌋ -
            ⌊((-⌊D⌋ - 1 - r : ℤ) : ℚ) / (p : ℚ)⌋) 0 : ℤ) : ℝ) := by
    exact_mod_cast hformula
  rw [hIccIoc]
  rw [hformulaR]
  have hU : ((⌊((⌊D⌋ : ℤ) - r : ℚ) / (p : ℚ)⌋ : ℤ) : ℝ) ≤
      (((⌊D⌋ : ℤ) - r : ℤ) : ℝ) / p := by
    have h := Int.floor_le (((⌊D⌋ : ℤ) - r : ℤ) / (p : ℚ))
    exact_mod_cast h
  have hL : (((-⌊D⌋ - 1 - r : ℤ) : ℚ) / (p : ℚ)) - 1 <
      ((⌊((-⌊D⌋ - 1 - r : ℤ) : ℚ) / (p : ℚ)⌋ : ℤ) : ℝ) := by
    have h := Int.sub_one_lt_floor (((-⌊D⌋ - 1 - r : ℤ) : ℚ) / (p : ℚ))
    exact_mod_cast h
  have hdiff :
      ((⌊((⌊D⌋ : ℤ) - r : ℚ) / (p : ℚ)⌋ : ℤ) : ℝ) -
        ((⌊((-⌊D⌋ - 1 - r : ℤ) : ℚ) / (p : ℚ)⌋ : ℤ) : ℝ) ≤
      (2 * (⌊D⌋ : ℝ) + 1) / p + 1 := by
    have hwidth :
        ((((⌊D⌋ : ℤ) - r : ℤ) : ℝ) / p) -
          (((-⌊D⌋ - 1 - r : ℤ) : ℚ) / (p : ℚ)) =
        (2 * (⌊D⌋ : ℝ) + 1) / p := by
      push_cast
      field_simp [hpPos.ne']
      ring
    linarith [hU, hL, hwidth]
  have hDbound : (2 * (⌊D⌋ : ℝ) + 1) / p + 1 ≤ 2 * D / p + 3 := by
    have hnum : 2 * (⌊D⌋ : ℝ) + 1 ≤ 2 * D + 1 := by nlinarith [hnUpper]
    have hdiv := div_le_div_of_nonneg_right hnum hpPos.le
    have hpge : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hpInv : 1 / (p : ℝ) ≤ 1 :=
      (div_le_iff₀ hpPos).2 (by simpa using hpge)
    have hsplit : (2 * D + 1) / p = 2 * D / p + 1 / p := by
      field_simp [hpPos.ne'] <;> ring
    nlinarith [hdiv, hpInv, hsplit]
  have hmax : (max
      (⌊((⌊D⌋ : ℤ) - r : ℚ) / (p : ℚ)⌋ -
        ⌊((-⌊D⌋ - 1 - r : ℤ) : ℚ) / (p : ℚ)⌋) 0 : ℤ) ≤
      2 * D / (p : ℝ) + 3 := by
    rw [Int.cast_max]
    apply max_le
    · rw [Int.cast_sub]
      exact le_trans hdiff hDbound
    · have hnum : 0 ≤ 2 * D := by nlinarith [hD]
      have hquot : 0 ≤ 2 * D / (p : ℝ) := div_nonneg hnum hpPos.le
      linarith
  exact_mod_cast hmax

private theorem product_filter_card_le_left (X Y : Finset ℤ) (P : ℤ → ℤ → Prop)
    (C : ℝ)
    (hbound : ∀ x, (({y : ℤ | y ∈ Y ∧ P x y}.ncard : ℝ)) ≤ C) :
    (((X ×ˢ Y).filter fun q => P q.1 q.2).card : ℝ) ≤
      (X.card : ℝ) * C := by
  classical
  let S := (X ×ˢ Y).filter fun q : ℤ × ℤ => P q.1 q.2
  have hmap : (S : Set (ℤ × ℤ)).MapsTo Prod.fst (X : Set ℤ) := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqProd, _⟩
    exact (Finset.mem_product.mp hqProd).1
  have hcard := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := S) (t := X) hmap
  have hfiber (x : ℤ) (hx : x ∈ X) :
      (S.filter fun q => q.1 = x).card = (Y.filter fun y => P x y).card := by
    apply Finset.card_bij (fun q _ => q.2)
    · intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqS, hqx⟩
      rcases Finset.mem_filter.mp hqS with ⟨hqProd, hqP⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hqProd).2,
        by simpa [hqx] using hqP⟩
    · intro q hq q' hq' heq
      rcases Finset.mem_filter.mp hq with ⟨_, hqx⟩
      rcases Finset.mem_filter.mp hq' with ⟨_, hq'x⟩
      apply Prod.ext
      · exact hqx.trans hq'x.symm
      · exact heq
    · intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyY, hP⟩
      have hpair : (x, y) ∈ S :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hx, hyY⟩, hP⟩
      have hpairFiber : (x, y) ∈ S.filter (fun q => q.1 = x) :=
        Finset.mem_filter.mpr ⟨hpair, rfl⟩
      exact ⟨(x, y), hpairFiber, rfl⟩
  have hfiberSet (x : ℤ) (hx : x ∈ X) :
      ((S.filter fun q => q.1 = x).card : ℝ) =
        (({y : ℤ | y ∈ Y ∧ P x y}.ncard : ℝ)) := by
    have hset : ((Y.filter fun y => P x y : Finset ℤ) : Set ℤ) =
        {y : ℤ | y ∈ Y ∧ P x y} := by
      ext y
      simp
    calc
      ((S.filter fun q => q.1 = x).card : ℝ) =
          ((Y.filter fun y => P x y).card : ℝ) := by exact_mod_cast hfiber x hx
      _ = (((Y.filter fun y => P x y : Finset ℤ) : Set ℤ).ncard : ℝ) := by
        exact_mod_cast (Set.ncard_coe_finset (Y.filter fun y => P x y)).symm
      _ = (({y : ℤ | y ∈ Y ∧ P x y}.ncard : ℝ)) := by
        rw [← hset]
  have hcardReal :
      (S.card : ℝ) = ∑ x ∈ X, ((S.filter fun q => q.1 = x).card : ℝ) := by
    exact_mod_cast hcard
  calc
    (((X ×ˢ Y).filter fun q => P q.1 q.2).card : ℝ) = (S.card : ℝ) := by rfl
    _ = ∑ x ∈ X, ((S.filter fun q => q.1 = x).card : ℝ) := hcardReal
    _ ≤ ∑ x ∈ X, C := by
      apply Finset.sum_le_sum
      intro x hx
      rw [hfiberSet x hx]
      exact hbound x
    _ = (X.card : ℝ) * C := by simp [Finset.sum_const, nsmul_eq_mul]

private theorem line_fiber_card_le {p : ℕ} (hp : p.Prime) (a b : ZMod p)
    (hb : b ≠ 0) (x : ℤ) (D : ℝ) (hD : 1 ≤ D) :
    ((Finset.Icc (-⌊D⌋) ⌊D⌋ : Finset ℤ).filter
      (fun y : ℤ => a * (x : ZMod p) + b * (y : ZMod p) = 0)).card ≤
        2 * D / (p : ℝ) + 3 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let r₀ : ZMod p := -(a * (x : ZMod p)) / b
  let r : ℤ := (r₀.val : ℤ)
  have hr : (r : ZMod p) = r₀ := by
    simp [r]
  have hsubset :
      (Finset.Icc (-⌊D⌋) ⌊D⌋ : Finset ℤ).filter
          (fun y : ℤ => a * (x : ZMod p) + b * (y : ZMod p) = 0) ⊆
        (Finset.Icc (-⌊D⌋) ⌊D⌋ : Finset ℤ).filter
          (fun y : ℤ => Int.ModEq (p : ℤ) y r) := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hyBox, heq⟩
    have hmul : b * (y : ZMod p) = -(a * (x : ZMod p)) := by
      linear_combination heq
    have hrmul : b * r₀ = -(a * (x : ZMod p)) := by
      dsimp [r₀]
      field_simp [hb]
    have hsolve : (y : ZMod p) = r₀ :=
      (mul_left_cancel₀ hb) (hmul.trans hrmul.symm)
    have hsolve' : (y : ZMod p) = (r : ZMod p) := by rw [hr]; exact hsolve
    have hmod : Int.ModEq (p : ℤ) y r :=
      (ZMod.intCast_eq_intCast_iff y r p).1 hsolve'
    exact Finset.mem_filter.mpr ⟨hyBox, hmod⟩
  calc
    (((Finset.Icc (-⌊D⌋) ⌊D⌋ : Finset ℤ).filter
      (fun y : ℤ => a * (x : ZMod p) + b * (y : ZMod p) = 0)).card : ℝ) ≤
      (((Finset.Icc (-⌊D⌋) ⌊D⌋ : Finset ℤ).filter
        (fun y : ℤ => Int.ModEq (p : ℤ) y r)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubset
    _ ≤ 2 * D / (p : ℝ) + 3 := int_floor_box_modEq_card_le D hD p hp r

private theorem box_line_count_le_of_second_nezero (p : ℕ) (hp : p.Prime)
    (A D : ℝ) (hA : 1 ≤ A) (hD : 1 ≤ D)
    (a b : ZMod p) (hb : b ≠ 0) :
    (({q : ℤ × ℤ | |(q.1 : ℝ)| ≤ A ∧ |(q.2 : ℝ)| ≤ D ∧
      a * (q.1 : ZMod p) + b * (q.2 : ZMod p) = 0}.ncard : ℝ)) ≤
        12 * (A * D / (p : ℝ) + max A D) := by
  let X : Finset ℤ := Finset.Icc (-⌊A⌋) ⌊A⌋
  let Y : Finset ℤ := Finset.Icc (-⌊D⌋) ⌊D⌋
  let P (x y : ℤ) : Prop := a * (x : ZMod p) + b * (y : ZMod p) = 0
  letI : DecidablePred (fun q : ℤ × ℤ => P q.1 q.2) :=
    fun q => Classical.propDecidable (P q.1 q.2)
  let S : Finset (ℤ × ℤ) := (X ×ˢ Y).filter fun q => P q.1 q.2
  have hsub : {q : ℤ × ℤ | |(q.1 : ℝ)| ≤ A ∧ |(q.2 : ℝ)| ≤ D ∧
      a * (q.1 : ZMod p) + b * (q.2 : ZMod p) = 0} ⊆ (S : Set (ℤ × ℤ)) := by
    intro q hq
    rcases hq with ⟨hqA, hqD, hline⟩
    have hqX : q.1 ∈ X := by
      exact int_abs_bound_mem_Icc_floor A hA q.1 hqA
    have hqY : q.2 ∈ Y := by
      exact int_abs_bound_mem_Icc_floor D hD q.2 hqD
    change q ∈ (S : Set (ℤ × ℤ))
    simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_product, P]
    exact ⟨⟨hqX, hqY⟩, hline⟩
  have htargetCard :
      {q : ℤ × ℤ | |(q.1 : ℝ)| ≤ A ∧ |(q.2 : ℝ)| ≤ D ∧
        a * (q.1 : ZMod p) + b * (q.2 : ZMod p) = 0}.ncard ≤ S.card := by
    calc
      _ ≤ (S : Set (ℤ × ℤ)).ncard := Set.ncard_le_ncard hsub S.finite_toSet
      _ = S.card := by simp
  have hbound (x : ℤ) :
      (({y : ℤ | y ∈ Y ∧ a * (x : ZMod p) + b * (y : ZMod p) = 0}.ncard : ℝ)) ≤
        2 * D / (p : ℝ) + 3 := by
    have hset : ((Y.filter
        (fun y : ℤ => a * (x : ZMod p) + b * (y : ZMod p) = 0) : Finset ℤ) : Set ℤ) =
        {y : ℤ | y ∈ Y ∧ a * (x : ZMod p) + b * (y : ZMod p) = 0} := by
      ext y
      simp
    let U : Finset ℤ :=
      Y.filter (fun y : ℤ => a * (x : ZMod p) + b * (y : ZMod p) = 0)
    calc
      _ = ((U : Set ℤ).ncard : ℝ) := by rw [← hset]
      _ = (U.card : ℝ) := by rw [Set.ncard_coe_finset]
      _ ≤ 2 * D / (p : ℝ) + 3 := by
        simpa [Y] using line_fiber_card_le hp a b hb x D hD
  have hprod : (S.card : ℝ) ≤ (X.card : ℝ) * (2 * D / (p : ℝ) + 3) := by
    change (((X ×ˢ Y).filter fun q => P q.1 q.2).card : ℝ) ≤
      (X.card : ℝ) * (2 * D / (p : ℝ) + 3)
    exact product_filter_card_le_left X Y P (2 * D / (p : ℝ) + 3) hbound
  have hX : (X.card : ℝ) ≤ 2 * A + 1 := by
    simpa [X] using int_floor_box_card_le A hA
  have hbase : 0 ≤ 2 * D / (p : ℝ) + 3 := by positivity
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hDdiv : 2 * D / (p : ℝ) ≤ D := by
    apply (div_le_iff₀ hpPos).2
    calc
      2 * D ≤ (p : ℝ) * D :=
        mul_le_mul_of_nonneg_right hpTwo (by linarith [hD])
      _ = D * p := by ring
  have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1) hA
  have hM : 0 ≤ max A D := le_trans hA0 (le_max_left A D)
  have hT : 0 ≤ A * D / (p : ℝ) := by positivity
  have harea : (2 * A + 1) * (2 * D / (p : ℝ) + 3) ≤
      12 * (A * D / (p : ℝ) + max A D) := by
    calc
      (2 * A + 1) * (2 * D / (p : ℝ) + 3) =
          4 * (A * D / (p : ℝ)) + 2 * D / (p : ℝ) + 6 * A + 3 := by ring
      _ ≤ 4 * (A * D / (p : ℝ)) + D + 6 * A + 3 := by nlinarith [hDdiv]
      _ ≤ 4 * (A * D / (p : ℝ)) + 10 * max A D := by
        have hAmax : A ≤ max A D := le_max_left _ _
        have hDmax : D ≤ max A D := le_max_right _ _
        nlinarith [hAmax, hDmax, hA, hD]
      _ ≤ 12 * (A * D / (p : ℝ) + max A D) := by nlinarith [hT, hM]
  calc
    ({q : ℤ × ℤ | |(q.1 : ℝ)| ≤ A ∧ |(q.2 : ℝ)| ≤ D ∧
      a * (q.1 : ZMod p) + b * (q.2 : ZMod p) = 0}.ncard : ℝ) ≤
        (S.card : ℝ) := by exact_mod_cast htargetCard
    _ ≤ (X.card : ℝ) * (2 * D / (p : ℝ) + 3) := hprod
    _ ≤ (2 * A + 1) * (2 * D / (p : ℝ) + 3) :=
        mul_le_mul_of_nonneg_right hX hbase
    _ ≤ 12 * (A * D / (p : ℝ) + max A D) := harea

theorem box_line_count_le (p : ℕ) (hp : p.Prime) (A D : ℝ)
    (hA : 1 ≤ A) (hD : 1 ≤ D) (a b : ZMod p) (hab : a ≠ 0 ∨ b ≠ 0) :
    (({q : ℤ × ℤ | |(q.1 : ℝ)| ≤ A ∧ |(q.2 : ℝ)| ≤ D ∧
      a * (q.1 : ZMod p) + b * (q.2 : ZMod p) = 0}.ncard : ℝ)) ≤
        12 * (A * D / (p : ℝ) + max A D) := by
  by_cases hb : b ≠ 0
  · exact box_line_count_le_of_second_nezero p hp A D hA hD a b hb
  · have hb0 : b = 0 := by simpa using hb
    have ha : a ≠ 0 := by
      intro ha0
      exact hab.elim (fun ha' => ha' ha0) hb
    let T : Set (ℤ × ℤ) :=
      {q | |(q.1 : ℝ)| ≤ A ∧ |(q.2 : ℝ)| ≤ D ∧
        a * (q.1 : ZMod p) + b * (q.2 : ZMod p) = 0}
    let T' : Set (ℤ × ℤ) :=
      {q | |(q.1 : ℝ)| ≤ D ∧ |(q.2 : ℝ)| ≤ A ∧
        b * (q.1 : ZMod p) + a * (q.2 : ZMod p) = 0}
    have hImage : Prod.swap '' T = T' := by
      ext q
      rcases q with ⟨x, y⟩
      constructor
      · rintro ⟨z, hz, heq⟩
        rcases z with ⟨z₁, z₂⟩
        have hzSwap : (z₂, z₁) = (x, y) := by simpa using heq
        have hz₂x : z₂ = x := congrArg Prod.fst hzSwap
        have hz₁y : z₁ = y := congrArg Prod.snd hzSwap
        rcases hz with ⟨hz₁A, hz₂D, hzline⟩
        refine ⟨?_, ?_, ?_⟩
        · simpa [hz₂x] using hz₂D
        · simpa [hz₁y] using hz₁A
        · rw [← hz₁y, ← hz₂x]
          linear_combination hzline
      · intro hq
        refine ⟨(y, x), ?_, ?_⟩
        · change |(y : ℝ)| ≤ A ∧ |(x : ℝ)| ≤ D ∧
            a * (y : ZMod p) + b * (x : ZMod p) = 0
          refine ⟨hq.2.1, hq.1, ?_⟩
          linear_combination hq.2.2
        · rfl
    have hswapInj : Function.Injective (Prod.swap : ℤ × ℤ → ℤ × ℤ) := by
      intro x y h
      have := congrArg Prod.swap h
      simpa using this
    have hcard : T.ncard = T'.ncard := by
      calc
        T.ncard = (Prod.swap '' T).ncard :=
          (Set.ncard_image_of_injective T hswapInj).symm
        _ = T'.ncard := congrArg Set.ncard hImage
    have hsmall := box_line_count_le_of_second_nezero p hp D A hD hA b a ha
    calc
      ({q : ℤ × ℤ | |(q.1 : ℝ)| ≤ A ∧ |(q.2 : ℝ)| ≤ D ∧
        a * (q.1 : ZMod p) + b * (q.2 : ZMod p) = 0}.ncard : ℝ) =
          (T'.ncard : ℝ) := by
            rw [← hcard]
      _ ≤ 12 * (D * A / (p : ℝ) + max D A) := hsmall
      _ = 12 * (A * D / (p : ℝ) + max A D) := by rw [mul_comm D A, max_comm]

private theorem majorArc_measurable (x Y A₀ : ℝ) :
    MeasurableSet {theta : ℝ | majorArc x Y A₀ theta} := by
  classical
  unfold majorArc
  measurability

private theorem additiveCharacter_norm (t : ℝ) :
    ‖ArtinPrimitiveRoots.TypeII.additiveCharacter t‖ = 1 := by
  unfold ArtinPrimitiveRoots.TypeII.additiveCharacter
  rw [Complex.norm_exp]
  simp

theorem exists_compact_psi_norm_bound (psi : ℝ → ℝ)
    (hcont : Continuous psi) (hcompact : HasCompactSupport psi) :
    ∃ Cpsi : ℝ, 0 ≤ Cpsi ∧ ∀ t, ‖(psi t : ℂ)‖ ≤ Cpsi := by
  have hrange : IsCompact (Set.range psi) := hcompact.isCompact_range hcont
  have habs : IsCompact (abs '' Set.range psi) := hrange.image continuous_abs
  obtain ⟨M, hM⟩ := habs.bddAbove
  let Cpsi := max 0 M
  refine ⟨Cpsi, le_max_left _ _, ?_⟩
  intro t
  have ht : |psi t| ∈ abs '' Set.range psi := ⟨psi t, ⟨t, rfl⟩, rfl⟩
  have hbound : |psi t| ≤ M := hM ht
  have hnorm : ‖(psi t : ℂ)‖ = |psi t| := by simp
  rw [hnorm]
  exact le_trans hbound (le_max_right _ _)

theorem exists_support_Icc_norm_bound (eta : ℝ → ℝ)
    (hcont : Continuous eta) (hsupport : Function.support eta ⊆ Set.Icc (1 : ℝ) 4) :
    ∃ Ceta : ℝ, 0 ≤ Ceta ∧ ∀ t, ‖(eta t : ℂ)‖ ≤ Ceta := by
  have hinterval : IsCompact (Set.Icc (1 : ℝ) 4) := isCompact_Icc
  have hetaRange : IsCompact (eta '' Set.Icc (1 : ℝ) 4) := hinterval.image hcont
  have habsRange : IsCompact (abs '' (eta '' Set.Icc (1 : ℝ) 4)) :=
    hetaRange.image continuous_abs
  obtain ⟨M, hM⟩ := habsRange.bddAbove
  let Ceta := max 0 M
  refine ⟨Ceta, le_max_left _ _, ?_⟩
  intro t
  have hnorm : ‖(eta t : ℂ)‖ = |eta t| := by simp
  rw [hnorm]
  by_cases ht : t ∈ Set.Icc (1 : ℝ) 4
  · have hmem : |eta t| ∈ abs '' (eta '' Set.Icc (1 : ℝ) 4) :=
      ⟨eta t, ⟨t, ht, rfl⟩, rfl⟩
    exact le_trans (hM hmem) (le_max_right _ _)
  · have hzero : eta t = 0 := by
      by_contra hne
      have hsupportT : t ∈ Function.support eta := by
        simpa [Function.mem_support] using hne
      exact ht (hsupport hsupportT)
    simp [hzero, Ceta]

private def majorArcIndices (P : ℝ) : Finset (ℕ × ℤ) :=
  (Finset.Icc 1 (Nat.floor P)).biUnion fun k =>
    (Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).image fun m => (k, m)

private theorem majorArcIndices_card_le (P : ℝ) (hP : 1 ≤ P) :
    (majorArcIndices P).card ≤ 4 * (Nat.floor P) ^ 2 := by
  classical
  let n := Nat.floor P
  let Kset := Finset.Icc 1 n
  have hn : (n : ℝ) ≤ P := Nat.floor_le (by linarith [hP])
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hP)
  have hintervalCard (k : ℕ) (hk : k ∈ Kset) :
      (Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).card ≤ 4 * k := by
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hcard : ((Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).card : ℤ) =
        3 * (k : ℤ) + 1 := by
      rw [Int.card_Icc_of_le (-(k : ℤ)) (2 * (k : ℤ)) (by omega)]
      ring
    have hcast : ((Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).card : ℝ) =
        3 * (k : ℝ) + 1 := by exact_mod_cast hcard
    have hkcast : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hbound : 3 * (k : ℝ) + 1 ≤ 4 * (k : ℝ) := by nlinarith [hkcast]
    have hboundReal : ((Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).card : ℝ) ≤
        (4 * k : ℕ) := by rw [hcast]; exact_mod_cast hbound
    exact_mod_cast hboundReal
  have hsum : (majorArcIndices P).card ≤
      ∑ k ∈ Kset, 4 * k := by
    dsimp [majorArcIndices, n, Kset]
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 (Nat.floor P),
          ((Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).image fun m => (k, m)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ k ∈ Finset.Icc 1 (Nat.floor P), 4 * k := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.card_image_of_injective _ (fun m₁ m₂ h => congrArg Prod.snd h)]
        exact hintervalCard k hk
  have hsumBound : (∑ k ∈ Kset, 4 * k) ≤ Kset.card * (4 * n) := by
    calc
      _ ≤ ∑ k ∈ Kset, 4 * n := by
        apply Finset.sum_le_sum
        intro k hk
        exact Nat.mul_le_mul_left 4 (Finset.mem_Icc.mp hk).2
      _ = Kset.card * (4 * n) := by simp [Finset.sum_const, nsmul_eq_mul]
  have hKcard : Kset.card = n := by simp [Kset]
  have hNat : (majorArcIndices P).card ≤ 4 * n ^ 2 := by
    calc
      _ ≤ ∑ k ∈ Kset, 4 * k := hsum
      _ ≤ Kset.card * (4 * n) := hsumBound
      _ = 4 * n ^ 2 := by rw [hKcard]; ring
  simpa [n] using hNat

private def majorArcInterval (P Y : ℝ) (j : ℕ × ℤ) : Set ℝ :=
  Set.Icc ((j.2 : ℝ) / (j.1 : ℝ) - 2 * P / Y)
    ((j.2 : ℝ) / (j.1 : ℝ) + 2 * P / Y)

private def majorArcCover (P Y : ℝ) : Set ℝ :=
  ⋃ j ∈ (majorArcIndices P : Set (ℕ × ℤ)), majorArcInterval P Y j

private theorem majorArc_restrict_subset_cover (x Y A₀ P : ℝ)
    (hP : P = Real.rpow (Real.log x) A₀) (hPone : 1 ≤ P)
    (hδ : 2 * P / Y ≤ 1) (theta : ℝ)
    (htheta : theta ∈ Set.Ioc 0 1) (hmajor : majorArc x Y A₀ theta) :
    theta ∈ majorArcCover P Y := by
  rcases hmajor with ⟨h, k, hk1, hkP, hgcd, z, hclose⟩
  have hkPos : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hk1)
  have hkP' : (k : ℝ) ≤ P := by simpa [hP] using hkP
  have hkFloor : k ≤ Nat.floor P := Nat.le_floor hkP'
  let m : ℤ := h + (k : ℤ) * z
  have hmEq : (m : ℝ) / (k : ℝ) = (h : ℝ) / (k : ℝ) + z := by
    dsimp [m]
    push_cast
    field_simp [hkPos.ne']
  have hdist : |theta - (m : ℝ) / (k : ℝ)| ≤ 2 * P / Y := by
    rw [hmEq]
    simpa [hP, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hclose
  have hcenterLo : -1 ≤ (m : ℝ) / (k : ℝ) := by
    have hh := (abs_le.mp hdist).2
    rcases htheta with ⟨htlo, hthi⟩
    linarith
  have hcenterHi : (m : ℝ) / (k : ℝ) ≤ 2 := by
    have hh := (abs_le.mp hdist).1
    rcases htheta with ⟨htlo, hthi⟩
    linarith
  have hmLoReal : -(k : ℝ) ≤ (m : ℝ) := by
    have h := (le_div_iff₀ hkPos).mp hcenterLo
    simpa using h
  have hmHiReal : (m : ℝ) ≤ 2 * (k : ℝ) := by
    exact (div_le_iff₀ hkPos).mp hcenterHi
  have hmLo : -(k : ℤ) ≤ m := by exact_mod_cast hmLoReal
  have hmHi : m ≤ 2 * (k : ℤ) := by exact_mod_cast hmHiReal
  have hmBox : m ∈ Finset.Icc (-(k : ℤ)) (2 * (k : ℤ)) :=
    Finset.mem_Icc.mpr ⟨hmLo, hmHi⟩
  have hindex : (k, m) ∈ majorArcIndices P := by
    simp only [majorArcIndices, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
    exact ⟨k, ⟨hk1, hkFloor⟩, m, ⟨hmLo, hmHi⟩, rfl⟩
  have hinterval : theta ∈ majorArcInterval P Y (k, m) := by
    change theta ∈ Set.Icc ((m : ℝ) / (k : ℝ) - 2 * P / Y)
      ((m : ℝ) / (k : ℝ) + 2 * P / Y)
    rcases abs_le.mp hdist with ⟨hlo, hhi⟩
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  change theta ∈ ⋃ j ∈ (majorArcIndices P : Set (ℕ × ℤ)), majorArcInterval P Y j
  exact Set.mem_iUnion.mpr ⟨(k, m), Set.mem_iUnion.mpr ⟨hindex, hinterval⟩⟩

private theorem majorArcCover_volume_le (P Y : ℝ) (hP : 1 ≤ P) (hY : 0 < Y) :
    volume (majorArcCover P Y) ≤ ENNReal.ofReal (32 * P ^ 3 / Y) := by
  classical
  let J := majorArcIndices P
  have hJcard : (J.card : ℝ) ≤ 4 * P ^ 2 := by
    have hcard := majorArcIndices_card_le P hP
    have hfloor : (Nat.floor P : ℝ) ≤ P := Nat.floor_le (by linarith [hP])
    calc
      (J.card : ℝ) ≤ 4 * (Nat.floor P : ℝ) ^ 2 := by exact_mod_cast hcard
      _ ≤ 4 * P ^ 2 := by
        have hPnonneg : 0 ≤ P := le_trans (by norm_num) hP
        nlinarith [hfloor, hPnonneg]
  have hwidthNonneg : 0 ≤ 4 * P / Y := div_nonneg (by positivity) hY.le
  have hvol (j : ℕ × ℤ) (hj : j ∈ J) :
      volume (majorArcInterval P Y j) = ENNReal.ofReal (4 * P / Y) := by
    have hjmem : j.1 ∈ Finset.Icc 1 (Nat.floor P) := by
      have hj' : j ∈ (Finset.Icc 1 (Nat.floor P)).biUnion
          (fun k => (Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).image fun m => (k, m)) := by
        simpa [J, majorArcIndices] using hj
      rcases Finset.mem_biUnion.mp hj' with ⟨k, hk, himage⟩
      rcases Finset.mem_image.mp himage with ⟨m, hm, heq⟩
      have hkEq : k = j.1 := congrArg Prod.fst heq
      simpa [hkEq] using (Finset.mem_Icc.mp hk)
    have hjPos : 0 < (j.1 : ℝ) := by
      have hj1 : 1 ≤ j.1 := (Finset.mem_Icc.mp hjmem).1
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hj1)
    rw [majorArcInterval, Real.volume_Icc]
    congr 1
    ring
  have hsum :
      (∑ j ∈ J, volume (majorArcInterval P Y j)) =
        ENNReal.ofReal ((J.card : ℝ) * (4 * P / Y)) := by
    calc
      _ = ∑ j ∈ J, ENNReal.ofReal (4 * P / Y) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hvol j hj
      _ = ENNReal.ofReal ((J.card : ℝ) * (4 * P / Y)) := by
        simp [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul, hwidthNonneg]
  have hproduct :
      (J.card : ℝ) * (4 * P / Y) ≤ 32 * P ^ 3 / Y := by
    have hPnonneg : 0 ≤ P := le_trans (by norm_num) hP
    have hP3 : 0 ≤ P ^ 3 := pow_nonneg hPnonneg 3
    calc
      (J.card : ℝ) * (4 * P / Y) ≤ (4 * P ^ 2) * (4 * P / Y) :=
        mul_le_mul_of_nonneg_right hJcard hwidthNonneg
      _ = 16 * P ^ 3 / Y := by ring
      _ ≤ 32 * P ^ 3 / Y := by
        exact div_le_div_of_nonneg_right (by nlinarith [hP3]) hY.le
  calc
    volume (majorArcCover P Y) ≤
        ∑ j ∈ J, volume (majorArcInterval P Y j) := by
      simpa [majorArcCover, J] using
        (MeasureTheory.measure_biUnion_finset_le J (majorArcInterval P Y))
    _ = ENNReal.ofReal ((J.card : ℝ) * (4 * P / Y)) := hsum
    _ ≤ ENNReal.ofReal (32 * P ^ 3 / Y) :=
      ENNReal.ofReal_le_ofReal hproduct

private theorem majorKernel_integral_norm_le (x Y A₀ t : ℝ) (a b : ℕ) :
    ‖∫ theta in (0 : ℝ)..1,
      if majorArc x Y A₀ theta then
        ArtinPrimitiveRoots.TypeII.additiveCharacter
          (theta * (t - (b : ℝ) + (a : ℝ))) else 0‖ ≤
      (volume (Set.Ioc 0 1 ∩ {theta : ℝ | majorArc x Y A₀ theta})).toReal := by
  classical
  let M : Set ℝ := {theta : ℝ | majorArc x Y A₀ theta}
  let g : ℝ → ℂ := fun theta =>
    ArtinPrimitiveRoots.TypeII.additiveCharacter (theta * (t - (b : ℝ) + (a : ℝ)))
  have hfinite : volume (Set.Ioc 0 1 ∩ M) < ⊤ := by
    have hsub : Set.Ioc 0 1 ∩ M ⊆ Set.Icc 0 1 := by
      intro theta htheta
      rcases htheta with ⟨⟨hlo, hhi⟩, _⟩
      exact ⟨hlo.le, hhi⟩
    have hmeasure : volume (Set.Ioc 0 1 ∩ M) ≤ 1 := by
      calc
        _ ≤ volume (Set.Icc 0 1) := MeasureTheory.measure_mono hsub
        _ = 1 := by simp [Real.volume_Icc]
    exact lt_of_le_of_lt hmeasure (by simp : (1 : ENNReal) < ⊤)
  have hchar (theta : ℝ) : ‖g theta‖ ≤ (1 : ℝ) := by
    change ‖ArtinPrimitiveRoots.TypeII.additiveCharacter
      (theta * (t - (b : ℝ) + (a : ℝ)))‖ ≤ 1
    rw [additiveCharacter_norm]
  have hset :
      ‖∫ theta in Set.Ioc 0 1 ∩ M, g theta ∂volume‖ ≤
        (volume (Set.Ioc 0 1 ∩ M)).toReal := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Ioc 0 1 ∩ M) (f := g) (C := (1 : ℝ)) hfinite
      (fun theta _ => hchar theta)
    simpa [MeasureTheory.measureReal_def] using h
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hfun :
      (fun theta : ℝ => if majorArc x Y A₀ theta then g theta else 0) =
        M.indicator g := by
    funext theta
    by_cases h : majorArc x Y A₀ theta <;> simp [M, g, h, Set.indicator]
  rw [hfun, MeasureTheory.setIntegral_indicator (majorArc_measurable x Y A₀)]
  simpa [g, one_mul] using hset

theorem majorKernel_norm_le_scaled (x Y A₀ t : ℝ) (a b : ℕ) (psi : ℝ → ℝ)
    (hL : 1 ≤ Real.log x) (hA₀ : 0 ≤ A₀) (hY : 0 < Y) :
    ‖ArtinPrimitiveRoots.TypeII.PD.majorKernel x Y A₀ t a b psi‖ ≤
      ‖(psi (t / Y) : ℂ)‖ *
        (32 * Real.rpow (Real.log x) A₀ ^ 3 / Y) := by
  let P := Real.rpow (Real.log x) A₀
  have hPone : 1 ≤ P := by
    dsimp [P]
    calc
      1 = Real.rpow (Real.log x) 0 := by simp
      _ ≤ Real.rpow (Real.log x) A₀ :=
        Real.rpow_le_rpow_of_exponent_le hL hA₀
  have hPnonneg : 0 ≤ P := le_trans (by norm_num) hPone
  have hratioNonneg : 0 ≤ 32 * P ^ 3 / Y := by positivity
  have houter :
      ‖(psi (t / Y) : ℂ) *
          ∫ theta in (0 : ℝ)..1,
            if majorArc x Y A₀ theta then
              ArtinPrimitiveRoots.TypeII.additiveCharacter
                (theta * (t - (b : ℝ) + (a : ℝ))) else 0‖ ≤
        ‖(psi (t / Y) : ℂ)‖ *
          (volume (Set.Ioc 0 1 ∩ {theta : ℝ | majorArc x Y A₀ theta})).toReal := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (majorKernel_integral_norm_le x Y A₀ t a b)
      (norm_nonneg _)
  change ‖(psi (t / Y) : ℂ) *
      ∫ theta in (0 : ℝ)..1,
        if majorArc x Y A₀ theta then
          ArtinPrimitiveRoots.TypeII.additiveCharacter
            (theta * (t - (b : ℝ) + (a : ℝ))) else 0‖ ≤ _
  by_cases hsmall : Y ≤ 32 * P ^ 3
  · have hvol : (volume
        (Set.Ioc (0 : ℝ) 1 ∩ {theta : ℝ | majorArc x Y A₀ theta})).toReal ≤ 1 := by
      have hsubset : Set.Ioc (0 : ℝ) 1 ∩
          {theta : ℝ | majorArc x Y A₀ theta} ⊆ Set.Ioc (0 : ℝ) 1 :=
        Set.inter_subset_left
      have hIocTop : volume (Set.Ioc (0 : ℝ) 1) ≠ ⊤ := by
        simp [Real.volume_Ioc]
      calc
        _ ≤ (volume (Set.Ioc (0 : ℝ) 1)).toReal :=
          MeasureTheory.measureReal_mono (μ := volume) hsubset hIocTop
        _ = 1 := by simp [MeasureTheory.measureReal_def, Real.volume_Ioc]
    have hfactor : 1 ≤ 32 * P ^ 3 / Y := by
      apply (le_div_iff₀ hY).2
      nlinarith [hsmall]
    calc
      _ ≤ ‖(psi (t / Y) : ℂ)‖ *
          (volume (Set.Ioc 0 1 ∩ {theta : ℝ | majorArc x Y A₀ theta})).toReal := houter
      _ ≤ ‖(psi (t / Y) : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hvol (norm_nonneg _)
      _ = ‖(psi (t / Y) : ℂ)‖ := by ring
      _ ≤ ‖(psi (t / Y) : ℂ)‖ * (32 * P ^ 3 / Y) :=
        le_mul_of_one_le_right (norm_nonneg _) hfactor
  · have hlarge : 32 * P ^ 3 < Y := lt_of_not_ge hsmall
    have hPcube : P ≤ P ^ 3 := by
      calc
        P = P * 1 := by ring
        _ ≤ P * P ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hPone) hPnonneg
        _ = P ^ 3 := by ring
    have hdelta : 2 * P / Y ≤ 1 := by
      apply (div_le_iff₀ hY).2
      nlinarith [hPcube, hlarge]
    have hcover := majorArcCover_volume_le P Y hPone hY
    have hsubset : Set.Ioc 0 1 ∩ {theta : ℝ | majorArc x Y A₀ theta} ⊆
        majorArcCover P Y := by
      intro theta htheta
      exact majorArc_restrict_subset_cover x Y A₀ P rfl hPone hdelta theta
        htheta.1 htheta.2
    have hcoverTop : volume (majorArcCover P Y) ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hcover ENNReal.ofReal_lt_top)
    have hvol :
        (volume (Set.Ioc 0 1 ∩ {theta : ℝ | majorArc x Y A₀ theta})).toReal ≤
          32 * P ^ 3 / Y := by
      calc
        _ ≤ (volume (majorArcCover P Y)).toReal :=
          MeasureTheory.measureReal_mono (μ := volume) hsubset hcoverTop
        _ ≤ (ENNReal.ofReal (32 * P ^ 3 / Y)).toReal :=
          ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hcover
        _ = 32 * P ^ 3 / Y := ENNReal.toReal_ofReal hratioNonneg
    calc
      _ ≤ ‖(psi (t / Y) : ℂ)‖ *
          (volume (Set.Ioc 0 1 ∩ {theta : ℝ | majorArc x Y A₀ theta})).toReal := houter
      _ ≤ ‖(psi (t / Y) : ℂ)‖ * (32 * P ^ 3 / Y) :=
        mul_le_mul_of_nonneg_left hvol (norm_nonneg _)

end

end ArtinPrimitiveRoots.TypeII.PD
