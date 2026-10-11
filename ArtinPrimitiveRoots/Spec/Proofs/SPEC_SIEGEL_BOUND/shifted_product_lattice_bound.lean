import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private def shiftedGridCell (δ : ℝ) (u : InfinitePlace F → ℂ) (a : F) :
    InfinitePlace F × Fin 2 → Bool × ℕ := fun j =>
  let z := j.1.embedding a + u j.1
  (decide (if j.2 = 0 then z.re < 0 else z.im < 0),
    Nat.floor ((if j.2 = 0 then |z.re| else |z.im|) / δ))

private def gridRadius (c : Bool × ℕ) : ℝ := (c.2 : ℝ)

private lemma abs_sub_lt_of_nat_floor_eq {δ x y : ℝ} (hδ : 0 < δ)
    (hfloor : Nat.floor (x / δ) = Nat.floor (y / δ))
    (hx : 0 ≤ x) (hy : 0 ≤ y) : |x - y| < δ := by
  have hx0 := Nat.floor_le (show 0 ≤ x / δ by positivity)
  have hx1 := Nat.lt_floor_add_one (x / δ)
  have hy0 := Nat.floor_le (show 0 ≤ y / δ by positivity)
  have hy1 := Nat.lt_floor_add_one (y / δ)
  have hx0' : (Nat.floor (x / δ) : ℝ) ≤ x / δ := hx0
  have hx1' : x / δ < (Nat.floor (x / δ) : ℝ) + 1 := hx1
  have hy0' : (Nat.floor (y / δ) : ℝ) ≤ y / δ := hy0
  have hy1' : y / δ < (Nat.floor (y / δ) : ℝ) + 1 := hy1
  have hx0'' : δ * (Nat.floor (x / δ) : ℝ) ≤ x := by
    calc
      δ * (Nat.floor (x / δ) : ℝ) ≤ δ * (x / δ) := mul_le_mul_of_nonneg_left hx0' hδ.le
      _ = x := by field_simp
  have hx1'' : x < δ * ((Nat.floor (x / δ) : ℝ) + 1) := by
    have hh : x / δ < (Nat.floor (x / δ) : ℝ) + 1 := hx1'
    calc
      x = δ * (x / δ) := by field_simp
      _ < δ * ((Nat.floor (x / δ) : ℝ) + 1) := mul_lt_mul_of_pos_left hh hδ
  have hy0'' : δ * (Nat.floor (y / δ) : ℝ) ≤ y := by
    calc
      δ * (Nat.floor (y / δ) : ℝ) ≤ δ * (y / δ) := mul_le_mul_of_nonneg_left hy0' hδ.le
      _ = y := by field_simp
  have hy1'' : y < δ * ((Nat.floor (y / δ) : ℝ) + 1) := by
    have hh : y / δ < (Nat.floor (y / δ) : ℝ) + 1 := hy1'
    calc
      y = δ * (y / δ) := by field_simp
      _ < δ * ((Nat.floor (y / δ) : ℝ) + 1) := mul_lt_mul_of_pos_left hh hδ
  rw [abs_lt]
  rw [← hfloor] at hy0'' hy1''
  constructor <;> nlinarith [hx0'', hx1'', hy0'', hy1'', hδ]

private lemma abs_sub_lt_of_shiftedGridCell_eq {δ x y : ℝ} (hδ : 0 < δ)
    (hsign : decide (x < 0) = decide (y < 0))
    (hfloor : Nat.floor (|x| / δ) = Nat.floor (|y| / δ)) : |x - y| < δ := by
  by_cases hx : x < 0
  · have hx' : decide (x < 0) = true := decide_eq_true hx
    have hy' : decide (y < 0) = true := hsign.symm.trans hx'
    have hy : y < 0 := of_decide_eq_true hy'
    have h := abs_sub_lt_of_nat_floor_eq hδ hfloor (abs_nonneg x) (abs_nonneg y)
    calc
      |x - y| = |(-x) - (-y)| := by
        rw [show x - y = -((-x) - (-y)) by ring, abs_neg]
      _ < δ := by simpa [abs_of_neg hx, abs_of_neg hy] using h
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    have hy : ¬ y < 0 := by
      intro hy
      have hx' : decide (x < 0) = false := decide_eq_false hx
      have hy' : decide (y < 0) = true := decide_eq_true hy
      have ht := hsign.symm.trans hx'
      rw [hy'] at ht
      cases ht
    have hy0 : 0 ≤ y := le_of_not_gt hy
    have h := abs_sub_lt_of_nat_floor_eq hδ hfloor (abs_nonneg x) (abs_nonneg y)
    simpa [abs_of_nonneg hx0, abs_of_nonneg hy0] using h

private lemma gridRadius_le_abs (δ x : ℝ) (hδ : 0 < δ) :
    δ * gridRadius (decide (x < 0), Nat.floor (|x| / δ)) ≤ |x| := by
  have hfloor := Nat.floor_le (show 0 ≤ |x| / δ by positivity)
  dsimp [gridRadius]
  have hcast : ((Nat.floor (|x| / δ) : ℕ) : ℝ) ≤ |x| / δ := hfloor
  have hmul := mul_le_mul_of_nonneg_left hcast hδ.le
  have hδne : δ ≠ 0 := hδ.ne'
  rwa [mul_div_cancel₀ |x| hδne] at hmul

private lemma shiftedGridCell_injective (D : ℕ) (hD : 0 < D)
    (u : InfinitePlace F → ℂ) :
    Function.Injective (fun a : DenominatorScalars (F := F) D =>
      shiftedGridCell ((4 * (D : ℝ))⁻¹) u a.1) := by
  intro a b hab
  by_contra hne
  let δ : ℝ := (4 * (D : ℝ))⁻¹
  have hDℝ : 0 < (D : ℝ) := by exact_mod_cast hD
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : 2 * δ < (D : ℝ)⁻¹ := by
    dsimp [δ]
    have hDne : (D : ℝ) ≠ 0 := hDℝ.ne'
    field_simp
    nlinarith
  have hne' : a.1 ≠ b.1 := by
    intro h
    apply hne
    exact Subtype.ext h
  obtain ⟨aO, haO⟩ := a.2
  obtain ⟨bO, hbO⟩ := b.2
  have hD0 : (D : F) ≠ 0 := by exact_mod_cast hD.ne'
  have hdiff : a.1 - b.1 ≠ 0 := sub_ne_zero.mpr hne'
  have hK : (D : F) * (a.1 - b.1) =
      algebraMap (𝓞 F) F (aO - bO) := by
    rw [map_sub]
    calc
      (D : F) * (a.1 - b.1) = (D : F) * a.1 - (D : F) * b.1 := by ring
      _ = algebraMap (𝓞 F) F aO - algebraMap (𝓞 F) F bO := by rw [haO, hbO]
  have hO0 : aO - bO ≠ 0 := by
    intro h
    have hmap := congrArg (algebraMap (𝓞 F) F) h
    have hmul : (D : F) * a.1 = (D : F) * b.1 := by
      rw [haO, hbO]
      simpa [map_sub, sub_eq_zero] using hmap
    exact hdiff (sub_eq_zero.mpr (mul_left_cancel₀ hD0 hmul))
  have hO_norm : 1 ≤ absFieldNorm F (algebraMap (𝓞 F) F (aO - bO)) :=
    absFieldNorm_ge_one_of_ringInteger _ hO0
  have hcoords (w : InfinitePlace F) (i : Fin 2) :
      |(if i = 0 then (w.embedding a.1 + u w).re else
        (w.embedding a.1 + u w).im) -
        (if i = 0 then (w.embedding b.1 + u w).re else
        (w.embedding b.1 + u w).im)| < δ := by
    fin_cases i
    · have hj := congrFun hab (w, 0)
      simp only [shiftedGridCell, Prod.mk.injEq, Fin.isValue] at hj
      exact abs_sub_lt_of_shiftedGridCell_eq hδ hj.1 hj.2
    · have hj := congrFun hab (w, 1)
      simp only [shiftedGridCell, Prod.mk.injEq, Fin.isValue] at hj
      exact abs_sub_lt_of_shiftedGridCell_eq hδ hj.1 hj.2
  have hEmbed (w : InfinitePlace F) : ‖w.embedding (a.1 - b.1)‖ < 2 * δ := by
    have hre : |(w.embedding a.1 + u w).re - (w.embedding b.1 + u w).re| < δ := by
      simpa using hcoords w 0
    have him : |(w.embedding a.1 + u w).im - (w.embedding b.1 + u w).im| < δ := by
      simpa using hcoords w 1
    have hre' : (w.embedding a.1 - w.embedding b.1).re =
        (w.embedding a.1 + u w).re - (w.embedding b.1 + u w).re := by
      simp [Complex.sub_re, Complex.add_re]
    have him' : (w.embedding a.1 - w.embedding b.1).im =
        (w.embedding a.1 + u w).im - (w.embedding b.1 + u w).im := by
      simp [Complex.sub_im, Complex.add_im]
    have hnorm := Complex.norm_le_abs_re_add_abs_im (w.embedding a.1 - w.embedding b.1)
    have hmap : w.embedding (a.1 - b.1) = w.embedding a.1 - w.embedding b.1 := map_sub _ _ _
    rw [hmap]
    calc
      ‖w.embedding a.1 - w.embedding b.1‖ ≤
          |(w.embedding a.1 - w.embedding b.1).re| +
            |(w.embedding a.1 - w.embedding b.1).im| := hnorm
      _ < 2 * δ := by rw [hre', him']; nlinarith [hre, him]
  have hterm (w : InfinitePlace F) :
      ‖w.embedding ((D : F) * (a.1 - b.1))‖ ^ 2 < 1 := by
    rw [map_mul, Complex.norm_mul]
    have hcast : w.embedding (D : F) = (D : ℂ) := by simp
    rw [hcast]
    have hnormD : ‖(D : ℂ)‖ = (D : ℝ) := by
      norm_cast
    rw [hnormD]
    have h := hEmbed w
    have hDmul : (D : ℝ) * ‖w.embedding (a.1 - b.1)‖ < 1 := by
      calc
        (D : ℝ) * ‖w.embedding (a.1 - b.1)‖ < (D : ℝ) * (2 * δ) := by
          exact mul_lt_mul_of_pos_left h hDℝ
        _ < 1 := by
          calc
            (D : ℝ) * (2 * δ) < (D : ℝ) * (D : ℝ)⁻¹ :=
              mul_lt_mul_of_pos_left hsmall hDℝ
            _ = 1 := mul_inv_cancel₀ hDℝ.ne'
    have hnonneg : 0 ≤ (D : ℝ) * ‖w.embedding (a.1 - b.1)‖ :=
      mul_nonneg hDℝ.le (norm_nonneg _)
    have hpos : 0 < 1 - (D : ℝ) * ‖w.embedding (a.1 - b.1)‖ := by linarith
    have hpos' : 0 < 1 + (D : ℝ) * ‖w.embedding (a.1 - b.1)‖ := by linarith
    have := mul_pos hpos hpos'
    nlinarith
  have hprod : absFieldNorm F ((D : F) * (a.1 - b.1)) < 1 := by
    unfold absFieldNorm
    classical
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    let f : InfinitePlace F → ℝ := fun w => ‖w.embedding ((D : F) * (a.1 - b.1))‖ ^ 2
    have hrest : ∏ i ∈ Finset.univ.erase w, f i ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro i hi
        exact sq_nonneg _
      · intro i hi
        exact (hterm i).le
    calc
      ∏ i : InfinitePlace F, ‖i.embedding ((D : F) * (a.1 - b.1))‖ ^ 2 =
          (∏ i ∈ Finset.univ.erase w, f i) * f w := by
        symm
        exact Finset.prod_erase_mul _ _ (Finset.mem_univ w)
      _ ≤ f w := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right hrest (sq_nonneg _)
      _ < 1 := hterm w
  rw [hK] at hprod
  exact (not_le_of_gt hprod) hO_norm

private lemma integral_one_add_rpow {p : ℝ} (hp : 1 < p) :
    IntegrableOn (fun x : ℝ => (1 + x) ^ (-p)) (Set.Ioi 0) ∧
      (∫ x in Set.Ioi 0, (1 + x) ^ (-p)) = 1 / (p - 1) := by
  have hp' : -p < -1 := by linarith
  have hInt : IntegrableOn (fun x : ℝ => (1 + x) ^ (-p)) (Set.Ioi 0) := by
    simpa [add_comm] using
      (integrableOn_add_rpow_Ioi_of_lt (a := -p) (c := 0) (m := 1) hp' (by norm_num))
  let G : ℝ → ℝ := fun x => (x + 1) ^ (1 - p) / (1 - p)
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt G ((1 + x) ^ (-p)) x := by
    intro x hx
    dsimp [G]
    have hx0 : 0 ≤ x := by simpa using hx
    convert! (((hasDerivAt_id x).add_const 1).rpow_const (p := 1 - p)
      (by left; change x + 1 ≠ 0; linarith [hx0])).div_const (1 - p) using 1
    all_goals simp [show 1 - p ≠ 0 by linarith, add_comm]
  have ht : Tendsto G atTop (nhds 0) := by
    change Tendsto (fun x : ℝ => (x + 1) ^ (1 - p) / (1 - p)) atTop (nhds 0)
    have hpow : Tendsto (fun x : ℝ => (x + 1) ^ (-(p - 1))) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by linarith : 0 < p - 1)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_id)
    rw [show 1 - p = -(p - 1) by ring]
    simpa using hpow.div_const (-(p - 1))
  have hEval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hInt ht
  refine ⟨hInt, ?_⟩
  calc
    (∫ x in Set.Ioi 0, (1 + x) ^ (-p)) = 0 - G 0 := hEval
    _ = 1 / (p - 1) := by
      dsimp [G]
      simp only [zero_add, Real.one_rpow, zero_sub]
      have hpneq : p - 1 ≠ 0 := by linarith
      have hpneq' : 1 - p ≠ 0 := by linarith
      field_simp [hpneq, hpneq']
      <;> ring

private lemma scaled_nat_rpow_sum {δ l p : ℝ} (hδ : 0 < δ) (hl : 0 < l)
    (hp : 1 < p) :
    Summable (fun n : ℕ => (1 + (δ / l) * (n : ℝ)) ^ (-p)) ∧
      (∑' n : ℕ, (1 + (δ / l) * (n : ℝ)) ^ (-p)) ≤
        1 + l / (δ * (p - 1)) := by
  let f : ℝ → ℝ := fun x => (1 + (δ / l) * x) ^ (-p)
  have hscale : 0 < δ / l := div_pos hδ hl
  have hbaseInt := integral_one_add_rpow hp
  have hInt : IntegrableOn f (Set.Ioi 0) := by
    have hbaseInt0 : IntegrableOn (fun x : ℝ => (1 + x) ^ (-p))
        (Set.Ioi ((δ / l) * 0)) := by simpa using hbaseInt.1
    have h := (integrableOn_Ioi_comp_mul_left_iff
        (fun x : ℝ => (1 + x) ^ (-p)) 0 hscale).2 hbaseInt0
    simpa [f] using h
  have hanti : AntitoneOn f (Set.Ici 0) := by
    intro x hx y hy hxy
    dsimp [f]
    have hx0 : 0 ≤ x := hx
    have hbase : 0 < 1 + (δ / l) * x := by positivity
    have hbase' : 1 + (δ / l) * x ≤ 1 + (δ / l) * y := by
      have hmul := mul_le_mul_of_nonneg_left hxy hscale.le
      linarith
    exact Real.rpow_le_rpow_of_nonpos hbase hbase' (by linarith)
  have hnonneg : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ f x := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    dsimp [f]
    positivity
  have hscaledInt : (∫ x in Set.Ioi 0, f x) = l / (δ * (p - 1)) := by
    calc
      (∫ x in Set.Ioi 0, f x) =
          (δ / l)⁻¹ • ∫ x in Set.Ioi 0, (1 + x) ^ (-p) := by
        dsimp [f]
        simpa [smul_eq_mul] using
          (integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x) ^ (-p)) 0 hscale)
      _ = l / (δ * (p - 1)) := by
        rw [hbaseInt.2]
        simp only [smul_eq_mul]
        field_simp [ne_of_gt hδ, ne_of_gt hl, ne_of_gt (sub_pos.mpr hp)]
        <;> ring
  refine ⟨hanti.summable_of_integrableOn_Ioi_zero hInt hnonneg, ?_⟩
  calc
    (∑' n : ℕ, (1 + (δ / l) * (n : ℝ)) ^ (-p)) ≤ f 0 + ∫ x in Set.Ioi 0, f x :=
      hanti.tsum_le_integral hInt hnonneg
    _ = 1 + l / (δ * (p - 1)) := by simp [hscaledInt, f]

private lemma grid_nat_term_le {δ l αmin αmax α : ℝ} (hδ : 0 < δ) (hl : 0 < l)
    (hαmin : 1 < αmin) (hαlo : αmin ≤ α) (hαhi : α ≤ αmax) (n : ℕ) :
    Real.rpow (l ^ 2 + (δ * (n : ℝ)) ^ 2) (-α / 2) ≤
      Real.rpow l (-α) * Real.rpow 2 (αmax / 2) *
        Real.rpow (1 + (δ / l) * (n : ℝ)) (-αmin) := by
  let t : ℝ := (δ / l) * (n : ℝ)
  have htnonneg : 0 ≤ t := by dsimp [t]; positivity
  have hlt : l * t = δ * (n : ℝ) := by
    dsimp [t]
    field_simp
  have hbase : l ^ 2 + (δ * (n : ℝ)) ^ 2 = l ^ 2 * (1 + t ^ 2) := by
    rw [← hlt]
    ring
  have hcomp : (1 + t) ^ 2 / 2 ≤ 1 + t ^ 2 := by
    nlinarith [sq_nonneg (t - 1)]
  have hmidpos : 0 < (1 + t) ^ 2 / 2 := by positivity
  have hmidpow := Real.rpow_le_rpow_of_nonpos hmidpos hcomp (by linarith : -α / 2 ≤ 0)
  have hpowSquareT :
      Real.rpow ((1 + t) ^ 2) (-α / 2) =
        Real.rpow (1 + t) (-α / 2) * Real.rpow (1 + t) (-α / 2) := by
    calc
      Real.rpow ((1 + t) ^ 2) (-α / 2) =
          (Real.rpow (1 + t) (-α / 2)) ^ 2 :=
        (Real.rpow_pow_comm (by positivity : 0 ≤ 1 + t) (-α / 2) 2).symm
      _ = Real.rpow (1 + t) (-α / 2) * Real.rpow (1 + t) (-α / 2) := by rw [pow_two]
  have hpowSquareL : Real.rpow (l ^ 2) (-α / 2) =
      Real.rpow l (-α / 2) * Real.rpow l (-α / 2) := by
    calc
      Real.rpow (l ^ 2) (-α / 2) = (Real.rpow l (-α / 2)) ^ 2 :=
        (Real.rpow_pow_comm hl.le (-α / 2) 2).symm
      _ = Real.rpow l (-α / 2) * Real.rpow l (-α / 2) := by rw [pow_two]
  have hpowSquareT' : Real.rpow (1 + t) (-α / 2) * Real.rpow (1 + t) (-α / 2) =
      Real.rpow (1 + t) (-α) := by
    calc
      _ = Real.rpow (1 + t) ((-α / 2) + (-α / 2)) :=
        (Real.rpow_add (by positivity : 0 < 1 + t) _ _).symm
      _ = Real.rpow (1 + t) (-α) := by congr 1 <;> ring
  have hpowSquareL' : Real.rpow l (-α / 2) * Real.rpow l (-α / 2) =
      Real.rpow l (-α) := by
    calc
      _ = Real.rpow l ((-α / 2) + (-α / 2)) := (Real.rpow_add hl _ _).symm
      _ = Real.rpow l (-α) := by congr 1 <;> ring
  have hinv : Real.rpow (2⁻¹) (-α / 2) = Real.rpow 2 (α / 2) := by
    calc
      Real.rpow (2⁻¹) (-α / 2) = (Real.rpow 2 (-α / 2))⁻¹ :=
        Real.inv_rpow (by norm_num : 0 ≤ (2 : ℝ)) (-α / 2)
      _ = Real.rpow 2 (α / 2) := by
        have hneg : Real.rpow 2 (-α / 2) = (Real.rpow 2 (α / 2))⁻¹ := by
          calc
            Real.rpow 2 (-α / 2) = Real.rpow 2 (-(α / 2)) := by congr 1 <;> ring
            _ = (Real.rpow 2 (α / 2))⁻¹ := Real.rpow_neg (by norm_num) (α / 2)
        rw [hneg]
        simp
  have hpowSplit :
      Real.rpow ((1 + t) ^ 2 / 2) (-α / 2) =
        Real.rpow (1 + t) (-α) * Real.rpow 2 (α / 2) := by
    calc
      Real.rpow ((1 + t) ^ 2 / 2) (-α / 2) =
          Real.rpow ((1 + t) ^ 2) (-α / 2) * Real.rpow (2⁻¹) (-α / 2) := by
        rw [div_eq_mul_inv]
        exact Real.mul_rpow (sq_nonneg (1 + t)) (inv_nonneg.mpr (by norm_num))
      _ = Real.rpow (1 + t) (-α) * Real.rpow 2 (α / 2) := by
        rw [hpowSquareT, hpowSquareT', hinv]
  have hbasePow : Real.rpow (l ^ 2) (-α / 2) = Real.rpow l (-α) := by
    rw [hpowSquareL, hpowSquareL']
  have hbaseSplit :
      Real.rpow (l ^ 2 * (1 + t ^ 2)) (-α / 2) =
        Real.rpow l (-α) * Real.rpow (1 + t ^ 2) (-α / 2) := by
    calc
      Real.rpow (l ^ 2 * (1 + t ^ 2)) (-α / 2) =
          Real.rpow (l ^ 2) (-α / 2) * Real.rpow (1 + t ^ 2) (-α / 2) :=
        Real.mul_rpow (sq_nonneg l) (by positivity)
      _ = Real.rpow l (-α) * Real.rpow (1 + t ^ 2) (-α / 2) := by rw [hbasePow]
  have hone : 1 ≤ 1 + t := by linarith
  have hpowExp := Real.rpow_le_rpow_of_exponent_le hone (by linarith : -α ≤ -αmin)
  have hconst := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ (2 : ℝ) by norm_num)
    (by linarith : α / 2 ≤ αmax / 2)
  have hnorm : Real.rpow (1 + t ^ 2) (-α / 2) ≤
      Real.rpow (1 + t) (-αmin) * Real.rpow 2 (αmax / 2) := by
    have hbtpos : 0 < 1 + t := by linarith [htnonneg]
    calc
      Real.rpow (1 + t ^ 2) (-α / 2) ≤
          Real.rpow ((1 + t) ^ 2 / 2) (-α / 2) := hmidpow
      _ = Real.rpow (1 + t) (-α) * Real.rpow 2 (α / 2) := hpowSplit
      _ ≤ Real.rpow (1 + t) (-αmin) * Real.rpow 2 (αmax / 2) := by
        exact mul_le_mul hpowExp hconst (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (le_of_lt hbtpos) _)
  calc
    Real.rpow (l ^ 2 + (δ * (n : ℝ)) ^ 2) (-α / 2) =
        Real.rpow l (-α) * Real.rpow (1 + t ^ 2) (-α / 2) := by
      rw [hbase, hbaseSplit]
    _ ≤ Real.rpow l (-α) *
        (Real.rpow (1 + t) (-αmin) * Real.rpow 2 (αmax / 2)) := by
      exact mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg (le_of_lt hl) _)
    _ = Real.rpow l (-α) * Real.rpow 2 (αmax / 2) *
        Real.rpow (1 + (δ / l) * (n : ℝ)) (-αmin) := by
      dsimp [t]
      ring

private lemma grid_nat_weight_bound (δ lmin αmin αmax : ℝ)
    (hδ : 0 < δ) (hlmin : 0 < lmin) (hαmin : 1 < αmin)
    (hαrange : αmin ≤ αmax) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ α : ℝ, αmin ≤ α → α ≤ αmax →
      ∀ l : ℝ, lmin ≤ l →
        Summable (fun n : ℕ =>
          Real.rpow (l ^ 2 + (δ * (n : ℝ)) ^ 2) (-α / 2)) ∧
        (∑' n : ℕ, Real.rpow (l ^ 2 + (δ * (n : ℝ)) ^ 2) (-α / 2)) ≤
          K * Real.rpow l (1 - α) := by
  let K : ℝ := Real.rpow 2 (αmax / 2) *
    (lmin⁻¹ + (δ * (αmin - 1))⁻¹)
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    positivity
  · intro α hαlo hαhi l hl
    have hlpos : 0 < l := lt_of_lt_of_le hlmin hl
    have hscaled := scaled_nat_rpow_sum hδ hlpos hαmin
    let f : ℕ → ℝ := fun n => (1 + (δ / l) * (n : ℝ)) ^ (-αmin)
    let c : ℝ := Real.rpow l (-α) * Real.rpow 2 (αmax / 2)
    have hmajor : ∀ n : ℕ,
        Real.rpow (l ^ 2 + (δ * (n : ℝ)) ^ 2) (-α / 2) ≤ c * f n := by
      intro n
      simpa [c, f] using grid_nat_term_le hδ hlpos hαmin hαlo hαhi n
    have hdom : Summable (fun n : ℕ => c * f n) := hscaled.1.mul_left c
    have htarget_nonneg : ∀ n : ℕ,
        0 ≤ Real.rpow (l ^ 2 + (δ * (n : ℝ)) ^ 2) (-α / 2) := by
      intro n
      exact Real.rpow_nonneg (by positivity) _
    have htarget : Summable (fun n : ℕ =>
        Real.rpow (l ^ 2 + (δ * (n : ℝ)) ^ 2) (-α / 2)) :=
      hdom.of_nonneg_of_le htarget_nonneg hmajor
    have htsum := htarget.tsum_le_tsum hmajor hdom
    have hqpos : 0 < δ * (αmin - 1) := mul_pos hδ (by linarith)
    have hratio : 1 ≤ l / lmin := (one_le_div₀ hlmin).2 hl
    have hscaleBound :
        1 + l / (δ * (αmin - 1)) ≤
          l * (lmin⁻¹ + (δ * (αmin - 1))⁻¹) := by
      calc
        1 + l / (δ * (αmin - 1)) ≤ l / lmin + l / (δ * (αmin - 1)) := by
          linarith [hratio]
        _ = l * (lmin⁻¹ + (δ * (αmin - 1))⁻¹) := by ring
    have hpowl : Real.rpow l (-α) * l = Real.rpow l (1 - α) := by
      calc
        Real.rpow l (-α) * l = Real.rpow l (-α) * Real.rpow l 1 := by simp
        _ = Real.rpow l (-α + 1) := (Real.rpow_add hlpos (-α) 1).symm
        _ = Real.rpow l (1 - α) := by congr 1 <;> ring
    refine ⟨htarget, ?_⟩
    calc
      (∑' n : ℕ, Real.rpow (l ^ 2 + (δ * (n : ℝ)) ^ 2) (-α / 2)) ≤
          ∑' n : ℕ, c * f n := htsum
      _ = c * ∑' n : ℕ, f n := by rw [tsum_mul_left]
      _ ≤ c * (1 + l / (δ * (αmin - 1))) := by
        exact mul_le_mul_of_nonneg_left hscaled.2 (by dsimp [c]; positivity)
      _ ≤ K * Real.rpow l (1 - α) := by
        dsimp [c, K]
        have hcpos : 0 ≤ Real.rpow l (-α) * Real.rpow 2 (αmax / 2) :=
          mul_nonneg (Real.rpow_nonneg hlpos.le _) (Real.rpow_nonneg (by norm_num) _)
        calc
          (Real.rpow l (-α) * Real.rpow 2 (αmax / 2)) *
              (1 + l / (δ * (αmin - 1))) ≤
              (Real.rpow l (-α) * Real.rpow 2 (αmax / 2)) *
                (l * (lmin⁻¹ + (δ * (αmin - 1))⁻¹)) :=
            mul_le_mul_of_nonneg_left hscaleBound hcpos
          _ = Real.rpow 2 (αmax / 2) *
              (lmin⁻¹ + (δ * (αmin - 1))⁻¹) * Real.rpow l (-α) * l := by ring
          _ = Real.rpow 2 (αmax / 2) *
              (lmin⁻¹ + (δ * (αmin - 1))⁻¹) * Real.rpow l (1 - α) := by
            calc
              _ = Real.rpow 2 (αmax / 2) *
                    (lmin⁻¹ + (δ * (αmin - 1))⁻¹) *
                    (Real.rpow l (-α) * l) := by ring
              _ = _ := by rw [hpowl]

private def gridCoordWeight (δ l α : ℝ) (c : Bool × ℕ) : ℝ :=
  Real.rpow (l ^ 2 + (δ * (c.2 : ℝ)) ^ 2) (-α / 2)

private def gridArrayWeight (δ : ℝ) (l : InfinitePlace F → ℝ) (α : ℝ)
    (c : (InfinitePlace F × Fin 2) → Bool × ℕ) : ℝ :=
  ∏ j : InfinitePlace F × Fin 2, gridCoordWeight δ (l j.1) α (c j)

private lemma grid_place_kernel_le (δ l α : ℝ) (hδ : 0 < δ) (hl : 0 < l) (hα : 0 < α)
    (z : ℂ) (cr ci : Bool × ℕ)
    (hcr : δ * (cr.2 : ℝ) ≤ |z.re|) (hci : δ * (ci.2 : ℝ) ≤ |z.im|) :
    Real.rpow (Complex.normSq z + l ^ 2) (-α) ≤
      gridCoordWeight δ l α cr * gridCoordWeight δ l α ci := by
  let A : ℝ := l ^ 2 + (δ * (cr.2 : ℝ)) ^ 2
  let B : ℝ := l ^ 2 + (δ * (ci.2 : ℝ)) ^ 2
  let X : ℝ := l ^ 2 + z.re ^ 2
  let Y : ℝ := l ^ 2 + z.im ^ 2
  let Q : ℝ := Complex.normSq z + l ^ 2
  have hcr0 : 0 ≤ δ * (cr.2 : ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg _)
  have hci0 : 0 ≤ δ * (ci.2 : ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg _)
  have hre0 : 0 ≤ |z.re| := abs_nonneg _
  have him0 : 0 ≤ |z.im| := abs_nonneg _
  have hcrsq : (δ * (cr.2 : ℝ)) ^ 2 ≤ z.re ^ 2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hcr) (add_nonneg hcr0 hre0)
    nlinarith [sq_abs z.re]
  have hcisq : (δ * (ci.2 : ℝ)) ^ 2 ≤ z.im ^ 2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hci) (add_nonneg hci0 him0)
    nlinarith [sq_abs z.im]
  have hA : A ≤ X := by dsimp [A, X]; nlinarith [hcrsq]
  have hB : B ≤ Y := by dsimp [B, Y]; nlinarith [hcisq]
  have hXnonneg : 0 ≤ X := by dsimp [X]; exact add_nonneg (sq_nonneg l) (sq_nonneg z.re)
  have hYnonneg : 0 ≤ Y := by dsimp [Y]; exact add_nonneg (sq_nonneg l) (sq_nonneg z.im)
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    exact add_nonneg (Complex.normSq_nonneg _) (sq_nonneg l)
  have hXQ : X ≤ Q := by
    dsimp [X, Q]
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  have hYQ : Y ≤ Q := by
    dsimp [Y, Q]
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re]
  have hAB : A * B ≤ Q ^ 2 := by
    calc
      A * B ≤ X * Y := mul_le_mul hA hB (by dsimp [B]; positivity) hXnonneg
      _ ≤ Q * Q := mul_le_mul hXQ hYQ hYnonneg hQnonneg
      _ = Q ^ 2 := by ring
  have hApos : 0 < A := by dsimp [A]; positivity
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hABpos : 0 < A * B := mul_pos hApos hBpos
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hl)
  have hQpow : Real.rpow (Q ^ 2) (-α / 2) = Real.rpow Q (-α) := by
    calc
      Real.rpow (Q ^ 2) (-α / 2) =
          Real.rpow Q (-α / 2) * Real.rpow Q (-α / 2) := by
        simpa [pow_two] using (Real.rpow_pow_comm hQpos.le (-α / 2) 2).symm
      _ = Real.rpow Q ((-α / 2) + (-α / 2)) :=
        (Real.rpow_add hQpos _ _).symm
      _ = Real.rpow Q (-α) := by congr 1 <;> ring
  calc
    Real.rpow (Complex.normSq z + l ^ 2) (-α) = Real.rpow (Q ^ 2) (-α / 2) := by
      dsimp [Q]
      exact hQpow.symm
    _ ≤ Real.rpow (A * B) (-α / 2) :=
      Real.rpow_le_rpow_of_nonpos hABpos hAB (by linarith)
    _ = Real.rpow A (-α / 2) * Real.rpow B (-α / 2) :=
      Real.mul_rpow (le_of_lt hApos) (le_of_lt hBpos)

private lemma grid_coord_box_sum_bound (δ l α B : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hl : 0 < l)
    (hsum : Summable (fun n : ℕ => gridCoordWeight δ l α (false, n)))
    (hbound : (∑' n : ℕ, gridCoordWeight δ l α (false, n)) ≤ B) :
    (∑ c ∈ Finset.univ.product (Finset.range (N + 1)), gridCoordWeight δ l α c) ≤ 2 * B := by
  classical
  change (∑ c ∈ Finset.univ ×ˢ Finset.range (N + 1), gridCoordWeight δ l α c) ≤ 2 * B
  rw [Finset.sum_product]
  have hnat : (∑ n ∈ Finset.range (N + 1), gridCoordWeight δ l α (false, n)) ≤ B := by
    exact (hsum.sum_le_tsum (Finset.range (N + 1)) (by
      intro n hn
      exact Real.rpow_nonneg
        (add_nonneg (sq_nonneg l) (sq_nonneg (δ * (n : ℝ)))) _)).trans hbound
  calc
    ∑ b ∈ Finset.univ, ∑ n ∈ Finset.range (N + 1), gridCoordWeight δ l α (b, n) =
        2 * ∑ n ∈ Finset.range (N + 1), gridCoordWeight δ l α (false, n) := by
      simp [gridCoordWeight]
    _ ≤ 2 * B := mul_le_mul_of_nonneg_left hnat (by norm_num)

private lemma grid_array_box_sum_bound [DecidableEq (InfinitePlace F × Fin 2)]
    (N : ℕ) (δ α : ℝ)
    (l : InfinitePlace F → ℝ) (B : InfinitePlace F × Fin 2 → ℝ)
    (hcoord : ∀ j : InfinitePlace F × Fin 2,
      (∑ c ∈ Finset.univ.product (Finset.range (N + 1)),
        gridCoordWeight δ (l j.1) α c) ≤ B j) :
    (∑ c ∈ Fintype.piFinset (fun _ : InfinitePlace F × Fin 2 =>
      Finset.univ.product (Finset.range (N + 1))), gridArrayWeight δ l α c) ≤
      ∏ j : InfinitePlace F × Fin 2, B j := by
  classical
  change (∑ c ∈ Fintype.piFinset (fun _ : InfinitePlace F × Fin 2 =>
      Finset.univ.product (Finset.range (N + 1))),
      ∏ j : InfinitePlace F × Fin 2, gridCoordWeight δ (l j.1) α (c j)) ≤ _
  rw [Finset.sum_prod_piFinset]
  apply Finset.prod_le_prod₀
  · intro j hj
    exact Finset.sum_nonneg fun c hc => by
      unfold gridCoordWeight
      exact Real.rpow_nonneg
        (add_nonneg (sq_nonneg (l j.1)) (sq_nonneg (δ * (c.2 : ℝ)))) _
  · intro j hj
    exact hcoord j

/-- The shifted PRODUCT-lattice estimate, uniform in the shift and individual scales.
Uses only denominator-lattice discreteness,
product shell packing, and finite products of geometric series; feeds
`balanced_first_coordinate_fiber_bound`. The constant is chosen before the exponent,
shift and scales; the exponent threshold is one, independent of the number of places. -/
theorem shifted_product_lattice_bound (D : ℕ) (hD : 0 < D)
    (lmin αmin αmax : ℝ) (hlmin : 0 < lmin) (hαmin : 1 < αmin)
    (hαrange : αmin ≤ αmax) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, αmin ≤ α → α ≤ αmax →
      ∀ (u : InfinitePlace F → ℂ) (l : InfinitePlace F → ℝ),
        (∀ w, lmin ≤ l w) →
      Summable (fun a : DenominatorScalars (F := F) D =>
          shiftedProductKernel u l α a.1) ∧
        (∑' a : DenominatorScalars (F := F) D, shiftedProductKernel u l α a.1) ≤
          C * ∏ w : InfinitePlace F, Real.rpow (l w) (2 - 2 * α) := by
  classical
  let δ : ℝ := (4 * (D : ℝ))⁻¹
  have hDℝ : 0 < (D : ℝ) := by exact_mod_cast hD
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK, hKbound⟩ :=
    grid_nat_weight_bound δ lmin αmin αmax hδ hlmin hαmin hαrange
  let C : ℝ := ∏ j : InfinitePlace F × Fin 2, 2 * K
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact Finset.prod_nonneg fun j hj => mul_nonneg (by norm_num) hK
  · intro α hαlo hαhi u l hl
    have hαpos : 0 < α := lt_of_lt_of_le (lt_trans zero_lt_one hαmin) hαlo
    let grid : DenominatorScalars (F := F) D →
        (InfinitePlace F × Fin 2 → Bool × ℕ) :=
      fun a => shiftedGridCell δ u a.1
    have hgridinj : Function.Injective grid := by
      intro a b hab
      exact shiftedGridCell_injective D hD u (by simpa [grid, δ] using hab)
    have hkernel_le_grid (a : DenominatorScalars (F := F) D) :
        shiftedProductKernel u l α a.1 ≤ gridArrayWeight δ l α (grid a) := by
      let c := grid a
      have hplace (w : InfinitePlace F) :
          Real.rpow (Complex.normSq (w.embedding a.1 + u w) + (l w) ^ 2) (-α) ≤
            gridCoordWeight δ (l w) α (c (w, 0)) *
              gridCoordWeight δ (l w) α (c (w, 1)) := by
        have hcr : δ * ((c (w, 0)).2 : ℝ) ≤ |(w.embedding a.1 + u w).re| := by
          simpa [c, grid, shiftedGridCell, gridRadius] using
            (gridRadius_le_abs δ (w.embedding a.1 + u w).re hδ)
        have hci : δ * ((c (w, 1)).2 : ℝ) ≤ |(w.embedding a.1 + u w).im| := by
          simpa [c, grid, shiftedGridCell, gridRadius] using
            (gridRadius_le_abs δ (w.embedding a.1 + u w).im hδ)
        exact grid_place_kernel_le δ (l w) α hδ (lt_of_lt_of_le hlmin (hl w)) hαpos
          (w.embedding a.1 + u w) (c (w, 0)) (c (w, 1)) hcr hci
      have hnonneg (w : InfinitePlace F) :
          0 ≤ Real.rpow (Complex.normSq (w.embedding a.1 + u w) + (l w) ^ 2) (-α) := by
        exact Real.rpow_nonneg
          (add_nonneg (Complex.normSq_nonneg _) (sq_nonneg (l w))) _
      have hprod :
          (∏ w : InfinitePlace F,
            Real.rpow (Complex.normSq (w.embedding a.1 + u w) + (l w) ^ 2) (-α)) ≤
          ∏ w : InfinitePlace F,
            (gridCoordWeight δ (l w) α (c (w, 0)) *
              gridCoordWeight δ (l w) α (c (w, 1))) := by
        apply Finset.prod_le_prod₀
        · intro w hw
          exact hnonneg w
        · intro w hw
          exact hplace w
      unfold shiftedProductKernel
      calc
        (∏ w : InfinitePlace F,
          Real.rpow (Complex.normSq (w.embedding a.1 + u w) + (l w) ^ 2) (-α)) ≤
          ∏ w : InfinitePlace F,
            (gridCoordWeight δ (l w) α (c (w, 0)) *
              gridCoordWeight δ (l w) α (c (w, 1))) := hprod
        _ = gridArrayWeight δ l α (grid a) := by
          change (∏ w : InfinitePlace F,
              gridCoordWeight δ (l w) α (c (w, 0)) *
                gridCoordWeight δ (l w) α (c (w, 1))) =
            ∏ j : InfinitePlace F × Fin 2, gridCoordWeight δ (l j.1) α (c j)
          calc
            (∏ w : InfinitePlace F,
                gridCoordWeight δ (l w) α (c (w, 0)) *
                  gridCoordWeight δ (l w) α (c (w, 1))) =
                ∏ w : InfinitePlace F, ∏ i : Fin 2,
                  gridCoordWeight δ (l w) α (c (w, i)) := by
              apply Finset.prod_congr rfl
              intro w hw
              rw [Fin.prod_univ_two]
            _ = ∏ j : InfinitePlace F × Fin 2, gridCoordWeight δ (l j.1) α (c j) := by
              exact (Fintype.prod_prod_type
                (fun j : InfinitePlace F × Fin 2 => gridCoordWeight δ (l j.1) α (c j))).symm
    have hfinite (s : Finset (DenominatorScalars (F := F) D)) :
        (∑ a ∈ s, shiftedProductKernel u l α a.1) ≤
          C * ∏ w : InfinitePlace F, Real.rpow (l w) (2 - 2 * α) := by
      let N : ℕ := ∑ a ∈ s, ∑ j : InfinitePlace F × Fin 2, (grid a j).2
      let coordBox : Finset (Bool × ℕ) := Finset.univ.product (Finset.range (N + 1))
      let arrayBox : Finset (InfinitePlace F × Fin 2 → Bool × ℕ) :=
        Fintype.piFinset (fun _ => coordBox)
      have hNmem (a : DenominatorScalars (F := F) D) (ha : a ∈ s)
          (j : InfinitePlace F × Fin 2) : (grid a j).2 ≤ N := by
        dsimp [N]
        calc
          (grid a j).2 ≤ ∑ j' : InfinitePlace F × Fin 2, (grid a j').2 := by
            exact Finset.single_le_sum
              (f := fun j' : InfinitePlace F × Fin 2 => (grid a j').2)
              (fun j' hj' => Nat.zero_le ((grid a j').2)) (Finset.mem_univ j)
          _ ≤ ∑ a' ∈ s, ∑ j' : InfinitePlace F × Fin 2, (grid a' j').2 :=
            Finset.single_le_sum
              (f := fun a' : DenominatorScalars (F := F) D =>
                ∑ j' : InfinitePlace F × Fin 2, (grid a' j').2)
              (fun a' ha' => Nat.zero_le _) ha
      have himage_subset : s.image grid ⊆ arrayBox := by
        intro c hc
        rcases Finset.mem_image.mp hc with ⟨a, ha, rfl⟩
        change grid a ∈ Fintype.piFinset (fun _ => coordBox)
        rw [Fintype.mem_piFinset]
        intro j
        apply Finset.mem_product.mpr
        constructor
        · exact Finset.mem_univ _
        · rw [Finset.mem_range]
          exact Nat.lt_succ_of_le (hNmem a ha j)
      let B : InfinitePlace F × Fin 2 → ℝ := fun j =>
        2 * K * Real.rpow (l j.1) (1 - α)
      have hcoord (j : InfinitePlace F × Fin 2) :
          (∑ c ∈ coordBox, gridCoordWeight δ (l j.1) α c) ≤ B j := by
        have hfiber := hKbound α hαlo hαhi (l j.1) (hl j.1)
        have hs : Summable (fun n : ℕ => gridCoordWeight δ (l j.1) α (false, n)) := by
          simpa [gridCoordWeight] using hfiber.1
        have hb : (∑' n : ℕ, gridCoordWeight δ (l j.1) α (false, n)) ≤
            K * Real.rpow (l j.1) (1 - α) := by
          simpa [gridCoordWeight] using hfiber.2
        have hbox := grid_coord_box_sum_bound δ (l j.1) α
          (K * Real.rpow (l j.1) (1 - α)) N hδ
          (lt_of_lt_of_le hlmin (hl j.1)) hs hb
        dsimp [B]
        calc
          (∑ c ∈ coordBox, gridCoordWeight δ (l j.1) α c) ≤
              2 * (K * Real.rpow (l j.1) (1 - α)) := by
            simpa [coordBox] using hbox
          _ = 2 * K * Real.rpow (l j.1) (1 - α) := by ring
      have hboxsum :
          (∑ c ∈ arrayBox, gridArrayWeight δ l α c) ≤
            ∏ j : InfinitePlace F × Fin 2, B j := by
        simpa [arrayBox, coordBox] using
          (grid_array_box_sum_bound N δ α l B hcoord)
      have hsum_grid :
          (∑ a ∈ s, shiftedProductKernel u l α a.1) ≤
            ∑ c ∈ s.image grid, gridArrayWeight δ l α c := by
        calc
          (∑ a ∈ s, shiftedProductKernel u l α a.1) ≤
              ∑ a ∈ s, gridArrayWeight δ l α (grid a) :=
            Finset.sum_le_sum fun a ha => hkernel_le_grid a
          _ = ∑ c ∈ s.image grid, gridArrayWeight δ l α c := by
            symm
            apply Finset.sum_image
            intro a ha b hb hab
            exact hgridinj hab
      have himage_le_box :
          (∑ c ∈ s.image grid, gridArrayWeight δ l α c) ≤
            ∑ c ∈ arrayBox, gridArrayWeight δ l α c := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himage_subset
        intro c hc hnot
        unfold gridArrayWeight
        apply Finset.prod_nonneg
        intro j hj
        exact Real.rpow_nonneg (by positivity) _
      have hscale_prod :
          (∏ j : InfinitePlace F × Fin 2, B j) =
            C * ∏ w : InfinitePlace F, Real.rpow (l w) (2 - 2 * α) := by
        dsimp [B, C]
        rw [Finset.prod_mul_distrib]
        congr 1
        calc
          (∏ j : InfinitePlace F × Fin 2, Real.rpow (l j.1) (1 - α)) =
              ∏ w : InfinitePlace F, ∏ i : Fin 2, Real.rpow (l w) (1 - α) :=
            Fintype.prod_prod_type _
          _ = ∏ w : InfinitePlace F, Real.rpow (l w) (2 - 2 * α) := by
            apply Finset.prod_congr rfl
            intro w hw
            calc
              (∏ i : Fin 2, Real.rpow (l w) (1 - α)) =
                  Real.rpow (l w) (1 - α) * Real.rpow (l w) (1 - α) := Fin.prod_univ_two _
              _ = Real.rpow (l w) ((1 - α) + (1 - α)) :=
                (Real.rpow_add (lt_of_lt_of_le hlmin (hl w)) _ _).symm
              _ = Real.rpow (l w) (2 - 2 * α) := by congr 1 <;> ring
      calc
        (∑ a ∈ s, shiftedProductKernel u l α a.1) ≤
            ∑ c ∈ s.image grid, gridArrayWeight δ l α c := hsum_grid
        _ ≤ ∑ c ∈ arrayBox, gridArrayWeight δ l α c := himage_le_box
        _ ≤ ∏ j : InfinitePlace F × Fin 2, B j := hboxsum
        _ = C * ∏ w : InfinitePlace F, Real.rpow (l w) (2 - 2 * α) := hscale_prod
    have hnonneg : ∀ a : DenominatorScalars (F := F) D,
        0 ≤ shiftedProductKernel u l α a.1 := by
      intro a
      unfold shiftedProductKernel
      apply Finset.prod_nonneg
      intro w hw
      exact Real.rpow_nonneg
        (add_nonneg (Complex.normSq_nonneg _) (sq_nonneg (l w))) _
    have hsumBound : ∀ s : Finset (DenominatorScalars (F := F) D),
        (∑ a ∈ s, shiftedProductKernel u l α a.1) ≤
          C * ∏ w : InfinitePlace F, Real.rpow (l w) (2 - 2 * α) := hfinite
    exact ⟨summable_of_sum_le hnonneg hsumBound,
      Real.tsum_le_of_sum_le hnonneg hsumBound⟩

end ArtinPrimitiveRoots.A1.Spec
