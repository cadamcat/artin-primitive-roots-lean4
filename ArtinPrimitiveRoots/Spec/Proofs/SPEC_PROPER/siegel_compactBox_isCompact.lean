import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem siegel_lowerHeight_pos (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (i : d.ι) : 0 < SiegelData.lowerHeight F d i := by
  let g : SL(2,F) := (d.σ i)⁻¹
  have hrow : g 1 0 ≠ 0 ∨ g 1 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have hd := g.2
    rw [Matrix.det_fin_two] at hd
    simp [h.1, h.2] at hd
  have hI : bottomRowFractionalIdeal F g ≠ 0 := by
    rw [bottomRowFractionalIdeal, FractionalIdeal.spanFinset_ne_zero]
    rcases hrow with h | h
    · exact ⟨0, Finset.mem_univ _, by simpa [bottomRow] using h⟩
    · exact ⟨1, Finset.mem_univ _, by simpa [bottomRow] using h⟩
  have hnorm : FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) ≠ 0 := by
    intro hz
    exact hI (FractionalIdeal.absNorm_eq_zero_iff.mp hz)
  have hnormQ : 0 < FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm hnorm)
  have hnormR : 0 < ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) : ℚ) : ℝ) :=
    by exact_mod_cast hnormQ
  dsimp [SiegelData.lowerHeight]
  exact inv_pos.mpr (mul_pos hnormR d.C_M_pos)

private theorem siegel_normHeight_ptX'_eq (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    normHeight F (ptX' F x y) = ∏ w : InfinitePlace F, y w := by
  change (∏ w : InfinitePlace F, height ((ptX' F x y) w)) = _
  apply Finset.prod_congr rfl
  intro w hw
  exact (G1_h3_basics (F := F)).1 (x w) (y w) (hy w)

private theorem siegel_balanced_height_bounds (y : InfinitePlace F → ℝ) (B c A : ℝ)
    (hy : ∀ w, 0 < y w)
    (hbal : ∀ w, |Real.log (y w) - (placeCount F)⁻¹ *
      ∑ w' : InfinitePlace F, Real.log (y w')| ≤ B)
    (hc : 0 < c) (hlo : c ≤ ∏ w : InfinitePlace F, y w)
    (hhi : (∏ w : InfinitePlace F, y w) ≤ A) :
    ∀ w, Real.exp (Real.log c / placeCount F - B) ≤ y w ∧
      y w ≤ Real.exp (Real.log A / placeCount F + B) := by
  have hr : 0 < placeCount F := by
    unfold placeCount
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (InfinitePlace F)))
  have hprodpos : 0 < ∏ w : InfinitePlace F, y w := lt_of_lt_of_le hc hlo
  have hlogprod : Real.log (∏ w : InfinitePlace F, y w) =
      ∑ w : InfinitePlace F, Real.log (y w) := by
    simpa using (Real.log_prod (s := Finset.univ) (f := y) (by
      intro w hw
      exact (hy w).ne'))
  have havg : (placeCount F)⁻¹ * ∑ w : InfinitePlace F, Real.log (y w) =
      Real.log (∏ w : InfinitePlace F, y w) / placeCount F := by
    rw [← hlogprod]
    simp [div_eq_mul_inv, mul_comm]
  have hloglo : Real.log c ≤ Real.log (∏ w : InfinitePlace F, y w) :=
    Real.log_le_log hc hlo
  have hloghi : Real.log (∏ w : InfinitePlace F, y w) ≤ Real.log A :=
    Real.log_le_log hprodpos hhi
  have havglo := div_le_div_of_nonneg_right hloglo (le_of_lt hr)
  have havghi := div_le_div_of_nonneg_right hloghi (le_of_lt hr)
  intro w
  have hleft := (abs_le.mp (hbal w)).1
  have hright := (abs_le.mp (hbal w)).2
  rw [havg] at hleft hright
  constructor
  · have hlog : Real.log c / placeCount F - B ≤ Real.log (y w) := by linarith
    have := Real.exp_le_exp.mpr hlog
    simpa [Real.exp_log (hy w)] using this
  · have hlog : Real.log (y w) ≤ Real.log A / placeCount F + B := by linarith
    have := Real.exp_le_exp.mpr hlog
    simpa [Real.exp_log (hy w)] using this

/-- A bounded product height in a balanced cusp chart gives a compact box.
Guide: sol-thin-spec/PROOFS.md:204 and 230–234 (R13 first conjunct only).
Uses G1_h3_basics, R3_cusps_finite for the positive lower height, and d.P_bounded;
feeds siegel_low_height_overlap_finite without using R13's orbit-cover conclusion. -/
theorem siegel_compactBox_isCompact (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 ≤ A) (i : d.ι) :
    IsCompact (SiegelData.compactBox F d i A) := by
  let c := SiegelData.lowerHeight F d i
  have hc : 0 < c := siegel_lowerHeight_pos Γ d i
  by_cases hAc : A < c
  · have hempty : SiegelData.compactBox F d i A = ∅ := by
      ext z
      constructor
      · rintro ⟨x, y, hEq, hx, hbal, hlo, hhi⟩
        have : c ≤ A := le_trans hlo hhi
        exact (not_le_of_gt hAc) this
      · simp
    simpa [hempty]
  · have hca : c ≤ A := le_of_not_gt hAc
    have hApos : 0 < A := hc.trans_le hca
    let lo := Real.exp (Real.log c / placeCount F - 2 * d.B i)
    let hi := Real.exp (Real.log A / placeCount F + 2 * d.B i)
    have hloPos : 0 < lo := Real.exp_pos _
    let Xcoord := InfinitePlace F → ℂ
    let Ycoord := InfinitePlace F → ℝ
    let K : Set (Xcoord × Ycoord) :=
      {p | p.1 ∈ closure (d.P i) ∧
        (∀ w, p.2 w ∈ Set.Icc lo hi) ∧
        (∀ w, |Real.log (max lo (p.2 w)) - (placeCount F)⁻¹ *
          ∑ w' : InfinitePlace F, Real.log (max lo (p.2 w'))| ≤ 2 * d.B i) ∧
        (∏ w : InfinitePlace F, p.2 w) ∈ Set.Icc c A}
    let Ybox : Set Ycoord := {y | ∀ w, y w ∈ Set.Icc lo hi}
    have hPcompact : IsCompact (closure (d.P i)) := (d.P_bounded i).isCompact_closure
    have hYcompact : IsCompact Ybox := by
      exact isCompact_pi_infinite (fun _ => isCompact_Icc)
    have hbase : IsCompact (closure (d.P i) ×ˢ Ybox) := hPcompact.prod hYcompact
    have hlogClamp : Continuous (fun t : ℝ => Real.log (max lo t)) := by
      apply Real.continuousOn_log.comp_continuous
      · fun_prop
      · intro t
        exact ne_of_gt (lt_of_lt_of_le hloPos (le_max_left _ _))
    have hlogW : ∀ w, Continuous (fun p : Xcoord × Ycoord =>
        Real.log (max lo (p.2 w))) := fun w =>
      hlogClamp.comp ((continuous_apply w).comp continuous_snd)
    have hlogSum : Continuous (fun p : Xcoord × Ycoord =>
        ∑ w : InfinitePlace F, Real.log (max lo (p.2 w))) := by
      exact continuous_finsetSum Finset.univ (fun w hw => hlogW w)
    have hbalanceFun (w : InfinitePlace F) : Continuous (fun p : Xcoord × Ycoord =>
        |Real.log (max lo (p.2 w)) - (placeCount F)⁻¹ *
          ∑ w' : InfinitePlace F, Real.log (max lo (p.2 w'))|) := by
      exact ((hlogW w).sub (continuous_const.mul hlogSum)).abs
    have hPclosed : IsClosed {p : Xcoord × Ycoord | p.1 ∈ closure (d.P i)} :=
      isClosed_closure.preimage continuous_fst
    have hYclosed : IsClosed {p : Xcoord × Ycoord | ∀ w, p.2 w ∈ Set.Icc lo hi} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun w =>
        isClosed_Icc.preimage ((continuous_apply w).comp continuous_snd)
    have hbalanceClosed : IsClosed {p : Xcoord × Ycoord |
        ∀ w, |Real.log (max lo (p.2 w)) - (placeCount F)⁻¹ *
          ∑ w' : InfinitePlace F, Real.log (max lo (p.2 w'))| ≤ 2 * d.B i} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun w => isClosed_Iic.preimage (hbalanceFun w)
    have hprodFun : Continuous (fun p : Xcoord × Ycoord =>
        ∏ w : InfinitePlace F, p.2 w) := by
      exact continuous_finsetProd Finset.univ (fun w hw =>
        (continuous_apply w).comp continuous_snd)
    have hprodClosed : IsClosed {p : Xcoord × Ycoord |
        (∏ w : InfinitePlace F, p.2 w) ∈ Set.Icc c A} :=
      isClosed_Icc.preimage hprodFun
    have hKclosed : IsClosed K := by
      change IsClosed ({p : Xcoord × Ycoord | p.1 ∈ closure (d.P i)} ∩
        ({p | ∀ w, p.2 w ∈ Set.Icc lo hi} ∩
          ({p | ∀ w, |Real.log (max lo (p.2 w)) - (placeCount F)⁻¹ *
            ∑ w' : InfinitePlace F, Real.log (max lo (p.2 w'))| ≤ 2 * d.B i} ∩
            {p | (∏ w : InfinitePlace F, p.2 w) ∈ Set.Icc c A})))
      exact hPclosed.inter (hYclosed.inter (hbalanceClosed.inter hprodClosed))
    have hKsub : K ⊆ closure (d.P i) ×ˢ Ybox := by
      intro p hp
      exact ⟨hp.1, hp.2.1⟩
    have hKcompact : IsCompact K := hbase.of_isClosed_subset hKclosed hKsub
    rcases G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, he, _⟩⟩
    let q : Xcoord × Ycoord → {p : Coord F // p ∈ posSet F} := fun p =>
      ⟨fun w => (p.1 w, max lo (p.2 w)), fun w =>
        lt_of_lt_of_le hloPos (le_max_left _ _)⟩
    have hq : Continuous q := by
      dsimp [q]
      apply Continuous.subtype_mk
      apply continuous_pi
      intro w
      fun_prop
    let φ : Xcoord × Ycoord → X F := fun p => (d.σ i) • e (q p)
    rcases G2_x_action (F := F) with ⟨_, _, _, hhomeo, _⟩
    obtain ⟨eσ, heσ, _⟩ := hhomeo (toInf F (d.σ i))
    have hact : Continuous (fun z : X F => (d.σ i) • z) := by
      have heq : (fun z : X F => (d.σ i) • z) = eσ := by
        funext z
        rw [heσ z]
        rfl
      rw [heq]
      exact eσ.continuous
    have hφ : Continuous φ := by
      dsimp [φ]
      exact hact.comp (e.continuous.comp hq)
    have hφcoord (x : Xcoord) (y : Ycoord) (hylo : ∀ w, lo ≤ y w) :
        φ (x, y) = (d.σ i) • ptX' F x y := by
      have hpoint : ptX F (q (x, y)).val = ptX' F x y := by
        ext w
        simp [q, ptX, ptX', max_eq_right (hylo w)]
      change (d.σ i) • e (q (x, y)) = _
      rw [he (q (x, y)), hpoint]
    have hboxeq : SiegelData.compactBox F d i A = φ '' K := by
      ext z
      constructor
      · rintro ⟨x, y, hz, hx, hbal, hlo, hhi⟩
        have hN := siegel_normHeight_ptX'_eq x y hbal.1
        have hprodlo : c ≤ ∏ w : InfinitePlace F, y w := by simpa [hN, c] using hlo
        have hprodhi : (∏ w : InfinitePlace F, y w) ≤ A := by simpa [hN] using hhi
        have hbounds := siegel_balanced_height_bounds y (2 * d.B i) c A hbal.1 hbal.2 hc
          hprodlo hprodhi
        have hmax : ∀ w, max lo (y w) = y w := fun w => max_eq_right (hbounds w).1
        refine ⟨(x, y), ?_, ?_⟩
        · refine ⟨hx, ?_, ?_, ?_⟩
          · intro w
            exact Set.mem_Icc.mpr (hbounds w)
          · intro w
            simpa [placeCount, hmax] using hbal.2 w
          · exact Set.mem_Icc.mpr ⟨hprodlo, hprodhi⟩
        · calc
            φ (x, y) = (d.σ i) • ptX' F x y := hφcoord x y (fun w => (hbounds w).1)
            _ = z := hz.symm
      · rintro ⟨⟨x, y⟩, hp, rfl⟩
        have hy : ∀ w, 0 < y w := fun w =>
          lt_of_lt_of_le hloPos (Set.mem_Icc.mp (hp.2.1 w)).1
        have hmax : ∀ w, max lo (y w) = y w := fun w =>
          max_eq_right (Set.mem_Icc.mp (hp.2.1 w)).1
        have hbal : IsBalancedHeights F (2 * d.B i) y := by
          refine ⟨hy, ?_⟩
          intro w
          simpa [placeCount, hmax] using hp.2.2.1 w
        have hN := siegel_normHeight_ptX'_eq x y hy
        refine ⟨x, y, ?_, hp.1, hbal, ?_, ?_⟩
        · exact hφcoord x y (fun w => (Set.mem_Icc.mp (hp.2.1 w)).1)
        · simpa [hN, c] using (Set.mem_Icc.mp hp.2.2.2).1
        · simpa [hN] using (Set.mem_Icc.mp hp.2.2.2).2
    rw [hboxeq]
    exact hKcompact.image hφ
end ArtinPrimitiveRoots.A1.Spec
