import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.shifted_product_lattice_bound

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private lemma balanced_product_coordinate_lower (B H : ℝ)
    (y : InfinitePlace F → ℝ) (hbal : IsBalancedHeights F B y)
    (hH : 0 < H) (hprod : H ≤ ∏ w : InfinitePlace F, y w) :
    ∀ w, Real.exp (Real.log H / placeCount F - B) ≤ y w := by
  rcases hbal with ⟨hy, hbal⟩
  have hr : 0 < placeCount F := by
    unfold placeCount
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (InfinitePlace F)))
  have hprodpos : 0 < ∏ w : InfinitePlace F, y w := lt_of_lt_of_le hH hprod
  have hlogprod : Real.log (∏ w : InfinitePlace F, y w) =
      ∑ w : InfinitePlace F, Real.log (y w) := by
    simpa using Real.log_prod (s := Finset.univ) (f := y) (by
      intro w hw
      exact (hy w).ne')
  have havg : (placeCount F)⁻¹ * ∑ w : InfinitePlace F, Real.log (y w) =
      Real.log (∏ w : InfinitePlace F, y w) / placeCount F := by
    rw [← hlogprod]
    simp [div_eq_mul_inv, mul_comm]
  have havg' : (Fintype.card (InfinitePlace F) : ℝ)⁻¹ *
      ∑ w : InfinitePlace F, Real.log (y w) =
        Real.log (∏ w : InfinitePlace F, y w) / placeCount F := by
    simpa [placeCount] using havg
  have hloglo : Real.log H ≤ Real.log (∏ w : InfinitePlace F, y w) :=
    Real.log_le_log hH hprod
  have havglo := div_le_div_of_nonneg_right hloglo hr.le
  intro w
  have hleft := (abs_le.mp (hbal w)).1
  rw [havg'] at hleft
  have hlog : Real.log H / placeCount F - B ≤ Real.log (y w) := by
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  simpa [Real.exp_log (hy w)] using hexp

private lemma embedding_norm_prod_sq (a : F) :
    (∏ w : InfinitePlace F, ‖w.embedding a‖) ^ 2 = absFieldNorm F a := by
  unfold absFieldNorm
  rw [← Finset.prod_pow]

private lemma row_kernel_eq_shifted (c a : F) (hc : c ≠ 0)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (α : ℝ) :
    siegelRowKernel (c, a) x y α =
      Real.rpow (∏ w : InfinitePlace F, y w) α *
        shiftedProductKernel (fun w => w.embedding c * x w)
          (fun w => ‖w.embedding c‖ * y w) α a := by
  have hcemb (w : InfinitePlace F) : w.embedding c ≠ 0 :=
    (map_ne_zero_iff _ w.embedding.injective).mpr hc
  have hnormpos (w : InfinitePlace F) : 0 < ‖w.embedding c‖ := norm_pos_iff.mpr (hcemb w)
  have hlpos (w : InfinitePlace F) : 0 < ‖w.embedding c‖ * y w := mul_pos (hnormpos w) (hy w)
  have hden (w : InfinitePlace F) :
      Complex.normSq (w.embedding c * x w + w.embedding a) +
        Complex.normSq (w.embedding c) * y w ^ 2 =
      Complex.normSq (w.embedding a + w.embedding c * x w) +
        (‖w.embedding c‖ * y w) ^ 2 := by
    rw [show w.embedding c * x w + w.embedding a =
      w.embedding a + w.embedding c * x w by exact add_comm _ _]
    calc
      Complex.normSq (w.embedding a + w.embedding c * x w) +
          Complex.normSq (w.embedding c) * y w ^ 2 =
        Complex.normSq (w.embedding a + w.embedding c * x w) +
          ‖w.embedding c‖ ^ 2 * y w ^ 2 := by
            rw [Complex.normSq_eq_norm_sq (w.embedding c)]
      _ = Complex.normSq (w.embedding a + w.embedding c * x w) +
          (‖w.embedding c‖ * y w) ^ 2 := by ring
  have hdenpos (w : InfinitePlace F) : 0 <
      Complex.normSq (w.embedding c * x w + w.embedding a) +
        Complex.normSq (w.embedding c) * y w ^ 2 := by
    rw [hden w]
    exact lt_of_lt_of_le (sq_pos_of_pos (hlpos w))
      (le_add_of_nonneg_left (Complex.normSq_nonneg _))
  have hterm (w : InfinitePlace F) :
      Real.rpow (y w /
        (Complex.normSq (w.embedding c * x w + w.embedding a) +
          Complex.normSq (w.embedding c) * y w ^ 2)) α =
      Real.rpow (y w) α * Real.rpow
        (Complex.normSq (w.embedding a + w.embedding c * x w) +
          (‖w.embedding c‖ * y w) ^ 2) (-α) := by
    have hzpos := hdenpos w
    rw [hden w] at hzpos
    calc
      _ = Real.rpow (y w) α /
          Real.rpow (Complex.normSq (w.embedding c * x w + w.embedding a) +
            Complex.normSq (w.embedding c) * y w ^ 2) α :=
          Real.div_rpow (hy w).le (hdenpos w).le α
      _ = _ := by
        rw [hden w]
        calc
          Real.rpow (y w) α /
              Real.rpow (Complex.normSq (w.embedding a + w.embedding c * x w) +
                (‖w.embedding c‖ * y w) ^ 2) α =
            Real.rpow (y w) α *
              (Real.rpow (Complex.normSq (w.embedding a + w.embedding c * x w) +
                (‖w.embedding c‖ * y w) ^ 2) α)⁻¹ := div_eq_mul_inv _ _
          _ = _ := by
            exact congrArg (fun z : ℝ => Real.rpow (y w) α * z)
              (Real.rpow_neg hzpos.le α).symm
  have hY : 0 < ∏ w : InfinitePlace F, y w := Finset.prod_pos (fun w hw => hy w)
  have hYpow : (∏ w : InfinitePlace F, Real.rpow (y w) α) =
      Real.rpow (∏ w : InfinitePlace F, y w) α := by
    exact Real.finsetProd_rpow Finset.univ y (by intro w hw; exact (hy w).le) α
  unfold siegelRowKernel shiftedProductKernel
  calc
    (∏ w : InfinitePlace F,
      Real.rpow (y w /
        (Complex.normSq (w.embedding c * x w + w.embedding a) +
          Complex.normSq (w.embedding c) * y w ^ 2)) α) =
        ∏ w : InfinitePlace F,
          (Real.rpow (y w) α * Real.rpow
            (Complex.normSq (w.embedding a + w.embedding c * x w) +
              (‖w.embedding c‖ * y w) ^ 2) (-α)) := by
      apply Finset.prod_congr rfl
      intro w hw
      exact hterm w
    _ = (∏ w : InfinitePlace F, Real.rpow (y w) α) *
        ∏ w : InfinitePlace F,
          Real.rpow (Complex.normSq (w.embedding a + w.embedding c * x w) +
            (‖w.embedding c‖ * y w) ^ 2) (-α) := Finset.prod_mul_distrib
    _ = _ := by rw [hYpow]

/-- Substitute `l_w = |w(c)| y_w` in the shifted product-lattice bound.
Balanced nonzero c and positive balanced heights with a product floor give a uniform
positive scale floor. Guide: `sol-thin-spec/PROOFS.md:353–358`. Uses
`shifted_product_lattice_bound` and the positive integer norm lower bound; feeds
`balanced_denominator_rows_bound`. -/
theorem balanced_first_coordinate_fiber_bound (D : ℕ) (hD : 0 < D)
    (Bc By H αmin αmax : ℝ) (hBc : 0 ≤ Bc) (hBy : 0 ≤ By) (hH : 0 < H)
    (hαmin : 1 < αmin) (hαrange : αmin ≤ αmax) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, αmin ≤ α → α ≤ αmax →
      ∀ c : F, c ≠ 0 → HasDenominatorBound F D c →
        IsBalancedHeights F Bc (fun w => ‖w.embedding c‖) →
      ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
        IsBalancedHeights F By y → H ≤ ∏ w, y w →
        Summable (fun a : DenominatorScalars (F := F) D =>
          siegelRowKernel (c, a.1) x y α) ∧
        (∑' a : DenominatorScalars (F := F) D, siegelRowKernel (c, a.1) x y α) ≤
          C * Real.rpow (∏ w, y w) (2 - α) *
            Real.rpow (absFieldNorm F c) (1 - α) := by
  classical
  let r : ℝ := placeCount F
  let M : ℝ := absFieldNorm F (D : F)
  let Hc : ℝ := Real.sqrt (M⁻¹)
  let lmin : ℝ :=
    Real.exp (Real.log Hc / r - Bc) * Real.exp (Real.log H / r - By)
  have hr : 0 < r := by
    dsimp [r, placeCount]
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (InfinitePlace F)))
  have hMpos : 0 < M := by
    dsimp [M]
    exact absFieldNorm_pos_of_ne_zero (by exact_mod_cast hD.ne')
  have hHcpos : 0 < Hc := by
    dsimp [Hc]
    exact Real.sqrt_pos.2 (inv_pos.mpr hMpos)
  have hlmin : 0 < lmin := by
    dsimp [lmin]
    positivity
  obtain ⟨CL, hCL, hL⟩ :=
    shifted_product_lattice_bound (F := F) D hD lmin αmin αmax hlmin hαmin hαrange
  refine ⟨CL, hCL, ?_⟩
  intro α hαlo hαhi c hc hcD hcbal x y hy hHY
  let P : ℝ := ∏ w : InfinitePlace F, ‖w.embedding c‖
  let Y : ℝ := ∏ w : InfinitePlace F, y w
  have hPpos : 0 < P := by
    dsimp [P]
    apply Finset.prod_pos
    intro w hw
    apply norm_pos_iff.mpr
    exact (map_ne_zero_iff _ w.embedding.injective).mpr hc
  have hYpos : 0 < Y := by
    dsimp [Y]
    exact Finset.prod_pos (fun w hw => hy.1 w)
  have hnormInv := absFieldNorm_inv_le_of_denominatorBound hD hcD hc
  have hNpos : 0 < absFieldNorm F c := absFieldNorm_pos_of_ne_zero hc
  have hMN : M⁻¹ ≤ absFieldNorm F c := by
    have hmul : 1 ≤ absFieldNorm F c * M := by
      calc
        1 = absFieldNorm F c * (absFieldNorm F c)⁻¹ :=
          (mul_inv_cancel₀ hNpos.ne').symm
        _ ≤ absFieldNorm F c * M := mul_le_mul_of_nonneg_left hnormInv hNpos.le
    rw [inv_eq_one_div, div_le_iff₀ hMpos]
    exact hmul
  have hPsq : P ^ 2 = absFieldNorm F c := by
    dsimp [P]
    exact embedding_norm_prod_sq c
  have hHcP : Hc ≤ P := by
    have hsqrt : Real.sqrt (M⁻¹) ≤ Real.sqrt (P ^ 2) := by
      apply Real.sqrt_le_sqrt
      rw [hPsq]
      exact hMN
    simpa [Hc, Real.sqrt_sq_eq_abs, abs_of_pos hPpos] using hsqrt
  have hclower := balanced_product_coordinate_lower Bc Hc
    (fun w => ‖w.embedding c‖) hcbal hHcpos hHcP
  have hylower := balanced_product_coordinate_lower By H y hy hH hHY
  have hl (w : InfinitePlace F) :
      lmin ≤ ‖w.embedding c‖ * y w := by
    dsimp [lmin, r, Hc]
    calc
      Real.exp (Real.log (Real.sqrt (M⁻¹)) / placeCount F - Bc) *
          Real.exp (Real.log H / placeCount F - By) ≤
        ‖w.embedding c‖ * Real.exp (Real.log H / placeCount F - By) :=
          mul_le_mul_of_nonneg_right (hclower w) (Real.exp_nonneg _)
      _ ≤ ‖w.embedding c‖ * y w :=
          mul_le_mul_of_nonneg_left (hylower w) (norm_nonneg _)
  have hYpos' : 0 < ∏ w : InfinitePlace F, y w :=
    Finset.prod_pos (fun w hw => hy.1 w)
  let u : InfinitePlace F → ℂ := fun w => w.embedding c * x w
  let l : InfinitePlace F → ℝ := fun w => ‖w.embedding c‖ * y w
  have hl' (w : InfinitePlace F) : lmin ≤ l w := by
    dsimp [l]
    exact hl w
  have hshift := hL α hαlo hαhi u l hl'
  have hroweq (a : DenominatorScalars (F := F) D) :
      siegelRowKernel (c, a.1) x y α =
        Real.rpow (∏ w : InfinitePlace F, y w) α *
          shiftedProductKernel u l α a.1 := by
    simpa [u, l] using row_kernel_eq_shifted c a.1 hc x y hy.1 α
  have hrowsum :
      (∑' a : DenominatorScalars (F := F) D, siegelRowKernel (c, a.1) x y α) =
        Real.rpow (∏ w : InfinitePlace F, y w) α *
          (∑' a : (DenominatorScalars (F := F) D),
            shiftedProductKernel u l α a.1) := by
    calc
      _ = ∑' a : (DenominatorScalars (F := F) D),
          Real.rpow (∏ w : InfinitePlace F, y w) α *
            shiftedProductKernel u l α a.1 := tsum_congr hroweq
      _ = _ := hshift.1.tsum_mul_left _
  have hprodL :
      (∏ w : InfinitePlace F, Real.rpow (l w) (2 - 2 * α)) =
        Real.rpow P (2 - 2 * α) * Real.rpow Y (2 - 2 * α) := by
    have hprodly : (∏ w : InfinitePlace F, l w) = P * Y := by
      dsimp [l, P, Y]
      rw [Finset.prod_mul_distrib]
    calc
      _ = Real.rpow (∏ w : InfinitePlace F, l w) (2 - 2 * α) :=
        Real.finsetProd_rpow Finset.univ l (by intro w hw; exact (mul_nonneg (norm_nonneg _) (hy.1 w).le)) _
      _ = Real.rpow (P * Y) (2 - 2 * α) := by rw [hprodly]
      _ = _ := Real.mul_rpow hPpos.le hYpos'.le
  have hPpow : Real.rpow P (2 - 2 * α) =
      Real.rpow (absFieldNorm F c) (1 - α) := by
    calc
      Real.rpow P (2 - 2 * α) = Real.rpow P (2 * (1 - α)) := by congr 1 <;> ring
      _ = Real.rpow (Real.rpow P (2 : ℝ)) (1 - α) :=
        Real.rpow_mul hPpos.le 2 (1 - α)
      _ = Real.rpow (absFieldNorm F c) (1 - α) := by
        congr 1
        calc
          Real.rpow P (2 : ℝ) = P ^ 2 := Real.rpow_two P
          _ = absFieldNorm F c := hPsq
  have hYpow : Real.rpow Y α * Real.rpow Y (2 - 2 * α) =
      Real.rpow Y (2 - α) := by
    calc
      Real.rpow Y α * Real.rpow Y (2 - 2 * α) =
          Real.rpow Y (α + (2 - 2 * α)) :=
        (Real.rpow_add hYpos' α (2 - 2 * α)).symm
      _ = Real.rpow Y (2 - α) := by congr 1 <;> ring
  have hrowsummable : Summable (fun a : DenominatorScalars (F := F) D =>
      siegelRowKernel (c, a.1) x y α) :=
    (hshift.1.mul_left (Real.rpow Y α)).congr (fun a => (hroweq a).symm)
  refine ⟨hrowsummable, ?_⟩
  rw [hrowsum]
  calc
    Real.rpow Y α * (∑' a : DenominatorScalars (F := F) D,
        shiftedProductKernel u l α a.1) ≤
      Real.rpow Y α * (CL * ∏ w : InfinitePlace F, Real.rpow (l w) (2 - 2 * α)) :=
        mul_le_mul_of_nonneg_left hshift.2 (Real.rpow_nonneg hYpos'.le _)
    _ = CL * Real.rpow Y (2 - α) * Real.rpow (absFieldNorm F c) (1 - α) := by
      rw [hprodL, hPpow]
      calc
        Real.rpow Y α * (CL *
            (Real.rpow (absFieldNorm F c) (1 - α) * Real.rpow Y (2 - 2 * α))) =
            CL * (Real.rpow Y α * Real.rpow Y (2 - 2 * α)) *
              Real.rpow (absFieldNorm F c) (1 - α) := by ring
        _ = _ := by rw [hYpow]

end ArtinPrimitiveRoots.A1.Spec
