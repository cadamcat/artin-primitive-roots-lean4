import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem specSiegelB_posSet_open : IsOpen (posSet F) := by
  rw [posSet, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro w
  have hc : Continuous (fun p : Coord F => (p w).2) := by fun_prop
  exact IsOpen.preimage hc (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

private theorem specSiegelB_normHeight_pos (z : X F) : 0 < normHeight F z := by
  unfold normHeight
  apply Finset.prod_pos
  intro w hw
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private theorem specSiegelB_normHeight_action_smooth (g : SL(2,F)) :
    IsSmoothRealX F (fun z => normHeight F (g • z)) := by
  change ContDiffOn ℝ ∞ (fun p => normHeight F (g • ptX F p)) (posSet F)
  let den : InfinitePlace F → Coord F → ℝ := fun w p =>
    Complex.normSq (w.embedding (g 1 0) * (p w).1 + w.embedding (g 1 1)) +
      Complex.normSq (w.embedding (g 1 0)) * (p w).2 ^ 2
  have hden_smooth (w : InfinitePlace F) :
      ContDiffOn ℝ ∞ (fun p => den w p) (posSet F) := by
    let f : Coord F → ℂ := fun p =>
      w.embedding (g 1 0) * (p w).1 + w.embedding (g 1 1)
    have hf : ContDiffOn ℝ ∞ f (posSet F) := by
      dsimp [f]
      fun_prop
    have hre : ContDiffOn ℝ ∞ (fun p => (f p).re) (posSet F) := by
      have h := Complex.reCLM.contDiff.comp_contDiffOn hf
      convert h using 1 <;> ext p <;> rfl
    have him : ContDiffOn ℝ ∞ (fun p => (f p).im) (posSet F) := by
      have h := Complex.imCLM.contDiff.comp_contDiffOn hf
      convert h using 1 <;> ext p <;> rfl
    have hnorm : ContDiffOn ℝ ∞ (fun p => Complex.normSq (f p)) (posSet F) := by
      simpa [Complex.normSq_apply, pow_two] using (hre.mul hre).add (him.mul him)
    have hc : ContDiffOn ℝ ∞ (fun _ : Coord F => Complex.normSq (w.embedding (g 1 0)))
        (posSet F) := contDiffOn_const
    have hy : ContDiffOn ℝ ∞ (fun p : Coord F => (p w).2) (posSet F) := by fun_prop
    have hsecond : ContDiffOn ℝ ∞
        (fun p => Complex.normSq (w.embedding (g 1 0)) * (p w).2 ^ 2) (posSet F) := by
      simpa [pow_two] using hc.mul (hy.mul hy)
    simpa [den, f, Complex.normSq_apply] using hnorm.add hsecond
  have hden_pos (w : InfinitePlace F) (p : Coord F) (hp : p ∈ posSet F) :
      0 < den w p := by
    have hy : 0 < (p w).2 := hp w
    have hheight : 0 < height ((g • ptX F p) w) := by
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos ((g • ptX F p) w)
    have hformula := height_smul_ptX'_at g (fun v => (p v).1) (fun v => (p v).2)
      (fun v => hp v) w
    have heq : height ((g • ptX F p) w) = (p w).2 / den w p := by
      change height ((g • ptX' F (fun v => (p v).1) (fun v => (p v).2)) w) = _
      simpa [den] using hformula
    rw [heq] at hheight
    exact (div_pos_iff_of_pos_left hy).mp hheight
  let quot : InfinitePlace F → Coord F → ℝ := fun w p => (p w).2 / den w p
  have hquot (w : InfinitePlace F) :
      ContDiffOn ℝ ∞ (fun p => quot w p) (posSet F) := by
    dsimp [quot]
    apply ContDiffOn.div
    · fun_prop
    · exact hden_smooth w
    · intro p hp
      exact (hden_pos w p hp).ne'
  have hprod : ContDiffOn ℝ ∞ (fun p => ∏ w : InfinitePlace F, quot w p) (posSet F) := by
    simpa using (contDiffOn_prod (t := (Finset.univ : Finset (InfinitePlace F)))
      (fun w hw => hquot w))
  apply hprod.congr
  intro p hp
  have hformula := (G2_x_action (F := F)).1 g (fun w => (p w).1) (fun w => (p w).2)
    (fun w => hp w)
  change normHeight F (g • ptX' F (fun w => (p w).1) (fun w => (p w).2)) = _
  simpa [quot, den] using hformula

private theorem specSiegelB_logNormHeight_action_smooth (g : SL(2,F)) :
    IsSmoothX F (fun z => logNormHeight F (g • z)) := by
  change ContDiffOn ℝ ∞
    (fun p => (Real.log (normHeight F (g • ptX F p)) : ℂ)) (posSet F)
  have h := specSiegelB_normHeight_action_smooth (F := F) g
  have hlog : ContDiffOn ℝ ∞
      (fun p => Real.log (normHeight F (g • ptX F p))) (posSet F) :=
    h.log (fun p hp => (specSiegelB_normHeight_pos (g • ptX F p)).ne')
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hlog

private theorem specSiegelB_fullGradient_norm_sq (f : X F → ℂ) (z : X F) :
    ‖fullGradient F f z‖ ^ 2 = totalGradNormSq F f z := by
  rw [fullGradient, PiLp.norm_sq_eq_of_L2]
  simp [totalGradNormSq, placeGradNormSq, Complex.normSq_eq_norm_sq,
    Fintype.sum_prod_type]

private theorem specSiegelB_fullGradient_exp (L : X F → ℂ) (hL : IsSmoothX F L)
    (a : ℂ) (z : X F) :
    fullGradient F (fun x => Complex.exp (a * L x)) z =
      (a * Complex.exp (a * L z)) • fullGradient F L z := by
  ext wj
  rcases wj with ⟨w, j⟩
  let p : Coord F := coordsX F z
  let Lc : Coord F → ℂ := fun p' => L (ptX F p')
  have hp : p ∈ posSet F := by
    intro w
    dsimp [p, coordsX]
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hpt : ptX F p = z := by
    funext w
    dsimp [p, coordsX, ptX]
    exact pt_horiz_height (z w)
  have hLc : ContDiffAt ℝ ∞ Lc p :=
    (hL.contDiffAt (specSiegelB_posSet_open.mem_nhds hp))
  have hLd : DifferentiableAt ℝ Lc p := hLc.differentiableAt (by norm_num)
  have hInner : DifferentiableAt ℝ (fun p' => Lc p' * a) p := hLd.mul_const a
  have hExpDeriv : fderiv ℝ (fun p' => Complex.exp (Lc p' * a)) p =
      Complex.exp (Lc p * a) • fderiv ℝ (fun p' => Lc p' * a) p :=
    (hInner.hasFDerivAt.cexp).fderiv
  rw [fderiv_mul_const hLd a] at hExpDeriv
  have hLcval : Lc p = L z := by
    dsimp [Lc]
    rw [hpt]
  change (p w).2 *
      fderiv ℝ (fun p' => Complex.exp (a * L (ptX F p'))) p
        (placeDirection F w j) =
    (a * Complex.exp (a * L z)) * ((p w).2 *
      fderiv ℝ (fun p' => L (ptX F p')) p (placeDirection F w j))
  have hchart : (fun p' => Complex.exp (a * L (ptX F p'))) =
      (fun p' => Complex.exp (Lc p' * a)) := by
    funext p'
    congr 1
    dsimp [Lc]
    ring
  rw [hchart, hExpDeriv, hLcval]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  dsimp [Lc]
  ring_nf

/-- A transitioned term has the real row-kernel norm and gradient norm equal to
`|1+2s| sqrt(r)` times its norm.
Uses `G2_x_action`, `G4_energy` and the chain rule for the positive height cpow;
feeds `nontriangular_siegel_summable`. No restriction on s is needed for a single term. -/
theorem eis_term_row_kernel_gradient (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ σ' : SL(2,F)) (s : ℂ) (q : CuspCosets F Γ σ) (z : X F) :
    ‖eisTerm F Γ σ s (σ' • z) q‖ =
      siegelRowKernel (bottomRow F (siegelTransition Γ σ σ' q))
        (fun w => horiz (z w)) (fun w => height (z w)) (1 + 2 * s.re) ∧
    ‖fullGradient F (fun x => eisTerm F Γ σ s (σ' • x) q) z‖ =
      ‖1 + 2 * s‖ * Real.sqrt (placeCount F) * ‖eisTerm F Γ σ s (σ' • z) q‖ := by
  let b : SL(2,F) := siegelTransition Γ σ σ' q
  let a : ℂ := 1 + 2 * s
  let H : X F → ℝ := fun x => normHeight F (b • x)
  let L : X F → ℂ := fun x => logNormHeight F (b • x)
  have hsmul (x : X F) :
      σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • (σ' • x)) = b • x := by
    change σ⁻¹ • (toSLF F ((q.out : Γ) : SL(2,𝓞 F)) • (σ' • x)) = _
    calc
      σ⁻¹ • (toSLF F ((q.out : Γ) : SL(2,𝓞 F)) • (σ' • x)) =
          (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))) • (σ' • x) :=
        smul_smul σ⁻¹ (toSLF F ((q.out : Γ) : SL(2,𝓞 F))) (σ' • x)
      _ = ((σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))) * σ') • x :=
        smul_smul (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))) σ' x
      _ = b • x := by simpa [b, siegelTransition, mul_assoc]
  have hHpos (x : X F) : 0 < H x := specSiegelB_normHeight_pos (b • x)
  have hterm (x : X F) : eisTerm F Γ σ s (σ' • x) q = Complex.exp (a * L x) := by
    have hact := hsmul x
    unfold eisTerm
    rw [hact]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hHpos x).ne')]
    rw [← Complex.ofReal_log (le_of_lt (hHpos x))]
    simp [a, L, H, logNormHeight, mul_comm]
  have hrow : H z = ∏ w : InfinitePlace F,
      height (z w) /
        (Complex.normSq (w.embedding (b 1 0) * horiz (z w) + w.embedding (b 1 1)) +
          Complex.normSq (w.embedding (b 1 0)) * height (z w) ^ 2) := by
    have hz : z = ptX' F (fun w => horiz (z w)) (fun w => height (z w)) := by
      funext w
      exact (pt_horiz_height (z w)).symm
    change normHeight F (b • z) = _
    calc
      normHeight F (b • z) =
          normHeight F (b • ptX' F (fun w => horiz (z w)) (fun w => height (z w))) :=
        congrArg (fun x : X F => normHeight F (b • x)) hz
      _ = ∏ w : InfinitePlace F, height (z w) /
          (Complex.normSq (w.embedding (b 1 0) * horiz (z w) + w.embedding (b 1 1)) +
            Complex.normSq (w.embedding (b 1 0)) * height (z w) ^ 2) := by
        simpa [ptX', height_pt] using
          (G2_x_action (F := F)).1 b (fun w => horiz (z w)) (fun w => height (z w))
            (fun w => by
              rw [height_eq_hyperbolicHeight]
              exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w))
  have hnormTerm : ‖eisTerm F Γ σ s (σ' • z) q‖ =
      siegelRowKernel (bottomRow F b) (fun w => horiz (z w))
        (fun w => height (z w)) (1 + 2 * s.re) := by
    calc
      ‖eisTerm F Γ σ s (σ' • z) q‖ =
          ‖((normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • (σ' • z))) : ℝ) : ℂ) ^
            (1 + 2 * s)‖ := by rfl
      _ = Real.rpow (H z) a.re := by
        rw [hsmul z]
        simpa [H, a] using
          (Complex.norm_cpow_eq_rpow_re_of_pos (hHpos z) (1 + 2 * s))
      _ = siegelRowKernel (bottomRow F b) (fun w => horiz (z w))
          (fun w => height (z w)) (1 + 2 * s.re) := by
        rw [hrow]
        rw [show a.re = 1 + 2 * s.re by simp [a]]
        simpa [siegelRowKernel, bottomRow] using
          (Real.finsetProd_rpow Finset.univ
            (fun w : InfinitePlace F => height (z w) /
              (Complex.normSq (w.embedding (b 1 0) * horiz (z w) + w.embedding (b 1 1)) +
                Complex.normSq (w.embedding (b 1 0)) * height (z w) ^ 2))
            (fun w hw => div_nonneg
              (le_of_lt (by
                rw [height_eq_hyperbolicHeight]
                exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)))
              (add_nonneg (Complex.normSq_nonneg _) (mul_nonneg
                (Complex.normSq_nonneg _) (sq_nonneg _)))) (1 + 2 * s.re)).symm
  refine ⟨hnormTerm, ?_⟩
  have hLsmooth : IsSmoothX F L := by
    simpa [L] using specSiegelB_logNormHeight_action_smooth (F := F) b
  have hbaseSmooth : IsSmoothX F (logNormHeight F) := by
    simpa using specSiegelB_logNormHeight_action_smooth (F := F) (1 : SL(2,F))
  have hzero : IsSmoothX F (fun _ : X F => (0 : ℂ)) := by
    change ContDiffOn ℝ ∞ (fun _ => (0 : ℂ)) (posSet F)
    exact contDiffOn_const
  let gPlaces : InfinitePlace F → SL(2,ℂ) := toInf F b
  have hG4 := G4_energy gPlaces (logNormHeight F) (fun _ => (0 : ℂ))
    hbaseSmooth hzero
  have hLenergy : totalGradNormSq F L z = placeCount F := by
    calc
      totalGradNormSq F L z =
          totalGradNormSq F (fun x => logNormHeight F (actAtPlaces F gPlaces x)) z := by rfl
      _ = totalGradNormSq F (logNormHeight F) (actAtPlaces F gPlaces z) := hG4.2.1 z
      _ = placeCount F := hG4.2.2 _
  have hLnorm : ‖fullGradient F L z‖ = Real.sqrt (placeCount F) := by
    have hcount : 0 ≤ placeCount F := by
      unfold placeCount
      positivity
    have hsq : ‖fullGradient F L z‖ ^ 2 = (Real.sqrt (placeCount F)) ^ 2 := by
      rw [Real.sq_sqrt hcount, specSiegelB_fullGradient_norm_sq]
      exact hLenergy
    exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hsq
  have hgrad := specSiegelB_fullGradient_exp L hLsmooth a z
  rw [show (fun x => eisTerm F Γ σ s (σ' • x) q) =
      (fun x => Complex.exp (a * L x)) by funext x; exact hterm x] at ⊢
  rw [hgrad, norm_smul, norm_mul, hLnorm]
  rw [← hterm z]
  simp [a, mul_assoc, mul_left_comm, mul_comm]

end ArtinPrimitiveRoots.A1.Spec
