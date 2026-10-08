import ArtinPrimitiveRoots.Spec.EisensteinExtra

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

def specRadialProfile (τ : ℝ → ℝ) (a : ℂ) (u : ℝ) : ℂ :=
  (τ (Real.exp u) : ℂ) * Complex.exp (a * (u : ℂ))

private theorem specRadialProfile_log (τ : ℝ → ℝ) (a : ℂ) {h : ℝ} (hh : 0 < h) :
    specRadialProfile τ a (Real.log h) = (τ h : ℂ) * (h : ℂ) ^ a := by
  have hne : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [specRadialProfile, Real.exp_log hh, Complex.cpow_def_of_ne_zero hne,
    Complex.ofReal_log hh.le]
  congr 1
  rw [mul_comm a (Complex.log (h : ℂ))]

private theorem specRadialProfile_contDiff (τ : ℝ → ℝ) (a : ℂ)
    (hτ : ContDiff ℝ ∞ τ) : ContDiff ℝ ∞ (specRadialProfile τ a) := by
  have hτ' : ContDiff ℝ ∞ (fun u : ℝ => τ (Real.exp u)) := hτ.comp Real.contDiff_exp
  have hreal : ContDiff ℝ ∞ (fun u : ℝ => (τ (Real.exp u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hτ'
  have harg : ContDiff ℝ ∞ (fun u : ℝ => a * (u : ℂ)) := by
    have h := (Complex.ofRealCLM.smulRight a).contDiff (n := ∞)
    convert h using 1 <;> ext u <;> simp [Complex.ofRealCLM_apply, ContinuousLinearMap.smulRight_apply,
      smul_eq_mul, mul_comm]
  have hexp : ContDiff ℝ ∞ (fun u : ℝ => Complex.exp (a * (u : ℂ))) :=
    Complex.contDiff_exp.comp harg
  change ContDiff ℝ ∞ (fun u : ℝ => (τ (Real.exp u) : ℂ) * Complex.exp (a * (u : ℂ)))
  exact hreal.mul hexp

private theorem spec_posSet_open : IsOpen (posSet F) := by
  rw [posSet, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun w => by
    have hcont : Continuous (fun p : Coord F => (p w).2) :=
      continuous_snd.comp (continuous_apply w)
    exact isOpen_lt continuous_const hcont

private theorem spec_normHeight_ptX (p : Coord F) (hp : p ∈ posSet F) :
    normHeight F (ptX F p) = ∏ w : InfinitePlace F, (p w).2 := by
  unfold normHeight
  apply Finset.prod_congr rfl
  intro w _
  change height (pt (p w).1 (p w).2) = _
  exact (G1_h3_basics (F := F)).1 (p w).1 (p w).2 (hp w)

private theorem spec_fullGradient_radial (τ : ℝ → ℝ) (a : ℂ)
    (hτ : ContDiff ℝ ∞ τ) (z : X F) :
    fullGradient F
        (fun z => (τ (normHeight F z) : ℂ) * (normHeight F z : ℂ) ^ a) z =
      (deriv (specRadialProfile τ a) (Real.log (normHeight F z))) •
        fullGradient F (logNormHeight F) z := by
  classical
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := by
    intro w
    change 0 < height (z w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  let Ncoord : Coord F → ℝ := fun p => normHeight F (ptX F p)
  let Lcoord : Coord F → ℝ := fun p => Real.log (Ncoord p)
  let ψ : ℝ → ℂ := specRadialProfile τ a
  let radial : X F → ℂ := fun z => (τ (normHeight F z) : ℂ) * (normHeight F z : ℂ) ^ a
  have hN_eq (p' : Coord F) (hp' : p' ∈ posSet F) :
      Ncoord p' = ∏ w : InfinitePlace F, (p' w).2 := by
    exact spec_normHeight_ptX p' hp'
  have hNpos (p' : Coord F) (hp' : p' ∈ posSet F) : 0 < Ncoord p' := by
    rw [hN_eq p' hp']
    exact Finset.prod_pos fun w _ => hp' w
  have hNprod : DifferentiableAt ℝ (fun p' : Coord F => ∏ w : InfinitePlace F, (p' w).2) p := by
    fun_prop
  have hNevent : Ncoord =ᶠ[𝓝 p] fun p' : Coord F => ∏ w : InfinitePlace F, (p' w).2 := by
    filter_upwards [(spec_posSet_open (F := F)).mem_nhds hp] with p' hp'
    exact hN_eq p' hp'
  have hNhas : HasFDerivAt Ncoord (fderiv ℝ (fun p' : Coord F => ∏ w, (p' w).2) p) p :=
    hNprod.hasFDerivAt.congr_of_eventuallyEq hNevent
  have hLhas : HasFDerivAt Lcoord (fderiv ℝ Lcoord p) p := by
    change HasFDerivAt (fun p' : Coord F => Real.log (Ncoord p')) _ p
    have hLcomp := (Real.hasDerivAt_log (ne_of_gt (hNpos p hp))).hasFDerivAt.comp p hNhas
    change HasFDerivAt (Real.log ∘ Ncoord) (fderiv ℝ (Real.log ∘ Ncoord) p) p
    rw [hLcomp.fderiv]
    exact hLcomp
  have hψsmooth : ContDiff ℝ ∞ ψ := specRadialProfile_contDiff τ a hτ
  have hψhas : HasDerivAt ψ (deriv ψ (Lcoord p)) (Lcoord p) :=
    (hψsmooth.contDiffAt (x := Lcoord p)).differentiableAt (by simp) |>.hasDerivAt
  have hcomp := hψhas.hasFDerivAt.comp p hLhas
  have hprofEq (p' : Coord F) (hp' : p' ∈ posSet F) : radial (ptX F p') = ψ (Lcoord p') := by
    change (τ (normHeight F (ptX F p')) : ℂ) *
        (normHeight F (ptX F p') : ℂ) ^ a = specRadialProfile τ a
          (Real.log (normHeight F (ptX F p')))
    exact (specRadialProfile_log τ a (hNpos p' hp')).symm
  have hprofEvent : (fun p' : Coord F => radial (ptX F p')) =ᶠ[𝓝 p]
      fun p' => ψ (Lcoord p') := by
    filter_upwards [spec_posSet_open (F := F).mem_nhds hp] with p' hp'
    exact hprofEq p' hp'
  have hradHas := hcomp.congr_of_eventuallyEq hprofEvent
  have hradDeriv : fderiv ℝ (fun p' : Coord F => radial (ptX F p')) p =
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv ψ (Lcoord p))).comp
        (fderiv ℝ Lcoord p) := hradHas.fderiv
  have hlogHas : HasFDerivAt (fun p' : Coord F => logNormHeight F (ptX F p'))
      (Complex.ofRealCLM.comp (fderiv ℝ Lcoord p)) p := by
    change HasFDerivAt (fun p' : Coord F => (Lcoord p' : ℂ)) _ p
    exact Complex.ofRealCLM.hasFDerivAt.comp p hLhas
  have hlogDeriv : fderiv ℝ (fun p' : Coord F => logNormHeight F (ptX F p')) p =
      Complex.ofRealCLM.comp (fderiv ℝ Lcoord p) := hlogHas.fderiv
  have hdir (v : Coord F) :
      fderiv ℝ (fun p' : Coord F => radial (ptX F p')) p v =
        deriv ψ (Lcoord p) * fderiv ℝ (fun p' : Coord F => logNormHeight F (ptX F p')) p v := by
    rw [hradDeriv, hlogDeriv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      Complex.ofRealCLM_apply]
    <;> ring
  have hplace (w : InfinitePlace F) (j : Fin 3) :
      placeGradient F w radial z j =
        deriv ψ (Lcoord p) * placeGradient F w (logNormHeight F) z j := by
    unfold placeGradient
    rw [show coordsX F z = p by rfl]
    have h := hdir (placeDirection F w j)
    have h' :
        fderiv ℝ (radial ∘ ptX F) p (placeDirection F w j) =
          deriv ψ (Lcoord p) *
            fderiv ℝ (logNormHeight F ∘ ptX F) p (placeDirection F w j) := by
      change fderiv ℝ (fun p' => radial (ptX F p')) p (placeDirection F w j) =
        deriv ψ (Lcoord p) *
          fderiv ℝ (fun p' => logNormHeight F (ptX F p')) p (placeDirection F w j)
      exact h
    rw [h']
    ring
  have hvec : fullGradient F radial z =
      (deriv ψ (Lcoord p)) • fullGradient F (logNormHeight F) z := by
    apply PiLp.ext
    intro ij
    rcases ij with ⟨w, j⟩
    simp [fullGradient, hplace]
  have hpoint : ptX F p = z := (G1_h3_basics (F := F)).2.2.2.2.2.2.2.1 z
  have hNpoint : Ncoord p = normHeight F z := by
    dsimp [Ncoord, p]
    rw [hpoint]
  simpa [ψ, Lcoord, hNpoint] using hvec

private theorem spec_fullGradient_norm_sq (f : X F → ℂ) (z : X F) :
    ‖fullGradient F f z‖ ^ 2 = totalGradNormSq F f z := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [fullGradient, PiLp.toLp_apply]
  change (∑ ij : InfinitePlace F × Fin 3, ‖placeGradient F ij.1 f z ij.2‖ ^ 2) = _
  rw [Fintype.sum_prod_type]
  simp [totalGradNormSq, placeGradNormSq, Complex.normSq_eq_norm_sq]

private theorem spec_radial_gradient_norm (τ : ℝ → ℝ) (a : ℂ)
    (hτ : ContDiff ℝ ∞ τ) (z : X F) :
    ‖fullGradient F
        (fun z => (τ (normHeight F z) : ℂ) * (normHeight F z : ℂ) ^ a) z‖ =
      ‖deriv (specRadialProfile τ a) (Real.log (normHeight F z))‖ *
        Real.sqrt (placeCount F) := by
  have hlogSmooth : IsSmoothX F (logNormHeight F) := by
    unfold IsSmoothX
    have hprod : ContDiff ℝ ∞ (fun p : Coord F => ∏ w : InfinitePlace F, (p w).2) := by
      fun_prop
    have hprodOn : ContDiffOn ℝ ∞
        (fun p : Coord F => ∏ w : InfinitePlace F, (p w).2) (posSet F) := hprod.contDiffOn
    have hlog : ContDiffOn ℝ ∞
        (fun p : Coord F => Real.log (∏ w : InfinitePlace F, (p w).2)) (posSet F) := by
      apply hprodOn.log
      intro p hp
      exact (Finset.prod_pos fun w _ => hp w).ne'
    have hcast := Complex.ofRealCLM.contDiff.comp_contDiffOn hlog
    apply hcast.congr
    intro p hp
    simp [logNormHeight, spec_normHeight_ptX p hp]
  have hG4 := G4_energy (F := F) (fun _ => (1 : SL(2,ℂ)))
    (logNormHeight F) (logNormHeight F) hlogSmooth hlogSmooth
  have hr : 0 < placeCount F := by
    unfold placeCount
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (InfinitePlace F)))
  have hnormsq : ‖fullGradient F (logNormHeight F) z‖ ^ 2 = placeCount F := by
    rw [spec_fullGradient_norm_sq]
    exact hG4.2.2 z
  have hnorm : ‖fullGradient F (logNormHeight F) z‖ = Real.sqrt (placeCount F) := by
    rw [← hnormsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [spec_fullGradient_radial τ a hτ z, norm_smul, hnorm]

set_option maxHeartbeats 1000000 in
private theorem probe_eisTerm_smooth (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (q : CuspCosets F Γ σ) :
    IsSmoothX F (fun z => eisTerm F Γ σ s z q) := by
  classical
  let a : ℂ := 1 + 2 * s
  let γ : SL(2,𝓞 F) := (q.out : Γ)
  let b : SL(2,F) := σ⁻¹ * toSLF F γ
  let denom (p : Coord F) (w : InfinitePlace F) : ℝ :=
    Complex.normSq (w.embedding (b 1 0) * (p w).1 + w.embedding (b 1 1)) +
      Complex.normSq (w.embedding (b 1 0)) * (p w).2 ^ 2
  let H (p : Coord F) : ℝ := ∏ w : InfinitePlace F, (p w).2 / denom p w
  have hbrow : b 1 0 ≠ 0 ∨ b 1 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have hdet := b.property
    rw [Matrix.det_fin_two] at hdet
    rw [h.1, h.2] at hdet
    norm_num at hdet
  have hden (p : Coord F) (hp : p ∈ posSet F) (w : InfinitePlace F) : 0 < denom p w := by
    by_cases hc : b 1 0 = 0
    · have hd : b 1 1 ≠ 0 := by
        intro hd0
        exact hbrow.elim (fun h => h hc) (fun h => h hd0)
      have hwd : w.embedding (b 1 1) ≠ 0 := (map_ne_zero (w.embedding)).2 hd
      have hnorm : 0 < Complex.normSq (w.embedding (b 1 1)) := by
        rw [Complex.normSq_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr hwd)
      simpa [denom, hc] using hnorm
    · have hwc : w.embedding (b 1 0) ≠ 0 := (map_ne_zero (w.embedding)).2 hc
      have hnorm : 0 < Complex.normSq (w.embedding (b 1 0)) := by
        rw [Complex.normSq_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr hwc)
      have hy : 0 < (p w).2 ^ 2 := pow_pos (hp w) 2
      unfold denom
      exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (mul_pos hnorm hy)
  have hHpos (p : Coord F) (hp : p ∈ posSet F) : 0 < H p := by
    apply Finset.prod_pos
    intro w hw
    exact div_pos (hp w) (hden p hp w)
  have hformula (p : Coord F) (hp : p ∈ posSet F) :
      normHeight F (σ⁻¹ • (γ • ptX F p)) = H p := by
    have hG := (G2_x_action (F := F)).1 b (fun w => (p w).1) (fun w => (p w).2) hp
    have hact : σ⁻¹ • (γ • ptX F p) = b • ptX F p := by
      change σ⁻¹ • ((toSLF F γ) • ptX F p) = _
      rw [← mul_smul]
    rw [hact]
    change normHeight F (b • ptX' F (fun w => (p w).1) (fun w => (p w).2)) = H p
    change normHeight F (b • ptX' F (fun w => (p w).1) (fun w => (p w).2)) = H p at hG
    exact hG
  have hdenomCont (w : InfinitePlace F) :
      ContDiff ℝ ∞ (fun p : Coord F => denom p w) := by
    let l : Coord F → ℂ := fun p =>
      w.embedding (b 1 0) * (p w).1 + w.embedding (b 1 1)
    have hleft : ContDiff ℝ ∞ l := by
      fun_prop
    have hleftRe : ContDiff ℝ ∞ (fun p => (l p).re) := Complex.reCLM.contDiff.comp hleft
    have hleftIm : ContDiff ℝ ∞ (fun p => (l p).im) := Complex.imCLM.contDiff.comp hleft
    have hleftSq : ContDiff ℝ ∞ (fun p : Coord F => Complex.normSq (l p)) := by
      have hsum : ContDiff ℝ ∞ (fun p : Coord F =>
          (l p).re * (l p).re + (l p).im * (l p).im) :=
        (hleftRe.mul hleftRe).add (hleftIm.mul hleftIm)
      simpa only [Complex.normSq_apply] using hsum
    have hrightSq : ContDiff ℝ ∞
        (fun p : Coord F => Complex.normSq (w.embedding (b 1 0)) * (p w).2 ^ 2) := by
      fun_prop
    change ContDiff ℝ ∞ (fun p => Complex.normSq (l p) +
      Complex.normSq (w.embedding (b 1 0)) * (p w).2 ^ 2)
    exact hleftSq.add hrightSq
  have hfracCont (w : InfinitePlace F) :
      ContDiffOn ℝ ∞ (fun p : Coord F => (p w).2 / denom p w) (posSet F) := by
    have hnum : ContDiff ℝ ∞ (fun p : Coord F => (p w).2) := by fun_prop
    exact hnum.contDiffOn.div (hdenomCont w).contDiffOn fun p hp => (hden p hp w).ne'
  have hHdiff : ContDiffOn ℝ ∞ H (posSet F) := by
    unfold H
    exact contDiffOn_prod (fun w _ => hfracCont w)
  have hlogH : ContDiffOn ℝ ∞ (fun p => Real.log (H p)) (posSet F) :=
    hHdiff.log fun p hp => (hHpos p hp).ne'
  let one : ℝ → ℝ := fun _ => 1
  have hone : ContDiff ℝ ∞ one := by fun_prop [one]
  have hprofile : ContDiffOn ℝ ∞
      (fun p => specRadialProfile one a (Real.log (H p))) (posSet F) :=
    (specRadialProfile_contDiff one a hone).comp_contDiffOn hlogH
  have hEq (p : Coord F) (hp : p ∈ posSet F) :
      eisTerm F Γ σ s (ptX F p) q = specRadialProfile one a (Real.log (H p)) := by
    change ((normHeight F (σ⁻¹ • (γ • ptX F p)) : ℝ) : ℂ) ^ (1 + 2 * s) = _
    rw [hformula p hp]
    simpa [one, a] using (specRadialProfile_log one a (hHpos p hp)).symm
  unfold IsSmoothX
  change ContDiffOn ℝ ∞ (fun p => eisTerm F Γ σ s (ptX F p) q) (posSet F)
  exact hprofile.congr fun p hp => hEq p hp

set_option maxHeartbeats 1000000 in
private theorem probe_eisSeries_fderiv_tsum (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (hs : 1 / 2 < s.re)
    (p : Coord F) (hp : p ∈ posSet F) (v : Coord F) :
    Summable (fun q : CuspCosets F Γ σ =>
      fderiv ℝ (fun p' => eisTerm F Γ σ s (ptX F p') q) p v) ∧
    fderiv ℝ (fun p' => eisSeries F Γ σ s (ptX F p')) p v =
      ∑' q : CuspCosets F Γ σ,
        fderiv ℝ (fun p' => eisTerm F Γ σ s (ptX F p') q) p v := by
  classical
  let line : ℝ → Coord F := fun t => p + t • v
  let g : CuspCosets F Γ σ → ℝ → ℂ := fun q t =>
    eisTerm F Γ σ s (ptX F (line t)) q
  let g' : CuspCosets F Γ σ → ℝ → ℂ := fun q t =>
    fderiv ℝ (fun p' => eisTerm F Γ σ s (ptX F p') q) (line t) v
  obtain ⟨ε, hε, hεball⟩ := (Metric.isOpen_iff.mp (spec_posSet_open (F := F)) p hp)
  let δ : ℝ := ε / (4 * (‖v‖ + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let K : Set (Coord F) := Metric.closedBall p (ε / 2)
  have hK : IsCompact K := isCompact_closedBall p (ε / 2)
  have hlineK (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) : line t ∈ K := by
    have hAbs : |t| < δ := abs_lt.mpr ⟨ht.1, ht.2⟩
    have hratio : δ * ‖v‖ ≤ ε / 4 := by
      dsimp [δ]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (‖v‖ + 1))).2
      have hv : 0 ≤ ‖v‖ := norm_nonneg v
      have he : 0 < ε := hε
      nlinarith [mul_nonneg he.le hv]
    have hnorm : ‖line t - p‖ = |t| * ‖v‖ := by
      dsimp [line]
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rw [Metric.mem_closedBall, dist_eq_norm, hnorm]
    have hprodle : |t| * ‖v‖ ≤ δ * ‖v‖ := by gcongr
    calc
      |t| * ‖v‖ ≤ δ * ‖v‖ := hprodle
      _ ≤ ε / 4 := hratio
      _ ≤ ε / 2 := by linarith
  have hKpos : K ⊆ posSet F := by
    intro p' hp'
    apply hεball
    have hpclosed : dist p' p ≤ ε / 2 := by simpa [K] using hp'
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hpclosed (by linarith))
  have hE3 := E3_eis_smooth (F := F) Γ σ s hs
  let V : Fin 1 → Coord F := fun _ => v
  obtain ⟨m, hm, hmBound⟩ := hE3.2.2 K hK hKpos 1 V
  have hlineDeriv (t : ℝ) : HasDerivAt line v t := by
    have hsum := (hasDerivAt_const t p).add ((hasDerivAt_id t).smul_const v)
    have hlineEq : line = (fun _ : ℝ => p) + (fun u : ℝ => u • v) := by
      funext u
      rfl
    rw [hlineEq]
    simpa using hsum
  have htermCont (q : CuspCosets F Γ σ) :
      ContDiffOn ℝ ∞ (fun p' => eisTerm F Γ σ s (ptX F p') q) (posSet F) :=
    probe_eisTerm_smooth Γ σ s q
  have hg (q : CuspCosets F Γ σ) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
      HasDerivAt (g q) (g' q t) t := by
    have hp' : line t ∈ posSet F := hKpos (hlineK t ht)
    have htermAt :=
      (htermCont q).contDiffAt ((spec_posSet_open (F := F)).mem_nhds hp')
    have htermFDeriv := (htermAt.differentiableAt (by simp)).hasFDerivAt
    have hcomp := htermFDeriv.comp_hasDerivAt t (hlineDeriv t)
    change HasDerivAt
      ((fun p' => eisTerm F Γ σ s (ptX F p') q) ∘ line)
      (fderiv ℝ (fun p' => eisTerm F Γ σ s (ptX F p') q) (line t) v) t
    simpa [g, g', Function.comp_def] using hcomp
  have hgBound (q : CuspCosets F Γ σ) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
      ‖g' q t‖ ≤ m q := by
    have h := hmBound q (line t) (hlineK t ht)
    simpa [g', V, iteratedFDeriv_one_apply] using h
  let σ₀ : ℝ := (1 / 2 + s.re) / 2
  have hσ₀ : 1 / 2 < σ₀ := by dsimp [σ₀]; linarith
  have hσ₀le : σ₀ ≤ s.re := by dsimp [σ₀]; linarith
  obtain ⟨m₀, hm₀, hm₀bound⟩ :=
    (E2_eis_converge (F := F) Γ σ).1 {ptX F p} isCompact_singleton σ₀ s.re hσ₀
  have hg0 : Summable (fun q => g q 0) := by
    apply Summable.of_norm_bounded hm₀
    intro q
    have h := hm₀bound (ptX F p) (Set.mem_singleton _) s hσ₀le le_rfl q
    simpa [g, line] using h
  have hzero : (0 : ℝ) ∈ Set.Ioo (-δ) δ := by
    rw [Set.mem_Ioo]
    constructor <;> linarith [hδ]
  have hsumDeriv := hasDerivAt_tsum_of_isPreconnected
    (g := g) (g' := g') (t := Set.Ioo (-δ) δ)
    hm isOpen_Ioo (convex_Ioo _ _).isPreconnected hg hgBound
    hzero hg0 hzero
  have hseriesCont : ContDiffOn ℝ ∞
      (fun p' => eisSeries F Γ σ s (ptX F p')) (posSet F) := hE3.1
  have hseriesAt := (hseriesCont.contDiffAt ((spec_posSet_open (F := F)).mem_nhds hp))
    |>.differentiableAt (by simp) |>.hasFDerivAt
  have hline0 : line 0 = p := by simp [line]
  have hseriesAt' : HasFDerivAt (fun p' => eisSeries F Γ σ s (ptX F p'))
      (fderiv ℝ (fun p' => eisSeries F Γ σ s (ptX F p')) p) (line 0) := by
    rw [hline0]
    exact hseriesAt
  have hseriesComp := hseriesAt'.comp_hasDerivAt 0 (hlineDeriv 0)
  have hseriesDeriv : HasDerivAt
      (fun t => eisSeries F Γ σ s (ptX F (line t)))
      (fderiv ℝ (fun p' => eisSeries F Γ σ s (ptX F p')) p v) 0 := by
    change HasDerivAt
      ((fun p' => eisSeries F Γ σ s (ptX F p')) ∘ line)
      (fderiv ℝ (fun p' => eisSeries F Γ σ s (ptX F p')) p v) 0
    exact hseriesComp
  have hfun : (fun t => ∑' q, g q t) =
      (fun t => eisSeries F Γ σ s (ptX F (line t))) := by
    funext t
    rfl
  have hsumDeriv' := hsumDeriv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun hfun t)
  have hfinal := hsumDeriv'.unique hseriesDeriv
  have hsumDerivative : Summable (fun q : CuspCosets F Γ σ =>
      fderiv ℝ (fun p' => eisTerm F Γ σ s (ptX F p') q) p v) := by
    apply Summable.of_norm_bounded hm
    intro q
    have hpK : p ∈ K := by
      change dist p p ≤ ε / 2
      rw [dist_self]
      positivity
    have h := hmBound q p hpK
    simpa [V, iteratedFDeriv_one_apply] using h
  refine ⟨hsumDerivative, ?_⟩
  simpa [g', line] using hfinal.symm

end ArtinPrimitiveRoots.A1.Spec
