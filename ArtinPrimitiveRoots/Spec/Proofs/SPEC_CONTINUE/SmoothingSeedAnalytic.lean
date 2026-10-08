import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.SeedProperties
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.RadialTransform
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_coord_smooth
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_compact_control
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.param_deriv_integral_formula
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.smoothing_uniform_eval_bound
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

open ArtinPrimitiveRoots.A1.Spec

namespace ArtinPrimitiveRoots.Proofs.spec_continue_p

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem specSeed_posSet_open' : IsOpen (posSet F) := by
  rw [posSet, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro w
  have hc : Continuous (fun p : Coord F => (p w).2) := by fun_prop
  exact IsOpen.preimage hc (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

theorem radialKernel_joint_derivative_continuousOn (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀) (n : ℕ) (v : Fin n → Coord F) :
    ContinuousOn
      (fun pq : Coord F × Coord F =>
        iteratedFDeriv ℝ n
          (fun r : Coord F × Coord F =>
            radialKernel F k₀ (ptX F r.1) (ptX F r.2)) pq
          (fun i => (v i, 0)))
      {pq | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F} := by
  let P : Set (Coord F × Coord F) := {pq | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F}
  let G : Coord F × Coord F → ℂ := fun pq =>
    radialKernel F k₀ (ptX F pq.1) (ptX F pq.2)
  have hPopen : IsOpen P := by
    change IsOpen (posSet F ×ˢ posSet F)
    exact specSeed_posSet_open'.prod specSeed_posSet_open'
  have hG : ContDiffOn ℝ ∞ G P := radialKernel_coord_smooth k₀ hkSmooth
  have hderiv : ContinuousOn (iteratedFDeriv ℝ n G) P :=
    ContinuousOn.continuousOn_iteratedFDeriv hG hPopen (by simp)
  have heval : Continuous
      (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F × Coord F) ℂ =>
        D (fun i => (v i, 0))) := by
    fun_prop
  change ContinuousOn (fun pq => iteratedFDeriv ℝ n G pq (fun i => (v i, 0))) P
  exact heval.continuousOn.comp hderiv (fun pq hpq => Set.mem_univ _)

private theorem radialKernel_slice_derivative_continuous_pre (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀) (n : ℕ) (v : Fin n → Coord F)
    (p q : Coord F) (hp : p ∈ posSet F) (hq : q ∈ posSet F) :
    iteratedFDeriv ℝ n (fun r => radialKernel F k₀ (ptX F r) (ptX F q)) p v =
      iteratedFDeriv ℝ n
        (fun r : Coord F × Coord F =>
          radialKernel F k₀ (ptX F r.1) (ptX F r.2)) (p, q)
        (fun i => (v i, 0)) := by
  let P : Set (Coord F × Coord F) := {r | r.1 ∈ posSet F ∧ r.2 ∈ posSet F}
  let G : Coord F × Coord F → ℂ := fun r =>
    radialKernel F k₀ (ptX F r.1) (ptX F r.2)
  have hPopen : IsOpen P := by
    change IsOpen (posSet F ×ˢ posSet F)
    exact specSeed_posSet_open'.prod specSeed_posSet_open'
  have hG : ContDiffOn ℝ ∞ G P := radialKernel_coord_smooth k₀ hkSmooth
  let a : Coord F × Coord F := (0, q)
  let fshift : Coord F × Coord F → Coord F × Coord F := fun r => r + a
  let S : Set (Coord F × Coord F) := fshift ⁻¹' P
  have hSopen : IsOpen S := hPopen.preimage (by fun_prop)
  have hGshift : ContDiffOn ℝ ∞ (fun r => G (r + a)) S := by
    have hshift : ContDiffOn ℝ ∞ fshift Set.univ := by fun_prop
    simpa [S, fshift, G, Function.comp_def] using hG.comp_inter hshift
  let L : Coord F →L[ℝ] Coord F × Coord F := ContinuousLinearMap.inl ℝ _ _
  let S' : Set (Coord F) := L ⁻¹' S
  have hS'open : IsOpen S' := hSopen.preimage L.continuous
  have hLp : L p ∈ S := by simp [S, fshift, L, a, P, hp, hq]
  have hpS' : p ∈ S' := hLp
  have hcomp := L.iteratedFDerivWithin_comp_right
    (f := fun r => G (r + a)) hGshift hSopen.uniqueDiffOn hS'open.uniqueDiffOn
    hLp (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hS'open hpS'] at hcomp
  rw [iteratedFDerivWithin_of_isOpen n hSopen hLp] at hcomp
  have hshiftDeriv := iteratedFDeriv_comp_add_right (𝕜 := ℝ) n a (L p) (f := G)
  rw [hshiftDeriv] at hcomp
  have hcompV := congrArg (fun D => D v) hcomp
  simpa [G, L, a, Function.comp_def,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using hcompV

theorem radialKernel_derivative_bcf (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀) (K : Set (Coord F)) (hK : IsCompact K)
    (hKpos : K ⊆ posSet F) (U : Set (Coord F)) (hUopen : IsOpen U)
    (hKU : K ⊆ U) (hUpos : U ⊆ posSet F) (W : Set (X F))
    (hW : IsCompact W) (hcontrol : SmoothingKernelControl F k₀ U W)
    (n : ℕ) (v : Fin n → Coord F) :
    ∃ κ : {w // w ∈ W} → ({p // p ∈ K} →ᵇ ℂ), ∃ C : ℝ,
      Continuous κ ∧ 0 ≤ C ∧
        (∀ w p, κ w p = iteratedFDeriv ℝ n
          (fun q => radialKernel F k₀ (ptX F q)
            (ptX F (coordsX F w.1))) p.1 v) ∧
        ∀ w, ‖κ w‖ ≤ C := by
  letI : CompactSpace {p // p ∈ K} := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace {w // w ∈ W} := isCompact_iff_compactSpace.mp hW
  obtain ⟨C, hC0, hCbound⟩ := hcontrol.bound n
  let jointD : Coord F × Coord F → ℂ := fun pq =>
    iteratedFDeriv ℝ n
      (fun r : Coord F × Coord F => radialKernel F k₀ (ptX F r.1) (ptX F r.2)) pq
      (fun i => (v i, 0))
  have hmapCont : Continuous (fun pw : {p // p ∈ K} × {w // w ∈ W} =>
      (pw.1.1, coordsX F pw.2.1)) := by
    have hp : Continuous (fun pw : {p // p ∈ K} × {w // w ∈ W} => pw.1.1) :=
      continuous_subtype_val.comp continuous_fst
    have hq : Continuous (fun pw : {p // p ∈ K} × {w // w ∈ W} => coordsX F pw.2.1) :=
      specCoordsX_continuous.comp (continuous_subtype_val.comp continuous_snd)
    exact hp.prodMk hq
  have hmaps : Set.MapsTo (fun pw : {p // p ∈ K} × {w // w ∈ W} =>
      (pw.1.1, coordsX F pw.2.1)) Set.univ
      {pq | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F} := by
    intro pw hpw
    exact ⟨hKpos pw.1.2, specCoordsX_mem_pos pw.2.1⟩
  have hjointOn :=
    (radialKernel_joint_derivative_continuousOn k₀ hkSmooth n v).comp
      hmapCont.continuousOn hmaps
  let sliceD : {p // p ∈ K} × {w // w ∈ W} → ℂ := fun pw =>
    iteratedFDeriv ℝ n
      (fun q => radialKernel F k₀ (ptX F q)
        (ptX F (coordsX F pw.2.1))) pw.1.1 v
  have hEq : Set.EqOn sliceD (fun pw => jointD (pw.1.1, coordsX F pw.2.1)) Set.univ := by
    intro pw hpw
    simpa [sliceD, jointD] using
      (radialKernel_slice_derivative_continuous_pre k₀ hkSmooth n v pw.1.1
        (coordsX F pw.2.1) (hKpos pw.1.2) (specCoordsX_mem_pos pw.2.1))
  have hslice : Continuous sliceD := by
    apply continuousOn_univ.mp
    exact hjointOn.congr hEq
  let J : C({p // p ∈ K} × {w // w ∈ W}, ℂ) := ⟨sliceD, hslice⟩
  let Jswap : C({w // w ∈ W} × {p // p ∈ K}, ℂ) :=
    ⟨fun pw => J (pw.2, pw.1), by fun_prop⟩
  let Jcurry : C({w // w ∈ W}, C({p // p ∈ K}, ℂ)) := Jswap.curry
  let e := ContinuousMap.isometryEquivBoundedOfCompact {p // p ∈ K} ℂ
  let κ : {w // w ∈ W} → ({p // p ∈ K} →ᵇ ℂ) := fun w => e (Jcurry w)
  have hκcont : Continuous κ := e.continuous.comp Jcurry.continuous
  let V : ℝ := ∏ i : Fin n, ‖v i‖
  let C' : ℝ := C * V
  have hC' : 0 ≤ C' := mul_nonneg hC0 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  refine ⟨κ, C', hκcont, hC', ?_, ?_⟩
  · intro w p
    simp [κ, e, Jcurry, Jswap, J, sliceD]
  · intro w
    apply (BoundedContinuousFunction.norm_le hC').2
    intro p
    have hval : κ w p = iteratedFDeriv ℝ n
        (fun q => radialKernel F k₀ (ptX F q) w.1) p.1 v := by
      calc
        κ w p = sliceD (p, w) := by simp [κ, e, Jcurry, Jswap, J]
        _ = iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q)
            (ptX F (coordsX F w.1))) p.1 v := rfl
        _ = iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w.1) p.1 v := by
          rw [specPtX_coordsX]
    calc
      ‖κ w p‖ = ‖iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w.1) p.1 v‖ :=
        congrArg norm hval
      _ ≤
          ‖iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w.1) p.1‖ * V :=
        (iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w.1) p.1).le_opNorm v
      _ ≤ C * V := mul_le_mul_of_nonneg_right (hCbound p.1 (hKU p.2) w.1)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)

theorem smoothingKernel_derivativeCLM (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀) (K : Set (Coord F)) (hK : IsCompact K)
    (hKpos : K ⊆ posSet F) (U : Set (Coord F)) (hUopen : IsOpen U)
    (hKU : K ⊆ U) (hUpos : U ⊆ posSet F) (W : Set (X F))
    (hW : IsCompact W) (hcontrol : SmoothingKernelControl F k₀ U W)
    (n : ℕ) (v : Fin n → Coord F) :
    ∃ T : (W →ᵇ ℂ) →L[ℂ] C({p // p ∈ K}, ℂ),
      ∀ f p, T f p = ∫ w : {w // w ∈ W},
        (f w * iteratedFDeriv ℝ n
          (fun q => radialKernel F k₀ (ptX F q) w.1) p.1 v)
          ∂((volX F).comap (fun w : {w // w ∈ W} => (w : X F))) := by
  letI : T2Space H3 := OAI.CubicEisenstein.upperCoordinatesHomeomorph.t2Space
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchartX⟩ := G1_h3_basics (F := F)
  obtain ⟨eChartX, _, _⟩ := hchartX
  letI : T2Space (X F) := eChartX.t2Space
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  letI : OpensMeasurableSpace {w // w ∈ W} := Subtype.opensMeasurableSpace W
  letI : CompactSpace {p // p ∈ K} := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace {w // w ∈ W} := isCompact_iff_compactSpace.mp hW
  letI : SecondCountableTopology (Coord F) := inferInstance
  letI : SecondCountableTopology {p // p ∈ K} := inferInstance
  letI : SecondCountableTopology C({p // p ∈ K}, ℂ) := inferInstance
  letI : MeasureSpace (X F) := ⟨volX F⟩
  letI : MeasureSpace {w // w ∈ W} := Measure.Subtype.measureSpace
  obtain ⟨κ, C, hκcont, hC0, hκval, hκbound⟩ :=
    radialKernel_derivative_bcf k₀ hkSmooth K hK hKpos U hUopen hKU hUpos W hW hcontrol n v
  let e := ContinuousMap.isometryEquivBoundedOfCompact {p // p ∈ K} ℂ
  let κC : {w // w ∈ W} → C({p // p ∈ K}, ℂ) := fun w => e.symm (κ w)
  have hκCcont : Continuous κC := e.symm.continuous.comp hκcont
  have hκCbound (w : {w // w ∈ W}) : ‖κC w‖ ≤ C := by
    apply (ContinuousMap.norm_le (f := κC w) hC0).2
    intro p
    calc
      ‖κC w p‖ = ‖κ w p‖ := by simp [κC, e]
      _ ≤ ‖κ w‖ := (κ w).norm_coe_le_norm p
      _ ≤ C := hκbound w
  have hCfinite : volX F W < ⊤ := (G3_volume (F := F)).2.2.1 W hW
  let μW : Measure {w // w ∈ W} :=
    (volX F).comap (fun w : {w // w ∈ W} => (w : X F))
  have hμfinite : μW Set.univ < ⊤ := by
    dsimp [μW]
    rw [comap_subtype_coe_apply hW.measurableSet]
    simpa using hCfinite
  letI : IsFiniteMeasure μW := ⟨hμfinite⟩
  have hintegrable (f : W →ᵇ ℂ) : Integrable (fun w : {w // w ∈ W} => f w • κC w) μW := by
    have hcont : Continuous (fun w : {w // w ∈ W} => f w • κC w) := by fun_prop
    let g : {w // w ∈ W} →ᵇ C({p // p ∈ K}, ℂ) := BoundedContinuousFunction.mkOfCompact ⟨_, hcont⟩
    exact g.integrable μW
  let L : (W →ᵇ ℂ) →ₗ[ℂ] C({p // p ∈ K}, ℂ) := {
    toFun := fun f => ∫ w : {w // w ∈ W}, f w • κC w ∂μW
    map_add' := by
      intro f g
      have hfg : (fun w : {w // w ∈ W} => (f + g) w • κC w) =
          (fun w => f w • κC w) + (fun w => g w • κC w) := by
        funext w
        simp [add_smul]
      rw [hfg]
      exact integral_add' (hintegrable f) (hintegrable g)
    map_smul' := by
      intro a f
      have hsmul : (fun w : {w // w ∈ W} => (a • f) w • κC w) =
          fun w => a • (f w • κC w) := by
        funext w
        simp [smul_smul]
      rw [hsmul]
      simpa using (integral_smul a (fun w : {w // w ∈ W} => f w • κC w))
  }
  have hbound (f : W →ᵇ ℂ) : ‖L f‖ ≤ (μW.real Set.univ * C) * ‖f‖ := by
    change ‖(∫ w : {w // w ∈ W}, f w • κC w ∂μW)‖ ≤ _
    calc
      ‖(∫ w : {w // w ∈ W}, f w • κC w ∂μW)‖ ≤
          ∫ w : {w // w ∈ W}, ‖f w • κC w‖ ∂μW :=
        norm_integral_le_integral_norm (fun w : {w // w ∈ W} => f w • κC w)
      _ ≤ ∫ _w : {w // w ∈ W}, (‖f‖ * C) ∂μW := by
        apply integral_mono ((hintegrable f).norm) (integrable_const _)
        intro w
        calc
          ‖f w • κC w‖ = ‖f w‖ * ‖κC w‖ := norm_smul _ _
          _ ≤ ‖f‖ * C := mul_le_mul (f.norm_coe_le_norm w) (hκCbound w) (norm_nonneg _) (norm_nonneg _)
      _ = (μW.real Set.univ * C) * ‖f‖ := by simp [integral_const, mul_assoc, mul_left_comm, mul_comm]
  let T : (W →ᵇ ℂ) →L[ℂ] C({p // p ∈ K}, ℂ) :=
    L.mkContinuous (μW.real Set.univ * C) hbound
  refine ⟨T, ?_⟩
  intro f p
  calc
    T f p = (L f) p := rfl
    _ = ∫ w : {w // w ∈ W}, (f w • κC w) p ∂μW :=
      ContinuousMap.integral_apply (hintegrable f) p
    _ = ∫ w : {w // w ∈ W}, f w * κC w p ∂μW := by
      congr 1
    _ = ∫ w : {w // w ∈ W}, f w *
        iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w.1) p.1 v ∂μW := by
      congr 1
      funext w
      simp [κC, e, hκval, specPtX_coordsX]

set_option maxHeartbeats 1000000 in
theorem smoothingSeed_derivative_analytic (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : MeasureTheory.IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (τ : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (hτ : IsCuspCutoff A τ) (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F)
    (n : ℕ) (v : Fin n → Coord F) :
    ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
      ∀ s p, Φ s p = iteratedFDeriv ℝ n
        (fun q => smoothingOperator F k₀ (eisSeed F Γ σ τ s) (ptX F q)) p.1 v := by
  letI : T2Space H3 := OAI.CubicEisenstein.upperCoordinatesHomeomorph.t2Space
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchartX⟩ := G1_h3_basics (F := F)
  obtain ⟨eChartX, _, _⟩ := hchartX
  letI : T2Space (X F) := eChartX.t2Space
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  let hseedData := specSeed_smooth_analytic Γ D hD σ A hA hsep τ hτ
  have hseed : ∀ s, IsSmoothX F (eisSeed F Γ σ τ s) := fun s => (hseedData.1 s).1
  obtain ⟨U, W, hUopen, hKU, hUpos, hW, hcontrol⟩ :=
    radialKernel_compact_control k₀ hkSmooth hkSupport K hK hKpos
  obtain ⟨T, hT⟩ := smoothingKernel_derivativeCLM k₀ hkSmooth K hK hKpos
    U hUopen hKU hUpos W hW hcontrol n v
  let KW : Set (Coord F) := coordsX F '' W
  have hKW : IsCompact KW := hW.image specCoordsX_continuous
  have hKWpos : KW ⊆ posSet F := by
    rintro p ⟨w, hw, rfl⟩
    exact specCoordsX_mem_pos w
  obtain ⟨Φ₀, hΦ₀, hΦ₀val⟩ := hseedData.2 KW hKW hKWpos 0 (Fin.elim0)
  let Wsub := {w // w ∈ W}
  let KWsub := {p // p ∈ KW}
  let Ksub := {p // p ∈ K}
  letI : CompactSpace Wsub := isCompact_iff_compactSpace.mp hW
  letI : CompactSpace KWsub := isCompact_iff_compactSpace.mp hKW
  letI : CompactSpace Ksub := isCompact_iff_compactSpace.mp hK
  have hKWsub : ∀ w : Wsub, coordsX F w.1 ∈ KW := fun w => ⟨w.1, w.2, rfl⟩
  let coordW : C(Wsub, KWsub) :=
    ⟨fun w => ⟨coordsX F w.1, hKWsub w⟩,
      (specCoordsX_continuous.comp continuous_subtype_val).subtype_mk _⟩
  let Rlin : (KWsub →ᵇ ℂ) →ₗ[ℂ] (Wsub →ᵇ ℂ) := {
    toFun := fun f => f.compContinuous coordW
    map_add' := by intro f g; ext w; rfl
    map_smul' := by intro a f; ext w; rfl }
  have hRbound (f : KWsub →ᵇ ℂ) : ‖Rlin f‖ ≤ ‖f‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity : (0 : ℝ) ≤ ‖f‖)).2
    intro w
    calc
      ‖Rlin f w‖ = ‖f (coordW w)‖ := rfl
      _ ≤ ‖f‖ := f.norm_coe_le_norm (coordW w)
  let R : (KWsub →ᵇ ℂ) →L[ℂ] (Wsub →ᵇ ℂ) :=
    Rlin.mkContinuous 1 (fun f => by simpa using hRbound f)
  have hseedCont (s : ℂ) : Continuous (eisSeed F Γ σ τ s) := by
    apply continuousOn_univ.mp
    have hcoord : ContinuousOn
        (fun p => eisSeed F Γ σ τ s (ptX F p)) (posSet F) := (hseed s).continuousOn
    have hcoords : ContinuousOn (coordsX F) Set.univ := specCoordsX_continuous.continuousOn
    have hmaps : Set.MapsTo (fun z => coordsX F z) Set.univ (posSet F) := by
      intro z hz
      exact specCoordsX_mem_pos z
    have hcomp : ContinuousOn
        (fun z => eisSeed F Γ σ τ s (ptX F (coordsX F z))) Set.univ :=
      hcoord.comp hcoords hmaps
    have heq : Set.EqOn (eisSeed F Γ σ τ s)
        (fun z => eisSeed F Γ σ τ s (ptX F (coordsX F z))) Set.univ := by
      intro z hz
      change eisSeed F Γ σ τ s z = eisSeed F Γ σ τ s (ptX F (coordsX F z))
      rw [specPtX_coordsX]
    exact hcomp.congr heq
  have hseedMeas (s : ℂ) : AEStronglyMeasurable (eisSeed F Γ σ τ s) (volX F) :=
    (hseedCont s).measurable.aestronglyMeasurable
  have hseedInt (s : ℂ) : IntegrableOn (eisSeed F Γ σ τ s) W (volX F) :=
    specSeed_integrableOn_compact Γ D hD σ A hA hsep τ hτ hseed s W hW
  have hparam (s : ℂ) := param_deriv_integral_formula k₀ U hUopen hUpos W hW hcontrol
    (eisSeed F Γ σ τ s) (hseedMeas s) (hseedInt s)
  let eK := ContinuousMap.linearIsometryBoundedOfCompact Ksub ℂ ℂ
  let T' : (Wsub →ᵇ ℂ) →L[ℂ] (Ksub →ᵇ ℂ) :=
    eK.toContinuousLinearEquiv.toContinuousLinearMap.comp T
  let S : (KWsub →ᵇ ℂ) →L[ℂ] (Ksub →ᵇ ℂ) := T'.comp R
  let Φ : ℂ → (Ksub →ᵇ ℂ) := fun s => S (Φ₀ s)
  have hΦ : AnalyticOnNhd ℂ Φ Set.univ := S.comp_analyticOnNhd hΦ₀
  refine ⟨Φ, hΦ, ?_⟩
  have hseedpull (s : ℂ) (w : Wsub) : R (Φ₀ s) w = eisSeed F Γ σ τ s w.1 := by
    change Φ₀ s (coordW w) = eisSeed F Γ σ τ s w.1
    rw [hΦ₀val s (coordW w)]
    simp
    change eisSeed F Γ σ τ s (ptX F (coordsX F w.1)) = _
    rw [specPtX_coordsX]
  have hTvalue (s : ℂ) (p : Ksub) :
      S (Φ₀ s) p = T (R (Φ₀ s)) p := rfl
  intro s p
  let g : X F → ℂ := fun w =>
    iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p.1 v *
      eisSeed F Γ σ τ s w
  have hzero (w : X F) (hw : w ∉ W) : g w = 0 := by
    simp [g, hcontrol.support n p.1 (hKU p.2) w hw]
  have hint : (∫ w, g w ∂(volX F)) =
      ∫ w : Wsub, g w.1 ∂((volX F).comap (fun w : Wsub => (w : X F))) := by
    calc
      (∫ w, g w ∂(volX F)) =
          ∫ w, Set.indicator W g w ∂(volX F) := by
        congr 1
        funext w
        by_cases hw : w ∈ W
        · simp [hw]
        · simp [hw, hzero w hw]
      _ = ∫ w in W, g w ∂(volX F) := integral_indicator hW.measurableSet
      _ = ∫ w : Wsub, g w.1
            ∂((volX F).comap (fun w : Wsub => (w : X F))) :=
          (integral_subtype_comap hW.measurableSet g).symm
  calc
    Φ s p = S (Φ₀ s) p := rfl
    _ = T (R (Φ₀ s)) p := hTvalue s p
    _ = ∫ w : Wsub, (R (Φ₀ s) w) *
        iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w.1) p.1 v
        ∂((volX F).comap (fun w : Wsub => (w : X F))) := hT _ p
    _ = ∫ w : Wsub, g w.1
        ∂((volX F).comap (fun w : Wsub => (w : X F))) := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [hseedpull s w]
      simp [g, mul_comm]
    _ = ∫ w, g w ∂(volX F) := hint.symm
    _ = iteratedFDeriv ℝ n
        (fun q => smoothingOperator F k₀ (eisSeed F Γ σ τ s) (ptX F q)) p.1 v := by
      symm
      exact (hparam s).2 n p.1 (hKU p.2) |>.2.2 v

private theorem integrable_eval_smul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {n : ℕ} (f : α → ℂ)
    (G : α → ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ)
    (hG : Integrable (fun x => f x • G x) μ) (v : Fin n → Coord F) :
    Integrable (fun x => f x * G x v) μ := by
  let Llin : (ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ) →ₗ[ℝ] ℂ := {
    toFun := fun D => D v
    map_add' := by intro D E; simp
    map_smul' := by intro c D; simp }
  let C : ℝ := ∏ i : Fin n, ‖v i‖
  have hC : 0 ≤ C := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hbound (D : ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ) :
      ‖Llin D‖ ≤ C * ‖D‖ := by
    dsimp [Llin, C]
    calc
      ‖D v‖ ≤ ‖D‖ * ∏ i, ‖v i‖ := D.le_opNorm v
      _ = (∏ i, ‖v i‖) * ‖D‖ := by ring_nf
  let L : (ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ) →L[ℝ] ℂ :=
    Llin.mkContinuous C hbound
  have hcomp := L.integrable_comp hG
  have heq : (fun x => L (f x • G x)) = fun x => f x * G x v := by
    funext x
    simp [L, Llin, smul_eq_mul]
  rw [← heq]
  exact hcomp

set_option maxHeartbeats 1000000 in
theorem smoothingSeedLift_derivative_data (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : MeasureTheory.IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (τ : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (hτ : IsCuspCutoff A τ) (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F)
    (n : ℕ) (v : Fin n → Coord F) :
    ∃ Φseed : ℂ → (K →ᵇ ℂ), ∃ T : L2Space F D →L[ℂ] (K →ᵇ ℂ),
      AnalyticOnNhd ℂ Φseed Set.univ ∧
      (∀ s p, Φseed s p = iteratedFDeriv ℝ n
        (fun q => smoothingOperator F k₀ (eisSeed F Γ σ τ s) (ptX F q)) p.1 v) ∧
      (∀ a p, T a p = iteratedFDeriv ℝ n
        (fun q => smoothingOperator F k₀ (l2Lift F Γ D a) (ptX F q)) p.1 v) ∧
      ∀ s a p, iteratedFDeriv ℝ n
        (fun q => smoothingOperator F k₀
          (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D a w) (ptX F q)) p.1 v =
        Φseed s p + T a p := by
  obtain ⟨Φseed, hΦseed, hΦseedval⟩ := smoothingSeed_derivative_analytic Γ D hD σ τ A hA
    hsep hτ k₀ hkSmooth hkSupport K hK hKpos n v
  obtain ⟨_, _, T, _, _, _, hT⟩ :=
    smoothing_uniform_eval_bound Γ D hD k₀ hkSmooth hkSupport K hK hKpos n v
  have hseedData := specSeed_smooth_analytic Γ D hD σ A hA hsep τ hτ
  have hseed : ∀ s, IsSmoothX F (eisSeed F Γ σ τ s) := fun s => (hseedData.1 s).1
  letI : T2Space H3 := OAI.CubicEisenstein.upperCoordinatesHomeomorph.t2Space
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchartX⟩ := G1_h3_basics (F := F)
  obtain ⟨eChartX, _, _⟩ := hchartX
  letI : T2Space (X F) := eChartX.t2Space
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  obtain ⟨U, W, hUopen, hKU, hUpos, hW, hcontrol⟩ :=
    radialKernel_compact_control k₀ hkSmooth hkSupport K hK hKpos
  have hseedCont (s : ℂ) : Continuous (eisSeed F Γ σ τ s) := by
    apply continuousOn_univ.mp
    have hcoord : ContinuousOn
        (fun p => eisSeed F Γ σ τ s (ptX F p)) (posSet F) := (hseed s).continuousOn
    have hcoords : ContinuousOn (coordsX F) Set.univ := specCoordsX_continuous.continuousOn
    have hmaps : Set.MapsTo (fun z => coordsX F z) Set.univ (posSet F) := by
      intro z hz
      exact specCoordsX_mem_pos z
    have hcomp : ContinuousOn
        (fun z => eisSeed F Γ σ τ s (ptX F (coordsX F z))) Set.univ :=
      hcoord.comp hcoords hmaps
    have heq : Set.EqOn (eisSeed F Γ σ τ s)
        (fun z => eisSeed F Γ σ τ s (ptX F (coordsX F z))) Set.univ := by
      intro z hz
      change eisSeed F Γ σ τ s z = eisSeed F Γ σ τ s (ptX F (coordsX F z))
      rw [specPtX_coordsX]
    exact hcomp.congr heq
  have hseedMeas (s : ℂ) : AEStronglyMeasurable (eisSeed F Γ σ τ s) (volX F) :=
    (hseedCont s).measurable.aestronglyMeasurable
  have hliftMeas (a : L2Space F D) : AEStronglyMeasurable
      (l2Lift F Γ D a) (volX F) := (T1_l2 Γ D hD).1 a |>.1
  have htotalMeas (s : ℂ) (a : L2Space F D) : AEStronglyMeasurable
      (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D a w) (volX F) :=
    (hseedMeas s).add (hliftMeas a)
  have hseedInt (s : ℂ) : IntegrableOn (eisSeed F Γ σ τ s) W (volX F) :=
    specSeed_integrableOn_compact Γ D hD σ A hA hsep τ hτ hseed s W hW
  have hliftInt (a : L2Space F D) : IntegrableOn (l2Lift F Γ D a) W (volX F) :=
    l2Lift_integrableOn_compact Γ D hD a W hW
  have htotalInt (s : ℂ) (a : L2Space F D) : IntegrableOn
      (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D a w) W (volX F) :=
    (hseedInt s).add (hliftInt a)
  have hparamSeed (s : ℂ) := param_deriv_integral_formula k₀ U hUopen hUpos W hW hcontrol
    (eisSeed F Γ σ τ s) (hseedMeas s) (hseedInt s)
  have hparamLift (a : L2Space F D) := param_deriv_integral_formula k₀ U hUopen hUpos W hW hcontrol
    (l2Lift F Γ D a) (hliftMeas a) (hliftInt a)
  have hparamTotal (s : ℂ) (a : L2Space F D) := param_deriv_integral_formula k₀ U hUopen hUpos W hW hcontrol
    (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D a w) (htotalMeas s a) (htotalInt s a)
  have hAdd : ∀ s a p, iteratedFDeriv ℝ n
      (fun q => smoothingOperator F k₀
        (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D a w) (ptX F q)) p.1 v =
      Φseed s p + T a p := by
    intro s a p
    have hpU : p.1 ∈ U := hKU p.2
    let G : X F → ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ :=
      fun w => iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p.1
    have hSeedEvalInt := integrable_eval_smul
      (fun w => eisSeed F Γ σ τ s w) G ((hparamSeed s).2 n p.1 hpU).1 v
    have hLiftEvalInt := integrable_eval_smul
      (l2Lift F Γ D a) G ((hparamLift a).2 n p.1 hpU).1 v
    have hTotalEvalInt := integrable_eval_smul
      (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D a w) G
      ((hparamTotal s a).2 n p.1 hpU).1 v
    have hIntegralAdd :
        (∫ w, (eisSeed F Γ σ τ s w + l2Lift F Γ D a w) * G w v ∂volX F) =
          (∫ w, eisSeed F Γ σ τ s w * G w v ∂volX F) +
          (∫ w, l2Lift F Γ D a w * G w v ∂volX F) := by
      rw [show (fun w => (eisSeed F Γ σ τ s w + l2Lift F Γ D a w) * G w v) =
        (fun w => eisSeed F Γ σ τ s w * G w v) +
            (fun w => l2Lift F Γ D a w * G w v) by
        funext w
        rw [add_mul]
        rfl]
      exact integral_add hSeedEvalInt hLiftEvalInt
    have hderivAdd :
        iteratedFDeriv ℝ n
            (fun q => smoothingOperator F k₀
              (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D a w) (ptX F q)) p.1 v =
          iteratedFDeriv ℝ n
            (fun q => smoothingOperator F k₀ (eisSeed F Γ σ τ s) (ptX F q)) p.1 v +
          iteratedFDeriv ℝ n
            (fun q => smoothingOperator F k₀ (l2Lift F Γ D a) (ptX F q)) p.1 v := by
      rw [(hparamTotal s a).2 n p.1 hpU |>.2.2 v,
        (hparamSeed s).2 n p.1 hpU |>.2.2 v,
        (hparamLift a).2 n p.1 hpU |>.2.2 v]
      simpa [G, mul_comm] using hIntegralAdd
    calc
      iteratedFDeriv ℝ n
          (fun q => smoothingOperator F k₀
            (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D a w) (ptX F q)) p.1 v =
          iteratedFDeriv ℝ n
            (fun q => smoothingOperator F k₀ (eisSeed F Γ σ τ s) (ptX F q)) p.1 v +
          iteratedFDeriv ℝ n
            (fun q => smoothingOperator F k₀ (l2Lift F Γ D a) (ptX F q)) p.1 v := hderivAdd
      _ = Φseed s p + T a p := by rw [hΦseedval s p, hT a p]
  exact ⟨Φseed, T, hΦseed, hΦseedval, hT, hAdd⟩

theorem radialTransformParam_analytic (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100)) :
    AnalyticOnNhd ℂ (fun s : ℂ => radialTransform F k₀ (1 + 2 * s)) Set.univ := by
  classical
  have h₀ : AnalyticOnNhd ℂ (radialTransform₀ k₀) Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    intro a
    exact radialTransform₀_differentiableAt F k₀ hkSmooth hkSupport a
  have hlinear : AnalyticOnNhd ℂ (fun s : ℂ => (1 : ℂ) + 2 * s) Set.univ := by
    fun_prop
  have hfactor : AnalyticOnNhd ℂ
      (fun s : ℂ => radialTransform₀ k₀ (1 + 2 * s)) Set.univ := by
    have h := h₀.comp hlinear (by intro s hs; exact Set.mem_univ _)
    exact h
  have hpow (n : ℕ) : AnalyticOnNhd ℂ
      (fun s : ℂ => (radialTransform₀ k₀ (1 + 2 * s)) ^ n) Set.univ := by
    induction n with
    | zero =>
        simpa using (analyticOnNhd_const (𝕜 := ℂ) (s := Set.univ) (v := (1 : ℂ)))
    | succ n ih =>
        simpa [pow_succ, mul_comm] using hfactor.mul ih
  simpa [radialTransform, Finset.prod_const] using
    hpow (Fintype.card (InfinitePlace F))

set_option maxHeartbeats 1000000 in
theorem pointwiseEisContinuation_derivative_analytic (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : MeasureTheory.IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (τ : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (hτ : IsCuspCutoff A τ) (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F)
    (u : ℂ → L2Space F D) (S : Set ℂ) (hu : AnalyticOnNhd ℂ u S)
    (hhat : ∀ s ∈ S, radialTransform F k₀ (1 + 2 * s) ≠ 0)
    (n : ℕ) (v : Fin n → Coord F) :
    ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ S ∧
      ∀ s ∈ S, ∀ p : K, Φ s p =
        iteratedFDeriv ℝ n
          (fun q => pointwiseEisContinuation F Γ σ D k₀ τ u s (ptX F q)) p.1 v := by
  obtain ⟨Φseed, T, hΦseed, hΦseedval, hT, hAdd⟩ :=
    smoothingSeedLift_derivative_data Γ D hD σ τ A hA hsep hτ k₀ hkSmooth hkSupport
      K hK hKpos n v
  let H : ℂ → (K →ᵇ ℂ) := fun s => Φseed s + T (u s)
  have hH : AnalyticOnNhd ℂ H S := by
    have hseedS : AnalyticOnNhd ℂ Φseed S := hΦseed.mono (Set.subset_univ S)
    have hTanalytic : AnalyticOnNhd ℂ (fun s => T (u s)) S := T.comp_analyticOnNhd hu
    exact hseedS.add hTanalytic
  have hR : AnalyticOnNhd ℂ
      (fun s : ℂ => radialTransform F k₀ (1 + 2 * s)) S :=
    (radialTransformParam_analytic k₀ hkSmooth hkSupport).mono (Set.subset_univ S)
  have hRinv : AnalyticOnNhd ℂ
      (fun s : ℂ => (radialTransform F k₀ (1 + 2 * s))⁻¹) S := by
    apply hR.inv
    intro s hs
    exact hhat s hs
  let Φ : ℂ → (K →ᵇ ℂ) := fun s =>
    (radialTransform F k₀ (1 + 2 * s))⁻¹ • H s
  have hΦ : AnalyticOnNhd ℂ Φ S := by
    simpa [Φ] using hRinv.smul hH
  refine ⟨Φ, hΦ, ?_⟩
  have hseedData := specSeed_smooth_analytic Γ D hD σ A hA hsep τ hτ
  have hseed : ∀ s, IsSmoothX F (eisSeed F Γ σ τ s) := fun s => (hseedData.1 s).1
  intro s hs p
  have hpPos : p.1 ∈ posSet F := hKpos p.2
  have hsmSmooth := smoothing_seed_add_lift_isSmooth Γ D hD σ k₀ τ hkSmooth hkSupport
    A hA hsep hτ hseed (u s) s
  have hsmCont : ContDiffAt ℝ n
      (fun q => smoothingOperator F k₀
        (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q)) p.1 := by
    have hc : ContDiffAt ℝ ∞
        (fun q => smoothingOperator F k₀
          (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q)) p.1 :=
      hsmSmooth.contDiffAt (specSeed_posSet_open'.mem_nhds hpPos)
    exact hc.of_le (by simp)
  have hfun : (fun q => pointwiseEisContinuation F Γ σ D k₀ τ u s (ptX F q)) =
      fun q => (radialTransform F k₀ (1 + 2 * s))⁻¹ •
        smoothingOperator F k₀
          (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q) := by
    funext q
    simp [pointwiseEisContinuation, smul_eq_mul]
  calc
    Φ s p = (radialTransform F k₀ (1 + 2 * s))⁻¹ * H s p := by
      simp [Φ, smul_eq_mul]
    _ = (radialTransform F k₀ (1 + 2 * s))⁻¹ *
        iteratedFDeriv ℝ n
          (fun q => smoothingOperator F k₀
            (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q)) p.1 v := by
      calc
        (radialTransform F k₀ (1 + 2 * s))⁻¹ * H s p =
            (radialTransform F k₀ (1 + 2 * s))⁻¹ *
              (Φseed s p + T (u s) p) := by rfl
        _ = (radialTransform F k₀ (1 + 2 * s))⁻¹ *
            iteratedFDeriv ℝ n
              (fun q => smoothingOperator F k₀
                (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q)) p.1 v := by
          rw [← hAdd s (u s) p]
    _ = iteratedFDeriv ℝ n
        (fun q => pointwiseEisContinuation F Γ σ D k₀ τ u s (ptX F q)) p.1 v := by
      symm
      rw [hfun]
      have hder := iteratedFDeriv_const_smul_apply'
        (𝕜 := ℝ) (i := n) (a := (radialTransform F k₀ (1 + 2 * s))⁻¹)
        (f := fun q => smoothingOperator F k₀
          (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q))
        (x := p.1) hsmCont
      have hderV : iteratedFDeriv ℝ n
          (fun q => (radialTransform F k₀ (1 + 2 * s))⁻¹ •
            smoothingOperator F k₀
              (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q)) p.1 v =
          (radialTransform F k₀ (1 + 2 * s))⁻¹ *
            iteratedFDeriv ℝ n
              (fun q => smoothingOperator F k₀
                (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) (ptX F q)) p.1 v := by
        simpa [smul_eq_mul] using congrArg (fun D => D v) hder
      exact hderV

/-- A derivative of the radial kernel in the output variable is jointly continuous in the output
coordinate and the input coordinate. -/
theorem radialKernel_slice_derivative_continuous (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀) (n : ℕ) (v : Fin n → Coord F)
    (p q : Coord F) (hp : p ∈ posSet F) (hq : q ∈ posSet F) :
    iteratedFDeriv ℝ n (fun r => radialKernel F k₀ (ptX F r) (ptX F q)) p v =
      iteratedFDeriv ℝ n
        (fun r : Coord F × Coord F =>
          radialKernel F k₀ (ptX F r.1) (ptX F r.2)) (p, q)
        (fun i => (v i, 0)) := by
  let P : Set (Coord F × Coord F) := {r | r.1 ∈ posSet F ∧ r.2 ∈ posSet F}
  let G : Coord F × Coord F → ℂ := fun r =>
    radialKernel F k₀ (ptX F r.1) (ptX F r.2)
  have hPopen : IsOpen P := by
    change IsOpen (posSet F ×ˢ posSet F)
    exact specSeed_posSet_open'.prod specSeed_posSet_open'
  have hG : ContDiffOn ℝ ∞ G P := by
    exact radialKernel_coord_smooth k₀ hkSmooth
  let a : Coord F × Coord F := (0, q)
  let fshift : Coord F × Coord F → Coord F × Coord F := fun r => r + a
  let S : Set (Coord F × Coord F) := fshift ⁻¹' P
  have hSopen : IsOpen S := hPopen.preimage (by fun_prop)
  have hGshift : ContDiffOn ℝ ∞ (fun r => G (r + a)) S := by
    have hshift : ContDiffOn ℝ ∞ fshift Set.univ := by fun_prop
    simpa [S, fshift, G, Function.comp_def] using hG.comp_inter hshift
  let L : Coord F →L[ℝ] Coord F × Coord F := ContinuousLinearMap.inl ℝ _ _
  let S' : Set (Coord F) := L ⁻¹' S
  have hS'open : IsOpen S' := hSopen.preimage L.continuous
  have hLp : L p ∈ S := by
    simp [S, fshift, L, a, P, hp, hq]
  have hpS' : p ∈ S' := hLp
  have hcomp := L.iteratedFDerivWithin_comp_right
    (f := fun r => G (r + a)) hGshift hSopen.uniqueDiffOn hS'open.uniqueDiffOn
    hLp (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hS'open hpS'] at hcomp
  rw [iteratedFDerivWithin_of_isOpen n hSopen hLp] at hcomp
  have hshiftDeriv := iteratedFDeriv_comp_add_right (𝕜 := ℝ) n a (L p)
    (f := G)
  rw [hshiftDeriv] at hcomp
  have hcompV := congrArg (fun D => D v) hcomp
  simpa [G, L, a, Function.comp_def,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using hcompV

end ArtinPrimitiveRoots.Proofs.spec_continue_p
