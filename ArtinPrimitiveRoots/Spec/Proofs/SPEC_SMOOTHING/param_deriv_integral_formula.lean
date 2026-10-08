import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.Defs

set_option autoImplicit false
set_option maxHeartbeats 5000000
open NumberField MeasureTheory Filter
open scoped ContDiff Topology Filter

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private noncomputable def smoothingKernelDerivInt (k₀ : ℝ → ℝ) (W : Set (X F))
    (f : X F → ℂ) (n : ℕ) (p : Coord F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ :=
  ∫ w in W, f w • iteratedFDeriv ℝ n
    (fun q => radialKernel F k₀ (ptX F q) w) p ∂(volX F)

private theorem smoothingKernelDerivInt_bound (k₀ : ℝ → ℝ)
    (U : Set (Coord F)) (W : Set (X F)) (hcontrol : SmoothingKernelControl F k₀ U W)
    (f : X F → ℂ) (hfInt : IntegrableOn f W (volX F)) (n : ℕ) :
    ∃ b : X F → ℝ, Integrable b ((volX F).restrict W) ∧
      (∀ w, 0 ≤ b w) ∧
      ∀ p ∈ U, ∀ w,
        ‖f w • iteratedFDeriv ℝ n
          (fun q => radialKernel F k₀ (ptX F q) w) p‖ ≤ b w := by
  obtain ⟨C, hC, hbound⟩ := hcontrol.bound n
  let b : X F → ℝ := fun w => C * ‖f w‖
  have hb : Integrable b ((volX F).restrict W) := hfInt.norm.const_mul C
  refine ⟨b, hb, ?_, ?_⟩
  · intro w
    exact mul_nonneg hC (norm_nonneg _)
  · intro p hp w
    rw [norm_smul]
    calc
      ‖f w‖ * ‖iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p‖
          ≤ ‖f w‖ * C := mul_le_mul_of_nonneg_left (hbound p hp w) (norm_nonneg _)
      _ = C * ‖f w‖ := mul_comm _ _

private theorem smoothingKernelDerivIntegrand_integrableOn (k₀ : ℝ → ℝ)
    (U : Set (Coord F)) (W : Set (X F)) (hcontrol : SmoothingKernelControl F k₀ U W)
    (f : X F → ℂ) (hfMeas : AEStronglyMeasurable f (volX F))
    (hfInt : IntegrableOn f W (volX F)) (n : ℕ) (p : Coord F) (hp : p ∈ U) :
    IntegrableOn (fun w => f w • iteratedFDeriv ℝ n
      (fun q => radialKernel F k₀ (ptX F q) w) p) W (volX F) := by
  obtain ⟨b, hb, _, hbound⟩ := smoothingKernelDerivInt_bound k₀ U W hcontrol f hfInt n
  apply hb.mono'
  · exact (hfMeas.smul (hcontrol.measurable n p hp)).mono_measure Measure.restrict_le_self
  · filter_upwards [] with w
    exact hbound p hp w

private theorem smoothingKernelDerivIntegrand_integrable (k₀ : ℝ → ℝ)
    (U : Set (Coord F)) (W : Set (X F)) (hcontrol : SmoothingKernelControl F k₀ U W)
    (f : X F → ℂ) (hfMeas : AEStronglyMeasurable f (volX F))
    (hfInt : IntegrableOn f W (volX F)) (n : ℕ) (p : Coord F) (hp : p ∈ U) :
    Integrable (fun w => f w • iteratedFDeriv ℝ n
      (fun q => radialKernel F k₀ (ptX F q) w) p) (volX F) := by
  have hOn := smoothingKernelDerivIntegrand_integrableOn k₀ U W hcontrol f hfMeas hfInt n p hp
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (f := fun w => f w •
      iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p)
    (s := W) (μ := volX F) hOn
  intro w hw
  simp [hcontrol.support n p hp w hw]

private theorem smoothingKernelPointwise_hasFDerivAt (k₀ : ℝ → ℝ)
    (U : Set (Coord F)) (hU : IsOpen U) (W : Set (X F))
    (hcontrol : SmoothingKernelControl F k₀ U W) (f : X F → ℂ)
    (n : ℕ) (p : Coord F) (hp : p ∈ U) (w : X F) :
    HasFDerivAt
      (fun q => f w • iteratedFDeriv ℝ n
        (fun q' => radialKernel F k₀ (ptX F q') w) q)
      (f w • (iteratedFDeriv ℝ (n + 1)
        (fun q' => radialKernel F k₀ (ptX F q') w) p).curryLeft) p := by
  let g : Coord F → ℂ := fun q => radialKernel F k₀ (ptX F q) w
  have hg : ContDiffAt ℝ ∞ g p := (hcontrol.smooth w p hp).contDiffAt (hU.mem_nhds hp)
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) p :=
    hg.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  have hderiv : HasFDerivAt (fun q => iteratedFDeriv ℝ n g q)
      ((iteratedFDeriv ℝ (n + 1) g p).curryLeft) p := by
    apply hd.hasFDerivAt.congr_fderiv
    rw [fderiv_iteratedFDeriv]
    rfl
  let E := ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ
  let Lsmul : ℂ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℂ
  let L : E →L[ℝ] E := Lsmul (f w)
  have hsmul (x : E) : L x = f w • x := by
    simp [L, Lsmul, ContinuousLinearMap.lsmul_apply]
  have hL : HasFDerivAt (fun x => f w • x) L (iteratedFDeriv ℝ n g p) :=
    (ContinuousLinearMap.hasFDerivAt L).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => (hsmul x).symm)
  have hcomp := HasFDerivAt.comp (f := fun q => iteratedFDeriv ℝ n g q)
    (x := p) hL hderiv
  have hEq : L.comp ((iteratedFDeriv ℝ (n + 1) g p).curryLeft) =
      f w • (iteratedFDeriv ℝ (n + 1) g p).curryLeft := by
    ext x
    simp [L, Lsmul, ContinuousLinearMap.comp_apply, smul_eq_mul]
  simpa only [Function.comp_def] using hcomp.congr_fderiv hEq

private noncomputable def smoothingCurryLeftCLM (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Coord F) ℂ →L[ℝ]
      Coord F →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ := by
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Coord F) ℂ →ₗ[ℝ]
      Coord F →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ := {
    toFun := fun D => D.curryLeft
    map_add' := by intro D D'; ext x v; rfl
    map_smul' := by intro c D; ext x v; simp
  }
  refine ⟨L, AddMonoidHomClass.continuous_of_bound L 1 ?_⟩
  intro D
  change ‖L D‖ ≤ 1 * ‖D‖
  simp [L, ContinuousMultilinearMap.curryLeft_norm]

private theorem smoothingKernelDerivInt_hasFDerivAt (k₀ : ℝ → ℝ)
    (U : Set (Coord F)) (hU : IsOpen U) (W : Set (X F))
    (hcontrol : SmoothingKernelControl F k₀ U W)
    (f : X F → ℂ) (hfMeas : AEStronglyMeasurable f (volX F))
    (hfInt : IntegrableOn f W (volX F)) (n : ℕ) (p : Coord F) (hp : p ∈ U) :
    HasFDerivAt (fun q => smoothingKernelDerivInt k₀ W f n q)
      (smoothingKernelDerivInt k₀ W f (n + 1) p).curryLeft p := by
  let E := ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ
  let E' := ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Coord F) ℂ
  let μW := (volX F).restrict W
  let ScalarL : ℂ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℂ
  let C := smoothingCurryLeftCLM (F := F) n
  let Fpar : Coord F → X F → E := fun q w =>
    f w • iteratedFDeriv ℝ n (fun q' => radialKernel F k₀ (ptX F q') w) q
  let Fpar' : Coord F → X F → Coord F →L[ℝ] E := fun q w =>
    (ScalarL (f w)).comp (C (iteratedFDeriv ℝ (n + 1)
      (fun q' => radialKernel F k₀ (ptX F q') w) q))
  obtain ⟨b, hb, hbpos, hbound⟩ :=
    smoothingKernelDerivInt_bound k₀ U W hcontrol f hfInt (n + 1)
  have hFmeas : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable (Fpar q) μW := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact (hfMeas.smul (hcontrol.measurable n q hq)).mono_measure Measure.restrict_le_self
  have hFint : Integrable (Fpar p) μW := by
    change IntegrableOn (fun w => f w • iteratedFDeriv ℝ n
      (fun q' => radialKernel F k₀ (ptX F q') w) p) W (volX F)
    exact smoothingKernelDerivIntegrand_integrableOn k₀ U W hcontrol f hfMeas hfInt n p hp
  have hCurryMeas : AEStronglyMeasurable
      (fun w => C (iteratedFDeriv ℝ (n + 1)
        (fun q' => radialKernel F k₀ (ptX F q') w) p)) μW := by
    have h := C.continuous.comp_aestronglyMeasurable
      (hcontrol.measurable (n + 1) p hp)
    exact h.mono_measure Measure.restrict_le_self
  have hC_apply (D : E') : C D = D.curryLeft := by
    simp [C, smoothingCurryLeftCLM, LinearMap.mkContinuous_apply]
  have hScalarMeas : AEStronglyMeasurable (fun w => ScalarL (f w)) μW := by
    exact ScalarL.continuous.comp_aestronglyMeasurable
      (hfMeas.mono_measure Measure.restrict_le_self)
  have hF'meas : AEStronglyMeasurable (Fpar' p) μW := by
    change AEStronglyMeasurable (fun w => (ScalarL (f w)).comp
      (C (iteratedFDeriv ℝ (n + 1)
        (fun q' => radialKernel F k₀ (ptX F q') w) p))) μW
    let pairFn : X F → (E →L[ℝ] E) × (Coord F →L[ℝ] E) := fun w =>
      (ScalarL (f w), C (iteratedFDeriv ℝ (n + 1)
        (fun q' => radialKernel F k₀ (ptX F q') w) p))
    have hpair : AEStronglyMeasurable pairFn μW := hScalarMeas.prodMk hCurryMeas
    -- Composition is continuous in both operator arguments.
    have hcomp : Continuous (fun z : (E →L[ℝ] E) ×
        (Coord F →L[ℝ] E) => z.1.comp z.2) := by fun_prop
    change AEStronglyMeasurable
      (fun w => (fun z : (E →L[ℝ] E) × (Coord F →L[ℝ] E) => z.1.comp z.2) (pairFn w)) μW
    exact hcomp.comp_aestronglyMeasurable hpair
  have hBound : ∀ᵐ w ∂μW, ∀ q ∈ U, ‖Fpar' q w‖ ≤ b w := by
    filter_upwards [] with w q hq
    calc
      ‖Fpar' q w‖ ≤ ‖ScalarL (f w)‖ * ‖C (iteratedFDeriv ℝ (n + 1)
          (fun q' => radialKernel F k₀ (ptX F q') w) q)‖ := by
        exact (ScalarL (f w)).opNorm_comp_le _
      _ ≤ ‖f w‖ * ‖C (iteratedFDeriv ℝ (n + 1)
          (fun q' => radialKernel F k₀ (ptX F q') w) q)‖ := by
        exact mul_le_mul_of_nonneg_right
          (by simpa [ScalarL] using
            (ContinuousLinearMap.opNorm_lsmul_apply_le (𝕜 := ℝ) (R := ℂ) (E := E) (f w)))
          (norm_nonneg (C (iteratedFDeriv ℝ (n + 1)
            (fun q' => radialKernel F k₀ (ptX F q') w) q)))
      _ = ‖f w • iteratedFDeriv ℝ (n + 1)
          (fun q' => radialKernel F k₀ (ptX F q') w) q‖ := by
        rw [hC_apply, norm_smul, ContinuousMultilinearMap.curryLeft_norm]
      _ ≤ b w := hbound q hq w
  have hDiff : ∀ᵐ w ∂μW, ∀ q ∈ U,
      HasFDerivAt (Fpar · w) (Fpar' q w) q := by
    filter_upwards [] with w q hq
    have hpoint := smoothingKernelPointwise_hasFDerivAt k₀ U hU W hcontrol f n q hq w
    apply hpoint.congr_fderiv
    have hmap (D : E') : f w • D.curryLeft = (ScalarL (f w)).comp (C D) := by
      ext x v
      rw [ContinuousLinearMap.comp_apply, hC_apply D]
      change f w • (D.curryLeft x v) = f w • (D.curryLeft x v)
      rfl
    exact hmap (iteratedFDeriv ℝ (n + 1)
      (fun q' => radialKernel F k₀ (ptX F q') w) q)
  have hparam : HasFDerivAt (fun q => ∫ w, Fpar q w ∂μW)
      (∫ w, Fpar' p w ∂μW) p :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := Fpar) (F' := Fpar') (x₀ := p) (s := U) (μ := μW) (bound := b)
      (hU.mem_nhds hp) hFmeas hFint hF'meas hBound hb hDiff
  have hIntNext : Integrable (fun w => f w • iteratedFDeriv ℝ (n + 1)
      (fun q' => radialKernel F k₀ (ptX F q') w) p) μW := by
    change IntegrableOn (fun w => f w • iteratedFDeriv ℝ (n + 1)
      (fun q' => radialKernel F k₀ (ptX F q') w) p) W (volX F)
    exact smoothingKernelDerivIntegrand_integrableOn k₀ U W hcontrol f hfMeas hfInt
      (n + 1) p hp
  have hF'bound : ∀ᵐ w ∂μW, ‖Fpar' p w‖ ≤ b w := by
    filter_upwards [hBound] with w hw
    exact hw p hp
  have hF'boundEnorm : ∀ᵐ w ∂μW, ‖Fpar' p w‖ₑ ≤ ‖b w‖ₑ := by
    filter_upwards [hF'bound] with w hw
    rw [enorm_le_iff_norm_le, Real.norm_of_nonneg (hbpos w)]
    exact hw
  letI : ContinuousENorm (Coord F →L[ℝ] E) := {
    toENorm := inferInstance
    continuous_enorm := by fun_prop
  }
  have hF'int : Integrable (Fpar' p) μW := hb.enorm.mono'_enorm hF'meas hF'boundEnorm
  have hF'evalBound (x : Coord F) :
      ∀ᵐ w ∂μW, ‖Fpar' p w x‖ ≤ b w * ‖x‖ := by
    filter_upwards [hF'bound] with w hw
    calc
      ‖Fpar' p w x‖ ≤ ‖Fpar' p w‖ * ‖x‖ := (Fpar' p w).le_opNorm x
      _ ≤ b w * ‖x‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
  have hF'evalInt (x : Coord F) : Integrable (fun w => Fpar' p w x) μW := by
    have hbX : Integrable (fun w => b w * ‖x‖) μW := by
      simpa [mul_comm] using hb.const_mul ‖x‖
    exact hbX.mono' (hF'meas.apply_continuousLinearMap x) (hF'evalBound x)
  have hFparEval (x : Coord F) (v : Fin n → Coord F) (w : X F) :
      Fpar' p w x v = f w •
        iteratedFDeriv ℝ (n + 1)
          (fun q' => radialKernel F k₀ (ptX F q') w) p (Fin.cons x v) := by
    let D := iteratedFDeriv ℝ (n + 1)
      (fun q' => radialKernel F k₀ (ptX F q') w) p
    change ((ScalarL (f w)).comp (C D) x) v = f w • D (Fin.cons x v)
    simp only [ContinuousLinearMap.comp_apply, hC_apply, ScalarL,
      ContinuousLinearMap.lsmul_apply]
    change f w • (D.curryLeft x v) = f w • D (Fin.cons x v)
    rw [ContinuousMultilinearMap.curryLeft_apply]
  have hCurryIntegral :
      (∫ w, Fpar' p w ∂μW) = (smoothingKernelDerivInt k₀ W f (n + 1) p).curryLeft := by
    ext x v
    calc
      (∫ w, Fpar' p w ∂μW) x v = (∫ w, Fpar' p w x ∂μW) v := by
        rw [ContinuousLinearMap.integral_apply hF'int x]
      _ = ∫ w, Fpar' p w x v ∂μW :=
        ContinuousMultilinearMap.integral_apply (hF'evalInt x) v
      _ = ∫ w, f w • iteratedFDeriv ℝ (n + 1)
          (fun q' => radialKernel F k₀ (ptX F q') w) p (Fin.cons x v) ∂μW := by
        apply integral_congr_ae
        filter_upwards [] with w
        exact hFparEval x v w
      _ = (∫ w, f w • iteratedFDeriv ℝ (n + 1)
          (fun q' => radialKernel F k₀ (ptX F q') w) p ∂μW) (Fin.cons x v) := by
        symm
        exact ContinuousMultilinearMap.integral_apply hIntNext (Fin.cons x v)
      _ = ((smoothingKernelDerivInt k₀ W f (n + 1) p).curryLeft x) v := by
        change (∫ w in W, f w • iteratedFDeriv ℝ (n + 1)
          (fun q' => radialKernel F k₀ (ptX F q') w) p ∂(volX F)) (Fin.cons x v) =
          (∫ w in W, f w • iteratedFDeriv ℝ (n + 1)
            (fun q' => radialKernel F k₀ (ptX F q') w) p ∂(volX F)) (Fin.cons x v)
        rfl
  have hparam' := hparam.congr_fderiv hCurryIntegral
  simpa [Fpar, smoothingKernelDerivInt] using hparam'

private theorem smoothingKernelDerivInt_iterated (k₀ : ℝ → ℝ)
    (U : Set (Coord F)) (hU : IsOpen U) (W : Set (X F))
    (hcontrol : SmoothingKernelControl F k₀ U W)
    (f : X F → ℂ) (hfMeas : AEStronglyMeasurable f (volX F))
    (hfInt : IntegrableOn f W (volX F)) :
    ∀ n (p : Coord F), p ∈ U →
      iteratedFDeriv ℝ n (fun q => smoothingOperator F k₀ f (ptX F q)) p =
        smoothingKernelDerivInt k₀ W f n p := by
  let g : Coord F → ℂ := fun q => smoothingOperator F k₀ f (ptX F q)
  intro n
  induction n with
  | zero =>
      intro p hp
      have h0IntOn : IntegrableOn (fun w => f w • iteratedFDeriv ℝ 0
          (fun q => radialKernel F k₀ (ptX F q) w) p) W (volX F) :=
        smoothingKernelDerivIntegrand_integrableOn k₀ U W hcontrol f hfMeas hfInt 0 p hp
      ext v
      rw [iteratedFDeriv_zero_apply]
      change smoothingOperator F k₀ f (ptX F p) =
        (∫ w in W, f w • iteratedFDeriv ℝ 0
          (fun q => radialKernel F k₀ (ptX F q) w) p ∂(volX F)) v
      rw [smoothingOperator, ContinuousMultilinearMap.integral_apply h0IntOn v]
      have hzero : ∀ w, w ∉ W →
          radialKernel F k₀ (ptX F p) w * f w = 0 := by
        intro w hw
        have hD := hcontrol.support 0 p hp w hw
        have hv := congrArg (fun D : ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => Coord F) ℂ => D (fun i => Fin.elim0 i)) hD
        have hk : radialKernel F k₀ (ptX F p) w = 0 := by
          simpa [iteratedFDeriv_zero_apply] using hv
        simp [hk]
      calc
        (∫ w, radialKernel F k₀ (ptX F p) w * f w ∂(volX F)) =
            ∫ w in W, radialKernel F k₀ (ptX F p) w * f w ∂(volX F) :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
        _ = ∫ w in W, f w • iteratedFDeriv ℝ 0
              (fun q => radialKernel F k₀ (ptX F q) w) p v ∂(volX F) := by
          apply integral_congr_ae
          filter_upwards [] with w
          simp [iteratedFDeriv_zero_apply, smul_eq_mul, mul_comm]
  | succ n ih =>
      intro p hp
      have hEq : (fun q => iteratedFDeriv ℝ n g q) =ᶠ[𝓝 p]
          (fun q => smoothingKernelDerivInt k₀ W f n q) := by
        filter_upwards [hU.mem_nhds hp] with q hq
        exact ih q hq
      have hderiv := smoothingKernelDerivInt_hasFDerivAt k₀ U hU W hcontrol
        f hfMeas hfInt n p hp
      have hderiv' := hderiv.congr_of_eventuallyEq hEq
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hderiv'.fderiv]
      change (smoothingKernelDerivInt k₀ W f (n + 1) p).curryLeft.uncurryLeft =
        smoothingKernelDerivInt k₀ W f (n + 1) p
      exact ContinuousMultilinearMap.uncurry_curryLeft _

/-- Local L1 and compact kernel control give smoothness and all multilinear
derivative-integral identities. Only the representative on W needs to be integrable.
Guide: `sol-thin-spec/PROOFS.md:403–405`. Uses `SmoothingKernelControl` and Mathlib's
`hasFDerivAt_integral_of_dominated_of_fderiv_le`; supplies
`smoothing_uniform_eval_bound`, `smoothing_smooth_representative`, S1 and generic S3 smoothing. -/
theorem param_deriv_integral_formula (k₀ : ℝ → ℝ)
    (U : Set (Coord F)) (hU : IsOpen U) (hUpos : U ⊆ posSet F)
    (W : Set (X F)) (hW : IsCompact W) (hcontrol : SmoothingKernelControl F k₀ U W)
    (f : X F → ℂ) (hfMeas : AEStronglyMeasurable f (volX F))
    (hfInt : IntegrableOn f W (volX F)) :
    ContDiffOn ℝ ∞ (fun q => smoothingOperator F k₀ f (ptX F q)) U ∧
      ∀ (n : ℕ) (p : Coord F), p ∈ U →
        Integrable (fun w => f w •
          iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p) (volX F) ∧
        iteratedFDeriv ℝ n (fun q => smoothingOperator F k₀ f (ptX F q)) p =
          ∫ w, f w • iteratedFDeriv ℝ n
            (fun q => radialKernel F k₀ (ptX F q) w) p ∂(volX F) ∧
    ∀ v : Fin n → Coord F,
          iteratedFDeriv ℝ n (fun q => smoothingOperator F k₀ f (ptX F q)) p v =
            ∫ w, iteratedFDeriv ℝ n
              (fun q => radialKernel F k₀ (ptX F q) w) p v * f w ∂(volX F) := by
  let g : Coord F → ℂ := fun q => smoothingOperator F k₀ f (ptX F q)
  have hiter := smoothingKernelDerivInt_iterated k₀ U hU W hcontrol f hfMeas hfInt
  have hSmooth : ContDiffOn ℝ ∞ g U := by
    refine contDiffOn_of_differentiableOn ?_
    intro m hm q hq
    have hwithin : iteratedFDerivWithin ℝ m g U q =
        smoothingKernelDerivInt k₀ W f m q := by
      calc
        iteratedFDerivWithin ℝ m g U q = iteratedFDeriv ℝ m g q :=
          iteratedFDerivWithin_of_isOpen m hU (x := q) hq
        _ = smoothingKernelDerivInt k₀ W f m q := hiter m q hq
    have hderiv := smoothingKernelDerivInt_hasFDerivAt k₀ U hU W hcontrol
      f hfMeas hfInt m q hq
    have hdiff : DifferentiableWithinAt ℝ
        (fun r => smoothingKernelDerivInt k₀ W f m r) U q :=
      hderiv.differentiableAt.differentiableWithinAt
    exact hdiff.congr
      (fun r hr => by
        calc
          iteratedFDerivWithin ℝ m g U r = iteratedFDeriv ℝ m g r :=
            iteratedFDerivWithin_of_isOpen m hU (x := r) hr
          _ = smoothingKernelDerivInt k₀ W f m r := hiter m r hr)
      hwithin
  refine ⟨?_, ?_⟩
  · simpa [g] using hSmooth
  · intro n p hp
    have hIntOn := smoothingKernelDerivIntegrand_integrableOn k₀ U W hcontrol
      f hfMeas hfInt n p hp
    have hInt := smoothingKernelDerivIntegrand_integrable k₀ U W hcontrol
      f hfMeas hfInt n p hp
    have hIter := hiter n p hp
    refine ⟨hInt, ?_, ?_⟩
    · calc
        iteratedFDeriv ℝ n g p = smoothingKernelDerivInt k₀ W f n p := hIter
        _ = ∫ w, f w • iteratedFDeriv ℝ n
              (fun q => radialKernel F k₀ (ptX F q) w) p ∂(volX F) := by
          unfold smoothingKernelDerivInt
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro w hw
          simp [hcontrol.support n p hp w hw]
    · intro v
      have hzero (w : X F) (hw : w ∉ W) :
          iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p v * f w = 0 := by
        have hD := hcontrol.support n p hp w hw
        have hv := congrArg (fun D : ContinuousMultilinearMap ℝ
            (fun _ : Fin n => Coord F) ℂ => D v) hD
        simp [hv]
      calc
        iteratedFDeriv ℝ n g p v =
            (smoothingKernelDerivInt k₀ W f n p) v := congrArg (fun D => D v) hIter
        _ = ∫ w in W, f w • iteratedFDeriv ℝ n
              (fun q => radialKernel F k₀ (ptX F q) w) p v ∂(volX F) :=
          ContinuousMultilinearMap.integral_apply hIntOn v
        _ = ∫ w in W, iteratedFDeriv ℝ n
              (fun q => radialKernel F k₀ (ptX F q) w) p v * f w ∂(volX F) := by
          apply integral_congr_ae
          filter_upwards [] with w
          simp [smul_eq_mul, mul_comm]
        _ = ∫ w, iteratedFDeriv ℝ n
              (fun q => radialKernel F k₀ (ptX F q) w) p v * f w ∂(volX F) :=
          setIntegral_eq_integral_of_forall_compl_eq_zero hzero

end ArtinPrimitiveRoots.A1.Spec
