import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_compact_control
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.param_deriv_integral_formula
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.localLiftCLM

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private noncomputable def smoothingEvalBCF {α β : Type*} [TopologicalSpace α]
    [PseudoMetricSpace β] (K : Set α) [CompactSpace K] (g : α → β)
    (hg : ContinuousOn g K) : K →ᵇ β :=
  ContinuousMap.equivBoundedOfCompact K β
    ⟨fun x => g x, (continuousOn_iff_continuous_restrict).mp hg⟩

private noncomputable def smoothingEvalDirCLM (n : ℕ) (v : Fin n → Coord F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ →L[ℝ] ℂ := by
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ →ₗ[ℝ] ℂ := {
    toFun := fun D => D v
    map_add' := by intro D D'; rfl
    map_smul' := by intro c D; simp
  }
  refine L.mkContinuous (∏ i, ‖v i‖) ?_
  intro D
  change ‖D v‖ ≤ (∏ i, ‖v i‖) * ‖D‖
  calc
    ‖D v‖ ≤ ‖D‖ * ∏ i, ‖v i‖ := D.le_opNorm v
    _ = (∏ i, ‖v i‖) * ‖D‖ := by ring

/-- Every fixed derivative evaluation on a compact coordinate set defines a bounded continuous
linear map, with its local L1/Cauchy–Schwarz bound. Constants are independent of the L2 vector.
Uses `radialKernel_compact_control`,
`param_deriv_integral_formula`, `localLiftCLM`, and frozen `G3_volume` and `T1_l2`.
Supplies the derivative-map conjunct of frozen `S1_smoothing` and generic maps for S3. -/
theorem smoothing_uniform_eval_bound (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F)
    (n : ℕ) (v : Fin n → Coord F) :
    ∃ (W : Set (X F)) (C : ℝ) (T : L2Space F D →L[ℂ] (K →ᵇ ℂ)),
      IsCompact W ∧ 0 ≤ C ∧
        ‖T‖ ≤ C * Real.sqrt ((volX F).real W) *
          Real.sqrt (overlapMultiplicity F Γ W : ℝ) ∧
        ∀ u p, T u p = iteratedFDeriv ℝ n
          (fun q => smoothingOperator F k₀ (l2Lift F Γ D u) (ptX F q)) p.1 v := by
  obtain ⟨U, W, hU, hKU, hUpos, hW, hcontrol⟩ :=
    radialKernel_compact_control k₀ hkSmooth hkSupport K hK hKpos
  let μW := (volX F).restrict W
  have hWvol : (volX F) W < ⊤ := (G3_volume (F := F)).2.2.1 W hW
  letI : IsFiniteMeasure μW := ⟨by
    simpa [μW, Measure.restrict_apply MeasurableSet.univ] using hWvol⟩
  obtain ⟨L, hLbound, hLrep⟩ := localLiftCLM Γ D hD W hW
  have hLiftMem (u : L2Space F D) : MemLp (l2Lift F Γ D u) 2 μW := by
    have hmem : MemLp (L u) 2 μW := Lp.memLp (L u)
    have hEq : l2Lift F Γ D u =ᵐ[μW] (L u) := by
      filter_upwards [hLrep u] with z hz
      exact hz.symm
    exact (memLp_congr_ae hEq).2 hmem
  have hLiftInt (u : L2Space F D) : IntegrableOn (l2Lift F Γ D u) W (volX F) := by
    change Integrable (l2Lift F Γ D u) μW
    exact (hLiftMem u).integrable (by norm_num)
  have hT1 := T1_l2 Γ D hD
  have hLiftSquare (u : L2Space F D) :
      ∫ z in W, ‖l2Lift F Γ D u z‖ ^ 2 ∂(volX F) ≤
        (overlapMultiplicity F Γ W : ℝ) * ‖u‖ ^ 2 :=
    (hT1.2.1 W hW).2 u
  have hLiftL1 (u : L2Space F D) :
      ∫ z in W, ‖l2Lift F Γ D u z‖ ∂(volX F) ≤
        Real.sqrt ((volX F).real W) *
          Real.sqrt (overlapMultiplicity F Γ W : ℝ) * ‖u‖ := by
    let f : X F → ℝ := fun z => ‖l2Lift F Γ D u z‖
    have hf : MemLp f 2 μW := by
      simpa [f] using (hLiftMem u).norm
    have hf' : MemLp f (ENNReal.ofReal 2) μW := by simpa using hf
    have hOne : MemLp (fun _ : X F => (1 : ℝ)) 2 μW := by
      exact memLp_const 1
    have hOne' : MemLp (fun _ : X F => (1 : ℝ)) (ENNReal.ofReal 2) μW := by
      simpa using hOne
    have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μW) (f := f) (g := fun _ : X F => (1 : ℝ)) Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun z => norm_nonneg (l2Lift F Γ D u z))
      (Filter.Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ 1)) hf' hOne'
    have hsq : ∫ z, f z ^ 2 ∂μW ≤
        (overlapMultiplicity F Γ W : ℝ) * ‖u‖ ^ 2 := by
      change ∫ z in W, ‖l2Lift F Γ D u z‖ ^ 2 ∂(volX F) ≤ _
      exact hLiftSquare u
    have hvol : μW.real Set.univ = (volX F).real W := by
      simp [μW, Measure.real, Measure.restrict_apply MeasurableSet.univ]
    have hOneInt : ∫ z, (1 : ℝ) ^ (2 : ℝ) ∂μW = μW.real Set.univ := by
      simp [Real.rpow_natCast]
    have hsqR : ∫ z, f z ^ (2 : ℝ) ∂μW ≤
        (overlapMultiplicity F Γ W : ℝ) * ‖u‖ ^ 2 := by
      calc
        ∫ z, f z ^ (2 : ℝ) ∂μW = ∫ z, f z ^ 2 ∂μW := by
          apply integral_congr_ae
          filter_upwards [] with z
          calc
            f z ^ (2 : ℝ) = f z ^ ((2 : ℕ) : ℝ) := by congr 1 <;> norm_num
            _ = f z ^ 2 := Real.rpow_natCast (f z) 2
        _ ≤ _ := hsq
    have hHolder' : ∫ z, f z ∂μW ≤
        (∫ z, f z ^ (2 : ℝ) ∂μW) ^ (1 / (2 : ℝ)) *
          ((volX F).real W) ^ (1 / (2 : ℝ)) := by
      calc
        ∫ z, f z ∂μW = ∫ z, f z * (1 : ℝ) ∂μW := by
          apply integral_congr_ae
          filter_upwards [] with z
          simp
        _ ≤ (∫ z, f z ^ (2 : ℝ) ∂μW) ^ (1 / (2 : ℝ)) *
              (∫ z, (1 : ℝ) ^ (2 : ℝ) ∂μW) ^ (1 / (2 : ℝ)) := hHolder
        _ = (∫ z, f z ^ (2 : ℝ) ∂μW) ^ (1 / (2 : ℝ)) *
              ((volX F).real W) ^ (1 / (2 : ℝ)) := by
          let A : ℝ := (∫ z, f z ^ (2 : ℝ) ∂μW) ^ (1 / (2 : ℝ))
          have hOnePow := congrArg (fun x : ℝ => x ^ (1 / (2 : ℝ))) hOneInt
          have hVolPow := congrArg (fun x : ℝ => x ^ (1 / (2 : ℝ))) hvol
          calc
            _ = A * (μW.real Set.univ) ^ (1 / (2 : ℝ)) := by
              dsimp [A]
              exact congrArg (fun x : ℝ =>
                ((∫ z, f z ^ (2 : ℝ) ∂μW) ^ (1 / (2 : ℝ)) * x)) hOnePow
            _ = A * ((volX F).real W) ^ (1 / (2 : ℝ)) := by
              exact congrArg (fun x : ℝ => A * x) hVolPow
    have hsqRoot : (∫ z, f z ^ (2 : ℝ) ∂μW) ^ (1 / (2 : ℝ)) ≤
        Real.sqrt ((overlapMultiplicity F Γ W : ℝ) * ‖u‖ ^ 2) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow (x := ∫ z, f z ^ (2 : ℝ) ∂μW)
        (y := (overlapMultiplicity F Γ W : ℝ) * ‖u‖ ^ 2) (z := (1 / 2 : ℝ))
        (integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _) hsqR (by norm_num)
    have hvolRoot : ((volX F).real W) ^ (1 / (2 : ℝ)) =
        Real.sqrt ((volX F).real W) := by
      rw [Real.sqrt_eq_rpow]
    calc
      ∫ z in W, ‖l2Lift F Γ D u z‖ ∂(volX F)
          = ∫ z, f z ∂μW := by rfl
      _ ≤ Real.sqrt ((overlapMultiplicity F Γ W : ℝ) * ‖u‖ ^ 2) *
            Real.sqrt ((volX F).real W) := by
          calc
            ∫ z, f z ∂μW ≤
                (∫ z, f z ^ (2 : ℝ) ∂μW) ^ (1 / (2 : ℝ)) *
                  ((volX F).real W) ^ (1 / (2 : ℝ)) := hHolder'
            _ ≤ Real.sqrt ((overlapMultiplicity F Γ W : ℝ) * ‖u‖ ^ 2) *
                  ((volX F).real W) ^ (1 / (2 : ℝ)) :=
              mul_le_mul_of_nonneg_right hsqRoot (by positivity)
            _ = Real.sqrt ((overlapMultiplicity F Γ W : ℝ) * ‖u‖ ^ 2) *
                  Real.sqrt ((volX F).real W) := by rw [hvolRoot]
      _ = Real.sqrt (overlapMultiplicity F Γ W : ℝ) * ‖u‖ *
            Real.sqrt ((volX F).real W) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
            abs_of_nonneg (norm_nonneg _)]
      _ = Real.sqrt ((volX F).real W) *
            Real.sqrt (overlapMultiplicity F Γ W : ℝ) * ‖u‖ := by ring
  obtain ⟨C₀, hC₀, hC₀bound⟩ := hcontrol.bound n
  let C : ℝ := C₀ * ∏ i, ‖v i‖
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  let g (u : L2Space F D) (p : Coord F) : ℂ :=
    iteratedFDeriv ℝ n
      (fun q => smoothingOperator F k₀ (l2Lift F Γ D u) (ptX F q)) p v
  have hFormula (u : L2Space F D) :=
    param_deriv_integral_formula k₀ U hU hUpos W hW hcontrol
      (l2Lift F Γ D u) (hT1.1 u).1 (hLiftInt u)
  have hScalarInt (u : L2Space F D) (p : Coord F) (hp : p ∈ U) :
      Integrable (fun w =>
        (iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p) v *
          l2Lift F Γ D u w) (volX F) := by
    have h := (smoothingEvalDirCLM n v).integrable_comp
      ((hFormula u).2 n p hp).1
    convert h using 1 <;> ext w <;> simp [smoothingEvalDirCLM,
      LinearMap.mkContinuous_apply, smul_eq_mul, mul_comm]
  have hcont (u : L2Space F D) : ContinuousOn (g u) U := by
    have hderiv := ContinuousOn.continuousOn_iteratedFDeriv (k := n)
      (hFormula u).1 hU (by simp)
    have heval : Continuous
        (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F) ℂ => D v) := by
      fun_prop
    exact heval.comp_continuousOn hderiv
  letI : CompactSpace K := (isCompact_iff_compactSpace).1 hK
  let Tlin : L2Space F D →ₗ[ℂ] (K →ᵇ ℂ) := {
    toFun := fun u => smoothingEvalBCF K (g u) ((hcont u).mono hKU)
    map_add' := by
      intro u u'
      apply BoundedContinuousFunction.ext
      intro p
      change g (u + u') p = g u p + g u' p
      let d (w : X F) := iteratedFDeriv ℝ n
        (fun q => radialKernel F k₀ (ptX F q) w) p.1 v
      have hp : (p : Coord F) ∈ U := hKU p.2
      have hsum := localLift_add_ae Γ D hD (localLift_action_measurePreserving Γ) u u'
      have hIntU : Integrable (fun w => d w * l2Lift F Γ D u w) (volX F) := by
        exact hScalarInt u p.1 hp
      have hIntU' : Integrable (fun w => d w * l2Lift F Γ D u' w) (volX F) := by
        exact hScalarInt u' p.1 hp
      calc
        g (u + u') p = ∫ w, d w * l2Lift F Γ D (u + u') w ∂(volX F) :=
          ((hFormula (u + u')).2 n p.1 hp).2.2 v
        _ = ∫ w, d w * (l2Lift F Γ D u w + l2Lift F Γ D u' w) ∂(volX F) := by
          apply integral_congr_ae
          filter_upwards [hsum] with w hw
          simp [d, hw]
        _ = ∫ w, (d w * l2Lift F Γ D u w + d w * l2Lift F Γ D u' w)
            ∂(volX F) := by
          apply integral_congr_ae
          filter_upwards [] with w
          ring
        _ = (∫ w, d w * l2Lift F Γ D u w ∂(volX F)) +
            ∫ w, d w * l2Lift F Γ D u' w ∂(volX F) := integral_add hIntU hIntU'
        _ = g u p + g u' p := by
          rw [← ((hFormula u).2 n p.1 hp).2.2 v,
            ← ((hFormula u').2 n p.1 hp).2.2 v]
    map_smul' := by
      intro c u
      apply BoundedContinuousFunction.ext
      intro p
      change g (c • u) p = c • g u p
      let d (w : X F) := iteratedFDeriv ℝ n
        (fun q => radialKernel F k₀ (ptX F q) w) p.1 v
      have hp : (p : Coord F) ∈ U := hKU p.2
      have hsmul := localLift_smul_ae Γ D hD
        (localLift_action_measurePreserving Γ) c u
      have hIntU : Integrable (fun w => d w * l2Lift F Γ D u w) (volX F) := by
        exact hScalarInt u p.1 hp
      calc
        g (c • u) p = ∫ w, d w * l2Lift F Γ D (c • u) w ∂(volX F) :=
          ((hFormula (c • u)).2 n p.1 hp).2.2 v
        _ = ∫ w, c • (d w * l2Lift F Γ D u w) ∂(volX F) := by
          apply integral_congr_ae
          filter_upwards [hsmul] with w hw
          simp [d, hw, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
        _ = c • (∫ w, d w * l2Lift F Γ D u w ∂(volX F)) := integral_smul c _
        _ = c • g u p := by rw [← ((hFormula u).2 n p.1 hp).2.2 v]
  }
  have hpointBound (u : L2Space F D) (p : K) :
      ‖Tlin u p‖ ≤ C * Real.sqrt ((volX F).real W) *
        Real.sqrt (overlapMultiplicity F Γ W : ℝ) * ‖u‖ := by
    change ‖g u p.1‖ ≤ _
    have hp : p.1 ∈ U := hKU p.2
    let d (w : X F) := iteratedFDeriv ℝ n
      (fun q => radialKernel F k₀ (ptX F q) w) p.1 v
    have hformula := ((hFormula u).2 n p.1 hp).2.2 v
    have hformula' : g u p.1 = ∫ w, d w * l2Lift F Γ D u w ∂(volX F) := by
      simpa [g, d] using hformula
    have hzero : ∀ w, w ∉ W → d w * l2Lift F Γ D u w = 0 := by
      intro w hw
      have hs := hcontrol.support n p.1 hp w hw
      have hs' := congrArg (fun D : ContinuousMultilinearMap
          ℝ (fun _ : Fin n => Coord F) ℂ => D v) hs
      simp [d, hs']
    have hset : (∫ w, d w * l2Lift F Γ D u w ∂(volX F)) =
        ∫ w in W, d w * l2Lift F Γ D u w ∂(volX F) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    have hIntW : Integrable (fun w => d w * l2Lift F Γ D u w) μW := by
      change Integrable (fun w =>
        (iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p.1) v *
          l2Lift F Γ D u w) ((volX F).restrict W)
      exact (hScalarInt u p.1 hp).restrict
    have hkernel (w : X F) : ‖d w‖ ≤ C := by
      dsimp [d, C]
      calc
        ‖(iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p.1) v‖ ≤
            ‖iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p.1‖ *
              ∏ i, ‖v i‖ := ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ C₀ * ∏ i, ‖v i‖ := by
          gcongr
          exact hC₀bound p.1 hp w
    have hmajor : Integrable (fun w => C * ‖l2Lift F Γ D u w‖) μW :=
      (hLiftInt u).norm.const_mul C
    have hnormBound : ∀ᵐ w ∂μW,
        ‖d w * l2Lift F Γ D u w‖ ≤ C * ‖l2Lift F Γ D u w‖ := by
      filter_upwards [] with w
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hkernel w) (norm_nonneg _)
    calc
      ‖Tlin u p‖ = ‖∫ w in W, d w * l2Lift F Γ D u w ∂(volX F)‖ := by
        change ‖g u p.1‖ = _
        rw [hformula', hset]
      _ ≤ ∫ w, ‖d w * l2Lift F Γ D u w‖ ∂μW := norm_integral_le_integral_norm _
      _ ≤ ∫ w, C * ‖l2Lift F Γ D u w‖ ∂μW := integral_mono_ae
        (hIntW.norm) hmajor hnormBound
      _ = C * ∫ w, ‖l2Lift F Γ D u w‖ ∂μW := by rw [integral_const_mul]
      _ ≤ C * (Real.sqrt ((volX F).real W) *
          Real.sqrt (overlapMultiplicity F Γ W : ℝ) * ‖u‖) := by
        exact mul_le_mul_of_nonneg_left (hLiftL1 u) hC
      _ = C * Real.sqrt ((volX F).real W) *
          Real.sqrt (overlapMultiplicity F Γ W : ℝ) * ‖u‖ := by ring
  have hbound (u : L2Space F D) : ‖Tlin u‖ ≤
      (C * Real.sqrt ((volX F).real W) *
        Real.sqrt (overlapMultiplicity F Γ W : ℝ)) * ‖u‖ := by
    let bcf := smoothingEvalBCF K (g u) ((hcont u).mono hKU)
    change ‖bcf‖ ≤ _
    by_cases hKne : Nonempty K
    · letI : Nonempty K := hKne
      apply (BoundedContinuousFunction.norm_le_of_nonempty).2
      intro p
      exact hpointBound u p
    · letI : IsEmpty K := not_nonempty_iff.mp hKne
      have hzero : bcf = 0 := BoundedContinuousFunction.eq_of_empty bcf 0
      rw [hzero, norm_zero]
      positivity
  let T : L2Space F D →L[ℂ] (K →ᵇ ℂ) :=
    Tlin.mkContinuous (C * Real.sqrt ((volX F).real W) *
      Real.sqrt (overlapMultiplicity F Γ W : ℝ)) hbound
  refine ⟨W, C, T, hW, hC, ?_, ?_⟩
  · change ‖Tlin.mkContinuous _ _‖ ≤ _
    exact LinearMap.mkContinuous_norm_le Tlin
      (by positivity) hbound
  · intro u p
    rfl

end ArtinPrimitiveRoots.A1.Spec
