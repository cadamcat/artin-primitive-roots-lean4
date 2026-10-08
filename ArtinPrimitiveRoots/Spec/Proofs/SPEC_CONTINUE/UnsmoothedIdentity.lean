import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.SmoothingSeedAnalytic
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.localLiftCLM
import ArtinPrimitiveRoots.Spec.Domain
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false

open NumberField Matrix MeasureTheory Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology

noncomputable section

open ArtinPrimitiveRoots.A1.Spec
open ArtinPrimitiveRoots.Proofs.spec_continue_p

namespace ArtinPrimitiveRoots.Proofs.spec_cont_sol

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Coordinate families on a compact set give local L² families on the corresponding
compact set in X. Extension by zero supplies the ambient representative. -/
private theorem compactCoordinateToLp (K : Set (X F)) (hK : IsCompact K) :
    ∃ T : (coordsX F '' K →ᵇ ℂ) →L[ℂ] Lp ℂ 2 ((volX F).restrict K),
      ∀ f, ∀ᵐ z ∂((volX F).restrict K), ∀ hz : z ∈ K,
        T f z = f ⟨coordsX F z, Set.mem_image_of_mem (coordsX F) hz⟩ := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchartX⟩ := G1_h3_basics (F := F)
  obtain ⟨eChartX, _, _⟩ := hchartX
  letI : T2Space (X F) := eChartX.t2Space
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  let P : Set (Coord F) := coordsX F '' K
  have hP : IsCompact P := hK.image specCoordsX_continuous
  let μ : Measure (X F) := (volX F).restrict K
  have hfinite : μ Set.univ < ⊤ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ] using
      (G3_volume (F := F)).2.2.1 K hK
  letI : IsFiniteMeasure μ := ⟨hfinite⟩
  let ext : (P →ᵇ ℂ) → X F → ℂ := fun f z =>
    Function.extend (Subtype.val : P → Coord F) f 0 (coordsX F z)
  have hbound (f : P →ᵇ ℂ) (z : X F) : ‖ext f z‖ ≤ ‖f‖ := by
    dsimp [ext, Function.extend]
    split_ifs
    · exact f.norm_coe_le_norm _
    · simpa using norm_nonneg f
  have hmem (f : P →ᵇ ℂ) : MemLp (ext f) 2 μ := by
    have hsm : StronglyMeasurable
        (Function.extend (Subtype.val : P → Coord F) f 0) :=
      (MeasurableEmbedding.subtype_coe hP.measurableSet).stronglyMeasurable_extend
        f.continuous.stronglyMeasurable stronglyMeasurable_const
    exact MemLp.of_bound
      (hsm.comp_measurable specCoordsX_continuous.measurable).aestronglyMeasurable
      ‖f‖ (Eventually.of_forall (hbound f))
  let L : (P →ᵇ ℂ) →ₗ[ℂ] Lp ℂ 2 μ := {
    toFun := fun f => (hmem f).toLp (ext f)
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [(hmem (f + g)).coeFn_toLp, (hmem f).coeFn_toLp,
        (hmem g).coeFn_toLp, Lp.coeFn_add ((hmem f).toLp (ext f))
          ((hmem g).toLp (ext g))] with z hfg hf hg hadd
      rw [hfg, hadd, Pi.add_apply, hf, hg]
      dsimp [ext, Function.extend]
      split_ifs <;> simp
    map_smul' := by
      intro a f
      apply Lp.ext
      filter_upwards [(hmem (a • f)).coeFn_toLp, (hmem f).coeFn_toLp,
        Lp.coeFn_smul a ((hmem f).toLp (ext f))] with z haf hf hsmul
      simp only [RingHom.id_apply]
      rw [haf, hsmul, Pi.smul_apply, hf]
      dsimp [ext, Function.extend]
      split_ifs <;> simp }
  have hnorm (f : P →ᵇ ℂ) :
      ‖L f‖ ≤ (measureUnivNNReal μ : ℝ) ^ (2 : ENNReal).toReal⁻¹ * ‖f‖ := by
    apply Lp.norm_le_of_ae_bound (norm_nonneg f)
    filter_upwards [(hmem f).coeFn_toLp] with z hz
    change ‖(hmem f).toLp (ext f) z‖ ≤ ‖f‖
    rw [hz]
    exact hbound f z
  let T : (P →ᵇ ℂ) →L[ℂ] Lp ℂ 2 μ :=
    L.mkContinuous ((measureUnivNNReal μ : ℝ) ^ (2 : ENNReal).toReal⁻¹) hnorm
  refine ⟨T, ?_⟩
  intro f
  filter_upwards [(hmem f).coeFn_toLp] with z hz
  intro hzK
  change (hmem f).toLp (ext f) z = _
  rw [hz]
  exact Subtype.coe_injective.extend_apply f 0
    ⟨coordsX F z, Set.mem_image_of_mem (coordsX F) hzK⟩

/-- The unsmoothed base identity and the smoothed convergence identity extend to
the whole supplied continuation domain in L² on every compact subset of X. -/
theorem s3_unsmoothed_identity (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (τ : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (hτ : IsCuspCutoff A τ) (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (u : ℂ → L2Space F D) (s₁ ε : ℝ)
    (hs₀ : 0 < s₁) (hs₁ : s₁ < 4) (hε : 0 < ε)
    (hu : AnalyticOnNhd ℂ u (contDomain s₁ ε))
    (hbase : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ᵐ z ∂(volX F),
      eisSeed F Γ σ τ s z + l2Lift F Γ D (u s) z = eisSeries F Γ σ s z)
    (hseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ z,
      smoothingOperator F k₀
        (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) z =
      radialTransform F k₀ (1 + 2 * s) * eisSeries F Γ σ s z) :
    ∀ s ∈ contDomain s₁ ε, ∀ K : Set (X F), IsCompact K →
      ∀ᵐ z ∂(volX F), z ∈ K →
        smoothingOperator F k₀
          (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) z =
        radialTransform F k₀ (1 + 2 * s) *
          (eisSeed F Γ σ τ s z + l2Lift F Γ D (u s) z) := by
  intro s hs K hK
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchartX⟩ := G1_h3_basics (F := F)
  obtain ⟨eChartX, _, _⟩ := hchartX
  letI : T2Space (X F) := eChartX.t2Space
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  let P : Set (Coord F) := coordsX F '' K
  have hP : IsCompact P := hK.image specCoordsX_continuous
  have hPpos : P ⊆ posSet F := by
    rintro p ⟨z, hz, rfl⟩
    exact specCoordsX_mem_pos z
  obtain ⟨J, hJ⟩ := compactCoordinateToLp K hK
  obtain ⟨L, _, hL⟩ := localLiftCLM Γ D hD K hK
  have hseedData := specSeed_smooth_analytic Γ D hD σ A hA hsep τ hτ
  obtain ⟨Φseed, hΦseed, hΦseedval⟩ := hseedData.2 P hP hPpos 0 Fin.elim0
  obtain ⟨Φsm, Tsm, hΦsm, _, _, hAdd⟩ :=
    smoothingSeedLift_derivative_data Γ D hD σ τ A hA hsep hτ k₀ hkSmooth hkSupport
      P hP hPpos 0 Fin.elim0
  let Hleft : ℂ → Lp ℂ 2 ((volX F).restrict K) := fun t => J (Φsm t + Tsm (u t))
  let Hraw : ℂ → Lp ℂ 2 ((volX F).restrict K) := fun t => J (Φseed t) + L (u t)
  let R : ℂ → ℂ := fun t => radialTransform F k₀ (1 + 2 * t)
  let Hright : ℂ → Lp ℂ 2 ((volX F).restrict K) := fun t => R t • Hraw t
  have hleft : AnalyticOnNhd ℂ Hleft (contDomain s₁ ε) :=
    J.comp_analyticOnNhd ((hΦsm.mono (Set.subset_univ _)).add
      (Tsm.comp_analyticOnNhd hu))
  have hraw : AnalyticOnNhd ℂ Hraw (contDomain s₁ ε) :=
    (J.comp_analyticOnNhd (hΦseed.mono (Set.subset_univ _))).add
      (L.comp_analyticOnNhd hu)
  have hright : AnalyticOnNhd ℂ Hright (contDomain s₁ ε) :=
    ((radialTransformParam_analytic k₀ hkSmooth hkSupport).mono
      (Set.subset_univ _)).smul hraw
  have hleftVal (t : ℂ) : ∀ᵐ z ∂((volX F).restrict K), Hleft t z =
      smoothingOperator F k₀
        (fun w => eisSeed F Γ σ τ t w + l2Lift F Γ D (u t) w) z := by
    filter_upwards [hJ (Φsm t + Tsm (u t)), ae_restrict_mem hK.measurableSet]
      with z hz hzK
    change J (Φsm t + Tsm (u t)) z = _
    rw [hz hzK]
    simpa only [iteratedFDeriv_zero_apply, specPtX_coordsX,
      BoundedContinuousFunction.add_apply] using
      (hAdd t (u t) ⟨coordsX F z, Set.mem_image_of_mem (coordsX F) hzK⟩).symm
  have hrawVal (t : ℂ) : ∀ᵐ z ∂((volX F).restrict K), Hraw t z =
      eisSeed F Γ σ τ t z + l2Lift F Γ D (u t) z := by
    filter_upwards [hJ (Φseed t), hL (u t),
      Lp.coeFn_add (J (Φseed t)) (L (u t)), ae_restrict_mem hK.measurableSet]
      with z hzSeed hzLift hzAdd hzK
    change (J (Φseed t) + L (u t)) z = _
    rw [hzAdd, Pi.add_apply, hzSeed hzK, hzLift]
    congr 1
    simpa only [iteratedFDeriv_zero_apply, specPtX_coordsX] using
      hΦseedval t ⟨coordsX F z, Set.mem_image_of_mem (coordsX F) hzK⟩
  have hrightVal (t : ℂ) : ∀ᵐ z ∂((volX F).restrict K), Hright t z =
      R t * (eisSeed F Γ σ τ t z + l2Lift F Γ D (u t) z) := by
    filter_upwards [Lp.coeFn_smul (R t) (Hraw t), hrawVal t] with z hzSmul hzRaw
    change (R t • Hraw t) z = _
    rw [hzSmul, Pi.smul_apply, hzRaw]
    rfl
  have hbaseEq : Hleft =ᶠ[𝓝 (5 / 2 : ℂ)] Hright := by
    filter_upwards [Metric.ball_mem_nhds (5 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)]
      with t ht
    apply Lp.ext
    filter_upwards [hleftVal t, hrightVal t, (hbase t ht).filter_mono ae_restrict_le]
      with z hzLeft hzRight hzBase
    rw [hzLeft, hzRight, hzBase]
    exact hseries t ht z
  have hcenter : (5 / 2 : ℂ) ∈ contDomain s₁ ε :=
    Or.inl (Or.inr (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))
  have hEq := hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (C1_domain s₁ ε hs₀ hs₁ hε).2 hcenter hbaseEq
  have hvalues : Hleft s = Hright s := hEq hs
  apply (ae_restrict_iff' hK.measurableSet).mp
  filter_upwards [hleftVal s, hrightVal s] with z hzLeft hzRight
  exact hzLeft.symm.trans ((congrArg
    (fun f : Lp ℂ 2 ((volX F).restrict K) => f z) hvalues).trans hzRight)

private theorem continuationX_sigmaCompact : SigmaCompactSpace (X F) := by
  have hposOpen : IsOpen (posSet F) := by
    rw [posSet, Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro w
    have hc : Continuous (fun p : Coord F => (p w).2) := by fun_prop
    exact isOpen_Ioi.preimage hc
  letI : LocallyCompactSpace {p : Coord F // p ∈ posSet F} :=
    hposOpen.locallyCompactSpace
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchartX⟩ := G1_h3_basics (F := F)
  obtain ⟨eChartX, _, _⟩ := hchartX
  letI : LocallyCompactSpace (X F) := eChartX.symm.isOpenEmbedding.locallyCompactSpace
  letI : SecondCountableTopology (X F) := eChartX.symm.isEmbedding.secondCountableTopology
  exact inferInstance

/-- The local L² identity identifies the smoothed residue with the original invariant lift.
The Laurent numerator is evaluated at the center only after taking a limit in local L². -/
theorem s3_residue_ae_lift (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (τ : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (hτ : IsCuspCutoff A τ) (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (u : ℂ → L2Space F D) (θ : L2Space F D) (s₁ ε : ℝ) (hε : 0 < ε)
    (hhatCenter : radialTransform F k₀ (1 + 2 * (s₁ : ℂ)) ≠ 0)
    (hres : ∃ Ψ : ℂ → L2Space F D,
      AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) ∧ Ψ (s₁ : ℂ) = θ ∧
        ∀ s ∈ Metric.ball (s₁ : ℂ) ε, s ≠ s₁ → Ψ s = (s - s₁) • u s)
    (hidentity : ∀ s ∈ contDomain s₁ ε, ∀ K : Set (X F), IsCompact K →
      ∀ᵐ z ∂(volX F), z ∈ K →
        smoothingOperator F k₀
          (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) z =
        radialTransform F k₀ (1 + 2 * s) *
          (eisSeed F Γ σ τ s z + l2Lift F Γ D (u s) z)) :
    ∀ᵐ z ∂(volX F),
      (radialTransform F k₀ (1 + 2 * (s₁ : ℂ)))⁻¹ *
        smoothingOperator F k₀ (l2Lift F Γ D θ) z = l2Lift F Γ D θ z := by
  obtain ⟨Ψu, hΨu, hΨuCenter, hΨurel⟩ := hres
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchartX⟩ := G1_h3_basics (F := F)
  obtain ⟨eChartX, _, _⟩ := hchartX
  letI : T2Space (X F) := eChartX.t2Space
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  let c : ℂ := s₁
  let B : Set ℂ := Metric.ball c ε
  have hcB : c ∈ B := Metric.mem_ball_self hε
  have hseedData := specSeed_smooth_analytic Γ D hD σ A hA hsep τ hτ
  have hlocal (K : Set (X F)) (hK : IsCompact K) : ∀ᵐ z ∂(volX F), z ∈ K →
      (radialTransform F k₀ (1 + 2 * c))⁻¹ *
        smoothingOperator F k₀ (l2Lift F Γ D θ) z = l2Lift F Γ D θ z := by
    let P : Set (Coord F) := coordsX F '' K
    have hP : IsCompact P := hK.image specCoordsX_continuous
    have hPpos : P ⊆ posSet F := by
      rintro p ⟨z, hz, rfl⟩
      exact specCoordsX_mem_pos z
    obtain ⟨J, hJ⟩ := compactCoordinateToLp K hK
    obtain ⟨L, _, hL⟩ := localLiftCLM Γ D hD K hK
    obtain ⟨Φseed, hΦseed, hΦseedval⟩ := hseedData.2 P hP hPpos 0 Fin.elim0
    obtain ⟨Φsm, Tsm, hΦsm, _, hTsm, hAdd⟩ :=
      smoothingSeedLift_derivative_data Γ D hD σ τ A hA hsep hτ k₀ hkSmooth hkSupport
        P hP hPpos 0 Fin.elim0
    let S : L2Space F D →L[ℂ] Lp ℂ 2 ((volX F).restrict K) := J.comp Tsm
    let Hsm : ℂ → Lp ℂ 2 ((volX F).restrict K) := fun t => J (Φsm t + Tsm (u t))
    let Hraw : ℂ → Lp ℂ 2 ((volX F).restrict K) := fun t => J (Φseed t) + L (u t)
    let R : ℂ → ℂ := fun t => radialTransform F k₀ (1 + 2 * t)
    have hsmVal (t : ℂ) : ∀ᵐ z ∂((volX F).restrict K), Hsm t z =
        smoothingOperator F k₀
          (fun w => eisSeed F Γ σ τ t w + l2Lift F Γ D (u t) w) z := by
      filter_upwards [hJ (Φsm t + Tsm (u t)), ae_restrict_mem hK.measurableSet]
        with z hz hzK
      change J (Φsm t + Tsm (u t)) z = _
      rw [hz hzK]
      simpa only [iteratedFDeriv_zero_apply, specPtX_coordsX,
        BoundedContinuousFunction.add_apply] using
        (hAdd t (u t) ⟨coordsX F z, Set.mem_image_of_mem (coordsX F) hzK⟩).symm
    have hrawVal (t : ℂ) : ∀ᵐ z ∂((volX F).restrict K), Hraw t z =
        eisSeed F Γ σ τ t z + l2Lift F Γ D (u t) z := by
      filter_upwards [hJ (Φseed t), hL (u t),
        Lp.coeFn_add (J (Φseed t)) (L (u t)), ae_restrict_mem hK.measurableSet]
        with z hzSeed hzLift hzAdd hzK
      change (J (Φseed t) + L (u t)) z = _
      rw [hzAdd, Pi.add_apply, hzSeed hzK, hzLift]
      congr 1
      simpa only [iteratedFDeriv_zero_apply, specPtX_coordsX] using
        hΦseedval t ⟨coordsX F z, Set.mem_image_of_mem (coordsX F) hzK⟩
    have hIdLp (t : ℂ) (ht : t ∈ contDomain s₁ ε) : Hsm t = R t • Hraw t := by
      apply Lp.ext
      filter_upwards [hsmVal t, hrawVal t, Lp.coeFn_smul (R t) (Hraw t),
        (ae_restrict_iff' hK.measurableSet).mpr (hidentity t ht K hK)]
        with z hzSm hzRaw hzCo hzId
      rw [hzSm, hzCo, Pi.smul_apply, hzRaw]
      simpa only [R, smul_eq_mul] using hzId
    let Nleft : ℂ → Lp ℂ 2 ((volX F).restrict K) := fun t =>
      (t - c) • J (Φsm t) + S (Ψu t)
    let Nright : ℂ → Lp ℂ 2 ((volX F).restrict K) := fun t =>
      R t • ((t - c) • J (Φseed t) + L (Ψu t))
    have hδ : AnalyticOnNhd ℂ (fun t : ℂ => t - c) B := by fun_prop
    have hNleft : AnalyticOnNhd ℂ Nleft B :=
      (hδ.smul (J.comp_analyticOnNhd (hΦsm.mono (Set.subset_univ _)))).add
        (S.comp_analyticOnNhd hΨu)
    have hNright : AnalyticOnNhd ℂ Nright B :=
      ((radialTransformParam_analytic k₀ hkSmooth hkSupport).mono
        (Set.subset_univ _)).smul
          ((hδ.smul (J.comp_analyticOnNhd (hΦseed.mono (Set.subset_univ _)))).add
            (L.comp_analyticOnNhd hΨu))
    have hpuncture : Nleft =ᶠ[𝓝[≠] c] Nright := by
      filter_upwards [show B ∈ 𝓝[≠] c from
        nhdsWithin_le_nhds (Metric.ball_mem_nhds c hε),
        self_mem_nhdsWithin] with t ht htne
      have htne' : t ≠ c := by simpa using htne
      have hdom : t ∈ contDomain s₁ ε := Or.inr ⟨ht, by simpa [c] using htne'⟩
      have hleftScale : Nleft t = (t - c) • Hsm t := by
        dsimp [Nleft, Hsm, S, c]
        rw [hΨurel t ht htne']
        simp only [map_smul, map_add, smul_add]
      have hrightScale : Nright t = (t - c) • (R t • Hraw t) := by
        dsimp [Nright, Hraw, c]
        rw [hΨurel t ht htne']
        simp only [map_smul, smul_add, smul_smul, mul_comm (R t) (t - (s₁ : ℂ))]
      rw [hleftScale, hrightScale, hIdLp t hdom]
    have hleftLim : Tendsto Nleft (𝓝[≠] c) (𝓝 (Nleft c)) :=
      (hNleft c hcB).continuousAt.mono_left nhdsWithin_le_nhds
    have hrightLim : Tendsto Nright (𝓝[≠] c) (𝓝 (Nright c)) :=
      (hNright c hcB).continuousAt.mono_left nhdsWithin_le_nhds
    have hcenterEq : S θ = R c • L θ := by
      have heq := tendsto_nhds_unique_of_eventuallyEq hleftLim hrightLim hpuncture
      simpa only [Nleft, Nright, c, hΨuCenter, sub_self, zero_smul, zero_add] using heq
    have hSval : ∀ᵐ z ∂((volX F).restrict K), S θ z =
        smoothingOperator F k₀ (l2Lift F Γ D θ) z := by
      filter_upwards [hJ (Tsm θ), ae_restrict_mem hK.measurableSet] with z hz hzK
      change J (Tsm θ) z = _
      rw [hz hzK]
      simpa only [iteratedFDeriv_zero_apply, specPtX_coordsX] using
        hTsm θ ⟨coordsX F z, Set.mem_image_of_mem (coordsX F) hzK⟩
    apply (ae_restrict_iff' hK.measurableSet).mp
    filter_upwards [hSval, hL θ, Lp.coeFn_smul (R c) (L θ)] with z hzS hzL hzCo
    have heq := congrArg (fun f : Lp ℂ 2 ((volX F).restrict K) => f z) hcenterEq
    rw [hzS, hzCo, Pi.smul_apply, hzL, smul_eq_mul] at heq
    change (R c)⁻¹ * smoothingOperator F k₀ (l2Lift F Γ D θ) z = _
    rw [heq, ← mul_assoc, inv_mul_cancel₀ hhatCenter, one_mul]
  letI : SigmaCompactSpace (X F) := continuationX_sigmaCompact
  obtain ⟨K, hK, hcover⟩ := SigmaCompactSpace.exists_compact_covering (X := X F)
  have hcount : ∀ᵐ z ∂(volX F), ∀ n : ℕ, z ∈ K n →
      (radialTransform F k₀ (1 + 2 * c))⁻¹ *
        smoothingOperator F k₀ (l2Lift F Γ D θ) z = l2Lift F Γ D θ z := by
    rw [eventually_countable_forall]
    exact fun n => hlocal (K n) (hK n)
  filter_upwards [hcount] with z hz
  have hzin : z ∈ ⋃ n, K n := by rw [hcover]; exact Set.mem_univ _
  obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp hzin
  exact hz n hzn

/-- An invariant representative equal a.e. to a quotient L² lift is square integrable
on every fundamental domain. -/
theorem residue_sq_of_ae_lift (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (θ : L2Space F D) (r : X F → ℂ)
    (hrInv : IsGammaInvariant F Γ r) (hrEq : r =ᵐ[volX F] l2Lift F Γ D θ) :
    ∀ D' : Set (X F), IsFundamentalDomain Γ D' (volX F) →
      IntegrableOn (fun z => ‖r z‖ ^ 2) D' (volX F) := by
  letI : Countable Γ := localLift_countableGamma Γ
  letI : MeasurableConstSMul Γ (X F) :=
    ⟨fun γ => (localLift_action_measurePreserving Γ γ).measurable⟩
  letI : SMulInvariantMeasure Γ (X F) (volX F) :=
    ⟨fun γ s hs => (localLift_action_measurePreserving Γ γ).measure_preimage
      hs.nullMeasurableSet⟩
  have hDval : r =ᵐ[(volX F).restrict D] (θ : X F → ℂ) :=
    (hrEq.filter_mono ae_restrict_le).trans (localLift_eq_on_D Γ D hD θ)
  have hθsq : Integrable (fun z => ‖θ z‖ ^ 2) ((volX F).restrict D) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable θ)).mp (Lp.memLp θ)
  have hSqD : IntegrableOn (fun z => ‖r z‖ ^ 2) D (volX F) :=
    hθsq.congr (hDval.symm.mono fun z hz => congrArg (fun a : ℂ => ‖a‖ ^ 2) hz)
  intro D' hD'
  apply (hD.integrableOn_iff hD' ?_).mp hSqD
  intro γ z
  exact congrArg (fun a : ℂ => ‖a‖ ^ 2) (hrInv γ γ.property z)

end ArtinPrimitiveRoots.Proofs.spec_cont_sol
