import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.SmoothingSeedAnalytic
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.localLiftCLM
import ArtinPrimitiveRoots.Spec.Domain
import Mathlib.Analysis.Analytic.IsolatedZeros

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

end ArtinPrimitiveRoots.Proofs.spec_cont_sol
