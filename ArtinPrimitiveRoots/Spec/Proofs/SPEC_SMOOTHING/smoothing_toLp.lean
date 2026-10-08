import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.smoothing_uniform_eval_bound
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.smoothing_smooth_representative

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction ENNReal

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Transport the bounded continuous value map to L2 of the compact image in X, retaining its
representative. Guide: `sol-thin-spec/PROOFS.md:409`. Uses `smoothing_uniform_eval_bound`
at order zero, `smoothing_smooth_representative`, and frozen `G1_h3_basics`, `G3_volume`.
Supplies the compact Lp conjunct of frozen `S1_smoothing`. -/
theorem smoothing_toLp (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F) :
    ∃ T : L2Space F D →L[ℂ] Lp ℂ 2 ((volX F).restrict (ptX F '' K)),
      ∀ u, ∀ᵐ z ∂(volX F), z ∈ ptX F '' K →
        T u z = smoothingOperator F k₀ (l2Lift F Γ D u) z := by
  classical
  by_cases hKempty : K = ∅
  · refine ⟨0, ?_⟩
    intro u
    filter_upwards [] with z hz
    simp [hKempty] at hz
  · rcases G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, hcoords, hpt, _, _, _, ⟨chart, hchart, hchartinv⟩⟩
    have hsecondX : SecondCountableTopology (X F) := chart.symm.secondCountableTopology
    have hT2X : T2Space (X F) := chart.t2Space
    have hsecondH3 : SecondCountableTopology H3 := by
      letI : SecondCountableTopology (X F) := hsecondX
      let w₀ : InfinitePlace F := Classical.choice inferInstance
      let c : H3 → X F := fun z _ => z
      let eval : X F → H3 := fun z => z w₀
      have hc : Continuous c := by
        change Continuous (fun z : H3 => fun _ : InfinitePlace F => z)
        exact continuous_pi fun _ => continuous_id
      have heval : Continuous eval := continuous_apply w₀
      have hleft : Function.LeftInverse eval c := by
        intro z
        simp [eval, c]
      exact hleft.isEmbedding heval hc |>.secondCountableTopology
    letI : SecondCountableTopology H3 := hsecondH3
    letI : BorelSpace H3 := ⟨rfl⟩
    letI : Countable (InfinitePlace F) := Finite.to_countable
    letI : BorelSpace (X F) := by
      change BorelSpace (∀ w : InfinitePlace F, H3)
      exact Pi.borelSpace
    letI : T2Space (X F) := hT2X
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hκpos (p : K) : p.val ∈ posSet F := hKpos p.property
    let κ : K → {p : Coord F // p ∈ posSet F} := fun p => ⟨p.val, hκpos p⟩
    have hκ : Continuous κ := by
      apply continuous_induced_rng.2
      exact continuous_subtype_val
    have hptMap : Continuous (fun p : K => ptX F p.val) := by
      have hfun : (fun p : K => ptX F p.val) = (fun p => chart (κ p)) := by
        funext p
        exact (hchart (κ p)).symm
      rw [hfun]
      exact chart.continuous.comp hκ
    let S : Set (X F) := ptX F '' K
    have hScompact : IsCompact S := by
      have himage : (fun p : K => ptX F p.val) '' Set.univ = S := by
        ext z
        simp [S]
      rw [← himage]
      exact isCompact_univ.image hptMap
    have hSmeas : MeasurableSet S := hScompact.isClosed.measurableSet
    have hSvol : (volX F) S < ⊤ := (G3_volume (F := F)).2.2.1 S hScompact
    have hSnonempty : S.Nonempty := by
      obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hKempty
      exact ⟨ptX F p, ⟨p, hp, rfl⟩⟩
    letI : BorelSpace S := inferInstance
    letI : SecondCountableTopology S := inferInstance
    have hcoordsContinuous : Continuous (coordsX F) := by
      have hfun : (fun z : X F => (chart.symm z).val) = coordsX F := funext hchartinv
      rw [← hfun]
      exact continuous_subtype_val.comp chart.symm.continuous
    have hcoordInK (z : S) : coordsX F z.val ∈ K := by
      obtain ⟨p, hp, hpz⟩ := z.property
      have hcoord : coordsX F z.val = p :=
        (congrArg (coordsX F) hpz.symm).trans (hcoords p (hKpos hp))
      rw [hcoord]
      exact hp
    let c : S → K := fun z => ⟨coordsX F z.val, hcoordInK z⟩
    have hc : Continuous c := by
      apply continuous_induced_rng.2
      exact hcoordsContinuous.comp continuous_subtype_val
    let cMap : C(S, K) := ⟨c, hc⟩
    obtain ⟨W, C, T₀, hW, hC, hbound, hT₀⟩ :=
      smoothing_uniform_eval_bound (F := F) Γ D hD k₀ hkSmooth hkSupport K hK hKpos
        0 (fun i => Fin.elim0 i)
    let cCLM : (K →ᵇ ℂ) →L[ℂ] (S →ᵇ ℂ) :=
      BoundedContinuousFunction.compContinuousCLM ℂ ℂ cMap
    let B : L2Space F D →L[ℂ] (S →ᵇ ℂ) := cCLM.comp T₀
    have hBpoint (u : L2Space F D) (z : S) : B u z =
        smoothingOperator F k₀ (l2Lift F Γ D u) z.val := by
      obtain ⟨p, hp, hpz⟩ := z.property
      have hcval : c z = ⟨p, hp⟩ := by
        apply Subtype.ext
        dsimp [c]
        change coordsX F z.val = p
        exact (congrArg (coordsX F) hpz.symm).trans (hcoords p (hKpos hp))
      calc
        B u z = T₀ u (c z) := by simp [B, cCLM, cMap]
        _ = T₀ u ⟨p, hp⟩ := by rw [hcval]
        _ = smoothingOperator F k₀ (l2Lift F Γ D u) (ptX F p) := by
          simpa [iteratedFDeriv_zero_apply] using hT₀ u ⟨p, hp⟩
        _ = smoothingOperator F k₀ (l2Lift F Γ D u) z.val := by rw [hpz]
    let μ : Measure (X F) := (volX F).restrict S
    let s₀ : S := ⟨Classical.choose hSnonempty, Classical.choose_spec hSnonempty⟩
    let r : X F → S := fun z => if hz : z ∈ S then ⟨z, hz⟩ else s₀
    have hrmeas : Measurable r := by
      simpa [r, s₀] using
        (Measurable.dite (s := S) measurable_id measurable_const hSmeas)
    have hμfinite : IsFiniteMeasure μ := by
      refine ⟨?_⟩
      dsimp [μ]
      simpa using hSvol
    let μS : Measure S := Measure.map r μ
    have hμSuniv : μS Set.univ < ⊤ := by
      change (Measure.map r μ) Set.univ < ⊤
      rw [Measure.map_apply hrmeas MeasurableSet.univ]
      simpa using hμfinite.measure_univ_lt_top
    letI : IsFiniteMeasure μS := ⟨hμSuniv⟩
    letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    have hrpres : MeasurePreserving r μ μS := ⟨hrmeas, rfl⟩
    let toLpS : (S →ᵇ ℂ) →L[ℂ] Lp ℂ 2 μS :=
      BoundedContinuousFunction.toLp (E := ℂ) 2 μS ℂ
    let pull : Lp ℂ 2 μS →L[ℂ] Lp ℂ 2 μ :=
      (Lp.compMeasurePreservingₗᵢ ℂ r hrpres).toContinuousLinearMap
    let T : L2Space F D →L[ℂ] Lp ℂ 2 μ := pull.comp (toLpS.comp B)
    refine ⟨T, ?_⟩
    intro u
    have hLpS : toLpS (B u) =ᵐ[μS] B u := by
      simpa [toLpS] using
        (BoundedContinuousFunction.coeFn_toLp (α := S) (E := ℂ) (p := (2 : ℝ≥0∞))
          (μ := μS) (𝕜 := ℂ) (B u))
    have hEqMeas : MeasurableSet {y : S | toLpS (B u) y = B u y} := by
      exact measurableSet_eq_fun (Lp.stronglyMeasurable (toLpS (B u))).measurable
        ((B u).continuous.measurable)
    have hLpScomp : (fun z => toLpS (B u) (r z)) =ᵐ[μ] (fun z => B u (r z)) := by
      exact (ae_map_iff hrmeas.aemeasurable hEqMeas).1 hLpS
    have hTrep : T u =ᵐ[μ] (fun z => B u (r z)) := by
      simpa [T, pull, toLpS] using
        (Lp.coeFn_compMeasurePreserving (toLpS (B u)) hrpres).trans hLpScomp
    have hfinal : ∀ᵐ z ∂μ, T u z =
        smoothingOperator F k₀ (l2Lift F Γ D u) z := by
      filter_upwards [hTrep, ae_restrict_mem hSmeas] with z hrep hz
      have hrz : r z = ⟨z, hz⟩ := by simp [r, hz]
      have hrep' : T u z = B u ⟨z, hz⟩ := by simpa [hrz] using hrep
      exact hrep'.trans (hBpoint u ⟨z, hz⟩)
    exact (ae_restrict_iff' hSmeas).1 hfinal

end ArtinPrimitiveRoots.A1.Spec
