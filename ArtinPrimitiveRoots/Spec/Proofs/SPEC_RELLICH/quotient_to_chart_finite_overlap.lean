import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff Pointwise ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private noncomputable def rellichGradientNormL2 {D : Set (X F)}
    (u : GradientL2Space F D) : L2Space F D :=
  Complex.ofRealCLM.compLpL 2 ((volX F).restrict D)
    ((Lp.memLp u).norm.toLp (fun z => ‖u z‖))

private theorem rellichGradientNormL2_ae {D : Set (X F)}
    (u : GradientL2Space F D) :
    ∀ᵐ z ∂((volX F).restrict D),
      rellichGradientNormL2 u z = (‖u z‖ : ℂ) := by
  let v : Lp ℝ 2 ((volX F).restrict D) :=
    (Lp.memLp u).norm.toLp (fun z => ‖u z‖)
  have hto : ∀ᵐ z ∂((volX F).restrict D), v z = ‖u z‖ :=
    MemLp.coeFn_toLp ((Lp.memLp u).norm)
  have hcomp := Complex.ofRealCLM.coeFn_compLpL v
  filter_upwards [hto, hcomp] with z hz₁ hz₂
  change (Complex.ofRealCLM.compLpL 2 ((volX F).restrict D) v) z = _
  rw [hz₂, hz₁]
  rfl

private theorem rellichGradientNormL2_norm_le {D : Set (X F)}
    (u : GradientL2Space F D) :
    ‖rellichGradientNormL2 u‖ ≤ ‖u‖ := by
  let v : Lp ℝ 2 ((volX F).restrict D) :=
    (Lp.memLp u).norm.toLp (fun z => ‖u z‖)
  have hnorm : ‖v‖ = ‖u‖ := by
    dsimp [v]
    rw [Lp.norm_toLp, Lp.norm_def]
    exact congrArg ENNReal.toReal
      (eLpNorm_norm (u : X F → GradientField F) (Lp.aestronglyMeasurable u))
  calc
    ‖Complex.ofRealCLM.compLpL 2 ((volX F).restrict D) v‖ ≤
        ‖Complex.ofRealCLM.compLpL 2 ((volX F).restrict D)‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖Complex.ofRealCLM‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.norm_compLpL_le Complex.ofRealCLM) (norm_nonneg _)
    _ = ‖u‖ := by rw [Complex.ofRealCLM_norm, one_mul, hnorm]

private theorem rellich_fullGradient_norm_sq (f : X F → ℂ) (z : X F) :
    ‖fullGradient F f z‖ ^ 2 = totalGradNormSq F f z := by
  simp [fullGradient, totalGradNormSq, placeGradNormSq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type, ← Complex.normSq_eq_norm_sq]

private theorem rellich_l2Lift_eq_of_rep
    (Γ : Subgroup SL(2,𝓞 F)) [Countable Γ]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (u : L2Space F D) (f : X F → ℂ)
    (hrep : ∀ᵐ z ∂(volX F), z ∈ D → u z = f z)
    (hmp : ∀ γ : Γ, MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F))
    (hliftInv : ∀ γ : Γ, ∀ z, l2Lift F Γ D u (γ • z) = l2Lift F Γ D u z)
    (hfInv : ∀ γ : Γ, ∀ z, f (γ • z) = f z) :
    l2Lift F Γ D u =ᵐ[volX F] f := by
  have huniq : ∀ᵐ z ∂(volX F), ∀ γ : Γ, z ∈ D → γ ≠ 1 → γ • z ∉ D := by
    rw [ae_all_iff]
    intro γ
    by_cases hγ : γ = 1
    · exact Filter.Eventually.of_forall fun z hDz hne => (hne hγ).elim
    · have hne : (1 : Γ) ≠ γ⁻¹ := by
        intro h
        exact hγ (by simpa using (congrArg Inv.inv h).symm)
      have hdis : AEDisjoint (volX F) ((1 : Γ) • D) (γ⁻¹ • D) :=
        hD.aedisjoint (i := 1) (j := γ⁻¹) hne
      have hnot : ∀ᵐ z ∂(volX F), z ∉ D ∨ z ∉ (γ⁻¹ : Γ) • D := by
        rw [ae_iff]
        simpa [one_smul] using hdis.eq
      exact hnot.mono fun z hz hDz _ hγz => by
        have hm : z ∈ (γ⁻¹ : Γ) • D := by
          rw [Set.mem_smul_set_iff_inv_smul_mem]
          simpa using hγz
        rcases hz with hz | hz
        · exact hz hDz
        · exact hz hm
  have hLiftD : ∀ᵐ z ∂(volX F), z ∈ D → l2Lift F Γ D u z = u z := by
    exact huniq.mono fun z hz hDz => by
      classical
      change (∑' γ : Γ,
        if (γ : SL(2,𝓞 F)) • z ∈ D then u ((γ : SL(2,𝓞 F)) • z) else 0) = u z
      rw [tsum_eq_single (1 : Γ)]
      · simp [hDz]
      · intro γ hγ
        have hnot : (γ : SL(2,𝓞 F)) • z ∉ D := hz γ hDz hγ
        simp [hnot]
  have hEqD : ∀ᵐ z ∂(volX F), z ∈ D → l2Lift F Γ D u z = f z := by
    filter_upwards [hLiftD, hrep] with z hz₁ hz₂ hDz
    exact (hz₁ hDz).trans (hz₂ hDz)
  have hbad : volX F {z | z ∈ D ∧ l2Lift F Γ D u z ≠ f z} = 0 := by
    have hgood : ∀ᵐ z ∂(volX F), ¬ (z ∈ D ∧ l2Lift F Γ D u z ≠ f z) := by
      filter_upwards [hEqD] with z hz
      intro hbad
      exact hbad.2 (hz hbad.1)
    simpa only [ae_iff, Classical.not_not] using hgood
  have hnotBad : ∀ᵐ z ∂(volX F), ∀ γ : Γ,
      γ • z ∉ {x | x ∈ D ∧ l2Lift F Γ D u x ≠ f x} := by
    rw [ae_all_iff]
    intro γ
    have hnull := (hmp γ).quasiMeasurePreserving.preimage_null hbad
    simpa only [measure_eq_zero_iff_ae_notMem, Set.mem_preimage] using hnull
  filter_upwards [hD.ae_covers, hnotBad] with z hzcover hzbad
  obtain ⟨γ, hγD⟩ := hzcover
  have heq : l2Lift F Γ D u (γ • z) = f (γ • z) := by
    by_contra hne
    exact hzbad γ ⟨hγD, hne⟩
  calc
    l2Lift F Γ D u z = l2Lift F Γ D u (γ • z) := (hliftInv γ z).symm
    _ = f (γ • z) := heq
    _ = f z := hfInv γ z

private theorem rellich_l2Lift_invariant
    (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (u : L2Space F D) (γ : Γ) (z : X F) :
    l2Lift F Γ D u (γ • z) = l2Lift F Γ D u z := by
  classical
  change (∑' δ : Γ,
      if (δ : SL(2,𝓞 F)) • ((γ : SL(2,𝓞 F)) • z) ∈ D then
        u ((δ : SL(2,𝓞 F)) • ((γ : SL(2,𝓞 F)) • z)) else 0) =
    ∑' δ : Γ, if (δ : SL(2,𝓞 F)) • z ∈ D then
      u ((δ : SL(2,𝓞 F)) • z) else 0
  simpa [l2Lift, mul_smul] using
    (Equiv.mulRight γ).tsum_eq
      (fun δ : Γ => if (δ : SL(2,𝓞 F)) • z ∈ D then
        u ((δ : SL(2,𝓞 F)) • z) else 0)

/-- Local mass and gradient energy are controlled by calibrated quotient energy.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:319. Uses the compact-overlap conjunct
of T1_l2 (passed as hOverlap), G3_volume, G4_energy and the T2 test characterization.
No freeness or finiteness assertion about translates meeting an unbounded D is used. -/
theorem quotient_to_chart_finite_overlap
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (htests : ∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f)
    (hOverlap : RellichOverlapControl Γ D) :
    RellichLocalEnergyBound Γ D E e := by
  classical
  have hCountF : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable F := hCountF
  letI : Countable (𝓞 F) :=
    Function.Injective.countable (f := fun x : 𝓞 F => (x : F)) Subtype.val_injective
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
    let toPairs : Matrix (Fin 2) (Fin 2) (𝓞 F) →
        ((𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F)) :=
      fun A => ((A 0 0, A 0 1), (A 1 0, A 1 1))
    have hInjective : Function.Injective toPairs := by
      intro A B h
      have h00 : A 0 0 = B 0 0 := congrArg (fun t : (𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F) => t.1.1) h
      have h01 : A 0 1 = B 0 1 := congrArg (fun t : (𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F) => t.1.2) h
      have h10 : A 1 0 = B 1 0 := congrArg (fun t : (𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F) => t.2.1) h
      have h11 : A 1 1 = B 1 1 := congrArg (fun t : (𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F) => t.2.2) h
      ext i j
      fin_cases i <;> fin_cases j <;> first
        | exact_mod_cast h00
        | exact_mod_cast h01
        | exact_mod_cast h10
        | exact_mod_cast h11
    exact Function.Injective.countable hInjective
  letI : Countable (SL(2,𝓞 F)) :=
    Function.Injective.countable
      (f := fun x : SL(2,𝓞 F) => (x : Matrix (Fin 2) (Fin 2) (𝓞 F)))
      Subtype.val_injective
  letI : Countable Γ :=
    Function.Injective.countable (f := fun x : Γ => (x : SL(2,𝓞 F)))
      Subtype.val_injective
  have hG3 := G3_volume (F := F)
  haveI : BorelSpace H3 := ⟨rfl⟩
  haveI : SecondCountableTopology (Fin 2 → Fin 2 → ℂ) := inferInstance
  have hCountMatrix2 : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := hCountMatrix2
  have hCountSL2C : SecondCountableTopology (SL(2,ℂ)) := by
    apply (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ))).secondCountableTopology
  haveI : SecondCountableTopology (SL(2,ℂ)) := hCountSL2C
  letI : ContinuousMul (SL(2,ℂ)) := ⟨by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)⟩
  have hCountH3 : SecondCountableTopology H3 := by
    letI : SecondCountableTopology (SL(2,ℂ)) := hCountSL2C
    exact Topology.IsOpenQuotientMap.secondCountableTopology
      (QuotientGroup.isOpenQuotientMap_mk (N := SU2))
  haveI : SecondCountableTopology H3 := hCountH3
  haveI : OpensMeasurableSpace H3 := inferInstance
  haveI : BorelSpace (X F) := inferInstance
  haveI : OpensMeasurableSpace (X F) := inferInstance
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, hcoordPt, _, _, _, _, ⟨chartEquiv, hchartEquiv, _⟩⟩
  haveI : OpensMeasurableSpace (X F) := inferInstance
  haveI : T2Space (X F) := chartEquiv.t2Space
  letI : IsFiniteMeasureOnCompacts (volX F) :=
    ⟨fun K hK => hG3.2.2.1 K hK⟩
  have hmp : ∀ γ : Γ,
      MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F) := by
    intro γ
    let g : InfinitePlace F → SL(2,ℂ) :=
      fun w => toInf F (toSLF F (γ : SL(2,𝓞 F))) w
    obtain ⟨a, ha, _⟩ := (G2_x_action (F := F)).2.2.2.1 g
    have hact (z : X F) : actAtPlaces F g z = (γ : SL(2,𝓞 F)) • z := rfl
    have hfun : (fun z : X F => (γ : SL(2,𝓞 F)) • z) = a := by
      funext z
      change actAtPlaces F g z = a z
      rw [← ha z]
    have hmeas : Measurable (fun z : X F => γ • z) := by
      have hcont : Continuous (fun z : X F => γ • z) := by
        change Continuous (fun z : X F => (γ : SL(2,𝓞 F)) • z)
        exact hfun ▸ a.continuous
      exact @Continuous.measurable (X F) (X F)
        (inferInstance : TopologicalSpace (X F))
        (inferInstance : MeasurableSpace (X F))
        (inferInstance : OpensMeasurableSpace (X F))
        (inferInstance : TopologicalSpace (X F))
        (inferInstance : MeasurableSpace (X F))
        (inferInstance : BorelSpace (X F))
        (fun z : X F => γ • z) hcont
    have hmeasure : Measure.map (fun z : X F => γ • z) (volX F) = volX F := by
      change Measure.map (fun z : X F => (γ : SL(2,𝓞 F)) • z) (volX F) = volX F
      simpa only [hact] using hG3.1 g
    exact ⟨hmeas, hmeasure⟩
  have hposOpen : IsOpen (posSet F) := by
    rw [show posSet F = ⋂ w : InfinitePlace F, {p : Coord F | 0 < (p w).2} by
      ext p
      simp [posSet]]
    exact isOpen_iInter_of_finite fun w => by
      have hcoord : Continuous (fun p : Coord F => (p w).2) := by fun_prop
      exact isOpen_Ioi.preimage hcoord
  intro S hS
  rcases hOverlap S hS with ⟨hfinite, hcontrol⟩
  let N : ℝ := (overlapMultiplicity F Γ S : ℝ)
  have hN : 0 ≤ N := by positivity
  have htestsS : ∀ f : testSubmodule F Γ, IsGammaTest F Γ (f : X F → ℂ) :=
    fun f => (htests (f : X F → ℂ)).1 f.property
  have hMassSmooth (f : testSubmodule F Γ) :
      IsSmoothX F (f : X F → ℂ) := (htestsS f).2.1
  have hfContinuous (f : testSubmodule F Γ) :
      Continuous (f : X F → ℂ) := by
    let P := {p : Coord F // p ∈ posSet F}
    have hchart : Continuous (fun p : P => (f : X F → ℂ) (ptX F p.1)) :=
      continuousOn_iff_continuous_domRestrict.mp (hMassSmooth f).continuousOn
    have hchartE : Continuous (fun p : P => (f : X F → ℂ) (chartEquiv p)) := by
      have heq : (fun p : P => (f : X F → ℂ) (chartEquiv p)) =
          fun p => (f : X F → ℂ) (ptX F p.1) := by
        funext p
        rw [hchartEquiv p]
      rw [heq]
      exact hchart
    have hrepr : (f : X F → ℂ) =
        (fun p : P => (f : X F → ℂ) (chartEquiv p)) ∘ chartEquiv.symm := by
      funext z
      simp [Function.comp_apply]
    rw [hrepr]
    exact hchartE.comp chartEquiv.symm.continuous
  have hgradContinuous (f : testSubmodule F Γ) :
      Continuous (fun z : X F => fullGradient F (f : X F → ℂ) z) := by
    let P := {p : Coord F // p ∈ posSet F}
    have hdf : ContinuousOn
        (fderiv ℝ ((f : X F → ℂ) ∘ ptX F)) (posSet F) :=
      (hMassSmooth f).continuousOn_fderiv_of_isOpen hposOpen (by simp)
    have hdfRestr : Continuous
        (fun p : P => fderiv ℝ ((f : X F → ℂ) ∘ ptX F) p.1) :=
      continuousOn_iff_continuous_domRestrict.mp hdf
    have hcoordFun : (fun p : P => coordsX F (chartEquiv p)) = Subtype.val := by
      funext p
      rw [hchartEquiv p]
      exact hcoordPt p.1 p.2
    have hgradPi : Continuous (fun p : P => fun wj : InfinitePlace F × Fin 3 =>
        placeGradient F wj.1 (f : X F → ℂ) (chartEquiv p) wj.2) := by
      apply continuous_pi
      intro wj
      rcases wj with ⟨w, j⟩
      change Continuous (fun p : P => placeGradient F w (f : X F → ℂ) (chartEquiv p) j)
      simp only [placeGradient]
      have hcoordAt (p : P) : coordsX F (chartEquiv p) = p.1 := congrFun hcoordFun p
      have hcoordEq : (fun p : P =>
          ((coordsX F (chartEquiv p) w).2 : ℂ) *
            fderiv ℝ ((f : X F → ℂ) ∘ ptX F) (coordsX F (chartEquiv p))
              (placeDirection F w j)) =
          (fun p : P => ((p.1 w).2 : ℂ) *
            fderiv ℝ ((f : X F → ℂ) ∘ ptX F) p.1 (placeDirection F w j)) := by
        funext p
        rw [hcoordAt p]
      change Continuous (fun p : P =>
          ((coordsX F (chartEquiv p) w).2 : ℂ) *
            fderiv ℝ ((f : X F → ℂ) ∘ ptX F) (coordsX F (chartEquiv p))
              (placeDirection F w j))
      rw [hcoordEq]
      have hy : Continuous (fun p : P => ((p.1 w).2 : ℂ)) :=
        Complex.continuous_ofReal.comp
          (continuous_snd.comp ((continuous_apply w).comp continuous_subtype_val))
      have hd : Continuous (fun p : P =>
          fderiv ℝ ((f : X F → ℂ) ∘ ptX F) p.1 (placeDirection F w j)) := by
        exact (ContinuousLinearMap.evalL ℝ (Coord F) ℂ (placeDirection F w j)).continuous.comp
          hdfRestr
      exact hy.mul hd
    have hgradChart : Continuous
        (fun p : P => fullGradient F (f : X F → ℂ) (chartEquiv p)) := by
      change Continuous (fun p : P => WithLp.toLp 2
        (fun wj : InfinitePlace F × Fin 3 =>
          placeGradient F wj.1 (f : X F → ℂ) (chartEquiv p) wj.2))
      exact (PiLp.continuous_toLp 2 (fun _ : InfinitePlace F × Fin 3 => ℂ)).comp hgradPi
    have hrepr : (fun z : X F => fullGradient F (f : X F → ℂ) z) =
        (fun p : P => fullGradient F (f : X F → ℂ) (chartEquiv p)) ∘
          chartEquiv.symm := by
      funext z
      simp [Function.comp_apply]
    rw [hrepr]
    exact hgradChart.comp chartEquiv.symm.continuous
  refine ⟨N, hN, ?_⟩
  intro f
  let hf : IsGammaTest F Γ (f : X F → ℂ) := htestsS f
  have hMassIntegrable :
      IntegrableOn (fun z : X F => ‖(f : X F → ℂ) z‖ ^ 2) S (volX F) := by
    have hcont : Continuous (fun z : X F => ‖(f : X F → ℂ) z‖ ^ 2) :=
      (hfContinuous f).norm.pow 2
    exact hcont.continuousOn.integrableOn_compact hS
  have hGradIntegrable :
    IntegrableOn (fun z : X F => ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) S
        (volX F) := by
    have hcont : Continuous
        (fun z : X F => ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) :=
      (hgradContinuous f).norm.pow 2
    exact hcont.continuousOn.integrableOn_compact hS
  have hMassLiftInv : ∀ γ : Γ, ∀ z,
      l2Lift F Γ D (e.toL2 f) (γ • z) = l2Lift F Γ D (e.toL2 f) z := by
    intro γ z
    exact rellich_l2Lift_invariant Γ D (e.toL2 f) γ z
  have hfInv : ∀ γ : Γ, ∀ z,
      (f : X F → ℂ) (γ • z) = (f : X F → ℂ) z := by
    intro γ z
    exact hf.1 (γ : SL(2,𝓞 F)) γ.2 z
  have hMassLift := rellich_l2Lift_eq_of_rep Γ D hD (e.toL2 f)
    (f : X F → ℂ) (e.mass_rep f) hmp hMassLiftInv hfInv
  have hMassEq :
      (∫ z in S, ‖(f : X F → ℂ) z‖ ^ 2 ∂(volX F)) =
        ∫ z in S, ‖l2Lift F Γ D (e.toL2 f) z‖ ^ 2 ∂(volX F) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hMassLift] with z hz
    simp [hz]
  have hMassBound :
      (∫ z in S, ‖(f : X F → ℂ) z‖ ^ 2 ∂(volX F)) ≤
        N * ‖e.toL2 f‖ ^ 2 := by
    calc
      _ = ∫ z in S, ‖l2Lift F Γ D (e.toL2 f) z‖ ^ 2 ∂(volX F) := hMassEq
      _ ≤ (overlapMultiplicity F Γ S : ℝ) * ‖e.toL2 f‖ ^ 2 := hcontrol (e.toL2 f)
      _ = N * ‖e.toL2 f‖ ^ 2 := by rfl
  let uNorm : L2Space F D := rellichGradientNormL2 (e.gradL2 f)
  have hNormRep : ∀ᵐ z ∂(volX F), z ∈ D →
      uNorm z = (‖fullGradient F (f : X F → ℂ) z‖ : ℂ) := by
    have hNormRepD := rellichGradientNormL2_ae (e.gradL2 f)
    have hNormRepGlobal : ∀ᵐ z ∂(volX F), z ∈ D →
        uNorm z = (‖e.gradL2 f z‖ : ℂ) := by
      apply (ae_restrict_iff'₀ hD.nullMeasurableSet).1
      exact hNormRepD
    filter_upwards [hNormRepGlobal, e.gradient_rep f] with z hn hg hz
    rw [hn hz, hg hz]
  let gradAbs : X F → ℂ := fun z => ‖fullGradient F (f : X F → ℂ) z‖
  have hGradAbsInv : ∀ γ : Γ, ∀ z, gradAbs (γ • z) = gradAbs z := by
    intro γ z
    let g : InfinitePlace F → SL(2,ℂ) :=
      fun w => toInf F (toSLF F (γ : SL(2,𝓞 F))) w
    have hact (x : X F) : actAtPlaces F g x = (γ : SL(2,𝓞 F)) • x := rfl
    have hG4 := G4_energy g (f : X F → ℂ) (f : X F → ℂ) hf.2.1 hf.2.1
    have hfComp : (fun x : X F => (f : X F → ℂ) (actAtPlaces F g x)) =
        (f : X F → ℂ) := by
      funext x
      rw [hact x]
      exact hf.1 (γ : SL(2,𝓞 F)) γ.2 x
    have hEnergyCast : totalGradNormSq F (f : X F → ℂ) z =
        totalGradNormSq F (f : X F → ℂ) ((γ : SL(2,𝓞 F)) • z) := by
      have h := hG4.2.1 z
      rw [hfComp] at h
      simpa only [hact] using h
    have hEnergy : totalGradNormSq F (f : X F → ℂ) z =
        totalGradNormSq F (f : X F → ℂ) (γ • z) := by
      change totalGradNormSq F (f : X F → ℂ) z =
        totalGradNormSq F (f : X F → ℂ) ((γ : SL(2,𝓞 F)) • z)
      exact hEnergyCast
    have hNormSq :
        ‖fullGradient F (f : X F → ℂ) (γ • z)‖ ^ 2 =
          ‖fullGradient F (f : X F → ℂ) z‖ ^ 2 := by
      rw [rellich_fullGradient_norm_sq, rellich_fullGradient_norm_sq]
      exact hEnergy.symm
    have hNorm :
        ‖fullGradient F (f : X F → ℂ) (γ • z)‖ =
          ‖fullGradient F (f : X F → ℂ) z‖ := by
      nlinarith [norm_nonneg (fullGradient F (f : X F → ℂ) (γ • z)),
        norm_nonneg (fullGradient F (f : X F → ℂ) z)]
    change (‖fullGradient F (f : X F → ℂ) (γ • z)‖ : ℂ) =
      (‖fullGradient F (f : X F → ℂ) z‖ : ℂ)
    exact congrArg Complex.ofReal hNorm
  have hNormLiftInv : ∀ γ : Γ, ∀ z,
      l2Lift F Γ D uNorm (γ • z) = l2Lift F Γ D uNorm z := by
    intro γ z
    exact rellich_l2Lift_invariant Γ D uNorm γ z
  have hGradLift := rellich_l2Lift_eq_of_rep Γ D hD uNorm gradAbs
    hNormRep hmp hNormLiftInv hGradAbsInv
  have hGradEq :
      (∫ z in S, ‖fullGradient F (f : X F → ℂ) z‖ ^ 2 ∂(volX F)) =
        ∫ z in S, ‖l2Lift F Γ D uNorm z‖ ^ 2 ∂(volX F) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hGradLift] with z hz
    simp [gradAbs, hz]
  have hNormBound : ‖uNorm‖ ≤ ‖e.gradL2 f‖ :=
    rellichGradientNormL2_norm_le (e.gradL2 f)
  have hNormSqBound : ‖uNorm‖ ^ 2 ≤ ‖e.gradL2 f‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hNormBound
  have hGradBound :
      (∫ z in S, ‖fullGradient F (f : X F → ℂ) z‖ ^ 2 ∂(volX F)) ≤
        N * ‖e.gradL2 f‖ ^ 2 := by
    calc
      _ = ∫ z in S, ‖l2Lift F Γ D uNorm z‖ ^ 2 ∂(volX F) := hGradEq
      _ ≤ (overlapMultiplicity F Γ S : ℝ) * ‖uNorm‖ ^ 2 := hcontrol uNorm
      _ ≤ N * ‖e.gradL2 f‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hNormSqBound hN
  calc
    ∫ z in S, (‖(f : X F → ℂ) z‖ ^ 2 +
        ‖fullGradient F (f : X F → ℂ) z‖ ^ 2) ∂(volX F) =
        (∫ z in S, ‖(f : X F → ℂ) z‖ ^ 2 ∂(volX F)) +
          (∫ z in S, ‖fullGradient F (f : X F → ℂ) z‖ ^ 2 ∂(volX F)) := by
            rw [integral_add hMassIntegrable hGradIntegrable]
    _ ≤ N * ‖e.toL2 f‖ ^ 2 + N * ‖e.gradL2 f‖ ^ 2 :=
      add_le_add hMassBound hGradBound
    _ = N * (‖e.toL2 f‖ ^ 2 + ‖e.gradL2 f‖ ^ 2) := by ring

end ArtinPrimitiveRoots.A1.Spec
