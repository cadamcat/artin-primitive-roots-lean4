import ArtinPrimitiveRoots.Spec.GeometryExtra
import ArtinPrimitiveRoots.Spec.ReductionExtra

/-! L² and energy-space nodes T1--T7. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem t1_cuspUnits_finiteIndex (Γ : Subgroup SL(2,𝓞 F))
    [Γ.FiniteIndex] (σ : SL(2,F)) : (cuspUnits F Γ σ).FiniteIndex := by
  classical
  obtain ⟨N, hN, hfreeN⟩ := R11_free_level (F := F)
  letI : NeZero N := ⟨hN⟩
  letI : (congrSubgroup F N).FiniteIndex := by
    change (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk N)).ker.FiniteIndex
    infer_instance
  let Δ : Subgroup SL(2,𝓞 F) := Γ ⊓ congrSubgroup F N
  letI : Δ.FiniteIndex := inferInstance
  have hfreeΔ : FreeAction F Δ := by
    intro γ hγ z hz
    exact hfreeN γ hγ.2 z hz
  have hΔunits : (cuspUnits F Δ σ).FiniteIndex :=
    (R2_cusp_units Δ hfreeΔ σ).1
  have hset : cuspUnitSet F Δ σ ⊆ cuspUnitSet F Γ σ := by
    intro ε hε
    rcases hε with ⟨μ, γ, hγ⟩
    refine ⟨μ, ⟨(γ : SL(2,𝓞 F)), γ.property.1⟩, ?_⟩
    exact hγ
  have hle : cuspUnits F Δ σ ≤ cuspUnits F Γ σ :=
    Subgroup.closure_mono hset
  exact Subgroup.finiteIndex_of_le hle

private theorem t1_cuspTranslationFD (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) :
    ∃ P : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain (cuspTranslations F Γ σ) P (volume) ∧
      Bornology.IsBounded P ∧ MeasurableSet P ∧
      ∀ x, ∃ μ ∈ cuspTranslations F Γ σ, μ + x ∈ P := by
  classical
  obtain ⟨_, _, _, hLatticeData, _⟩ := R1_cusp_lattice Γ σ
  rcases hLatticeData with ⟨hFull, _, _⟩
  rcases hFull with ⟨hdisc, hZLattice⟩
  let E := InfinitePlace F → ℂ
  let L : Submodule ℤ E := cuspTranslationsZ F Γ σ
  letI : DiscreteTopology L := hdisc
  letI : IsZLattice ℝ L := hZLattice
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  letI : Module.Free ℤ L := ZLattice.module_free ℝ L
  let b := Module.Free.chooseBasis ℤ L
  let bE := b.ofZLatticeBasis ℝ
  let P : Set E := ZSpan.fundamentalDomain bE
  have hLcoe : (L : Set E) = cuspTranslations F Γ σ := by
    change (Submodule.span ℤ (cuspTranslations F Γ σ : Set E) : Set E) = _
    rw [show (cuspTranslations F Γ σ : Set E) =
      ((cuspTranslations F Γ σ).toIntSubmodule : Set E) by
        exact (AddSubgroup.coe_toIntSubmodule _).symm]
    rw [Submodule.span_eq, AddSubgroup.coe_toIntSubmodule]
  have hLadd : L.toAddSubgroup = cuspTranslations F Γ σ := by
    ext x
    change x ∈ (L : Set E) ↔ x ∈ cuspTranslations F Γ σ
    rw [hLcoe]
    rfl
  have hPfund : IsAddFundamentalDomain (cuspTranslations F Γ σ) P (volume : Measure E) := by
    have h := ZLattice.isAddFundamentalDomain b (volume : Measure E)
    let e : ↥(cuspTranslations F Γ σ) ≃ ↥L := Set.equivOfEq hLcoe.symm
    simpa [P] using h.image_of_equiv (Equiv.refl E)
      (MeasurePreserving.id (volume : Measure E)).quasiMeasurePreserving e (by
      intro g x
      rfl)
  have hPbounded : Bornology.IsBounded P := by
    exact ZSpan.fundamentalDomain_isBounded bE
  have hPmeas : MeasurableSet P := by
    exact ZSpan.fundamentalDomain_measurableSet bE
  have hfloor_mem (x : E) : (ZSpan.floor bE x : E) ∈ L := by
    have hspan_le : Submodule.span ℤ (Set.range bE) ≤ L := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      change bE i ∈ L
      simpa [bE] using (b i).property
    exact hspan_le (ZSpan.floor bE x).property
  have hfloor_translation (x : E) : (ZSpan.floor bE x : E) ∈ cuspTranslations F Γ σ := by
    have hx : (ZSpan.floor bE x : E) ∈ (L : Set E) := hfloor_mem x
    rw [hLcoe] at hx
    exact hx
  refine ⟨P, hPfund, hPbounded, hPmeas, ?_⟩
  intro x
  refine ⟨-((ZSpan.floor bE x : E)), ?_, ?_⟩
  · exact (cuspTranslations F Γ σ).neg_mem (hfloor_translation x)
  · have hfract : -(ZSpan.floor bE x : E) + x = ZSpan.fract bE x := by
      simp [ZSpan.fract, sub_eq_add_neg, add_comm]
    rw [hfract]
    exact ZSpan.fract_mem_fundamentalDomain bE x

private theorem t1_siegelData_nonempty (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    Nonempty (SiegelData F Γ) := by
  classical
  obtain ⟨⟨ι, hι, σ, hReps⟩, _, _, _⟩ := R3_cusps_finite (F := F) Γ
  letI : Fintype ι := hι
  obtain ⟨C_M, hC_M, hMinkowski⟩ := R7_minkowski (F := F)
  have hPData (i : ι) := t1_cuspTranslationFD (F := F) Γ (σ i)
  choose P hPfund hPbounded hPmeas hPcover using hPData
  have hR4 (i : ι) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : InfinitePlace F → ℝ, (∀ w, 0 < t w) →
        ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ (σ i) ∧ ∀ w,
          |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
            (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')| ≤ B := by
    letI : (cuspUnits F Γ (σ i)).FiniteIndex :=
      t1_cuspUnits_finiteIndex (F := F) Γ (σ i)
    exact R4_unit_balance (cuspUnits F Γ (σ i))
  choose B hB hBalance using hR4
  refine ⟨{
    ι := ι
    fintype := hι
    σ := σ
    P := P
    B := B
    C_M := C_M
    C_M_pos := hC_M
    minkowski := hMinkowski
    P_fundamental := hPfund
    P_covers := hPcover
    P_bounded := hPbounded
    P_measurable := hPmeas
    balanced := hBalance
    reps_bijective := hReps
  }⟩

private theorem t1_action_facts (Γ : Subgroup SL(2,𝓞 F)) :
    Countable Γ ∧ MeasurableConstSMul Γ (X F) ∧
      SMulInvariantMeasure Γ (X F) (volX F) := by
  classical
  letI : IsTopologicalGroup SL(2,ℂ) := Matrix.SpecialLinearGroup.isTopologicalGroup
  letI : BorelSpace (H3) := ⟨rfl⟩
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (𝓞 F) := NumberField.RingOfIntegers.coe_injective.countable
  letI : Countable (Fin 2 → 𝓞 F) := inferInstance
  letI : Countable (Fin 2 → Fin 2 → 𝓞 F) := inferInstance
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
    change Countable (Fin 2 → Fin 2 → 𝓞 F)
    infer_instance
  letI : Countable (SL(2,𝓞 F)) := Subtype.val_injective.countable
  letI : Countable Γ := Subtype.val_injective.countable
  have hmeas (γ : Γ) : Measurable (fun z : X F => (γ : SL(2,𝓞 F)) • z) := by
    apply measurable_pi_iff.mpr
    intro w
    change Measurable (fun z : X F =>
      (toInf F (toSLF F (γ : SL(2,𝓞 F))) w) • z w)
    exact (continuous_const_smul _).measurable.comp (measurable_pi_apply w)
  have hmap (γ : Γ) :
      Measure.map (fun z : X F => (γ : SL(2,𝓞 F)) • z) (volX F) = volX F := by
    change Measure.map (fun z : X F => actAtPlaces F
      (toInf F (toSLF F (γ : SL(2,𝓞 F)))) z) (volX F) = _
    exact (G3_volume (F := F)).1 _
  let hmeasSMul : MeasurableConstSMul Γ (X F) := ⟨fun γ => by
    change Measurable (fun z : X F => (γ : SL(2,𝓞 F)) • z)
    exact hmeas γ⟩
  let hInvariant : SMulInvariantMeasure Γ (X F) (volX F) := by
    refine ⟨fun γ s hs => ?_⟩
    change (volX F) ((fun x : X F => (γ : SL(2,𝓞 F)) • x) ⁻¹' s) = _
    have hh := congrArg (fun μ : Measure (X F) => μ s) (hmap γ)
    rw [Measure.map_apply (hmeas γ) hs] at hh
    exact hh
  exact ⟨inferInstance, hmeasSMul, hInvariant⟩

private theorem t1_l2Lift_properties (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (hD : IsFundamentalDomain Γ D (volX F)) (u : L2Space F D) :
    AEStronglyMeasurable (l2Lift F Γ D u) (volX F) ∧
      ∀ γ ∈ Γ, ∀ z, l2Lift F Γ D u ((γ : SL(2,𝓞 F)) • z) = l2Lift F Γ D u z := by
  classical
  rcases t1_action_facts (F := F) Γ with ⟨hCountable, hMeasurable, hInvariant⟩
  letI : Countable Γ := hCountable
  letI : MeasurableConstSMul Γ (X F) := hMeasurable
  letI : SMulInvariantMeasure Γ (X F) (volX F) := hInvariant
  have hu : AEStronglyMeasurable (u : X F → ℂ) ((volX F).restrict D) :=
    Lp.aestronglyMeasurable u
  have hext : AEStronglyMeasurable (D.indicator (u : X F → ℂ)) (volX F) :=
    (aestronglyMeasurable_indicator_iff₀ hD.nullMeasurableSet).2 hu
  constructor
  · apply AEStronglyMeasurable.tsum
    intro γ
    have hpres : MeasurePreserving (fun z : X F => (γ : SL(2,𝓞 F)) • z)
        (volX F) (volX F) := by
      change MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F)
      exact measurePreserving_smul γ (volX F)
    convert hext.comp_measurePreserving hpres using 1
    ext z
    rfl
  · intro δ hδ z
    let δ' : Γ := ⟨δ, hδ⟩
    change (∑' γ : Γ,
        if (γ : SL(2,𝓞 F)) • ((δ : SL(2,𝓞 F)) • z) ∈ D then
          u ((γ : SL(2,𝓞 F)) • ((δ : SL(2,𝓞 F)) • z)) else 0) =
      ∑' γ : Γ,
        if (γ : SL(2,𝓞 F)) • z ∈ D then u ((γ : SL(2,𝓞 F)) • z) else 0
    let t : Γ → ℂ := fun γ =>
      if (γ : SL(2,𝓞 F)) • z ∈ D then u ((γ : SL(2,𝓞 F)) • z) else 0
    calc
      (∑' γ : Γ,
          if (γ : SL(2,𝓞 F)) • ((δ : SL(2,𝓞 F)) • z) ∈ D then
            u ((γ : SL(2,𝓞 F)) • ((δ : SL(2,𝓞 F)) • z)) else 0) =
        ∑' γ : Γ, t (γ * δ') := by
          apply tsum_congr
          intro γ
          simp [t, δ', smul_smul, Subgroup.coe_mul]
      _ = ∑' γ : Γ, t γ := (Equiv.mulRight δ').tsum_eq t

open scoped Pointwise in
private theorem t1_l2Lift_eq_on_D (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (hD : IsFundamentalDomain Γ D (volX F)) (u : L2Space F D) :
    ∀ᵐ z ∂(volX F), z ∈ D → l2Lift F Γ D u z = u z := by
  classical
  rcases t1_action_facts (F := F) Γ with ⟨hCountable, hMeasurable, hInvariant⟩
  letI : Countable Γ := hCountable
  letI : MeasurableConstSMul Γ (X F) := hMeasurable
  letI : SMulInvariantMeasure Γ (X F) (volX F) := hInvariant
  have hUnique : ∀ᵐ z ∂(volX F).restrict D, ∀ γ : Γ,
      (γ : SL(2,𝓞 F)) • z ∈ D → γ = 1 := by
    rw [ae_all_iff]
    intro γ
    by_cases hγ : γ = 1
    · filter_upwards [] with z hz
      exact hγ
    · have hne : (1 : Γ) ≠ γ⁻¹ := by
        intro h
        have h' := congrArg (fun x : Γ => x⁻¹) h
        have h'' : (1 : Γ) = γ := by simpa using h'
        exact hγ h''.symm
      have hdisj : AEDisjoint (volX F) D ((γ⁻¹ : Γ) • D) := by
        have h := hD.aedisjoint hne
        change AEDisjoint (volX F) ((1 : Γ) • D) ((γ⁻¹ : Γ) • D) at h
        simpa using h
      have hNo : ∀ᵐ z ∂(volX F), z ∈ D → z ∉ (γ⁻¹ : Γ) • D := by
        filter_upwards [hdisj.sdiff_ae_eq_left] with z hzDiff
        intro hzD
        exact (hzDiff.mpr hzD).2
      have hNoRestrict : ∀ᵐ z ∂(volX F).restrict D, z ∉ (γ⁻¹ : Γ) • D := by
        filter_upwards [hNo.filter_mono ae_restrict_le,
          ae_restrict_mem₀ hD.nullMeasurableSet] with z hNo hzD
        exact hNo hzD
      filter_upwards [hNoRestrict] with z hzNo hzγ
      have hzInv : z ∈ (γ⁻¹ : Γ) • D := by
        refine Set.mem_smul_set.mpr ⟨(γ : SL(2,𝓞 F)) • z, hzγ, ?_⟩
        change ((γ⁻¹ : Γ) : SL(2,𝓞 F)) • ((γ : SL(2,𝓞 F)) • z) = z
        simp
      exact False.elim (hzNo hzInv)
  have hEqRestrict : ∀ᵐ z ∂(volX F).restrict D, l2Lift F Γ D u z = u z := by
    filter_upwards [hUnique, ae_restrict_mem₀ hD.nullMeasurableSet] with z hzUnique hzD
    change (∑' γ : Γ,
        if (γ : SL(2,𝓞 F)) • z ∈ D then u ((γ : SL(2,𝓞 F)) • z) else 0) = u z
    rw [tsum_eq_single (1 : Γ)]
    · simp [hzD]
    · intro γ hγ
      have hnot : (γ : SL(2,𝓞 F)) • z ∉ D := by
        intro hmem
        exact hγ (hzUnique γ hmem)
      simp [hnot]
  exact ae_imp_of_ae_restrict hEqRestrict

open scoped Pointwise in
private theorem t1_translate_support_card (Γ : Subgroup SL(2,𝓞 F))
    (K : Set (X F)) (hOverlap : (overlapSet F Γ K K).Finite) (z : X F) :
    ( {γ : Γ | z ∈ (γ : SL(2,𝓞 F)) • K}.Finite ∧
      Nat.card {γ : Γ | z ∈ (γ : SL(2,𝓞 F)) • K} ≤ Nat.card (overlapSet F Γ K K)) := by
  classical
  let S : Set Γ := {γ | z ∈ (γ : SL(2,𝓞 F)) • K}
  by_cases hS : S.Nonempty
  · rcases hS with ⟨γ₀val, hγ₀mem⟩
    let γ₀ : S := ⟨γ₀val, hγ₀mem⟩
    have hγ₀K : ((γ₀.1 : SL(2,𝓞 F))⁻¹) • z ∈ K :=
      (Set.mem_smul_set_iff_inv_smul_mem).mp γ₀.2
    letI : Finite (overlapSet F Γ K K) := hOverlap
    let e : S ↪ overlapSet F Γ K K :=
      { toFun := fun γ =>
          ⟨γ.1⁻¹ * γ₀.1, by
            have hγK : ((γ.1 : SL(2,𝓞 F))⁻¹) • z ∈ K :=
              (Set.mem_smul_set_iff_inv_smul_mem).mp γ.2
            refine ⟨((γ₀.1 : SL(2,𝓞 F))⁻¹) • z, hγ₀K, ?_⟩
            simpa [smul_smul, mul_assoc] using hγK⟩
        inj' := by
          intro γ γ' h
          apply Subtype.ext
          apply inv_injective
          exact mul_right_cancel (congrArg Subtype.val h) }
    exact ⟨Finite.of_injective e e.injective, Finite.card_le_of_embedding e⟩
  · have hEmpty : ({γ : Γ | z ∈ (γ : SL(2,𝓞 F)) • K} : Set Γ) = ∅ := by
      ext γ
      constructor
      · intro hγ
        exact (hS ⟨γ, hγ⟩).elim
      · intro hfalse
        exact hfalse.elim
    refine ⟨?_, ?_⟩
    · rw [hEmpty]
      exact Set.finite_empty
    · rw [hEmpty]
      simp

open scoped Classical in
private theorem t1_tsum_indicator_one {ι : Type*} [Countable ι]
    (S : Set ι) (hS : S.Finite) :
    ∑' i : ι, (if i ∈ S then (1 : ENNReal) else 0) = (Nat.card S : ENNReal) := by
  classical
  calc
    ∑' i : ι, (if i ∈ S then (1 : ENNReal) else 0) =
        ∑ i ∈ hS.toFinset, (if i ∈ S then (1 : ENNReal) else 0) :=
      tsum_eq_sum (s := hS.toFinset) (fun i hi => by
        have hnot : i ∉ S := fun h => hi (hS.mem_toFinset.mpr h)
        simp [hnot])
    _ = ∑ i ∈ hS.toFinset, (1 : ENNReal) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hmem : i ∈ S := hS.mem_toFinset.mp hi
      simp [hmem]
    _ = (hS.toFinset.card : ENNReal) := by simp
    _ = (S.ncard : ENNReal) := by rw [Set.ncard_eq_toFinset_card S hS]

open scoped Pointwise in
/-- T1 `spec:l2` — P-SPEC.md:228. The invariant lift, compact-overlap bound, unfolding formula,
and independence of the chosen fundamental domain. -/
theorem T1_l2 (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F)) :
    (∀ u : L2Space F D, AEStronglyMeasurable (l2Lift F Γ D u) (volX F) ∧
      ∀ γ ∈ Γ, ∀ z, l2Lift F Γ D u ((γ : SL(2,𝓞 F)) • z) = l2Lift F Γ D u z) ∧
    (∀ K : Set (X F), IsCompact K →
      Set.Finite (overlapSet F Γ K K) ∧
      ∀ u : L2Space F D,
        ∫ z in K, ‖l2Lift F Γ D u z‖ ^ 2 ∂(volX F) ≤
          (overlapMultiplicity F Γ K : ℝ) * ‖u‖ ^ 2) ∧
    (∀ f : X F → ℂ, Integrable f (volX F) →
      ∫ z in D, (∑' γ : Γ, f ((γ : SL(2,𝓞 F)) • z)) ∂(volX F) =
        ∫ z, f z ∂(volX F)) ∧
    (∀ D' : Set (X F), IsFundamentalDomain Γ D' (volX F) →
      ∀ f : X F → ℂ, Integrable f (volX F) →
        (∀ γ ∈ Γ, ∀ z, f ((γ : SL(2,𝓞 F)) • z) = f z) →
        ∫ z in D, f z ∂(volX F) = ∫ z in D', f z ∂(volX F)) := by
  classical
  rcases t1_action_facts (F := F) Γ with ⟨hCountable, hMeasurable, hInvariant⟩
  letI : Countable Γ := hCountable
  letI : MeasurableConstSMul Γ (X F) := hMeasurable
  letI : SMulInvariantMeasure Γ (X F) (volX F) := hInvariant
  have hpres (γ : Γ) : MeasurePreserving
      (fun z : X F => (γ : SL(2,𝓞 F)) • z) (volX F) (volX F) := by
    change MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F)
    exact measurePreserving_smul γ (volX F)
  refine ⟨?_, ?_⟩
  · intro u
    exact t1_l2Lift_properties (F := F) Γ D hD u
  · refine ⟨?_, ?_⟩
    · intro K hK
      let d : SiegelData F Γ := Classical.choice (t1_siegelData_nonempty (F := F) Γ)
      have hSL : {g : SL(2,𝓞 F) | ∃ z ∈ K, g • z ∈ K}.Finite :=
        (R9_proper Γ d).1 K K hK hK
      have hOverlap : (overlapSet F Γ K K).Finite := by
        let e : Γ ↪ SL(2,𝓞 F) := ⟨Subtype.val, Subtype.val_injective⟩
        simpa [overlapSet, e] using hSL.preimage_embedding e
      refine ⟨hOverlap, ?_⟩
      · intro u
        let q : X F → ENNReal := fun z => ENNReal.ofReal (‖l2Lift F Γ D u z‖ ^ 2)
        let p : X F → ENNReal := fun z => ENNReal.ofReal (‖u z‖ ^ 2)
        have hLiftProps := t1_l2Lift_properties (F := F) Γ D hD u
        have hLiftEq := t1_l2Lift_eq_on_D (F := F) Γ D hD u
        have hEqD : ∀ᵐ z ∂(volX F).restrict D, l2Lift F Γ D u z = u z :=
          (ae_restrict_iff'₀ (μ := volX F) (s := D) hD.nullMeasurableSet).2 hLiftEq
        have hDecomp :
            ∫⁻ z in K, q z ∂(volX F) =
              ∑' γ : Γ, ∫⁻ z in (γ : SL(2,𝓞 F)) • K ∩ D,
                q (((γ⁻¹ : Γ) : SL(2,𝓞 F)) • z) ∂(volX F) :=
          hD.setLIntegral_eq_tsum' q K
        have hInv (γ : Γ) (z : X F) :
            l2Lift F Γ D u (((γ⁻¹ : Γ) : SL(2,𝓞 F)) • z) = l2Lift F Γ D u z :=
          hLiftProps.2 ((γ⁻¹ : Γ) : SL(2,𝓞 F)) (γ⁻¹).property z
        have hDecompU :
            ∫⁻ z in K, q z ∂(volX F) =
              ∑' γ : Γ, ∫⁻ z in (γ : SL(2,𝓞 F)) • K ∩ D, p z ∂(volX F) := by
          calc
            ∫⁻ z in K, q z ∂(volX F) =
                ∑' γ : Γ, ∫⁻ z in (γ : SL(2,𝓞 F)) • K ∩ D,
                  q (((γ⁻¹ : Γ) : SL(2,𝓞 F)) • z) ∂(volX F) := hDecomp
            _ = ∑' γ : Γ, ∫⁻ z in (γ : SL(2,𝓞 F)) • K ∩ D, p z ∂(volX F) := by
              apply tsum_congr
              intro γ
              apply lintegral_congr_ae
              have hEqInter : ∀ᵐ z ∂(volX F).restrict
                  ((γ : SL(2,𝓞 F)) • K ∩ D), l2Lift F Γ D u z = u z :=
                ae_mono (Measure.restrict_mono Set.inter_subset_right le_rfl) hEqD
              filter_upwards [hEqInter] with z hz
              change ENNReal.ofReal
                  (‖l2Lift F Γ D u (((γ⁻¹ : Γ) : SL(2,𝓞 F)) • z)‖ ^ 2) =
                ENNReal.ofReal (‖u z‖ ^ 2)
              rw [hInv γ z, hz]
        letI : TopologicalSpace SL(2,ℂ) :=
          Matrix.SpecialLinearGroup.instTopologicalSpace
        letI : IsTopologicalGroup SL(2,ℂ) := Matrix.SpecialLinearGroup.isTopologicalGroup
        letI : BorelSpace H3 := ⟨rfl⟩
        have hUnitaryClosed : IsClosed
            (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
          have hEq : (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
              {A | A * star A = 1} := by
            ext A
            exact Matrix.mem_unitaryGroup_iff
          rw [hEq]
          exact isClosed_eq (by fun_prop) continuous_const
        have hSU2Closed : IsClosed (SU2 : Set SL(2,ℂ)) := by
          change IsClosed ((Subtype.val : SL(2,ℂ) → Matrix (Fin 2) (Fin 2) ℂ) ⁻¹'
            (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)))
          exact hUnitaryClosed.preimage continuous_subtype_val
        letI : IsClosed (SU2 : Set SL(2,ℂ)) := hSU2Closed
        letI : SecondCountableTopology (Fin 2 → ℝ) := inferInstance
        letI : SecondCountableTopology ℂ :=
          Complex.basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.secondCountableTopology
        letI : SecondCountableTopology (Fin 2 → ℂ) := by infer_instance
        letI : SecondCountableTopology (Fin 2 → Fin 2 → ℂ) := by infer_instance
        letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
          change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
          infer_instance
        letI : SecondCountableTopology (SL(2,ℂ)) :=
          TopologicalSpace.secondCountableTopology_induced
            (SL(2,ℂ)) (Matrix (Fin 2) (Fin 2) ℂ) Subtype.val
        letI : T2Space (H3) := inferInstance
        letI : SecondCountableTopology (H3) :=
          TopologicalSpace.Quotient.secondCountableTopology
            QuotientGroup.isOpenQuotientMap_mk.isOpenMap
        letI : T2Space (X F) := Pi.t2Space
        letI : BorelSpace (X F) := Pi.borelSpace
        letI : OpensMeasurableSpace (X F) := BorelSpace.opensMeasurable
        have hcont (γ : Γ) : Continuous (fun z : X F => (γ : SL(2,𝓞 F)) • z) := by
          change Continuous (fun z : X F =>
            actAtPlaces F (toInf F (toSLF F (γ : SL(2,𝓞 F)))) z)
          exact continuous_pi fun w =>
            (continuous_const_smul _).comp (continuous_apply w)
        have hKmeas (γ : Γ) : MeasurableSet ((γ : SL(2,𝓞 F)) • K) := by
          exact (hK.image (hcont γ)).isClosed.measurableSet
        have hu : AEStronglyMeasurable (u : X F → ℂ) ((volX F).restrict D) :=
          Lp.aestronglyMeasurable u
        have hpNorm : AEStronglyMeasurable (fun z : X F => ‖u z‖ ^ 2)
            ((volX F).restrict D) :=
          (continuous_pow 2).comp_aestronglyMeasurable hu.norm
        have hp : AEMeasurable p ((volX F).restrict D) := by
          exact ENNReal.measurable_ofReal.comp_aemeasurable hpNorm.aemeasurable
        have hIndicatorTerm (γ : Γ) :
            ∫⁻ z in (γ : SL(2,𝓞 F)) • K ∩ D, p z ∂(volX F) =
              ∫⁻ z in D, ((γ : SL(2,𝓞 F)) • K).indicator p z ∂(volX F) := by
          exact (setLIntegral_indicator (hKmeas γ) p (t := D)).symm
        have hTsumIndicator :
            ∑' γ : Γ, ∫⁻ z in (γ : SL(2,𝓞 F)) • K ∩ D, p z ∂(volX F) =
              ∫⁻ z in D, ∑' γ : Γ, ((γ : SL(2,𝓞 F)) • K).indicator p z ∂(volX F) := by
          calc
            _ = ∑' γ : Γ, ∫⁻ z in D,
                  ((γ : SL(2,𝓞 F)) • K).indicator p z ∂(volX F) := tsum_congr hIndicatorTerm
            _ = _ := (lintegral_tsum (μ := (volX F).restrict D)
              (fun γ => hp.indicator (hKmeas γ))).symm
        have hPointwise (z : X F) :
            ∑' γ : Γ, ((γ : SL(2,𝓞 F)) • K).indicator p z ≤
              (Nat.card (overlapSet F Γ K K) : ENNReal) * p z := by
          classical
          let S : Set Γ := {γ | z ∈ (γ : SL(2,𝓞 F)) • K}
          have hInfo := t1_translate_support_card (F := F) Γ K hOverlap z
          have hOne := t1_tsum_indicator_one S hInfo.1
          have hTerm (γ : Γ) :
              ((γ : SL(2,𝓞 F)) • K).indicator p z =
                (if γ ∈ S then (1 : ENNReal) else 0) * p z := by
            by_cases hz : z ∈ (γ : SL(2,𝓞 F)) • K <;>
              simp [Set.indicator, S, hz]
          calc
            ∑' γ : Γ, ((γ : SL(2,𝓞 F)) • K).indicator p z =
                ∑' γ : Γ, (if γ ∈ S then (1 : ENNReal) else 0) * p z :=
              tsum_congr hTerm
            _ = (Nat.card S : ENNReal) * p z := by rw [ENNReal.tsum_mul_right, hOne]
            _ ≤ (Nat.card (overlapSet F Γ K K) : ENNReal) * p z := by
              have hCard : (Nat.card S : ENNReal) ≤ Nat.card (overlapSet F Γ K K) := by
                exact_mod_cast hInfo.2
              exact mul_le_mul_of_nonneg_right hCard (by positivity)
        have hLintegralBound :
            ∫⁻ z in D, ∑' γ : Γ, ((γ : SL(2,𝓞 F)) • K).indicator p z ∂(volX F) ≤
              (Nat.card (overlapSet F Γ K K) : ENNReal) *
                ∫⁻ z in D, p z ∂(volX F) := by
          calc
            ∫⁻ z in D, ∑' γ : Γ, ((γ : SL(2,𝓞 F)) • K).indicator p z ∂(volX F) ≤
                ∫⁻ z in D, (Nat.card (overlapSet F Γ K K) : ENNReal) * p z ∂(volX F) :=
              lintegral_mono hPointwise
            _ = _ := by
              rw [lintegral_const_mul'' _ hp]
        have hDecompSum :
            ∫⁻ z in K, q z ∂(volX F) =
              ∫⁻ z in D, ∑' γ : Γ, ((γ : SL(2,𝓞 F)) • K).indicator p z ∂(volX F) := by
          calc
            ∫⁻ z in K, q z ∂(volX F) =
                ∑' γ : Γ, ∫⁻ z in (γ : SL(2,𝓞 F)) • K ∩ D, p z ∂(volX F) := hDecompU
            _ = _ := hTsumIndicator
        have hLintegralK :
            ∫⁻ z in K, q z ∂(volX F) ≤
              (Nat.card (overlapSet F Γ K K) : ENNReal) *
                ∫⁻ z in D, p z ∂(volX F) := hDecompSum.trans_le hLintegralBound
        have huSq : Integrable (fun z : X F => ‖u z‖ ^ 2) ((volX F).restrict D) :=
          (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
        have hNormSq : ‖u‖ ^ 2 = ∫ z, ‖u z‖ ^ 2 ∂((volX F).restrict D) := by
          calc
            ‖u‖ ^ 2 = RCLike.re (inner ℂ u u) := InnerProductSpace.norm_sq_eq_re_inner u
            _ = ∫ z, RCLike.re (inner ℂ (u z) (u z)) ∂((volX F).restrict D) := by
              rw [L2.inner_def]
              exact (integral_re (L2.integrable_inner u u)).symm
            _ = ∫ z, ‖u z‖ ^ 2 ∂((volX F).restrict D) := by
              apply integral_congr_ae
              filter_upwards with z
              rw [inner_self_eq_norm_sq_to_K]
              exact RCLike.re_ofReal_pow _ _
        have hpReal :
            ∫ z in D, ‖u z‖ ^ 2 ∂(volX F) =
              ENNReal.toReal (∫⁻ z in D, p z ∂(volX F)) := by
          change ∫ z, ‖u z‖ ^ 2 ∂((volX F).restrict D) =
            ENNReal.toReal (∫⁻ z, p z ∂((volX F).restrict D))
          simpa [p] using
            (integral_eq_lintegral_of_nonneg_ae
              (μ := (volX F).restrict D)
              (ae_of_all _ fun z => sq_nonneg _)
              ((continuous_pow 2).comp_aestronglyMeasurable
                (Lp.aestronglyMeasurable u).norm))
        have hpFinite : (∫⁻ z in D, p z ∂(volX F)) < (⊤ : ENNReal) := by
          change (∫⁻ z, ENNReal.ofReal (‖u z‖ ^ 2) ∂((volX F).restrict D)) <
            (⊤ : ENNReal)
          have h := hasFiniteIntegral_iff_enorm.mp huSq.hasFiniteIntegral
          have heq : (fun z : X F => ‖‖u z‖ ^ 2‖ₑ) =
              fun z => ENNReal.ofReal (‖u z‖ ^ 2) := by
            funext z
            simp [enorm, abs_of_nonneg (sq_nonneg (‖u z‖))]
          rw [heq] at h
          exact h
        have hqReal :
            ∫ z in K, ‖l2Lift F Γ D u z‖ ^ 2 ∂(volX F) =
              ENNReal.toReal (∫⁻ z in K, q z ∂(volX F)) := by
          change ∫ z, ‖l2Lift F Γ D u z‖ ^ 2 ∂((volX F).restrict K) =
            ENNReal.toReal (∫⁻ z, q z ∂((volX F).restrict K))
          simpa [q] using
            (integral_eq_lintegral_of_nonneg_ae
              (μ := (volX F).restrict K)
              (ae_of_all _ fun z => sq_nonneg _)
              ((continuous_pow 2).comp_aestronglyMeasurable
                hLiftProps.1.restrict.norm))
        have hBoundFinite :
            (Nat.card (overlapSet F Γ K K) : ENNReal) *
              ∫⁻ z in D, p z ∂(volX F) < (⊤ : ENNReal) :=
          ENNReal.mul_lt_top (by simp) hpFinite
        calc
          ∫ z in K, ‖l2Lift F Γ D u z‖ ^ 2 ∂(volX F) =
              ENNReal.toReal (∫⁻ z in K, q z ∂(volX F)) := hqReal
          _ ≤ ENNReal.toReal ((Nat.card (overlapSet F Γ K K) : ENNReal) *
                ∫⁻ z in D, p z ∂(volX F)) :=
            ENNReal.toReal_mono hBoundFinite.ne hLintegralK
          _ = (overlapMultiplicity F Γ K : ℝ) * ‖u‖ ^ 2 := by
            rw [ENNReal.toReal_mul]
            simp only [ENNReal.toReal_natCast]
            rw [hNormSq.trans hpReal]
            simp [overlapMultiplicity]
    · refine ⟨?_, ?_⟩
      · intro f hf
        have hsumNorm := ne_of_lt (hasFiniteIntegral_iff_enorm.mp hf.hasFiniteIntegral)
        rw [hD.lintegral_eq_tsum'' (fun z => ‖f z‖ₑ)] at hsumNorm
        have hmeas (γ : Γ) : AEStronglyMeasurable
            (fun z : X F => f ((γ : SL(2,𝓞 F)) • z)) ((volX F).restrict D) := by
          exact (hf.aestronglyMeasurable.comp_measurePreserving (hpres γ)).restrict
        calc
          ∫ z in D, (∑' γ : Γ, f ((γ : SL(2,𝓞 F)) • z)) ∂(volX F) =
              ∑' γ : Γ, ∫ z in D, f ((γ : SL(2,𝓞 F)) • z) ∂(volX F) := by
            exact integral_tsum (μ := (volX F).restrict D) hmeas hsumNorm
          _ = ∫ z, f z ∂(volX F) := (hD.integral_eq_tsum'' f hf).symm
      · intro D' hD' f hf hInv
        exact hD.setIntegral_eq hD' (fun γ z => hInv (γ : SL(2,𝓞 F)) γ.property z)

/-- T2 `spec:tests` — P-SPEC.md:229, 349–352. Test functions form the stated submodule, their
mass and gradient have the quotient representatives, and an automorphic partition of unity is
locally finite and reconstructs each test function. -/
private theorem t2_gammaTest_zero (Γ : Subgroup SL(2,𝓞 F)) :
    IsGammaTest F Γ (0 : X F → ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ z
    rfl
  · unfold IsSmoothX
    change ContDiffOn ℝ ∞ (fun _ : Coord F => (0 : ℂ)) (posSet F)
    exact contDiffOn_const
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro z hz
    simp at hz

private theorem t2_gammaTest_add (Γ : Subgroup SL(2,𝓞 F))
    (f g : X F → ℂ) (hf : IsGammaTest F Γ f) (hg : IsGammaTest F Γ g) :
    IsGammaTest F Γ (f + g) := by
  rcases hf with ⟨hInvF, hSmoothF, hCompactF⟩
  rcases hg with ⟨hInvG, hSmoothG, hCompactG⟩
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ z
    change f ((γ : SL(2,𝓞 F)) • z) + g ((γ : SL(2,𝓞 F)) • z) = f z + g z
    rw [hInvF γ hγ z, hInvG γ hγ z]
  · change ContDiffOn ℝ ∞ (fun p => (f + g) (ptX F p)) (posSet F)
    simpa [Pi.add_apply] using hSmoothF.add hSmoothG
  · rcases hCompactF with ⟨K, hK, hSuppF⟩
    rcases hCompactG with ⟨K', hK', hSuppG⟩
    refine ⟨K ∪ K', hK.union hK', ?_⟩
    intro z hz
    have hne : f z ≠ 0 ∨ g z ≠ 0 := by
      by_contra h
      push_neg at h
      simp [h.1, h.2] at hz
    rcases hne with hfz | hgz
    · rcases hSuppF hfz with ⟨γ, x, hx, hzx⟩
      exact ⟨γ, x, Set.mem_union_left _ hx, hzx⟩
    · rcases hSuppG hgz with ⟨γ, x, hx, hzx⟩
      exact ⟨γ, x, Set.mem_union_right _ hx, hzx⟩

private theorem t2_gammaTest_smul (Γ : Subgroup SL(2,𝓞 F))
    (c : ℂ) (f : X F → ℂ) (hf : IsGammaTest F Γ f) :
    IsGammaTest F Γ (c • f) := by
  rcases hf with ⟨hInv, hSmooth, hCompact⟩
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ z
    change c * f ((γ : SL(2,𝓞 F)) • z) = c * f z
    rw [hInv γ hγ z]
  · change ContDiffOn ℝ ∞ (fun p => c • f (ptX F p)) (posSet F)
    exact hSmooth.const_smul c
  · rcases hCompact with ⟨K, hK, hSupp⟩
    refine ⟨K, hK, ?_⟩
    intro z hz
    have hfz : f z ≠ 0 := by
      intro hzero
      simp [hzero] at hz
    exact hSupp hfz

private def t2_gammaTestSubmodule (Γ : Subgroup SL(2,𝓞 F)) :
    Submodule ℂ (X F → ℂ) where
  carrier := {f | IsGammaTest F Γ f}
  zero_mem' := t2_gammaTest_zero Γ
  add_mem' := by
    intro f g hf hg
    exact t2_gammaTest_add Γ f g hf hg
  smul_mem' := by
    intro c f hf
    exact t2_gammaTest_smul Γ c f hf

private theorem t2_chartEquiv :
    ∃ e : {p : Coord F // p ∈ posSet F} ≃ₜ X F,
      (∀ p, e p = ptX F p.1) ∧ (∀ z, (e.symm z).1 = coordsX F z) := by
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hcoords⟩
  exact hcoords

private theorem t2_coordinate_bump (C : Set (Coord F)) (hC : IsCompact C)
    (hCpos : C ⊆ posSet F) :
    ∃ φ : Coord F → ℝ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ posSet F ∧
      (∀ p, 0 ≤ φ p) ∧ IsOpen {p | 0 < φ p} ∧ C ⊆ {p | 0 < φ p} := by
  classical
  letI : Finite (InfinitePlace F) := inferInstance
  letI : Countable (InfinitePlace F) := Finite.to_countable
  have hposOpen : IsOpen (posSet F) := by
    rw [show posSet F = ⋂ w : InfinitePlace F, {p : Coord F | 0 < (p w).2} by
      ext p
      simp [posSet]]
    exact isOpen_iInter_of_finite fun w => by
      have hcont : Continuous (fun p : Coord F => (p w).2) := by fun_prop
      exact isOpen_lt continuous_const hcont
  let ι := {p : Coord F // p ∈ C}
  let b : ι → Coord F → ℝ := fun p =>
    Classical.choose (exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (hposOpen.mem_nhds (hCpos p.2)))
  have hb (p : ι) :
      tsupport (b p) ⊆ posSet F ∧ HasCompactSupport (b p) ∧
        ContDiff ℝ ∞ (b p) ∧ Set.range (b p) ⊆ Set.Icc 0 1 ∧ b p p.1 = 1 := by
    exact Classical.choose_spec (exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (hposOpen.mem_nhds (hCpos p.2)))
  let U : ι → Set (Coord F) := fun p => {x | 0 < b p x}
  have hUopen (p : ι) : IsOpen (U p) := by
    exact isOpen_lt continuous_const (hb p).2.2.1.continuous
  have hcover : C ⊆ ⋃ p : ι, U p := by
    intro x hx
    let p : ι := ⟨x, hx⟩
    refine Set.mem_iUnion.2 ⟨p, ?_⟩
    change 0 < b p x
    rw [hb p |>.2.2.2.2]
    norm_num
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hUopen hcover
  let φ : Coord F → ℝ := fun x => ∑ i ∈ t, b i x
  have hφdiff : ContDiff ℝ ∞ φ := by
    change ContDiff ℝ ∞ (fun x => ∑ i ∈ t, b i x)
    exact ContDiff.sum fun i hi => (hb i).2.2.1
  have hsumCompact : ∀ s : Finset ι, IsCompact (⋃ i ∈ s, tsupport (b i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isCompact_empty
    | @insert i s hi ih =>
        simpa [Finset.biUnion_insert, hi] using (hb i).2.1.union ih
  have hsumSupport : ∀ s : Finset ι,
      Function.support (fun x => ∑ i ∈ s, b i x) ⊆ ⋃ i ∈ s, tsupport (b i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.support]
    | @insert i s hi ih =>
        intro x hx
        have hnot : b i x ≠ 0 ∨ (∑ j ∈ s, b j x) ≠ 0 := by
          by_contra h
          simp only [not_or, not_ne_iff] at h
          simp [h.1, h.2] at hx
        rcases hnot with hxi | hxs
        · exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2
            ⟨Finset.mem_insert_self i s, subset_tsupport _ hxi⟩⟩
        · rcases Set.mem_iUnion.1 (ih hxs) with ⟨j, hj⟩
          rcases Set.mem_iUnion.1 hj with ⟨hjmem, hjx⟩
          exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2
            ⟨Finset.mem_insert_of_mem hjmem, hjx⟩⟩
  have hsumSupportT : Function.support φ ⊆ ⋃ i ∈ t, tsupport (b i) := by
    simpa [φ] using hsumSupport t
  have hclosed : IsClosed (⋃ i ∈ t, tsupport (b i)) :=
    isClosed_biUnion_finset fun i hi => isClosed_tsupport _
  have htsupportUnion : tsupport φ ⊆ ⋃ i ∈ t, tsupport (b i) :=
    closure_minimal hsumSupportT hclosed
  have hφcompact : HasCompactSupport φ := by
    change IsCompact (tsupport φ)
    exact (hsumCompact t).of_isClosed_subset (isClosed_tsupport _) htsupportUnion
  have hφsupport : tsupport φ ⊆ posSet F := by
    refine htsupportUnion.trans ?_
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    rcases Set.mem_iUnion.1 hi with ⟨hit, hix⟩
    exact (hb i).1 hix
  have hnonneg (i : ι) (x : Coord F) : 0 ≤ b i x := by
    exact ((hb i).2.2.2.1 ⟨x, rfl⟩).1
  have hpositive (x : Coord F) (hx : x ∈ C) : 0 < φ x := by
    have hxcover := ht hx
    rcases Set.mem_iUnion.1 hxcover with ⟨i, hi⟩
    rcases Set.mem_iUnion.1 hi with ⟨hit, hix⟩
    have hiPos : 0 < b i x := by
      change 0 < b i x at hix
      exact hix
    unfold φ
    exact Finset.sum_pos' (fun j hj => hnonneg j x) ⟨i, hit, hiPos⟩
  refine ⟨φ, hφdiff, hφcompact, hφsupport, ?_, ?_, ?_⟩
  · intro x
    unfold φ
    exact Finset.sum_nonneg fun i hi => hnonneg i x
  · exact isOpen_lt continuous_const hφdiff.continuous
  · intro x hx
    exact hpositive x hx

private theorem t2_compact_bump (K : Set (X F)) (hK : IsCompact K) :
    ∃ ψ : X F → ℝ,
      IsSmoothRealX F ψ ∧ HasCompactSupportX F (fun z => (ψ z : ℂ)) ∧
      (∀ z, 0 ≤ ψ z) ∧
      ∃ U : Set (X F), IsOpen U ∧ K ⊆ U ∧ ∀ z ∈ U, 0 < ψ z := by
  classical
  obtain ⟨e, hept, hecoords⟩ := t2_chartEquiv (F := F)
  let C : Set (Coord F) := (fun z => (e.symm z).1) '' K
  have hC : IsCompact C := by
    exact hK.image (continuous_subtype_val.comp e.symm.continuous)
  have hCpos : C ⊆ posSet F := by
    rintro p ⟨z, hz, rfl⟩
    exact (e.symm z).2
  rcases t2_coordinate_bump (F := F) C hC hCpos with
    ⟨θ, hθsmooth, hθcompact, hθsupport, hθnonneg, hθopen, hθpositive⟩
  let ψ : X F → ℝ := fun z => θ (coordsX F z)
  have hcoordCont : Continuous (coordsX F) := by
    rw [← funext hecoords]
    exact continuous_subtype_val.comp e.symm.continuous
  have hψcont : Continuous ψ := by
    dsimp [ψ]
    exact hθsmooth.continuous.comp hcoordCont
  have hcoordsPt (p : Coord F) (hp : p ∈ posSet F) :
      coordsX F (ptX F p) = p := by
    let q : {p : Coord F // p ∈ posSet F} := ⟨p, hp⟩
    calc
      coordsX F (ptX F p) = (e.symm (ptX F p)).1 := (hecoords _).symm
      _ = (e.symm (e q)).1 := by rw [← hept q]
      _ = p := by simp [q]
  have hψsmooth : IsSmoothRealX F ψ := by
    unfold IsSmoothRealX
    apply hθsmooth.contDiffOn.congr
    intro p hp
    simp [ψ, hcoordsPt p hp]
  have hψnonneg : ∀ z, 0 ≤ ψ z := by
    intro z
    exact hθnonneg (coordsX F z)
  let S : Set (X F) := Set.range (fun p : {q : Coord F // q ∈ tsupport θ} =>
    e ⟨p.1, hθsupport p.2⟩)
  have hScompact : IsCompact S := by
    have hsub : IsCompact (Set.univ : Set {q : Coord F // q ∈ tsupport θ}) :=
      (isCompact_iff_isCompact_univ).mp hθcompact
    have hcont : Continuous (fun p : {q : Coord F // q ∈ tsupport θ} =>
        e ⟨p.1, hθsupport p.2⟩) := by
      apply e.continuous.comp
      exact Continuous.subtype_mk continuous_subtype_val (fun p => hθsupport p.2)
    simpa [S, Set.image_univ] using hsub.image hcont
  have hψsupport : {z | (ψ z : ℂ) ≠ 0} ⊆ S := by
    intro z hz
    have hzθ : θ (coordsX F z) ≠ 0 := by
      intro hz0
      apply hz
      simp [ψ, hz0]
    have hcoords : coordsX F z ∈ tsupport θ := subset_tsupport _ hzθ
    let p : {q : Coord F // q ∈ tsupport θ} := ⟨coordsX F z, hcoords⟩
    have heq : e ⟨p.1, hθsupport p.2⟩ = z := by
      have hz' := congrArg e (show e.symm z = ⟨p.1, hθsupport p.2⟩ from by
        apply Subtype.ext
        exact hecoords z)
      simpa using hz'.symm
    exact ⟨p, heq⟩
  have hUopen : IsOpen {z | 0 < ψ z} := isOpen_lt continuous_const hψcont
  have hKU : K ⊆ {z | 0 < ψ z} := by
    intro z hz
    have hpC : (e.symm z).1 ∈ C := ⟨z, hz, rfl⟩
    have hcoord : coordsX F z = (e.symm z).1 := hecoords z |>.symm
    change 0 < θ (coordsX F z)
    rw [hcoord]
    exact hθpositive hpC
  refine ⟨ψ, hψsmooth, ⟨S, hScompact, hψsupport⟩, hψnonneg,
    {z | 0 < ψ z}, hUopen, hKU, ?_⟩
  intro z hz
  exact hz

private theorem t2_posSet_open : IsOpen (posSet F) := by
  letI : Finite (InfinitePlace F) := inferInstance
  rw [show posSet F = ⋂ w : InfinitePlace F, {p : Coord F | 0 < (p w).2} by
    ext p
    simp [posSet]]
  exact isOpen_iInter_of_finite fun w => by
    have hcont : Continuous (fun p : Coord F => (p w).2) := by fun_prop
    exact isOpen_lt continuous_const hcont

private theorem t2_compact_neighborhood (z : X F) :
    ∃ U K : Set (X F), IsOpen U ∧ z ∈ U ∧ IsCompact K ∧ U ⊆ K := by
  classical
  obtain ⟨e, _, hecoords⟩ := t2_chartEquiv (F := F)
  let p : Coord F := (e.symm z).1
  have hp : p ∈ posSet F := (e.symm z).2
  have hpn : posSet F ∈ nhds p := (t2_posSet_open (F := F)).mem_nhds hp
  obtain ⟨r, hr, hball⟩ := Euclidean.nhds_basis_closedBall.mem_iff.mp hpn
  let B : Set (Coord F) := Euclidean.closedBall p r
  have hBcompact : IsCompact B := Euclidean.isCompact_closedBall
  let Pos := {q : Coord F // q ∈ posSet F}
  let Bsub := {q : Coord F // q ∈ B}
  let f : Bsub → Pos := fun q => ⟨q.1, hball q.2⟩
  have hf : Continuous f := by
    exact Continuous.subtype_mk continuous_subtype_val (fun q => hball q.2)
  let j : Bsub → X F := fun q => e (f q)
  have hj : Continuous j := e.continuous.comp hf
  have hKcompact : IsCompact (Set.range j) := by
    have hsub : IsCompact (Set.univ : Set Bsub) :=
      (isCompact_iff_isCompact_univ).mp hBcompact
    simpa [j, Set.image_univ] using hsub.image hj
  let U : Set (X F) := {x | coordsX F x ∈ Euclidean.ball p r}
  have hcoordCont : Continuous (coordsX F) := by
    rw [← funext hecoords]
    exact continuous_subtype_val.comp e.symm.continuous
  have hUopen : IsOpen U := hcoordCont.isOpen_preimage _ Euclidean.isOpen_ball
  have hzU : z ∈ U := by
    have hzcoord : coordsX F z = p := (hecoords z).symm
    change coordsX F z ∈ Euclidean.ball p r
    rw [hzcoord]
    exact Metric.mem_ball_self hr
  refine ⟨U, Set.range j, hUopen, hzU, hKcompact, ?_⟩
  intro x hx
  have hxball : coordsX F x ∈ Euclidean.closedBall p r :=
    (Euclidean.ball_subset_closedBall hx)
  let q : Pos := e.symm x
  have hqcoord : q.1 = coordsX F x := hecoords x
  let qB : Bsub := ⟨q.1, by simpa [B, hqcoord] using hxball⟩
  have hfq : f qB = q := by
    apply Subtype.ext
    rfl
  refine ⟨qB, ?_⟩
  change e (f qB) = x
  rw [hfq]
  exact e.apply_symm_apply x

private theorem t2_h3_herm_action (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (g : SL(2,ℂ)) (z : H3) :
    herm (g • z) = (g : Matrix (Fin 2) (Fin 2) ℂ) * herm z * star (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  rcases G1_h3_basics (F := F) with ⟨_, _, _, hherm, _, _, _, _, _, _, _, _⟩
  exact hherm g z

private theorem t2_herm_pt_entries (x : ℂ) (y : ℝ) (hy : 0 < y) :
    herm (pt x y) 0 0 = ((Complex.normSq x / y + y : ℝ) : ℂ) ∧
    herm (pt x y) 0 1 = x / y ∧
    herm (pt x y) 1 0 = star x / y ∧
    herm (pt x y) 1 1 = ((1 / y : ℝ) : ℂ) := by
  have hsqrt : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have hsqrt4 : Real.sqrt y ^ 4 = y ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsqrt]
  have hsqrtC : (Real.sqrt y : ℂ) ^ 2 = (y : ℂ) := by exact_mod_cast hsqrt
  have hsqrt4C : (Real.sqrt y : ℂ) ^ 4 = (y : ℂ) ^ 2 := by exact_mod_cast hsqrt4
  have hsqrt_ne : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  constructor
  · simp only [pt, dif_pos hy]
    change (((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
      star ((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = _
    simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Complex.normSq_eq_conj_mul_self]
    push_cast
    by_cases hx : x = 0
    · subst x
      exact (by simpa [pow_two] using hsqrtC)
    · have hstar : star x ≠ 0 := by simpa using hx
      field_simp [hsqrt_ne, hy.ne', hx, hstar]
      rw [hsqrt4C, hsqrtC]
      ring_nf
  constructor
  · simp only [pt, dif_pos hy]
    change (((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
      star ((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 = _
    simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    push_cast
    by_cases hx : x = 0
    · subst x
      simp
    · field_simp [hsqrt_ne, hy.ne', hx]
      exact hsqrtC.symm
  constructor
  · simp only [pt, dif_pos hy]
    change (((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
      star ((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) 1 0 = _
    simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    push_cast
    by_cases hx : x = 0
    · subst x
      simp
    · have hstar : star x ≠ 0 := by simpa using hx
      field_simp [hsqrt_ne, hy.ne', hstar]
      rw [hsqrtC]
      ring_nf
  · simp only [pt, dif_pos hy]
    change (((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
      star ((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) 1 1 = _
    simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    push_cast
    field_simp [hsqrt_ne, hy.ne']
    exact hsqrtC.symm

private theorem t2_horiz_action_pt (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (g : SL(2,ℂ)) (x : ℂ) (y : ℝ) (hy : 0 < y) :
    horiz (g • pt x y) =
      (((g 0 0 * x + g 0 1) * star (g 1 0 * x + g 1 1) +
        g 0 0 * star (g 1 0) * (y : ℂ) ^ 2) /
        (Complex.normSq (g 1 0 * x + g 1 1) + Complex.normSq (g 1 0) * y ^ 2 : ℝ) : ℂ) := by
  let den : ℝ := Complex.normSq (g 1 0 * x + g 1 1) + Complex.normSq (g 1 0) * y ^ 2
  have hden : den ≠ 0 := by
    intro hzero
    have hheight := (G1_h3_basics (F := F)).2.2.1 g x y hy
    have hpositive : 0 < height (g • pt x y) := by
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos _
    rw [hheight] at hpositive
    change 0 < y / den at hpositive
    rw [hzero] at hpositive
    simp at hpositive
  have hherm := t2_h3_herm_action F g (pt x y)
  rcases t2_herm_pt_entries x y hy with ⟨h00, h01, h10, h11⟩
  have hnormx : (Complex.normSq x : ℂ) = star x * x := by
    simpa [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := x))
  have h01value :
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * herm (pt x y) *
          star (g : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 =
        ((g 0 0 * x + g 0 1) * star (g 1 0 * x + g 1 1) +
          g 0 0 * star (g 1 0) * (y : ℂ) ^ 2) / (y : ℂ) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, h00, h01, h10, h11]
    push_cast
    simp only [Complex.star_def, map_add, map_mul]
    rw [hnormx]
    field_simp [hy.ne']
    simp only [starRingEnd_apply]
    ring
  have h11value :
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * herm (pt x y) *
          star (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 1 =
        ((Complex.normSq (g 1 0 * x + g 1 1) +
          Complex.normSq (g 1 0) * y ^ 2 : ℝ) : ℂ) / (y : ℂ) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, h00, h01, h10, h11]
    push_cast
    simp only [Complex.star_def, map_add, map_mul, Complex.normSq_eq_conj_mul_self]
    field_simp [hy.ne']
    ring_nf
  rw [horiz, hherm, h01value, h11value]
  field_simp [den, hden, hy.ne']
  <;> ring_nf

private theorem t2_action_den_pos (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (g : SL(2,ℂ)) (x : ℂ) (y : ℝ) (hy : 0 < y) :
    0 < Complex.normSq (g 1 0 * x + g 1 1) + Complex.normSq (g 1 0) * y ^ 2 := by
  let d := Complex.normSq (g 1 0 * x + g 1 1) + Complex.normSq (g 1 0) * y ^ 2
  have hheight := (G1_h3_basics (F := F)).2.2.1 g x y hy
  have hpos : 0 < height (g • pt x y) := by
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos _
  rw [hheight] at hpos
  have hdne : d ≠ 0 := by
    intro hd
    change 0 < y / d at hpos
    rw [hd] at hpos
    simp at hpos
  have hdn : 0 ≤ d := by
    dsimp [d]
    exact add_nonneg (Complex.normSq_nonneg _)
      (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))
  exact lt_of_le_of_ne hdn (Ne.symm hdne)

private def t2_actionCoordAt (g : SL(2,ℂ)) (q : ℂ × ℝ) : ℂ × ℝ :=
  let x := q.1
  let y := q.2
  let d := Complex.normSq (g 1 0 * x + g 1 1) + Complex.normSq (g 1 0) * y ^ 2
  (((g 0 0 * x + g 0 1) * star (g 1 0 * x + g 1 1) +
      g 0 0 * star (g 1 0) * (y : ℂ) ^ 2) / (d : ℂ), y / d)

private def t2_actionCoord (γ : SL(2,𝓞 F)) (p : Coord F) : Coord F :=
  fun w => t2_actionCoordAt (toInf F (toSLF F γ) w) (p w)

private theorem t2_action_coords (γ : SL(2,𝓞 F)) (p : Coord F) (hp : p ∈ posSet F) :
    coordsX F (γ • ptX F p) = t2_actionCoord γ p := by
  funext w
  have hy : 0 < (p w).2 := hp w
  change (horiz ((toInf F (toSLF F γ) w) • pt (p w).1 (p w).2),
      height ((toInf F (toSLF F γ) w) • pt (p w).1 (p w).2)) = _
  rw [t2_horiz_action_pt F (toInf F (toSLF F γ) w) (p w).1 (p w).2 hy,
    (G1_h3_basics (F := F)).2.2.1 (toInf F (toSLF F γ) w) (p w).1 (p w).2 hy]
  rfl

private theorem t2_contDiff_normSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun q => Complex.normSq (f q)) := by
  rw [show (fun q => Complex.normSq (f q)) =
      fun q => (Complex.reCLM (f q)) ^ 2 + (Complex.imCLM (f q)) ^ 2 by
    funext q
    rw [Complex.normSq_apply]
    simp only [Complex.reCLM_apply, Complex.imCLM_apply]
    ring]
  exact (Complex.reCLM.contDiff.comp hf).pow 2 |>.add
    ((Complex.imCLM.contDiff.comp hf).pow 2)

private theorem t2_actionCoordAt_contDiff (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (g : SL(2,ℂ)) :
    ContDiffOn ℝ ∞ (fun q : ℂ × ℝ => t2_actionCoordAt g q) {q | 0 < q.2} := by
  have hden (q : ℂ × ℝ) (hq : 0 < q.2) :
      Complex.normSq (g 1 0 * q.1 + g 1 1) + Complex.normSq (g 1 0) * q.2 ^ 2 ≠ 0 :=
    (t2_action_den_pos F g q.1 q.2 hq).ne'
  let a : ℂ × ℝ → ℂ := fun q => g 1 0 * q.1 + g 1 1
  let b : ℂ × ℝ → ℂ := fun q => g 0 0 * q.1 + g 0 1
  let d : ℂ × ℝ → ℝ := fun q => Complex.normSq (a q) + Complex.normSq (g 1 0) * q.2 ^ 2
  let n : ℂ × ℝ → ℂ := fun q => b q * star (a q) +
    g 0 0 * star (g 1 0) * (q.2 : ℂ) ^ 2
  have ha : ContDiff ℝ ∞ a := by fun_prop
  have hb : ContDiff ℝ ∞ b := by fun_prop
  have hstarA : ContDiff ℝ ∞ (fun q => star (a q)) := by
    change ContDiff ℝ ∞ (Complex.conjCLE ∘ a)
    exact Complex.conjCLE.contDiff.comp ha
  have hnormA : ContDiff ℝ ∞ (fun q => Complex.normSq (a q)) :=
    t2_contDiff_normSq ha
  have hnormC : ContDiff ℝ ∞ (fun _ : ℂ × ℝ => Complex.normSq (g 1 0)) := contDiff_const
  have hq2 : ContDiff ℝ ∞ (fun q : ℂ × ℝ => q.2 ^ 2) := by fun_prop
  have hd : ContDiff ℝ ∞ d := by
    dsimp [d]
    exact hnormA.add (hnormC.mul hq2)
  have hq : ContDiff ℝ ∞ (fun q : ℂ × ℝ => q.2) := by fun_prop
  have hqC : ContDiff ℝ ∞ (fun q : ℂ × ℝ => (q.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hq
  have hqC2 : ContDiff ℝ ∞ (fun q : ℂ × ℝ => (q.2 : ℂ) ^ 2) := hqC.pow 2
  have hconst : ContDiff ℝ ∞ (fun _ : ℂ × ℝ => g 0 0 * star (g 1 0)) := contDiff_const
  have hn : ContDiff ℝ ∞ n := by
    dsimp [n]
    exact (hb.mul hstarA).add (hconst.mul hqC2)
  have hdc : ContDiff ℝ ∞ (fun q => (d q : ℂ)) := Complex.ofRealCLM.contDiff.comp hd
  have hdcInv : ContDiffOn ℝ ∞ (fun q => ((d q : ℂ)⁻¹)) {q | 0 < q.2} :=
    ContDiffOn.inv hdc.contDiffOn (by
      intro q hq
      have hqden : d q ≠ 0 := by simpa [d, a] using hden q hq
      exact_mod_cast hqden)
  have hfirst : ContDiffOn ℝ ∞ (fun q => n q / (d q : ℂ)) {q | 0 < q.2} := by
    simpa only [div_eq_mul_inv] using hn.contDiffOn.mul hdcInv
  have hsecond : ContDiffOn ℝ ∞ (fun q : ℂ × ℝ => q.2 / d q) {q | 0 < q.2} := by
    exact ContDiffOn.div (s := {q : ℂ × ℝ | 0 < q.2})
      (f := fun q : ℂ × ℝ => q.2) (g := d) hq.contDiffOn hd.contDiffOn (by
        intro q hq
        simpa [d, a] using hden q hq)
  simpa [t2_actionCoordAt, d, n, a, b] using hfirst.prodMk hsecond

private theorem t2_actionCoord_contDiff (γ : SL(2,𝓞 F)) :
    ContDiffOn ℝ ∞ (t2_actionCoord γ) (posSet F) := by
  classical
  rw [contDiffOn_pi]
  intro w
  have hAt := t2_actionCoordAt_contDiff F (toInf F (toSLF F γ) w)
  exact hAt.comp (by fun_prop) (by intro p hp; exact hp w)

private theorem t2_actionCoord_mem_pos (γ : SL(2,𝓞 F)) (p : Coord F)
    (hp : p ∈ posSet F) : t2_actionCoord γ p ∈ posSet F := by
  intro w
  change 0 < (t2_actionCoordAt (toInf F (toSLF F γ) w) (p w)).2
  simpa [t2_actionCoordAt] using div_pos (hp w)
    (t2_action_den_pos F (toInf F (toSLF F γ) w) (p w).1 (p w).2 (hp w))

private theorem t2_translate_smooth (Γ : Subgroup SL(2,𝓞 F)) (γ : Γ)
    (ψ : X F → ℝ) (hψ : IsSmoothRealX F ψ) :
    IsSmoothRealX F (fun z => ψ ((γ : SL(2,𝓞 F)) • z)) := by
  unfold IsSmoothRealX at hψ ⊢
  have hcomp := hψ.comp (t2_actionCoord_contDiff (γ : SL(2,𝓞 F)))
    (fun p hp => t2_actionCoord_mem_pos (γ : SL(2,𝓞 F)) p hp)
  rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, hptcoords, _, _, _, _⟩
  apply hcomp.congr
  intro p hp
  have hcoords := t2_action_coords (γ : SL(2,𝓞 F)) p hp
  have hpt : ptX F (t2_actionCoord (γ : SL(2,𝓞 F)) p) =
      (γ : SL(2,𝓞 F)) • ptX F p := by
    calc
      ptX F (t2_actionCoord (γ : SL(2,𝓞 F)) p) =
          ptX F (coordsX F ((γ : SL(2,𝓞 F)) • ptX F p)) := by rw [← hcoords]
      _ = (γ : SL(2,𝓞 F)) • ptX F p := hptcoords _
  change ψ ((γ : SL(2,𝓞 F)) • ptX F p) =
    ψ (ptX F (t2_actionCoord (γ : SL(2,𝓞 F)) p))
  rw [hpt]

private theorem t2_translate_locally_finite (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (ψ : X F → ℝ) (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ))) :
    ∀ z, ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧
      {γ : Γ | ∃ x ∈ U, ψ ((γ : SL(2,𝓞 F)) • x) ≠ 0}.Finite := by
  classical
  rcases hψcompact with ⟨K, hK, hSupport⟩
  let d : SiegelData F Γ := Classical.choice (t1_siegelData_nonempty (F := F) Γ)
  have hproper := (R9_proper Γ d).1
  intro z
  rcases t2_compact_neighborhood (F := F) z with ⟨U, V, hUopen, hzU, hV, hUV⟩
  have hSL : {g : SL(2,𝓞 F) | ∃ x ∈ V, g • x ∈ K}.Finite := hproper V K hV hK
  have hfinite : ({γ : Γ | ∃ x ∈ V, (γ : SL(2,𝓞 F)) • x ∈ K} : Set Γ).Finite := by
    let e : Γ ↪ SL(2,𝓞 F) := ⟨Subtype.val, Subtype.val_injective⟩
    simpa [e] using hSL.preimage_embedding e
  refine ⟨U, hUopen, hzU, hfinite.subset ?_⟩
  intro γ hγ
  rcases hγ with ⟨x, hxU, hψne⟩
  refine ⟨x, hUV hxU, hSupport ?_⟩
  change (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ) ≠ 0
  exact_mod_cast hψne

open scoped Pointwise in
private theorem t2_orbitSaturation_closed (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (K : Set (X F)) (hK : IsCompact K) : IsClosed (orbitSaturation F Γ K) := by
  classical
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have d : SiegelData F Γ := Classical.choice (t1_siegelData_nonempty (F := F) Γ)
  have hproper := (R9_proper Γ d).1
  rcases t2_compact_neighborhood (F := F) z with
    ⟨N, Cpt, hN, hzN, hCpt, hNCpt⟩
  have hSL : {g : SL(2,𝓞 F) | ∃ x ∈ Cpt, g • x ∈ K}.Finite :=
    hproper Cpt K hCpt hK
  obtain ⟨chart, hept, _⟩ := t2_chartEquiv (F := F)
  let Pos := {p : Coord F // p ∈ posSet F}
  letI : T2Space Pos := inferInstance
  letI : T2Space (X F) := chart.t2Space
  have hActionCont (γ : Γ) : Continuous (fun x : X F => (γ : SL(2,𝓞 F)) • x) := by
    let A := t2_actionCoord (γ : SL(2,𝓞 F))
    have hApos (p : Coord F) (hp : p ∈ posSet F) : A p ∈ posSet F :=
      t2_actionCoord_mem_pos (γ : SL(2,𝓞 F)) p hp
    have hAcont : ContinuousOn A (posSet F) :=
      (t2_actionCoord_contDiff (γ : SL(2,𝓞 F))).continuousOn
    have hAcontSub : Continuous (fun p : Pos => A p.1) :=
      continuousOn_univ.mp (hAcont.comp continuous_subtype_val.continuousOn
        (by intro p hp; exact p.2))
    let c : Pos → Pos := fun p => ⟨A p.1, hApos p.1 p.2⟩
    have hc : Continuous c := by
      exact Continuous.subtype_mk hAcontSub (fun p => hApos p.1 p.2)
    have hfactor : (fun x : X F => (γ : SL(2,𝓞 F)) • x) = chart ∘ c ∘ chart.symm := by
      funext x
      let p : Pos := chart.symm x
      have hcoords := t2_action_coords (γ : SL(2,𝓞 F)) p.1 p.2
      have hpt : ptX F (A p.1) = (γ : SL(2,𝓞 F)) • ptX F p.1 := by
        have hptcoords := (G1_h3_basics (F := F)).2.2.2.2.2.2.2.1
        calc
          ptX F (A p.1) = ptX F (coordsX F ((γ : SL(2,𝓞 F)) • ptX F p.1)) := by
            change ptX F (t2_actionCoord (γ : SL(2,𝓞 F)) p.1) = _
            rw [← hcoords]
          _ = (γ : SL(2,𝓞 F)) • ptX F p.1 := hptcoords _
      have heq : chart (c p) = (γ : SL(2,𝓞 F)) • chart p := by
        calc
          chart (c p) = ptX F (A p.1) := hept (c p)
          _ = (γ : SL(2,𝓞 F)) • ptX F p.1 := hpt
          _ = (γ : SL(2,𝓞 F)) • chart p := by rw [hept]
      simpa [p, heq]
    rw [hfactor]
    exact chart.continuous.comp (hc.comp chart.symm.continuous)
  let e : Γ ↪ SL(2,𝓞 F) :=
    ⟨fun γ => ((γ⁻¹ : Γ) : SL(2,𝓞 F)), by
      intro γ γ' h
      apply inv_injective
      exact Subtype.ext h⟩
  let S : Set Γ := {γ | ∃ x ∈ Cpt, ((γ⁻¹ : Γ) : SL(2,𝓞 F)) • x ∈ K}
  have hS : S.Finite := by
    have hpre := hSL.preimage_embedding e
    simpa [S, e] using hpre
  let C : Set (X F) := ⋃ γ ∈ hS.toFinset, (γ : SL(2,𝓞 F)) • K
  have hCclosed : IsClosed C := by
    apply isClosed_biUnion_finset
    intro γ hγ
    have himage : IsCompact ((γ : SL(2,𝓞 F)) • K) := by
      exact hK.image (hActionCont γ)
    exact himage.isClosed
  have hzC : z ∉ C := by
    intro hzC
    rcases Set.mem_iUnion.1 hzC with ⟨γ, hγ⟩
    rcases Set.mem_iUnion.1 hγ with ⟨hγT, hzγK⟩
    have hzK : ((γ⁻¹ : Γ) : SL(2,𝓞 F)) • z ∈ K :=
      (Set.mem_smul_set_iff_inv_smul_mem).mp hzγK
    apply hz
    refine ⟨γ, ((γ⁻¹ : Γ) : SL(2,𝓞 F)) • z, hzK, ?_⟩
    simp
  have hcover : N ∩ orbitSaturation F Γ K ⊆ C := by
    rintro x ⟨hxN, ⟨γ, y, hyK, hxy⟩⟩
    have hinv : ((γ⁻¹ : Γ) : SL(2,𝓞 F)) • x = y := by
      calc
        _ = ((γ⁻¹ : Γ) : SL(2,𝓞 F)) • ((γ : SL(2,𝓞 F)) • y) := by rw [hxy]
        _ = (((γ⁻¹ : Γ) : SL(2,𝓞 F)) * (γ : SL(2,𝓞 F))) • y := by rw [mul_smul]
        _ = y := by simp
    have hγS : γ ∈ S := ⟨x, hNCpt hxN, by rw [hinv]; exact hyK⟩
    change x ∈ ⋃ δ ∈ hS.toFinset, (δ : SL(2,𝓞 F)) • K
    exact Set.mem_iUnion.2 ⟨γ, Set.mem_iUnion.2
      ⟨hS.mem_toFinset.mpr hγS, Set.mem_smul_set.mpr ⟨y, hyK, hxy⟩⟩⟩
  apply Filter.mem_of_superset ((hN.inter hCclosed.isOpen_compl).mem_nhds ⟨hzN, hzC⟩)
  intro x hx
  change x ∉ orbitSaturation F Γ K
  intro hxsat
  exact hx.2 (hcover ⟨hx.1, hxsat⟩)

private def t2_periodize (Γ : Subgroup SL(2,𝓞 F)) (ψ : X F → ℝ) : X F → ℝ :=
  fun z => ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z)

private theorem t2_periodize_smul (Γ : Subgroup SL(2,𝓞 F)) (ψ : X F → ℝ)
    (δ : Γ) (z : X F) : t2_periodize Γ ψ ((δ : SL(2,𝓞 F)) • z) =
      t2_periodize Γ ψ z := by
  classical
  let t : Γ → ℝ := fun γ => ψ ((γ : SL(2,𝓞 F)) • z)
  change (∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • ((δ : SL(2,𝓞 F)) • z))) =
    ∑' γ : Γ, t γ
  calc
    (∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • ((δ : SL(2,𝓞 F)) • z))) =
        ∑' γ : Γ, t (γ * δ) := by
      apply tsum_congr
      intro γ
      simp [t, smul_smul, Subgroup.coe_mul]
    _ = ∑' γ : Γ, t γ := (Equiv.mulRight δ).tsum_eq t

private theorem t2_periodize_eq_sum (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (ψ : X F → ℝ) (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ))) (z : X F) :
    ∃ T : Finset Γ,
      t2_periodize Γ ψ z = ∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • z) ∧
      ∀ γ ∉ T, ψ ((γ : SL(2,𝓞 F)) • z) = 0 := by
  classical
  rcases t2_translate_locally_finite Γ ψ hψcompact z with ⟨U, hU, hzU, hfinite⟩
  let T := hfinite.toFinset
  have hzero (γ : Γ) (hγ : γ ∉ T) : ψ ((γ : SL(2,𝓞 F)) • z) = 0 := by
    by_contra hne
    have hmem : γ ∈ {γ : Γ | ∃ x ∈ U, ψ ((γ : SL(2,𝓞 F)) • x) ≠ 0} :=
      ⟨z, hzU, hne⟩
    apply hγ
    simpa [T] using hmem
  refine ⟨T, ?_, hzero⟩
  rw [t2_periodize]
  exact tsum_eq_sum (s := T) hzero

private theorem t2_periodize_smooth (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (ψ : X F → ℝ) (hψ : IsSmoothRealX F ψ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ))) :
    IsSmoothRealX F (t2_periodize Γ ψ) := by
  classical
  obtain ⟨e, hept, _⟩ := t2_chartEquiv (F := F)
  unfold IsSmoothRealX
  intro p hp
  let Pos := {q : Coord F // q ∈ posSet F}
  let p' : Pos := ⟨p, hp⟩
  rcases t2_translate_locally_finite Γ ψ hψcompact (ptX F p) with
    ⟨U, hU, hpU, hfinite⟩
  let V : Set Pos := {q | e q ∈ U}
  have hV : IsOpen V := hU.preimage e.continuous
  let W : Set (Coord F) := Subtype.val '' V
  have hW : IsOpen W := by
    change IsOpen (Subtype.val '' V)
    exact (t2_posSet_open (F := F)).isOpenMap_subtype_val V hV
  have hpW : p ∈ W := by
    refine ⟨p', ?_, rfl⟩
    change e p' ∈ U
    rw [hept]
    exact hpU
  have hptU : ∀ q ∈ W, ptX F q ∈ U := by
    intro q hq
    rcases hq with ⟨q', hqV, hqeq⟩
    change e q' ∈ U at hqV
    have hqcoord : q'.1 = q := hqeq
    rw [← hqcoord, ← hept q']
    exact hqV
  let T := hfinite.toFinset
  have hzero (q : Coord F) (hq : q ∈ W) (γ : Γ) (hγ : γ ∉ T) :
      ψ ((γ : SL(2,𝓞 F)) • ptX F q) = 0 := by
    have hγnot : γ ∉ {γ : Γ | ∃ x ∈ U,
        ψ ((γ : SL(2,𝓞 F)) • x) ≠ 0} := by
      intro hmem
      apply hγ
      simpa [T] using hmem
    by_contra hne
    exact hγnot ⟨ptX F q, hptU q hq, hne⟩
  have heq (q : Coord F) (hq : q ∈ W) :
      t2_periodize Γ ψ (ptX F q) =
        ∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • ptX F q) := by
    rw [t2_periodize]
    exact tsum_eq_sum (s := T) (fun γ hγ => hzero q hq γ hγ)
  have hsum : ContDiffOn ℝ ∞
      (fun q : Coord F => ∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • ptX F q)) (posSet F) := by
    apply ContDiffOn.sum
    intro γ hγ
    exact t2_translate_smooth Γ γ ψ hψ
  have hWevent : ∀ᶠ q in nhdsWithin p (posSet F), q ∈ W :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hW.mem_nhds hpW)
  have hEq : (fun q : Coord F => t2_periodize Γ ψ (ptX F q)) =ᶠ[
      nhdsWithin p (posSet F)]
      (fun q => ∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • ptX F q)) := by
    filter_upwards [hWevent] with q hq
    exact heq q hq
  exact (hsum p hp).congr_of_eventuallyEq hEq (heq p hpW)

private theorem t2_periodize_continuous (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (ψ : X F → ℝ) (hψ : IsSmoothRealX F ψ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ))) :
    Continuous (t2_periodize Γ ψ) := by
  classical
  obtain ⟨e, hept, _⟩ := t2_chartEquiv (F := F)
  have hcoord := t2_periodize_smooth Γ ψ hψ hψcompact
  have hcoordCont : ContinuousOn (fun p : Coord F => t2_periodize Γ ψ (ptX F p))
      (posSet F) := hcoord.continuousOn
  let Pos := {p : Coord F // p ∈ posSet F}
  have hchart₀ : ContinuousOn (fun p : Pos => t2_periodize Γ ψ (ptX F p.1)) Set.univ :=
    hcoordCont.comp continuous_subtype_val.continuousOn (by intro p hp; exact p.2)
  have hchart₀ : Continuous (fun p : Pos => t2_periodize Γ ψ (ptX F p.1)) :=
    continuousOn_univ.mp hchart₀
  have hchart : Continuous (fun p : Pos => t2_periodize Γ ψ (e p)) := by
    convert hchart₀ using 1
    funext p
    rw [hept]
  have hdecomp : t2_periodize Γ ψ = (fun p : Pos => t2_periodize Γ ψ (e p)) ∘ e.symm := by
    funext z
    simp
  rw [hdecomp]
  exact hchart.comp e.symm.continuous

private theorem t2_periodize_nonneg (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (ψ : X F → ℝ) (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ)))
    (hψnonneg : ∀ z, 0 ≤ ψ z) (z : X F) : 0 ≤ t2_periodize Γ ψ z := by
  rcases t2_periodize_eq_sum Γ ψ hψcompact z with ⟨T, hsum, _⟩
  rw [hsum]
  exact Finset.sum_nonneg fun γ hγ => hψnonneg ((γ : SL(2,𝓞 F)) • z)

private theorem t2_periodize_pos (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (ψ : X F → ℝ) (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ)))
    (hψnonneg : ∀ z, 0 ≤ ψ z) {z : X F} (hψpos : 0 < ψ z) :
    0 < t2_periodize Γ ψ z := by
  rcases t2_periodize_eq_sum Γ ψ hψcompact z with ⟨T, hsum, hzero⟩
  have hone : (1 : Γ) ∈ T := by
    by_contra hnot
    have hzero' := hzero 1 hnot
    have hzero'' : ψ z = 0 := by simpa using hzero'
    exact (ne_of_gt hψpos) hzero''
  rw [hsum]
  exact Finset.sum_pos' (s := T)
    (fun γ hγ => hψnonneg ((γ : SL(2,𝓞 F)) • z))
    ⟨1, hone, by simpa using hψpos⟩

private def t2_cutoffBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : ℝ) :=
  ⟨δ / 3, δ / 2, by positivity, by linarith⟩

private def t2_cutoffEta (δ : ℝ) (hδ : 0 < δ) : ℝ → ℝ :=
  fun t => 1 - t2_cutoffBump δ hδ t

private theorem t2_cutoffEta_smooth (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (t2_cutoffEta δ hδ) := by
  exact contDiff_const.sub (t2_cutoffBump δ hδ).contDiff

private theorem t2_cutoffEta_nonneg (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    0 ≤ t2_cutoffEta δ hδ t := by
  dsimp [t2_cutoffEta]
  linarith [(t2_cutoffBump δ hδ).le_one (x := t)]

private theorem t2_cutoffEta_zero (δ : ℝ) (hδ : 0 < δ) {t : ℝ}
    (ht : t ∈ Metric.closedBall 0 (δ / 3)) : t2_cutoffEta δ hδ t = 0 := by
  simp [t2_cutoffEta, (t2_cutoffBump δ hδ).one_of_mem_closedBall ht]

private theorem t2_cutoffEta_one (δ : ℝ) (hδ : 0 < δ) {t : ℝ}
    (ht : δ / 2 ≤ t) : t2_cutoffEta δ hδ t = 1 := by
  let b := t2_cutoffBump δ hδ
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hdist : b.rOut ≤ dist t 0 := by
    change δ / 2 ≤ dist t 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    exact ht
  rw [t2_cutoffEta, b.zero_of_le_dist hdist]
  simp

private def t2_cutoffRecip (δ : ℝ) (hδ : 0 < δ) : ℝ → ℝ :=
  fun t => if 0 < t then t2_cutoffEta δ hδ t / t else 0

private theorem t2_cutoffRecip_smooth (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (t2_cutoffRecip δ hδ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < δ / 3
  · have hev : (t2_cutoffRecip δ hδ) =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
      by_cases hspos : 0 < s
      · have hsball : s ∈ Metric.closedBall (0 : ℝ) (δ / 3) := by
          change dist s 0 ≤ δ / 3
          rw [Real.dist_eq, sub_zero, abs_of_pos hspos]
          exact hs.le
        simp [t2_cutoffRecip, hspos, t2_cutoffEta_zero δ hδ hsball]
      · simp [t2_cutoffRecip, hspos]
    exact contDiff_const.contDiffAt.congr_of_eventuallyEq hev
  · have htpos : 0 < t := by
      have hδ3 : 0 < δ / 3 := by positivity
      exact lt_of_lt_of_le hδ3 (le_of_not_gt ht)
    have hquot : ContDiffAt ℝ ∞ (fun s : ℝ => t2_cutoffEta δ hδ s / s) t :=
      (t2_cutoffEta_smooth δ hδ).contDiffAt.div contDiff_id.contDiffAt htpos.ne'
    have hev : (t2_cutoffRecip δ hδ) =ᶠ[nhds t]
        fun s => t2_cutoffEta δ hδ s / s := by
      filter_upwards [isOpen_Ioi.mem_nhds htpos] with s hs
      change 0 < s at hs
      change (if 0 < s then t2_cutoffEta δ hδ s / s else 0) =
        t2_cutoffEta δ hδ s / s
      rw [if_pos hs]
    exact hquot.congr_of_eventuallyEq hev

private theorem t2_cutoffRecip_nonneg (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    0 ≤ t2_cutoffRecip δ hδ t := by
  by_cases ht : 0 < t
  · simp [t2_cutoffRecip, ht, div_nonneg (t2_cutoffEta_nonneg δ hδ t) ht.le]
  · simp [t2_cutoffRecip, ht]

private theorem t2_cutoffRecip_eq_inv (δ : ℝ) (hδ : 0 < δ) {t : ℝ}
    (ht : δ / 2 < t) : t2_cutoffRecip δ hδ t = t⁻¹ := by
  have htpos : 0 < t := lt_trans (by positivity) ht
  rw [t2_cutoffRecip, if_pos htpos, t2_cutoffEta_one δ hδ ht.le]
  simp


private theorem t2_partition_of_compact (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (K : Set (X F)) (hK : IsCompact K) :
    ∃ ψ : X F → ℝ,
      IsSmoothRealX F ψ ∧ HasCompactSupportX F (fun z => (ψ z : ℂ)) ∧
      (∀ z, 0 ≤ ψ z) ∧
      (∀ z, ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧
        {γ : Γ | ∃ x ∈ U, ψ ((γ : SL(2,𝓞 F)) • x) ≠ 0}.Finite) ∧
      (∃ U : Set (X F), IsOpen U ∧ orbitSaturation F Γ K ⊆ U ∧
        ∀ z ∈ U, ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) = 1) := by
  classical
  obtain ⟨ψ₀, hψ₀smooth, hψ₀compact, hψ₀nonneg, U₀, hU₀, hKU₀, hψ₀pos⟩ :=
    t2_compact_bump (F := F) K hK
  let P : X F → ℝ := t2_periodize Γ ψ₀
  have hPsmooth : IsSmoothRealX F P := by
    simpa [P] using t2_periodize_smooth Γ ψ₀ hψ₀smooth hψ₀compact
  have hPcont : Continuous P := by
    simpa [P] using t2_periodize_continuous Γ ψ₀ hψ₀smooth hψ₀compact
  have hPnonneg : ∀ z, 0 ≤ P z := by
    intro z
    exact t2_periodize_nonneg Γ ψ₀ hψ₀compact hψ₀nonneg z
  have hPpos : ∀ z ∈ K, 0 < P z := by
    intro z hz
    exact t2_periodize_pos Γ ψ₀ hψ₀compact hψ₀nonneg (hψ₀pos z (hKU₀ hz))
  obtain ⟨δ, hδ, hδle⟩ :=
    hK.exists_forall_le' hPcont.continuousOn hPpos
  let ψ : X F → ℝ := fun z => ψ₀ z * t2_cutoffRecip δ hδ (P z)
  have hPcoord : ContDiffOn ℝ ∞ (fun p : Coord F => P (ptX F p)) (posSet F) := by
    unfold IsSmoothRealX at hPsmooth
    simpa [P] using hPsmooth
  have hρcoord : ContDiffOn ℝ ∞
      (fun p : Coord F => t2_cutoffRecip δ hδ (P (ptX F p))) (posSet F) :=
    (t2_cutoffRecip_smooth δ hδ).comp_contDiffOn hPcoord
  have hψsmooth : IsSmoothRealX F ψ := by
    unfold IsSmoothRealX
    change ContDiffOn ℝ ∞
      (fun p : Coord F => ψ₀ (ptX F p) * t2_cutoffRecip δ hδ (P (ptX F p)))
      (posSet F)
    exact hψ₀smooth.mul hρcoord
  have hψnonneg : ∀ z, 0 ≤ ψ z := by
    intro z
    exact mul_nonneg (hψ₀nonneg z) (t2_cutoffRecip_nonneg δ hδ (P z))
  obtain ⟨K₀, hK₀, hψ₀support⟩ := hψ₀compact
  have hψ₀compact' : HasCompactSupportX F (fun z => (ψ₀ z : ℂ)) :=
    ⟨K₀, hK₀, hψ₀support⟩
  have hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ)) := by
    refine ⟨K₀, hK₀, ?_⟩
    intro z hz
    apply hψ₀support
    intro hzero
    apply hz
    have hzeroR : ψ₀ z = 0 := Complex.ofReal_eq_zero.mp hzero
    simp [ψ, hzeroR]
  have hlocal := t2_translate_locally_finite Γ ψ hψcompact
  let V : Set (X F) := {z | δ / 2 < P z}
  have hVopen : IsOpen V := by
    change IsOpen ((fun z => P z) ⁻¹' Set.Ioi (δ / 2))
    exact isOpen_Ioi.preimage hPcont
  have hVsat : orbitSaturation F Γ K ⊆ V := by
    rintro z ⟨γ, x, hx, rfl⟩
    change δ / 2 < t2_periodize Γ ψ₀ ((γ : SL(2,𝓞 F)) • x)
    rw [t2_periodize_smul Γ ψ₀ γ x]
    exact (half_lt_self hδ).trans_le (hδle x hx)
  refine ⟨ψ, hψsmooth, hψcompact, hψnonneg, hlocal, ⟨V, hVopen, hVsat, ?_⟩⟩
  intro z hz
  rcases t2_periodize_eq_sum Γ ψ₀ hψ₀compact' z with ⟨T, hseedSum, hseedZero⟩
  have hnormalizedZero (γ : Γ) (hγ : γ ∉ T) :
      ψ ((γ : SL(2,𝓞 F)) • z) = 0 := by
    simp [ψ, hseedZero γ hγ]
  have hnormalizedSum : t2_periodize Γ ψ z =
      ∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • z) := by
    rw [t2_periodize]
    exact tsum_eq_sum (s := T) hnormalizedZero
  have hfactorSeed :
      (∑ γ ∈ T, ψ₀ ((γ : SL(2,𝓞 F)) • z) *
        t2_cutoffRecip δ hδ (P ((γ : SL(2,𝓞 F)) • z))) =
        (∑ γ ∈ T, ψ₀ ((γ : SL(2,𝓞 F)) • z)) *
          t2_cutoffRecip δ hδ (P z) := by
    calc
      (∑ γ ∈ T, ψ₀ ((γ : SL(2,𝓞 F)) • z) *
          t2_cutoffRecip δ hδ (P ((γ : SL(2,𝓞 F)) • z))) =
        ∑ γ ∈ T, ψ₀ ((γ : SL(2,𝓞 F)) • z) * t2_cutoffRecip δ hδ (P z) := by
        apply Finset.sum_congr rfl
        intro γ hγ
        rw [show P ((γ : SL(2,𝓞 F)) • z) = P z from by
          change t2_periodize Γ ψ₀ ((γ : SL(2,𝓞 F)) • z) = t2_periodize Γ ψ₀ z
          exact t2_periodize_smul Γ ψ₀ γ z]
      _ = (∑ γ ∈ T, ψ₀ ((γ : SL(2,𝓞 F)) • z)) *
            t2_cutoffRecip δ hδ (P z) := (Finset.sum_mul _ _ _).symm
  have hfactor :
      (∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • z)) =
        (∑ γ ∈ T, ψ₀ ((γ : SL(2,𝓞 F)) • z)) *
          t2_cutoffRecip δ hδ (P z) := by
    simpa [ψ] using hfactorSeed
  change t2_periodize Γ ψ z = 1
  rw [hnormalizedSum, hfactor, ← hseedSum]
  exact t2_cutoffRecip_eq_inv δ hδ hz ▸
    mul_inv_cancel₀ (ne_of_gt (lt_trans (by positivity) hz))

private theorem t2_partition_reconstruct (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (K : Set (X F)) (ψ : X F → ℝ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ)))
    (hpartition : ∀ z ∈ orbitSaturation F Γ K,
      ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) = 1)
    (f : X F → ℂ) (hfinv : IsGammaInvariant F Γ f)
    (hfsupport : {z | f z ≠ 0} ⊆ orbitSaturation F Γ K) :
    ∀ z, f z = ∑' γ : Γ,
      (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) * f ((γ : SL(2,𝓞 F)) • z) := by
  classical
  intro z
  by_cases hz : z ∈ orbitSaturation F Γ K
  · rcases t2_translate_locally_finite Γ ψ hψcompact z with ⟨U, hU, hzU, hfinite⟩
    let T := hfinite.toFinset
    have hzero (γ : Γ) (hγ : γ ∉ T) :
        ψ ((γ : SL(2,𝓞 F)) • z) = 0 := by
      by_contra hne
      have hmem : γ ∈ {γ : Γ | ∃ x ∈ U, ψ ((γ : SL(2,𝓞 F)) • x) ≠ 0} :=
        ⟨z, hzU, hne⟩
      apply hγ
      simpa [T] using hmem
    have hsumψ : (∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • z)) = 1 := by
      calc
        (∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • z)) = t2_periodize Γ ψ z := by
          symm
          rw [t2_periodize]
          exact tsum_eq_sum (s := T) hzero
        _ = ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) := rfl
        _ = 1 := hpartition z hz
    have hsumψC : (∑ γ ∈ T, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ)) = 1 := by
      exact_mod_cast hsumψ
    have hweightedZero (γ : Γ) (hγ : γ ∉ T) :
        (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) *
          f ((γ : SL(2,𝓞 F)) • z) = 0 := by
      rw [hzero γ hγ]
      simp
    have hweightedSum :
        (∑' γ : Γ, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) *
          f ((γ : SL(2,𝓞 F)) • z)) =
        ∑ γ ∈ T, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) *
          f ((γ : SL(2,𝓞 F)) • z) := by
      rw [tsum_eq_sum (s := T) hweightedZero]
    have hfiniteSum :
        (∑ γ ∈ T, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) *
          f ((γ : SL(2,𝓞 F)) • z)) = f z := by
      calc
        _ = ∑ γ ∈ T, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) * f z := by
          apply Finset.sum_congr rfl
          intro γ hγ
          rw [hfinv γ γ.property z]
        _ = (∑ γ ∈ T, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ)) * f z :=
          (Finset.sum_mul _ _ _).symm
        _ = f z := by rw [hsumψC]; simp
    exact hfiniteSum.symm.trans hweightedSum.symm
  · have hfz : f z = 0 := by
      by_contra hne
      exact hz (hfsupport hne)
    have hzero (γ : Γ) :
        (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) *
          f ((γ : SL(2,𝓞 F)) • z) = 0 := by
      rw [hfinv γ γ.property z, hfz]
      simp
    rw [hfz]
    simp [hzero]

private theorem t2_fullGradient_continuous (f : X F → ℂ) (hf : IsSmoothX F f) :
    Continuous (fullGradient F f) := by
  classical
  obtain ⟨e, hept, _⟩ := t2_chartEquiv (F := F)
  rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, hcoordsPt, _, _, _, _, _⟩
  have hposOpen := t2_posSet_open (F := F)
  have hfcoord : ContDiffOn ℝ ∞ (fun p : Coord F => f (ptX F p)) (posSet F) := hf
  have hderiv : ContinuousOn
      (fun p : Coord F => fderiv ℝ (fun q => f (ptX F q)) p) (posSet F) :=
    hfcoord.continuousOn_fderiv_of_isOpen hposOpen (by norm_num)
  have hPi : ContinuousOn
      (fun p : Coord F => fun wj : InfinitePlace F × Fin 3 =>
        ((p wj.1).2 : ℂ) *
          (fderiv ℝ (fun q => f (ptX F q)) p (placeDirection F wj.1 wj.2)))
      (posSet F) := by
    rw [continuousOn_pi]
    intro wj
    have hy : Continuous (fun p : Coord F => ((p wj.1).2 : ℂ)) := by fun_prop
    have hderivEval : ContinuousOn
        (fun p : Coord F =>
          (fderiv ℝ (fun q => f (ptX F q)) p (placeDirection F wj.1 wj.2)))
        (posSet F) := hderiv.clm_apply continuousOn_const
    exact hy.continuousOn.mul hderivEval
  let E : InfinitePlace F × Fin 3 → Type := fun _ => ℂ
  let e' := PiLp.continuousLinearEquiv 2 ℂ E
  have hLp : ContinuousOn (fun p : Coord F => e'.symm
      (fun wj : InfinitePlace F × Fin 3 =>
        ((p wj.1).2 : ℂ) *
          (fderiv ℝ (fun q => f (ptX F q)) p (placeDirection F wj.1 wj.2))))
      (posSet F) := by
    exact e'.symm.continuous.continuousOn.comp hPi (by intro p hp; exact Set.mem_univ _)
  have hgradCoord : ContinuousOn (fun p : Coord F => fullGradient F f (ptX F p))
      (posSet F) := by
    apply hLp.congr
    intro p hp
    have hcoords := hcoordsPt p hp
    simp [fullGradient, placeGradient, hcoords, Function.comp_def, e', E,
      PiLp.coe_symm_continuousLinearEquiv]
  let Pos := {p : Coord F // p ∈ posSet F}
  have hchart₀ : ContinuousOn (fun p : Pos => fullGradient F f (ptX F p.1)) Set.univ :=
    hgradCoord.comp continuous_subtype_val.continuousOn (by intro p hp; exact p.2)
  have hchart₀ : Continuous (fun p : Pos => fullGradient F f (ptX F p.1)) :=
    continuousOn_univ.mp hchart₀
  have hchart : Continuous (fun p : Pos => fullGradient F f (e p)) := by
    convert hchart₀ using 1
    funext p
    rw [hept]
  have hdecomp : fullGradient F f =
      (fun p : Pos => fullGradient F f (e p)) ∘ e.symm := by
    funext z
    simp
  rw [hdecomp]
  exact hchart.comp e.symm.continuous

private theorem t2_fullGradient_norm_sq (f : X F → ℂ) (z : X F) :
    ‖fullGradient F f z‖ ^ 2 = totalGradNormSq F f z := by
  simp [fullGradient, totalGradNormSq, placeGradNormSq, EuclideanSpace.norm_sq_eq,
    Complex.normSq_eq_norm_sq, Fintype.sum_prod_type]

private theorem t2_smooth_continuous (f : X F → ℂ) (hf : IsSmoothX F f) :
    Continuous f := by
  classical
  obtain ⟨e, hept, _⟩ := t2_chartEquiv (F := F)
  have hfcoord : ContDiffOn ℝ ∞ (fun p : Coord F => f (ptX F p)) (posSet F) := hf
  have hfcont : ContinuousOn (fun p : Coord F => f (ptX F p)) (posSet F) :=
    hfcoord.continuousOn
  let Pos := {p : Coord F // p ∈ posSet F}
  have hchart₀ : ContinuousOn (fun p : Pos => f (ptX F p.1)) Set.univ :=
    hfcont.comp continuous_subtype_val.continuousOn (by intro p hp; exact p.2)
  have hchart₀ : Continuous (fun p : Pos => f (ptX F p.1)) :=
    continuousOn_univ.mp hchart₀
  have hchart : Continuous (fun p : Pos => f (e p)) := by
    convert hchart₀ using 1
    funext p
    rw [hept]
  have hdecomp : f = (fun p : Pos => f (e p)) ∘ e.symm := by
    funext z
    simp
  rw [hdecomp]
  exact hchart.comp e.symm.continuous

private theorem t2_realSmooth_continuous (f : X F → ℝ) (hf : IsSmoothRealX F f) :
    Continuous f := by
  classical
  obtain ⟨e, hept, _⟩ := t2_chartEquiv (F := F)
  have hfcoord : ContDiffOn ℝ ∞ (fun p : Coord F => f (ptX F p)) (posSet F) := hf
  have hfcont : ContinuousOn (fun p : Coord F => f (ptX F p)) (posSet F) :=
    hfcoord.continuousOn
  let Pos := {p : Coord F // p ∈ posSet F}
  have hchart₀ : ContinuousOn (fun p : Pos => f (ptX F p.1)) Set.univ :=
    hfcont.comp continuous_subtype_val.continuousOn (by intro p hp; exact p.2)
  have hchart₀ : Continuous (fun p : Pos => f (ptX F p.1)) :=
    continuousOn_univ.mp hchart₀
  have hchart : Continuous (fun p : Pos => f (e p)) := by
    convert hchart₀ using 1
    funext p
    rw [hept]
  have hdecomp : f = (fun p : Pos => f (e p)) ∘ e.symm := by
    funext z
    simp
  rw [hdecomp]
  exact hchart.comp e.symm.continuous

private theorem t2_compact_isClosed {K : Set (X F)} (hK : IsCompact K) : IsClosed K := by
  classical
  obtain ⟨e, _, _⟩ := t2_chartEquiv (F := F)
  let Pos := {p : Coord F // p ∈ posSet F}
  letI : T2Space Pos := inferInstance
  have hpre : IsCompact (e.symm '' K) := hK.image e.symm.continuous
  have hpreClosed : IsClosed (e.symm '' K) := hpre.isClosed
  have hEq : e '' (e.symm '' K) = K := by
    ext z
    simp
  rw [← hEq]
  exact e.isClosedMap _ hpreClosed

private theorem t2_weighted_lintegral_unfold (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (K : Set (X F)) (ψ : X F → ℝ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ)))
    (hψnonneg : ∀ z, 0 ≤ ψ z)
    (hψcont : Continuous ψ)
    (hpartition : ∀ z ∈ orbitSaturation F Γ K,
      ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) = 1)
    (E : X F → ℝ) (hEcont : Continuous E) (hEnonneg : ∀ z, 0 ≤ E z)
    (hEinv : ∀ γ ∈ Γ, ∀ z, E ((γ : SL(2,𝓞 F)) • z) = E z)
    (hEsupport : {z | E z ≠ 0} ⊆ orbitSaturation F Γ K) :
    (∫⁻ z in D, ENNReal.ofReal (E z) ∂(volX F) =
      ∫⁻ z, ENNReal.ofReal (ψ z * E z) ∂(volX F)) ∧
      Integrable (fun z => ψ z * E z) (volX F) := by
  classical
  letI : Finite (InfinitePlace F) := inferInstance
  letI : Countable (InfinitePlace F) := Finite.to_countable
  letI : TopologicalSpace (X F) := Pi.topologicalSpace
  letI : TopologicalSpace SL(2,ℂ) := Matrix.SpecialLinearGroup.instTopologicalSpace
  letI : IsTopologicalGroup SL(2,ℂ) := Matrix.SpecialLinearGroup.isTopologicalGroup
  letI : SecondCountableTopology (Fin 2 → ℝ) := inferInstance
  letI : SecondCountableTopology ℂ :=
    Complex.basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (Fin 2 → ℂ) := by infer_instance
  letI : SecondCountableTopology (Fin 2 → Fin 2 → ℂ) := by infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  letI : SecondCountableTopology SL(2,ℂ) :=
    TopologicalSpace.secondCountableTopology_induced
      (SL(2,ℂ)) (Matrix (Fin 2) (Fin 2) ℂ) Subtype.val
  have hsecH3 : SecondCountableTopology H3 :=
    TopologicalSpace.Quotient.secondCountableTopology
      QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  letI : SecondCountableTopology H3 := hsecH3
  letI : BorelSpace H3 := ⟨rfl⟩
  letI : OpensMeasurableSpace H3 := BorelSpace.opensMeasurable
  letI : ∀ w : InfinitePlace F,
      SecondCountableTopology ((fun _ : InfinitePlace F => H3) w) := fun _ => hsecH3
  letI : ∀ w : InfinitePlace F,
      BorelSpace ((fun _ : InfinitePlace F => H3) w) := fun _ => ⟨rfl⟩
  letI : ∀ w : InfinitePlace F,
      OpensMeasurableSpace ((fun _ : InfinitePlace F => H3) w) := fun _ => BorelSpace.opensMeasurable
  obtain ⟨chart, _, _⟩ := t2_chartEquiv (F := F)
  let Pos := {p : Coord F // p ∈ posSet F}
  letI : T2Space Pos := inferInstance
  have hOpenPi : ∀ w : InfinitePlace F, OpensMeasurableSpace H3 :=
    fun _ => BorelSpace.opensMeasurable
  letI : OpensMeasurableSpace (X F) := by
    exact @Pi.opensMeasurableSpace (InfinitePlace F) (fun _ => H3) Finite.to_countable
      (fun _ => inferInstance) (fun _ => inferInstance)
      (fun _ => hsecH3) hOpenPi
  have hOpenX : OpensMeasurableSpace (X F) := inferInstance
  letI : IsFiniteMeasureOnCompacts (volX F) :=
    ⟨fun hK => (G3_volume (F := F)).2.2.1 hK⟩
  rcases t1_action_facts (F := F) Γ with ⟨hCountable, hMeasurable, hInvariant⟩
  letI : Countable Γ := hCountable
  letI : MeasurableConstSMul Γ (X F) := hMeasurable
  letI : SMulInvariantMeasure Γ (X F) (volX F) := hInvariant
  let q : X F → ENNReal := fun z => ENNReal.ofReal (ψ z * E z)
  let r : X F → ℝ := fun z => ψ z * E z
  have hψsupportReal : HasCompactSupport ψ := by
    rcases hψcompact with ⟨Kψ, hKψ, hψsupport⟩
    have hKψclosed : IsClosed Kψ := t2_compact_isClosed hKψ
    have hsupport : Function.support ψ ⊆ Kψ := by
      intro z hz
      apply hψsupport
      have hz' : ψ z ≠ 0 := by simpa [Function.mem_support] using hz
      change (ψ z : ℂ) ≠ 0
      exact_mod_cast hz'
    have htsupport : tsupport ψ ⊆ Kψ := closure_minimal hsupport hKψclosed
    change IsCompact (tsupport ψ)
    exact hKψ.of_isClosed_subset (isClosed_tsupport _) htsupport
  have hrcont : Continuous r := by
    dsimp [r]
    exact hψcont.mul hEcont
  have hrnonneg : ∀ z, 0 ≤ r z := by
    intro z
    exact mul_nonneg (hψnonneg z) (hEnonneg z)
  have hrintegrable : Integrable r (volX F) := by
    dsimp [r]
    exact (hψcont.mul hEcont).integrable_of_hasCompactSupport hψsupportReal.mul_right
  have hqmeas : Measurable q := by
    dsimp [q, r]
    exact ENNReal.measurable_ofReal.comp (hψcont.mul hEcont).measurable
  have htermMeas (γ : Γ) : AEMeasurable
      (fun z => q ((γ : SL(2,𝓞 F)) • z)) ((volX F).restrict D) := by
    exact ((hqmeas.comp (measurable_const_smul γ)).aemeasurable).restrict
  have hpoint (z : X F) :
      ∑' γ : Γ, ENNReal.ofReal
        (ψ ((γ : SL(2,𝓞 F)) • z) * E ((γ : SL(2,𝓞 F)) • z)) =
        ENNReal.ofReal (E z) := by
    by_cases hEz : E z = 0
    · have hzero (γ : Γ) : ENNReal.ofReal
          (ψ ((γ : SL(2,𝓞 F)) • z) * E ((γ : SL(2,𝓞 F)) • z)) = 0 := by
        rw [hEinv γ γ.property z, hEz]
        simp
      simp [hzero, hEz]
    · have hzsat : z ∈ orbitSaturation F Γ K := hEsupport hEz
      rcases t2_periodize_eq_sum Γ ψ hψcompact z with ⟨T, hψsum, hψzero⟩
      have hsumOne : (∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • z)) = 1 := by
        calc
          _ = t2_periodize Γ ψ z := hψsum.symm
          _ = ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) := rfl
          _ = 1 := hpartition z hzsat
      have hrealSum :
          (∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • z) * E z) = E z := by
        calc
          _ = (∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • z)) * E z :=
            (Finset.sum_mul _ _ _).symm
          _ = E z := by rw [hsumOne]; simp
      have hzero (γ : Γ) (hγ : γ ∉ T) :
          ENNReal.ofReal
            (ψ ((γ : SL(2,𝓞 F)) • z) * E ((γ : SL(2,𝓞 F)) • z)) = 0 := by
        rw [hψzero γ hγ]
        simp
      rw [tsum_eq_sum (s := T) hzero]
      calc
        (∑ γ ∈ T, ENNReal.ofReal
          (ψ ((γ : SL(2,𝓞 F)) • z) * E ((γ : SL(2,𝓞 F)) • z))) =
            (∑ γ ∈ T, ENNReal.ofReal
              (ψ ((γ : SL(2,𝓞 F)) • z) * E z)) := by
          apply Finset.sum_congr rfl
          intro γ hγ
          rw [hEinv γ γ.property z]
        _ = ENNReal.ofReal (∑ γ ∈ T,
              ψ ((γ : SL(2,𝓞 F)) • z) * E z) := by
          exact (ENNReal.ofReal_sum_of_nonneg (s := T)
            (fun γ hγ => mul_nonneg (hψnonneg ((γ : SL(2,𝓞 F)) • z)) (hEnonneg z))).symm
        _ = ENNReal.ofReal (E z) := by rw [hrealSum]
  refine ⟨?_, hrintegrable⟩
  calc
    ∫⁻ z in D, ENNReal.ofReal (E z) ∂(volX F) =
        ∫⁻ z in D, ∑' γ : Γ, q ((γ : SL(2,𝓞 F)) • z) ∂(volX F) := by
      apply lintegral_congr_ae
      filter_upwards with z
      exact (hpoint z).symm
    _ = ∑' γ : Γ, ∫⁻ z in D, q ((γ : SL(2,𝓞 F)) • z) ∂(volX F) :=
      lintegral_tsum (μ := (volX F).restrict D) htermMeas
    _ = ∫⁻ z, q z ∂(volX F) := (hD.lintegral_eq_tsum'' q).symm

private theorem t2_invariant_energy_integrable (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (K : Set (X F)) (hK : IsCompact K) (E : X F → ℝ)
    (hEcont : Continuous E) (hEnonneg : ∀ z, 0 ≤ E z)
    (hEinv : ∀ γ ∈ Γ, ∀ z, E ((γ : SL(2,𝓞 F)) • z) = E z)
    (hEsupport : {z | E z ≠ 0} ⊆ orbitSaturation F Γ K) :
    Integrable E ((volX F).restrict D) := by
  classical
  letI : Finite (InfinitePlace F) := inferInstance
  letI : Countable (InfinitePlace F) := Finite.to_countable
  letI : TopologicalSpace (X F) := Pi.topologicalSpace
  letI : TopologicalSpace SL(2,ℂ) := Matrix.SpecialLinearGroup.instTopologicalSpace
  letI : IsTopologicalGroup SL(2,ℂ) := Matrix.SpecialLinearGroup.isTopologicalGroup
  letI : SecondCountableTopology (Fin 2 → ℝ) := inferInstance
  letI : SecondCountableTopology ℂ :=
    Complex.basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (Fin 2 → ℂ) := by infer_instance
  letI : SecondCountableTopology (Fin 2 → Fin 2 → ℂ) := by infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  letI : SecondCountableTopology SL(2,ℂ) :=
    TopologicalSpace.secondCountableTopology_induced
      (SL(2,ℂ)) (Matrix (Fin 2) (Fin 2) ℂ) Subtype.val
  have hsecH3 : SecondCountableTopology H3 :=
    TopologicalSpace.Quotient.secondCountableTopology
      QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  letI : SecondCountableTopology H3 := hsecH3
  letI : BorelSpace H3 := ⟨rfl⟩
  letI : OpensMeasurableSpace H3 := BorelSpace.opensMeasurable
  letI : ∀ w : InfinitePlace F,
      SecondCountableTopology ((fun _ : InfinitePlace F => H3) w) := fun _ => hsecH3
  letI : ∀ w : InfinitePlace F, BorelSpace ((fun _ : InfinitePlace F => H3) w) :=
    fun _ => ⟨rfl⟩
  letI : ∀ w : InfinitePlace F,
      OpensMeasurableSpace ((fun _ : InfinitePlace F => H3) w) := fun _ => inferInstance
  letI : OpensMeasurableSpace (X F) := by
    exact @Pi.opensMeasurableSpace (InfinitePlace F) (fun _ => H3) Finite.to_countable
      (fun _ => inferInstance) (fun _ => inferInstance)
      (fun _ => hsecH3) (fun _ => BorelSpace.opensMeasurable)
  rcases t2_partition_of_compact Γ K hK with
    ⟨ψ, hψsmooth, hψcompact, hψnonneg, _, ⟨U, hUopen, hUsat, hpartition⟩⟩
  have hψcont : Continuous ψ := t2_realSmooth_continuous ψ hψsmooth
  have hpartitionSat (z : X F) (hz : z ∈ orbitSaturation F Γ K) :
      ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) = 1 := hpartition z (hUsat hz)
  have hweighted := t2_weighted_lintegral_unfold Γ D hD K ψ hψcompact hψnonneg
    hψcont hpartitionSat E hEcont hEnonneg hEinv hEsupport
  have hEm : AEStronglyMeasurable E ((volX F).restrict D) :=
    hEcont.aestronglyMeasurable
  have hEae : 0 ≤ᵐ[(volX F).restrict D] E := ae_of_all _ hEnonneg
  have hfinite :
      ∫⁻ z in D, ENNReal.ofReal (E z) ∂(volX F) ≠ ⊤ := by
    rw [hweighted.1]
    exact (lintegral_ofReal_ne_top_iff_integrable
      ((hψcont.mul hEcont).aestronglyMeasurable)
      (ae_of_all _ fun z => mul_nonneg (hψnonneg z) (hEnonneg z))).2 hweighted.2
  exact (lintegral_ofReal_ne_top_iff_integrable hEm hEae).mp hfinite

private theorem t2_continuous_aestronglyMeasurable {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.PseudoMetrizableSpace Y] (f : X F → Y) (hf : Continuous f)
    (μ : Measure (X F)) :
    AEStronglyMeasurable f μ := by
  classical
  letI : Finite (InfinitePlace F) := inferInstance
  letI : Countable (InfinitePlace F) := Finite.to_countable
  letI : TopologicalSpace (X F) := Pi.topologicalSpace
  letI : TopologicalSpace SL(2,ℂ) := Matrix.SpecialLinearGroup.instTopologicalSpace
  letI : IsTopologicalGroup SL(2,ℂ) := Matrix.SpecialLinearGroup.isTopologicalGroup
  letI : SecondCountableTopology (Fin 2 → ℝ) := inferInstance
  letI : SecondCountableTopology ℂ :=
    Complex.basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (Fin 2 → ℂ) := by infer_instance
  letI : SecondCountableTopology (Fin 2 → Fin 2 → ℂ) := by infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  letI : SecondCountableTopology SL(2,ℂ) :=
    TopologicalSpace.secondCountableTopology_induced
      (SL(2,ℂ)) (Matrix (Fin 2) (Fin 2) ℂ) Subtype.val
  letI : SecondCountableTopology H3 :=
    TopologicalSpace.Quotient.secondCountableTopology
      QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  letI : ∀ w : InfinitePlace F,
      SecondCountableTopology ((fun _ : InfinitePlace F => H3) w) := fun _ => inferInstance
  letI : SecondCountableTopology (X F) :=
    TopologicalSpace.secondCountableTopology_iInf (fun w =>
      TopologicalSpace.secondCountableTopology_induced (X F) H3 fun z => z w)
  letI : BorelSpace H3 := ⟨rfl⟩
  letI : OpensMeasurableSpace H3 := BorelSpace.opensMeasurable
  letI : ∀ w : InfinitePlace F,
      SecondCountableTopology ((fun _ : InfinitePlace F => H3) w) := fun _ => inferInstance
  letI : ∀ w : InfinitePlace F,
      OpensMeasurableSpace ((fun _ : InfinitePlace F => H3) w) := fun _ => inferInstance
  letI : OpensMeasurableSpace (X F) := by
    exact @Pi.opensMeasurableSpace (InfinitePlace F) (fun _ => H3) Finite.to_countable
      (fun _ => inferInstance) (fun _ => inferInstance)
      (fun _ => inferInstance) (fun _ => inferInstance)
  exact hf.aestronglyMeasurable

private theorem t2_test_mass_memLp (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (f : X F → ℂ) (hf : IsGammaTest F Γ f) :
    MemLp f 2 ((volX F).restrict D) := by
  classical
  obtain ⟨K, hK, hfsupport⟩ := hf.2.2
  let E : X F → ℝ := fun z => ‖f z‖ ^ 2
  have hfc : Continuous f := t2_smooth_continuous f hf.2.1
  have hEcont : Continuous E := by
    convert hfc.norm.pow 2 using 1
  have hEnonneg : ∀ z, 0 ≤ E z := by
    intro z
    exact sq_nonneg _
  have hEinv : ∀ γ ∈ Γ, ∀ z, E ((γ : SL(2,𝓞 F)) • z) = E z := by
    intro γ hγ z
    simp [E, hf.1 γ hγ z]
  have hEsupport : {z | E z ≠ 0} ⊆ orbitSaturation F Γ K := by
    intro z hz
    apply hfsupport
    intro hfz
    apply hz
    simp [E, hfz]
  have hEint : Integrable E ((volX F).restrict D) :=
    t2_invariant_energy_integrable Γ D hD K hK E hEcont hEnonneg hEinv hEsupport
  have hfaesm : AEStronglyMeasurable f ((volX F).restrict D) :=
    t2_continuous_aestronglyMeasurable f hfc ((volX F).restrict D)
  apply (memLp_two_iff_integrable_sq_norm hfaesm).2
  simpa [E] using hEint

private theorem t2_fullGradient_zero_of_not_saturated
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (K : Set (X F))
    (f : X F → ℂ) (hf : IsSmoothX F f)
    (hfsupport : {z | f z ≠ 0} ⊆ orbitSaturation F Γ K)
    (hclosed : IsClosed (orbitSaturation F Γ K)) {z : X F}
    (hz : z ∉ orbitSaturation F Γ K) : fullGradient F f z = 0 := by
  classical
  obtain ⟨e, hept, hecoords⟩ := t2_chartEquiv (F := F)
  let Pos := {p : Coord F // p ∈ posSet F}
  let V : Set Pos := e ⁻¹' (orbitSaturation F Γ K)ᶜ
  have hVopen : IsOpen V := hclosed.isOpen_compl.preimage e.continuous
  let W : Set (Coord F) := Subtype.val '' V
  have hWopen : IsOpen W := by
    change IsOpen (Subtype.val '' V)
    exact (t2_posSet_open (F := F)).isOpenMap_subtype_val V hVopen
  let p : Pos := e.symm z
  have hpV : p ∈ V := by
    change e p ∉ orbitSaturation F Γ K
    simpa [p] using hz
  have hpW : p.1 ∈ W := ⟨p, hpV, rfl⟩
  have hcoordEventually : (fun q : Coord F => f (ptX F q)) =ᶠ[𝓝 p.1] 0 := by
    filter_upwards [hWopen.mem_nhds hpW] with q hq
    rcases hq with ⟨q', hq', hqeq⟩
    have hnot : e q' ∉ orbitSaturation F Γ K := by
      change q' ∈ V at hq'
      simpa [V] using hq'
    have hzero : f (e q') = 0 := by
      by_contra hne
      exact hnot (hfsupport hne)
    rw [← hqeq, ← hept q']
    exact hzero
  have hpcoord : p.1 = coordsX F z := hecoords z
  have hcoordEventually' : (fun q : Coord F => f (ptX F q)) =ᶠ[𝓝 (coordsX F z)] 0 := by
    rw [← hpcoord]
    exact hcoordEventually
  have hderiv : fderiv ℝ (fun q : Coord F => f (ptX F q)) (coordsX F z) = 0 := by
    rw [hcoordEventually'.fderiv_eq]
    simp
  have hderiv' : fderiv ℝ (f ∘ ptX F) (coordsX F z) = 0 := by
    simpa only [Function.comp_def] using hderiv
  ext wj
  simp [fullGradient, placeGradient, hderiv']

private theorem t2_test_gradient_memLp (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (f : X F → ℂ) (hf : IsGammaTest F Γ f) :
    MemLp (fullGradient F f) 2 ((volX F).restrict D) := by
  classical
  obtain ⟨K, hK, hfsupport⟩ := hf.2.2
  let E : X F → ℝ := fun z => totalGradNormSq F f z
  have hgradcont : Continuous (fullGradient F f) := t2_fullGradient_continuous f hf.2.1
  have hEcont : Continuous E := by
    convert hgradcont.norm.pow 2 using 1
    funext z
    exact (t2_fullGradient_norm_sq f z).symm
  have hEnonneg : ∀ z, 0 ≤ E z := by
    intro z
    change 0 ≤ totalGradNormSq F f z
    rw [← t2_fullGradient_norm_sq]
    exact sq_nonneg _
  have hEinv : ∀ γ ∈ Γ, ∀ z, E ((γ : SL(2,𝓞 F)) • z) = E z := by
    intro γ hγ z
    let g : InfinitePlace F → SL(2,ℂ) :=
      toInf F (toSLF F (γ : SL(2,𝓞 F)))
    have hact (x : X F) : actAtPlaces F g x =
        (γ : SL(2,𝓞 F)) • x := rfl
    have hcomp : (fun x => f (actAtPlaces F g x)) = f := by
      funext x
      rw [hact]
      exact hf.1 γ hγ x
    have hG4 := (G4_energy g f f hf.2.1 hf.2.1).2.1 z
    have hG : E z = E (actAtPlaces F g z) := by
      simpa only [E, hcomp] using hG4
    rw [← hact z]
    exact hG.symm
  have hclosed := t2_orbitSaturation_closed Γ K hK
  have hEsupport : {z | E z ≠ 0} ⊆ orbitSaturation F Γ K := by
    intro z hz
    by_contra hnot
    have hgradzero := t2_fullGradient_zero_of_not_saturated Γ K f hf.2.1
      hfsupport hclosed hnot
    have hEzero : E z = 0 := by
      change totalGradNormSq F f z = 0
      rw [← t2_fullGradient_norm_sq]
      simp [hgradzero]
    exact hz hEzero
  have hEint : Integrable E ((volX F).restrict D) :=
    t2_invariant_energy_integrable Γ D hD K hK E hEcont hEnonneg hEinv hEsupport
  have hgradAesm : AEStronglyMeasurable (fullGradient F f) ((volX F).restrict D) :=
    t2_continuous_aestronglyMeasurable (fullGradient F f) hgradcont ((volX F).restrict D)
  apply (memLp_two_iff_integrable_sq_norm hgradAesm).2
  simpa only [E, t2_fullGradient_norm_sq] using hEint

private theorem t2_fullGradient_add (f g : X F → ℂ)
    (hf : IsSmoothX F f) (hg : IsSmoothX F g) (z : X F) :
    fullGradient F (f + g) z = fullGradient F f z + fullGradient F g z := by
  classical
  obtain ⟨e, _, hecoords⟩ := t2_chartEquiv (F := F)
  have hp : coordsX F z ∈ posSet F := by
    rw [← hecoords z]
    exact (e.symm z).property
  have hposOpen := t2_posSet_open (F := F)
  have hfdiff : DifferentiableAt ℝ (fun p : Coord F => f (ptX F p)) (coordsX F z) :=
    hf.differentiableOn (by norm_num) |>.differentiableAt (hposOpen.mem_nhds hp)
  have hgdiff : DifferentiableAt ℝ (fun p : Coord F => g (ptX F p)) (coordsX F z) :=
    hg.differentiableOn (by norm_num) |>.differentiableAt (hposOpen.mem_nhds hp)
  have hfun : (f + g) ∘ ptX F =
      (fun p : Coord F => f (ptX F p)) + (fun p => g (ptX F p)) := by
    funext p
    rfl
  have hderiv := fderiv_add hfdiff hgdiff
  ext wj
  change ((coordsX F z wj.1).2 : ℂ) *
      (fderiv ℝ ((fun p : Coord F => f (ptX F p)) +
        (fun p => g (ptX F p))) (coordsX F z)) (placeDirection F wj.1 wj.2) = _
  rw [hderiv]
  simp [fullGradient, placeGradient, PiLp.coe_symm_continuousLinearEquiv,
    Function.comp_def]
  ring

private theorem t2_fullGradient_smul (c : ℂ) (f : X F → ℂ)
    (hf : IsSmoothX F f) (z : X F) :
    fullGradient F (c • f) z = c • fullGradient F f z := by
  classical
  obtain ⟨e, _, hecoords⟩ := t2_chartEquiv (F := F)
  have hp : coordsX F z ∈ posSet F := by
    rw [← hecoords z]
    exact (e.symm z).property
  have hposOpen := t2_posSet_open (F := F)
  have hfdiff : DifferentiableAt ℝ (fun p : Coord F => f (ptX F p)) (coordsX F z) :=
    hf.differentiableOn (by norm_num) |>.differentiableAt (hposOpen.mem_nhds hp)
  have hfun : (c • f) ∘ ptX F = fun p : Coord F => c * f (ptX F p) := by
    funext p
    simp [Pi.smul_apply, smul_eq_mul]
  ext wj
  change ((coordsX F z wj.1).2 : ℂ) *
      (fderiv ℝ (fun p : Coord F => c * f (ptX F p)) (coordsX F z))
        (placeDirection F wj.1 wj.2) = _
  rw [fderiv_const_mul hfdiff c]
  simp [fullGradient, placeGradient, PiLp.coe_symm_continuousLinearEquiv,
    Pi.smul_apply, smul_eq_mul, Function.comp_def]
  ring

theorem T2_tests (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F)) :
    (∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f) ∧
    ∃ (toL2 : testSubmodule F Γ →ₗ[ℂ] L2Space F D)
      (gradL2 : testSubmodule F Γ →ₗ[ℂ] GradientL2Space F D),
      (∀ f, ∀ᵐ z ∂(volX F), z ∈ D → toL2 f z = (f : X F → ℂ) z) ∧
      (∀ f, ∀ᵐ z ∂(volX F), z ∈ D → gradL2 f z = fullGradient F (f : X F → ℂ) z) ∧
      (∀ K : Set (X F), IsCompact K →
        ∃ ψ : X F → ℝ,
          IsSmoothRealX F ψ ∧ HasCompactSupportX F (fun z => (ψ z : ℂ)) ∧
          (∀ z, 0 ≤ ψ z) ∧
          (∀ z, ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧
            {γ : Γ | ∃ x ∈ U, ψ ((γ : SL(2,𝓞 F)) • x) ≠ 0}.Finite) ∧
          (∃ U : Set (X F), IsOpen U ∧ orbitSaturation F Γ K ⊆ U ∧
            ∀ z ∈ U, ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) = 1) ∧
          ∀ f ∈ testSubmodule F Γ,
            {z | (f : X F → ℂ) z ≠ 0} ⊆ orbitSaturation F Γ K →
            ∀ z, (f : X F → ℂ) z =
              ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) * (f : X F → ℂ) ((γ : SL(2,𝓞 F)) • z)) := by
  have hspan : testSubmodule F Γ = t2_gammaTestSubmodule Γ := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro f hf
      exact hf
    · intro f hf
      change IsGammaTest F Γ f at hf
      exact Submodule.subset_span hf
  have hmem : ∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f := by
    intro f
    change f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f
    rw [hspan]
    rfl
  have hmass : ∀ f : testSubmodule F Γ,
      MemLp (f : X F → ℂ) 2 ((volX F).restrict D) := fun f =>
    t2_test_mass_memLp Γ D hD (f : X F → ℂ) (hmem (f : X F → ℂ) |>.mp f.property)
  have hgrad : ∀ f : testSubmodule F Γ,
      MemLp (fullGradient F (f : X F → ℂ)) 2 ((volX F).restrict D) := fun f =>
    t2_test_gradient_memLp Γ D hD (f : X F → ℂ) (hmem (f : X F → ℂ) |>.mp f.property)
  let toL2 : testSubmodule F Γ →ₗ[ℂ] L2Space F D := {
    toFun := fun f => (hmass f).toLp (f : X F → ℂ)
    map_add' := by
      intro f g
      change (hmass (f + g)).toLp ((f + g : testSubmodule F Γ) : X F → ℂ) =
        (hmass f).toLp (f : X F → ℂ) + (hmass g).toLp (g : X F → ℂ)
      have hproof : hmass (f + g) = (hmass f).add (hmass g) := Subsingleton.elim _ _
      rw [hproof]
      exact MemLp.toLp_add (f := (f : X F → ℂ)) (g := (g : X F → ℂ))
        (hmass f) (hmass g)
    map_smul' := by
      intro c f
      change (hmass (c • f)).toLp ((c • f : testSubmodule F Γ) : X F → ℂ) =
        c • (hmass f).toLp (f : X F → ℂ)
      have hproof : hmass (c • f) = (hmass f).const_smul c := Subsingleton.elim _ _
      rw [hproof]
      exact MemLp.toLp_const_smul (f := (f : X F → ℂ)) c (hmass f)
  }
  let gradL2 : testSubmodule F Γ →ₗ[ℂ] GradientL2Space F D := {
    toFun := fun f => (hgrad f).toLp (fullGradient F (f : X F → ℂ))
    map_add' := by
      intro f g
      change (hgrad (f + g)).toLp (fullGradient F ((f + g : testSubmodule F Γ) : X F → ℂ)) =
        (hgrad f).toLp (fullGradient F (f : X F → ℂ)) +
          (hgrad g).toLp (fullGradient F (g : X F → ℂ))
      calc
        _ = ((hgrad f).add (hgrad g)).toLp
            (fullGradient F (f : X F → ℂ) + fullGradient F (g : X F → ℂ)) :=
          MemLp.toLp_congr
            (f := fullGradient F ((f + g : testSubmodule F Γ) : X F → ℂ))
            (g := fullGradient F (f : X F → ℂ) + fullGradient F (g : X F → ℂ))
            (hgrad (f + g)) ((hgrad f).add (hgrad g))
            (ae_of_all _ fun z => t2_fullGradient_add (f : X F → ℂ) (g : X F → ℂ)
              (hmem (f : X F → ℂ) |>.mp f.property).2.1
              (hmem (g : X F → ℂ) |>.mp g.property).2.1 z)
        _ = _ := MemLp.toLp_add
          (f := fullGradient F (f : X F → ℂ))
          (g := fullGradient F (g : X F → ℂ)) (hgrad f) (hgrad g)
    map_smul' := by
      intro c f
      change (hgrad (c • f)).toLp (fullGradient F ((c • f : testSubmodule F Γ) : X F → ℂ)) =
        c • (hgrad f).toLp (fullGradient F (f : X F → ℂ))
      calc
        _ = ((hgrad f).const_smul c).toLp
            (c • fullGradient F (f : X F → ℂ)) :=
          MemLp.toLp_congr
            (f := fullGradient F ((c • f : testSubmodule F Γ) : X F → ℂ))
            (g := c • fullGradient F (f : X F → ℂ))
            (hgrad (c • f)) ((hgrad f).const_smul c)
            (ae_of_all _ fun z => t2_fullGradient_smul c (f : X F → ℂ)
              (hmem (f : X F → ℂ) |>.mp f.property).2.1 z)
        _ = _ := MemLp.toLp_const_smul
          (f := fullGradient F (f : X F → ℂ)) c (hgrad f)
  }
  have hmass_rep : ∀ f, ∀ᵐ z ∂(volX F),
      z ∈ D → toL2 f z = (f : X F → ℂ) z := by
    intro f
    have hEq : ∀ᵐ z ∂(volX F).restrict D, toL2 f z = (f : X F → ℂ) z := by
      change ∀ᵐ z ∂(volX F).restrict D, (hmass f).toLp (f : X F → ℂ) z = _
      exact (hmass f).coeFn_toLp
    exact ae_imp_of_ae_restrict hEq
  have hgradient_rep : ∀ f, ∀ᵐ z ∂(volX F),
      z ∈ D → gradL2 f z = fullGradient F (f : X F → ℂ) z := by
    intro f
    have hEq : ∀ᵐ z ∂(volX F).restrict D,
        gradL2 f z = fullGradient F (f : X F → ℂ) z := by
      change ∀ᵐ z ∂(volX F).restrict D,
        (hgrad f).toLp (fullGradient F (f : X F → ℂ)) z = _
      exact (hgrad f).coeFn_toLp
    exact ae_imp_of_ae_restrict hEq
  refine ⟨?_, ⟨toL2, gradL2, hmass_rep, hgradient_rep, ?_⟩⟩
  · intro f
    change f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f
    rw [hspan]
    rfl
  · intro K hK
    rcases t2_partition_of_compact Γ K hK with
      ⟨ψ, hψsmooth, hψcompact, hψnonneg, hψlocal,
        ⟨U, hUopen, hUsat, hpartitionU⟩⟩
    have hpartitionSat (z : X F) (hz : z ∈ orbitSaturation F Γ K) :
        ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) = 1 := hpartitionU z (hUsat hz)
    refine ⟨ψ, hψsmooth, hψcompact, hψnonneg, hψlocal,
      ⟨U, hUopen, hUsat, hpartitionU⟩, ?_⟩
    intro f hf hfsupport
    exact t2_partition_reconstruct Γ K ψ hψcompact hpartitionSat
      (f : X F → ℂ) (hmem (f : X F → ℂ) |>.mp hf).1 hfsupport

/-- T3 `spec:green-q` — P-SPEC.md:230, 349–352. Green's identity on a finite-volume
fundamental domain with one test factor and one invariant smooth factor. -/
theorem T3_green_q (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F)) :
    (∀ f : X F → ℂ, f ∈ testSubmodule F Γ →
      ∀ g : X F → ℂ, IsGammaInvariant F Γ g → IsSmoothX F g →
      ∀ w : InfinitePlace F,
        ∫ z in D, star (f z) * partialLap F w g z ∂(volX F) =
          ∫ z in D, placeGradInner F w f g z ∂(volX F)) ∧
    (∀ f : X F → ℂ, f ∈ testSubmodule F Γ →
      ∀ g : X F → ℂ, IsGammaInvariant F Γ g → IsSmoothX F g →
      ∀ w : InfinitePlace F,
        ∫ z in D, star (partialLap F w f z) * g z ∂(volX F) =
          ∫ z in D, placeGradInner F w f g z ∂(volX F)) := by
  sorry

/-- T4 `spec:energy-space` — P-SPEC.md:231. The energy space is the closed graph closure of the
mass and gradient maps; its test graph is dense and its norm splits into the two components.
Correction from `sol-gate-spec`: require the maps' actual quotient-representative calibrations. -/
theorem T4_energy_space (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (toL2 : testSubmodule F Γ →ₗ[ℂ] L2Space F D)
    (gradL2 : testSubmodule F Γ →ₗ[ℂ] GradientL2Space F D)
    (hmass_rep : ∀ f, ∀ᵐ z ∂(volX F), z ∈ D → toL2 f z = (f : X F → ℂ) z)
    (hgradient_rep : ∀ f, ∀ᵐ z ∂(volX F), z ∈ D →
      gradL2 f z = fullGradient F (f : X F → ℂ) z) :
    ∃ E : FAEnergySpace (L2Space F D) (GradientL2Space F D),
      ∃ e : EnergyContext F Γ D E,
        e.toL2 = toL2 ∧ e.gradL2 = gradL2 ∧
        (∀ x : E.V, ‖x‖ ^ 2 = ‖E.M x‖ ^ 2 + ‖E.Gr x‖ ^ 2) := by
  refine ⟨⟨energyGraph toL2 gradL2, ?_⟩, ?_⟩
  · exact Submodule.isClosed_topologicalClosure _
  refine ⟨⟨toL2, gradL2, rfl, hmass_rep, hgradient_rep⟩, rfl, rfl, ?_⟩
  intro x
  change ‖(x : WithLp 2 (L2Space F D × GradientL2Space F D))‖ ^ 2 =
    ‖(x : WithLp 2 (L2Space F D × GradientL2Space F D)).fst‖ ^ 2 +
      ‖(x : WithLp 2 (L2Space F D × GradientL2Space F D)).snd‖ ^ 2
  exact WithLp.prod_norm_sq_eq_of_L2 _

/-- T5 `spec:cutoff` — P-SPEC.md:232, 354–357. A bounded invariant smooth function with bounded
gradient is represented by an energy vector with those mass and gradient components. Correction
from `sol-gate-spec`: use a context calibrated to the quotient representatives. -/
theorem T5_cutoff (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (f : X F → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hInv : IsGammaInvariant F Γ f) (hSmooth : IsSmoothX F f)
    (hBound : ∀ z, ‖f z‖ ≤ B)
    (hGradBound : ∀ z, ‖fullGradient F f z‖ ≤ B)
    (fL2 : L2Space F D) (grad : GradientL2Space F D)
    (hfL2 : ∀ᵐ z ∂(volX F), z ∈ D → fL2 z = f z)
    (hgrad : ∀ᵐ z ∂(volX F), z ∈ D → grad z = fullGradient F f z) :
    ∃ x : E.V, E.M x = fL2 ∧ E.Gr x = grad := by
  sorry

/-- T6 `spec:rellich` — P-SPEC.md:233, 358–362. Restriction of mass to the orbit of a compact
set is a compact operator from the energy graph to the quotient `L²` space. Correction from
`sol-gate-spec`: tie the energy maps to the geometric representatives. -/
theorem T6_rellich (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E) (K : Set (X F)) (hK : IsCompact K) :
    ∃ R : E.V →L[ℂ] L2Space F D,
      IsCompactOperator R ∧
      ∀ x : E.V, ∀ᵐ z ∂(volX F), z ∈ D →
        R x z = orbitRestrictedMass F D E Γ K x z := by
  sorry

/-- T7 `spec:ground-state` — P-SPEC.md:234, 364–368. The ground-state transform gives the
coercivity estimate with compact error at every height cutoff above all cusp thresholds. Correction
from review lane `rev-spec`: include separation of distinct cusp representatives at the cutoff.
Correction from `sol-gate-spec`: require a calibrated energy context. -/
theorem T7_ground_state (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (d : SiegelData F Γ)
    (A₀ : d.ι → ℝ) (hA₀ : ∀ i, 0 < A₀ i)
    (hA₀sep : ∀ i j : d.ι, ∀ γ γ' : Γ, ∀ z : X F,
      A₀ i ≤ normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ j ≤ normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d.σ i))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (A : ℝ) (hA : ∀ i, A₀ i ≤ A) :
    ∃ K : Set (X F), IsCompact K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ R : E.V →L[ℂ] L2Space F D,
        IsCompactOperator R ∧
        (∀ x : E.V, placeCount F * (1 - 1 / (2 * A)) * ‖E.M x‖ ^ 2 ≤
          ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2) ∧
        (∀ x : E.V, ∀ᵐ z ∂(volX F), z ∈ D →
          R x z = orbitRestrictedMass F D E Γ K x z) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
