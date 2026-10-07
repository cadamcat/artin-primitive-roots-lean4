import ArtinPrimitiveRoots.Spec.GeometryExtra
import ArtinPrimitiveRoots.Spec.ReductionExtra

/-! L² and energy-space nodes T1--T7. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

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
  sorry

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
