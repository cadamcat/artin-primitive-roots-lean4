import ArtinPrimitiveRoots.Spec.GeometryExtra
import ArtinPrimitiveRoots.Spec.ReductionExtra
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Assembly
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GAP.SiegelData
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GAP.CuspSums
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GAP.T5Core
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GAP.GroundState

/-! L² and energy-space nodes T1--T7. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

open Classical

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

private noncomputable def sgEnergyGraphTestPoint
    {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (D : Set (X F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E) (t : testSubmodule F Γ) : E.V :=
  ⟨energyGraphMap e.toL2 e.gradL2 t, by
    rw [e.graph_eq]
    change energyGraphMap e.toL2 e.gradL2 t ∈
      closure (energyGraphMap e.toL2 e.gradL2).range
    exact subset_closure ⟨t, rfl⟩⟩

private theorem sgFullGradient_norm_sq (f : X F → ℂ) (z : X F) :
    ‖fullGradient F f z‖ ^ 2 = totalGradNormSq F f z := by
  rw [fullGradient, PiLp.norm_sq_eq_of_L2]
  simp [totalGradNormSq, placeGradNormSq, Complex.normSq_eq_norm_sq,
    Fintype.sum_prod_type]

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

/-- Complex conjugation preserves smoothness on the product-coordinate chart. -/
private theorem t3_star_smooth (f : X F → ℂ) (hf : IsSmoothX F f) :
    IsSmoothX F (fun z => star (f z)) := by
  change ContDiffOn ℝ ∞ (fun p : Coord F => star (f (ptX F p))) (posSet F)
  change ContDiffOn ℝ ∞ (fun p : Coord F =>
    ((starL' ℝ : ℂ ≃L[ℝ] ℂ) (f (ptX F p)))) (posSet F)
  exact ContDiffOn.continuousLinearMap_comp
    ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) hf

private theorem t3_coord_differentiable (f : X F → ℂ) (hf : IsSmoothX F f)
    {p : Coord F} (hp : p ∈ posSet F) :
    DifferentiableAt ℝ (fun q : Coord F => f (ptX F q)) p := by
  have hposOpen := t2_posSet_open (F := F)
  exact hf.differentiableOn (by norm_num) |>.differentiableAt (hposOpen.mem_nhds hp)

private theorem t3_placeGradient_mul (w : InfinitePlace F) (f g : X F → ℂ)
    (hf : IsSmoothX F f) (hg : IsSmoothX F g) (z : X F) (j : Fin 3) :
    placeGradient F w (fun x => f x * g x) z j =
      f z * placeGradient F w g z j + g z * placeGradient F w f z j := by
  obtain ⟨e, hept, hecoords⟩ := t2_chartEquiv (F := F)
  have hp : coordsX F z ∈ posSet F := by
    rw [← hecoords z]
    exact (e.symm z).property
  have hpt : ptX F (coordsX F z) = z := by
    calc
      ptX F (coordsX F z) = ptX F ((e.symm z).1) := by rw [← hecoords z]
      _ = e (e.symm z) := (hept (e.symm z)).symm
      _ = z := e.apply_symm_apply z
  have hfd : DifferentiableAt ℝ (fun p : Coord F => f (ptX F p)) (coordsX F z) :=
    t3_coord_differentiable f hf hp
  have hgd : DifferentiableAt ℝ (fun p : Coord F => g (ptX F p)) (coordsX F z) :=
    t3_coord_differentiable g hg hp
  have hfun : (fun p : Coord F => (fun x => f x * g x) (ptX F p)) =
      (fun p => f (ptX F p)) * (fun p => g (ptX F p)) := by
    funext p
    rfl
  change ((coordsX F z w).2 : ℂ) *
      fderiv ℝ ((fun x => f x * g x) ∘ ptX F) (coordsX F z)
        (placeDirection F w j) = _
  rw [show ((fun x => f x * g x) ∘ ptX F) =
      (fun p => f (ptX F p)) * (fun p => g (ptX F p)) by exact hfun,
    fderiv_mul hfd hgd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    placeGradient]
  rw [hpt]
  simp only [Function.comp_def]
  ring_nf

private theorem t3_placeGradient_star (w : InfinitePlace F) (f : X F → ℂ)
    (hf : IsSmoothX F f) (z : X F) (j : Fin 3) :
    placeGradient F w (fun x => star (f x)) z j = star (placeGradient F w f z j) := by
  have hp : coordsX F z ∈ posSet F := by
    obtain ⟨e, _, hecoords⟩ := t2_chartEquiv (F := F)
    rw [← hecoords z]
    exact (e.symm z).property
  change ((coordsX F z w).2 : ℂ) *
      fderiv ℝ (fun p : Coord F => star (f (ptX F p))) (coordsX F z)
        (placeDirection F w j) = _
  rw [fderiv_star]
  simp [placeGradient, Function.comp_def]

private theorem t3_partialLap_star (w : InfinitePlace F) (f : X F → ℂ)
    (hf : IsSmoothX F f) (z : X F) :
    partialLap F w (fun x => star (f x)) z = star (partialLap F w f z) := by
  classical
  obtain ⟨e, _, hecoords⟩ := t2_chartEquiv (F := F)
  let p := coordsX F z
  let q : Coord F → ℂ := fun x => f (ptX F x)
  have hp : p ∈ posSet F := by
    dsimp [p]
    rw [← hecoords z]
    exact (e.symm z).property
  have hposOpen := t2_posSet_open (F := F)
  have hqcd : ContDiffAt ℝ 2 q p := by
    have h := hf.contDiffAt (hposOpen.mem_nhds hp)
    exact h.of_le (by norm_num)
  have hstar2 : iteratedFDeriv ℝ 2 (fun x : Coord F => star (q x)) p =
      ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).compContinuousMultilinearMap
        (iteratedFDeriv ℝ 2 q p) := by
    exact (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap
      |>.iteratedFDeriv_comp_left hqcd (by norm_num)
  have hstar1Eval (v : Coord F) :
      fderiv ℝ (fun x : Coord F => star (q x)) p v =
        star (fderiv ℝ q p v) := by
    rw [fderiv_star]
    simp [Function.comp_def]
  have hstar2Eval (v u : Coord F) :
      iteratedFDeriv ℝ 2 (fun x : Coord F => star (q x)) p ![v, u] =
        star (iteratedFDeriv ℝ 2 q p ![v, u]) := by
    rw [hstar2]
    simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  -- The second derivative is obtained by applying conjugation to the value of the
  -- second iterated derivative; all coordinate directions are real.
  let e1 : Coord F := Pi.single w ((1 : ℂ), (0 : ℝ))
  let e2 : Coord F := Pi.single w (Complex.I, (0 : ℝ))
  let e3 : Coord F := Pi.single w ((0 : ℂ), (1 : ℝ))
  change ((p w).2 : ℂ) * fderiv ℝ (fun x : Coord F => star (q x)) p e3 -
      ((p w).2 : ℂ) ^ 2 *
        (iteratedFDeriv ℝ 2 (fun x : Coord F => star (q x)) p ![e1, e1] +
          iteratedFDeriv ℝ 2 (fun x : Coord F => star (q x)) p ![e2, e2] +
          iteratedFDeriv ℝ 2 (fun x : Coord F => star (q x)) p ![e3, e3]) =
      star (((p w).2 : ℂ) * fderiv ℝ q p e3 -
        ((p w).2 : ℂ) ^ 2 *
          (iteratedFDeriv ℝ 2 q p ![e1, e1] + iteratedFDeriv ℝ 2 q p ![e2, e2] +
            iteratedFDeriv ℝ 2 q p ![e3, e3]))
  rw [hstar1Eval, hstar2Eval, hstar2Eval, hstar2Eval]
  simp only [star_add, star_mul, star_pow, star_sub, Complex.star_def,
    Complex.conj_ofReal]
  ring

private theorem t3_placeGradient_continuous (w : InfinitePlace F) (f : X F → ℂ)
    (hf : IsSmoothX F f) (j : Fin 3) :
    Continuous (fun z => placeGradient F w f z j) := by
  have heval : Continuous (fun v : GradientField F => v.ofLp (w, j)) :=
    (continuous_apply (w, j)).comp (PiLp.continuous_ofLp 2 (fun _ : InfinitePlace F × Fin 3 => ℂ))
  have h := heval.comp (t2_fullGradient_continuous f hf)
  have htarget : Continuous (fun z => (fullGradient F f z).ofLp (w, j)) := by
    change Continuous ((fun v : GradientField F => v.ofLp (w, j)) ∘ fullGradient F f)
    exact h
  have hEq : (fun z => placeGradient F w f z j) =
      (fun z => (fullGradient F f z).ofLp (w, j)) := by
    funext z
    simp [fullGradient, placeGradient, PiLp.coe_symm_continuousLinearEquiv]
  rw [hEq]
  exact htarget

private theorem t3_placeGradInner_continuous (w : InfinitePlace F)
    (f g : X F → ℂ) (hf : IsSmoothX F f) (hg : IsSmoothX F g) :
    Continuous (placeGradInner F w f g) := by
  have h1 (j : Fin 3) : Continuous (fun z => placeGradient F w f z j) :=
    t3_placeGradient_continuous w f hf j
  have h2 (j : Fin 3) : Continuous (fun z => placeGradient F w g z j) :=
    t3_placeGradient_continuous w g hg j
  unfold placeGradInner
  exact continuous_finset_sum _ fun j hj =>
    (continuous_star.comp (h1 j)).mul (h2 j)

private theorem t3_placeGradBilinear_continuous (w : InfinitePlace F)
    (f g : X F → ℂ) (hf : IsSmoothX F f) (hg : IsSmoothX F g) :
    Continuous (placeGradBilinear F w f g) := by
  have h1 (j : Fin 3) : Continuous (fun z => placeGradient F w f z j) :=
    t3_placeGradient_continuous w f hf j
  have h2 (j : Fin 3) : Continuous (fun z => placeGradient F w g z j) :=
    t3_placeGradient_continuous w g hg j
  unfold placeGradBilinear
  exact continuous_finset_sum _ fun j hj => (h1 j).mul (h2 j)

private theorem t3_partialLap_continuous (w : InfinitePlace F) (f : X F → ℂ)
    (hf : IsSmoothX F f) : Continuous (partialLap F w f) := by
  classical
  obtain ⟨e, hept, _⟩ := t2_chartEquiv (F := F)
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, hcoordPt, _, _, _, _, _⟩
  have hposOpen := t2_posSet_open (F := F)
  let q : Coord F → ℂ := fun p => f (ptX F p)
  have hfcoord : ContDiffOn ℝ ∞ q (posSet F) := hf
  have hfd : ContinuousOn (fderiv ℝ q) (posSet F) :=
    hfcoord.continuousOn_fderiv_of_isOpen hposOpen (by norm_num)
  have hderivCD : ContDiffOn ℝ ∞ (fderiv ℝ q) (posSet F) :=
    hfcoord.fderiv_of_isOpen hposOpen (by norm_num)
  have hsecond : ContinuousOn (fderiv ℝ (fderiv ℝ q)) (posSet F) :=
    hderivCD.continuousOn_fderiv_of_isOpen hposOpen (by norm_num)
  let e1 : Coord F := Pi.single w ((1 : ℂ), (0 : ℝ))
  let e2 : Coord F := Pi.single w (Complex.I, (0 : ℝ))
  let e3 : Coord F := Pi.single w ((0 : ℂ), (1 : ℝ))
  have hfirstEval (v : Coord F) :
      ContinuousOn (fun p => fderiv ℝ q p v) (posSet F) := by
    exact hfd.clm_apply continuousOn_const
  have hsecondEval (v u : Coord F) :
      ContinuousOn (fun p => iteratedFDeriv ℝ 2 q p ![v, u]) (posSet F) := by
    have hEvalV : ContinuousOn
        (fun p => fderiv ℝ (fderiv ℝ q) p v) (posSet F) :=
      hsecond.clm_apply continuousOn_const
    have hEvalVU : ContinuousOn
        (fun p => fderiv ℝ (fderiv ℝ q) p v u) (posSet F) :=
      hEvalV.clm_apply continuousOn_const
    apply hEvalVU.congr
    intro p hp
    change iteratedFDeriv ℝ 2 q p ![v, u] = fderiv ℝ (fderiv ℝ q) p v u
    simp [iteratedFDeriv_two_apply]
  have hy : ContinuousOn (fun p : Coord F => ((p w).2 : ℂ)) (posSet F) := by
    fun_prop
  have hformula : ∀ p : Coord F, p ∈ posSet F →
      partialLap F w f (ptX F p) =
      ((p w).2 : ℂ) * fderiv ℝ q p e3 - ((p w).2 : ℂ) ^ 2 *
        (iteratedFDeriv ℝ 2 q p ![e1, e1] + iteratedFDeriv ℝ 2 q p ![e2, e2] +
          iteratedFDeriv ℝ 2 q p ![e3, e3]) := by
    intro p hp
    have hcoords := hcoordPt p hp
    simp [partialLap, q, hcoords, e1, e2, e3, Function.comp_def]
  have hcoord : ContinuousOn
      (fun p : Coord F => partialLap F w f (ptX F p)) (posSet F) := by
    have hsum : ContinuousOn
        (fun p => iteratedFDeriv ℝ 2 q p ![e1, e1] +
          iteratedFDeriv ℝ 2 q p ![e2, e2] + iteratedFDeriv ℝ 2 q p ![e3, e3])
        (posSet F) := by
      exact ((hsecondEval e1 e1).add (hsecondEval e2 e2)).add (hsecondEval e3 e3)
    have hp : ContinuousOn
        (fun p => ((p w).2 : ℂ) * fderiv ℝ q p e3) (posSet F) :=
      hy.mul (hfirstEval e3)
    have hq : ContinuousOn
        (fun p => ((p w).2 : ℂ) ^ 2 *
          (iteratedFDeriv ℝ 2 q p ![e1, e1] + iteratedFDeriv ℝ 2 q p ![e2, e2] +
            iteratedFDeriv ℝ 2 q p ![e3, e3])) (posSet F) :=
      (hy.pow 2).mul hsum
    apply (hp.sub hq).congr
    intro p hp
    exact hformula p hp
  let Pos := {p : Coord F // p ∈ posSet F}
  have hcoordPos : Continuous
      (fun p : Pos => partialLap F w f (ptX F p.1)) := by
    apply continuousOn_univ.mp
    exact hcoord.comp continuous_subtype_val.continuousOn
      (by intro p hp; exact p.property)
  have hchart : Continuous (fun p : Pos => partialLap F w f (e p)) := by
    convert hcoordPos using 1
    funext p
    rw [hept]
  have hfactor : partialLap F w f =
      (fun p : Pos => partialLap F w f (e p)) ∘ e.symm := by
    funext z
    simp
  rw [hfactor]
  exact hchart.comp e.symm.continuous

private theorem t3_placeGradient_zero_of_not_compact (w : InfinitePlace F)
    (ψ : X F → ℝ) (K : Set (X F)) (hK : IsCompact K)
    (hψsupport : {z | (ψ z : ℂ) ≠ 0} ⊆ K) {z : X F} (hz : z ∉ K) :
    placeGradient F w (fun x => (ψ x : ℂ)) z = 0 := by
  classical
  obtain ⟨e, hept, hecoords⟩ := t2_chartEquiv (F := F)
  have hKclosed := t2_compact_isClosed hK
  let Pos := {p : Coord F // p ∈ posSet F}
  let V : Set Pos := e ⁻¹' Kᶜ
  have hVopen : IsOpen V := hKclosed.isOpen_compl.preimage e.continuous
  let W : Set (Coord F) := Subtype.val '' V
  have hWopen : IsOpen W := (t2_posSet_open (F := F)).isOpenMap_subtype_val V hVopen
  let p : Pos := e.symm z
  have hpV : p ∈ V := by
    change e p ∉ K
    simpa [p] using hz
  have hpW : p.1 ∈ W := ⟨p, hpV, rfl⟩
  have hcoordEventually : (fun q : Coord F => (ψ (ptX F q) : ℂ)) =ᶠ[𝓝 p.1] 0 := by
    filter_upwards [hWopen.mem_nhds hpW] with q hq
    rcases hq with ⟨q', hq', hqq'⟩
    have hzero : (ψ (e q') : ℂ) = 0 := by
      by_contra hne
      exact hq' (hψsupport hne)
    rw [← hqq', ← hept q']
    exact hzero
  have hpcoord : p.1 = coordsX F z := hecoords z
  have hcoordEventually' :
      (fun q : Coord F => (ψ (ptX F q) : ℂ)) =ᶠ[𝓝 (coordsX F z)] 0 := by
    rw [← hpcoord]
    exact hcoordEventually
  have hderiv : fderiv ℝ (fun q : Coord F => (ψ (ptX F q) : ℂ)) (coordsX F z) = 0 := by
    rw [hcoordEventually'.fderiv_eq]
    simp
  have hderiv' : fderiv ℝ ((fun x => (ψ x : ℂ)) ∘ ptX F) (coordsX F z) = 0 := by
    simpa [Function.comp_def] using hderiv
  ext j
  simp [placeGradient, hderiv']

private theorem t3_placeGradient_congr_open (w : InfinitePlace F)
    (f g : X F → ℂ) (U : Set (X F)) (hU : IsOpen U) {z : X F}
    (hz : z ∈ U) (hfg : ∀ x ∈ U, f x = g x) :
    placeGradient F w f z = placeGradient F w g z := by
  classical
  obtain ⟨e, hept, hecoords⟩ := t2_chartEquiv (F := F)
  let Pos := {p : Coord F // p ∈ posSet F}
  let V : Set Pos := e ⁻¹' U
  have hVopen : IsOpen V := hU.preimage e.continuous
  let W : Set (Coord F) := Subtype.val '' V
  have hWopen : IsOpen W := (t2_posSet_open (F := F)).isOpenMap_subtype_val V hVopen
  let p : Pos := e.symm z
  have hpV : p ∈ V := by
    change e p ∈ U
    simpa [p] using hz
  have hpW : p.1 ∈ W := by
    exact ⟨p, hpV, rfl⟩
  have hcoordEventually : (fun q : Coord F => f (ptX F q)) =ᶠ[𝓝 p.1]
      (fun q => g (ptX F q)) := by
    filter_upwards [hWopen.mem_nhds hpW] with q hq
    rcases hq with ⟨q', hq', hqq'⟩
    have hEq : f (e q') = g (e q') := hfg (e q') hq'
    rw [← hqq', ← hept q']
    exact hEq
  have hpcoord : p.1 = coordsX F z := hecoords z
  have hcoordEventually' : (fun q : Coord F => f (ptX F q)) =ᶠ[𝓝 (coordsX F z)]
      (fun q => g (ptX F q)) := by
    rw [← hpcoord]
    exact hcoordEventually
  have hderiv : fderiv ℝ (fun q : Coord F => f (ptX F q)) (coordsX F z) =
      fderiv ℝ (fun q : Coord F => g (ptX F q)) (coordsX F z) :=
    hcoordEventually'.fderiv_eq
  have hderiv' : fderiv ℝ (f ∘ ptX F) (coordsX F z) =
      fderiv ℝ (g ∘ ptX F) (coordsX F z) := by
    simpa [Function.comp_def] using hderiv
  ext j
  simp only [placeGradient]
  rw [hderiv']

private theorem t3_ofReal_smooth (ψ : X F → ℝ) (hψ : IsSmoothRealX F ψ) :
    IsSmoothX F (fun z => (ψ z : ℂ)) := by
  unfold IsSmoothX IsSmoothRealX at *
  exact ContDiffOn.continuousLinearMap_comp Complex.ofRealCLM hψ

private theorem t3_periodize_gradInner (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (w : InfinitePlace F) (u : X F → ℂ) (hu : IsSmoothX F u)
    (ψ : X F → ℝ) (hψ : IsSmoothRealX F ψ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ))) (z : X F) :
    (∑' γ : Γ, placeGradInner F w u
      (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z) =
      placeGradInner F w u (fun x => (t2_periodize Γ ψ x : ℂ)) z := by
  classical
  rcases t2_translate_locally_finite Γ ψ hψcompact z with
    ⟨U, hU, hzU, hfinite⟩
  let T := hfinite.toFinset
  have hzero (x : X F) (hx : x ∈ U) (γ : Γ) (hγ : γ ∉ T) :
      ψ ((γ : SL(2,𝓞 F)) • x) = 0 := by
    by_contra hne
    have hmem : γ ∈ {δ : Γ | ∃ y ∈ U,
        ψ ((δ : SL(2,𝓞 F)) • y) ≠ 0} := ⟨x, hx, hne⟩
    exact hγ (by simpa [T] using hmem)
  have hPsum (x : X F) (hx : x ∈ U) :
      t2_periodize Γ ψ x = ∑ γ ∈ T, ψ ((γ : SL(2,𝓞 F)) • x) := by
    rw [t2_periodize]
    exact tsum_eq_sum (s := T) (fun γ hγ => hzero x hx γ hγ)
  have hPsumC (x : X F) (hx : x ∈ U) :
      (t2_periodize Γ ψ x : ℂ) = ∑ γ ∈ T,
        (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ) := by
    exact_mod_cast hPsum x hx
  have hsumGradient (j : Fin 3) :
      placeGradient F w (fun x => (t2_periodize Γ ψ x : ℂ)) z j =
        ∑ γ ∈ T, placeGradient F w
          (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z j := by
    obtain ⟨chart, heptChart, hecoords⟩ := t2_chartEquiv (F := F)
    let Pos := {p : Coord F // p ∈ posSet F}
    let p : Coord F := coordsX F z
    have hpPos : p ∈ posSet F := by
      dsimp [p]
      rw [← hecoords z]
      exact (chart.symm z).property
    have hpcoord : (chart.symm z).1 = p := hecoords z
    let V : Set Pos := {q | chart q ∈ U}
    have hV : IsOpen V := hU.preimage chart.continuous
    let W : Set (Coord F) := Subtype.val '' V
    have hW : IsOpen W := (t2_posSet_open (F := F)).isOpenMap_subtype_val V hV
    have hpW : p ∈ W := by
      refine ⟨chart.symm z, ?_, hpcoord⟩
      change chart (chart.symm z) ∈ U
      simpa using hzU
    have hptU : ∀ q ∈ W, ptX F q ∈ U := by
      intro q hq
      rcases hq with ⟨q', hqV, hqq'⟩
      change chart q' ∈ U at hqV
      rw [← hqq', ← heptChart q']
      exact hqV
    have hfunAt : (fun q : Coord F =>
        (t2_periodize Γ ψ (ptX F q) : ℂ)) =ᶠ[𝓝 p]
        (fun q => ∑ γ ∈ T,
          (ψ ((γ : SL(2,𝓞 F)) • ptX F q) : ℂ)) := by
      filter_upwards [hW.mem_nhds hpW] with q hq
      exact hPsumC (ptX F q) (hptU q hq)
    have htermsmooth (γ : Γ) : IsSmoothX F
        (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) :=
      t3_ofReal_smooth _ (t2_translate_smooth Γ γ ψ hψ)
    have hdiff (γ : Γ) (hγ : γ ∈ T) :
        DifferentiableAt ℝ
          (fun q : Coord F => (ψ ((γ : SL(2,𝓞 F)) • ptX F q) : ℂ)) p :=
      t3_coord_differentiable _ (htermsmooth γ) hpPos
    have hderiv := fderiv_fun_sum (u := T) hdiff
    have hderivEq : fderiv ℝ (fun q : Coord F =>
        (t2_periodize Γ ψ (ptX F q) : ℂ)) p =
        ∑ γ ∈ T, fderiv ℝ
          (fun q : Coord F => (ψ ((γ : SL(2,𝓞 F)) • ptX F q) : ℂ)) p := by
      rw [hfunAt.fderiv_eq, hderiv]
    change ((coordsX F z w).2 : ℂ) *
        fderiv ℝ (fun q : Coord F =>
          (t2_periodize Γ ψ (ptX F q) : ℂ)) (coordsX F z)
          (placeDirection F w j) = _
    rw [hderivEq]
    have hEval : (∑ γ ∈ T, fderiv ℝ
        (fun q : Coord F => (ψ ((γ : SL(2,𝓞 F)) • ptX F q) : ℂ)) p)
          (placeDirection F w j) =
        ∑ γ ∈ T, fderiv ℝ
          (fun q : Coord F => (ψ ((γ : SL(2,𝓞 F)) • ptX F q) : ℂ)) p
            (placeDirection F w j) := by simp
    rw [hEval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [show p = coordsX F z from rfl]
    simp only [placeGradient]
    rfl

  have hinnerFinite :
      placeGradInner F w u (fun x => (t2_periodize Γ ψ x : ℂ)) z =
        ∑ γ ∈ T, placeGradInner F w u
          (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z := by
    unfold placeGradInner
    calc
      _ = ∑ j : Fin 3, ∑ γ ∈ T,
            star (placeGradient F w u z j) *
              placeGradient F w (fun x =>
                (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hsumGradient j]
          simp only [Finset.mul_sum]
      _ = _ := by
          rw [Finset.sum_comm]
  have hzeroInner (γ : Γ) (hγ : γ ∉ T) :
      placeGradInner F w u
        (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z = 0 := by
    have hcongr := t3_placeGradient_congr_open w
      (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) (fun _ => (0 : ℂ))
      U hU hzU (by
        intro x hx
        simp [hzero x hx γ hγ])
    have hgrad : placeGradient F w
        (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z = 0 := by
      have hzeroGrad : placeGradient F w (fun _ => (0 : ℂ)) z = 0 := by
        ext j
        simp [placeGradient, Function.comp_def]
      exact hcongr.trans hzeroGrad
    simp [placeGradInner, hgrad]
  calc
    _ = ∑ γ ∈ T, placeGradInner F w u
          (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z := by
      rw [tsum_eq_sum (s := T) hzeroInner]
    _ = placeGradInner F w u (fun x => (t2_periodize Γ ψ x : ℂ)) z :=
      hinnerFinite.symm

private theorem t3_integral_unfold (Γ : Subgroup SL(2,𝓞 F))
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (q : X F → ℂ) (hq : Integrable q (volX F)) :
    ∫ z in D, (∑' γ : Γ, q ((γ : SL(2,𝓞 F)) • z)) ∂(volX F) =
      ∫ z, q z ∂(volX F) := by
  classical
  rcases t1_action_facts (F := F) Γ with ⟨hCountable, hMeasurable, hInvariant⟩
  letI : Countable Γ := hCountable
  letI : MeasurableConstSMul Γ (X F) := hMeasurable
  letI : SMulInvariantMeasure Γ (X F) (volX F) := hInvariant
  have hpres (γ : Γ) : MeasurePreserving
      (fun z : X F => (γ : SL(2,𝓞 F)) • z) (volX F) (volX F) := by
    change MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F)
    exact measurePreserving_smul γ (volX F)
  have hsumNorm := ne_of_lt (hasFiniteIntegral_iff_enorm.mp hq.hasFiniteIntegral)
  rw [hD.lintegral_eq_tsum'' (fun z => ‖q z‖ₑ)] at hsumNorm
  have hmeas (γ : Γ) : AEStronglyMeasurable
      (fun z : X F => q ((γ : SL(2,𝓞 F)) • z)) ((volX F).restrict D) := by
    exact (hq.aestronglyMeasurable.comp_measurePreserving (hpres γ)).restrict
  calc
    ∫ z in D, (∑' γ : Γ, q ((γ : SL(2,𝓞 F)) • z)) ∂(volX F) =
        ∑' γ : Γ, ∫ z in D, q ((γ : SL(2,𝓞 F)) • z) ∂(volX F) :=
      integral_tsum (μ := (volX F).restrict D) hmeas hsumNorm
    _ = ∫ z, q z ∂(volX F) := (hD.integral_eq_tsum'' q hq).symm

private theorem t3_quotient_weight (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (K : Set (X F)) (ψ : X F → ℝ) (hψ : IsSmoothRealX F ψ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ)))
    (hpartition : ∀ z ∈ orbitSaturation F Γ K,
      ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) = 1)
    (H : X F → ℂ) (hHcont : Continuous H)
    (hHinv : ∀ γ ∈ Γ, ∀ z, H ((γ : SL(2,𝓞 F)) • z) = H z)
    (hHsupport : {z | H z ≠ 0} ⊆ orbitSaturation F Γ K) :
    ∫ z in D, H z ∂(volX F) =
      ∫ z, (ψ z : ℂ) * H z ∂(volX F) := by
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
      OpensMeasurableSpace ((fun _ : InfinitePlace F => H3) w) :=
    fun _ => BorelSpace.opensMeasurable
  letI : OpensMeasurableSpace (X F) := by
    exact @Pi.opensMeasurableSpace (InfinitePlace F) (fun _ => H3) Finite.to_countable
      (fun _ => inferInstance) (fun _ => inferInstance)
      (fun _ => hsecH3) (fun _ => BorelSpace.opensMeasurable)
  letI : IsFiniteMeasureOnCompacts (volX F) :=
    ⟨fun hK => (G3_volume (F := F)).2.2.1 hK⟩
  let Q : X F → ℂ := fun z => (ψ z : ℂ) * H z
  have hψcont : Continuous (fun z => (ψ z : ℂ)) :=
    Complex.ofRealCLM.continuous.comp (t2_realSmooth_continuous ψ hψ)
  have hQcont : Continuous Q := by
    dsimp [Q]
    exact hψcont.mul hHcont
  have hQcompact : HasCompactSupport Q := by
    rcases hψcompact with ⟨Kψ, hKψ, hψsupport⟩
    have hKψclosed := t2_compact_isClosed hKψ
    have hsupport : Function.support Q ⊆ Kψ := by
      intro z hz
      apply hψsupport
      have hψne : (ψ z : ℂ) ≠ 0 := by
        intro hzero
        apply hz
        simp [Q, hzero]
      exact hψne
    change IsCompact (tsupport Q)
    exact hKψ.of_isClosed_subset (isClosed_tsupport _) <|
      closure_minimal hsupport hKψclosed
  have hQint : Integrable Q (volX F) := hQcont.integrable_of_hasCompactSupport hQcompact
  have hpoint (z : X F) : ∑' γ : Γ, Q ((γ : SL(2,𝓞 F)) • z) = H z := by
    by_cases hz : z ∈ orbitSaturation F Γ K
    · obtain ⟨S, hSsum, hSzero⟩ := t2_periodize_eq_sum Γ ψ hψcompact z
      have hsumReal : (∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z)) =
          ∑ γ ∈ S, ψ ((γ : SL(2,𝓞 F)) • z) := by
        simpa [t2_periodize] using hSsum
      have hpartFin : ∑ γ ∈ S, ψ ((γ : SL(2,𝓞 F)) • z) = 1 := by
        calc
          _ = ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) := hsumReal.symm
          _ = 1 := hpartition z hz
      have hSzeroC (γ : Γ) (hγ : γ ∉ S) :
          (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) = 0 := by
        exact_mod_cast hSzero γ hγ
      have hsumC : (∑' γ : Γ, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ)) =
          ∑ γ ∈ S, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) :=
        tsum_eq_sum (s := S) hSzeroC
      have hpartC : ∑ γ ∈ S, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) = 1 := by
        exact_mod_cast hpartFin
      have hterm (γ : Γ) : Q ((γ : SL(2,𝓞 F)) • z) =
          (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) * H z := by
        simp [Q, hHinv γ γ.property z]
      calc
        _ = ∑' γ : Γ, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) * H z := tsum_congr hterm
        _ = (∑' γ : Γ, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ)) * H z := tsum_mul_right
        _ = H z := by rw [hsumC, hpartC]; simp
    · have hHz : H z = 0 := by
        by_contra hne
        exact hz (hHsupport hne)
      have hterm (γ : Γ) : Q ((γ : SL(2,𝓞 F)) • z) = 0 := by
        simp [Q, hHinv γ γ.property z, hHz]
      have hfun : (fun γ : Γ => Q ((γ : SL(2,𝓞 F)) • z)) = 0 := by
        funext γ
        exact hterm γ
      rw [hfun, hHz]
      change (∑' γ : Γ, (0 : ℂ)) = 0
      exact tsum_zero
  calc
    ∫ z in D, H z ∂(volX F) =
        ∫ z in D, (∑' γ : Γ, Q ((γ : SL(2,𝓞 F)) • z)) ∂(volX F) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => (hpoint z).symm
    _ = ∫ z, Q z ∂(volX F) := t3_integral_unfold Γ D hD Q hQint

private theorem t3_partialLap_zero_of_open_zero (w : InfinitePlace F)
    (f : X F → ℂ) (U : Set (X F)) (hU : IsOpen U) {z : X F}
    (hz : z ∈ U) (hzero : ∀ x ∈ U, f x = 0) :
    partialLap F w f z = 0 := by
  classical
  obtain ⟨e, hept, hecoords⟩ := t2_chartEquiv (F := F)
  let Pos := {p : Coord F // p ∈ posSet F}
  let V : Set Pos := e ⁻¹' U
  have hV : IsOpen V := hU.preimage e.continuous
  let W : Set (Coord F) := Subtype.val '' V
  have hW : IsOpen W := (t2_posSet_open (F := F)).isOpenMap_subtype_val V hV
  let p : Coord F := coordsX F z
  have hpPos : p ∈ posSet F := by
    dsimp [p]
    rw [← hecoords z]
    exact (e.symm z).property
  have hpcoord : (e.symm z).1 = p := hecoords z
  have hpW : p ∈ W := ⟨e.symm z, by simpa [V] using hz, hpcoord⟩
  have hptU : ∀ q ∈ W, ptX F q ∈ U := by
    intro q hq
    rcases hq with ⟨q', hq', hqq'⟩
    change e q' ∈ U at hq'
    rw [← hqq', ← hept q']
    exact hq'
  have hcoordZero (q : Coord F) (hq : q ∈ W) : f (ptX F q) = 0 :=
    hzero (ptX F q) (hptU q hq)
  have hcoordLocal (q : Coord F) (hq : q ∈ W) :
      (fun r : Coord F => f (ptX F r)) =ᶠ[𝓝 q] 0 := by
    filter_upwards [hW.mem_nhds hq] with r hr
    exact hcoordZero r hr
  have hderivLocal (q : Coord F) (hq : q ∈ W) :
      fderiv ℝ (fun r : Coord F => f (ptX F r)) q = 0 := by
    rw [(hcoordLocal q hq).fderiv_eq]
    simp
  have hfirst : fderiv ℝ (f ∘ ptX F) p = 0 := by
    simpa [Function.comp_def, p] using hderivLocal p hpW
  have hderivEventually : (fun q : Coord F =>
      fderiv ℝ (fun r : Coord F => f (ptX F r)) q) =ᶠ[𝓝 p] 0 := by
    filter_upwards [hW.mem_nhds hpW] with q hq
    exact hderivLocal q hq
  have hsecond : fderiv ℝ (fderiv ℝ (fun q : Coord F => f (ptX F q))) p = 0 := by
    rw [hderivEventually.fderiv_eq]
    simp
  let e1 : Coord F := Pi.single w ((1 : ℂ), (0 : ℝ))
  let e2 : Coord F := Pi.single w (Complex.I, (0 : ℝ))
  let e3 : Coord F := Pi.single w ((0 : ℂ), (1 : ℝ))
  have hsecondEval (a b : Coord F) :
      iteratedFDeriv ℝ 2 (fun q : Coord F => f (ptX F q)) p ![a, b] = 0 := by
    rw [iteratedFDeriv_two_apply, hsecond]
    simp
  change ((coordsX F z w).2 : ℂ) *
      fderiv ℝ (f ∘ ptX F) (coordsX F z) e3 -
        ((coordsX F z w).2 : ℂ) ^ 2 *
          (iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e1, e1] +
            iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e2, e2] +
            iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e3, e3]) = 0
  rw [hfirst]
  have hs1 : iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e1, e1] = 0 := by
    simpa [Function.comp_def, p] using hsecondEval e1 e1
  have hs2 : iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e2, e2] = 0 := by
    simpa [Function.comp_def, p] using hsecondEval e2 e2
  have hs3 : iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e3, e3] = 0 := by
    simpa [Function.comp_def, p] using hsecondEval e3 e3
  rw [hs1, hs2, hs3]
  simp

private theorem t3_partialLap_invariant (Γ : Subgroup SL(2,𝓞 F))
    (ψ : X F → ℝ) (hψ : IsSmoothRealX F ψ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ)))
    (f : X F → ℂ) (hfInv : IsGammaInvariant F Γ f) (hf : IsSmoothX F f)
    (γ : Γ) (w : InfinitePlace F) (z : X F) :
    partialLap F w f ((γ : SL(2,𝓞 F)) • z) = partialLap F w f z := by
  let gAct : InfinitePlace F → SL(2,ℂ) := toInf F (toSLF F (γ : SL(2,𝓞 F)))
  have hact (x : X F) : actAtPlaces F gAct x =
      (γ : SL(2,𝓞 F)) • x := rfl
  have hcomp : (fun x => f (actAtPlaces F gAct x)) = f := by
    funext x
    rw [hact]
    exact hfInv γ γ.property x
  have hψC : IsSmoothX F (fun x => (ψ x : ℂ)) := t3_ofReal_smooth ψ hψ
  have hcomm := (G5_green_x f (fun x => (ψ x : ℂ)) hf hψC hψcompact).2.2
    gAct f hf w z
  calc
    partialLap F w f ((γ : SL(2,𝓞 F)) • z) = partialLap F w f (actAtPlaces F gAct z) := by
      rw [hact]
    _ = partialLap F w (fun x => f (actAtPlaces F gAct x)) z := hcomm.symm
    _ = partialLap F w f z := by rw [hcomp]

private theorem t3_continuous_compact_integrable (q : X F → ℂ)
    (hq : Continuous q) (hcompact : HasCompactSupport q) :
    Integrable q (volX F) := by
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
      OpensMeasurableSpace ((fun _ : InfinitePlace F => H3) w) :=
    fun _ => BorelSpace.opensMeasurable
  letI : OpensMeasurableSpace (X F) := by
    exact @Pi.opensMeasurableSpace (InfinitePlace F) (fun _ => H3) Finite.to_countable
      (fun _ => inferInstance) (fun _ => inferInstance)
      (fun _ => hsecH3) (fun _ => BorelSpace.opensMeasurable)
  letI : IsFiniteMeasureOnCompacts (volX F) :=
    ⟨fun hK => (G3_volume (F := F)).2.2.1 hK⟩
  exact hq.integrable_of_hasCompactSupport hcompact

private theorem t3_mul_hasCompactSupportX (φ g : X F → ℂ)
    (hφcompact : HasCompactSupportX F φ) :
    HasCompactSupportX F (fun z => φ z * g z) := by
  rcases hφcompact with ⟨K, hK, hφsupport⟩
  refine ⟨K, hK, ?_⟩
  intro z hz
  apply hφsupport
  intro hφzero
  apply hz
  simp [hφzero]

private theorem t3_compact_mul_integrable (ψ : X F → ℝ) (hψcont : Continuous ψ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ)))
    (H : X F → ℂ) (hHcont : Continuous H) :
    Integrable (fun z => (ψ z : ℂ) * H z) (volX F) := by
  let q : X F → ℂ := fun z => (ψ z : ℂ) * H z
  have hqcont : Continuous q := by
    dsimp [q]
    exact Complex.ofRealCLM.continuous.comp hψcont |>.mul hHcont
  have hqcompact : HasCompactSupport q := by
    rcases hψcompact with ⟨K, hK, hψsupport⟩
    have hKclosed := t2_compact_isClosed hK
    have hsupport : Function.support q ⊆ K := by
      intro z hz
      apply hψsupport
      have hψne : (ψ z : ℂ) ≠ 0 := by
        intro hzero
        apply hz
        simp [q, hzero]
      exact hψne
    change IsCompact (tsupport q)
    exact hK.of_isClosed_subset (isClosed_tsupport _) <|
      closure_minimal hsupport hKclosed
  simpa [q] using t3_continuous_compact_integrable q hqcont hqcompact

private theorem t3_partition_gradient_correction_zero
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (K : Set (X F)) (hK : IsCompact K)
    (ψ : X F → ℝ) (hψ : IsSmoothRealX F ψ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ)))
    (U : Set (X F)) (hU : IsOpen U)
    (hUsat : orbitSaturation F Γ K ⊆ U)
    (hpartition : ∀ z ∈ U,
      ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) = 1)
    (a u : X F → ℂ) (haCont : Continuous a)
    (haInv : IsGammaInvariant F Γ a)
    (hOffSupport : ∀ z, z ∉ orbitSaturation F Γ K →
      a z = 0 ∨ ∀ x, x ∉ orbitSaturation F Γ K → u x = 0)
    (hu : IsGammaInvariant F Γ u) (huSmooth : IsSmoothX F u)
    (w : InfinitePlace F) :
    (∫ z, a z * placeGradInner F w u (fun x => (ψ x : ℂ)) z ∂(volX F) = 0) ∧
      Integrable (fun z => a z * placeGradInner F w u (fun x => (ψ x : ℂ)) z)
        (volX F) := by
  classical
  let ψC : X F → ℂ := fun z => (ψ z : ℂ)
  let Q : X F → ℂ := fun z => a z * placeGradInner F w u ψC z
  have hψCsmooth : IsSmoothX F ψC := t3_ofReal_smooth ψ hψ
  have hinnerCont : Continuous (placeGradInner F w u ψC) :=
    t3_placeGradInner_continuous w u ψC huSmooth hψCsmooth
  have hQcont : Continuous Q := by
    dsimp [Q]
    exact haCont.mul hinnerCont
  have hQcompact : HasCompactSupport Q := by
    rcases hψcompact with ⟨Kψ, hKψ, hψsupport⟩
    have hKψclosed := t2_compact_isClosed hKψ
    have hQsupport : Function.support Q ⊆ Kψ := by
      intro z hz
      by_contra hzK
      have hgrad := t3_placeGradient_zero_of_not_compact w ψ Kψ hKψ hψsupport hzK
      have hgrad' : placeGradient F w ψC z = 0 := by
        simpa [ψC] using hgrad
      have hinner : placeGradInner F w u ψC z = 0 := by
        simp [placeGradInner, hgrad']
      have hQzero : Q z = 0 := by simp [Q, hinner]
      have hQne : Q z ≠ 0 := by simpa [Function.mem_support] using hz
      exact hQne hQzero
    change IsCompact (tsupport Q)
    exact hKψ.of_isClosed_subset (isClosed_tsupport _) <|
      closure_minimal hQsupport hKψclosed
  have hQint := t3_continuous_compact_integrable Q hQcont hQcompact
  have hG4pair (γ : Γ) (z : X F) :
      placeGradInner F w u (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z =
        placeGradInner F w u ψC ((γ : SL(2,𝓞 F)) • z) := by
    let gAct : InfinitePlace F → SL(2,ℂ) := toInf F (toSLF F (γ : SL(2,𝓞 F)))
    have hact (x : X F) : actAtPlaces F gAct x =
        (γ : SL(2,𝓞 F)) • x := rfl
    have hucomp : (fun x => u (actAtPlaces F gAct x)) = u := by
      funext x
      rw [hact]
      exact hu γ γ.property x
    have hψcomp : (fun x => ψC (actAtPlaces F gAct x)) =
        (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) := by
      funext x
      rw [hact]
    have hG := (G4_energy gAct u ψC huSmooth hψCsmooth).1 w z
    calc
      placeGradInner F w u (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z =
          placeGradInner F w (fun x => u (actAtPlaces F gAct x))
            (fun x => ψC (actAtPlaces F gAct x)) z := by
        rw [hucomp, hψcomp]
      _ = placeGradInner F w u ψC (actAtPlaces F gAct z) := hG
      _ = placeGradInner F w u ψC ((γ : SL(2,𝓞 F)) • z) := by rw [hact]
  have hPone (x : X F) (hx : x ∈ U) :
      (t2_periodize Γ ψ x : ℂ) = 1 := by
    have hreal : t2_periodize Γ ψ x = 1 := by
      simpa [t2_periodize] using hpartition x hx
    exact_mod_cast hreal
  have hPgrad (z : X F) (hz : z ∈ U) :
      placeGradient F w (fun x => (t2_periodize Γ ψ x : ℂ)) z = 0 := by
    have hcongr := t3_placeGradient_congr_open w
      (fun x => (t2_periodize Γ ψ x : ℂ)) (fun _ => (1 : ℂ)) U hU hz hPone
    have hgradOne : placeGradient F w (fun _ => (1 : ℂ)) z = 0 := by
      ext j
      simp [placeGradient, Function.comp_def]
    exact hcongr.trans hgradOne
  have hPinner (z : X F) (hz : z ∈ U) :
      placeGradInner F w u (fun x => (t2_periodize Γ ψ x : ℂ)) z = 0 := by
    simp [placeGradInner, hPgrad z hz]
  have hsumInner (z : X F) :=
    t3_periodize_gradInner Γ w u huSmooth ψ hψ hψcompact z
  have htermEq (γ : Γ) (z : X F) : Q ((γ : SL(2,𝓞 F)) • z) =
      a z * placeGradInner F w u
        (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z := by
    dsimp [Q]
    rw [haInv γ γ.property z, ← hG4pair γ z]
  have hSatClosed := t2_orbitSaturation_closed Γ K hK
  have hsumZero (z : X F) : ∑' γ : Γ, Q ((γ : SL(2,𝓞 F)) • z) = 0 := by
    by_cases hzSat : z ∈ orbitSaturation F Γ K
    · have hzU := hUsat hzSat
      calc
        _ = ∑' γ : Γ, a z * placeGradInner F w u
              (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z :=
            tsum_congr (fun γ => htermEq γ z)
        _ = a z * ∑' γ : Γ, placeGradInner F w u
              (fun x => (ψ ((γ : SL(2,𝓞 F)) • x) : ℂ)) z := tsum_mul_left
        _ = a z * placeGradInner F w u
              (fun x => (t2_periodize Γ ψ x : ℂ)) z := by rw [hsumInner z]
        _ = 0 := by rw [hPinner z hzU]; simp
    · rcases hOffSupport z hzSat with ha0 | huZero
      · have hterm (γ : Γ) : Q ((γ : SL(2,𝓞 F)) • z) = 0 := by
          rw [htermEq γ z, ha0]
          simp
        have hfun : (fun γ : Γ => Q ((γ : SL(2,𝓞 F)) • z)) = 0 := by
          funext γ
          exact hterm γ
        rw [hfun]
        change (∑' γ : Γ, (0 : ℂ)) = 0
        exact tsum_zero
      · have hgradU : placeGradient F w u z = 0 := by
          have hUzero : IsOpen (orbitSaturation F Γ K)ᶜ := hSatClosed.isOpen_compl
          have hcongr := t3_placeGradient_congr_open w u (fun _ => (0 : ℂ))
            (orbitSaturation F Γ K)ᶜ hUzero hzSat (fun x hx => huZero x hx)
          have hzeroGrad : placeGradient F w (fun _ => (0 : ℂ)) z = 0 := by
            ext j
            simp [placeGradient, Function.comp_def]
          exact hcongr.trans hzeroGrad
        have hterm (γ : Γ) : Q ((γ : SL(2,𝓞 F)) • z) = 0 := by
          rw [htermEq γ z]
          simp [placeGradInner, hgradU]
        have hfun : (fun γ : Γ => Q ((γ : SL(2,𝓞 F)) • z)) = 0 := by
          funext γ
          exact hterm γ
        rw [hfun]
        change (∑' γ : Γ, (0 : ℂ)) = 0
        exact tsum_zero
  refine ⟨?_, hQint⟩
  change ∫ z, Q z ∂(volX F) = 0
  calc
    ∫ z, Q z ∂(volX F) =
        ∫ z in D, (∑' γ : Γ, Q ((γ : SL(2,𝓞 F)) • z)) ∂(volX F) :=
      (t3_integral_unfold Γ D hD Q hQint).symm
    _ = ∫ z in D, (0 : ℂ) ∂(volX F) := by
      apply integral_congr_ae
      exact ae_of_all _ hsumZero
    _ = 0 := by simp

private theorem t3_mul_smooth (f g : X F → ℂ)
    (hf : IsSmoothX F f) (hg : IsSmoothX F g) :
    IsSmoothX F (fun z => f z * g z) := by
  unfold IsSmoothX at *
  simpa only [Function.comp_def] using hf.mul hg

private theorem t3_placeGradBilinear_mul_right (w : InfinitePlace F)
    (a b c : X F → ℂ) (ha : IsSmoothX F a) (hb : IsSmoothX F b)
    (hc : IsSmoothX F c) (z : X F) :
    placeGradBilinear F w a (fun x => b x * c x) z =
      b z * placeGradBilinear F w a c z + c z * placeGradBilinear F w a b z := by
  unfold placeGradBilinear
  rw [show (fun j : Fin 3 => placeGradient F w a z j *
      placeGradient F w (fun x => b x * c x) z j) =
      (fun j => placeGradient F w a z j *
        (b z * placeGradient F w c z j + c z * placeGradient F w b z j)) by
    funext j
    rw [t3_placeGradient_mul w b c hb hc z j]]
  calc
    _ = ∑ j : Fin 3,
        (b z * (placeGradient F w a z j * placeGradient F w c z j) +
          c z * (placeGradient F w a z j * placeGradient F w b z j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

private theorem t3_placeGradBilinear_star_left (w : InfinitePlace F)
    (f g : X F → ℂ) (hf : IsSmoothX F f) (hg : IsSmoothX F g) (z : X F) :
    placeGradBilinear F w (fun x => star (f x)) g z = placeGradInner F w f g z := by
  unfold placeGradBilinear placeGradInner
  apply Finset.sum_congr rfl
  intro j hj
  rw [t3_placeGradient_star w f hf z j]

private theorem t3_placeGradBilinear_star_right (w : InfinitePlace F)
    (f g : X F → ℂ) (hf : IsSmoothX F f) (hg : IsSmoothX F g) (z : X F) :
    placeGradBilinear F w g (fun x => star (f x)) z = placeGradInner F w f g z := by
  unfold placeGradBilinear placeGradInner
  apply Finset.sum_congr rfl
  intro j hj
  rw [t3_placeGradient_star w f hf z j]
  ring

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
  classical
  rcases T2_tests Γ D hD with ⟨hmem, ⟨toL2, gradL2, hmassRep, hgradRep, hpart⟩⟩
  have hBoth : ∀ f : X F → ℂ, f ∈ testSubmodule F Γ →
      ∀ g : X F → ℂ, IsGammaInvariant F Γ g → IsSmoothX F g →
      ∀ w : InfinitePlace F,
        (∫ z in D, star (f z) * partialLap F w g z ∂(volX F) =
          ∫ z in D, placeGradInner F w f g z ∂(volX F)) ∧
        (∫ z in D, star (partialLap F w f z) * g z ∂(volX F) =
          ∫ z in D, placeGradInner F w f g z ∂(volX F)) := by
    intro f hf g hgInv hgSmooth w
    rcases (hmem f).mp hf with ⟨hfInv, hfSmooth, hfSupportMod⟩
    rcases hfSupportMod with ⟨K, hK, hfSupport⟩
    rcases hpart K hK with
      ⟨ψ, hψsmooth, hψcompact, hψnonneg, hψlocal,
        ⟨U, hUopen, hUsat, hpartitionU⟩, hReconstruct⟩
    let ψC : X F → ℂ := fun z => (ψ z : ℂ)
    let fStar : X F → ℂ := fun z => star (f z)
    let gStar : X F → ℂ := fun z => star (g z)
    let H₁ : X F → ℂ := fun z => star (f z) * partialLap F w g z
    let H₂ : X F → ℂ := fun z => star (partialLap F w f z) * g z
    let J : X F → ℂ := placeGradInner F w f g
    have hψCsmooth : IsSmoothX F ψC := t3_ofReal_smooth ψ hψsmooth
    have hψCcompact : HasCompactSupportX F ψC := by simpa [ψC] using hψcompact
    have hψcont : Continuous ψ := t2_realSmooth_continuous ψ hψsmooth
    have hpartSat : ∀ z ∈ orbitSaturation F Γ K,
        ∑' γ : Γ, ψ ((γ : SL(2,𝓞 F)) • z) = 1 := by
      intro z hz
      exact hpartitionU z (hUsat hz)
    have hSatClosed : IsClosed (orbitSaturation F Γ K) :=
      t2_orbitSaturation_closed Γ K hK
    have hLapFInv : IsGammaInvariant F Γ (partialLap F w f) := by
      intro γ hγ z
      exact t3_partialLap_invariant Γ ψ hψsmooth hψcompact f hfInv hfSmooth
        ⟨γ, hγ⟩ w z
    have hLapGInv : IsGammaInvariant F Γ (partialLap F w g) := by
      intro γ hγ z
      exact t3_partialLap_invariant Γ ψ hψsmooth hψcompact g hgInv hgSmooth
        ⟨γ, hγ⟩ w z
    have hLapFSupport : {z | partialLap F w f z ≠ 0} ⊆ orbitSaturation F Γ K := by
      intro z hz
      by_contra hzSat
      have hzero : ∀ x ∈ (orbitSaturation F Γ K)ᶜ, f x = 0 := by
        intro x hx
        by_contra hne
        exact hx (hfSupport hne)
      have hLapZero := t3_partialLap_zero_of_open_zero w f
        (orbitSaturation F Γ K)ᶜ hSatClosed.isOpen_compl hzSat hzero
      exact hz hLapZero
    have hJSupport : {z | J z ≠ 0} ⊆ orbitSaturation F Γ K := by
      intro z hz
      by_contra hzSat
      have hzero : ∀ x ∈ (orbitSaturation F Γ K)ᶜ, f x = 0 := by
        intro x hx
        by_contra hne
        exact hx (hfSupport hne)
      have hgradZero := t3_placeGradient_congr_open w f (fun _ => (0 : ℂ))
        (orbitSaturation F Γ K)ᶜ hSatClosed.isOpen_compl hzSat hzero
      have hzeroGrad : placeGradient F w (fun _ => (0 : ℂ)) z = 0 := by
        ext j
        simp [placeGradient, Function.comp_def]
      have hJzero : J z = 0 := by
        change placeGradInner F w f g z = 0
        simp [placeGradInner, hgradZero, hzeroGrad]
      exact hz hJzero
    have hH₁support : {z | H₁ z ≠ 0} ⊆ orbitSaturation F Γ K := by
      intro z hz
      by_contra hzSat
      have hfz : f z = 0 := by
        by_contra hne
        exact hzSat (hfSupport hne)
      exact hz (by simp [H₁, hfz])
    have hH₂support : {z | H₂ z ≠ 0} ⊆ orbitSaturation F Γ K := by
      intro z hz
      by_contra hzSat
      have hLapZero : partialLap F w f z = 0 := by
        by_contra hne
        exact hzSat (hLapFSupport hne)
      exact hz (by simp [H₂, hLapZero])
    have hfcont : Continuous f := t2_smooth_continuous f hfSmooth
    have hgcont : Continuous g := t2_smooth_continuous g hgSmooth
    have hLapFcont : Continuous (partialLap F w f) := t3_partialLap_continuous w f hfSmooth
    have hLapGcont : Continuous (partialLap F w g) := t3_partialLap_continuous w g hgSmooth
    have hH₁cont : Continuous H₁ := by
      dsimp [H₁]
      exact (continuous_star.comp hfcont).mul hLapGcont
    have hH₂cont : Continuous H₂ := by
      dsimp [H₂]
      exact (continuous_star.comp hLapFcont).mul hgcont
    have hJcont : Continuous J := by
      dsimp [J]
      exact t3_placeGradInner_continuous w f g hfSmooth hgSmooth
    have hH₁inv : ∀ γ ∈ Γ, ∀ z, H₁ ((γ : SL(2,𝓞 F)) • z) = H₁ z := by
      intro γ hγ z
      simp [H₁, hfInv γ hγ z, hLapGInv γ hγ z]
    have hH₂inv : ∀ γ ∈ Γ, ∀ z, H₂ ((γ : SL(2,𝓞 F)) • z) = H₂ z := by
      intro γ hγ z
      simp [H₂, hLapFInv γ hγ z, hgInv γ hγ z]
    have hJinv : ∀ γ ∈ Γ, ∀ z, J ((γ : SL(2,𝓞 F)) • z) = J z := by
      intro γ hγ z
      let gAct : InfinitePlace F → SL(2,ℂ) := toInf F (toSLF F (γ : SL(2,𝓞 F)))
      have hact (x : X F) : actAtPlaces F gAct x =
          (γ : SL(2,𝓞 F)) • x := rfl
      have hfcomp : (fun x => f (actAtPlaces F gAct x)) = f := by
        funext x
        rw [hact]
        exact hfInv γ hγ x
      have hgcomp : (fun x => g (actAtPlaces F gAct x)) = g := by
        funext x
        rw [hact]
        exact hgInv γ hγ x
      have hG4 := (G4_energy gAct f g hfSmooth hgSmooth).1 w z
      calc
        J ((γ : SL(2,𝓞 F)) • z) = J (actAtPlaces F gAct z) := by rw [hact]
        _ = placeGradInner F w (fun x => f (actAtPlaces F gAct x))
              (fun x => g (actAtPlaces F gAct x)) z := hG4.symm
        _ = J z := by rw [hfcomp, hgcomp]
    have hWeight₁ := t3_quotient_weight Γ D hD K ψ hψsmooth hψcompact
      hpartSat H₁ hH₁cont hH₁inv hH₁support
    have hWeight₂ := t3_quotient_weight Γ D hD K ψ hψsmooth hψcompact
      hpartSat H₂ hH₂cont hH₂inv hH₂support
    have hWeightJ := t3_quotient_weight Γ D hD K ψ hψsmooth hψcompact
      hpartSat J hJcont hJinv hJSupport
    have hPsiJint : Integrable (fun z => ψC z * J z) (volX F) :=
      t3_compact_mul_integrable ψ hψcont hψcompact J hJcont
    let φ₁ : X F → ℂ := fun z => ψC z * fStar z
    let φ₂ : X F → ℂ := fun z => ψC z * g z
    have hfStarSmooth : IsSmoothX F fStar := t3_star_smooth f hfSmooth
    have hgStarSmooth : IsSmoothX F gStar := t3_star_smooth g hgSmooth
    have hφ₁smooth : IsSmoothX F φ₁ := t3_mul_smooth ψC fStar hψCsmooth hfStarSmooth
    have hφ₂smooth : IsSmoothX F φ₂ := t3_mul_smooth ψC g hψCsmooth hgSmooth
    have hφ₁compact : HasCompactSupportX F φ₁ := by
      simpa [φ₁, ψC] using t3_mul_hasCompactSupportX ψC fStar hψCcompact
    have hφ₂compact : HasCompactSupportX F φ₂ := by
      simpa [φ₂] using t3_mul_hasCompactSupportX ψC g hψCcompact
    have hBcorrG (z : X F) :
        placeGradBilinear F w g ψC z = placeGradInner F w gStar ψC z := by
      simpa [gStar] using t3_placeGradBilinear_star_left w
        (fun x => star (g x)) ψC (t3_star_smooth g hgSmooth) hψCsmooth z
    have hB₁point (z : X F) :
        placeGradBilinear F w g φ₁ z =
          ψC z * J z + fStar z * placeGradInner F w gStar ψC z := by
      rw [show φ₁ = fun x => ψC x * fStar x by rfl]
      rw [t3_placeGradBilinear_mul_right w g ψC fStar hgSmooth hψCsmooth hfStarSmooth z]
      rw [t3_placeGradBilinear_star_right w f g hfSmooth hgSmooth z, hBcorrG z]
    have hB₂point (z : X F) :
        placeGradBilinear F w fStar φ₂ z =
          ψC z * J z + g z * placeGradInner F w f ψC z := by
      rw [show φ₂ = fun x => ψC x * g x by rfl]
      rw [t3_placeGradBilinear_mul_right w fStar ψC g hfStarSmooth hψCsmooth hgSmooth z]
      rw [t3_placeGradBilinear_star_left w f g hfSmooth hgSmooth z,
        t3_placeGradBilinear_star_left w f ψC hfSmooth hψCsmooth z]
    have hStarFcont : Continuous fStar := continuous_star.comp hfcont
    have hStarGcont : Continuous gStar := continuous_star.comp hgcont
    have hStarFInv : IsGammaInvariant F Γ fStar := by
      intro γ hγ z
      simp [fStar, hfInv γ hγ z]
    have hStarGInv : IsGammaInvariant F Γ gStar := by
      intro γ hγ z
      simp [gStar, hgInv γ hγ z]
    have hOffStarF : ∀ z, z ∉ orbitSaturation F Γ K →
        fStar z = 0 ∨ ∀ x, x ∉ orbitSaturation F Γ K → gStar x = 0 := by
      intro z hz
      left
      have hfz : f z = 0 := by
        by_contra hne
        exact hz (hfSupport hne)
      simp [fStar, hfz]
    have hOffG : ∀ z, z ∉ orbitSaturation F Γ K →
        g z = 0 ∨ ∀ x, x ∉ orbitSaturation F Γ K → f x = 0 := by
      intro z hz
      right
      intro x hx
      by_contra hne
      exact hx (hfSupport hne)
    have hCorr₁ := t3_partition_gradient_correction_zero Γ D hD K hK ψ hψsmooth
      hψcompact U hUopen hUsat hpartitionU fStar gStar hStarFcont hStarFInv
      hOffStarF hStarGInv hgStarSmooth w
    have hCorr₂ := t3_partition_gradient_correction_zero Γ D hD K hK ψ hψsmooth
      hψcompact U hUopen hUsat hpartitionU g f hgcont hgInv hOffG hfInv hfSmooth w
    have hA₁int : Integrable (fun z => ψC z * J z) (volX F) := hPsiJint
    have hB₁int : Integrable (fun z => fStar z * placeGradInner F w gStar ψC z)
        (volX F) := by simpa [fStar, gStar, ψC] using hCorr₁.2
    have hB₂int : Integrable (fun z => g z * placeGradInner F w f ψC z)
        (volX F) := by simpa [ψC] using hCorr₂.2
    have hGreen₁ := (G5_green_x g φ₁ hgSmooth hφ₁smooth hφ₁compact).1 w
    have hGreen₂ := (G5_green_x fStar φ₂ hfStarSmooth hφ₂smooth hφ₂compact).1 w
    have hLeft₁ :
        ∫ z, ψC z * H₁ z ∂(volX F) =
          ∫ z, partialLap F w g z * φ₁ z ∂(volX F) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by simp [H₁, φ₁, ψC, fStar]; ring
    have hRight₁ :
        ∫ z, placeGradBilinear F w g φ₁ z ∂(volX F) =
          ∫ z, ψC z * J z + fStar z * placeGradInner F w gStar ψC z ∂(volX F) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => hB₁point z
    have hRight₂ :
        ∫ z, placeGradBilinear F w fStar φ₂ z ∂(volX F) =
          ∫ z, ψC z * J z + g z * placeGradInner F w f ψC z ∂(volX F) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => hB₂point z
    have hExpand₁ :
        ∫ z, ψC z * J z + fStar z * placeGradInner F w gStar ψC z ∂(volX F) =
          ∫ z, ψC z * J z ∂(volX F) +
            ∫ z, fStar z * placeGradInner F w gStar ψC z ∂(volX F) :=
      integral_add hA₁int hB₁int
    have hExpand₂ :
        ∫ z, ψC z * J z + g z * placeGradInner F w f ψC z ∂(volX F) =
          ∫ z, ψC z * J z ∂(volX F) +
            ∫ z, g z * placeGradInner F w f ψC z ∂(volX F) :=
      integral_add hA₁int hB₂int
    have hWhole₁ :
        ∫ z, ψC z * H₁ z ∂(volX F) = ∫ z, ψC z * J z ∂(volX F) := by
      calc
        _ = ∫ z, partialLap F w g z * φ₁ z ∂(volX F) := hLeft₁
        _ = ∫ z, placeGradBilinear F w g φ₁ z ∂(volX F) := hGreen₁
        _ = ∫ z, ψC z * J z + fStar z * placeGradInner F w gStar ψC z ∂(volX F) := hRight₁
        _ = ∫ z, ψC z * J z ∂(volX F) +
              ∫ z, fStar z * placeGradInner F w gStar ψC z ∂(volX F) := hExpand₁
        _ = ∫ z, ψC z * J z ∂(volX F) := by rw [hCorr₁.1]; simp
    have hWhole₂ :
        ∫ z, ψC z * H₂ z ∂(volX F) = ∫ z, ψC z * J z ∂(volX F) := by
      calc
        _ = ∫ z, partialLap F w fStar z * φ₂ z ∂(volX F) := by
          apply integral_congr_ae
          exact ae_of_all _ fun z => by
            change ψC z * (star (partialLap F w f z) * g z) =
              partialLap F w (fun x => star (f x)) z * (ψC z * g z)
            rw [t3_partialLap_star w f hfSmooth z]
            ring
        _ = ∫ z, placeGradBilinear F w fStar φ₂ z ∂(volX F) := hGreen₂
        _ = ∫ z, ψC z * J z + g z * placeGradInner F w f ψC z ∂(volX F) := hRight₂
        _ = ∫ z, ψC z * J z ∂(volX F) +
              ∫ z, g z * placeGradInner F w f ψC z ∂(volX F) := hExpand₂
        _ = ∫ z, ψC z * J z ∂(volX F) := by rw [hCorr₂.1]; simp
    refine ⟨?_, ?_⟩
    · calc
        ∫ z in D, H₁ z ∂(volX F) = ∫ z, ψC z * H₁ z ∂(volX F) := hWeight₁
        _ = ∫ z, ψC z * J z ∂(volX F) := hWhole₁
        _ = ∫ z in D, J z ∂(volX F) := hWeightJ.symm
    · calc
        ∫ z in D, H₂ z ∂(volX F) = ∫ z, ψC z * H₂ z ∂(volX F) := hWeight₂
        _ = ∫ z, ψC z * J z ∂(volX F) := hWhole₂
        _ = ∫ z in D, J z ∂(volX F) := hWeightJ.symm
  constructor
  · intro f hf g hgInv hgSmooth w
    exact (hBoth f hf g hgInv hgSmooth w).1
  · intro f hf g hgInv hgSmooth w
    exact (hBoth f hf g hgInv hgSmooth w).2

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
  classical
  let d : SiegelData F Γ := Classical.choice (specGap_siegelData_exists Γ)
  obtain ⟨A₀, hA₀, hsepRaw⟩ := (R10_cusp_separation Γ).2.1 d
  have hA₀pos : 0 < A₀ := lt_of_lt_of_le (by norm_num) hA₀
  have hsepBase : ∀ i j : d.ι, ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d.σ i) := by
    intro i j γ γ' z hi hj
    exact hsepRaw A₀ le_rfl i j γ γ' z hi hj
  have hsepIndex := specGapAllCuspIndex_eq_of_separation d A₀ hsepBase
  let a : ℕ → ℝ := fun n => A₀ + (n : ℝ) + 1
  have hA₀n (n : ℕ) : A₀ ≤ a n := by
    dsimp [a]
    calc
      A₀ ≤ A₀ + (n : ℝ) := le_add_of_nonneg_right (by positivity)
      _ ≤ A₀ + (n : ℝ) + 1 := by linarith
  have hAn (n : ℕ) : 0 < a n := lt_of_lt_of_le hA₀pos (hA₀n n)
  have hsepN (n : ℕ) : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      a n ≤ specGapAllCuspHeight Γ d p z →
      a n ≤ specGapAllCuspHeight Γ d p' z → p = p' := by
    intro p p' z hp hp'
    exact hsepIndex p p' z (le_trans (hA₀n n) hp) (le_trans (hA₀n n) hp')
  obtain ⟨L, hL, hLderiv⟩ := specGapHeightCutoff_deriv_bound_uniform
  let C : ℝ := 2 * L * Real.sqrt (placeCount F)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let ρ : ℕ → X F → ℝ := fun n z => specGapAllCuspRho Γ d (a n) z
  let fn : ℕ → X F → ℂ := fun n z => (ρ n z : ℂ) * f z
  have hρRange (n : ℕ) (z : X F) : 0 ≤ ρ n z ∧ ρ n z ≤ 1 := by
    exact specGapAllCuspRho_bounds d (a n) (hAn n) (hsepN n) z
  have hρSmooth (n : ℕ) : IsSmoothRealX F (ρ n) := by
    exact specGapAllCuspRho_smooth d (a n) (hAn n)
  have hρSmoothC (n : ℕ) : IsSmoothX F (fun x => (ρ n x : ℂ)) := by
    change ContDiffOn ℝ ∞ (fun p => ((ρ n (ptX F p) : ℝ) : ℂ)) (posSet F)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hρSmooth n)
  have hρInv (n : ℕ) (γ : Γ) (z : X F) :
      ρ n ((γ : SL(2,𝓞 F)) • z) = ρ n z :=
    specGapAllCuspRho_invariant d (a n) γ z
  have hρGrad (n : ℕ) (z : X F) :
      ‖fullGradient F (fun x => (ρ n x : ℂ)) z‖ ≤ C := by
    exact specGapAllCuspRho_gradient_bound d (a n) L (hAn n) hL
      (hLderiv (a n) (hAn n)) (hsepN n) z
  have hρSupport (n : ℕ) : ∃ K : Set (X F), IsCompact K ∧
      {z | ρ n z ≠ 0} ⊆ orbitSaturation F Γ K := by
    exact specGapAllCuspRho_support d (a n) (hAn n) (hsepN n)
  have hfnTest (n : ℕ) : IsGammaTest F Γ (fn n) := by
    constructor
    · intro γ hγ z
      simp only [fn]
      rw [hρInv n ⟨γ, hγ⟩ z, hInv γ hγ z]
    constructor
    · change ContDiffOn ℝ ∞
        (fun p => ((ρ n (ptX F p) : ℝ) : ℂ) * f (ptX F p)) (posSet F)
      exact (hρSmoothC n).mul hSmooth
    · rcases hρSupport n with ⟨K, hK, hKsupport⟩
      refine ⟨K, hK, ?_⟩
      intro z hz
      apply hKsupport
      intro hzero
      apply hz
      simp [fn, hzero]
  have hT2 := (T2_tests Γ D hD).1
  have hfnMem (n : ℕ) : fn n ∈ testSubmodule F Γ := (hT2 (fn n)).2 (hfnTest n)
  let t : ℕ → testSubmodule F Γ := fun n => ⟨fn n, hfnMem n⟩
  let μ : Measure (X F) := (volX F).restrict D
  let massErr : ℕ → L2Space F D := fun n => e.toL2 (t n) - fL2
  let gradErr : ℕ → GradientL2Space F D := fun n => e.gradL2 (t n) - grad
  have hfμ : ∀ᵐ z ∂μ, fL2 z = f z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 hfL2
  have hgradμ : ∀ᵐ z ∂μ, grad z = fullGradient F f z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 hgrad
  have hmassRepμ (n : ℕ) : ∀ᵐ z ∂μ, e.toL2 (t n) z = fn n z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 (e.mass_rep (t n))
  have hgradRepμ (n : ℕ) : ∀ᵐ z ∂μ, e.gradL2 (t n) z = fullGradient F (fn n) z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 (e.gradient_rep (t n))
  have hmassRepAll : ∀ᵐ z ∂μ, ∀ n : ℕ, e.toL2 (t n) z = fn n z :=
    ae_all_iff.2 hmassRepμ
  have hgradRepAll : ∀ᵐ z ∂μ, ∀ n : ℕ,
      e.gradL2 (t n) z = fullGradient F (fn n) z := ae_all_iff.2 hgradRepμ
  have hmassSubμ (n : ℕ) : ∀ᵐ z ∂μ,
      massErr n z = e.toL2 (t n) z - fL2 z := by
    change (fun z => (e.toL2 (t n) - fL2) z) =ᵐ[μ] _
    exact Lp.coeFn_sub (e.toL2 (t n)) fL2
  have hgradSubμ (n : ℕ) : ∀ᵐ z ∂μ,
      gradErr n z = e.gradL2 (t n) z - grad z := by
    change (fun z => (e.gradL2 (t n) - grad) z) =ᵐ[μ] _
    exact Lp.coeFn_sub (e.gradL2 (t n)) grad
  have hmassSubAll : ∀ᵐ z ∂μ, ∀ n : ℕ,
      massErr n z = e.toL2 (t n) z - fL2 z := ae_all_iff.2 hmassSubμ
  have hgradSubAll : ∀ᵐ z ∂μ, ∀ n : ℕ,
      gradErr n z = e.gradL2 (t n) z - grad z := ae_all_iff.2 hgradSubμ
  have hfSq : Integrable (fun z => ‖fL2 z‖ ^ 2) μ := specGapLpTwo_integrable_norm_sq μ fL2
  have hgradSq : Integrable (fun z => ‖grad z‖ ^ 2) μ := specGapLpTwo_integrable_norm_sq μ grad
  let massDom : X F → ℝ := fun z => 4 * ‖fL2 z‖ ^ 2
  have hmassDomInt : Integrable massDom μ := by
    dsimp [massDom]
    exact hfSq.const_mul 4
  have hmassBound (n : ℕ) : ∀ᵐ z ∂μ,
      ‖massErr n z‖ ^ 2 ≤ massDom z := by
    filter_upwards [hmassRepAll, hmassSubAll, hfμ] with z hrep hsub hfz
    have hr := hρRange n z
    have hnormρ : ‖(ρ n z : ℂ)‖ = ρ n z := by
      calc
        _ = |ρ n z| := RCLike.norm_ofReal _
        _ = ρ n z := abs_of_nonneg hr.1
    have hnorm : ‖massErr n z‖ ≤ 2 * ‖fL2 z‖ := by
      rw [hsub n, hrep n, hfz]
      calc
        ‖(ρ n z : ℂ) * f z - f z‖ ≤ ‖(ρ n z : ℂ) * f z‖ + ‖f z‖ := norm_sub_le _ _
        _ = ‖(ρ n z : ℂ)‖ * ‖f z‖ + ‖f z‖ := by rw [norm_mul]
        _ ≤ 2 * ‖f z‖ := by rw [hnormρ]; nlinarith [hr.2, norm_nonneg (f z)]
    have hsq := (sq_le_sq₀ (norm_nonneg (massErr n z)) (by positivity)).2 hnorm
    dsimp [massDom]
    nlinarith [hsq]
  have hmassPointwise : ∀ᵐ z ∂μ,
      Tendsto (fun n => ‖massErr n z‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards [hmassRepAll, hmassSubAll, hfμ] with z hrep hsub hfz
    have hzero : ∀ᶠ n : ℕ in atTop, massErr n z = 0 := by
      filter_upwards [specGapAllCuspRho_eventually_one_zero_grad d A₀ hA₀pos z] with n hn
      rw [hsub n, hrep n, hfz]
      simp [fn, ρ, a, hn.1]
    apply tendsto_const_nhds.congr'
    filter_upwards [hzero] with n hn
    change (0 : ℝ) = ‖massErr n z‖ ^ 2
    rw [hn]
    simp
  have hmassMeas (n : ℕ) : AEStronglyMeasurable (fun z => ‖massErr n z‖ ^ 2) μ :=
    ((Lp.aestronglyMeasurable (massErr n)).norm).pow 2
  have hmassDomAE (n : ℕ) : ∀ᵐ z ∂μ,
      ‖‖massErr n z‖ ^ 2‖ ≤ massDom z := by
    filter_upwards [hmassBound n] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hz
  have hmassIntegral : Tendsto (fun n => ∫ z, ‖massErr n z‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ : X F => (0 : ℝ))
      massDom hmassMeas hmassDomInt hmassDomAE hmassPointwise
    simpa using h
  have hmassTendsto : Tendsto massErr atTop (𝓝 0) :=
    specGapLpTwo_tendsto_zero μ massErr hmassIntegral
  let gradDom : X F → ℝ := fun z => 8 * ‖grad z‖ ^ 2 + 2 * C ^ 2 * ‖fL2 z‖ ^ 2
  have hgradDomInt : Integrable gradDom μ := by
    have h1 : Integrable (fun z => 8 * ‖grad z‖ ^ 2) μ := hgradSq.const_mul 8
    have h2 : Integrable (fun z => 2 * C ^ 2 * ‖fL2 z‖ ^ 2) μ := hfSq.const_mul (2 * C ^ 2)
    change Integrable (fun z => 8 * ‖grad z‖ ^ 2 + 2 * C ^ 2 * ‖fL2 z‖ ^ 2) μ
    exact h1.add h2
  have hgradBound (n : ℕ) : ∀ᵐ z ∂μ,
      ‖gradErr n z‖ ^ 2 ≤ gradDom z := by
    filter_upwards [hgradRepAll, hgradSubAll, hgradμ, hfμ] with z hrep hsub hgr hzf
    have hr := hρRange n z
    have hnρ : ‖(ρ n z : ℂ)‖ = ρ n z := by
      calc
        _ = |ρ n z| := RCLike.norm_ofReal _
        _ = ρ n z := abs_of_nonneg hr.1
    have hprod : fullGradient F (fn n) z =
        (ρ n z : ℂ) • fullGradient F f z + f z • fullGradient F (fun x => (ρ n x : ℂ)) z := by
      simpa [fn] using fullGradient_mul (fun x => (ρ n x : ℂ)) f (hρSmoothC n) hSmooth z
    have hnorm : ‖gradErr n z‖ ≤ 2 * ‖grad z‖ + C * ‖fL2 z‖ := by
      rw [hsub n, hrep n]
      rw [hprod]
      calc
        ‖((ρ n z : ℂ) • fullGradient F f z +
              f z • fullGradient F (fun x => (ρ n x : ℂ)) z) - grad z‖ ≤
            ‖(ρ n z : ℂ) • fullGradient F f z‖ +
              ‖f z • fullGradient F (fun x => (ρ n x : ℂ)) z‖ +
              ‖grad z‖ := by
                exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
        _ = ‖(ρ n z : ℂ)‖ * ‖fullGradient F f z‖ +
              ‖f z‖ * ‖fullGradient F (fun x => (ρ n x : ℂ)) z‖ +
              ‖grad z‖ := by simp [norm_smul]
        _ ≤ 2 * ‖grad z‖ + C * ‖fL2 z‖ := by
              have hgmul : ‖fL2 z‖ *
                  ‖fullGradient F (fun x => (ρ n x : ℂ)) z‖ ≤ ‖fL2 z‖ * C :=
                mul_le_mul_of_nonneg_left (hρGrad n z) (norm_nonneg (fL2 z))
              have hfmul : ‖f z‖ *
                  ‖fullGradient F (fun x => (ρ n x : ℂ)) z‖ ≤ ‖f z‖ * C :=
                mul_le_mul_of_nonneg_left (hρGrad n z) (norm_nonneg (f z))
              have hrmul : ρ n z * ‖grad z‖ ≤ ‖grad z‖ := by
                nlinarith [hr.2, norm_nonneg (grad z)]
              have hgrnorm : ‖fullGradient F f z‖ = ‖grad z‖ := by rw [hgr]
              have hfnorm : ‖f z‖ = ‖fL2 z‖ := by rw [← hzf]
              rw [hnρ]
              nlinarith [hgmul, hrmul, hgrnorm, hfnorm, hC,
                norm_nonneg (fL2 z), norm_nonneg (grad z)]
    have hsq := (sq_le_sq₀ (norm_nonneg (gradErr n z)) (by positivity)).2 hnorm
    have hsqAdd : (2 * ‖grad z‖ + C * ‖fL2 z‖) ^ 2 ≤
        8 * ‖grad z‖ ^ 2 + 2 * C ^ 2 * ‖fL2 z‖ ^ 2 := by
      nlinarith [sq_nonneg (2 * ‖grad z‖ - C * ‖fL2 z‖)]
    dsimp [gradDom]
    exact le_trans hsq hsqAdd
  have hgradPointwise : ∀ᵐ z ∂μ,
      Tendsto (fun n => ‖gradErr n z‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards [hgradRepAll, hgradSubAll, hgradμ, hfμ] with z hrep hsub hgr hfz
    have hzero : ∀ᶠ n : ℕ in atTop, gradErr n z = 0 := by
      filter_upwards [specGapAllCuspRho_eventually_one_zero_grad d A₀ hA₀pos z] with n hn
      have hprodRule : fullGradient F (fn n) z =
          (ρ n z : ℂ) • fullGradient F f z +
            f z • fullGradient F (fun x => (ρ n x : ℂ)) z := by
        simpa [fn] using fullGradient_mul (fun x => (ρ n x : ℂ)) f
          (hρSmoothC n) hSmooth z
      have hrhoEq : ρ n z = 1 := by simpa [ρ, a] using hn.1
      have hrhoGrad : fullGradient F (fun x => (ρ n x : ℂ)) z = 0 := by
        simpa [ρ, a] using hn.2
      have hprod : fullGradient F (fn n) z = fullGradient F f z := by
        calc
          _ = (ρ n z : ℂ) • fullGradient F f z +
              f z • fullGradient F (fun x => (ρ n x : ℂ)) z := hprodRule
          _ = fullGradient F f z := by rw [hrhoEq, hrhoGrad]; simp
      rw [hsub n, hrep n, hgr]
      rw [hprod]
      simp
    apply tendsto_const_nhds.congr'
    filter_upwards [hzero] with n hn
    change (0 : ℝ) = ‖gradErr n z‖ ^ 2
    rw [hn]
    simp
  have hgradMeas (n : ℕ) : AEStronglyMeasurable (fun z => ‖gradErr n z‖ ^ 2) μ :=
    ((Lp.aestronglyMeasurable (gradErr n)).norm).pow 2
  have hgradDomAE (n : ℕ) : ∀ᵐ z ∂μ,
      ‖‖gradErr n z‖ ^ 2‖ ≤ gradDom z := by
    filter_upwards [hgradBound n] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hz
  have hgradIntegral : Tendsto (fun n => ∫ z, ‖gradErr n z‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ : X F => (0 : ℝ))
      gradDom hgradMeas hgradDomInt hgradDomAE hgradPointwise
    simpa using h
  have hgradTendsto : Tendsto gradErr atTop (𝓝 0) :=
    specGapLpTwo_tendsto_zero μ gradErr hgradIntegral
  have hmassL2 : Tendsto (fun n => e.toL2 (t n)) atTop (𝓝 fL2) := by
    have h := hmassTendsto.add_const fL2
    simpa [massErr] using h
  have hgradL2 : Tendsto (fun n => e.gradL2 (t n)) atTop (𝓝 grad) := by
    have h := hgradTendsto.add_const grad
    simpa [gradErr] using h
  have hpair : Tendsto (fun n => (e.toL2 (t n), e.gradL2 (t n))) atTop (𝓝 (fL2, grad)) :=
    hmassL2.prodMk_nhds hgradL2
  have htoLp : Continuous (fun p : L2Space F D × GradientL2Space F D => WithLp.toLp 2 p) :=
    WithLp.prod_continuous_toLp 2 (L2Space F D) (GradientL2Space F D)
  have hgraphlim : Tendsto
      (fun n => energyGraphMap e.toL2 e.gradL2 (t n)) atTop
      (𝓝 (WithLp.toLp 2 (fL2, grad))) := by
    change Tendsto (fun n => WithLp.toLp 2 (e.toL2 (t n), e.gradL2 (t n)))
      atTop (𝓝 (WithLp.toLp 2 (fL2, grad)))
    exact (htoLp.tendsto (fL2, grad)).comp hpair
  have hgraphmem := specGap_energyGraph_limit e.toL2 e.gradL2 t fL2 grad hgraphlim
  have hmem : WithLp.toLp 2 (fL2, grad) ∈ E.V := by
    rw [e.graph_eq]
    exact hgraphmem
  refine ⟨⟨WithLp.toLp 2 (fL2, grad), hmem⟩, ?_, ?_⟩ <;>
    simp [FAEnergySpace.M, FAEnergySpace.Gr]

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
  classical
  have hT1 := T1_l2 Γ D hD
  have hT2 := T2_tests Γ D hD
  obtain ⟨hSat, I, hI⟩ := orbitRestrictedMass_eq_indicator Γ D hD K hK
  obtain ⟨toL2, gradL2, hmass, hgrad, hpartition⟩ := hT2.2
  obtain ⟨ψ, hψsmooth, hψcompact, hψnonneg, hψfinite, hψpartition, hreconstruct⟩ :=
    hpartition K hK
  let hψ : RellichPartition Γ K ψ :=
    ⟨hψsmooth, hψcompact, hψnonneg, hψfinite, hψpartition⟩
  have hlocal := quotient_to_chart_finite_overlap Γ D hD E e hT2.1 hT1.2.1
  obtain ⟨c⟩ := localized_chart_H1_membership Γ hT2.1 ψ hψsmooth hψcompact
  obtain ⟨C, hC, hbound⟩ :=
    localized_chart_H1_bound Γ D hD E e hT2.1 hlocal ψ hψsmooth hψcompact c
  obtain ⟨A, B, hA, hB, hAB⟩ := localized_chart_extension Γ D E e ψ c C hC hbound
  obtain ⟨L, hLcompact, hL⟩ := complex_chart_rellich_compact c.support c.compact A B hAB
  have hLrep := rellich_recombine_test_rep Γ D E e ψ c A B hA hB L hL
  obtain ⟨C', hC', hmassbound⟩ :=
    periodization_L2_bound Γ D hD E e hT2.1 hT1.2.1 hT1.2.2.1 K hK ψ hψ I hI L hLrep
  refine ⟨I.comp E.M, ?_, ?_⟩
  · apply rellich_compact_of_test_bound Γ D E e (I.comp E.M) L hLcompact C' hC'
    intro f
    change ‖I (e.toL2 f)‖ ≤ C' * ‖L (rellichTestVector e f)‖
    exact hmassbound f
  · intro x
    filter_upwards [hI.2 (E.M x)] with z hz
    intro hzD
    simpa [orbitRestrictedMass, Set.indicator] using hz hzD

set_option maxHeartbeats 1000000 in
private theorem sgGroundQuotient_test_green_integrable
    {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (f : X F → ℂ) (hfTest : IsGammaTest F Γ f)
    (φ : X F → ℝ) (hφ : IsSmoothRealX F φ)
    (hφInv : IsGammaInvariant F Γ (fun z => (φ z : ℂ)))
    (hφpos : ∀ z, 0 < φ z) :
    ∃ q : X F → ℂ,
      q = (fun z => (specGapGroundQuotient f φ z : ℂ)) ∧
      q ∈ testSubmodule F Γ ∧ IsGammaInvariant F Γ q ∧ IsSmoothX F q ∧
      ∀ w : InfinitePlace F,
        Integrable (fun z => star (q z) *
          partialLap F w (fun x => (φ x : ℂ)) z) ((volX F).restrict D) ∧
        Integrable (placeGradInner F w q (fun x => (φ x : ℂ))) ((volX F).restrict D) ∧
        (∫ z in D, star (q z) *
          partialLap F w (fun x => (φ x : ℂ)) z ∂(volX F)) =
        ∫ z in D, placeGradInner F w q (fun x => (φ x : ℂ)) z ∂(volX F) := by
  classical
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX
  let q : X F → ℂ := fun z => (specGapGroundQuotient f φ z : ℂ)
  have hqReal : IsSmoothRealX F (specGapGroundQuotient f φ) :=
    specGapGroundQuotient_smooth f φ hfTest.2.1 hφ hφpos
  have hqSmooth : IsSmoothX F q := by
    change ContDiffOn ℝ ∞
      (fun p => (specGapGroundQuotient f φ (ptX F p) : ℂ)) (posSet F)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hqReal
  have hqInv : IsGammaInvariant F Γ q := by
    simpa [q] using specGapGroundQuotient_invariant f φ hfTest.1 hφInv
  have hqSupport : {z | q z ≠ 0} ⊆ {z | f z ≠ 0} := by
    intro z hz
    have hqne : specGapGroundQuotient f φ z ≠ 0 := by
      intro hzero
      apply hz
      simp [q, hzero]
    exact sgGroundQuotient_nonzero_implies f φ z hqne
  have hqTest : IsGammaTest F Γ q := by
    refine ⟨hqInv, hqSmooth, ?_⟩
    rcases hfTest.2.2 with ⟨K, hK, hfsupport⟩
    refine ⟨K, hK, ?_⟩
    exact hqSupport.trans hfsupport
  have hqMem : q ∈ testSubmodule F Γ :=
    ((T2_tests Γ D hD).1 q).2 hqTest
  let φC : X F → ℂ := fun z => (φ z : ℂ)
  have hφC : IsSmoothX F φC := by
    change ContDiffOn ℝ ∞ (fun p => (φ (ptX F p) : ℂ)) (posSet F)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  rcases hfTest.2.2 with ⟨K, hK, hfsupport⟩
  let lapFun : InfinitePlace F → X F → ℂ :=
    fun w z => star (q z) * partialLap F w φC z
  let gradFun : InfinitePlace F → X F → ℂ :=
    fun w z => placeGradInner F w q φC z
  have hLapCont (w : InfinitePlace F) : Continuous (lapFun w) := by
    have hqcont := sgSmoothX_continuous q hqSmooth
    have hstar : Continuous (fun z => star (q z)) :=
      Complex.continuous_conj.comp hqcont
    exact hstar.mul (sgPartialLap_continuous φC hφC w)
  have hGradCont (w : InfinitePlace F) : Continuous (gradFun w) :=
    sgPlaceGradInner_continuous q φC hqSmooth hφC w
  have hLapInv (w : InfinitePlace F) : IsGammaInvariant F Γ (lapFun w) := by
    intro γ hγ z
    change star (q ((γ : SL(2,𝓞 F)) • z)) *
        partialLap F w φC ((γ : SL(2,𝓞 F)) • z) =
      star (q z) * partialLap F w φC z
    rw [hqInv γ hγ z]
    rw [sgPartialLap_invariant ⟨γ, hγ⟩ φC hφC hφInv w z]
  have hGradInv (w : InfinitePlace F) : IsGammaInvariant F Γ (gradFun w) := by
    intro γ hγ z
    change placeGradInner F w q φC ((γ : SL(2,𝓞 F)) • z) = _
    exact sgPlaceGradInner_invariant ⟨γ, hγ⟩ q φC hqSmooth hφC hqInv hφInv w z
  have hLapSupport (w : InfinitePlace F) :
      {z | lapFun w z ≠ 0} ⊆ orbitSaturation F Γ K := by
    intro z hz
    apply hfsupport
    intro hfz
    apply hz
    simp [lapFun, q, specGapGroundQuotient, hfz]
  have hGradSupport (w : InfinitePlace F) :
      {z | gradFun w z ≠ 0} ⊆ orbitSaturation F Γ K := by
    intro z hz
    apply hfsupport
    intro hfz
    apply hz
    have hqgrad (j : Fin 3) : placeGradient F w q z j = 0 := by
      simpa [q] using sgGroundQuotient_placeGradient_zero_of_zero
        f φ hfTest.2.1 hφ hqReal hφpos z hfz w j
    simp [gradFun, placeGradInner, hqgrad]
  let μ : Measure (X F) := (volX F).restrict D
  have hLapInt (w : InfinitePlace F) : Integrable (lapFun w) μ :=
    sgIntegrable_of_compactOrbitSupport (Γ := Γ) D hD (lapFun w) (hLapCont w)
      (hLapInv w) (hLapCont w).measurable.aestronglyMeasurable K hK (hLapSupport w)
  have hGradInt (w : InfinitePlace F) : Integrable (gradFun w) μ :=
    sgIntegrable_of_compactOrbitSupport (Γ := Γ) D hD (gradFun w) (hGradCont w)
      (hGradInv w) (hGradCont w).measurable.aestronglyMeasurable K hK (hGradSupport w)
  have hGreen (w : InfinitePlace F) :
      (∫ z in D, star (q z) * partialLap F w φC z ∂(volX F)) =
        ∫ z in D, placeGradInner F w q φC z ∂(volX F) := by
    exact (T3_green_q Γ D hD).1 q hqMem φC hφInv hφC w
  refine ⟨q, rfl, hqMem, hqInv, hqSmooth, ?_⟩
  intro w
  refine ⟨?_, ?_, hGreen w⟩
  · simpa [lapFun, μ] using hLapInt w
  · simpa [gradFun, μ] using hGradInt w

set_option maxHeartbeats 1000000 in
private theorem sgGroundState_test_estimate
    {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (φ : X F → ℝ) (hφ : IsSmoothRealX F φ)
    (hφInv : IsGammaInvariant F Γ (fun z => (φ z : ℂ)))
    (hφpos : ∀ z, 0 < φ z)
    (K : Set (X F)) (a C : ℝ)
    (hRatio : ∀ z, a ≤ sgGroundLaplacianRatio φ z +
      C * (if z ∈ orbitSaturation F Γ K then 1 else 0))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (R : E.V →L[ℂ] L2Space F D)
    (hRrep : ∀ x : E.V, ∀ᵐ z ∂(volX F), z ∈ D →
      R x z = orbitRestrictedMass F D E Γ K x z)
    (t : testSubmodule F Γ) :
    a * ‖E.M (sgEnergyGraphTestPoint D E e t)‖ ^ 2 ≤
      ‖E.Gr (sgEnergyGraphTestPoint D E e t)‖ ^ 2 +
        C * ‖R (sgEnergyGraphTestPoint D E e t)‖ ^ 2 := by
  classical
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX
  let f : X F → ℂ := t
  have hfTest : IsGammaTest F Γ f := ((T2_tests Γ D hD).1 f).mp t.property
  rcases sgGroundQuotient_test_green_integrable D hD f hfTest φ hφ hφInv hφpos with
    ⟨q, hqEq, hqMem, hqInv, hqSmooth, hGreen⟩
  subst q
  let q : X F → ℂ := fun z => (specGapGroundQuotient f φ z : ℂ)
  let φC : X F → ℂ := fun z => (φ z : ℂ)
  have hφC : IsSmoothX F φC := by
    change ContDiffOn ℝ ∞ (fun p => (φ (ptX F p) : ℂ)) (posSet F)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  have hqReal : IsSmoothRealX F (specGapGroundQuotient f φ) :=
    specGapGroundQuotient_smooth f φ hfTest.2.1 hφ hφpos
  let x : E.V := sgEnergyGraphTestPoint D E e t
  have hMx : E.M x = e.toL2 t := by
    simp [x, sgEnergyGraphTestPoint, FAEnergySpace.M, energyGraphMap]
  have hGrx : E.Gr x = e.gradL2 t := by
    simp [x, sgEnergyGraphTestPoint, FAEnergySpace.Gr, energyGraphMap]
  let μ : Measure (X F) := (volX F).restrict D
  have hmassRep : ∀ᵐ z ∂μ, e.toL2 t z = f z := by
    exact (ae_restrict_iff'₀ hD.nullMeasurableSet).2 (e.mass_rep t)
  have hgradRep : ∀ᵐ z ∂μ, e.gradL2 t z = fullGradient F f z := by
    exact (ae_restrict_iff'₀ hD.nullMeasurableSet).2 (e.gradient_rep t)
  have hmassSqAE : (fun z => ‖e.toL2 t z‖ ^ 2) =ᵐ[μ]
      fun z => Complex.normSq (f z) := by
    filter_upwards [hmassRep] with z hz
    rw [hz]
    simp [Complex.normSq_eq_norm_sq]
  have hmassSqInt : Integrable (fun z => Complex.normSq (f z)) μ :=
    (specGapLpTwo_integrable_norm_sq μ (e.toL2 t)).congr hmassSqAE
  have hmassNorm : ‖e.toL2 t‖ ^ 2 = ∫ z, Complex.normSq (f z) ∂μ := by
    calc
      ‖e.toL2 t‖ ^ 2 = ∫ z, ‖e.toL2 t z‖ ^ 2 ∂μ :=
        specGapLpTwo_norm_sq_eq_integral μ (e.toL2 t)
      _ = ∫ z, Complex.normSq (f z) ∂μ := integral_congr_ae hmassSqAE
  have hgradSqAE : (fun z => ‖e.gradL2 t z‖ ^ 2) =ᵐ[μ]
      fun z => totalGradNormSq F f z := by
    filter_upwards [hgradRep] with z hz
    rw [hz]
    exact sgFullGradient_norm_sq f z
  have henergyInt : Integrable (fun z => totalGradNormSq F f z) μ :=
    (specGapLpTwo_integrable_norm_sq μ (e.gradL2 t)).congr hgradSqAE
  have hgradNorm : ‖e.gradL2 t‖ ^ 2 =
      ∫ z, totalGradNormSq F f z ∂μ := by
    calc
      ‖e.gradL2 t‖ ^ 2 = ∫ z, ‖e.gradL2 t z‖ ^ 2 ∂μ :=
        specGapLpTwo_norm_sq_eq_integral μ (e.gradL2 t)
      _ = ∫ z, totalGradNormSq F f z ∂μ := integral_congr_ae hgradSqAE
  let S : Set (X F) := orbitSaturation F Γ K
  let err : X F → ℝ := fun z => if z ∈ S then Complex.normSq (f z) else 0
  have hRrepμ : ∀ᵐ z ∂μ, R x z = orbitRestrictedMass F D E Γ K x z := by
    exact (ae_restrict_iff'₀ hD.nullMeasurableSet).2 (hRrep x)
  have hRerrAE : (fun z => ‖R x z‖ ^ 2) =ᵐ[μ] err := by
    filter_upwards [hRrepμ, hmassRep] with z hzR hzm
    rw [hzR]
    by_cases hz : z ∈ S
    · simp [err, orbitRestrictedMass, S, hMx, hzm, hz,
        Complex.normSq_eq_norm_sq]
    · simp [err, orbitRestrictedMass, S, hMx, hzm, hz]
  have hErrInt : Integrable err μ :=
    (specGapLpTwo_integrable_norm_sq μ (R x)).congr hRerrAE
  have hRnorm : ‖R x‖ ^ 2 = ∫ z, err z ∂μ := by
    calc
      ‖R x‖ ^ 2 = ∫ z, ‖R x z‖ ^ 2 ∂μ := specGapLpTwo_norm_sq_eq_integral μ (R x)
      _ = ∫ z, err z ∂μ := integral_congr_ae hRerrAE
  let lapFun : InfinitePlace F → X F → ℂ :=
    fun w z => star (q z) * partialLap F w φC z
  let gradFun : InfinitePlace F → X F → ℂ := fun w z => placeGradInner F w q φC z
  let lapSum : X F → ℂ := fun z => star (q z) * totalLap F φC z
  let gradSum : X F → ℂ := fun z => ∑ w : InfinitePlace F, gradFun w z
  have hLapEachInt (w : InfinitePlace F) : Integrable (lapFun w) μ := (hGreen w).1
  have hGradEachInt (w : InfinitePlace F) : Integrable (gradFun w) μ := (hGreen w).2.1
  have hLapEq (z : X F) : lapSum z = ∑ w : InfinitePlace F, lapFun w z := by
    simp [lapSum, lapFun, totalLap, Finset.mul_sum]
  have hLapSumInt : Integrable lapSum μ := by
    have h := integrable_finsetSum Finset.univ (fun w hw => hLapEachInt w)
    exact h.congr (ae_of_all _ fun z => (hLapEq z).symm)
  have hGradSumInt : Integrable gradSum μ :=
    integrable_finsetSum Finset.univ (fun w hw => hGradEachInt w)
  have hGreenμ (w : InfinitePlace F) :
      ∫ z, lapFun w z ∂μ = ∫ z, gradFun w z ∂μ := by
    simpa [lapFun, gradFun, μ, q, φC] using (hGreen w).2.2
  have hGreenTotal :
      ∫ z, lapSum z ∂μ = ∫ z, gradSum z ∂μ := by
    calc
      ∫ z, lapSum z ∂μ = ∫ z, ∑ w : InfinitePlace F, lapFun w z ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ hLapEq
      _ = ∑ w : InfinitePlace F, ∫ z, lapFun w z ∂μ := by
        rw [integral_finsetSum Finset.univ (fun w hw => hLapEachInt w)]
      _ = ∑ w : InfinitePlace F, ∫ z, gradFun w z ∂μ := by
        apply Finset.sum_congr rfl
        intro w hw
        exact hGreenμ w
      _ = ∫ z, ∑ w : InfinitePlace F, gradFun w z ∂μ := by
        rw [integral_finsetSum Finset.univ (fun w hw => hGradEachInt w)]
      _ = ∫ z, gradSum z ∂μ := by rfl
  have hRatioEq (z : X F) :
      Complex.normSq (f z) * sgGroundLaplacianRatio φ z = (lapSum z).re := by
    calc
      _ = Complex.normSq (f z) *
          ((totalLap F φC z).re / φ z) := by
            simp [sgGroundLaplacianRatio, φC]
      _ = (Complex.normSq (f z) / φ z) * (totalLap F φC z).re := by
            field_simp [ne_of_gt (hφpos z)]
      _ = (lapSum z).re := by
            simp [lapSum, q, specGapGroundQuotient, Complex.conj_ofReal,
              Complex.mul_re]
  have hRatioMassInt :
      Integrable (fun z => Complex.normSq (f z) * sgGroundLaplacianRatio φ z) μ := by
    have h := hLapSumInt.re
    exact h.congr (ae_of_all _ fun z => (hRatioEq z).symm)
  have hRatioGreen :
      (∫ z, Complex.normSq (f z) * sgGroundLaplacianRatio φ z ∂μ) =
        ∫ z, (gradSum z).re ∂μ := by
    calc
      _ = ∫ z, (lapSum z).re ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ hRatioEq
      _ = Complex.re (∫ z, lapSum z ∂μ) := integral_re hLapSumInt
      _ = Complex.re (∫ z, gradSum z ∂μ) := congrArg Complex.re hGreenTotal
      _ = ∫ z, (gradSum z).re ∂μ := (integral_re hGradSumInt).symm
  have hPointwise (z : X F) : (gradSum z).re ≤ totalGradNormSq F f z := by
    have h := specGapGroundQuotient_density_ineq f φ hfTest.2.1 hφ hqReal hφpos z
    change Complex.re (∑ w : InfinitePlace F, ∑ j : Fin 3,
      star (placeGradient F w q z j) * placeGradient F w φC z j) ≤ _
    simpa [q, φC, placeGradInner] using h
  have hCrossInt : Integrable (fun z => (gradSum z).re) μ := hGradSumInt.re
  have hCrossEnergy :
      (∫ z, (gradSum z).re ∂μ) ≤ ∫ z, totalGradNormSq F f z ∂μ :=
    integral_mono hCrossInt henergyInt hPointwise
  have hRatioEnergy :
      (∫ z, Complex.normSq (f z) * sgGroundLaplacianRatio φ z ∂μ) ≤
        ∫ z, totalGradNormSq F f z ∂μ := by
    rw [hRatioGreen]
    exact hCrossEnergy
  have hRatioPointwise (z : X F) :
      a * Complex.normSq (f z) ≤
        Complex.normSq (f z) * sgGroundLaplacianRatio φ z + C * err z := by
    have hmul := mul_le_mul_of_nonneg_right (hRatio z) (Complex.normSq_nonneg (f z))
    have heq :
        (sgGroundLaplacianRatio φ z +
          C * (if z ∈ orbitSaturation F Γ K then 1 else 0)) * Complex.normSq (f z) =
        Complex.normSq (f z) * sgGroundLaplacianRatio φ z + C * err z := by
      by_cases hz : z ∈ orbitSaturation F Γ K <;> simp [err, S, hz] <;> ring
    exact hmul.trans_eq heq
  have hCoefficientInt :
      a * (∫ z, Complex.normSq (f z) ∂μ) ≤
        (∫ z, Complex.normSq (f z) * sgGroundLaplacianRatio φ z ∂μ) +
          C * (∫ z, err z ∂μ) := by
    have h := integral_mono (hmassSqInt.const_mul a)
      (hRatioMassInt.add (hErrInt.const_mul C)) hRatioPointwise
    calc
      _ = ∫ z, a * Complex.normSq (f z) ∂μ := by
        rw [integral_const_mul a]
      _ ≤ ∫ z, Complex.normSq (f z) * sgGroundLaplacianRatio φ z + C * err z ∂μ := h
      _ = (∫ z, Complex.normSq (f z) * sgGroundLaplacianRatio φ z ∂μ) +
          C * (∫ z, err z ∂μ) := by
        rw [integral_add hRatioMassInt (hErrInt.const_mul C), integral_const_mul]
  have hFinalInt :
      a * (∫ z, Complex.normSq (f z) ∂μ) ≤
        (∫ z, totalGradNormSq F f z ∂μ) + C * ‖R x‖ ^ 2 := by
    calc
      _ ≤ (∫ z, Complex.normSq (f z) * sgGroundLaplacianRatio φ z ∂μ) +
            C * (∫ z, err z ∂μ) := hCoefficientInt
      _ ≤ (∫ z, totalGradNormSq F f z ∂μ) + C * (∫ z, err z ∂μ) :=
            by linarith [hRatioEnergy]
      _ = (∫ z, totalGradNormSq F f z ∂μ) + C * ‖R x‖ ^ 2 := by rw [← hRnorm]
  calc
    a * ‖E.M x‖ ^ 2 = a * ‖e.toL2 t‖ ^ 2 := by rw [hMx]
    _ = a * (∫ z, Complex.normSq (f z) ∂μ) := by rw [hmassNorm]
    _ ≤ (∫ z, totalGradNormSq F f z ∂μ) + C * ‖R x‖ ^ 2 := hFinalInt
    _ = ‖e.gradL2 t‖ ^ 2 + C * ‖R x‖ ^ 2 := by rw [← hgradNorm]
    _ = ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2 := by rw [hGrx]

set_option maxHeartbeats 1000000

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
  classical
  letI : Fintype d.ι := d.fintype
  have hι : Nonempty d.ι := by
    let q : Quotient (QuotientGroup.rightRel (borelSL F)) :=
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) (1 : SL(2,F))
    obtain ⟨p, _⟩ := d.reps_bijective.2 q
    exact ⟨p.1⟩
  let i₀ : d.ι := Classical.choice hι
  have hApos : 0 < A := lt_of_lt_of_le (hA₀ i₀) (hA i₀)
  have hsep : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A ≤ specGapAllCuspHeight Γ d p z →
      A ≤ specGapAllCuspHeight Γ d p' z → p = p' := by
    intro p p' z hp hp'
    rcases p with ⟨i, q⟩
    rcases p' with ⟨j, q'⟩
    have hs := hA₀sep i j q.out q'.out z
      ((hA i).trans hp) ((hA j).trans hp')
    rcases hs with ⟨hij, hstab⟩
    subst j
    have hrel : QuotientGroup.rightRel (cuspStab F Γ (d.σ i)) q.out q'.out :=
      QuotientGroup.rightRel_apply.mpr hstab
    have hq : q = q' := q.out_eq.symm.trans ((Quotient.sound hrel).trans q'.out_eq)
    subst q'
    rfl
  let φ : X F → ℝ := specGapGroundPhi d A
  have hφ : IsSmoothRealX F φ := specGapGroundPhi_smooth d A hApos
  have hφInv : IsGammaInvariant F Γ (fun z => (φ z : ℂ)) := by
    intro γ hγ z
    exact congrArg Complex.ofReal (specGapGroundPhi_invariant d A ⟨γ, hγ⟩ z)
  have hφpos (z : X F) : 0 < φ z := by
    have hge := specGapGroundPhi_ge_one d A A hApos le_rfl hsep hApos z
    dsimp [φ]
    linarith
  let K : Set (X F) := ⋃ i, SiegelData.compactBox F d i (2 * A)
  have hK : IsCompact K := by
    have hbox (i : d.ι) : IsCompact (SiegelData.compactBox F d i (2 * A)) :=
      (R13_compact_part Γ d).1 (2 * A) (by positivity) i
    simpa [K] using isCompact_iUnion hbox
  obtain ⟨C₀, hC₀, hRatioK⟩ :=
    sgGroundPhi_compact_ratio_bound d A A hApos le_rfl hsep hApos
  obtain ⟨R, hRcompact, hRrep⟩ := T6_rellich Γ D hD E e K hK
  let a : ℝ := placeCount F * (1 - 1 / (2 * A))
  let C : ℝ := max 0 (a + C₀)
  have hC : 0 ≤ C := le_max_left _ _
  have hCbig : a + C₀ ≤ C := le_max_right _ _
  have hRatio (z : X F) :
      a ≤ sgGroundLaplacianRatio φ z +
        C * (if z ∈ orbitSaturation F Γ K then 1 else 0) := by
    by_cases hz : z ∈ orbitSaturation F Γ K
    · rcases hz with ⟨γ, x, hxK, hγx⟩
      have hInv := sgGroundLaplacianRatio_invariant d A hApos γ x
      have hrz : sgGroundLaplacianRatio φ z = sgGroundLaplacianRatio φ x := by
        rw [← hγx]
        exact hInv
      have hlow : -C₀ ≤ sgGroundLaplacianRatio φ x := hRatioK x hxK
      have hbase : a ≤ sgGroundLaplacianRatio φ x + C := by
        linarith
      have hzS : z ∈ orbitSaturation F Γ K := ⟨γ, x, hxK, hγx⟩
      have hmain : a ≤ sgGroundLaplacianRatio φ z + C := by
        rw [hrz]
        exact hbase
      simpa [hzS] using hmain
    · have hex : ∃ p : SpecGapCuspIndex Γ d,
          2 * A < specGapAllCuspHeight Γ d p z := by
        by_contra hnone
        push_neg at hnone
        have hbound : ∀ p : SpecGapCuspIndex Γ d,
            specGapAllCuspHeight Γ d p z ≤ 2 * A := hnone
        have hmem := sgCompactLow_mem_orbit d (2 * A) (by positivity) z hbound
        change z ∈ orbitSaturation F Γ K at hmem
        exact hz hmem
      rcases hex with ⟨p, hp⟩
      have hhigh := specGapGroundPhi_ratio_high d A A hApos le_rfl hsep hApos p z hp
      simpa [a, φ, hz] using hhigh
  refine ⟨K, hK, C, hC, R, hRcompact, ?_, hRrep⟩
  let pt : testSubmodule F Γ → E.V := fun t => sgEnergyGraphTestPoint D E e t
  have hDense : DenseRange pt := by
    rw [Metric.denseRange_iff]
    intro y ε hε
    have hy : (y : WithLp 2 (L2Space F D × GradientL2Space F D)) ∈
        closure (energyGraphMap e.toL2 e.gradL2).range := by
      change (y : WithLp 2 (L2Space F D × GradientL2Space F D)) ∈
        energyGraph e.toL2 e.gradL2
      exact e.graph_eq ▸ y.property
    obtain ⟨v, hv, hvdist⟩ := (Metric.mem_closure_iff).mp hy ε hε
    rcases hv with ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    change dist y (sgEnergyGraphTestPoint D E e t) < ε
    change dist (y : WithLp 2 (L2Space F D × GradientL2Space F D))
      (energyGraphMap e.toL2 e.gradL2 t) < ε
    exact hvdist
  let good : Set E.V := {x | a * ‖E.M x‖ ^ 2 ≤ ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2}
  have hLcont : Continuous (fun x : E.V => a * ‖E.M x‖ ^ 2) := by fun_prop
  have hRcont : Continuous (fun x : E.V => ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2) := by fun_prop
  have hgoodClosed : IsClosed good := by
    dsimp [good]
    exact isClosed_le hLcont hRcont
  have hRange : Set.range pt ⊆ good := by
    rintro x ⟨t, rfl⟩
    change a * ‖E.M (pt t)‖ ^ 2 ≤ ‖E.Gr (pt t)‖ ^ 2 + C * ‖R (pt t)‖ ^ 2
    exact sgGroundState_test_estimate D hD φ hφ hφInv hφpos K a C hRatio E e R hRrep t
  have hclosure : closure (Set.range pt) ⊆ good := closure_minimal hRange hgoodClosed
  intro x
  have hx : x ∈ closure (Set.range pt) := by
    rw [hDense.closure_range]
    simp
  simpa [good, a] using hclosure hx

end ArtinPrimitiveRoots.A1.Spec
