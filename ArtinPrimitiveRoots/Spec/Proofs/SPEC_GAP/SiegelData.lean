import ArtinPrimitiveRoots.Spec.ReductionExtra

/-! Helpers for the calibrated all-cusp cutoffs in SPEC-GAP. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory Submodule
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem congrSubgroup_finiteIndex (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) :
    (congrSubgroup F N).FiniteIndex := by
  letI : Finite (𝓞 F ⧸ N) := Ring.HasFiniteQuotients.finiteQuotient hN
  letI : Fintype (𝓞 F ⧸ N) := Fintype.ofFinite _
  letI : Fintype (SL(2, 𝓞 F ⧸ N)) := Fintype.ofFinite _
  dsimp [congrSubgroup]
  infer_instance

/-- Choose the pointwise half-open parallelepiped associated to a full cusp translation lattice.
The frozen R1 interface only exposes almost-everywhere coverage of its chosen measurable domain;
the stronger pointwise coverage field of `SiegelData` is obtained from the lattice basis. -/
private theorem cuspTranslationDomain (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (hfull : IsFullZLattice (cuspTranslationsZ F Γ σ)) :
    ∃ P : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain (cuspTranslations F Γ σ) P ∧
      Bornology.IsBounded P ∧ MeasurableSet P ∧
      ∀ x, ∃ μ ∈ cuspTranslations F Γ σ, μ + x ∈ P := by
  classical
  let L : Submodule ℤ (InfinitePlace F → ℂ) := cuspTranslationsZ F Γ σ
  rcases hfull with ⟨hdisc, hZ⟩
  letI : DiscreteTopology L := hdisc
  letI : IsZLattice ℝ L := hZ
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let bZ := Module.Free.chooseBasis ℤ L
  letI : Fintype (Module.Free.ChooseBasisIndex ℤ L) :=
    Module.Free.ChooseBasisIndex.fintype ℤ L
  let b := bZ.ofZLatticeBasis ℝ
  let P := ZSpan.fundamentalDomain b
  have hspan : span ℤ (Set.range b) = L := bZ.ofZLatticeBasis_span ℝ
  have hL : L = (cuspTranslations F Γ σ).toIntSubmodule := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by intro x hx; exact hx)
    · intro x hx
      exact Submodule.subset_span hx
  have hLadd : L.toAddSubgroup = cuspTranslations F Γ σ := by
    simpa using congrArg Submodule.toAddSubgroup hL
  have hspanAdd : (span ℤ (Set.range b)).toAddSubgroup = L.toAddSubgroup :=
    congrArg Submodule.toAddSubgroup hspan
  have hfdL : IsAddFundamentalDomain
      (span ℤ (Set.range b)).toAddSubgroup P (volume : Measure (InfinitePlace F → ℂ)) := by
    simpa [P] using
      (ZSpan.isAddFundamentalDomain' b (volume : Measure (InfinitePlace F → ℂ)))
  have hfd : IsAddFundamentalDomain (cuspTranslations F Γ σ) P := by
    rw [← hLadd, ← hspanAdd]
    exact hfdL
  have hbounded : Bornology.IsBounded P := ZSpan.fundamentalDomain_isBounded b
  have hmeas : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet b
  have hcover : ∀ x, ∃ μ ∈ cuspTranslations F Γ σ, μ + x ∈ P := by
    intro x
    obtain ⟨μ, hμ, -⟩ := (ZSpan.exist_unique_vadd_mem_fundamentalDomain b x)
    have hμL : (μ : InfinitePlace F → ℂ) ∈ L :=
      (congrArg (fun S : Submodule ℤ (InfinitePlace F → ℂ) =>
        (μ : InfinitePlace F → ℂ) ∈ S) hspan).mp μ.property
    have hμtrans : (μ : InfinitePlace F → ℂ) ∈ cuspTranslations F Γ σ := by
      have : (μ : InfinitePlace F → ℂ) ∈ L.toAddSubgroup := hμL
      simpa [hLadd] using this
    refine ⟨(μ : InfinitePlace F → ℂ), hμtrans, ?_⟩
    change (μ : InfinitePlace F → ℂ) + x ∈ P
    rw [← vadd_eq_add]
    exact hμ
  exact ⟨P, hfd, hbounded, hmeas, hcover⟩

/-- The structure fields defining a `SiegelData` package can be selected from the frozen
reduction interfaces, even when the given finite-index group itself has torsion. -/
theorem specGap_siegelData_exists (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    Nonempty (SiegelData F Γ) := by
  classical
  obtain ⟨N, hN, hfreeN⟩ := R11_free_level (F := F)
  let Γ₀ : Subgroup SL(2,𝓞 F) := congrSubgroup F N
  have hΓ₀fin : Γ₀.FiniteIndex := congrSubgroup_finiteIndex (F := F) N hN
  letI : Γ₀.FiniteIndex := hΓ₀fin
  have hHfin : (Γ ⊓ Γ₀).FiniteIndex := inferInstance
  let H : Subgroup SL(2,𝓞 F) := Γ ⊓ Γ₀
  letI : H.FiniteIndex := hHfin
  have hHfree : FreeAction F H := by
    intro γ hγ z hz
    exact hfreeN γ hγ.2 z hz
  have hunitSub (σ : SL(2,F)) : cuspUnits F H σ ≤ cuspUnits F Γ σ := by
    change Subgroup.closure (cuspUnitSet F H σ) ≤ cuspUnits F Γ σ
    rw [Subgroup.closure_le]
    intro ε hε
    rcases hε with ⟨μ, γ, hconj⟩
    apply Subgroup.subset_closure
    exact ⟨μ, ⟨⟨(γ : SL(2,𝓞 F)), γ.property.1⟩, hconj⟩⟩
  have hunitFin (σ : SL(2,F)) : (cuspUnits F Γ σ).FiniteIndex := by
    have h₀ : (cuspUnits F H σ).FiniteIndex := (R2_cusp_units H hHfree σ).1
    letI : (cuspUnits F H σ).FiniteIndex := h₀
    exact Subgroup.finiteIndex_of_le (hunitSub σ)
  obtain ⟨ι, hι, σ, hbij⟩ := (R3_cusps_finite Γ).1
  obtain ⟨C_M, hCM, hminkowski⟩ := R7_minkowski (F := F)
  let getP := fun i : ι => cuspTranslationDomain Γ (σ i)
    ((R1_cusp_lattice Γ (σ i)).2.2.2.1.1)
  let P : ι → Set (InfinitePlace F → ℂ) := fun i => Classical.choose (getP i)
  have hP (i : ι) : IsAddFundamentalDomain (cuspTranslations F Γ (σ i)) (P i) ∧
      Bornology.IsBounded (P i) ∧ MeasurableSet (P i) ∧
      ∀ x, ∃ μ ∈ cuspTranslations F Γ (σ i), μ + x ∈ P i :=
    Classical.choose_spec (getP i)
  let getB := fun i : ι => by
    letI : (cuspUnits F Γ (σ i)).FiniteIndex := hunitFin (σ i)
    exact R4_unit_balance (cuspUnits F Γ (σ i))
  let B : ι → ℝ := fun i => Classical.choose (getB i)
  have hB (i : ι) : 0 ≤ B i ∧ ∀ t : InfinitePlace F → ℝ, (∀ w, 0 < t w) →
      ∃ ε ∈ cuspUnits F Γ (σ i), ∀ w,
        |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
          (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')| ≤ B i := by
    letI : (cuspUnits F Γ (σ i)).FiniteIndex := hunitFin (σ i)
    exact Classical.choose_spec (getB i)
  refine ⟨{
    ι := ι
    fintype := hι
    σ := σ
    P := P
    B := B
    C_M := C_M
    C_M_pos := hCM
    minkowski := hminkowski
    P_fundamental := fun i => (hP i).1
    P_covers := fun i => (hP i).2.2.2
    P_bounded := fun i => (hP i).2.1
    P_measurable := fun i => (hP i).2.2.1
    balanced := by
      intro i t ht
      exact (hB i).2 t ht
    reps_bijective := hbij
  }⟩

end ArtinPrimitiveRoots.A1.Spec

end
