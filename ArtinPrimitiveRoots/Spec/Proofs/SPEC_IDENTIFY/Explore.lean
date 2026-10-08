import ArtinPrimitiveRoots.Spec.EisensteinExtra

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Pointwise
set_option maxHeartbeats 1000000

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem finiteVolume_probe (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F)) :
    volX F D < ⊤ := by
  classical
  obtain ⟨N, hN, hfreeN⟩ := R11_free_level (F := F)
  let Γf : Subgroup SL(2,𝓞 F) := Γ ⊓ congrSubgroup F N
  have hfiniteCong : (congrSubgroup F N).FiniteIndex := by
    letI : Finite (𝓞 F ⧸ N) := Ring.HasFiniteQuotients.finiteQuotient hN
    letI : Finite (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F ⧸ N)) := inferInstance
    unfold congrSubgroup
    exact Subgroup.finiteIndex_ker _
  have hfiniteΓf : Γf.FiniteIndex := by
    letI : Γ.FiniteIndex := inferInstance
    letI : (congrSubgroup F N).FiniteIndex := hfiniteCong
    infer_instance
  have hfreeΓf : FreeAction F Γf := by
    intro γ hγ z hfix
    exact hfreeN γ hγ.2 z hfix
  letI : Γf.FiniteIndex := hfiniteΓf
  let d0 : SiegelData F Γf := Classical.choice (spec_exists_siegelData Γf)
  let D0 := fundamentalDomainCandidate F Γf (SiegelData.unionSet F d0)
  have hR12 := R12_fund_domain (F := F) Γf hfreeΓf d0
  have hD0 : IsFundamentalDomain Γf D0 (volX F) := by
    simpa [D0] using hR12.2.1
  have hD0fin : volX F D0 < ⊤ := by
    simpa [D0] using hR12.2.2
  have hΓfΓ : Γf ≤ Γ := inf_le_left
  let H : Subgroup Γ := Γf.subgroupOf Γ
  letI : H.FiniteIndex := inferInstance
  let e : H ≃* Γf := Subgroup.subgroupOfEquivOfLe hΓfΓ
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
  letI : Countable (Fin 2 → 𝓞 F) := inferInstance
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
    change Countable (Fin 2 → Fin 2 → 𝓞 F)
    infer_instance
  letI : Countable (SL(2,𝓞 F)) :=
    (Subtype.val_injective : Function.Injective
      (fun g : SL(2,𝓞 F) => (g : Matrix (Fin 2) (Fin 2) (𝓞 F)))).countable
  letI : Countable Γ :=
    (Subtype.val_injective : Function.Injective (fun g : Γ => (g : SL(2,𝓞 F)))).countable
  letI : Countable H := inferInstance
  have hsmulMeas (γ : SL(2,𝓞 F)) : Measurable (fun z : X F => γ • z) := by
    let g := toInf F (toSLF F γ)
    change Measurable (actAtPlaces F g)
    apply measurable_pi_iff.2
    intro w
    exact (OAI.CubicEisenstein.continuous_hyperbolic_action (g w)).measurable.comp
      (measurable_pi_apply w)
  letI : MeasurableConstSMul Γ (X F) := ⟨fun γ => hsmulMeas (γ : SL(2,𝓞 F))⟩
  letI : MeasurableConstSMul H (X F) := inferInstance
  letI : SMulInvariantMeasure Γ (X F) (volX F) := ⟨fun γ s hs => by
    have hmap : Measure.map (fun z : X F => γ • z) (volX F) = volX F := by
      change Measure.map (actAtPlaces F (toInf F (toSLF F γ))) (volX F) = volX F
      exact (G3_volume (F := F)).1 (toInf F (toSLF F γ))
    exact Measure.measure_preimage_of_map_eq_self hmap (hsmulMeas (γ : SL(2,𝓞 F))).aemeasurable
      hs.nullMeasurableSet⟩
  let Q := Quotient (QuotientGroup.rightRel H)
  let q0 : Q := Quotient.mk _ (1 : Γ)
  let rep : Q → Γ := fun q => if q = q0 then 1 else Quotient.out q
  have hrep (q : Q) : Quotient.mk (QuotientGroup.rightRel H) (rep q) = q := by
    by_cases hq : q = q0
    · subst q
      simp [rep, q0]
    · simp [rep, hq, Quotient.out_eq']
  letI : Finite (Γ ⧸ H) := inferInstance
  letI : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  letI : Fintype Q := QuotientGroup.fintypeQuotientRightRel
  let U : Set (X F) := ⋃ q : Q, (rep q : Γ) • D
  have hUmeas : NullMeasurableSet U (volX F) := by
    change NullMeasurableSet (⋃ q : Q, (rep q : Γ) • D) (volX F)
    refine .iUnion fun q => ?_
    rw [← inv_inv (rep q : Γ), ← Set.preimage_smul]
    exact hD.nullMeasurableSet.preimage
      (measurePreserving_smul ((rep q : Γ)⁻¹) (volX F)).quasiMeasurePreserving
  have hcover : ∀ᵐ x ∂(volX F), ∃ a : H, a • x ∈ U := by
    filter_upwards [hD.ae_covers] with x hx
    rcases hx with ⟨g, hg⟩
    let δ : Γ := g⁻¹
    let q : Q := Quotient.mk _ δ
    have hrel : QuotientGroup.rightRel H (rep q) δ := by
      apply Quotient.exact'
      simpa [q] using hrep q
    have hmem : δ * (rep q)⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hrel
    let k : H := ⟨δ * (rep q)⁻¹, hmem⟩
    have hδ : δ = k * rep q := by
      dsimp [k, δ]
      group
    have hprod : (k : Γ) * rep q = g⁻¹ := by
      simpa [δ] using hδ.symm
    have hsolve : (rep q)⁻¹ * (k⁻¹ : Γ) = g := by
      calc
        (rep q)⁻¹ * (k⁻¹ : Γ) = ((k : Γ) * rep q)⁻¹ := by group
        _ = (g⁻¹)⁻¹ := congrArg Inv.inv hprod
        _ = g := by simp
    refine ⟨k⁻¹, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
    change (k⁻¹ : H) • x ∈ (rep q : Γ) • D
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change (rep q : Γ)⁻¹ • (((k⁻¹ : H) : Γ) • x) ∈ D
    have hval : (rep q : Γ)⁻¹ • (((k⁻¹ : H) : Γ) • x) = g • x := by
      calc
        (rep q : Γ)⁻¹ • (((k⁻¹ : H) : Γ) • x) =
            ((rep q : Γ)⁻¹ * ((k⁻¹ : H) : Γ)) • x := smul_smul _ _ _
        _ = g • x := by simpa using congrArg (fun z : Γ => z • x) hsolve
    rw [hval]
    exact hg
  have hUfd : IsFundamentalDomain H U (volX F) := by
    apply IsFundamentalDomain.mk'' hUmeas hcover
    · intro a ha
      simp only [U, Set.smul_set_iUnion]
      rw [AEDisjoint.iUnion_left_iff]
      intro q
      rw [AEDisjoint.iUnion_right_iff]
      intro q'
      have hset : a • (rep q : Γ) • D = ((a : Γ) * rep q) • D := by
        change (a : Γ) • ((rep q : Γ) • D) = _
        rw [smul_smul]
      have hneq : (a : Γ) * rep q ≠ rep q' := by
        intro heq
        have hmem' : rep q' * (rep q)⁻¹ ∈ H := by
          rw [← heq]
          have hmul : ((a : Γ) * rep q) * (rep q)⁻¹ = (a : Γ) := by group
          rw [hmul]
          exact a.property
        have hclass : q = q' := by
          calc
            q = Quotient.mk _ (rep q) := (hrep q).symm
            _ = Quotient.mk _ (rep q') := Quotient.sound
              (QuotientGroup.rightRel_apply.mpr hmem')
            _ = q' := hrep q'
        subst q'
        apply ha
        apply Subtype.ext
        have hmul := congrArg (fun z : Γ => z * (rep q)⁻¹) heq
        simpa using hmul
      have hpair := hD.aedisjoint (i := (a : Γ) * rep q) (j := rep q') hneq
      simpa only [hset] using hpair
    · intro a
      exact (measurePreserving_smul a (volX F)).quasiMeasurePreserving
  have hD0H : IsFundamentalDomain H D0 (volX F) := by
    refine ⟨hD0.nullMeasurableSet, ?_, ?_⟩
    · filter_upwards [hD0.ae_covers] with x hx
      rcases hx with ⟨g, hg⟩
      refine ⟨e.symm g, ?_⟩
      change e (e.symm g) • x ∈ D0
      rw [e.apply_symm_apply]
      exact hg
    · intro a b hab
      have hne : e a ≠ e b := by
        intro heq
        exact hab (e.injective heq)
      have hdis := hD0.aedisjoint (i := e a) (j := e b) hne
      have hsetA : (e a) • D0 = a • D0 := by
        ext x
        simp only [Set.mem_smul_set_iff_inv_smul_mem]
        rfl
      have hsetB : (e b) • D0 = b • D0 := by
        ext x
        simp only [Set.mem_smul_set_iff_inv_smul_mem]
        rfl
      change AEDisjoint (volX F) ((e a) • D0) ((e b) • D0) at hdis
      rw [hsetA, hsetB] at hdis
      exact hdis
  have hmeasure : volX F U = volX F D0 := hUfd.measure_eq hD0H
  have hDsub : D ⊆ U := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨q0, ?_⟩
    change x ∈ (rep q0 : Γ) • D
    simpa [rep, q0] using hx
  calc
    volX F D ≤ volX F U := measure_mono hDsub
    _ = volX F D0 := hmeasure
    _ < ⊤ := hD0fin

end ArtinPrimitiveRoots.A1.Spec
