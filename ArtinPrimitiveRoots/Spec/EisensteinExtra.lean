import ArtinPrimitiveRoots.Spec.Energy
import Mathlib.LinearAlgebra.Countable
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.triangular_transition_unique
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.triangular_transition_term
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.nontriangular_siegel_summable

/-! Remaining Eisenstein and resolvent nodes E3--E7. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- E3 `spec:eis-smooth` — P-SPEC.md:239, 385–388. In the convergence region, the series is
smooth with normally convergent coordinate derivatives and is an eigenfunction of every partial
Laplacian. -/
theorem E3_eis_smooth (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (hs : 1 / 2 < s.re) :
    IsSmoothX F (eisSeries F Γ σ s) ∧
    (∀ w z, partialLap F w (eisSeries F Γ σ s) z =
      (1 - 4 * s ^ 2) * eisSeries F Γ σ s z) ∧
    (∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
      ∀ n : ℕ, ∀ v : Fin n → Coord F,
        ∃ m : CuspCosets F Γ σ → ℝ, Summable m ∧
          ∀ q, ∀ p, p ∈ K →
            ‖iteratedFDeriv ℝ n
              (fun p => eisTerm F Γ σ s (ptX F p) q) p v‖ ≤ m q) := by
  sorry

/-- E4 `spec:eis-siegel` — P-SPEC.md:240, 390–395. On each Siegel set there is at most one
upper-triangular seed coset; the remaining terms and their gradients are uniformly summable on
compact parameter sets in `2 < Re s < 3`. Correction from review lane `rev-spec`: state pointwise
summability and use the corrected Siegel set. Correction from `sol-gate-spec`: use the field norm
of the triangular matrix's upper-left entry in the leading term. -/
theorem E4_eis_siegel (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (σ : SL(2,F))
    (Kₛ : Set ℂ) (hKₛ : IsCompact Kₛ)
    (hKₛstrip : Kₛ ⊆ {s : ℂ | 2 < s.re ∧ s.re < 3}) :
    ∀ i : d.ι,
      (∀ q q' : CuspCosets F Γ σ,
        σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∈ borelSL F →
        σ⁻¹ * toSLF F ((q'.out : Γ) : SL(2,𝓞 F)) * d.σ i ∈ borelSL F → q = q') ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Kₛ, ∀ z ∈ SiegelData.setAt F d i,
        Summable (fun q' : {q : CuspCosets F Γ σ //
          σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∉ borelSL F} =>
            (‖eisTerm F Γ σ s ((d.σ i) • z) q'.1‖ +
              ‖fullGradient F (fun x => eisTerm F Γ σ s ((d.σ i) • x) q'.1) z‖)) ∧
        (∑' q' : {q : CuspCosets F Γ σ //
          σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∉ borelSL F},
          (‖eisTerm F Γ σ s ((d.σ i) • z) q'.1‖ +
            ‖fullGradient F (fun x => eisTerm F Γ σ s ((d.σ i) • x) q'.1) z‖)) ≤ C) ∧
      (∀ q : CuspCosets F Γ σ,
        σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∈ borelSL F →
        ∀ s ∈ Kₛ, ∀ z ∈ SiegelData.setAt F d i,
          let b := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i
          eisTerm F Γ σ s ((d.σ i) • z) q =
            ((absFieldNorm F (b 0 0) : ℝ) : ℂ) ^ (1 + 2 * s) *
              ((normHeight F z : ℝ) : ℂ) ^ (1 + 2 * s)) := by
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro q q' hq hq'
    exact triangular_transition_unique Γ σ (d.σ i) q q' hq hq'
  · exact nontriangular_siegel_summable Γ d σ Kₛ hKₛ hKₛstrip i
  · intro q hq s hs z hz
    exact triangular_transition_term Γ σ (d.σ i) q hq s z

/-- E5 `spec:seed` — P-SPEC.md:241, 131–133. The truncated seed and its defect are locally finite,
smooth and invariant; the defect is compactly supported modulo `Γ`, entire as an `L²` family, and
has the explicit height-only formula in the active cusp. Correction from review lane `rev-spec`:
include the cusp-separation property at the cutoff threshold. -/
theorem E5_seed (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) :
    (∀ s z,
      {q : CuspCosets F Γ σ | seedTerm F Γ σ τ s z q ≠ 0}.Finite ∧
      (Nat.card {q : CuspCosets F Γ σ | seedTerm F Γ σ τ s z q ≠ 0} ≤ 1)) ∧
    (∀ s, IsSmoothX F (eisSeed F Γ σ τ s) ∧
      IsGammaInvariant F Γ (eisSeed F Γ σ τ s) ∧
      ∀ z, totalLap F (eisSeed F Γ σ τ s) z -
        spectralParameter F s * eisSeed F Γ σ τ s z = eisSeedDefect F Γ σ τ s z) ∧
    (∃ K : Set (X F), IsCompact K ∧ ∀ s,
      {z | eisSeedDefect F Γ σ τ s z ≠ 0} ⊆ orbitSaturation F Γ K) ∧
    (∃ G : ℂ → L2Space F D, AnalyticOnNhd ℂ G Set.univ ∧
      ∀ s, ∀ᵐ z ∂(volX F), z ∈ D → G s z = eisSeedDefect F Γ σ τ s z) ∧
    (∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
      ∀ n : ℕ, ∀ v : Fin n → Coord F,
        ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
          ∀ s p, Φ s p = iteratedFDeriv ℝ n
            (fun q => eisSeed F Γ σ τ s (ptX F q)) p v) ∧
    (∀ s z, z ∈ cuspTail F Γ σ A₀ →
      ∃ γ : Γ,
        eisSeedDefect F Γ σ τ s z =
          -(placeCount F : ℂ) *
            (((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ 2 *
                deriv (deriv (fun t : ℝ => (τ t : ℂ)))
                  (normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))) +
              (1 + 4 * s) *
                ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) *
                deriv (fun t : ℝ => (τ t : ℂ))
                  (normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))) ) *
            ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ (1 + 2 * s)) := by
  sorry

theorem spec_cuspUnits_finiteIndex (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) : (cuspUnits F Γ σ).FiniteIndex := by
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
  have hR2 := R2_cusp_units (F := F) Γf hfreeΓf σ
  have hle : cuspUnits F Γf σ ≤ cuspUnits F Γ σ := by
    apply Subgroup.closure_mono
    intro ε hε
    rcases hε with ⟨μ, γ, hEq⟩
    refine ⟨μ, ⟨γ.1, γ.2.1⟩, ?_⟩
    exact hEq
  letI : (cuspUnits F Γf σ).FiniteIndex := hR2.1
  exact Subgroup.finiteIndex_of_le hle

theorem spec_exists_siegelData (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    Nonempty (SiegelData F Γ) := by
  classical
  obtain ⟨ι, hι, σ, hbij⟩ := (R3_cusps_finite (F := F) Γ).1
  letI : Fintype ι := hι
  obtain ⟨C_M, hC_M, hmink⟩ := R7_minkowski (F := F)
  have hfull (i : ι) : IsFullZLattice (cuspTranslationsZ F Γ (σ i)) :=
    (R1_cusp_lattice (F := F) Γ (σ i)).2.2.2.1.1
  have hbalance (i : ι) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : InfinitePlace F → ℝ, (∀ w, 0 < t w) →
        ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ (σ i) ∧ ∀ w,
          |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
            (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')| ≤ B := by
    letI : (cuspUnits F Γ (σ i)).FiniteIndex := spec_cuspUnits_finiteIndex Γ (σ i)
    exact R4_unit_balance (cuspUnits F Γ (σ i))
  let P : ι → Set (InfinitePlace F → ℂ) := fun i => by
    let L := cuspTranslationsZ F Γ (σ i)
    let hLi := hfull i
    letI : DiscreteTopology L := Classical.choose hLi
    letI : IsZLattice ℝ L := Classical.choose_spec hLi
    letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
    letI : Module.Free ℤ L := ZLattice.module_free ℝ L
    let b₀ := Module.Free.chooseBasis ℤ L
    letI : Fintype (Module.Free.ChooseBasisIndex ℤ L) := Fintype.ofFinite _
    exact ZSpan.fundamentalDomain (b₀.ofZLatticeBasis ℝ)
  let B : ι → ℝ := fun i => Classical.choose (hbalance i)
  refine ⟨{ ι := ι
            fintype := hι
            σ := σ
            P := P
            B := B
            C_M := C_M
            C_M_pos := hC_M
            minkowski := hmink
            P_fundamental := ?_
            P_covers := ?_
            P_bounded := ?_
            P_measurable := ?_
            balanced := ?_
            reps_bijective := hbij }⟩
  · intro i
    let L := cuspTranslationsZ F Γ (σ i)
    let hLi := hfull i
    letI : DiscreteTopology L := Classical.choose hLi
    letI : IsZLattice ℝ L := Classical.choose_spec hLi
    letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
    letI : Module.Free ℤ L := ZLattice.module_free ℝ L
    let b₀ := Module.Free.chooseBasis ℤ L
    letI : Fintype (Module.Free.ChooseBasisIndex ℤ L) := Fintype.ofFinite _
    let b := b₀.ofZLatticeBasis ℝ
    have hspan : (Submodule.span ℤ (Set.range b)).toAddSubgroup =
        cuspTranslations F Γ (σ i) := by
      calc
        _ = L.toAddSubgroup := by rw [b₀.ofZLatticeBasis_span ℝ]
        _ = cuspTranslations F Γ (σ i) := by
          change (cuspTranslationsZ F Γ (σ i)).toAddSubgroup = _
          exact Submodule.span_int_eq (cuspTranslations F Γ (σ i))
    have hfd := ZSpan.isAddFundamentalDomain' b (volume : Measure (InfinitePlace F → ℂ))
    rw [hspan] at hfd
    simpa [P] using hfd
  · intro i x
    let L := cuspTranslationsZ F Γ (σ i)
    let hLi := hfull i
    letI : DiscreteTopology L := Classical.choose hLi
    letI : IsZLattice ℝ L := Classical.choose_spec hLi
    letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
    letI : Module.Free ℤ L := ZLattice.module_free ℝ L
    let b₀ := Module.Free.chooseBasis ℤ L
    letI : Fintype (Module.Free.ChooseBasisIndex ℤ L) := Fintype.ofFinite _
    let b := b₀.ofZLatticeBasis ℝ
    have hspan : (Submodule.span ℤ (Set.range b)).toAddSubgroup =
        cuspTranslations F Γ (σ i) := by
      calc
        _ = L.toAddSubgroup := by rw [b₀.ofZLatticeBasis_span ℝ]
        _ = cuspTranslations F Γ (σ i) := by
          change (cuspTranslationsZ F Γ (σ i)).toAddSubgroup = _
          exact Submodule.span_int_eq (cuspTranslations F Γ (σ i))
    obtain ⟨μ, hμ⟩ := (ZSpan.exist_unique_vadd_mem_fundamentalDomain b x).exists
    have hmem : (μ : InfinitePlace F → ℂ) ∈
        (Submodule.span ℤ (Set.range b)).toAddSubgroup := μ.property
    rw [hspan] at hmem
    refine ⟨(μ : InfinitePlace F → ℂ), hmem, ?_⟩
    change (μ +ᵥ x) ∈ ZSpan.fundamentalDomain b
    exact hμ
  · intro i
    let L := cuspTranslationsZ F Γ (σ i)
    let hLi := hfull i
    letI : DiscreteTopology L := Classical.choose hLi
    letI : IsZLattice ℝ L := Classical.choose_spec hLi
    letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
    letI : Module.Free ℤ L := ZLattice.module_free ℝ L
    let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ
    simpa [P] using ZSpan.fundamentalDomain_isBounded b
  · intro i
    let L := cuspTranslationsZ F Γ (σ i)
    let hLi := hfull i
    letI : DiscreteTopology L := Classical.choose hLi
    letI : IsZLattice ℝ L := Classical.choose_spec hLi
    letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
    letI : Module.Free ℤ L := ZLattice.module_free ℝ L
    let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ
    simpa [P] using ZSpan.fundamentalDomain_measurableSet b
  · intro i
    exact (Classical.choose_spec (hbalance i)).2

set_option maxHeartbeats 1000000 in
theorem spec_finiteVolume_any_fd (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
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
    exact Measure.measure_preimage_of_map_eq_self hmap
      (hsmulMeas (γ : SL(2,𝓞 F))).aemeasurable hs.nullMeasurableSet⟩
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

def specIdentifyRadialProfile (τ : ℝ → ℝ) (a : ℂ) (u : ℝ) : ℂ :=
  (τ (Real.exp u) : ℂ) * Complex.exp (a * (u : ℂ))

theorem specIdentifyRadialProfile_log (τ : ℝ → ℝ) (a : ℂ) {h : ℝ} (hh : 0 < h) :
    specIdentifyRadialProfile τ a (Real.log h) = (τ h : ℂ) * (h : ℂ) ^ a := by
  have hne : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [specIdentifyRadialProfile, Real.exp_log hh, Complex.cpow_def_of_ne_zero hne,
    Complex.ofReal_log hh.le]
  congr 1
  rw [mul_comm a (Complex.log (h : ℂ))]

private theorem specIdentifyRadialProfile_contDiff (τ : ℝ → ℝ) (a : ℂ)
    (hτ : ContDiff ℝ ∞ τ) :
    ContDiff ℝ ∞ (specIdentifyRadialProfile τ a) := by
  have hτ' : ContDiff ℝ ∞ (fun u : ℝ => τ (Real.exp u)) := hτ.comp Real.contDiff_exp
  have hreal : ContDiff ℝ ∞ (fun u : ℝ => (τ (Real.exp u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hτ'
  have harg : ContDiff ℝ ∞ (fun u : ℝ => a * (u : ℂ)) := by
    have h := (Complex.ofRealCLM.smulRight a).contDiff (n := ∞)
    convert h using 1 <;> ext u <;> simp [Complex.ofRealCLM_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_comm]
  have hexp : ContDiff ℝ ∞ (fun u : ℝ => Complex.exp (a * (u : ℂ))) :=
    Complex.contDiff_exp.comp harg
  change ContDiff ℝ ∞ (fun u : ℝ => (τ (Real.exp u) : ℂ) * Complex.exp (a * (u : ℂ)))
  exact hreal.mul hexp

theorem specIdentify_posSet_open : IsOpen (posSet F) := by
  rw [posSet, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun w => by
    have hcont : Continuous (fun p : Coord F => (p w).2) :=
      continuous_snd.comp (continuous_apply w)
    exact isOpen_lt continuous_const hcont

private theorem specIdentify_heightAction_smooth (b : SL(2,F)) :
    ContDiffOn ℝ ∞ (fun p : Coord F => normHeight F (b • ptX F p)) (posSet F) := by
  classical
  let denom (p : Coord F) (w : InfinitePlace F) : ℝ :=
    Complex.normSq (w.embedding (b 1 0) * (p w).1 + w.embedding (b 1 1)) +
      Complex.normSq (w.embedding (b 1 0)) * (p w).2 ^ 2
  let H (p : Coord F) : ℝ := ∏ w : InfinitePlace F, (p w).2 / denom p w
  have hbrow : b 1 0 ≠ 0 ∨ b 1 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have hdet := b.property
    rw [Matrix.det_fin_two] at hdet
    rw [h.1, h.2] at hdet
    norm_num at hdet
  have hden (p : Coord F) (hp : p ∈ posSet F) (w : InfinitePlace F) : 0 < denom p w := by
    by_cases hc : b 1 0 = 0
    · have hd : b 1 1 ≠ 0 := by
        intro hd0
        exact hbrow.elim (fun h => h hc) (fun h => h hd0)
      have hwd : w.embedding (b 1 1) ≠ 0 := (map_ne_zero (w.embedding)).2 hd
      have hnorm : 0 < Complex.normSq (w.embedding (b 1 1)) := by
        rw [Complex.normSq_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr hwd)
      simpa [denom, hc] using hnorm
    · have hwc : w.embedding (b 1 0) ≠ 0 := (map_ne_zero (w.embedding)).2 hc
      have hnorm : 0 < Complex.normSq (w.embedding (b 1 0)) := by
        rw [Complex.normSq_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr hwc)
      have hy : 0 < (p w).2 ^ 2 := pow_pos (hp w) 2
      unfold denom
      exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (mul_pos hnorm hy)
  have hHpos (p : Coord F) (hp : p ∈ posSet F) : 0 < H p := by
    apply Finset.prod_pos
    intro w hw
    exact div_pos (hp w) (hden p hp w)
  have hformula (p : Coord F) (hp : p ∈ posSet F) :
      normHeight F (b • ptX F p) = H p := by
    have hG := (G2_x_action (F := F)).1 b (fun w => (p w).1) (fun w => (p w).2) hp
    change normHeight F (b • ptX' F (fun w => (p w).1) (fun w => (p w).2)) = H p
    change normHeight F (b • ptX' F (fun w => (p w).1) (fun w => (p w).2)) = H p at hG
    exact hG
  have hdenomCont (w : InfinitePlace F) :
      ContDiff ℝ ∞ (fun p : Coord F => denom p w) := by
    let l : Coord F → ℂ := fun p =>
      w.embedding (b 1 0) * (p w).1 + w.embedding (b 1 1)
    have hleft : ContDiff ℝ ∞ l := by fun_prop
    have hleftRe : ContDiff ℝ ∞ (fun p => (l p).re) := Complex.reCLM.contDiff.comp hleft
    have hleftIm : ContDiff ℝ ∞ (fun p => (l p).im) := Complex.imCLM.contDiff.comp hleft
    have hleftSq : ContDiff ℝ ∞ (fun p : Coord F => Complex.normSq (l p)) := by
      have hsum : ContDiff ℝ ∞ (fun p : Coord F =>
          (l p).re * (l p).re + (l p).im * (l p).im) :=
        (hleftRe.mul hleftRe).add (hleftIm.mul hleftIm)
      simpa only [Complex.normSq_apply] using hsum
    have hrightSq : ContDiff ℝ ∞
        (fun p : Coord F => Complex.normSq (w.embedding (b 1 0)) * (p w).2 ^ 2) := by
      fun_prop
    change ContDiff ℝ ∞ (fun p => Complex.normSq (l p) +
      Complex.normSq (w.embedding (b 1 0)) * (p w).2 ^ 2)
    exact hleftSq.add hrightSq
  have hfracCont (w : InfinitePlace F) :
      ContDiffOn ℝ ∞ (fun p : Coord F => (p w).2 / denom p w) (posSet F) := by
    have hnum : ContDiff ℝ ∞ (fun p : Coord F => (p w).2) := by fun_prop
    exact hnum.contDiffOn.div (hdenomCont w).contDiffOn fun p hp => (hden p hp w).ne'
  have hHdiff : ContDiffOn ℝ ∞ H (posSet F) := by
    unfold H
    exact contDiffOn_prod (fun w _ => hfracCont w)
  unfold H at hHdiff
  exact hHdiff.congr fun p hp => hformula p hp

private theorem specIdentify_seedTerm_smooth_action
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ σ' : SL(2,F)) (τ : ℝ → ℝ) (hτ : ContDiff ℝ ∞ τ)
    (s : ℂ) (q : CuspCosets F Γ σ) :
    IsSmoothX F (fun x => seedTerm F Γ σ τ s (σ' • x) q) := by
  classical
  let a : ℂ := 1 + 2 * s
  let γ : SL(2,𝓞 F) := (q.out : Γ)
  let b : SL(2,F) := σ⁻¹ * toSLF F γ * σ'
  let H : Coord F → ℝ := fun p => normHeight F (b • ptX F p)
  have hHdiff : ContDiffOn ℝ ∞ H (posSet F) := by
    simpa [H] using specIdentify_heightAction_smooth b
  have hHpos (p : Coord F) (hp : p ∈ posSet F) : 0 < H p := by
    unfold H normHeight
    apply Finset.prod_pos
    intro w hw
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos ((b • ptX F p) w)
  have hlogH : ContDiffOn ℝ ∞ (fun p => Real.log (H p)) (posSet F) :=
    hHdiff.log fun p hp => (hHpos p hp).ne'
  have hprofile : ContDiffOn ℝ ∞
    (fun p => specIdentifyRadialProfile τ a (Real.log (H p))) (posSet F) :=
    (specIdentifyRadialProfile_contDiff τ a hτ).comp_contDiffOn hlogH
  have hEq (p : Coord F) (hp : p ∈ posSet F) :
      seedTerm F Γ σ τ s (σ' • ptX F p) q =
        specIdentifyRadialProfile τ a (Real.log (H p)) := by
    have hact : σ⁻¹ • ((γ : SL(2,𝓞 F)) • (σ' • ptX F p)) = b • ptX F p := by
      change σ⁻¹ • ((toSLF F γ) • (σ' • ptX F p)) = _
      rw [← mul_smul, ← mul_smul]
    unfold seedTerm
    change (τ (normHeight F (σ⁻¹ •
      ((γ : SL(2,𝓞 F)) • (σ' • ptX F p))) : ℝ) : ℂ) *
        ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • (σ' • ptX F p))) : ℝ) : ℂ) ^ a = _
    rw [hact]
    change (τ (H p) : ℂ) * (H p : ℂ) ^ a = _
    exact (specIdentifyRadialProfile_log τ a (hHpos p hp)).symm
  unfold IsSmoothX
  change ContDiffOn ℝ ∞
    (fun p => seedTerm F Γ σ τ s (σ' • ptX F p) q) (posSet F)
  exact hprofile.congr fun p hp => hEq p hp

private theorem specIdentify_seedHighCosets_finite
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ σ' : SL(2,F)) (τ : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hτ : IsCuspCutoff A τ) (s : ℂ) (y : X F) :
    ∃ Q : Set (CuspCosets F Γ σ), Q.Finite ∧
      ∃ U : Set (X F), IsOpen U ∧ y ∈ U ∧
        ∀ x ∈ U, ∀ q ∉ Q, seedTerm F Γ σ τ s (σ' • x) q = 0 := by
  classical
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, hptCoord, _, _, _, hex⟩
  obtain ⟨e, he, hesym⟩ := hex
  have hcoord : Continuous (coordsX F) := by
    have heq : coordsX F = fun z => (e.symm z).1 := by
      funext z
      exact (hesym z).symm
    rw [heq]
    exact continuous_subtype_val.comp e.symm.continuous
  let p : Coord F := coordsX F y
  have hp : p ∈ posSet F := by
    intro w
    change 0 < height (y w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (y w)
  obtain ⟨ε, hε, hεball⟩ := (Metric.isOpen_iff.mp
    (specIdentify_posSet_open (F := F)) p hp)
  let r : ℝ := ε / 2
  let Kcoord : Set (Coord F) := Metric.closedBall p r
  have hKcoord : IsCompact Kcoord := isCompact_closedBall p r
  have hKcoordPos : Kcoord ⊆ posSet F := by
    intro p' hp'
    apply hεball
    have hclosed : dist p' p ≤ r := by simpa [Kcoord] using hp'
    have hrε : r < ε := by dsimp [r]; linarith
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hclosed hrε)
  let fPos : Kcoord → {p : Coord F // p ∈ posSet F} := fun p' =>
    ⟨p'.1, hKcoordPos p'.2⟩
  have hfPos : Continuous fPos :=
    Continuous.subtype_mk continuous_subtype_val (fun p' => hKcoordPos p'.2)
  have hmap : Continuous (fun p' : Kcoord => σ' • ptX F p'.1) := by
    obtain ⟨eAct, hAct, _⟩ := (G2_x_action (F := F)).2.2.2.1 (toInf F σ')
    have hActCont : Continuous (fun z : X F => σ' • z) := by
      have heq : (fun z : X F => σ' • z) = eAct := by
        funext z
        calc
          σ' • z = actAtPlaces F (toInf F σ') z := by rfl
          _ = eAct z := (hAct z).symm
      rw [heq]
      exact eAct.continuous
    exact hActCont.comp ((e.continuous.comp hfPos).congr fun p' => by
      simpa [fPos] using he (fPos p'))
  let Kact : Set (X F) := Set.range (fun p' : Kcoord => σ' • ptX F p'.1)
  have hKact : IsCompact Kact := by
    change IsCompact (Set.range (fun p' : Kcoord => σ' • ptX F p'.1))
    exact isCompact_range hmap
  let Q : Set (CuspCosets F Γ σ) :=
    {q | ∃ z ∈ Kact, A ≤ normHeight F
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))}
  have hQ : Q.Finite :=
    (R10_cusp_separation (F := F) Γ).2.2 σ Kact hKact A hA
  let U : Set (X F) := coordsX F ⁻¹' Metric.ball p r
  have hUopen : IsOpen U := Metric.isOpen_ball.preimage hcoord
  have hyU : y ∈ U := by
    change coordsX F y ∈ Metric.ball p r
    dsimp [p, r]
    rw [Metric.mem_ball, dist_self]
    linarith [hε]
  refine ⟨Q, hQ, U, hUopen, hyU, ?_⟩
  intro x hx q hq
  have hp' : coordsX F x ∈ Kcoord := by
    change coordsX F x ∈ Metric.closedBall p r
    exact Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))
  have hz : σ' • x ∈ Kact := by
    refine ⟨⟨coordsX F x, hp'⟩, ?_⟩
    change σ' • ptX F (coordsX F x) = σ' • x
    rw [hptCoord x]
  have hnotHigh : ¬ A ≤ normHeight F
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • (σ' • x))) := by
    intro hhigh
    exact hq ⟨σ' • x, hz, hhigh⟩
  have hheight : normHeight F
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • (σ' • x))) ≤ A := le_of_not_ge hnotHigh
  unfold seedTerm
  simp [hτ.2.2.1 _ hheight]

private theorem specIdentify_normHeight_ptX (p : Coord F) (hp : p ∈ posSet F) :
    normHeight F (ptX F p) = ∏ w : InfinitePlace F, (p w).2 := by
  unfold normHeight
  apply Finset.prod_congr rfl
  intro w _
  change height (pt (p w).1 (p w).2) = _
  exact (G1_h3_basics (F := F)).1 (p w).1 (p w).2 (hp w)

private theorem specIdentify_radial_smooth (τ : ℝ → ℝ) (a : ℂ)
    (hτ : ContDiff ℝ ∞ τ) :
    IsSmoothX F (fun z => (τ (normHeight F z) : ℂ) * (normHeight F z : ℂ) ^ a) := by
  unfold IsSmoothX
  let Ncoord : Coord F → ℝ := fun p => ∏ w : InfinitePlace F, (p w).2
  have hN : ContDiff ℝ ∞ Ncoord := by
    dsimp [Ncoord]
    fun_prop
  have hNOn : ContDiffOn ℝ ∞ Ncoord (posSet F) := hN.contDiffOn
  have hNpos (p : Coord F) (hp : p ∈ posSet F) : 0 < Ncoord p := by
    apply Finset.prod_pos
    intro w hw
    exact hp w
  have hlogN : ContDiffOn ℝ ∞ (fun p => Real.log (Ncoord p)) (posSet F) :=
    hNOn.log fun p hp => (hNpos p hp).ne'
  have hprofile : ContDiffOn ℝ ∞
      (fun p => specIdentifyRadialProfile τ a (Real.log (Ncoord p))) (posSet F) :=
    (specIdentifyRadialProfile_contDiff τ a hτ).comp_contDiffOn hlogN
  apply hprofile.congr
  intro p hp
  change (τ (normHeight F (ptX F p)) : ℂ) *
    (normHeight F (ptX F p) : ℂ) ^ a = _
  rw [specIdentify_normHeight_ptX p hp]
  exact (specIdentifyRadialProfile_log τ a (hNpos p hp)).symm

private theorem specIdentify_fullGradient_radial (τ : ℝ → ℝ) (a : ℂ)
    (hτ : ContDiff ℝ ∞ τ) (z : X F) :
    fullGradient F
        (fun z => (τ (normHeight F z) : ℂ) * (normHeight F z : ℂ) ^ a) z =
      (deriv (specIdentifyRadialProfile τ a) (Real.log (normHeight F z))) •
        fullGradient F (logNormHeight F) z := by
  classical
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := by
    intro w
    change 0 < height (z w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  let Ncoord : Coord F → ℝ := fun p => normHeight F (ptX F p)
  let Lcoord : Coord F → ℝ := fun p => Real.log (Ncoord p)
  let ψ : ℝ → ℂ := specIdentifyRadialProfile τ a
  let radial : X F → ℂ := fun z => (τ (normHeight F z) : ℂ) * (normHeight F z : ℂ) ^ a
  have hN_eq (p' : Coord F) (hp' : p' ∈ posSet F) :
      Ncoord p' = ∏ w : InfinitePlace F, (p' w).2 := by
    exact specIdentify_normHeight_ptX p' hp'
  have hNpos (p' : Coord F) (hp' : p' ∈ posSet F) : 0 < Ncoord p' := by
    rw [hN_eq p' hp']
    exact Finset.prod_pos fun w _ => hp' w
  have hNprod : DifferentiableAt ℝ (fun p' : Coord F => ∏ w : InfinitePlace F, (p' w).2) p := by
    fun_prop
  have hNevent : Ncoord =ᶠ[𝓝 p] fun p' : Coord F => ∏ w : InfinitePlace F, (p' w).2 := by
    filter_upwards [(specIdentify_posSet_open (F := F)).mem_nhds hp] with p' hp'
    exact hN_eq p' hp'
  have hNhas : HasFDerivAt Ncoord (fderiv ℝ (fun p' : Coord F => ∏ w, (p' w).2) p) p :=
    hNprod.hasFDerivAt.congr_of_eventuallyEq hNevent
  have hLhas : HasFDerivAt Lcoord (fderiv ℝ Lcoord p) p := by
    change HasFDerivAt (fun p' : Coord F => Real.log (Ncoord p')) _ p
    have hLcomp := (Real.hasDerivAt_log (ne_of_gt (hNpos p hp))).hasFDerivAt.comp p hNhas
    change HasFDerivAt (Real.log ∘ Ncoord) (fderiv ℝ (Real.log ∘ Ncoord) p) p
    rw [hLcomp.fderiv]
    exact hLcomp
  have hψsmooth : ContDiff ℝ ∞ ψ := specIdentifyRadialProfile_contDiff τ a hτ
  have hψhas : HasDerivAt ψ (deriv ψ (Lcoord p)) (Lcoord p) :=
    (hψsmooth.contDiffAt (x := Lcoord p)).differentiableAt (by simp) |>.hasDerivAt
  have hcomp := hψhas.hasFDerivAt.comp p hLhas
  have hprofEq (p' : Coord F) (hp' : p' ∈ posSet F) : radial (ptX F p') = ψ (Lcoord p') := by
    change (τ (normHeight F (ptX F p')) : ℂ) *
        (normHeight F (ptX F p') : ℂ) ^ a = specIdentifyRadialProfile τ a
          (Real.log (normHeight F (ptX F p')))
    exact (specIdentifyRadialProfile_log τ a (hNpos p' hp')).symm
  have hprofEvent : (fun p' : Coord F => radial (ptX F p')) =ᶠ[𝓝 p]
      fun p' => ψ (Lcoord p') := by
    filter_upwards [specIdentify_posSet_open (F := F).mem_nhds hp] with p' hp'
    exact hprofEq p' hp'
  have hradHas := hcomp.congr_of_eventuallyEq hprofEvent
  have hradDeriv : fderiv ℝ (fun p' : Coord F => radial (ptX F p')) p =
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv ψ (Lcoord p))).comp
        (fderiv ℝ Lcoord p) := hradHas.fderiv
  have hlogHas : HasFDerivAt (fun p' : Coord F => logNormHeight F (ptX F p'))
      (Complex.ofRealCLM.comp (fderiv ℝ Lcoord p)) p := by
    change HasFDerivAt (fun p' : Coord F => (Lcoord p' : ℂ)) _ p
    exact Complex.ofRealCLM.hasFDerivAt.comp p hLhas
  have hlogDeriv : fderiv ℝ (fun p' : Coord F => logNormHeight F (ptX F p')) p =
      Complex.ofRealCLM.comp (fderiv ℝ Lcoord p) := hlogHas.fderiv
  have hdir (v : Coord F) :
      fderiv ℝ (fun p' : Coord F => radial (ptX F p')) p v =
        deriv ψ (Lcoord p) * fderiv ℝ (fun p' : Coord F => logNormHeight F (ptX F p')) p v := by
    rw [hradDeriv, hlogDeriv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      Complex.ofRealCLM_apply]
    <;> ring
  have hplace (w : InfinitePlace F) (j : Fin 3) :
      placeGradient F w radial z j =
        deriv ψ (Lcoord p) * placeGradient F w (logNormHeight F) z j := by
    unfold placeGradient
    rw [show coordsX F z = p by rfl]
    have h := hdir (placeDirection F w j)
    have h' :
        fderiv ℝ (radial ∘ ptX F) p (placeDirection F w j) =
          deriv ψ (Lcoord p) *
            fderiv ℝ (logNormHeight F ∘ ptX F) p (placeDirection F w j) := by
      change fderiv ℝ (fun p' => radial (ptX F p')) p (placeDirection F w j) =
        deriv ψ (Lcoord p) *
          fderiv ℝ (fun p' => logNormHeight F (ptX F p')) p (placeDirection F w j)
      exact h
    rw [h']
    ring
  have hvec : fullGradient F radial z =
      (deriv ψ (Lcoord p)) • fullGradient F (logNormHeight F) z := by
    apply PiLp.ext
    intro ij
    rcases ij with ⟨w, j⟩
    simp [fullGradient, hplace]
  have hpoint : ptX F p = z := (G1_h3_basics (F := F)).2.2.2.2.2.2.2.1 z
  have hNpoint : Ncoord p = normHeight F z := by
    dsimp [Ncoord, p]
    rw [hpoint]
  simpa [ψ, Lcoord, hNpoint] using hvec

private theorem specIdentify_fullGradient_norm_sq (f : X F → ℂ) (z : X F) :
    ‖fullGradient F f z‖ ^ 2 = totalGradNormSq F f z := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [fullGradient, PiLp.toLp_apply]
  change (∑ ij : InfinitePlace F × Fin 3, ‖placeGradient F ij.1 f z ij.2‖ ^ 2) = _
  rw [Fintype.sum_prod_type]
  simp [totalGradNormSq, placeGradNormSq, Complex.normSq_eq_norm_sq]

private theorem specIdentify_radial_gradient_norm (τ : ℝ → ℝ) (a : ℂ)
    (hτ : ContDiff ℝ ∞ τ) (z : X F) :
    ‖fullGradient F
        (fun z => (τ (normHeight F z) : ℂ) * (normHeight F z : ℂ) ^ a) z‖ =
      ‖deriv (specIdentifyRadialProfile τ a) (Real.log (normHeight F z))‖ *
        Real.sqrt (placeCount F) := by
  have hlogSmooth : IsSmoothX F (logNormHeight F) := by
    unfold IsSmoothX
    have hprod : ContDiff ℝ ∞ (fun p : Coord F => ∏ w : InfinitePlace F, (p w).2) := by
      fun_prop
    have hprodOn : ContDiffOn ℝ ∞
        (fun p : Coord F => ∏ w : InfinitePlace F, (p w).2) (posSet F) := hprod.contDiffOn
    have hlog : ContDiffOn ℝ ∞
        (fun p : Coord F => Real.log (∏ w : InfinitePlace F, (p w).2)) (posSet F) := by
      apply hprodOn.log
      intro p hp
      exact (Finset.prod_pos fun w _ => hp w).ne'
    have hcast := Complex.ofRealCLM.contDiff.comp_contDiffOn hlog
    apply hcast.congr
    intro p hp
    simp [logNormHeight, specIdentify_normHeight_ptX p hp]
  have hG4 := G4_energy (F := F) (fun _ => (1 : SL(2,ℂ)))
    (logNormHeight F) (logNormHeight F) hlogSmooth hlogSmooth
  have hr : 0 < placeCount F := by
    unfold placeCount
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (InfinitePlace F)))
  have hnormsq : ‖fullGradient F (logNormHeight F) z‖ ^ 2 = placeCount F := by
    rw [specIdentify_fullGradient_norm_sq]
    exact hG4.2.2 z
  have hnorm : ‖fullGradient F (logNormHeight F) z‖ = Real.sqrt (placeCount F) := by
    rw [← hnormsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [specIdentify_fullGradient_radial τ a hτ z, norm_smul, hnorm]

private theorem specIdentify_gradient_norm_isometry
    (g : InfinitePlace F → SL(2,ℂ)) (f : X F → ℂ)
    (hf : IsSmoothX F f) (z : X F) :
    ‖fullGradient F (fun x => f (actAtPlaces F g x)) z‖ =
      ‖fullGradient F f (actAtPlaces F g z)‖ := by
  have hG4 := G4_energy (F := F) g f f hf hf
  have hsq :
      ‖fullGradient F (fun x => f (actAtPlaces F g x)) z‖ ^ 2 =
        ‖fullGradient F f (actAtPlaces F g z)‖ ^ 2 := by
    rw [specIdentify_fullGradient_norm_sq, specIdentify_fullGradient_norm_sq]
    exact hG4.2.1 z
  have h₀ : 0 ≤ ‖fullGradient F (fun x => f (actAtPlaces F g x)) z‖ := norm_nonneg _
  have h₁ : 0 ≤ ‖fullGradient F f (actAtPlaces F g z)‖ := norm_nonneg _
  nlinarith [hsq]

private theorem specIdentify_radial_action_gradient_norm
    (g : InfinitePlace F → SL(2,ℂ)) (τ : ℝ → ℝ) (a : ℂ)
    (hτ : ContDiff ℝ ∞ τ) (z : X F) :
    ‖fullGradient F
        (fun x => (τ (normHeight F (actAtPlaces F g x)) : ℂ) *
          (normHeight F (actAtPlaces F g x) : ℂ) ^ a) z‖ =
      ‖deriv (specIdentifyRadialProfile τ a)
          (Real.log (normHeight F (actAtPlaces F g z)))‖ *
        Real.sqrt (placeCount F) := by
  let radial : X F → ℂ := fun x =>
    (τ (normHeight F x) : ℂ) * (normHeight F x : ℂ) ^ a
  have hradial : IsSmoothX F radial := by
    simpa [radial] using specIdentify_radial_smooth τ a hτ
  have h := specIdentify_gradient_norm_isometry g radial hradial z
  rw [specIdentify_radial_gradient_norm τ a hτ (actAtPlaces F g z)] at h
  simpa [radial] using h


theorem specIdentify_profile_interval_bound (τ : ℝ → ℝ) (a : ℂ)
    (hτ : ContDiff ℝ ∞ τ) (lo hi : ℝ) (hlohi : lo ≤ hi) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Set.Icc lo hi,
      ‖specIdentifyRadialProfile τ a u‖ ≤ B ∧
      ‖deriv (specIdentifyRadialProfile τ a) u‖ ≤ B := by
  let ψ := specIdentifyRadialProfile τ a
  have hψ : ContDiff ℝ ∞ ψ := specIdentifyRadialProfile_contDiff τ a hτ
  have hvalCont : Continuous (fun u : ℝ => ‖ψ u‖) := hψ.continuous.norm
  have hderivCont : Continuous (fun u : ℝ => ‖deriv ψ u‖) :=
    (hψ.continuous_deriv (by norm_num : (1 : ℕ∞) ≤ ∞)).norm
  have hvalBdd : BddAbove ((fun u : ℝ => ‖ψ u‖) '' Set.Icc lo hi) :=
    isCompact_Icc.bddAbove_image hvalCont.continuousOn
  have hderivBdd : BddAbove ((fun u : ℝ => ‖deriv ψ u‖) '' Set.Icc lo hi) :=
    isCompact_Icc.bddAbove_image hderivCont.continuousOn
  obtain ⟨B₀, hB₀⟩ := hvalBdd
  obtain ⟨B₁, hB₁⟩ := hderivBdd
  refine ⟨max B₀ (max B₁ 0),
    le_trans (le_max_right B₁ 0) (le_max_right B₀ (max B₁ 0)), ?_⟩
  intro u hu
  have h₀ : ‖ψ u‖ ≤ B₀ := hB₀ ⟨u, hu, rfl⟩
  have h₁ : ‖deriv ψ u‖ ≤ B₁ := hB₁ ⟨u, hu, rfl⟩
  exact ⟨h₀.trans (le_max_left _ _), h₁.trans (le_trans (le_max_left _ _) (le_max_right _ _))⟩

private theorem specIdentify_radialProfile_one_deriv (a : ℂ) (u : ℝ) :
    deriv (specIdentifyRadialProfile (fun _ : ℝ => 1) a) u =
      a * Complex.exp (a * (u : ℂ)) := by
  have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
  have hmul' := hcast.const_mul a
  have hmul : HasDerivAt (fun x : ℝ => a * (x : ℂ)) a u := by
    simpa using hmul'
  have hexp := (Complex.hasDerivAt_exp (a * (u : ℂ))).comp u hmul
  have hprofile : specIdentifyRadialProfile (fun _ : ℝ => 1) a =
      fun x : ℝ => Complex.exp (a * (x : ℂ)) := by
    funext x
    simp [specIdentifyRadialProfile]
  have hderiv : deriv (fun x : ℝ => Complex.exp (a * (x : ℂ))) u =
      Complex.exp (a * (u : ℂ)) * a := by
    simpa only [Function.comp_def] using hexp.deriv
  rw [hprofile, hderiv]
  ring

theorem specIdentify_cpow_norm (t : ℝ) (a : ℂ) (ht : 0 < t) :
    ‖(t : ℂ) ^ a‖ = t ^ a.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos ht a

private theorem specIdentify_cutoffResidual_deriv_bound
    (τ : ℝ → ℝ) (A : ℝ) (hA : 1 ≤ A) (a : ℂ)
    (haRe : 0 ≤ a.re) (ha : ‖a‖ ≤ 7)
    (hτ : IsCuspCutoff A τ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t →
      ‖deriv (specIdentifyRadialProfile (fun x => 1 - τ x) a) (Real.log t)‖ ≤ B := by
  classical
  let χ : ℝ → ℝ := fun x => 1 - τ x
  have hχ : ContDiff ℝ ∞ χ := by
    dsimp [χ]
    exact contDiff_const.sub hτ.1
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hA2pos : 0 < A / 2 := by positivity
  have h2Aone : 1 ≤ 2 * A := by nlinarith
  let M₀ : ℝ := max 1 ((2 * A) ^ 7)
  have hM₀ : 0 ≤ M₀ := by dsimp [M₀]; positivity
  have hpow (t : ℝ) (ht : 0 < t) (ht₂ : t ≤ 2 * A) : t ^ a.re ≤ M₀ := by
    by_cases ht₁ : t ≤ 1
    · exact (Real.rpow_le_one ht.le ht₁ haRe).trans (le_max_left _ _)
    · have ht₁' : 1 ≤ t := le_of_not_ge ht₁
      have hre7 : a.re ≤ 7 := by
        calc
          a.re ≤ |a.re| := le_abs_self _
          _ ≤ ‖a‖ := Complex.abs_re_le_norm a
          _ ≤ 7 := ha
      calc
        t ^ a.re ≤ (2 * A) ^ a.re := Real.rpow_le_rpow ht.le ht₂ haRe
        _ ≤ (2 * A) ^ 7 := Real.rpow_le_rpow_of_exponent_le h2Aone hre7
        _ ≤ M₀ := by simpa [M₀] using (le_max_right 1 ((2 * A) ^ 7))
  let lo : ℝ := Real.log (A / 2)
  let hi : ℝ := Real.log (2 * A)
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    apply Real.log_le_log hA2pos
    nlinarith [hA]
  obtain ⟨M₁, hM₁, hprof⟩ :=
    specIdentify_profile_interval_bound χ a hχ lo hi hlohi
  let B : ℝ := max (7 * M₀) M₁
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro t ht
  by_cases hlow : t ≤ A / 2
  · let u : ℝ := Real.log t
    have hu : u < Real.log A := by
      dsimp [u]
      apply Real.log_lt_log ht
      have hstrict : A / 2 < A := by nlinarith [hA]
      exact lt_of_le_of_lt hlow hstrict
    have heq : specIdentifyRadialProfile χ a =ᶠ[𝓝 u]
        specIdentifyRadialProfile (fun _ : ℝ => 1) a := by
      filter_upwards [isOpen_Iio.mem_nhds hu] with v hv
      have hexp : Real.exp v ≤ A := by
        rw [← Real.exp_log hApos]
        exact Real.exp_le_exp.mpr hv.le
      have hτ0 := hτ.2.2.1 (Real.exp v) hexp
      simp [specIdentifyRadialProfile, χ, hτ0]
    have hExp : Complex.exp (a * (Real.log t : ℂ)) = (t : ℂ) ^ a := by
      have h := specIdentifyRadialProfile_log (fun _ : ℝ => 1) a ht
      simpa [specIdentifyRadialProfile] using h
    have hpow' : t ^ a.re ≤ M₀ := hpow t ht (by nlinarith [hlow, hA])
    rw [heq.deriv_eq, specIdentify_radialProfile_one_deriv, norm_mul, hExp,
      specIdentify_cpow_norm t a ht]
    have hpowNonneg : 0 ≤ t ^ a.re := (Real.rpow_pos_of_pos ht _).le
    calc
      ‖a‖ * t ^ a.re ≤ 7 * t ^ a.re := mul_le_mul_of_nonneg_right ha hpowNonneg
      _ ≤ 7 * M₀ := by nlinarith [hpow']
      _ ≤ B := le_max_left _ _
  · by_cases hhigh : 2 * A < t
    · let u : ℝ := Real.log t
      have hu : Real.log (2 * A) < u := Real.log_lt_log (by positivity) hhigh
      have heq : specIdentifyRadialProfile χ a =ᶠ[𝓝 u] (fun _ : ℝ => 0) := by
        filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
        have hexp : 2 * A ≤ Real.exp v := by
          rw [← Real.exp_log (by positivity : 0 < 2 * A)]
          exact Real.exp_le_exp.mpr hv.le
        have hτ1 := hτ.2.2.2 (Real.exp v) hexp
        simp [specIdentifyRadialProfile, χ, hτ1]
      rw [heq.deriv_eq]
      simpa [B] using hB
    · have hlow' : A / 2 ≤ t := le_of_not_ge hlow
      have hhigh' : t ≤ 2 * A := le_of_not_gt hhigh
      have hlog : Real.log t ∈ Set.Icc lo hi := by
        rw [Set.mem_Icc]
        exact ⟨Real.log_le_log hA2pos hlow', Real.log_le_log (by positivity) hhigh'⟩
      have h := (hprof (Real.log t) hlog).2
      exact h.trans (le_max_right _ _)

private theorem specIdentify_seedProfile_deriv_bound
    (τ : ℝ → ℝ) (A : ℝ) (hA : 1 ≤ A) (hτ : IsCuspCutoff A τ)
    (a : ℂ) (H : ℝ) (hH : 2 * A ≤ H) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t → t ≤ H →
      ‖deriv (specIdentifyRadialProfile τ a) (Real.log t)‖ ≤ B := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hlo : 0 < A / 2 := by positivity
  have hlohi : Real.log (A / 2) ≤ Real.log H := by
    apply Real.log_le_log hlo
    nlinarith [hA, hH]
  obtain ⟨B, hB, hprofile⟩ :=
    specIdentify_profile_interval_bound τ a hτ.1 (Real.log (A / 2)) (Real.log H) hlohi
  refine ⟨B, hB, ?_⟩
  intro t ht htH
  by_cases hlow : t ≤ A / 2
  · let u : ℝ := Real.log t
    have hu : u < Real.log A := by
      dsimp [u]
      apply Real.log_lt_log ht
      have hstrict : A / 2 < A := by nlinarith [hA]
      exact lt_of_le_of_lt hlow hstrict
    have heq : specIdentifyRadialProfile τ a =ᶠ[𝓝 u] (fun _ : ℝ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hu] with v hv
      have hexp : Real.exp v ≤ A := by
        rw [← Real.exp_log hApos]
        exact Real.exp_le_exp.mpr hv.le
      have hτ0 := hτ.2.2.1 (Real.exp v) hexp
      simp [specIdentifyRadialProfile, hτ0]
    rw [heq.deriv_eq]
    simpa using hB
  · have hlow' : A / 2 ≤ t := le_of_not_ge hlow
    have hlog : Real.log t ∈ Set.Icc (Real.log (A / 2)) (Real.log H) := by
      rw [Set.mem_Icc]
      exact ⟨Real.log_le_log hlo hlow', Real.log_le_log ht htH⟩
    exact (hprofile (Real.log t) hlog).2

theorem specIdentify_normHeight_pos (z : X F) : 0 < normHeight F z := by
  unfold normHeight
  apply Finset.prod_pos
  intro w hw
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)


theorem specIdentify_radialProfile_norm (τ : ℝ → ℝ) (a : ℂ) (t : ℝ)
    (ht : 0 < t) :
    ‖specIdentifyRadialProfile τ a (Real.log t)‖ = |τ t| * t ^ a.re := by
  rw [specIdentifyRadialProfile_log τ a ht, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, specIdentify_cpow_norm t a ht]


set_option maxHeartbeats 1000000 in
theorem specIdentify_eisTerm_smooth (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (q : CuspCosets F Γ σ) :
    IsSmoothX F (fun z => eisTerm F Γ σ s z q) := by
  classical
  let a : ℂ := 1 + 2 * s
  let γ : SL(2,𝓞 F) := (q.out : Γ)
  let b : SL(2,F) := σ⁻¹ * toSLF F γ
  let denom (p : Coord F) (w : InfinitePlace F) : ℝ :=
    Complex.normSq (w.embedding (b 1 0) * (p w).1 + w.embedding (b 1 1)) +
      Complex.normSq (w.embedding (b 1 0)) * (p w).2 ^ 2
  let H (p : Coord F) : ℝ := ∏ w : InfinitePlace F, (p w).2 / denom p w
  have hbrow : b 1 0 ≠ 0 ∨ b 1 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have hdet := b.property
    rw [Matrix.det_fin_two] at hdet
    rw [h.1, h.2] at hdet
    norm_num at hdet
  have hden (p : Coord F) (hp : p ∈ posSet F) (w : InfinitePlace F) : 0 < denom p w := by
    by_cases hc : b 1 0 = 0
    · have hd : b 1 1 ≠ 0 := by
        intro hd0
        exact hbrow.elim (fun h => h hc) (fun h => h hd0)
      have hwd : w.embedding (b 1 1) ≠ 0 := (map_ne_zero (w.embedding)).2 hd
      have hnorm : 0 < Complex.normSq (w.embedding (b 1 1)) := by
        rw [Complex.normSq_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr hwd)
      simpa [denom, hc] using hnorm
    · have hwc : w.embedding (b 1 0) ≠ 0 := (map_ne_zero (w.embedding)).2 hc
      have hnorm : 0 < Complex.normSq (w.embedding (b 1 0)) := by
        rw [Complex.normSq_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr hwc)
      have hy : 0 < (p w).2 ^ 2 := pow_pos (hp w) 2
      unfold denom
      exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (mul_pos hnorm hy)
  have hHpos (p : Coord F) (hp : p ∈ posSet F) : 0 < H p := by
    apply Finset.prod_pos
    intro w hw
    exact div_pos (hp w) (hden p hp w)
  have hformula (p : Coord F) (hp : p ∈ posSet F) :
      normHeight F (σ⁻¹ • (γ • ptX F p)) = H p := by
    have hG := (G2_x_action (F := F)).1 b (fun w => (p w).1) (fun w => (p w).2) hp
    have hact : σ⁻¹ • (γ • ptX F p) = b • ptX F p := by
      change σ⁻¹ • ((toSLF F γ) • ptX F p) = _
      rw [← mul_smul]
    rw [hact]
    change normHeight F (b • ptX' F (fun w => (p w).1) (fun w => (p w).2)) = H p
    change normHeight F (b • ptX' F (fun w => (p w).1) (fun w => (p w).2)) = H p at hG
    exact hG
  have hdenomCont (w : InfinitePlace F) :
      ContDiff ℝ ∞ (fun p : Coord F => denom p w) := by
    let l : Coord F → ℂ := fun p =>
      w.embedding (b 1 0) * (p w).1 + w.embedding (b 1 1)
    have hleft : ContDiff ℝ ∞ l := by fun_prop
    have hleftRe : ContDiff ℝ ∞ (fun p => (l p).re) := Complex.reCLM.contDiff.comp hleft
    have hleftIm : ContDiff ℝ ∞ (fun p => (l p).im) := Complex.imCLM.contDiff.comp hleft
    have hleftSq : ContDiff ℝ ∞ (fun p : Coord F => Complex.normSq (l p)) := by
      have hsum : ContDiff ℝ ∞ (fun p : Coord F =>
          (l p).re * (l p).re + (l p).im * (l p).im) :=
        (hleftRe.mul hleftRe).add (hleftIm.mul hleftIm)
      simpa only [Complex.normSq_apply] using hsum
    have hrightSq : ContDiff ℝ ∞
        (fun p : Coord F => Complex.normSq (w.embedding (b 1 0)) * (p w).2 ^ 2) := by
      fun_prop
    change ContDiff ℝ ∞ (fun p => Complex.normSq (l p) +
      Complex.normSq (w.embedding (b 1 0)) * (p w).2 ^ 2)
    exact hleftSq.add hrightSq
  have hfracCont (w : InfinitePlace F) :
      ContDiffOn ℝ ∞ (fun p : Coord F => (p w).2 / denom p w) (posSet F) := by
    have hnum : ContDiff ℝ ∞ (fun p : Coord F => (p w).2) := by fun_prop
    exact hnum.contDiffOn.div (hdenomCont w).contDiffOn fun p hp => (hden p hp w).ne'
  have hHdiff : ContDiffOn ℝ ∞ H (posSet F) := by
    unfold H
    exact contDiffOn_prod (fun w _ => hfracCont w)
  have hlogH : ContDiffOn ℝ ∞ (fun p => Real.log (H p)) (posSet F) :=
    hHdiff.log fun p hp => (hHpos p hp).ne'
  let one : ℝ → ℝ := fun _ => 1
  have hone : ContDiff ℝ ∞ one := by fun_prop [one]
  have hprofile : ContDiffOn ℝ ∞
      (fun p => specIdentifyRadialProfile one a (Real.log (H p))) (posSet F) :=
    (specIdentifyRadialProfile_contDiff one a hone).comp_contDiffOn hlogH
  have hEq (p : Coord F) (hp : p ∈ posSet F) :
      eisTerm F Γ σ s (ptX F p) q = specIdentifyRadialProfile one a (Real.log (H p)) := by
    change ((normHeight F (σ⁻¹ • (γ • ptX F p)) : ℝ) : ℂ) ^ (1 + 2 * s) = _
    rw [hformula p hp]
    simpa [one, a] using (specIdentifyRadialProfile_log one a (hHpos p hp)).symm
  unfold IsSmoothX
  change ContDiffOn ℝ ∞ (fun p => eisTerm F Γ σ s (ptX F p) q) (posSet F)
  exact hprofile.congr fun p hp => hEq p hp

set_option maxHeartbeats 1000000 in
theorem specIdentify_eisSeries_fderiv_tsum (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (hs : 1 / 2 < s.re)
    (p : Coord F) (hp : p ∈ posSet F) (v : Coord F) :
    Summable (fun q : CuspCosets F Γ σ =>
      fderiv ℝ (fun p' => eisTerm F Γ σ s (ptX F p') q) p v) ∧
    fderiv ℝ (fun p' => eisSeries F Γ σ s (ptX F p')) p v =
      ∑' q : CuspCosets F Γ σ,
        fderiv ℝ (fun p' => eisTerm F Γ σ s (ptX F p') q) p v := by
  classical
  let line : ℝ → Coord F := fun t => p + t • v
  let g : CuspCosets F Γ σ → ℝ → ℂ := fun q t =>
    eisTerm F Γ σ s (ptX F (line t)) q
  let g' : CuspCosets F Γ σ → ℝ → ℂ := fun q t =>
    fderiv ℝ (fun p' => eisTerm F Γ σ s (ptX F p') q) (line t) v
  obtain ⟨ε, hε, hεball⟩ := (Metric.isOpen_iff.mp (specIdentify_posSet_open (F := F)) p hp)
  let δ : ℝ := ε / (4 * (‖v‖ + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let K : Set (Coord F) := Metric.closedBall p (ε / 2)
  have hK : IsCompact K := isCompact_closedBall p (ε / 2)
  have hlineK (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) : line t ∈ K := by
    have hAbs : |t| < δ := abs_lt.mpr ⟨ht.1, ht.2⟩
    have hratio : δ * ‖v‖ ≤ ε / 4 := by
      dsimp [δ]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (‖v‖ + 1))).2
      have hv : 0 ≤ ‖v‖ := norm_nonneg v
      have he : 0 < ε := hε
      nlinarith [mul_nonneg he.le hv]
    have hnorm : ‖line t - p‖ = |t| * ‖v‖ := by
      dsimp [line]
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rw [Metric.mem_closedBall, dist_eq_norm, hnorm]
    have hprodle : |t| * ‖v‖ ≤ δ * ‖v‖ := by gcongr
    calc
      |t| * ‖v‖ ≤ δ * ‖v‖ := hprodle
      _ ≤ ε / 4 := hratio
      _ ≤ ε / 2 := by linarith
  have hKpos : K ⊆ posSet F := by
    intro p' hp'
    apply hεball
    have hpclosed : dist p' p ≤ ε / 2 := by simpa [K] using hp'
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hpclosed (by linarith))
  have hE3 := E3_eis_smooth (F := F) Γ σ s hs
  let V : Fin 1 → Coord F := fun _ => v
  obtain ⟨m, hm, hmBound⟩ := hE3.2.2 K hK hKpos 1 V
  have hlineDeriv (t : ℝ) : HasDerivAt line v t := by
    have hsum := (hasDerivAt_const t p).add ((hasDerivAt_id t).smul_const v)
    have hlineEq : line = (fun _ : ℝ => p) + (fun u : ℝ => u • v) := by
      funext u
      rfl
    rw [hlineEq]
    simpa using hsum
  have htermCont (q : CuspCosets F Γ σ) :
      ContDiffOn ℝ ∞ (fun p' => eisTerm F Γ σ s (ptX F p') q) (posSet F) :=
    specIdentify_eisTerm_smooth Γ σ s q
  have hg (q : CuspCosets F Γ σ) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
      HasDerivAt (g q) (g' q t) t := by
    have hp' : line t ∈ posSet F := hKpos (hlineK t ht)
    have htermAt :=
      (htermCont q).contDiffAt ((specIdentify_posSet_open (F := F)).mem_nhds hp')
    have htermFDeriv := (htermAt.differentiableAt (by simp)).hasFDerivAt
    have hcomp := htermFDeriv.comp_hasDerivAt t (hlineDeriv t)
    change HasDerivAt
      ((fun p' => eisTerm F Γ σ s (ptX F p') q) ∘ line)
      (fderiv ℝ (fun p' => eisTerm F Γ σ s (ptX F p') q) (line t) v) t
    simpa [g, g', Function.comp_def] using hcomp
  have hgBound (q : CuspCosets F Γ σ) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
      ‖g' q t‖ ≤ m q := by
    have h := hmBound q (line t) (hlineK t ht)
    simpa [g', V, iteratedFDeriv_one_apply] using h
  let σ₀ : ℝ := (1 / 2 + s.re) / 2
  have hσ₀ : 1 / 2 < σ₀ := by dsimp [σ₀]; linarith
  have hσ₀le : σ₀ ≤ s.re := by dsimp [σ₀]; linarith
  obtain ⟨m₀, hm₀, hm₀bound⟩ :=
    (E2_eis_converge (F := F) Γ σ).1 {ptX F p} isCompact_singleton σ₀ s.re hσ₀
  have hg0 : Summable (fun q => g q 0) := by
    apply Summable.of_norm_bounded hm₀
    intro q
    have h := hm₀bound (ptX F p) (Set.mem_singleton _) s hσ₀le le_rfl q
    simpa [g, line] using h
  have hzero : (0 : ℝ) ∈ Set.Ioo (-δ) δ := by
    rw [Set.mem_Ioo]
    constructor <;> linarith [hδ]
  have hsumDeriv := hasDerivAt_tsum_of_isPreconnected
    (g := g) (g' := g') (t := Set.Ioo (-δ) δ)
    hm isOpen_Ioo (convex_Ioo _ _).isPreconnected hg hgBound
    hzero hg0 hzero
  have hseriesCont : ContDiffOn ℝ ∞
      (fun p' => eisSeries F Γ σ s (ptX F p')) (posSet F) := hE3.1
  have hseriesAt := (hseriesCont.contDiffAt ((specIdentify_posSet_open (F := F)).mem_nhds hp))
    |>.differentiableAt (by simp) |>.hasFDerivAt
  have hline0 : line 0 = p := by simp [line]
  have hseriesAt' : HasFDerivAt (fun p' => eisSeries F Γ σ s (ptX F p'))
      (fderiv ℝ (fun p' => eisSeries F Γ σ s (ptX F p')) p) (line 0) := by
    rw [hline0]
    exact hseriesAt
  have hseriesComp := hseriesAt'.comp_hasDerivAt 0 (hlineDeriv 0)
  have hseriesDeriv : HasDerivAt
      (fun t => eisSeries F Γ σ s (ptX F (line t)))
      (fderiv ℝ (fun p' => eisSeries F Γ σ s (ptX F p')) p v) 0 := by
    change HasDerivAt
      ((fun p' => eisSeries F Γ σ s (ptX F p')) ∘ line)
      (fderiv ℝ (fun p' => eisSeries F Γ σ s (ptX F p')) p v) 0
    exact hseriesComp
  have hfun : (fun t => ∑' q, g q t) =
      (fun t => eisSeries F Γ σ s (ptX F (line t))) := by
    funext t
    rfl
  have hsumDeriv' := hsumDeriv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun hfun t)
  have hfinal := hsumDeriv'.unique hseriesDeriv
  have hsumDerivative : Summable (fun q : CuspCosets F Γ σ =>
      fderiv ℝ (fun p' => eisTerm F Γ σ s (ptX F p') q) p v) := by
    apply Summable.of_norm_bounded hm
    intro q
    have hpK : p ∈ K := by
      change dist p p ≤ ε / 2
      rw [dist_self]
      positivity
    have h := hmBound q p hpK
    simpa [V, iteratedFDeriv_one_apply] using h
  refine ⟨hsumDerivative, ?_⟩
  simpa [g', line] using hfinal.symm

private theorem specIdentify_smooth_meas
    (D : Set (X F)) (f : X F → ℂ) (hf : IsSmoothX F f) :
    AEStronglyMeasurable f ((volX F).restrict D) ∧
    AEStronglyMeasurable (fullGradient F f) ((volX F).restrict D) := by
  classical
  letI : Countable (InfinitePlace F) := by infer_instance
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, hptCoord, _, _, _, hex⟩
  obtain ⟨e, he, hesym⟩ := hex
  letI : SecondCountableTopology (X F) := e.symm.secondCountableTopology
  let w₀ : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  have hproj : IsOpenQuotientMap (fun z : X F => z w₀) :=
    ⟨(fun z => ⟨fun _ => z, rfl⟩), continuous_apply w₀, isOpenMap_eval w₀⟩
  letI : SecondCountableTopology H3 := Topology.IsOpenQuotientMap.secondCountableTopology hproj
  letI : MeasurableSpace H3 := borel H3
  letI : BorelSpace H3 := ⟨rfl⟩
  have hXBorel : BorelSpace (InfinitePlace F → H3) := Pi.borelSpace
  letI : BorelSpace (X F) := hXBorel
  letI : OpensMeasurableSpace (X F) := BorelSpace.opensMeasurable
  have hcoord : Continuous (coordsX F) := by
    have heq : coordsX F = fun z => (e.symm z).1 := by
      funext z
      exact (hesym z).symm
    rw [heq]
    exact continuous_subtype_val.comp e.symm.continuous
  let g : Coord F → ℂ := fun p => f (ptX F p)
  have hgCont : Continuous (fun p : {p : Coord F // p ∈ posSet F} => g p.1) :=
    hf.continuousOn.domRestrict
  have hfeq : f = fun z => g ((e.symm z).1) := by
    funext z
    dsimp [g]
    rw [hesym z]
    exact congrArg f (hptCoord z).symm
  have hfCont : Continuous f := by
    rw [hfeq]
    exact hgCont.comp e.symm.continuous
  have hWmeas : AEStronglyMeasurable f ((volX F).restrict D) :=
    hfCont.aestronglyMeasurable
  have hDeriv : ContDiffOn ℝ ∞ (fderiv ℝ g) (posSet F) :=
    hf.fderiv_of_isOpen (specIdentify_posSet_open (F := F)) (by simp)
  have hGradCoord : ∀ ij : InfinitePlace F × Fin 3,
      Continuous (fun z => placeGradient F ij.1 f z ij.2) := by
    intro ij
    rcases ij with ⟨w, j⟩
    let v := placeDirection F w j
    let ev : (Coord F →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ v
    have hEvalOn : ContinuousOn (fun p : Coord F => (fderiv ℝ g p) v) (posSet F) := by
      have hev : ContinuousOn ev (Set.univ : Set (Coord F →L[ℝ] ℂ)) :=
        ev.continuous.continuousOn
      exact (ContinuousOn.comp hev hDeriv.continuousOn
        (fun p hp => Set.mem_univ (fderiv ℝ g p)))
    have hPos : ∀ z : X F, coordsX F z ∈ posSet F := by
      intro z
      have hp := (e.symm z).2
      simpa [hesym z] using hp
    have hcoordOn : ContinuousOn (coordsX F) (Set.univ : Set (X F)) := hcoord.continuousOn
    have hPosMaps : Set.MapsTo (coordsX F) Set.univ (posSet F) := fun z hz => hPos z
    have hEval : Continuous fun z : X F => (fderiv ℝ g (coordsX F z)) v :=
      continuousOn_univ.mp (hEvalOn.comp hcoordOn hPosMaps)
    have hheight : Continuous fun z : X F => (coordsX F z w).2 :=
      ((continuous_apply w).comp hcoord).snd
    have hcomp : Continuous fun z : X F =>
        ((coordsX F z w).2 : ℂ) * (fderiv ℝ g (coordsX F z)) v := by
      exact (Complex.ofRealCLM.continuous.comp hheight).mul hEval
    simpa [v, placeGradient, g, Function.comp_def] using hcomp
  have hGradCont : Continuous (fun z => fullGradient F f z) := by
    change Continuous (fun z => WithLp.toLp 2
      (fun ij : InfinitePlace F × Fin 3 => placeGradient F ij.1 f z ij.2))
    exact (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : InfinitePlace F × Fin 3 => ℂ)).symm.continuous.comp
      (continuous_pi hGradCoord)
  exact ⟨hWmeas, hGradCont.aestronglyMeasurable⟩

private theorem specIdentify_bounded_smooth_energy_repr
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (w : X F → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hInv : IsGammaInvariant F Γ w) (hSmooth : IsSmoothX F w)
    (hBound : ∀ z, ‖w z‖ ≤ B)
    (hGradBound : ∀ z, ‖fullGradient F w z‖ ≤ B)
    (hWmeas : AEStronglyMeasurable w ((volX F).restrict D))
    (hGradMeas : AEStronglyMeasurable (fullGradient F w) ((volX F).restrict D)) :
    ∃ x : E.V,
      (∀ᵐ z ∂(volX F), z ∈ D → E.M x z = w z) ∧
      (∀ᵐ z ∂(volX F), z ∈ D → E.Gr x z = fullGradient F w z) := by
  classical
  let μ := (volX F).restrict D
  have hμfinite : μ Set.univ < ⊤ := by
    simpa [μ, Measure.restrict_apply_univ] using spec_finiteVolume_any_fd Γ D hD
  letI : IsFiniteMeasure μ := ⟨hμfinite⟩
  let hwLp : MemLp w 2 μ := MemLp.of_bound hWmeas B
    (Filter.Eventually.of_forall fun z => hBound z)
  let hgradLp : MemLp (fullGradient F w) 2 μ := MemLp.of_bound hGradMeas B
    (Filter.Eventually.of_forall fun z => hGradBound z)
  let wL2 : L2Space F D := hwLp.toLp w
  let gradL2 : GradientL2Space F D := hgradLp.toLp (fullGradient F w)
  have hwAE : ∀ᵐ z ∂(volX F), z ∈ D → wL2 z = w z := by
    exact (ae_restrict_iff'₀ hD.nullMeasurableSet).1 hwLp.coeFn_toLp
  have hgradAE : ∀ᵐ z ∂(volX F), z ∈ D → gradL2 z = fullGradient F w z := by
    exact (ae_restrict_iff'₀ hD.nullMeasurableSet).1 hgradLp.coeFn_toLp
  obtain ⟨x, hMx, hGrx⟩ := T5_cutoff Γ D hD E e w B hB hInv hSmooth
    hBound hGradBound wL2 gradL2 hwAE hgradAE
  refine ⟨x, ?_, ?_⟩
  · filter_upwards [hwAE] with z hz
    intro hzD
    rw [hMx]
    exact hz hzD
  · filter_upwards [hgradAE] with z hz
    intro hzD
    rw [hGrx]
    exact hz hzD

private theorem specIdentify_T7_estimate
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E) :
    ∃ R : E.V →L[ℂ] L2Space F D, IsCompactOperator R ∧
      ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
        ∀ x : E.V, ‖E.M x‖ ^ 2 ≤ c * ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2 := by
  classical
  let d : SiegelData F Γ := Classical.choice (spec_exists_siegelData Γ)
  obtain ⟨A₀, hA₀, hsep⟩ := (R10_cusp_separation (F := F) Γ).2.1 d
  let A : d.ι → ℝ := fun _ => A₀
  have hApos : ∀ i, 0 < A i := fun _ => lt_of_lt_of_le zero_lt_one hA₀
  have hAsep : ∀ i j : d.ι, ∀ γ γ' : Γ, ∀ z : X F,
      A i ≤ normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A j ≤ normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d.σ i) := by
    intro i j γ γ' z hi hj
    exact hsep A₀ le_rfl i j γ γ' z hi hj
  obtain ⟨K, hK, C₀, hC₀, R, hR, hT7, _⟩ :=
    T7_ground_state Γ D hD d A hApos hAsep E e A₀ (fun _ => le_rfl)
  let k : ℝ := placeCount F * (1 - 1 / (2 * A₀))
  have hr : 0 < placeCount F := by
    unfold placeCount
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (InfinitePlace F)))
  have hk : 0 < k := by
    dsimp [k]
    have hA₀pos : 0 < A₀ := lt_of_lt_of_le zero_lt_one hA₀
    have hfactor : 0 < 1 - 1 / (2 * A₀) := by
      have hden : 1 / (2 * A₀) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * A₀)).2
        nlinarith [hA₀]
      linarith
    exact mul_pos hr hfactor
  let c : ℝ := k⁻¹
  let C : ℝ := C₀ * k⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨R, hR, c, C, hc, hC, ?_⟩
  intro x
  have hmul := mul_le_mul_of_nonneg_right (hT7 x) (inv_nonneg.mpr hk.le)
  have hleft : (k * ‖E.M x‖ ^ 2) * k⁻¹ = ‖E.M x‖ ^ 2 := by
    field_simp [hk.ne']
  rw [hleft] at hmul
  calc
    ‖E.M x‖ ^ 2 ≤ (‖E.Gr x‖ ^ 2 + C₀ * ‖R x‖ ^ 2) * k⁻¹ := hmul
    _ = c * ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2 := by
      dsimp [c, C]
      ring

private theorem specIdentify_cutoffResidual_bound
    (τ : ℝ → ℝ) (A : ℝ) (hA : 1 ≤ A) (a : ℂ)
    (haRe : 0 ≤ a.re) (ha : ‖a‖ ≤ 7) (hτ : IsCuspCutoff A τ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g : InfinitePlace F → SL(2,ℂ), ∀ z : X F,
      ‖((1 - τ (normHeight F (actAtPlaces F g z)) : ℝ) : ℂ) *
        (normHeight F (actAtPlaces F g z) : ℂ) ^ a‖ ≤ B ∧
      ‖fullGradient F (fun x =>
        ((1 - τ (normHeight F (actAtPlaces F g x)) : ℝ) : ℂ) *
          (normHeight F (actAtPlaces F g x) : ℂ) ^ a) z‖ ≤ B := by
  let M : ℝ := max 1 ((2 * A) ^ 7)
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hbase : 1 ≤ 2 * A := by linarith
  have hre : a.re ≤ 7 := (le_abs_self a.re).trans
    ((Complex.abs_re_le_norm a).trans ha)
  have hpow (t : ℝ) (ht : 0 < t) (htA : t ≤ 2 * A) : t ^ a.re ≤ M := by
    by_cases htOne : t ≤ 1
    · exact (Real.rpow_le_one ht.le htOne haRe).trans (le_max_left _ _)
    · calc
        t ^ a.re ≤ (2 * A) ^ a.re := Real.rpow_le_rpow ht.le htA haRe
        _ ≤ (2 * A) ^ 7 := Real.rpow_le_rpow_of_exponent_le hbase hre
        _ ≤ M := by simpa [M] using (le_max_right 1 ((2 * A) ^ 7))
  have hτrange (t : ℝ) : 0 ≤ τ t ∧ τ t ≤ 1 := by
    constructor
    · by_cases ht : t ≤ A
      · rw [hτ.2.2.1 t ht]
      · have h := hτ.2.1 (le_of_not_ge ht)
        rw [hτ.2.2.1 A le_rfl] at h
        exact h
    · by_cases ht : 2 * A ≤ t
      · rw [hτ.2.2.2 t ht]
      · have h := hτ.2.1 (le_of_not_ge ht)
        rw [hτ.2.2.2 (2 * A) le_rfl] at h
        exact h
  have hvalue (t : ℝ) (ht : 0 < t) :
      ‖((1 - τ t : ℝ) : ℂ) * (t : ℂ) ^ a‖ ≤ M := by
    by_cases htA : 2 * A ≤ t
    · rw [hτ.2.2.2 t htA]
      simpa using hM
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        specIdentify_cpow_norm t a ht]
      have hfactor : |1 - τ t| ≤ 1 := by
        rw [abs_le]
        have hrange := hτrange t
        constructor <;> linarith only [hrange.1, hrange.2]
      calc
        |1 - τ t| * t ^ a.re ≤ 1 * t ^ a.re :=
          mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg ht.le _)
        _ ≤ M := by simpa using hpow t ht (le_of_not_ge htA)
  obtain ⟨C, hC, hderiv⟩ := specIdentify_cutoffResidual_deriv_bound τ A hA a haRe ha hτ
  let B : ℝ := max M (C * Real.sqrt (placeCount F))
  have hB : 0 ≤ B := hM.trans (le_max_left _ _)
  refine ⟨B, hB, ?_⟩
  intro g z
  have ht : 0 < normHeight F (actAtPlaces F g z) := specIdentify_normHeight_pos _
  refine ⟨(hvalue _ ht).trans (le_max_left _ _), ?_⟩
  have hχ : ContDiff ℝ ∞ (fun t : ℝ => 1 - τ t) := contDiff_const.sub hτ.1
  rw [specIdentify_radial_action_gradient_norm g (fun t => 1 - τ t) a hχ z]
  exact (mul_le_mul_of_nonneg_right (hderiv _ ht) (Real.sqrt_nonneg _)).trans
    (le_max_right _ _)

private theorem specIdentify_seed_gradient_tsum
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ σ' : SL(2,F)) (τ : ℝ → ℝ) (cut : CutoffData F Γ σ τ)
    (s : ℂ) (z : X F) :
    Summable (fun q : CuspCosets F Γ σ =>
      fullGradient F (fun x => seedTerm F Γ σ τ s (σ' • x) q) z) ∧
    fullGradient F (fun x => eisSeed F Γ σ τ s (σ' • x)) z =
      ∑' q : CuspCosets F Γ σ,
        fullGradient F (fun x => seedTerm F Γ σ τ s (σ' • x) q) z := by
  classical
  have hA : 0 < cut.A := lt_of_lt_of_le zero_lt_one (cut.A₀_ge.trans cut.A_ge)
  obtain ⟨Q, hQ, U, hUopen, hzU, hzero⟩ :=
    specIdentify_seedHighCosets_finite Γ σ σ' τ cut.A hA cut.cutoff s z
  let S : Finset (CuspCosets F Γ σ) := hQ.toFinset
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := by
    intro w
    change 0 < height (z w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, hptCoord, _, _, _, hchart⟩
  obtain ⟨chart, hchart, _⟩ := hchart
  have hpt : ptX F p = z := hptCoord z
  have hPtOn : ContinuousOn (ptX F) (posSet F) := by
    have heq : (posSet F).domRestrict (ptX F) = chart := by
      funext p'
      exact (hchart p').symm
    exact continuousOn_iff_continuous_domRestrict.mpr (heq ▸ chart.continuous)
  have hPtAt : ContinuousAt (ptX F) p :=
    (hPtOn p hp).continuousAt ((specIdentify_posSet_open (F := F)).mem_nhds hp)
  have hUevent : ∀ᶠ p' : Coord F in 𝓝 p, ptX F p' ∈ U :=
    hPtAt.eventually (hUopen.mem_nhds (hpt.symm ▸ hzU))
  have houtside (q : CuspCosets F Γ σ) (hq : q ∉ S) :
      fullGradient F (fun x => seedTerm F Γ σ τ s (σ' • x) q) z = 0 := by
    have hqQ : q ∉ Q := by simpa [S] using hq
    have hlocal : (fun p' : Coord F => seedTerm F Γ σ τ s (σ' • ptX F p') q)
        =ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := by
      filter_upwards [hUevent] with p' hp'
      exact hzero (ptX F p') hp' q hqQ
    have hder := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hlocal
    ext wj
    rcases wj with ⟨w, j⟩
    change ((coordsX F z w).2 : ℂ) *
      fderiv ℝ (fun p' => seedTerm F Γ σ τ s (σ' • ptX F p') q) p
        (placeDirection F w j) = 0
    rw [hder]
    simp
  have hlocalSum : (fun p' : Coord F => eisSeed F Γ σ τ s (σ' • ptX F p'))
      =ᶠ[𝓝 p] (fun p' => ∑ q ∈ S, seedTerm F Γ σ τ s (σ' • ptX F p') q) := by
    filter_upwards [hUevent] with p' hp'
    unfold eisSeed
    apply tsum_eq_sum (s := S)
    intro q hq
    exact hzero (ptX F p') hp' q (by simpa [S] using hq)
  have hderSum := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hlocalSum
  have htermDiff (q : CuspCosets F Γ σ) :
      DifferentiableAt ℝ (fun p' => seedTerm F Γ σ τ s (σ' • ptX F p') q) p := by
    have hsm : ContDiffOn ℝ ∞
        (fun p' => seedTerm F Γ σ τ s (σ' • ptX F p') q) (posSet F) :=
      specIdentify_seedTerm_smooth_action Γ σ σ' τ cut.cutoff.1 s q
    exact (hsm.contDiffAt ((specIdentify_posSet_open (F := F)).mem_nhds hp)).differentiableAt
      (by norm_num)
  refine ⟨summable_of_ne_finset_zero houtside, ?_⟩
  rw [tsum_eq_sum (s := S) houtside]
  change WithLp.toLp 2 (fun wj : InfinitePlace F × Fin 3 =>
      placeGradient F wj.1 (fun x => eisSeed F Γ σ τ s (σ' • x)) z wj.2) =
    ∑ q ∈ S, WithLp.toLp 2 (fun wj : InfinitePlace F × Fin 3 =>
      placeGradient F wj.1 (fun x => seedTerm F Γ σ τ s (σ' • x) q) z wj.2)
  rw [← WithLp.toLp_sum]
  congr 1
  funext wj
  rcases wj with ⟨w, j⟩
  simp only [Finset.sum_apply, placeGradient]
  change ((coordsX F z w).2 : ℂ) *
    fderiv ℝ (fun p' => eisSeed F Γ σ τ s (σ' • ptX F p')) p
      (placeDirection F w j) =
    ∑ q ∈ S, ((coordsX F z w).2 : ℂ) *
      fderiv ℝ (fun p' => seedTerm F Γ σ τ s (σ' • ptX F p') q) p
        (placeDirection F w j)
  rw [hderSum, fderiv_fun_sum (fun q _ => htermDiff q)]
  simp only [ContinuousLinearMap.sum_apply, Finset.mul_sum]

private theorem specIdentify_eis_gradient_tsum
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (hs : 1 / 2 < s.re) (z : X F) :
    Summable (fun q : CuspCosets F Γ σ =>
      fullGradient F (fun x => eisTerm F Γ σ s x q) z) ∧
    fullGradient F (eisSeries F Γ σ s) z =
      ∑' q : CuspCosets F Γ σ,
        fullGradient F (fun x => eisTerm F Γ σ s x q) z := by
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := by
    intro w
    change 0 < height (z w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hcoord (wj : InfinitePlace F × Fin 3) :
      HasSum (fun q : CuspCosets F Γ σ =>
        placeGradient F wj.1 (fun x => eisTerm F Γ σ s x q) z wj.2)
        (placeGradient F wj.1 (eisSeries F Γ σ s) z wj.2) := by
    obtain ⟨hSumm, hDeriv⟩ := specIdentify_eisSeries_fderiv_tsum Γ σ s hs p hp
      (placeDirection F wj.1 wj.2)
    change HasSum (fun q : CuspCosets F Γ σ =>
      ((coordsX F z wj.1).2 : ℂ) *
        fderiv ℝ (fun p' => eisTerm F Γ σ s (ptX F p') q) p
          (placeDirection F wj.1 wj.2))
      (((coordsX F z wj.1).2 : ℂ) *
        fderiv ℝ (fun p' => eisSeries F Γ σ s (ptX F p')) p
          (placeDirection F wj.1 wj.2))
    rw [hDeriv]
    exact hSumm.hasSum.mul_left _
  have hPi : HasSum
      (fun q : CuspCosets F Γ σ => fun wj : InfinitePlace F × Fin 3 =>
        placeGradient F wj.1 (fun x => eisTerm F Γ σ s x q) z wj.2)
      (fun wj : InfinitePlace F × Fin 3 =>
        placeGradient F wj.1 (eisSeries F Γ σ s) z wj.2) :=
    Pi.hasSum.mpr hcoord
  let toGrad : (InfinitePlace F × Fin 3 → ℂ) →L[ℂ] GradientField F :=
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : InfinitePlace F × Fin 3 => ℂ)).symm).toContinuousLinearMap
  have hGrad : HasSum
      (fun q : CuspCosets F Γ σ =>
        fullGradient F (fun x => eisTerm F Γ σ s x q) z)
      (fullGradient F (eisSeries F Γ σ s) z) := by
    exact hPi.map toGrad toGrad.continuous
  exact ⟨hGrad.summable, hGrad.tsum_eq.symm⟩

private theorem specIdentify_nontriangular_bound
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (σ : SL(2,F)) (s : ℂ)
    (hs : 2 < s.re ∧ s.re < 3) (i : d.ι) :
    let Q := {q : CuspCosets F Γ σ //
      σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∉ borelSL F}
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ SiegelData.setAt F d i,
      Summable (fun q : Q => eisTerm F Γ σ s ((d.σ i) • z) q.1) ∧
      Summable (fun q : Q =>
        fullGradient F (fun x => eisTerm F Γ σ s x q.1) ((d.σ i) • z)) ∧
      ‖∑' q : Q, eisTerm F Γ σ s ((d.σ i) • z) q.1‖ ≤ C ∧
      ‖∑' q : Q,
        fullGradient F (fun x => eisTerm F Γ σ s x q.1) ((d.σ i) • z)‖ ≤ C := by
  classical
  let Q := {q : CuspCosets F Γ σ //
    σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∉ borelSL F}
  have hstrip : ({s} : Set ℂ) ⊆ {s' : ℂ | 2 < s'.re ∧ s'.re < 3} := by
    intro s' hs'
    rcases Set.mem_singleton_iff.mp hs' with rfl
    exact hs
  obtain ⟨C, hC, hbound⟩ :=
    (E4_eis_siegel Γ d σ {s} isCompact_singleton hstrip i).2.1
  refine ⟨C, hC, ?_⟩
  intro z hz
  obtain ⟨hm, hsum⟩ := hbound s (Set.mem_singleton s) z hz
  let value : Q → ℂ := fun q => eisTerm F Γ σ s ((d.σ i) • z) q.1
  let grad : Q → GradientField F := fun q =>
    fullGradient F (fun x => eisTerm F Γ σ s x q.1) ((d.σ i) • z)
  let m : Q → ℝ := fun q => ‖value q‖ +
    ‖fullGradient F (fun x => eisTerm F Γ σ s ((d.σ i) • x) q.1) z‖
  have hm' : Summable m := hm
  have hsum' : (∑' q : Q, m q) ≤ C := hsum
  have hgradNorm (q : Q) : ‖grad q‖ =
      ‖fullGradient F (fun x => eisTerm F Γ σ s ((d.σ i) • x) q.1) z‖ := by
    exact (specIdentify_gradient_norm_isometry (toInf F (d.σ i))
      (fun x => eisTerm F Γ σ s x q.1) (specIdentify_eisTerm_smooth Γ σ s q.1) z).symm
  have hvalueDom (q : Q) : ‖value q‖ ≤ m q :=
    le_add_of_nonneg_right (norm_nonneg _)
  have hgradDom (q : Q) : ‖grad q‖ ≤ m q := by
    rw [hgradNorm]
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hvalueNormSumm : Summable (fun q : Q => ‖value q‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hvalueDom hm'
  have hgradNormSumm : Summable (fun q : Q => ‖grad q‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hgradDom hm'
  have hvalueSumm : Summable value := Summable.of_norm_bounded hm' hvalueDom
  have hgradSumm : Summable grad := Summable.of_norm_bounded hm' hgradDom
  have hvalueBound : ‖∑' q : Q, value q‖ ≤ C :=
    (norm_tsum_le_tsum_norm hvalueNormSumm).trans
      ((hvalueNormSumm.tsum_le_tsum hvalueDom hm').trans hsum')
  have hgradBound : ‖∑' q : Q, grad q‖ ≤ C :=
    (norm_tsum_le_tsum_norm hgradNormSumm).trans
      ((hgradNormSumm.tsum_le_tsum hgradDom hm').trans hsum')
  exact ⟨hvalueSumm, hgradSumm, hvalueBound, hgradBound⟩

private theorem specIdentify_nontriangular_seed_bound
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (σ : SL(2,F)) (τ : ℝ → ℝ)
    (cut : CutoffData F Γ σ τ) (s : ℂ) (i : d.ι) :
    let Q := {q : CuspCosets F Γ σ //
      σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∉ borelSL F}
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ SiegelData.setAt F d i,
      Summable (fun q : Q => seedTerm F Γ σ τ s ((d.σ i) • z) q.1) ∧
      Summable (fun q : Q =>
        fullGradient F (fun x => seedTerm F Γ σ τ s x q.1) ((d.σ i) • z)) ∧
      ‖∑' q : Q, seedTerm F Γ σ τ s ((d.σ i) • z) q.1‖ ≤ C ∧
      ‖∑' q : Q,
        fullGradient F (fun x => seedTerm F Γ σ τ s x q.1) ((d.σ i) • z)‖ ≤ C := by
  classical
  let Q := {q : CuspCosets F Γ σ //
    σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∉ borelSL F}
  let a : ℂ := 1 + 2 * s
  let b (q : CuspCosets F Γ σ) : SL(2,F) :=
    σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
  let heightAt (q : CuspCosets F Γ σ) (x : X F) : ℝ :=
    normHeight F (actAtPlaces F (toInf F (b q)) x)
  let f (q : CuspCosets F Γ σ) : X F → ℂ := fun x => seedTerm F Γ σ τ s x q
  have hact (q : CuspCosets F Γ σ) (x : X F) :
      σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • x) =
        actAtPlaces F (toInf F (b q)) x := by
    change σ⁻¹ • ((toSLF F ((q.out : Γ) : SL(2,𝓞 F))) • x) = b q • x
    rw [← mul_smul]
  have hheight (q : CuspCosets F Γ σ) (x : X F) :
      heightAt q x = normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • x)) :=
    congrArg (normHeight F) (hact q x).symm
  have hseed (q : CuspCosets F Γ σ) : f q =
      fun x => (τ (heightAt q x) : ℂ) * (heightAt q x : ℂ) ^ a := by
    funext x
    simp only [f, seedTerm, hact, heightAt, a]
  obtain ⟨R, hRpos, hR⟩ := (R6_two_heights (F := F) Γ).2 (d.σ i) σ
  have hLower : 0 < SiegelData.lowerHeight F d i := by
    unfold SiegelData.lowerHeight
    have hI : bottomRowFractionalIdeal F ((d.σ i)⁻¹) ≠ 0 :=
      (R3_cusps_finite (F := F) Γ).2.1 ((d.σ i)⁻¹)
    have hnormNe : FractionalIdeal.absNorm
        (bottomRowFractionalIdeal F ((d.σ i)⁻¹)) ≠ 0 := by
      intro hh
      exact hI (FractionalIdeal.absNorm_eq_zero_iff.mp hh)
    have hnormPos : 0 < FractionalIdeal.absNorm
        (bottomRowFractionalIdeal F ((d.σ i)⁻¹)) :=
      lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm hnormNe)
    have hrealPos : 0 <
        ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F ((d.σ i)⁻¹)) : ℚ) : ℝ) := by
      exact_mod_cast hnormPos
    exact inv_pos.mpr (mul_pos hrealPos d.C_M_pos)
  let H : ℝ := max (2 * cut.A) (R / SiegelData.lowerHeight F d i)
  have hAone : 1 ≤ cut.A := cut.A₀_ge.trans cut.A_ge
  have hApos : 0 < cut.A := lt_of_lt_of_le zero_lt_one hAone
  have hAH : cut.A ≤ H := by
    have hA2 : cut.A ≤ 2 * cut.A := by linarith only [hApos]
    exact hA2.trans (le_max_left _ _)
  obtain ⟨Mv, hMv, hprofile⟩ := specIdentify_profile_interval_bound τ a cut.cutoff.1
    (Real.log cut.A) (Real.log H) (Real.log_le_log hApos hAH)
  obtain ⟨Mg, hMg, hderiv⟩ := specIdentify_seedProfile_deriv_bound τ cut.A hAone
    cut.cutoff a H (le_max_left _ _)
  let C : ℝ := max Mv (Mg * Real.sqrt (placeCount F))
  have hC : 0 ≤ C := hMv.trans (le_max_left _ _)
  have htermBound (q : CuspCosets F Γ σ) (x : X F) (htH : heightAt q x ≤ H) :
      ‖f q x‖ ≤ C ∧ ‖fullGradient F (f q) x‖ ≤ C := by
    let t : ℝ := heightAt q x
    have ht : 0 < t := specIdentify_normHeight_pos _
    constructor
    · by_cases htA : t ≤ cut.A
      · rw [hseed q]
        change ‖(τ t : ℂ) * (t : ℂ) ^ a‖ ≤ C
        rw [cut.cutoff.2.2.1 t htA]
        simpa only [Complex.ofReal_zero, zero_mul, norm_zero] using hC
      · have hlog : Real.log t ∈ Set.Icc (Real.log cut.A) (Real.log H) :=
          ⟨Real.log_le_log hApos (le_of_not_ge htA), Real.log_le_log ht htH⟩
        rw [hseed q]
        change ‖(τ t : ℂ) * (t : ℂ) ^ a‖ ≤ C
        rw [← specIdentifyRadialProfile_log τ a ht]
        exact ((hprofile (Real.log t) hlog).1).trans (le_max_left _ _)
    · rw [hseed q]
      change ‖fullGradient F (fun y =>
        (τ (normHeight F (actAtPlaces F (toInf F (b q)) y)) : ℂ) *
          (normHeight F (actAtPlaces F (toInf F (b q)) y) : ℂ) ^ a) x‖ ≤ C
      rw [specIdentify_radial_action_gradient_norm (toInf F (b q)) τ a cut.cutoff.1 x]
      exact (mul_le_mul_of_nonneg_right (hderiv t ht htH) (Real.sqrt_nonneg _)).trans
        (le_max_right _ _)
  have hupper (z : X F) (hz : z ∈ SiegelData.setAt F d i) (q : Q) :
      heightAt q.1 ((d.σ i) • z) ≤ H := by
    have hNy : SiegelData.lowerHeight F d i ≤ normHeight F z := by
      have hz' := hz
      simp only [SiegelData.setAt, siegelSet] at hz'
      rcases hz' with ⟨x, y, hEq, hx, hbal, hNy⟩
      rw [← hEq] at hNy
      exact hNy
    have hentry : (σ⁻¹ * toSLF F ((q.1.out : Γ) : SL(2,𝓞 F)) * d.σ i) 1 0 ≠ 0 := by
      intro h0
      apply q.2
      change (σ⁻¹ * toSLF F ((q.1.out : Γ) : SL(2,𝓞 F)) * d.σ i) 1 0 = 0
      exact h0
    have hproduct : normHeight F z * heightAt q.1 ((d.σ i) • z) ≤ R := by
      have h := hR q.1.out ((d.σ i) • z) hentry
      simpa only [inv_smul_smul, ← hheight] using h
    have ht : 0 < heightAt q.1 ((d.σ i) • z) := specIdentify_normHeight_pos _
    have hquot : heightAt q.1 ((d.σ i) • z) ≤ R / SiegelData.lowerHeight F d i := by
      apply (le_div_iff₀ hLower).2
      calc
        heightAt q.1 ((d.σ i) • z) * SiegelData.lowerHeight F d i ≤
            heightAt q.1 ((d.σ i) • z) * normHeight F z :=
          mul_le_mul_of_nonneg_left hNy ht.le
        _ = normHeight F z * heightAt q.1 ((d.σ i) • z) := mul_comm _ _
        _ ≤ R := hproduct
    exact hquot.trans (le_max_right _ _)
  have hUnique (x : X F) (q q' : CuspCosets F Γ σ)
      (hq : cut.A₀ ≤ heightAt q x) (hq' : cut.A₀ ≤ heightAt q' x) : q = q' := by
    have hsep := cut.separation q.out q'.out x (hheight q x ▸ hq) (hheight q' x ▸ hq')
    have hrel : QuotientGroup.rightRel (cuspStab F Γ σ) q.out q'.out :=
      QuotientGroup.rightRel_apply.mpr hsep
    calc
      q = Quotient.mk _ q.out := (Quotient.out_eq' q).symm
      _ = Quotient.mk _ q'.out := Quotient.sound hrel
      _ = q' := Quotient.out_eq' q'
  have hlowValue (q : CuspCosets F Γ σ) (x : X F) (hlt : heightAt q x < cut.A₀) :
      f q x = 0 := by
    rw [hseed q]
    change (τ (heightAt q x) : ℂ) * (heightAt q x : ℂ) ^ a = 0
    rw [cut.cutoff.2.2.1 (heightAt q x) (hlt.le.trans cut.A_ge)]
    simp only [Complex.ofReal_zero, zero_mul]
  have hlow (q : CuspCosets F Γ σ) (x : X F) (hlt : heightAt q x < cut.A₀) :
      f q x = 0 ∧ fullGradient F (f q) x = 0 := by
    refine ⟨hlowValue q x hlt, ?_⟩
    let p : Coord F := coordsX F x
    have hp : p ∈ posSet F := by
      intro w
      change 0 < height (x w)
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (x w)
    have hpt : ptX F p = x := (G1_h3_basics (F := F)).2.2.2.2.2.2.2.1 x
    have hCont : ContinuousAt (fun p' : Coord F => heightAt q (ptX F p')) p := by
      have hSm : ContDiffOn ℝ ∞ (fun p' : Coord F => heightAt q (ptX F p')) (posSet F) :=
        specIdentify_heightAction_smooth (b q)
      exact (hSm.contDiffAt ((specIdentify_posSet_open (F := F)).mem_nhds hp)).continuousAt
    have hlt' : heightAt q (ptX F p) < cut.A₀ := hpt.symm ▸ hlt
    have hlocal : (fun p' : Coord F => f q (ptX F p')) =ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := by
      filter_upwards [hCont.eventually (isOpen_Iio.mem_nhds hlt')] with p' hp'
      exact hlowValue q (ptX F p') hp'
    have hder := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hlocal
    ext wj
    rcases wj with ⟨w, j⟩
    change ((coordsX F x w).2 : ℂ) *
      fderiv ℝ (fun p' => f q (ptX F p')) p (placeDirection F w j) = 0
    rw [hder]
    simp
  refine ⟨C, hC, ?_⟩
  intro z hz
  let x : X F := (d.σ i) • z
  change Summable (fun q : Q => f q.1 x) ∧
    Summable (fun q : Q => fullGradient F (f q.1) x) ∧
    ‖∑' q : Q, f q.1 x‖ ≤ C ∧
    ‖∑' q : Q, fullGradient F (f q.1) x‖ ≤ C
  by_cases hex : ∃ q : Q, cut.A₀ ≤ heightAt q.1 x
  · obtain ⟨q₀, hq₀⟩ := hex
    have hother (q : Q) (hq : q ≠ q₀) :
        f q.1 x = 0 ∧ fullGradient F (f q.1) x = 0 := by
      apply hlow q.1 x
      apply lt_of_not_ge
      intro hqHigh
      exact hq (Subtype.ext (hUnique x q.1 q₀.1 hqHigh hq₀))
    have hvalueSumm : Summable (fun q : Q => f q.1 x) :=
      summable_of_ne_finset_zero (s := {q₀}) (fun q hq =>
        (hother q (by simpa only [Finset.mem_singleton] using hq)).1)
    have hgradSumm : Summable (fun q : Q => fullGradient F (f q.1) x) :=
      summable_of_ne_finset_zero (s := {q₀}) (fun q hq =>
        (hother q (by simpa only [Finset.mem_singleton] using hq)).2)
    have hvalueSum : (∑' q : Q, f q.1 x) = f q₀.1 x :=
      tsum_eq_single q₀ (fun q hq => (hother q hq).1)
    have hgradSum : (∑' q : Q, fullGradient F (f q.1) x) = fullGradient F (f q₀.1) x :=
      tsum_eq_single q₀ (fun q hq => (hother q hq).2)
    have hbnd := htermBound q₀.1 x (hupper z hz q₀)
    refine ⟨hvalueSumm, hgradSumm, ?_, ?_⟩
    · rw [hvalueSum]
      exact hbnd.1
    · rw [hgradSum]
      exact hbnd.2
  · have hzero (q : Q) : f q.1 x = 0 ∧ fullGradient F (f q.1) x = 0 :=
      hlow q.1 x (lt_of_not_ge (fun h => hex ⟨q, h⟩))
    have hvzero : (fun q : Q => f q.1 x) = 0 := funext fun q => (hzero q).1
    have hgzero : (fun q : Q => fullGradient F (f q.1) x) = 0 := funext fun q => (hzero q).2
    rw [hvzero, hgzero]
    refine ⟨summable_zero, summable_zero, ?_, ?_⟩
    · change ‖∑' q : Q, (0 : ℂ)‖ ≤ C
      simpa only [tsum_zero, norm_zero] using hC
    · change ‖∑' q : Q, (0 : GradientField F)‖ ≤ C
      simpa only [tsum_zero, norm_zero] using hC

set_option maxHeartbeats 1000000 in
private theorem specIdentify_cusp_bound
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (τ : ℝ → ℝ) (cut : CutoffData F Γ σ τ)
    (s : ℂ) (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2))
    (d : SiegelData F Γ) (i : d.ι) :
    let w := fun z => eisSeries F Γ σ s z - eisSeed F Γ σ τ s z
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ SiegelData.setAt F d i,
      ‖w ((d.σ i) • z)‖ ≤ B ∧
      ‖fullGradient F (fun x => w ((d.σ i) • x)) z‖ ≤ B := by
  classical
  have hdist : ‖s - (5 / 2 : ℂ)‖ < 1 / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hs
  have hRe : |s.re - (5 / 2 : ℝ)| < 1 / 2 := by
    have h := Complex.abs_re_le_norm (s - (5 / 2 : ℂ))
    have heq : (s - (5 / 2 : ℂ)).re = s.re - (5 / 2 : ℝ) := by norm_num
    rw [heq] at h
    exact h.trans_lt hdist
  obtain ⟨hReLo, hReHi⟩ := abs_lt.mp hRe
  have hstrip : 2 < s.re ∧ s.re < 3 := by
    constructor <;> linarith only [hReLo, hReHi]
  have hhalf : 1 / 2 < s.re := by linarith only [hstrip.1]
  have hnorms : ‖s‖ < 3 := by
    calc
      ‖s‖ = ‖(s - (5 / 2 : ℂ)) + (5 / 2 : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖s - (5 / 2 : ℂ)‖ + ‖(5 / 2 : ℂ)‖ := norm_add_le _ _
      _ < 3 := by norm_num; linarith only [hdist]
  let a : ℂ := 1 + 2 * s
  have haRe : 0 ≤ a.re := by
    have haReal : a.re = 1 + 2 * s.re := by
      dsimp [a]
      norm_num [Complex.add_re, Complex.mul_re]
    rw [haReal]
    linarith only [hstrip.1]
  have haNorm : ‖a‖ ≤ 7 := by
    calc
      ‖a‖ ≤ ‖(1 : ℂ)‖ + ‖2 * s‖ := norm_add_le _ _
      _ = 1 + 2 * ‖s‖ := by norm_num [norm_mul]
      _ ≤ 7 := by linarith only [hnorms]
  obtain ⟨B, hB, hResidual⟩ := specIdentify_cutoffResidual_bound (F := F) τ cut.A
    (cut.A₀_ge.trans cut.A_ge) a haRe haNorm cut.cutoff
  obtain ⟨CE, hCE, hNonE⟩ := specIdentify_nontriangular_bound Γ d σ s hstrip i
  obtain ⟨CS, hCS, hNonS⟩ := specIdentify_nontriangular_seed_bound Γ d σ τ cut s i
  have hKstrip : ({s} : Set ℂ) ⊆ {s' : ℂ | 2 < s'.re ∧ s'.re < 3} := by
    intro s' hs'
    rcases Set.mem_singleton_iff.mp hs' with rfl
    exact hstrip
  let tri (q : CuspCosets F Γ σ) : Prop :=
    σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * d.σ i ∈ borelSL F
  let Tri := {q : CuspCosets F Γ σ // tri q}
  let Nontri := {q : CuspCosets F Γ σ // ¬ tri q}
  have hTriUnique : ∀ q q' : CuspCosets F Γ σ, tri q → tri q' → q = q' :=
    (E4_eis_siegel Γ d σ {s} isCompact_singleton hKstrip i).1
  letI : Subsingleton Tri := ⟨fun q q' => Subtype.ext (hTriUnique q.1 q'.1 q.2 q'.2)⟩
  let te (q : CuspCosets F Γ σ) : X F → ℂ := fun x => eisTerm F Γ σ s x q
  let ts (q : CuspCosets F Γ σ) : X F → ℂ := fun x => seedTerm F Γ σ τ s x q
  let residual (q : CuspCosets F Γ σ) : X F → ℂ := fun x => te q x - ts q x
  let w : X F → ℂ := fun x => eisSeries F Γ σ s x - eisSeed F Γ σ τ s x
  have hE3 := E3_eis_smooth Γ σ s hhalf
  have hE5 := E5_seed Γ D hD σ cut.A₀ cut.A cut.A₀_ge cut.A_ge cut.separation τ cut.cutoff
  have hSeedSmooth : IsSmoothX F (eisSeed F Γ σ τ s) := (hE5.2.1 s).1
  have hSmooth : IsSmoothX F w := by
    have hsmE : ContDiffOn ℝ ∞ (fun p => eisSeries F Γ σ s (ptX F p)) (posSet F) := hE3.1
    have hsmS : ContDiffOn ℝ ∞ (fun p => eisSeed F Γ σ τ s (ptX F p)) (posSet F) := hSeedSmooth
    exact hsmE.sub hsmS
  have hSeedTermSmooth (q : CuspCosets F Γ σ) : IsSmoothX F (ts q) := by
    simpa only [one_smul] using specIdentify_seedTerm_smooth_action Γ σ 1 τ cut.cutoff.1 s q
  have hGradSub (f g : X F → ℂ) (hf : IsSmoothX F f) (hg : IsSmoothX F g) (x : X F) :
      fullGradient F (fun y => f y - g y) x = fullGradient F f x - fullGradient F g x := by
    let p : Coord F := coordsX F x
    have hp : p ∈ posSet F := by
      intro v
      change 0 < height (x v)
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (x v)
    have hfOn : ContDiffOn ℝ ∞ (fun p' => f (ptX F p')) (posSet F) := hf
    have hgOn : ContDiffOn ℝ ∞ (fun p' => g (ptX F p')) (posSet F) := hg
    have hfDiff := (hfOn.contDiffAt ((specIdentify_posSet_open (F := F)).mem_nhds hp))
      |>.differentiableAt (by norm_num)
    have hgDiff := (hgOn.contDiffAt ((specIdentify_posSet_open (F := F)).mem_nhds hp))
      |>.differentiableAt (by norm_num)
    ext wj
    rcases wj with ⟨v, j⟩
    change ((coordsX F x v).2 : ℂ) *
      fderiv ℝ (fun p' => f (ptX F p') - g (ptX F p')) p (placeDirection F v j) =
      ((coordsX F x v).2 : ℂ) * fderiv ℝ (fun p' => f (ptX F p')) p (placeDirection F v j) -
      ((coordsX F x v).2 : ℂ) * fderiv ℝ (fun p' => g (ptX F p')) p (placeDirection F v j)
    rw [fderiv_fun_sub hfDiff hgDiff]
    simp only [ContinuousLinearMap.sub_apply, mul_sub]
  have hResGrad (q : CuspCosets F Γ σ) (x : X F) :
      fullGradient F (residual q) x = fullGradient F (te q) x - fullGradient F (ts q) x :=
    hGradSub (te q) (ts q) (specIdentify_eisTerm_smooth Γ σ s q) (hSeedTermSmooth q) x
  have hResBound (q : CuspCosets F Γ σ) (x : X F) :
      ‖residual q x‖ ≤ B ∧ ‖fullGradient F (residual q) x‖ ≤ B := by
    let b : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
    have hact (y : X F) : σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • y) =
        actAtPlaces F (toInf F b) y := by
      change σ⁻¹ • ((toSLF F ((q.out : Γ) : SL(2,𝓞 F))) • y) = b • y
      rw [← mul_smul]
    have hEq : residual q = fun y =>
        ((1 - τ (normHeight F (actAtPlaces F (toInf F b) y)) : ℝ) : ℂ) *
          (normHeight F (actAtPlaces F (toInf F b) y) : ℂ) ^ a := by
      funext y
      dsimp only [residual, te, ts, eisTerm, seedTerm]
      rw [hact]
      let t := normHeight F (actAtPlaces F (toInf F b) y)
      change (t : ℂ) ^ a - (τ t : ℂ) * (t : ℂ) ^ a =
        ((1 - τ t : ℝ) : ℂ) * (t : ℂ) ^ a
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul]
    have h := hResidual (toInf F b) x
    exact ⟨(congrArg (fun f : X F → ℂ => ‖f x‖) hEq).le.trans h.1,
      (congrArg (fun f : X F → ℂ => ‖fullGradient F f x‖) hEq).le.trans h.2⟩
  have hTriBound (V : Type) [NormedAddCommGroup V] (f : Tri → V)
      (hf : ∀ q, ‖f q‖ ≤ B) : ‖∑' q : Tri, f q‖ ≤ B := by
    by_cases h : Nonempty Tri
    · obtain ⟨q₀⟩ := h
      have heq : (∑' q : Tri, f q) = f q₀ :=
        tsum_eq_single q₀ (fun q hq => (hq (Subsingleton.elim q q₀)).elim)
      rw [heq]
      exact hf q₀
    · have hzero : f = 0 := funext fun q => (h ⟨q⟩).elim
      rw [hzero]
      change ‖∑' q : Tri, (0 : V)‖ ≤ B
      simpa only [tsum_zero, norm_zero] using hB
  let C : ℝ := B + (CE + CS)
  have hC : 0 ≤ C := add_nonneg hB (add_nonneg hCE hCS)
  refine ⟨C, hC, ?_⟩
  intro z hz
  let x : X F := (d.σ i) • z
  obtain ⟨hNEv, hNEg, hNEvBound, hNEgBound⟩ := hNonE z hz
  obtain ⟨hNSv, hNSg, hNSvBound, hNSgBound⟩ := hNonS z hz
  let σ₀ : ℝ := (1 / 2 + s.re) / 2
  have hσ₀ : 1 / 2 < σ₀ := by dsimp [σ₀]; linarith only [hhalf]
  have hσ₀le : σ₀ ≤ s.re := by dsimp [σ₀]; linarith only [hhalf]
  obtain ⟨m, hm, hmBound⟩ := (E2_eis_converge (F := F) Γ σ).1
    {x} isCompact_singleton σ₀ s.re hσ₀
  have hESum : Summable (fun q : CuspCosets F Γ σ => te q x) :=
    Summable.of_norm_bounded hm (hmBound x (Set.mem_singleton x) s hσ₀le le_rfl)
  have hSSum : Summable (fun q : CuspCosets F Γ σ => ts q x) :=
    summable_of_hasFiniteSupport (hE5.1 s x).1
  have hResSum : Summable (fun q : CuspCosets F Γ σ => residual q x) := hESum.sub hSSum
  have hEGrad := specIdentify_eis_gradient_tsum Γ σ s hhalf x
  have hSGrad : Summable (fun q : CuspCosets F Γ σ => fullGradient F (ts q) x) ∧
      fullGradient F (eisSeed F Γ σ τ s) x =
        ∑' q : CuspCosets F Γ σ, fullGradient F (ts q) x := by
    simpa only [one_smul] using specIdentify_seed_gradient_tsum Γ σ 1 τ cut s x
  have hResGradSum : Summable (fun q : CuspCosets F Γ σ => fullGradient F (residual q) x) := by
    simp_rw [hResGrad]
    exact hEGrad.1.sub hSGrad.1
  have hwValue : w x = ∑' q : CuspCosets F Γ σ, residual q x :=
    (hESum.tsum_sub hSSum).symm
  have hwGrad : fullGradient F w x =
      ∑' q : CuspCosets F Γ σ, fullGradient F (residual q) x := by
    rw [hGradSub (eisSeries F Γ σ s) (eisSeed F Γ σ τ s) hE3.1 hSeedSmooth x,
      hEGrad.2, hSGrad.2]
    simp_rw [hResGrad]
    exact (hEGrad.1.tsum_sub hSGrad.1).symm
  have hValueSplit : w x = (∑' q : Tri, residual q.1 x) +
      (∑' q : Nontri, residual q.1 x) := by
    rw [hwValue]
    exact (hResSum.tsum_subtype_add_tsum_subtype_compl {q | tri q}).symm
  have hGradSplit : fullGradient F w x =
      (∑' q : Tri, fullGradient F (residual q.1) x) +
      (∑' q : Nontri, fullGradient F (residual q.1) x) := by
    rw [hwGrad]
    exact (hResGradSum.tsum_subtype_add_tsum_subtype_compl {q | tri q}).symm
  have hTriV : ‖∑' q : Tri, residual q.1 x‖ ≤ B :=
    hTriBound ℂ (fun q => residual q.1 x) (fun q => (hResBound q.1 x).1)
  have hTriG : ‖∑' q : Tri, fullGradient F (residual q.1) x‖ ≤ B :=
    hTriBound (GradientField F) (fun q => fullGradient F (residual q.1) x)
      (fun q => (hResBound q.1 x).2)
  have hNonV : ‖∑' q : Nontri, residual q.1 x‖ ≤ CE + CS := by
    change ‖∑' q : Nontri, (te q.1 x - ts q.1 x)‖ ≤ CE + CS
    rw [hNEv.tsum_sub hNSv]
    exact (norm_sub_le _ _).trans (add_le_add hNEvBound hNSvBound)
  have hNonG : ‖∑' q : Nontri, fullGradient F (residual q.1) x‖ ≤ CE + CS := by
    simp_rw [hResGrad]
    rw [hNEg.tsum_sub hNSg]
    exact (norm_sub_le _ _).trans (add_le_add hNEgBound hNSgBound)
  have hValueBound : ‖w x‖ ≤ C := by
    rw [hValueSplit]
    exact (norm_add_le _ _).trans (add_le_add hTriV hNonV)
  have hGradBound : ‖fullGradient F w x‖ ≤ C := by
    rw [hGradSplit]
    exact (norm_add_le _ _).trans (add_le_add hTriG hNonG)
  refine ⟨hValueBound, ?_⟩
  change ‖fullGradient F (fun y => w (actAtPlaces F (toInf F (d.σ i)) y)) z‖ ≤ C
  exact (specIdentify_gradient_norm_isometry (toInf F (d.σ i)) w hSmooth z).le.trans hGradBound

private theorem specIdentify_global_bound
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (τ : ℝ → ℝ) (cut : CutoffData F Γ σ τ)
    (s : ℂ) (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2)) :
    let w := fun z => eisSeries F Γ σ s z - eisSeed F Γ σ τ s z
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖w z‖ ≤ B ∧ ‖fullGradient F w z‖ ≤ B := by
  classical
  let w : X F → ℂ := fun z => eisSeries F Γ σ s z - eisSeed F Γ σ τ s z
  have hdist : ‖s - (5 / 2 : ℂ)‖ < 1 / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hs
  have hRe : |s.re - (5 / 2 : ℝ)| < 1 / 2 := by
    have h := Complex.abs_re_le_norm (s - (5 / 2 : ℂ))
    have heq : (s - (5 / 2 : ℂ)).re = s.re - (5 / 2 : ℝ) := by norm_num
    rw [heq] at h
    exact h.trans_lt hdist
  have hhalf : 1 / 2 < s.re := by
    have hlo := (abs_lt.mp hRe).1
    linarith only [hlo]
  have hE3 := E3_eis_smooth Γ σ s hhalf
  have hE5 := E5_seed Γ D hD σ cut.A₀ cut.A cut.A₀_ge cut.A_ge
    cut.separation τ cut.cutoff
  have hSmooth : IsSmoothX F w := by
    have hsmE : ContDiffOn ℝ ∞ (fun p => eisSeries F Γ σ s (ptX F p)) (posSet F) := hE3.1
    have hsmS : ContDiffOn ℝ ∞ (fun p => eisSeed F Γ σ τ s (ptX F p)) (posSet F) :=
      (hE5.2.1 s).1
    exact hsmE.sub hsmS
  have hInv : IsGammaInvariant F Γ w := by
    intro γ hγ z
    change eisSeries F Γ σ s (γ • z) - eisSeed F Γ σ τ s (γ • z) =
      eisSeries F Γ σ s z - eisSeed F Γ σ τ s z
    rw [(E2_eis_converge Γ σ).2.1 s hhalf γ hγ z, (hE5.2.1 s).2.1 γ hγ z]
  let d : SiegelData F Γ := Classical.choice (spec_exists_siegelData Γ)
  letI : Fintype d.ι := d.fintype
  have hBounds : ∀ i : d.ι, ∃ B : ℝ, 0 ≤ B ∧
      ∀ z ∈ SiegelData.setAt F d i, ‖w ((d.σ i) • z)‖ ≤ B ∧
        ‖fullGradient F (fun x => w ((d.σ i) • x)) z‖ ≤ B :=
    fun i => specIdentify_cusp_bound Γ D hD σ τ cut s hs d i
  choose B hB hCusp using hBounds
  refine ⟨∑ i : d.ι, B i, Finset.sum_nonneg (fun i _ => hB i), ?_⟩
  intro x
  obtain ⟨i, γ, hy⟩ := R8_siegel_cover Γ d x
  let y : X F := (d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • x)
  have hact : (d.σ i) • y = (γ : SL(2,𝓞 F)) • x :=
    smul_inv_smul (d.σ i) ((γ : SL(2,𝓞 F)) • x)
  obtain ⟨hValue, hGrad⟩ := hCusp i y hy
  have hGradAt : ‖fullGradient F w ((d.σ i) • y)‖ ≤ B i := by
    calc
      ‖fullGradient F w ((d.σ i) • y)‖ =
          ‖fullGradient F (fun z => w ((d.σ i) • z)) y‖ :=
        (specIdentify_gradient_norm_isometry (toInf F (d.σ i)) w hSmooth y).symm
      _ ≤ B i := hGrad
  have hComp : (fun z => w ((γ : SL(2,𝓞 F)) • z)) = w :=
    funext (fun z => hInv γ γ.property z)
  have hIso := specIdentify_gradient_norm_isometry
    (toInf F (toSLF F (γ : SL(2,𝓞 F)))) w hSmooth x
  change ‖fullGradient F (fun z => w ((γ : SL(2,𝓞 F)) • z)) x‖ =
    ‖fullGradient F w ((γ : SL(2,𝓞 F)) • x)‖ at hIso
  rw [hComp] at hIso
  rw [hact, hInv γ γ.property x] at hValue
  rw [hact, ← hIso] at hGradAt
  have hBi : B i ≤ ∑ j : d.ι, B j :=
    Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
  exact ⟨hValue.trans hBi, hGradAt.trans hBi⟩

set_option maxHeartbeats 1000000 in
private theorem specIdentify_test_weak_identity
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (w : X F → ℂ) (hw : IsSmoothX F w) (hinv : IsGammaInvariant F Γ w)
    (x : E.V) (g : L2Space F D) (lam : ℂ)
    (hM : ∀ᵐ z ∂(volX F), z ∈ D → E.M x z = w z)
    (hGr : ∀ᵐ z ∂(volX F), z ∈ D → E.Gr x z = fullGradient F w z)
    (hPDE : ∀ᵐ z ∂(volX F), z ∈ D →
      totalLap F w z - lam * w z = g z)
    (t : testSubmodule F Γ) :
    inner ℂ (e.gradL2 t) (E.Gr x) - lam * inner ℂ (e.toL2 t) (E.M x) =
      inner ℂ (e.toL2 t) g := by
  classical
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX
  let μ : Measure (X F) := (volX F).restrict D
  let f : X F → ℂ := t
  have hf : IsGammaTest F Γ f := ((T2_tests Γ D hD).1 f).mp t.property
  have htf : ∀ᵐ z ∂μ, e.toL2 t z = f z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 (e.mass_rep t)
  have htg : ∀ᵐ z ∂μ, e.gradL2 t z = fullGradient F f z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 (e.gradient_rep t)
  have hMx : ∀ᵐ z ∂μ, E.M x z = w z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 hM
  have hGx : ∀ᵐ z ∂μ, E.Gr x z = fullGradient F w z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 hGr
  have hPDEμ : ∀ᵐ z ∂μ, totalLap F w z - lam * w z = g z :=
    (ae_restrict_iff'₀ hD.nullMeasurableSet).2 hPDE
  have hFullInner (z : X F) :
      inner ℂ (fullGradient F f z) (fullGradient F w z) =
        ∑ v : InfinitePlace F, placeGradInner F v f w z := by
    simp only [fullGradient, PiLp.inner_apply, Fintype.sum_prod_type,
      RCLike.inner_apply', placeGradInner]
    rfl
  have hMassAE : (fun z => inner ℂ (e.toL2 t z) (E.M x z)) =ᵐ[μ]
      (fun z => star (f z) * w z) := by
    filter_upwards [htf, hMx] with z hzf hzw
    rw [hzf, hzw, RCLike.inner_apply']
    rfl
  have hSourceAE : (fun z => inner ℂ (e.toL2 t z) (g z)) =ᵐ[μ]
      (fun z => star (f z) * g z) := by
    filter_upwards [htf] with z hzf
    rw [hzf, RCLike.inner_apply']
    rfl
  have hGradAE : (fun z => inner ℂ (e.gradL2 t z) (E.Gr x z)) =ᵐ[μ]
      (fun z => ∑ v : InfinitePlace F, placeGradInner F v f w z) := by
    filter_upwards [htg, hGx] with z hzf hzw
    rw [hzf, hzw, hFullInner]
  have hMassInt : Integrable (fun z => star (f z) * w z) μ :=
    (L2.integrable_inner (e.toL2 t) (E.M x)).congr hMassAE
  have hSourceInt : Integrable (fun z => star (f z) * g z) μ :=
    (L2.integrable_inner (e.toL2 t) g).congr hSourceAE
  have hMassEq : inner ℂ (e.toL2 t) (E.M x) =
      ∫ z, star (f z) * w z ∂μ := by
    rw [L2.inner_def]
    exact integral_congr_ae hMassAE
  have hSourceEq : inner ℂ (e.toL2 t) g =
      ∫ z, star (f z) * g z ∂μ := by
    rw [L2.inner_def]
    exact integral_congr_ae hSourceAE
  have hGradEq : inner ℂ (e.gradL2 t) (E.Gr x) =
      ∫ z, (∑ v : InfinitePlace F, placeGradInner F v f w z) ∂μ := by
    rw [L2.inner_def]
    exact integral_congr_ae hGradAE
  rcases hf.2.2 with ⟨K, hK, hsupport⟩
  have hLapInt (v : InfinitePlace F) :
      Integrable (fun z => star (f z) * partialLap F v w z) μ := by
    have hcont : Continuous (fun z => star (f z) * partialLap F v w z) :=
      (Complex.continuous_conj.comp (sgSmoothX_continuous f hf.2.1)).mul
        (sgPartialLap_continuous w hw v)
    have hInvariant : IsGammaInvariant F Γ
        (fun z => star (f z) * partialLap F v w z) := by
      intro γ hγ z
      change star (f ((γ : SL(2,𝓞 F)) • z)) *
        partialLap F v w ((γ : SL(2,𝓞 F)) • z) = star (f z) * partialLap F v w z
      rw [hf.1 γ hγ z, sgPartialLap_invariant ⟨γ, hγ⟩ w hw hinv v z]
    apply sgIntegrable_of_compactOrbitSupport D hD _ hcont hInvariant
      hcont.aestronglyMeasurable K hK
    intro z hz
    apply hsupport
    intro hfz
    apply hz
    simp only [hfz, star_zero, zero_mul]
  have hDomInt : Integrable
      (fun z => 3 * (‖e.gradL2 t z‖ ^ 2 + ‖E.Gr x z‖ ^ 2)) μ :=
    ((specGapLpTwo_integrable_norm_sq μ (e.gradL2 t)).add
      (specGapLpTwo_integrable_norm_sq μ (E.Gr x))).const_mul 3
  have hGradInt (v : InfinitePlace F) : Integrable (placeGradInner F v f w) μ := by
    apply hDomInt.mono'
      (sgPlaceGradInner_continuous f w hf.2.1 hw v).aestronglyMeasurable
    filter_upwards [htg, hGx] with z hzf hzw
    rw [hzf, hzw]
    calc
      ‖placeGradInner F v f w z‖ ≤
          ∑ j : Fin 3, ‖star (placeGradient F v f z j) * placeGradient F v w z j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, (‖fullGradient F f z‖ ^ 2 + ‖fullGradient F w z‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_star]
        have ha : ‖placeGradient F v f z j‖ ≤ ‖fullGradient F f z‖ :=
          PiLp.norm_apply_le (fullGradient F f z) (v, j)
        have hb : ‖placeGradient F v w z j‖ ≤ ‖fullGradient F w z‖ :=
          PiLp.norm_apply_le (fullGradient F w z) (v, j)
        have hprod := mul_le_mul ha hb (norm_nonneg _) (norm_nonneg _)
        have hYoung : ‖fullGradient F f z‖ * ‖fullGradient F w z‖ ≤
            ‖fullGradient F f z‖ ^ 2 + ‖fullGradient F w z‖ ^ 2 := by
          nlinarith only [sq_nonneg (‖fullGradient F f z‖ - ‖fullGradient F w z‖),
            sq_nonneg ‖fullGradient F f z‖, sq_nonneg ‖fullGradient F w z‖]
        exact hprod.trans hYoung
      _ = 3 * (‖fullGradient F f z‖ ^ 2 + ‖fullGradient F w z‖ ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_ofNat]
  have hGreen : (∫ z, star (f z) * totalLap F w z ∂μ) =
      ∫ z, (∑ v : InfinitePlace F, placeGradInner F v f w z) ∂μ := by
    calc
      (∫ z, star (f z) * totalLap F w z ∂μ) =
          ∫ z, (∑ v : InfinitePlace F, star (f z) * partialLap F v w z) ∂μ := by
        simp only [totalLap, Finset.mul_sum]
      _ = ∑ v : InfinitePlace F, ∫ z, star (f z) * partialLap F v w z ∂μ :=
        integral_finset_sum _ (fun v _ => hLapInt v)
      _ = ∑ v : InfinitePlace F, ∫ z, placeGradInner F v f w z ∂μ := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (T3_green_q Γ D hD).1 f t.property w hinv hw v
      _ = ∫ z, (∑ v : InfinitePlace F, placeGradInner F v f w z) ∂μ :=
        (integral_finset_sum _ (fun v _ => hGradInt v)).symm
  have hPDEIntegral : (∫ z, star (f z) * totalLap F w z ∂μ) =
      (∫ z, star (f z) * g z ∂μ) + lam * (∫ z, star (f z) * w z ∂μ) := by
    have hEq : (fun z => star (f z) * totalLap F w z) =ᵐ[μ]
        (fun z => star (f z) * g z + lam * (star (f z) * w z)) := by
      filter_upwards [hPDEμ] with z hz
      have h := sub_eq_iff_eq_add.mp hz
      rw [h]
      ring
    rw [integral_congr_ae hEq, integral_add hSourceInt (hMassInt.const_mul lam),
      integral_const_mul]
  rw [hGradEq, ← hGreen, hPDEIntegral, hMassEq, hSourceEq]
  ring

set_option maxHeartbeats 1000000 in
private theorem specIdentify_weak_resolvent
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (w : X F → ℂ) (hw : IsSmoothX F w) (hinv : IsGammaInvariant F Γ w)
    (x : E.V) (g : L2Space F D) (lam : ℂ)
    (hlam : ¬ (lam.im = 0 ∧ 0 ≤ lam.re))
    (hM : ∀ᵐ z ∂(volX F), z ∈ D → E.M x z = w z)
    (hGr : ∀ᵐ z ∂(volX F), z ∈ D → E.Gr x z = fullGradient F w z)
    (hPDE : ∀ᵐ z ∂(volX F), z ∈ D →
      totalLap F w z - lam * w z = g z) :
    E.M x = faResolvent E lam g := by
  classical
  let pt : testSubmodule F Γ → E.V := fun t =>
    ⟨energyGraphMap e.toL2 e.gradL2 t, by
      rw [e.graph_eq]
      change energyGraphMap e.toL2 e.gradL2 t ∈
        closure (energyGraphMap e.toL2 e.gradL2).range
      exact subset_closure ⟨t, rfl⟩⟩
  have hptM (t : testSubmodule F Γ) : E.M (pt t) = e.toL2 t := rfl
  have hptGr (t : testSubmodule F Γ) : E.Gr (pt t) = e.gradL2 t := rfl
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
    change dist (y : WithLp 2 (L2Space F D × GradientL2Space F D))
      (energyGraphMap e.toL2 e.gradL2 t) < ε
    exact hvdist
  let u : E.V := E.A lam x - E.M.adjoint g
  have hzeroOn (t : testSubmodule F Γ) : inner ℂ (pt t) u = 0 := by
    change inner ℂ (pt t) (E.A lam x - E.M.adjoint g) = 0
    rw [inner_sub_right, faA_inner_polarized E lam (pt t) x,
      E.M.adjoint_inner_right (pt t) g]
    apply sub_eq_zero.mpr
    rw [hptGr t, hptM t]
    exact specIdentify_test_weak_identity Γ D hD E e w hw hinv x g lam hM hGr hPDE t
  let Z : Set E.V := {v | inner ℂ v u = 0}
  have hZclosed : IsClosed Z := by
    change IsClosed ((fun v : E.V => inner ℂ v u) ⁻¹' ({0} : Set ℂ))
    exact isClosed_singleton.preimage <| continuous_inner.comp
      ((continuous_id : Continuous fun v : E.V => v).prodMk continuous_const)
  have hRange : Set.range pt ⊆ Z := by
    rintro _ ⟨t, rfl⟩
    exact hzeroOn t
  have hself : inner ℂ u u = 0 :=
    (hZclosed.closure_subset_iff.mpr hRange) (hDense u)
  have hu : u = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp hself
  have hAx : E.A lam x = E.M.adjoint g := sub_eq_zero.mp hu
  have hUnit : IsUnit (E.A lam) := faA_off_cut_isUnit E lam hlam
  have hinverse : faInverse E lam (E.A lam x) = x := by
    rw [faInverse_eq_ringInverse E lam hUnit]
    exact congrArg (fun T : E.V →L[ℂ] E.V => T x)
      (Ring.inverse_mul_cancel (E.A lam) hUnit)
  change E.M x = E.M (faInverse E lam (E.M.adjoint g))
  rw [← hAx, hinverse]

/-- E6 `spec:identify` — P-SPEC.md:242, 397–400. On the convergence ball, the series minus its
cutoff seed is bounded with bounded gradient, lies in the energy graph, and solves the weak
resolvent equation with source equal to the negative seed defect. Correction from `sol-gate-spec`:
require a genuine separated cusp cutoff and calibrated energy representatives. -/
theorem E6_identify (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (τ : ℝ → ℝ) (cut : CutoffData F Γ σ τ) (s : ℂ)
    (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (gL2 : L2Space F D)
    (hg : ∀ᵐ z ∂(volX F), z ∈ D →
      gL2 z = eisSeedDefect F Γ σ τ s z) :
    let w := fun z => eisSeries F Γ σ s z - eisSeed F Γ σ τ s z
    (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖w z‖ ≤ B ∧ ‖fullGradient F w z‖ ≤ B) ∧
    (∃ x : E.V, (∀ᵐ z ∂(volX F), z ∈ D → E.M x z = w z) ∧
      (∀ᵐ z ∂(volX F), z ∈ D → E.Gr x z = fullGradient F w z) ∧
      E.M x = faResolvent E (spectralParameter F s) (-gL2)) := by
  sorry

/-- The compact energy error and strict Fredholm threshold used by E7. The `sol-gate-spec`
correction makes the compact coercivity input and its center threshold explicit. -/
structure SpectralGapData {D : Set (X F)}
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D)) (s₁ : ℝ) where
  K : E.V →L[ℂ] L2Space F D
  compact : IsCompactOperator K
  c : ℝ
  C : ℝ
  c_pos : 0 < c
  C_nonneg : 0 ≤ C
  estimate : ∀ x : E.V, ‖E.M x‖ ^ 2 ≤ c * ‖E.Gr x‖ ^ 2 + C * ‖K x‖ ^ 2
  below : placeCount F * (1 - 4 * s₁ ^ 2) < 1 / c

private def specContinuousLinearSandwich {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (L : A →L[ℂ] B) (R : B →L[ℂ] A) :
    (A →L[ℂ] A) →L[ℂ] (B →L[ℂ] B) :=
  (ContinuousLinearMap.compL ℂ B A B L).comp
    ((ContinuousLinearMap.compL ℂ B A A).flip R)

set_option maxHeartbeats 1000000

/-- E7 `spec:l2-cont` — P-SPEC.md:243, 402–404. The correction is analytic on the connected
continuation domain and has a simple pole at `s₁` with the stated projected-resolvent residue.
Correction from `sol-gate-spec`: use the actual seed-defect source, calibrated energy graph, and
compact Fredholm estimate below the center. -/
theorem E7_l2_cont (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (s₁ : ℝ) (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1 / 2)
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E) (gap : SpectralGapData E s₁)
    (G : ℂ → L2Space F D) (hG : AnalyticOnNhd ℂ G Set.univ)
    (τ : ℝ → ℝ) (cut : CutoffData F Γ σ τ)
    (hsource : ∀ s, ∀ᵐ z ∂(volX F), z ∈ D →
      G s z = eisSeedDefect F Γ σ τ s z)
    (lam₁ : ℝ)
    (hLam1 : lam₁ = placeCount F * (1 - 4 * s₁ ^ 2))
    (P : E.V →L[ℂ] E.V) (N : Submodule ℂ E.V)
    (hP : P.range = N ∧ P.comp P = P ∧ IsSelfAdjoint P ∧
      N = (E.A (lam₁ : ℂ)).toLinearMap.ker)
    (κ : ℝ) (hκ : κ = (lam₁ + 1) / (8 * placeCount F * s₁)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ s₁ ∧
      let u : ℂ → L2Space F D := fun s =>
        faResolvent E (spectralParameter F s) (-G s)
      let θ : L2Space F D := -κ • (E.M.comp (P.comp E.M.adjoint)) (G (s₁ : ℂ))
      AnalyticOnNhd ℂ u (contDomain s₁ ε) ∧
      (∃ Ψ : ℂ → L2Space F D,
        AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) ∧ Ψ (s₁ : ℂ) = θ ∧
        ∀ s ∈ Metric.ball (s₁ : ℂ) ε, s ≠ s₁ → Ψ s = (s - s₁) • u s) ∧
      ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
        ∀ᵐ z ∂(volX F), z ∈ D →
          l2Lift F Γ D (u s) z =
            eisSeries F Γ σ s z - eisSeed F Γ σ τ s z := by
  classical
  have hr : 0 < placeCount F := by
    unfold placeCount
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (InfinitePlace F)))
  have hsprod : 0 ≤ (1 / 2 - s₁) * (1 / 2 + s₁) :=
    mul_nonneg (by linarith) (by linarith)
  have hbase : 0 ≤ 1 - 4 * s₁ ^ 2 := by nlinarith [hsprod]
  have hlam₁_nonneg : 0 ≤ lam₁ := by
    rw [hLam1]
    exact mul_nonneg hr.le hbase
  have hlam₁_lt : lam₁ < 1 / gap.c := by
    rw [hLam1]
    exact gap.below
  have hF := F2_resolvent E gap.K gap.compact gap.c gap.C
    gap.c_pos gap.C_nonneg gap.estimate
  have hOff := hF.2.2.1
  have hInvAnalytic := hF.2.2.2.1
  have hlocal := hF.2.2.2.2.1 lam₁ hlam₁_nonneg hlam₁_lt
  rcases hlocal with ⟨_, _, hlocalP⟩
  rcases hlocalP with ⟨P₀, δ, B, hδ, hP₀id, hP₀range, hP₀self, hB, hExpand⟩
  let ε : ℝ := min s₁ (δ / (24 * placeCount F * s₁))
  have hεden : 0 < 24 * placeCount F * s₁ := by positivity
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hs₀ (div_pos hδ hεden)
  have hεle : ε ≤ s₁ := min_le_left _ _
  have hsq_re (z : ℂ) : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  have hsq_im (z : ℂ) : (z ^ 2).im = 2 * z.re * z.im := by
    rw [pow_two, Complex.mul_im]
    ring
  have hinner_re (z : ℂ) :
      (1 - 4 * z ^ 2).re = 1 - 4 * z.re ^ 2 + 4 * z.im ^ 2 := by
    calc
      (1 - 4 * z ^ 2).re = 1 - (4 * z ^ 2).re := by
        rw [Complex.sub_re]
        simp only [Complex.one_re]
      _ = 1 - 4 * (z ^ 2).re := by
        rw [Complex.mul_re]
        norm_num
      _ = 1 - 4 * z.re ^ 2 + 4 * z.im ^ 2 := by rw [hsq_re]; ring
  have hinner_im (z : ℂ) :
      (1 - 4 * z ^ 2).im = -8 * z.re * z.im := by
    calc
      (1 - 4 * z ^ 2).im = -(4 * z ^ 2).im := by
        rw [Complex.sub_im]
        simp only [Complex.one_im, zero_sub]
      _ = -4 * (z ^ 2).im := by
        rw [Complex.mul_im]
        norm_num
      _ = -8 * z.re * z.im := by rw [hsq_im]; ring
  have hparam_re (z : ℂ) :
      (spectralParameter F z).re =
        placeCount F * (1 - 4 * z.re ^ 2 + 4 * z.im ^ 2) := by
    change ((placeCount F : ℂ) * (1 - 4 * z ^ 2)).re = _
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hinner_re]
  have hparam_im (z : ℂ) :
      (spectralParameter F z).im = -8 * placeCount F * z.re * z.im := by
    change ((placeCount F : ℂ) * (1 - 4 * z ^ 2)).im = _
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, hinner_im]
    ring
  have hparamAnalytic : AnalyticOnNhd ℂ (spectralParameter F) Set.univ := by
    intro z hz
    fun_prop [spectralParameter]
  have hstripOff (z : ℂ)
      (hz : z ∈ {s : ℂ | 0 < s.re ∧ s.re < 4 ∧ 0 < s.im ∧ s.im < 1}) :
      ¬ ((spectralParameter F z).im = 0 ∧ 0 ≤ (spectralParameter F z).re) := by
    have hne : (spectralParameter F z).im ≠ 0 := by
      rw [hparam_im]
      have hre : z.re ≠ 0 := ne_of_gt hz.1
      have him : z.im ≠ 0 := ne_of_gt hz.2.2.1
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hr)) hre) him
    exact fun h => hne h.1
  have hconvOff (z : ℂ)
      (hz : z ∈ Metric.ball (5 / 2 : ℂ) (1 / 2)) :
      ¬ ((spectralParameter F z).im = 0 ∧ 0 ≤ (spectralParameter F z).re) := by
    have hdist : ‖z - (5 / 2 : ℂ)‖ < 1 / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hreabs : |z.re - (5 / 2 : ℝ)| < 1 / 2 := by
      have h := Complex.abs_re_le_norm (z - (5 / 2 : ℂ))
      have hre : (z - (5 / 2 : ℂ)).re = z.re - (5 / 2 : ℝ) := by simp
      rw [hre] at h
      exact lt_of_le_of_lt h hdist
    have himabs : |z.im| < 1 / 2 := by
      have h := Complex.abs_im_le_norm (z - (5 / 2 : ℂ))
      have him : (z - (5 / 2 : ℂ)).im = z.im := by simp
      rw [him] at h
      exact lt_of_le_of_lt h hdist
    have hre : 2 < z.re := by
      have h := (abs_lt.mp hreabs).1
      norm_num at h
      linarith
    have himsq : z.im ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      have h := abs_lt.mp himabs
      nlinarith
    have hreal : (spectralParameter F z).re < 0 := by
      rw [hparam_re]
      have hq : 1 - 4 * z.re ^ 2 + 4 * z.im ^ 2 < 0 := by nlinarith
      exact mul_neg_of_pos_of_neg hr hq
    exact fun h => (not_le_of_gt hreal) h.2
  have hfaStrip : AnalyticOnNhd ℂ
      (fun z : ℂ => faInverse E (spectralParameter F z))
      {z : ℂ | 0 < z.re ∧ z.re < 4 ∧ 0 < z.im ∧ z.im < 1} := by
    exact hInvAnalytic.comp (hparamAnalytic.mono (Set.subset_univ _)) (by
      intro z hz
      exact hstripOff z hz)
  have hfaConv : AnalyticOnNhd ℂ
      (fun z : ℂ => faInverse E (spectralParameter F z))
      (Metric.ball (5 / 2 : ℂ) (1 / 2)) := by
    exact hInvAnalytic.comp (hparamAnalytic.mono (Set.subset_univ _)) (by
      intro z hz
      exact hconvOff z hz)
  have hparamCenter : spectralParameter F (s₁ : ℂ) = (lam₁ : ℂ) := by
    rw [hLam1]
    simp [spectralParameter]
    <;> ring
  have hfactor (z : ℂ) :
      (lam₁ : ℂ) - spectralParameter F z =
        4 * (placeCount F : ℂ) * (z - (s₁ : ℂ)) * (z + (s₁ : ℂ)) := by
    rw [← hparamCenter]
    simp [spectralParameter]
    ring
  have hdistToCenter (z : ℂ) (hz : z ∈ Metric.ball (s₁ : ℂ) ε) :
      ‖z - (s₁ : ℂ)‖ < ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hsumNorm (z : ℂ) (hz : z ∈ Metric.ball (s₁ : ℂ) ε) :
      ‖z + (s₁ : ℂ)‖ ≤ 3 * s₁ := by
    have heq : z + (s₁ : ℂ) = (z - (s₁ : ℂ)) + (2 * (s₁ : ℂ)) := by ring
    rw [heq]
    have hnorm2 : ‖(2 * (s₁ : ℂ))‖ = 2 * s₁ := by
      have hcast : (2 * (s₁ : ℂ)) = ((2 * s₁ : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      ‖(z - (s₁ : ℂ)) + 2 * (s₁ : ℂ)‖ ≤
          ‖z - (s₁ : ℂ)‖ + ‖2 * (s₁ : ℂ)‖ := norm_add_le _ _
      _ ≤ ε + 2 * s₁ := add_le_add (le_of_lt (hdistToCenter z hz)) (le_of_eq hnorm2)
      _ ≤ 3 * s₁ := by nlinarith [hεle]
  have himage (z : ℂ) (hz : z ∈ Metric.ball (s₁ : ℂ) ε) :
      spectralParameter F z ∈ Metric.ball (lam₁ : ℂ) δ := by
    have hnormfactor :
        ‖(lam₁ : ℂ) - spectralParameter F z‖ ≤
          12 * placeCount F * s₁ * ε := by
      rw [hfactor]
      have hnorm :
          ‖4 * (placeCount F : ℂ) * (z - (s₁ : ℂ)) * (z + (s₁ : ℂ))‖ =
            4 * placeCount F * ‖z - (s₁ : ℂ)‖ * ‖z + (s₁ : ℂ)‖ := by
        simp [norm_mul, Complex.norm_real, abs_of_pos hr]
        <;> ring
      rw [hnorm]
      calc
        4 * placeCount F * ‖z - (s₁ : ℂ)‖ * ‖z + (s₁ : ℂ)‖ ≤
            4 * placeCount F * ε * (3 * s₁) := by
              gcongr
              · exact le_of_lt (hdistToCenter z hz)
              · exact hsumNorm z hz
        _ = 12 * placeCount F * s₁ * ε := by ring
    have hsmall : 12 * placeCount F * s₁ * ε < δ := by
      have hden : 0 < 24 * placeCount F * s₁ :=
        hεden
      have hε' : ε ≤ δ / (24 * placeCount F * s₁) := min_le_right _ _
      have hmul : 12 * placeCount F * s₁ * ε ≤
          12 * placeCount F * s₁ * (δ / (24 * placeCount F * s₁)) :=
        mul_le_mul_of_nonneg_left hε' (by positivity)
      have hval : 12 * placeCount F * s₁ *
          (δ / (24 * placeCount F * s₁)) = δ / 2 := by
        field_simp [hden.ne']
        ring
      rw [hval] at hmul
      linarith [hδ]
    have hdist : dist (spectralParameter F z) (lam₁ : ℂ) < δ := by
      rw [dist_eq_norm, norm_sub_rev]
      exact lt_of_le_of_lt hnormfactor hsmall
    exact Metric.mem_ball.mpr hdist
  have hsum_ne (z : ℂ) (hz : z ∈ Metric.ball (s₁ : ℂ) ε) :
      z + (s₁ : ℂ) ≠ 0 := by
    intro h
    have hzeq : z = -(s₁ : ℂ) := by
      calc
        z = z + (s₁ : ℂ) - (s₁ : ℂ) := by ring
        _ = -(s₁ : ℂ) := by rw [h]; ring
    have hdist := hdistToCenter z hz
    have hbelow : ‖z - (s₁ : ℂ)‖ < s₁ := lt_of_lt_of_le hdist hεle
    have heq : -(s₁ : ℂ) - (s₁ : ℂ) = ((-2 * s₁ : ℝ) : ℂ) := by push_cast; ring
    have hbelow' : ‖((-2 * s₁ : ℝ) : ℂ)‖ < s₁ := by simpa [hzeq, heq] using hbelow
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : -2 * s₁ ≤ 0)] at hbelow'
    linarith
  have hparam_ne (z : ℂ) (hz : z ∈ Metric.ball (s₁ : ℂ) ε)
      (hne : z ≠ (s₁ : ℂ)) : spectralParameter F z ≠ (lam₁ : ℂ) := by
    intro heq
    have hprodne :
        4 * (placeCount F : ℂ) * (z - (s₁ : ℂ)) * (z + (s₁ : ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · exact mul_ne_zero (by norm_num) (by exact_mod_cast hr.ne')
        · exact sub_ne_zero.mpr hne
      · exact hsum_ne z hz
    apply hprodne
    rw [← hfactor, heq]
    simp
  have hInvPunct : AnalyticOnNhd ℂ (faInverse E)
      (Metric.ball (lam₁ : ℂ) δ \ {(lam₁ : ℂ)}) := by
    intro z hz
    have hzball : z ∈ Metric.ball (lam₁ : ℂ) δ := hz.1
    have hzne : z ≠ (lam₁ : ℂ) := by simpa using hz.2
    have hopen : IsOpen (Metric.ball (lam₁ : ℂ) δ \ {(lam₁ : ℂ)}) :=
      IsOpen.sdiff Metric.isOpen_ball isClosed_singleton
    have heq : faInverse E =ᶠ[𝓝 z] fun w : ℂ =>
        (((lam₁ + 1 : ℝ) : ℂ) * ((lam₁ : ℂ) - w)⁻¹) • P₀ + B w := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact (hExpand w hw.1 (by simpa using hw.2)).2
    have hform : AnalyticAt ℂ (fun w : ℂ =>
        (((lam₁ + 1 : ℝ) : ℂ) * ((lam₁ : ℂ) - w)⁻¹) • P₀ + B w) z := by
      let coeff : ℂ → ℂ := fun w =>
        (((lam₁ + 1 : ℝ) : ℂ) * ((lam₁ : ℂ) - w)⁻¹)
      have hden : (lam₁ : ℂ) - z ≠ 0 := sub_ne_zero.mpr hzne.symm
      have hcoef : AnalyticAt ℂ coeff z := by
        dsimp [coeff]
        fun_prop
      let smulP : ℂ →L[ℂ] (E.V →L[ℂ] E.V) :=
        ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) P₀
      have hsmulMap : AnalyticAt ℂ (fun c : ℂ => smulP c) (coeff z) :=
        ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
          (F := E.V →L[ℂ] E.V) smulP (coeff z)
      have hsmul : AnalyticAt ℂ (fun w : ℂ => coeff w • P₀) z := by
        have h := hsmulMap.comp_of_eq hcoef rfl
        have h' : AnalyticAt ℂ (fun w : ℂ => smulP (coeff w)) z := by
          change AnalyticAt ℂ ((fun c : ℂ => smulP c) ∘ coeff) z
          exact h
        have heq : (fun w : ℂ => smulP (coeff w)) =
            (fun w : ℂ => coeff w • P₀) := by
          funext w
          simp [smulP, ContinuousLinearMap.smulRight_apply,
            ContinuousLinearMap.id_apply]
        rw [heq] at h'
        exact h'
      exact hsmul.add (hB z hzball)
    exact hform.congr heq.symm
  have hfaPunct : AnalyticOnNhd ℂ
      (fun z : ℂ => faInverse E (spectralParameter F z))
      (Metric.ball (s₁ : ℂ) ε \ {(s₁ : ℂ)}) := by
    exact hInvPunct.comp (hparamAnalytic.mono (Set.subset_univ _)) (by
      intro z hz
      exact ⟨himage z hz.1, hparam_ne z hz.1 (by simpa using hz.2)⟩)
  have hfaDomain : AnalyticOnNhd ℂ
      (fun z : ℂ => faInverse E (spectralParameter F z)) (contDomain s₁ ε) := by
    intro z hz
    have hz' : z ∈ ({w : ℂ | 0 < w.re ∧ w.re < 4 ∧ 0 < w.im ∧ w.im < 1} ∪
        Metric.ball (5 / 2 : ℂ) (1 / 2)) ∪
        (Metric.ball (s₁ : ℂ) ε \ {(s₁ : ℂ)}) := by
      simpa [contDomain] using hz
    rcases hz' with hleft | hpunct
    · rcases hleft with hstrip | hconv
      · exact hfaStrip z hstrip
      · exact hfaConv z (by simpa using hconv)
    · exact hfaPunct z hpunct
  let sandwich : (E.V →L[ℂ] E.V) →L[ℂ]
      (L2Space F D →L[ℂ] L2Space F D) :=
    @specContinuousLinearSandwich E.V (L2Space F D)
      (inferInstance) (inferInstance) (inferInstance) (inferInstance) E.M E.M.adjoint
  have hu : AnalyticOnNhd ℂ
      (fun z : ℂ => faResolvent E (spectralParameter F z) (-G z))
      (contDomain s₁ ε) := by
    intro z hz
    have hfa := hfaDomain z hz
    have hmap : AnalyticAt ℂ (fun T : E.V →L[ℂ] E.V => sandwich T)
        (faInverse E (spectralParameter F z)) :=
      ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := E.V →L[ℂ] E.V)
        (F := L2Space F D →L[ℂ] L2Space F D) sandwich
        (faInverse E (spectralParameter F z))
    have hresOp : AnalyticAt ℂ
        (fun w : ℂ => faResolvent E (spectralParameter F w)) z := by
      have hcomp := hmap.comp_of_eq hfa rfl
      have heq : ((fun T : E.V →L[ℂ] E.V => sandwich T) ∘
          (fun w : ℂ => faInverse E (spectralParameter F w))) =
          (fun w : ℂ => faResolvent E (spectralParameter F w)) := by
        funext w
        simp [faResolvent, sandwich, specContinuousLinearSandwich,
          ContinuousLinearMap.compL_apply]
      rw [heq] at hcomp
      exact hcomp
    have hGneg : AnalyticAt ℂ (fun w : ℂ => -G w) z := by
      have hGz := hG z (Set.mem_univ z)
      fun_prop
    have happ : AnalyticAt ℂ
        (fun p : L2Space F D × (L2Space F D →L[ℂ] L2Space F D) =>
          (ContinuousLinearMap.apply ℂ (L2Space F D) p.1) p.2)
        (-G z, faResolvent E (spectralParameter F z)) := by
      let eval : L2Space F D →L[ℂ]
          (L2Space F D →L[ℂ] L2Space F D) →L[ℂ] L2Space F D :=
        ContinuousLinearMap.apply ℂ (L2Space F D)
      exact eval.analyticAt_bilinear (-G z, faResolvent E (spectralParameter F z))
    have hresult := happ.comp₂ hGneg hresOp
    simpa only [ContinuousLinearMap.apply_apply] using hresult
  have hNclosed : IsClosed (N : Set E.V) := by
    rw [hP.2.2.2]
    exact (E.A (lam₁ : ℂ)).isClosed_ker
  letI : CompleteSpace N := hNclosed.completeSpace_coe
  letI : N.HasOrthogonalProjection := inferInstance
  have hprojection_eq_star (Q : E.V →L[ℂ] E.V)
      (hQr : Q.range = N) (hQid : Q.comp Q = Q) (hQs : IsSelfAdjoint Q) :
      Q = N.starProjection := by
    ext x
    have hmem : Q x ∈ N := by
      have hx : Q x ∈ Q.range := ⟨x, rfl⟩
      rw [hQr] at hx
      exact hx
    have hQon (y : E.V) (hy : y ∈ N) : Q y = y := by
      have hy' : y ∈ Q.range := by rw [hQr]; exact hy
      obtain ⟨y', hy'⟩ := hy'
      have hQidApply : Q (Q y') = Q y' := by
        simpa only [ContinuousLinearMap.comp_apply] using
          congrArg (fun T : E.V →L[ℂ] E.V => T y') hQid
      calc
        Q y = Q (Q y') := congrArg Q hy'.symm
        _ = Q y' := hQidApply
        _ = y := hy'
    have horth : ∀ y ∈ N, inner ℂ (x - Q x) y = 0 := by
      intro y hy
      rw [inner_sub_left]
      have hsym : inner ℂ (Q x) y = inner ℂ x (Q y) := by
        simpa only [ContinuousLinearMap.coe_coe] using hQs.isSymmetric x y
      rw [hsym, hQon y hy, sub_self]
    exact congrArg Subtype.val
      (N.eq_starProjection_of_mem_of_inner_eq_zero hmem horth).symm
  have hP_eq_P₀ : P = P₀ := by
    have hP₀range' : P₀.range = N := by
      calc
        P₀.range = (E.A (lam₁ : ℂ)).toLinearMap.ker := hP₀range
        _ = N := hP.2.2.2.symm
    calc
      P = N.starProjection := hprojection_eq_star P hP.1 hP.2.1 hP.2.2.1
      _ = P₀ := (hprojection_eq_star P₀ hP₀range' hP₀id hP₀self).symm
  have hLiftOnD (v : L2Space F D) :
      ∀ᵐ z ∂(volX F), z ∈ D → l2Lift F Γ D v z = v z := by
    letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
    letI : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
    letI : Countable (Fin 2 → 𝓞 F) := inferInstance
    letI : Countable (Fin 2 → Fin 2 → 𝓞 F) := inferInstance
    letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
      change Countable (Fin 2 → Fin 2 → 𝓞 F)
      infer_instance
    letI : Countable (SL(2,𝓞 F)) :=
      (Subtype.val_injective : Function.Injective
        (fun g : SL(2,𝓞 F) => (g : Matrix (Fin 2) (Fin 2) (𝓞 F)))).countable
    letI : Countable Γ :=
      (Subtype.val_injective : Function.Injective
        (fun γ : Γ => (γ : SL(2,𝓞 F)))).countable
    have hnoOverlap : ∀ᵐ z ∂(volX F),
        ∀ γ : Γ, γ ≠ 1 → z ∈ D → (γ : SL(2,𝓞 F)) • z ∉ D := by
      rw [ae_all_iff]
      intro γ
      by_cases hγ : γ = 1
      · filter_upwards [] with z hne hzD
        exact False.elim (hne hγ)
      · have hneInv : γ⁻¹ ≠ (1 : Γ) := by simpa using hγ
        have hdis := hD.aedisjoint (i := γ⁻¹) (j := (1 : Γ)) hneInv
        have hsdiff := hdis.sdiff_ae_eq_right
        filter_upwards [hsdiff] with z hz
        intro hne hzD hγz
        have hzOne : z ∈ (1 : Γ) • D := by
          rw [Set.mem_smul_set_iff_inv_smul_mem]
          simpa using hzD
        have hmem := hz.mpr hzOne
        have hnot := (Set.mem_sdiff z).mp hmem |>.2
        have htranslate : z ∈ (γ⁻¹ : Γ) • D := by
          have hscalar : (((γ⁻¹ : Γ)⁻¹ : Γ) : SL(2,𝓞 F)) =
              (γ : SL(2,𝓞 F)) := by simp
          rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
          change (((γ⁻¹ : Γ)⁻¹ : Γ) : SL(2,𝓞 F)) • z ∈ D
          rw [hscalar]
          exact hγz
        exact hnot htranslate
    filter_upwards [hnoOverlap] with z hzGood hzD
    rw [l2Lift]
    have hterm (γ : Γ) (hγ : γ ≠ 1) :
        (if (γ : SL(2,𝓞 F)) • z ∈ D then
          v ((γ : SL(2,𝓞 F)) • z) else 0) = 0 := by
      have hzγ := hzGood γ hγ hzD
      simp [hzγ]
    rw [tsum_eq_single (1 : Γ) hterm]
    simp [hzD]
  let C₀ : L2Space F D →L[ℂ] L2Space F D := sandwich P
  let C₁ : ℂ → L2Space F D →L[ℂ] L2Space F D := fun z =>
    sandwich (B (spectralParameter F z))
  let a : ℂ → ℂ := fun z =>
    -(((lam₁ + 1 : ℝ) : ℂ) /
      ((4 : ℂ) * (placeCount F : ℂ) * (z + (s₁ : ℂ))))
  let Ψ : ℂ → L2Space F D := fun z =>
    a z • C₀ (G z) - (z - (s₁ : ℂ)) • C₁ z (G z)
  have hBparam : AnalyticOnNhd ℂ (fun z : ℂ => B (spectralParameter F z))
      (Metric.ball (s₁ : ℂ) ε) := by
    exact hB.comp (hparamAnalytic.mono (Set.subset_univ _)) (by
      intro z hz
      exact himage z hz)
  have hC₁analytic : AnalyticOnNhd ℂ C₁ (Metric.ball (s₁ : ℂ) ε) := by
    intro z hz
    change AnalyticAt ℂ (fun w : ℂ => sandwich (B (spectralParameter F w))) z
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := E.V →L[ℂ] E.V)
      (F := L2Space F D →L[ℂ] L2Space F D) sandwich
      (B (spectralParameter F z))).comp_of_eq (hBparam z hz) rfl
  have hC₀G : AnalyticOnNhd ℂ (fun z : ℂ => C₀ (G z))
      (Metric.ball (s₁ : ℂ) ε) := by
    intro z hz
    have hGz := hG z (Set.mem_univ z)
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
      (E := L2Space F D) (F := L2Space F D) C₀ (G z)).comp_of_eq hGz rfl
  have hC₁G : AnalyticOnNhd ℂ (fun z : ℂ => C₁ z (G z))
      (Metric.ball (s₁ : ℂ) ε) := by
    intro z hz
    have hCz := hC₁analytic z hz
    have hGz := hG z (Set.mem_univ z)
    have happ : AnalyticAt ℂ
        (fun p : L2Space F D × (L2Space F D →L[ℂ] L2Space F D) =>
          (ContinuousLinearMap.apply ℂ (L2Space F D) p.1) p.2)
        (G z, C₁ z) := by
      let eval : L2Space F D →L[ℂ]
          (L2Space F D →L[ℂ] L2Space F D) →L[ℂ] L2Space F D :=
        ContinuousLinearMap.apply ℂ (L2Space F D)
      exact eval.analyticAt_bilinear (G z, C₁ z)
    have hresult := happ.comp₂ hGz hCz
    simpa only [ContinuousLinearMap.apply_apply] using hresult
  have haAnalytic : AnalyticOnNhd ℂ a (Metric.ball (s₁ : ℂ) ε) := by
    intro z hz
    have hsum := hsum_ne z hz
    have hden : (4 : ℂ) * (placeCount F : ℂ) * (z + (s₁ : ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (by exact_mod_cast hr.ne')
      · exact hsum
    dsimp [a]
    fun_prop
  have hΨAnalytic : AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) := by
    intro z hz
    have haz := haAnalytic z hz
    have hC₀z := hC₀G z hz
    have hC₁z := hC₁G z hz
    have hterm₁ : AnalyticAt ℂ (fun w : ℂ => a w • C₀ (G w)) z := haz.smul hC₀z
    have hscale₂ : AnalyticAt ℂ (fun w : ℂ => w - (s₁ : ℂ)) z :=
      analyticAt_id.sub analyticAt_const
    have hterm₂ : AnalyticAt ℂ
        (fun w : ℂ => (w - (s₁ : ℂ)) • C₁ w (G w)) z := hscale₂.smul hC₁z
    have hsub := hterm₁.sub hterm₂
    have hfun :
        (fun w : ℂ => a w • C₀ (G w)) -
            (fun w : ℂ => (w - (s₁ : ℂ)) • C₁ w (G w)) =
          (fun w : ℂ => a w • C₀ (G w) - (w - (s₁ : ℂ)) • C₁ w (G w)) := by
      funext w
      rfl
    rw [hfun] at hsub
    exact hsub
  have haCenter : a (s₁ : ℂ) = -(κ : ℂ) := by
    dsimp [a]
    rw [hκ]
    push_cast
    field_simp [hr.ne', hs₀.ne']
    <;> ring
  refine ⟨ε, hε, hεle, ?_, ?_, ?_⟩
  · exact hu
  · refine ⟨Ψ, hΨAnalytic, ?_, ?_⟩
    · dsimp [Ψ]
      simp [haCenter, C₀, sandwich, specContinuousLinearSandwich,
        ContinuousLinearMap.compL_apply] <;> rfl
    · intro z hz hzne
      have hExpz := hExpand (spectralParameter F z) (himage z hz)
        (hparam_ne z hz hzne)
      have hExpz' : faInverse E (spectralParameter F z) =
          (((lam₁ + 1 : ℝ) : ℂ) *
            ((lam₁ : ℂ) - spectralParameter F z)⁻¹) • P +
            B (spectralParameter F z) := by
        rw [hP_eq_P₀]
        exact hExpz.2
      have hscalar : (z - (s₁ : ℂ)) *
          (((lam₁ + 1 : ℝ) : ℂ) *
            ((lam₁ : ℂ) - spectralParameter F z)⁻¹) = -a z := by
        rw [hfactor]
        dsimp [a]
        have hrC : (placeCount F : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
        field_simp [hrC, sub_ne_zero.mpr hzne, hsum_ne z hz]
        <;> ring
      have hres : faResolvent E (spectralParameter F z) (-G z) =
          -((((lam₁ + 1 : ℝ) : ℂ) *
            ((lam₁ : ℂ) - spectralParameter F z)⁻¹)) • C₀ (G z) -
            C₁ z (G z) := by
        rw [faResolvent, hExpz']
        simp [C₀, C₁, sandwich, specContinuousLinearSandwich,
          ContinuousLinearMap.compL_apply, ContinuousLinearMap.map_neg,
          ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
        <;> abel
      change Ψ z = (z - (s₁ : ℂ)) •
        faResolvent E (spectralParameter F z) (-G z)
      dsimp [Ψ]
      rw [hres]
      simp only [smul_sub, smul_smul, mul_neg]
      rw [hscalar]
      simp
  · intro s hs
    have hE6 := E6_identify Γ D hD σ τ cut s hs E e (G s) (hsource s)
    obtain ⟨x, hM, hGr, hRes⟩ := hE6.2
    have hRes' : ∀ᵐ z ∂(volX F), z ∈ D →
        E.M x z = faResolvent E (spectralParameter F s) (-G s) z :=
      MeasureTheory.ae_imp_of_ae_restrict (Lp.ext_iff.mp hRes)
    have hLift := hLiftOnD (faResolvent E (spectralParameter F s) (-G s))
    filter_upwards [hLift, hRes', hM] with z hzL hzR hzM
    intro hzD
    exact (hzL hzD).trans ((hzR hzD).symm.trans (hzM hzD))

end ArtinPrimitiveRoots.A1.Spec
