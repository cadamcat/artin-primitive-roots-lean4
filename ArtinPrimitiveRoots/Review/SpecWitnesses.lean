import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.TypeII.Marked
import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.A1.Analytic
import ArtinPrimitiveRoots.Theta.Cover
import ArtinPrimitiveRoots.Theta.LocalWhit
import ArtinPrimitiveRoots.Theta.AnalysisS
import ArtinPrimitiveRoots.Spec.Main

/-!
Kernel-checked inhabitance witnesses for the Prop-valued predicates used in part B.
The smooth witness uses Mathlib's `ContDiffBump`; its support is a compact open interval
strictly inside `(1, 2)`.
-/

namespace ArtinPrimitiveRoots.Review.SpecWitnesses

open NumberField IsDedekindDomain
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Construction

theorem roughAbove_witness : ∃ n : ℕ, ∀ y : ℝ, roughAbove n y := by
  refine ⟨1, ?_⟩
  intro y p hp hdiv
  have hpone : p = 1 := Nat.dvd_one.mp hdiv
  subst p
  exact (Nat.not_prime_one hp).elim
example : ∃ n : ℕ, ∀ y : ℝ, roughAbove n y := roughAbove_witness

theorem validBands_witness : ∃ K : ℕ, ∃ a : Fin K → ℝ, ValidBands K a := by
  refine ⟨1, fun _ => (3 / 20 : ℝ), ?_⟩
  norm_num [ValidBands]
example : ∃ K : ℕ, ∃ a : Fin K → ℝ, ValidBands K a := validBands_witness

theorem markedInvariant_witness : ∃ x : ℝ, ∃ K : ℕ, ∃ a : Fin K → ℝ, ∃ F : ℕ → ℂ,
    IsMarkedInvariant x K a F := by
  refine ⟨2, 1, fun _ => (3 / 20 : ℝ), fun _ => 0, ?_⟩
  constructor
  · intro h
    simp
  · intro p h hp _
    simp
example : ∃ x : ℝ, ∃ K : ℕ, ∃ a : Fin K → ℝ, ∃ F : ℕ → ℂ,
    IsMarkedInvariant x K a F := markedInvariant_witness

theorem groupInteger_witness : ∃ x : ℝ, ∃ K : ℕ, ∃ a : Fin K → ℝ, ∃ r : ℕ,
    IsGroupInteger x K a r := by
  refine ⟨2, 1, fun _ => (3 / 20 : ℝ), 1, ?_⟩
  intro p hp hdiv
  have hpone : p = 1 := Nat.dvd_one.mp hdiv
  subst p
  exact (Nat.not_prime_one hp).elim
example : ∃ x : ℝ, ∃ K : ℕ, ∃ a : Fin K → ℝ, ∃ r : ℕ,
    IsGroupInteger x K a r := groupInteger_witness

noncomputable def witnessBump : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

noncomputable def witnessTestFunction : ℝ → ℝ := witnessBump

theorem testFunction_witness : ∃ Ψ : ℝ → ℝ, IsTestFunction Ψ := by
  refine ⟨witnessTestFunction, ?_⟩
  have hbumpSmooth :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) witnessTestFunction := by
    simpa [witnessTestFunction] using
      (witnessBump.contDiff :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (witnessBump : ℝ → ℝ))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hbumpSmooth
  · intro y hy
    rw [show Function.support witnessTestFunction = Metric.ball (3 / 2 : ℝ) (1 / 4 : ℝ) by
      simpa [witnessTestFunction, witnessBump] using witnessBump.support_eq] at hy
    have hy' : |y - (3 / 2 : ℝ)| < 1 / 4 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hy
    rcases abs_lt.mp hy' with ⟨hlo, hhi⟩
    constructor <;> nlinarith
  · intro y
    exact witnessBump.nonneg
  · intro y
    exact witnessBump.le_one
  · apply intervalIntegral.integral_pos
    · norm_num
    · exact hbumpSmooth.continuous.continuousOn
    · intro y hy
      exact witnessBump.nonneg
    · refine ⟨(3 / 2 : ℝ), by norm_num, ?_⟩
      have hcenter : (3 / 2 : ℝ) ∈ Metric.closedBall (3 / 2 : ℝ) witnessBump.rIn := by
        simp [Metric.mem_closedBall, witnessBump]
      rw [witnessTestFunction, witnessBump.one_of_mem_closedBall hcenter]
      norm_num
example : ∃ Ψ : ℝ → ℝ, IsTestFunction Ψ := testFunction_witness

noncomputable def zeroCancellationFamily : CoefficientFamily 0 1 1 1 where
  Hm := fun x => x
  Hn := fun _ => 1
  interval := fun _ => ∅
  alpha := fun _ _ => 0
  interval_property := by
    intro x m n k hm hn hmin hmax
    have hfalse : False := by simpa using hm
    exact hfalse.elim
  scales := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by linarith
    simpa [Real.rpow_zero] using
      (show (1 : ℝ) ≤ x ∧ 1 ≤ 1 ∧ x ≤ x ∧ x ≤ x from
        ⟨hx1, le_rfl, le_rfl, le_rfl⟩)
  interval_bounds := by simp
  rough_support := by simp
  coefficient_bound := by simp

theorem longCancellation_witness : ∃ family : CoefficientFamily 0 1 1 1,
    HasLongCoefficientCancellation family := by
  refine ⟨zeroCancellationFamily, ?_⟩
  intro A₀ B A hA₀ hB hA
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  intro x hx k hk hkL χ t ht
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  simp [familyTerms, zeroCancellationFamily]
  positivity
example : ∃ family : CoefficientFamily 0 1 1 1,
    HasLongCoefficientCancellation family := longCancellation_witness

#print axioms roughAbove_witness
#print axioms validBands_witness
#print axioms markedInvariant_witness
#print axioms groupInteger_witness
#print axioms testFunction_witness
#print axioms longCancellation_witness

/-! ## Theta/A1 predicate inhabitance -/

open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1.Spec
open scoped ContDiff MatrixGroups

theorem cyclotomic12_FieldData_witness
    (σ0 : CyclotomicField 12 ℚ →+* ℂ) :
    Nonempty (FieldData (CyclotomicField 12 ℚ)) := by
  exact ⟨cyclotomicFieldData 12 (by norm_num) σ0⟩
example (σ0 : CyclotomicField 12 ℚ →+* ℂ) :
    Nonempty (FieldData (CyclotomicField 12 ℚ)) := cyclotomic12_FieldData_witness σ0

theorem isExterior_top_witness {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη) : S.IsExterior ⊤ := by
  refine ⟨by simp, ?_⟩
  intro v hv hle
  have htop : v.asIdeal = ⊤ := top_le_iff.mp hle
  exact v.isMaximal.ne_top htop
example {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) : S.IsExterior ⊤ := isExterior_top_witness S

theorem isGen_one_top_witness {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη) :
    S.IsGen (1 : F) ⊤ := by
  refine ⟨isExterior_top_witness S, one_ne_zero, ?_⟩
  intro v hv
  rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.coeIdeal_top]
example {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) : S.IsGen (1 : F) ⊤ := isGen_one_top_witness S

theorem isGen_implies_isExterior_witness {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη)
    {c : F} {I : Ideal (𝓞 F)} (h : S.IsGen c I) : S.IsExterior I := h.1
example {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) {c : F} {I : Ideal (𝓞 F)} (h : S.IsGen c I) :
    S.IsExterior I := isGen_implies_isExterior_witness S h

theorem isGen_zero_ideal_impossible {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη) (c : F) :
    ¬ S.IsGen c ⊥ := by
  intro h
  exact h.1.1 rfl

theorem unramified_trivial_character_witness {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) : (1 : HeckeChar F).UnramifiedAt v := by
  intro u hu huv
  simp [HeckeChar.loc]
example {F : Type} [Field F] [NumberField F] (v : FinPlace F) :
    (1 : HeckeChar F).UnramifiedAt v := unramified_trivial_character_witness v

theorem conductor_trivial_character_witness {F : Type} [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) : (1 : HeckeChar F).ConductorDvd 𝔪 := by
  intro v u hu huv hcong
  simp [HeckeChar.loc]
example {F : Type} [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) :
    (1 : HeckeChar F).ConductorDvd 𝔪 := conductor_trivial_character_witness 𝔪

theorem sheetHypFin_zero_witness {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (δ : ℝ) : SheetHypFin v δ (fun _ => 0) := by
  refine ⟨?_, ⟨1, ?_⟩, ⟨0, ?_⟩⟩
  · intro x hx
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ x, ?_⟩
    intro y hy
    rfl
  · intro y hy
    rfl
  · intro y hy hsmall
    simp
example {F : Type} [Field F] [NumberField F] (v : FinPlace F) (δ : ℝ) :
    SheetHypFin v δ (fun _ => 0) := sheetHypFin_zero_witness v δ

theorem sheetHypC_zero_witness (δ : ℝ) : SheetHypC δ (fun _ => 0) := by
  refine ⟨by fun_prop, ?_⟩
  intro j A hA
  refine ⟨0, ?_⟩
  intro y hy
  simp [normDeriv]
example (δ : ℝ) :
    SheetHypC δ (fun _ => 0) := sheetHypC_zero_witness δ

theorem steinbergAt_witness {F : Type} [Field F] [NumberField F]
    {H : HilbertData F} {v : FinPlace F} : SteinbergAt H v := by
  intro a h
  exact H.steinberg v a h
example {F : Type} [Field F] [NumberField F] {H : HilbertData F} {v : FinPlace F} :
    SteinbergAt H v := steinbergAt_witness

theorem isLocUnit_one_witness {F : Type} [Field F] [NumberField F]
    {v : FinPlace F} : IsLocUnit v 1 := by
  constructor <;> simp [IsLocUnit]
example {F : Type} [Field F] [NumberField F] {v : FinPlace F} :
    IsLocUnit v 1 := isLocUnit_one_witness

theorem isSectionC_zero_witness (s : ℂ) : IsSectionC s (fun _ => 0) := by
  intro x y g
  simp
example (s : ℂ) : IsSectionC s (fun _ => 0) := isSectionC_zero_witness s

theorem sheetMultiplier_zero_witness {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη) (L : SChar S) :
    SheetMultiplier S (fun _ => 0) := by
  refine ⟨L, 0, fun _ => 0, ⟨0, ?_⟩, ?_⟩
  · intro x
    simp
  · intro y
    simp
example {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) (L : SChar S) : SheetMultiplier S (fun _ => 0) :=
  sheetMultiplier_zero_witness S L

theorem allowed_one_witness {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F}
    (Bd : BData S H) : Bd.Allowed 1 := by
  simp [BData.Allowed]
example {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    {S : SData F CE condη} {H : HilbertData F} (Bd : BData S H) : Bd.Allowed 1 :=
  allowed_one_witness Bd

/-! ## P-SPEC predicate and structure checks -/

theorem spec_freeAction_witness {F : Type} [Field F] [NumberField F] :
    FreeAction F (⊥ : Subgroup SL(2,𝓞 F)) := by
  intro γ hγ z _
  simpa using hγ

example {F : Type} [Field F] [NumberField F] :
    FreeAction F (⊥ : Subgroup SL(2,𝓞 F)) := spec_freeAction_witness

theorem spec_denominatorBound_witness {F : Type} [Field F] [NumberField F] :
    HasDenominatorBound F 1 (0 : F) := by
  exact ⟨0, by simp⟩

example {F : Type} [Field F] [NumberField F] :
    HasDenominatorBound F 1 (0 : F) := spec_denominatorBound_witness

noncomputable def specCutoffOne : ℝ → ℝ := fun t => Real.smoothTransition (t - 1)

theorem spec_cuspCutoff_witness : IsCuspCutoff 1 specCutoffOne := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (t - 1))
    fun_prop
  · intro x y hxy
    apply Real.smoothTransition.monotone
    linarith
  · intro t ht
    apply Real.smoothTransition.zero_of_nonpos
    linarith
  · intro t ht
    apply Real.smoothTransition.one_of_one_le
    linarith

example : IsCuspCutoff 1 specCutoffOne := spec_cuspCutoff_witness

theorem spec_balancedHeights_witness {F : Type} [Field F] [NumberField F] :
    IsBalancedHeights F 0 (fun _ : InfinitePlace F => 1) := by
  constructor
  · intro w
    norm_num
  · intro w
    simp

example {F : Type} [Field F] [NumberField F] :
    IsBalancedHeights F 0 (fun _ : InfinitePlace F => 1) := spec_balancedHeights_witness

theorem spec_smoothX_zero_witness {F : Type} [Field F] [NumberField F] :
    IsSmoothX F (fun _ : X F => (0 : ℂ)) := by
  unfold IsSmoothX
  fun_prop

theorem spec_smoothRealX_zero_witness {F : Type} [Field F] [NumberField F] :
    IsSmoothRealX F (fun _ : X F => (0 : ℝ)) := by
  unfold IsSmoothRealX
  fun_prop

theorem spec_compactSupportX_zero_witness {F : Type} [Field F] [NumberField F] :
    HasCompactSupportX F (fun _ : X F => (0 : ℂ)) := by
  refine ⟨∅, isCompact_empty, ?_⟩
  intro z hz
  simp at hz

theorem spec_gammaInvariant_zero_witness {F : Type} [Field F] [NumberField F]
    (Γ : Subgroup SL(2,𝓞 F)) : IsGammaInvariant F Γ (fun _ : X F => (0 : ℂ)) := by
  intro γ hγ z
  rfl

theorem spec_compactSupportModulo_zero_witness {F : Type} [Field F] [NumberField F]
    (Γ : Subgroup SL(2,𝓞 F)) :
    HasCompactSupportModulo F Γ (fun _ : X F => (0 : ℂ)) := by
  refine ⟨∅, isCompact_empty, ?_⟩
  intro z hz
  simp at hz

theorem spec_gammaTest_zero_witness {F : Type} [Field F] [NumberField F]
    (Γ : Subgroup SL(2,𝓞 F)) : IsGammaTest F Γ (fun _ : X F => (0 : ℂ)) := by
  exact ⟨spec_gammaInvariant_zero_witness Γ, spec_smoothX_zero_witness,
    spec_compactSupportModulo_zero_witness Γ⟩

theorem spec_unitAssociatedRows_reflexive {F : Type} [Field F] [NumberField F]
    (v : F × F) : unitAssociatedRows F v v := by
  refine ⟨1, ?_⟩
  simp

example {F : Type} [Field F] [NumberField F] (v : F × F) : unitAssociatedRows F v v :=
  spec_unitAssociatedRows_reflexive v

theorem spec_fullLattice_zeroDim_witness :
    ∃ L : Submodule ℤ (Fin 0 → ℝ), IsFullZLattice L := by
  refine ⟨⊤, ?_⟩
  refine ⟨by infer_instance, ?_⟩
  constructor
  simp

noncomputable def spec_zeroEnergySpace : FAEnergySpace ℂ ℂ :=
  { V := energyGraph (0 : ℂ →ₗ[ℂ] ℂ) (0 : ℂ →ₗ[ℂ] ℂ)
    closedV := by
      exact isClosed_closure }

noncomputable def spec_zeroEnergyContext : EnergyContext (T := ℂ) spec_zeroEnergySpace :=
  { toL2 := 0
    gradL2 := 0
    graph_eq := rfl }

example : Nonempty (FAEnergySpace ℂ ℂ) := ⟨spec_zeroEnergySpace⟩

example : Nonempty (EnergyContext (T := ℂ) spec_zeroEnergySpace) :=
  ⟨spec_zeroEnergyContext⟩

theorem spec_S2_zeroKernel_refutation {F : Type} [Field F] [NumberField F]
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) :
    ¬ (∀ s : ℂ, ‖s‖ ≤ 5 →
      0 < (radialTransform₀ (fun _ => 0) (1 + 2 * s)).re) := by
  intro h
  have hh := h 0 (by norm_num)
  have hz : radialTransform₀ (fun _ => 0) (1 + 2 * (0 : ℂ)) = 0 := by
    simp [radialTransform₀]
  rw [hz] at hh
  norm_num at hh

noncomputable def specRootVector : Fin 2 → ℝ := fun i => if i = 0 then Real.exp 1 else Real.exp (-1)

noncomputable def specSquareVector : Fin 2 → ℝ := fun i => (specRootVector i) ^ 2

theorem spec_squareRoot_balance_counterexample :
    (∀ i : Fin 2, |Real.log (specRootVector i) -
      (2 : ℝ)⁻¹ * ∑ j : Fin 2, Real.log (specRootVector j)| ≤ 1) ∧
    ¬ (∀ i : Fin 2, |Real.log (specSquareVector i) -
      (2 : ℝ)⁻¹ * ∑ j : Fin 2, Real.log (specSquareVector j)| ≤ 1) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [specRootVector, Real.log_exp, Fin.sum_univ_two]
  · intro h
    have h0 := h 0
    norm_num [specSquareVector, specRootVector, Real.log_exp, Fin.sum_univ_two] at h0

theorem spec_unsummable_tsum_counterexample :
    (∑' n : ℕ, (1 : ℝ)) = 0 := by
  have hnot : ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
    rw [not_summable_iff_tendsto_nat_atTop_of_nonneg (fun _ => by norm_num)]
    have hsum : (fun n : ℕ => ∑ i ∈ Finset.range n, (1 : ℝ)) = fun n : ℕ => (n : ℝ) := by
      funext n
      simp
    rw [hsum]
    exact tendsto_natCast_atTop_atTop
  exact tsum_eq_zero_of_not_summable hnot

#print axioms isExterior_top_witness
#print axioms cyclotomic12_FieldData_witness
#print axioms isGen_one_top_witness
#print axioms isGen_implies_isExterior_witness
#print axioms isGen_zero_ideal_impossible
#print axioms unramified_trivial_character_witness
#print axioms conductor_trivial_character_witness
#print axioms sheetHypFin_zero_witness
#print axioms sheetHypC_zero_witness
#print axioms steinbergAt_witness
#print axioms isLocUnit_one_witness
#print axioms isSectionC_zero_witness
#print axioms sheetMultiplier_zero_witness
#print axioms allowed_one_witness
#print axioms spec_freeAction_witness
#print axioms spec_denominatorBound_witness
#print axioms spec_cuspCutoff_witness
#print axioms spec_balancedHeights_witness
#print axioms spec_smoothX_zero_witness
#print axioms spec_smoothRealX_zero_witness
#print axioms spec_compactSupportX_zero_witness
#print axioms spec_gammaInvariant_zero_witness
#print axioms spec_compactSupportModulo_zero_witness
#print axioms spec_gammaTest_zero_witness
#print axioms spec_unitAssociatedRows_reflexive
#print axioms spec_fullLattice_zeroDim_witness
#print axioms spec_zeroEnergySpace
#print axioms spec_zeroEnergyContext
#print axioms spec_S2_zeroKernel_refutation
#print axioms spec_squareRoot_balance_counterexample
#print axioms spec_unsummable_tsum_counterexample

end ArtinPrimitiveRoots.Review.SpecWitnesses
