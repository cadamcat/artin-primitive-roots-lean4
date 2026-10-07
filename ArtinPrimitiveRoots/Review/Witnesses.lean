import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.TypeII.Marked
import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.A1.Analytic
import ArtinPrimitiveRoots.Theta.Cover
import ArtinPrimitiveRoots.Theta.LocalWhit
import ArtinPrimitiveRoots.Theta.AnalysisS

/-!
Kernel-checked inhabitance witnesses for the Prop-valued predicates used in part B.
The smooth witness uses Mathlib's `ContDiffBump`; its support is a compact open interval
strictly inside `(1, 2)`.
-/

namespace ArtinPrimitiveRoots.Review

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

end ArtinPrimitiveRoots.Review
