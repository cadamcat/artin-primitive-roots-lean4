import ArtinPrimitiveRoots.A2.Reflection.Nodes
import ArtinPrimitiveRoots.A1.SLattice
import ArtinPrimitiveRoots.Theta.AnalysisS
import ArtinPrimitiveRoots.A2.ZeroFree.Results

/-!
Producer interfaces consumed by A2 §§4–6. New records name their producing package and TeX
lines. Existing corrected frequency and Hecke continuation records are reused.
-/
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}

-- Use the product measurable structure supplied by Theta.Shared. A second `borel FS`
-- instance makes measures incompatible by definitional equality at the A1 boundary.

/-- Extend a unit-domain function by zero; nonunits must never be given a quotient class. -/
def onUnits {S : SData F CE condη} (f : S.FSˣ → ℂ) (y : S.FS) : ℂ :=
  if h : IsUnit y then f h.unit else 0

def qI (I : Ideal (𝓞 F)) : ℝ := Ideal.absNorm I
def cls {S : SData F CE condη} (y : S.FSˣ) : S.V := QuotientGroup.mk y

/-- Missing exterior ideal operations, prime support, and generators in R.
Consumers: def:rf-digit-sums, def:rf-active, def:rf-frozen-factors, def:po-probe,
def:po-finite-factor, po:finite-poisson-transform, po:poisson-orbits.
Residues below are the actual R/(a), not an arbitrary finite type. -/
structure ExteriorArithmetic (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (Bd : BData S H) (bc : BalancedChoices D S H Bd) where
  one : S.ExtIdeal
  one_val : one.1 = ⊤
  mul : S.ExtIdeal → S.ExtIdeal → S.ExtIdeal
  mul_val : ∀ I J, (mul I J).1 = I.1 * J.1
  pow : S.ExtIdeal → ℕ → S.ExtIdeal
  pow_val : ∀ I n, (pow I n).1 = I.1 ^ n
  ofSqf : S.SqfExtIdeal → S.ExtIdeal
  ofSqf_val : ∀ I, (ofSqf I).1 = I.1
  prime : (v : FinPlace F) → v ∉ S.Sf → S.ExtIdeal
  prime_val : ∀ v hv, (prime v hv).1 = v.asIdeal
  support : S.ExtIdeal → Finset (FinPlace F)
  mem_support : ∀ I v, v ∈ support I ↔ v.asIdeal ∣ I.1
  support_exterior : ∀ I v, v ∈ support I → v ∉ S.Sf
  genR : S.ExtIdeal → S.R
  genR_val : ∀ I, (genR I : F) = (bc.gen I : F)
  residueFinite : ∀ I, Fintype (S.R ⧸ Ideal.span {genR I})
  residue_card : ∀ I, @Fintype.card _ (residueFinite I) = Ideal.absNorm I.1
  /-- The zero-ring residue of the unit ideal has character 1, including its zero element. -/
  unit_character : ∀ x : S.R, chiIdealPow D one.1 (x : F) 1 = 1

abbrev ResidueRing {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
    {Bd : BData S H} {bc : BalancedChoices D S H Bd}
    (E : ExteriorArithmetic D S H Bd bc) (I : S.ExtIdeal) :=
  S.R ⧸ Ideal.span {E.genR I}

/-- A1 producer obligation for exterior ideals and residue rings (02:229-283; 04:99-132). -/
theorem exteriorArithmetic_exists (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (Bd : BData S H) (bc : BalancedChoices D S H Bd) :
    Nonempty (ExteriorArithmetic D S H Bd bc) := by
  sorry

/-- Arithmetic integration geometry with the same normalization for V, the probe, and c₀.
Consumers: def:rf-digit-sums, rf:descent, rf:angular-cancellation, rf:forward-unfolding,
rf:reflected-absolute, rf:S-unfolding, def:po-weights, def:po-probe, po:poisson-orbits.
`sheetInt` is the frozen parametrized integral. Its disintegration has a factor π, so our
multiplicative measure is π⁻¹ times the frozen product measure. Quotient measure is induced
by counting measure on Γ; no probability normalization is imposed. -/
structure SheetGeometry (D : FieldData F) (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F) where
  ellU : ℝ → S.FSˣ
  ellU_val : ∀ T (hT : 0 < T), (ellU T : S.FS) = S.ell D T hT
  ellU_norm : ∀ T, 0 < T → S.absS (ellU T : S.FS) = T
  sheet : ℝ → Measure S.FS
  sheet_support : ∀ T, 0 < T → ∀ᵐ y ∂sheet T, IsUnit y ∧ S.absS y = T
  sheetInt_eq : ∀ T, 0 < T → ∀ f : S.FS → ℂ, Integrable f (sheet T) →
    ∫ y, f y ∂sheet T = Theta.sheetInt S μ v0 f T
  mul : Measure S.FS
  mul_eq : mul = (ENNReal.ofReal Real.pi)⁻¹ • Theta.mulHaarS S μ
  disintegrate : ∀ f : S.FS → ℂ, Integrable f mul →
    ∫ y, f y ∂mul = ∫ T in Set.Ioi (0 : ℝ), (∫ y, f y ∂sheet T) / (T : ℂ)
  omega : Set S.FS
  omega_measurable : MeasurableSet omega
  omega_norm : ∀ y ∈ omega, IsUnit y ∧ S.absS y = 1
  omega_partition : ∀ y : S.FSˣ, S.absS (y : S.FS) = 1 →
    ∃! γ : Gamma S, ((S.diagU (γ.1 : Fˣ))⁻¹ * y : S.FSˣ).val ∈ omega
  omega_bounded : ∃ K : Set S.FS, IsCompact K ∧ omega ⊆ K
  /-- Haar invariance transports between norm sheets without an additive norm Jacobian. -/
  sheet_translate : ∀ a : S.FSˣ, ∀ T, 0 < T →
    Measure.map (fun y : S.FS => (a : S.FS) * y) (sheet T) =
      sheet (S.absS (a : S.FS) * T)
  sheet_inversion : ∀ T, 0 < T →
    Measure.map (fun y : S.FS => Ring.inverse y) (sheet T) = sheet T⁻¹
  unitSixFinite : Fintype (UnitSix S)
  classFinite : Fintype S.V
  eps : UnitSix S → S.US
  eps_class : ∀ u, unitSixClass S (eps u) = u

/-- Theta/A1 producer obligation for the sheet normalization and fundamental domain
(03:474-659). -/
theorem sheetGeometry_exists (D : FieldData F) (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F) :
    Nonempty (SheetGeometry D S μ v0) := by
  sorry

/-- Turn the row characters into the frozen admissible `SChar` type, with no new analytic
conclusion assumed. Consumers: def:rf-digit-sums, def:rf-profiles, lem:reflection-theta-representation.
The row decomposition is a field here to avoid importing the unproved `exists_rowUnit` into
these statement definitions through its choice function. -/
structure ReflectionCharacters (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (Bd : BData S H) (bc : BalancedChoices D S H Bd)
    (ϑ : HeckeChar F) where
  eps : UnitSix S → S.US
  eps_class : ∀ u, unitSixClass S (eps u) = u
  L : UnitSix S → SChar S
  L_value : ∀ u y, ((L u).L y : ℂ) = rfSCharacter D S H ϑ (eps u) y
  rowEps : ReflectionRow S → S.US
  rowEps_spec : ∀ r, rowElement S r = rowEps r * bc.gen r.ideal

/-- A1 producer obligation for reflection row characters (02:606-625; 04:51-65). Corrected by
`sol-gate-a2b` and independently by `sol-gate-theta3`: admissibility requires a unitary,
exterior-unramified character with angular type. -/
theorem reflectionCharacters_exists (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (Bd : BData S H) (bc : BalancedChoices D S H Bd)
    (ϑ : HeckeChar F)
    (hunit : ∀ x, ‖((ϑ x : ℂˣ) : ℂ)‖ = 1)
    (houtside : ∀ v, v ∉ S.Sf → ϑ.UnramifiedAt v)
    (hangular : HeckeChar.HasAngularType D ϑ) :
    Nonempty (ReflectionCharacters D S H Bd bc ϑ) := by
  sorry

/-- Pairing descended to sixth-power classes (HilbertData already kills sixth powers).
Consumers: def:rf-profiles and rf:S-unfolding. Existence/descent still needs a proof. -/
structure ClassPairing (D : FieldData F) (S : SData F CE condη) (H : HilbertData F) where
  pair : S.V → S.V → ℂ
  pair_eq : ∀ x y, pair (cls x) (cls y) = D.σ0 (((S.HS H x y : Fˣ) : F))
  unitary : ∀ x y, ‖pair x y‖ = 1

/-- Quotient-descent glue from HilbertData and SData.HS (02:114-132; 04:507-548). -/
theorem classPairing_exists (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) : Nonempty (ClassPairing D S H) := by
  sorry


/-- Reuse the corrected smoothness order already fixed in A1/Analytic.lean and ThetaFamily.T6. -/
abbrev SheetHypCInfinity (δ : ℝ) (f : ℂ → ℂ) : Prop :=
  ArtinPrimitiveRoots.A1.SheetHypC δ f

/-- The corrected FrequencyData stores the S-integer conductor bounds for both twists.
Producer: A1/Characters.lean; TeX 02:285-387, 06:13-30, 74-84. -/
def kummer_Sinteger_conductor_statement (S : SData F CE condη)
    (D : FieldData F) (η : HeckeChar F) (U : FrequencyData S D η) : Prop :=
  IsOfFinOrder η → (∀ v, v ∉ S.Sf → η.UnramifiedAt v) →
    ∃ C : ℝ, 0 < C ∧ ∀ u,
      (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧ (U.kummer u).ConductorDvd m ∧
        qI m ≤ C * U.q u) ∧
      (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧ (η * (U.kummer u)⁻¹).ConductorDvd m ∧
        qI m ≤ C * U.q u)

theorem kummer_Sinteger_conductor_from_data (S : SData F CE condη)
    (D : FieldData F) (η : HeckeChar F) (U : FrequencyData S D η) :
    kummer_Sinteger_conductor_statement S D η U :=
  U.kummer_twist_conductor_bound

/-- The norm and finite-shell facts from the corrected FrequencyData object
(02:285-387; 06:13-30). -/
def frequency_norm_count_statement (S : SData F CE condη)
    (D : FieldData F) (η : HeckeChar F) (U : FrequencyData S D η) : Prop :=
  (∀ u, 1 ≤ U.q u) ∧ U.q U.one = 1 ∧ ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
    {u | T ≤ U.q u ∧ U.q u < 2 * T}.Finite ∧
      ({u | T ≤ U.q u ∧ U.q u < 2 * T}.ncard : ℝ) ≤ C * T

theorem frequency_norm_count_from_data (S : SData F CE condη)
    (D : FieldData F) (η : HeckeChar F) (U : FrequencyData S D η) :
    frequency_norm_count_statement S D η U := by
  refine ⟨U.q_ge_one, U.q_one, ?_⟩
  obtain ⟨C, hC, hcount⟩ := U.dyadic_count
  obtain ⟨C₀, hC₀, hlow, hlowBound⟩ := U.low_shell_bound
  refine ⟨C + C₀, add_pos hC hC₀, ?_⟩
  intro T hT
  by_cases hT₂ : 2 ≤ T
  · obtain ⟨hfinite, hbound⟩ := hcount T hT₂
    refine ⟨hfinite, ?_⟩
    calc
      _ ≤ C * T := hbound
      _ ≤ (C + C₀) * T := by nlinarith [hC₀, hT]
  · have hTlt : T < 2 := lt_of_not_ge hT₂
    have hsubset : {u : U.U | T ≤ U.q u ∧ U.q u < 2 * T} ⊆
        {u : U.U | 1 ≤ U.q u ∧ U.q u < 4} := by
      intro u hu
      exact ⟨le_trans hT hu.1, lt_trans hu.2 (by nlinarith [hTlt])⟩
    refine ⟨hlow.subset hsubset, ?_⟩
    have hcardle := Set.ncard_le_ncard hsubset hlow
    calc
      (Set.ncard {u : U.U | T ≤ U.q u ∧ U.q u < 2 * T} : ℝ) ≤
          Set.ncard {u : U.U | 1 ≤ U.q u ∧ U.q u < 4} := by exact_mod_cast hcardle
      _ ≤ C₀ := hlowBound
      _ ≤ (C + C₀) * T := by nlinarith [hC, hT, hC₀]

/-- Aggregate analytic interface whose nonprincipal values are existing
HeckeLContinuation objects. It is a subtype alias, not a competing continuation structure.
Producer: Hecke/Continuation.lean; TeX 06:37-73 and 413-477. -/
abbrev HeckeAnalysis (F : Type) [Field F] [NumberField F] :=
  {A : (HeckeChar F → ℂ → ℂ) × (ℂ → ℂ) //
    (∀ χ s, 1 < s.re → A.1 χ s = heckeLSeries χ s) ∧
    (∀ χ, IsOfFinOrder χ → χ ≠ 1 →
      ∃ C : HeckeLContinuation χ, C.value = A.1 χ) ∧
    DifferentiableOn ℂ (A.1 1) {s | s ≠ 1} ∧ Differentiable ℂ A.2 ∧
    (∀ s, s ≠ 1 → A.2 s = (s - 1) * A.1 1 s) ∧
    (A.2 1).im = 0 ∧ 0 < (A.2 1).re }

namespace HeckeAnalysis

def L {F : Type} [Field F] [NumberField F] (A : HeckeAnalysis F)
    (χ : HeckeChar F) : ℂ → ℂ := A.1.1 χ

def LS {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (A : HeckeAnalysis F) (S : SData F CE condη)
    (χ : HeckeChar F) (s : ℂ) : ℂ :=
  A.L χ s * ∏ v ∈ S.Sf, (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))

def RS {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (A : HeckeAnalysis F) (S : SData F CE condη) : ℂ :=
  A.1.2 1 * ∏ v ∈ S.Sf, (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹)

end HeckeAnalysis

/-- Hecke producer obligation for the existing per-character continuations and principal
regularization (06:37-73, 139-153, 413-477). -/
theorem heckeAnalysis_exists (F : Type) [Field F] [NumberField F] :
    Nonempty (HeckeAnalysis F) := by
  sorry

end ArtinPrimitiveRoots.A2
