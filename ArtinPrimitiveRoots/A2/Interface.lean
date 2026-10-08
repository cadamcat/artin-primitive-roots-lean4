import ArtinPrimitiveRoots.A2.Reflection.Nodes
import ArtinPrimitiveRoots.A2.Proofs.A2_PRODUCERS.Reflection
import ArtinPrimitiveRoots.A2.Proofs.A2_PRODUCERS.Angles
import ArtinPrimitiveRoots.A2.Proofs.A2_PRODUCERS.Sheet
import ArtinPrimitiveRoots.A1.SLattice
import ArtinPrimitiveRoots.Theta.AnalysisS
import ArtinPrimitiveRoots.A2.ZeroFree.Results
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_residues_exists
import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ResidueUnits

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

private lemma a2p_count_coe_eq_normalizedFactors (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥)
    (v : FinPlace F) :
    FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors J) : ℤ) := by
  have hJ0 : J ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hJ
  rw [FractionalIdeal.count_coe F v hJ0]
  exact_mod_cast (Ideal.count_associates_factors_eq hJ0 v.isPrime v.ne_bot)

private lemma a2p_principal_count_le_of_valuation_le (v : FinPlace F) {a c : F}
    (ha : a ≠ 0) (hc : c ≠ 0) (hval : v.valuation F a ≤ v.valuation F c) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) ≤
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) a) := by
  have hlog : WithZero.log (v.valuation F a) ≤ WithZero.log (v.valuation F c) :=
    (WithZero.log_le_log ((v.valuation F).ne_zero_iff.mpr ha)
      ((v.valuation F).ne_zero_iff.mpr hc)).2 hval
  rw [ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation v c hc,
    ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation v a ha]
  exact neg_le_neg hlog

private lemma a2p_valuation_le_of_principal_count_le (v : FinPlace F) {a c : F}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hcount : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) ≤
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) a)) :
    v.valuation F a ≤ v.valuation F c := by
  have hlog : WithZero.log (v.valuation F a) ≤ WithZero.log (v.valuation F c) := by
    rw [ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation v c hc,
      ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation v a ha] at hcount
    linarith
  exact (WithZero.log_le_log ((v.valuation F).ne_zero_iff.mpr ha)
    ((v.valuation F).ne_zero_iff.mpr hc)).mp hlog

private theorem a2p_ideal_mem_of_valuation_le (S : SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : S.IsExterior I) {c : F}
    (hc : S.IsGen c I) (a : 𝓞 F)
    (hval : ∀ v : FinPlace F, v ∉ S.Sf →
      v.valuation F (a : F) ≤ v.valuation F c) : a ∈ I := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have haF : (a : F) ≠ 0 := by
    intro h
    exact ha0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hspan : Ideal.span {a} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot] using ha0
  have hfactor : UniqueFactorizationMonoid.normalizedFactors I ≤
      UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}) := by
    apply Multiset.le_iff_count.mpr
    intro Q
    by_cases hQ : Q.IsPrime ∧ Q ≠ ⊥
    · let v : FinPlace F := ⟨Q, hQ.1, hQ.2⟩
      by_cases hvS : v ∈ S.Sf
      · have hnot : Q ∉ UniqueFactorizationMonoid.normalizedFactors I := by
          intro hmem
          have hP := (Ideal.mem_normalizedFactors_iff hI.1).mp hmem
          have hle : I ≤ Q := hP.2
          exact hI.2 v hvS (by simpa [v] using hle)
        rw [Multiset.count_eq_zero.mpr hnot]
        exact Nat.zero_le _
      · have hcount : FractionalIdeal.count F v
            (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≤
          FractionalIdeal.count F v
            (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
          calc
            _ = FractionalIdeal.count F v
                (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) :=
                  (hc.2.2 v hvS).symm
            _ ≤ _ := a2p_principal_count_le_of_valuation_le v haF hc.2.1 (hval v hvS)
            _ = FractionalIdeal.count F v
                (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
                  rw [← FractionalIdeal.coeIdeal_span_singleton]
        rw [a2p_count_coe_eq_normalizedFactors I hI.1 v,
          a2p_count_coe_eq_normalizedFactors (Ideal.span {a}) hspan v] at hcount
        exact_mod_cast hcount
    · have hnot : Q ∉ UniqueFactorizationMonoid.normalizedFactors I := by
        intro hmem
        have hP := (Ideal.mem_normalizedFactors_iff hI.1).mp hmem
        have hQ0 : Q ≠ ⊥ := by
          intro hbot
          apply hI.1
          exact bot_unique (by simpa [hbot] using hP.2)
        exact hQ ⟨hP.1, hQ0⟩
      rw [Multiset.count_eq_zero.mpr hnot]
      exact Nat.zero_le _
  have hdiv : I ∣ Ideal.span {a} :=
    (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hI.1 hspan).2 hfactor
  have hle : Ideal.span {a} ≤ I := Ideal.dvd_iff_le.mp hdiv
  exact hle (Ideal.subset_span (by simp))

private theorem a2p_gen_mem_R (S : SData F CE condη) {D : FieldData F}
    {H : HilbertData F} {Bd : BData S H} (bc : BalancedChoices D S H Bd)
    (I : S.ExtIdeal) : ((bc.gen I : Fˣ) : F) ∈ S.R := by
  change ∀ v : FinPlace F, v ∉ S.Sf → v.valuation F ((bc.gen I : Fˣ) : F) ≤ 1
  intro v hv
  have hgen := (bc.gen_spec I).1.2.2 v hv
  have hcount : 0 ≤ FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
        ((bc.gen I : Fˣ) : F)) := by
    rw [hgen]
    exact FractionalIdeal.count_coe_nonneg F v I.1
  have hform := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation v
    ((bc.gen I : Fˣ) : F) (Units.ne_zero (bc.gen I))
  have hlog : WithZero.log
      (v.valuation F ((bc.gen I : Fˣ) : F)) ≤ 0 := by
    linarith
  simpa using WithZero.le_exp_of_log_le hlog

private theorem a2p_map_eq_span_genR (S : SData F CE condη)
    (I : S.ExtIdeal) (cR : S.R) (hc : S.IsGen (cR : F) I.1) :
    Ideal.map (algebraMap (𝓞 F) S.R) I.1 = Ideal.span {cR} := by
  classical
  let M := conductorDenominators S
  letI : IsLocalization M S.R := conductorSInteger_isLocalization S
  have hc0 : (cR : F) ≠ 0 := hc.2.1
  have hunder : (Ideal.span {cR}).under (𝓞 F) = I.1 := by
    ext a
    change algebraMap (𝓞 F) S.R a ∈ Ideal.span {cR} ↔ a ∈ I.1
    constructor
    · intro ha
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp ha
      have hfield : (a : F) = (cR : F) * (r : F) := by
        have h := congrArg (fun x : S.R => (x : F)) hr
        simpa [mul_comm] using h.symm
      apply a2p_ideal_mem_of_valuation_le S hc.1 hc a
      intro v hv
      calc
        v.valuation F (a : F) = v.valuation F ((cR : F) * (r : F)) := by rw [hfield]
        _ = v.valuation F (cR : F) * v.valuation F (r : F) := by rw [map_mul]
        _ ≤ v.valuation F (cR : F) * 1 :=
          mul_le_mul_of_nonneg_left (r.property v hv) (zero_le)
        _ = v.valuation F (cR : F) := by simp
    · intro ha
      by_cases ha0 : a = 0
      · subst a
        simp
      have haF : (a : F) ≠ 0 := by
        intro h
        exact ha0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
      have hspan : Ideal.span {a} ≠ ⊥ := by
        simpa [Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot] using ha0
      have hspanle : Ideal.span {a} ≤ I.1 := Ideal.span_le.mpr (by
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact ha)
      have hspanleF :
          (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≤
            (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
        exact (FractionalIdeal.coeIdeal_le_coeIdeal F).2 hspanle
      have hspanF : (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
        exact FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa only [Ideal.zero_eq_bot] using hspan)
      have hratio : (a : F) / (cR : F) ∈ S.R := by
        change ∀ v : FinPlace F, v ∉ S.Sf →
          v.valuation F ((a : F) / (cR : F)) ≤ 1
        intro v hv
        have hcount : FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (cR : F)) ≤
          FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) := by
          have hspanCount : FractionalIdeal.count F v
              (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
            FractionalIdeal.count F v
              (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
            rw [← FractionalIdeal.coeIdeal_span_singleton]
          calc
            _ = FractionalIdeal.count F v
                (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hc.2.2 v hv
            _ ≤ FractionalIdeal.count F v
                (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
                  FractionalIdeal.count_mono F v hspanF hspanleF
            _ = _ := hspanCount.symm
        have hval := a2p_valuation_le_of_principal_count_le v haF hc0 hcount
        rw [Valuation.map_div]
        exact (div_le_one₀
          (WithZero.pos_iff_ne_zero.mpr ((v.valuation F).ne_zero_iff.mpr hc0))).2 hval
      let r : S.R := ⟨(a : F) / (cR : F), hratio⟩
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨r, ?_⟩
      apply Subtype.ext
      change ((a : F) / (cR : F)) * (cR : F) = (a : F)
      field_simp [hc0]
  calc
    Ideal.map (algebraMap (𝓞 F) S.R) I.1 =
        Ideal.map (algebraMap (𝓞 F) S.R) ((Ideal.span {cR}).under (𝓞 F)) := by rw [hunder]
    _ = Ideal.span {cR} := IsLocalization.map_under M S.R (Ideal.span {cR})

abbrev ResidueRing {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
    {Bd : BData S H} {bc : BalancedChoices D S H Bd}
    (E : ExteriorArithmetic D S H Bd bc) (I : S.ExtIdeal) :=
  S.R ⧸ Ideal.span {E.genR I}

/-- A1 producer obligation for exterior ideals and residue rings (02:229-283; 04:99-132). -/
theorem exteriorArithmetic_exists (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (Bd : BData S H) (bc : BalancedChoices D S H Bd) :
    Nonempty (ExteriorArithmetic D S H Bd bc) := by
  classical
  let one : S.ExtIdeal := ⟨⊤, ⟨top_ne_bot, by
    intro v hv hle
    exact v.isPrime.ne_top (top_le_iff.mp hle)⟩⟩
  have one_val : one.1 = ⊤ := rfl
  let mul : S.ExtIdeal → S.ExtIdeal → S.ExtIdeal := fun I J =>
    ⟨I.1 * J.1, ⟨by
      intro h
      rcases Ideal.mul_eq_bot.mp h with hI | hJ
      · exact I.2.1 hI
      · exact J.2.1 hJ, by
      intro v hv hle
      rcases v.isPrime.mul_le.mp hle with hI | hJ
      · exact I.2.2 v hv hI
      · exact J.2.2 v hv hJ⟩⟩
  let pow : S.ExtIdeal → ℕ → S.ExtIdeal := fun I n =>
    ⟨I.1 ^ n, ⟨pow_ne_zero n I.2.1, by
      intro v hv hle
      by_cases hn : n = 0
      · subst n
        exact v.isPrime.ne_top (top_le_iff.mp (by simpa using hle))
      · exact I.2.2 v hv ((v.isPrime.pow_le_iff hn).mp hle)⟩⟩
  let ofSqf : S.SqfExtIdeal → S.ExtIdeal := fun I => ⟨I.1, I.2.1⟩
  let prime : (v : FinPlace F) → v ∉ S.Sf → S.ExtIdeal := fun v hv =>
    ⟨v.asIdeal, ⟨v.ne_bot, by
      intro w hw hle
      have heq : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top hle
      have hvw : v = w := HeightOneSpectrum.ext heq
      exact hv (by simpa [hvw] using hw)⟩⟩
  let support : S.ExtIdeal → Finset (FinPlace F) := fun I =>
    (Ideal.finite_factors (by simpa only [Ideal.zero_eq_bot] using I.2.1)).toFinset
  have mem_support : ∀ I v, v ∈ support I ↔ v.asIdeal ∣ I.1 := by
    intro I v
    have hI0 : I.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using I.2.1
    change v ∈ (Ideal.finite_factors hI0).toFinset ↔ v.asIdeal ∣ I.1
    exact (Ideal.finite_factors hI0).mem_toFinset
  let genR : S.ExtIdeal → S.R := fun I => ⟨(bc.gen I : Fˣ), a2p_gen_mem_R S bc I⟩
  have genR_val : ∀ I, (genR I : F) = (bc.gen I : F) := fun _ => rfl
  obtain ⟨residues⟩ := conductor_residues_exists S
  let residueEquiv (I : S.ExtIdeal) :
      S.R ⧸ Ideal.span {genR I} ≃+* 𝓞 F ⧸ I.1 := by
    have hmap : Ideal.map (algebraMap (𝓞 F) S.R) I.1 = Ideal.span {genR I} :=
      a2p_map_eq_span_genR S I (genR I) (by
        change S.IsGen ((bc.gen I : Fˣ) : F) I.1
        exact (bc.gen_spec I).1)
    have hkernel : RingHom.ker (residues.red I) = Ideal.span {genR I} := by
      calc
        RingHom.ker (residues.red I) = Ideal.map (algebraMap (𝓞 F) S.R) I.1 :=
          residues.ker I
        _ = Ideal.span {genR I} := hmap
    exact (Ideal.quotEquivOfEq hkernel).symm.trans
      (RingHom.quotientKerEquivOfSurjective (residues.surjective I))
  let residueFinite : ∀ I : S.ExtIdeal, Fintype (S.R ⧸ Ideal.span {genR I}) :=
    fun I => Fintype.ofEquiv (𝓞 F ⧸ I.1) (residueEquiv I).symm
  let residueCard : ∀ I : S.ExtIdeal,
      @Fintype.card _ (residueFinite I) = Ideal.absNorm I.1 := by
    intro I
    letI : Fintype (S.R ⧸ Ideal.span {genR I}) := residueFinite I
    calc
      Fintype.card (S.R ⧸ Ideal.span {genR I}) = Fintype.card (𝓞 F ⧸ I.1) :=
        Fintype.card_congr (residueEquiv I).toEquiv
      _ = Ideal.absNorm I.1 := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  refine ⟨{
    one := one
    one_val := one_val
    mul := mul
    mul_val := by intro I J; rfl
    pow := pow
    pow_val := by intro I n; rfl
    ofSqf := ofSqf
    ofSqf_val := by intro I; rfl
    prime := prime
    prime_val := by intro v hv; rfl
    support := support
    mem_support := mem_support
    support_exterior := by
      intro I v hv
      have hdiv : v.asIdeal ∣ I.1 := (mem_support I v).mp hv
      intro hvS
      exact I.2.2 v hvS (Ideal.dvd_iff_le.mp hdiv)
    genR := genR
    genR_val := genR_val
    residueFinite := residueFinite
    residue_card := residueCard
    unit_character := by
      intro x
      simp [chiIdealPow, one_val, ← Ideal.one_eq_top]
  }⟩

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
  classical
  let ellU : ℝ → S.FSˣ := fun T =>
    if hT : 0 < T then ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.sheetEllUnit D S T hT else 1
  let sheet : ℝ → Measure S.FS :=
    ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.sheetMeasure S μ v0
  let mul : Measure S.FS := (ENNReal.ofReal Real.pi)⁻¹ • Theta.mulHaarS S μ
  obtain ⟨omega, K, hOmegaMeas, hKcompact, hOmegaK, hOmegaNorm, hOmegaPartition⟩ :=
    ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.sheetOmega_exists D S
  let eps : UnitSix S → S.US := fun u => Classical.choose (QuotientGroup.mk_surjective u)
  refine ⟨{
    ellU := ellU
    ellU_val := by
      intro T hT
      simp [ellU, hT, ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.sheetEllUnit]
    ellU_norm := by
      intro T hT
      simpa [ellU, hT, ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.sheetEllUnit] using
        ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.sheet_absS_ell D S T hT
    sheet := sheet
    sheet_support := by
      intro T hT
      simpa [sheet] using
        ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.sheetMeasure_support S μ v0 T hT
    sheetInt_eq := by
      intro T hT f hf
      simpa [sheet] using
        ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.integral_sheetMeasure_eq_sheetInt
          S μ v0 T f hf
    mul := mul
    mul_eq := rfl
    disintegrate := by
      intro f hf
      simpa [sheet, mul] using
        ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.sheet_measure_disintegrate D S μ v0 f hf
    omega := omega
    omega_measurable := hOmegaMeas
    omega_norm := hOmegaNorm
    omega_partition := by
      simpa [ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.sheetGammaAction] using hOmegaPartition
    omega_bounded := ⟨K, hKcompact, hOmegaK⟩
    sheet_translate := by
      sorry
    sheet_inversion := by
      sorry
    unitSixFinite := by
      letI : Finite (UnitSix S) :=
        ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.unitSixFinite D S
      exact Fintype.ofFinite (UnitSix S)
    classFinite := by
      letI : Finite S.V := ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.classVFinite S
      exact Fintype.ofFinite S.V
    eps := eps
    eps_class := by
      intro u
      simpa [unitSixClass, eps] using
        (Classical.choose_spec (QuotientGroup.mk_surjective u))
  }⟩

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
  classical
  obtain ⟨A⟩ := A1.AddCharData.nonempty D
  let eps : UnitSix S → S.US := fun u => Classical.choose (QuotientGroup.mk_surjective u)
  have heps : ∀ u, unitSixClass S (eps u) = u := by
    intro u
    simpa [unitSixClass, eps] using
      (Classical.choose_spec (QuotientGroup.mk_surjective u))
  let charExists (u : UnitSix S) :=
    ArtinPrimitiveRoots.Proofs.A2_PRODUCERS.reflectionSChar_exists
      D S H Bd A ϑ hunit houtside hangular (eps u)
  let chars : UnitSix S → SChar S := fun u => Classical.choose (charExists u)
  have hchars : ∀ u y, ((chars u).L y : ℂˣ) =
      rfSCharacter D S H ϑ (eps u) y := by
    intro u y
    exact Classical.choose_spec (charExists u) y
  let rowEps : ReflectionRow S → S.US := rowEpsilon S bc
  have hrow : ∀ r, rowElement S r = rowEps r * bc.gen r.ideal := by
    intro r
    simpa [rowEps, rowEpsilon] using Classical.choose_spec (exists_rowUnit S bc r)
  exact ⟨eps, heps, chars, hchars, rowEps, hrow⟩

/-- Pairing descended to sixth-power classes (HilbertData already kills sixth powers).
Consumers: def:rf-profiles and rf:S-unfolding. Existence/descent still needs a proof. -/
structure ClassPairing (D : FieldData F) (S : SData F CE condη) (H : HilbertData F) where
  pair : S.V → S.V → ℂ
  pair_eq : ∀ x y, pair (cls x) (cls y) = D.σ0 (((S.HS H x y : Fˣ) : F))
  unitary : ∀ x y, ‖pair x y‖ = 1

/-- Quotient-descent glue from HilbertData and SData.HS (02:114-132; 04:507-548). -/
theorem classPairing_exists (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) : Nonempty (ClassPairing D S H) := by
  classical
  let g : rootsOfUnity 6 F →* ℂ :=
    (Units.coeHom ℂ).comp
      ((Units.map D.σ0.toMonoidHom).comp (rootsOfUnity 6 F).subtype)
  let f : S.FSˣ → S.FSˣ → ℂ := fun x y => g (S.HS H x y)
  have hmulHSLeft (x x' y : S.FSˣ) :
      S.HS H (x * x') y = S.HS H x y * S.HS H x' y := by
    unfold SData.HS
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    exact H.mul_left v.1 (S.compU v x) (S.compU v x') (S.compU v y)
  have hmulHSRight (x y y' : S.FSˣ) :
      S.HS H x (y * y') = S.HS H x y * S.HS H x y' := by
    unfold SData.HS
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    exact H.mul_right v.1 (S.compU v x) (S.compU v y) (S.compU v y')
  have hsixHSLeft (x y : S.FSˣ) : S.HS H (x ^ 6) y = 1 := by
    unfold SData.HS
    apply Finset.prod_eq_one
    intro v hv
    exact H.sixth_power v.1 (S.compU v (x ^ 6)) (S.compU v y)
      ⟨S.compU v x, by simp [SData.compU]⟩
  -- `sixth_power` is stated in the first argument; skewness transfers it to the second.
  have hsixHSRight' (x y : S.FSˣ) : S.HS H x (y ^ 6) = 1 := by
    unfold SData.HS
    apply Finset.prod_eq_one
    intro v hv
    have hfirst := H.sixth_power v.1 (S.compU v (y ^ 6)) (S.compU v x)
      ⟨S.compU v y, by simp [SData.compU]⟩
    have hskew := H.skew v.1 (S.compU v x) (S.compU v (y ^ 6))
    rw [hfirst] at hskew
    simpa using hskew
  have hmulLeft (x x' y : S.FSˣ) : f (x * x') y = f x y * f x' y := by
    calc
      f (x * x') y = g (S.HS H (x * x') y) := rfl
      _ = g (S.HS H x y * S.HS H x' y) := congrArg g (hmulHSLeft x x' y)
      _ = f x y * f x' y := g.map_mul _ _
  have hmulRight (x y y' : S.FSˣ) : f x (y * y') = f x y * f x y' := by
    calc
      f x (y * y') = g (S.HS H x (y * y')) := rfl
      _ = g (S.HS H x y * S.HS H x y') := congrArg g (hmulHSRight x y y')
      _ = f x y * f x y' := g.map_mul _ _
  have hsixLeft (x y : S.FSˣ) : f (x ^ 6) y = 1 := by
    change g (S.HS H (x ^ 6) y) = 1
    rw [hsixHSLeft]
    exact g.map_one
  have hsixRight (x y : S.FSˣ) : f x (y ^ 6) = 1 := by
    change g (S.HS H x (y ^ 6)) = 1
    rw [hsixHSRight']
    exact g.map_one
  have hnorm (x y : S.FSˣ) : ‖f x y‖ = 1 := by
    change ‖g (S.HS H x y)‖ = 1
    have hroot : ((S.HS H x y : Fˣ) : F) ^ 6 = 1 := by
      have hunit : (S.HS H x y : Fˣ) ^ 6 = 1 :=
        (mem_rootsOfUnity 6 (S.HS H x y : Fˣ)).mp (S.HS H x y).property
      simpa using congrArg (fun u : Fˣ => (u : F)) hunit
    have hpow : (g (S.HS H x y)) ^ 6 = 1 := by
      change (D.σ0 ((S.HS H x y : Fˣ) : F)) ^ 6 = 1
      rw [← map_pow, hroot]
      simp
    exact ((isOfFinOrder_iff_pow_eq_one).2 ⟨6, by norm_num, hpow⟩).norm_eq_one
  let pair : S.V → S.V → ℂ := fun x y =>
    Quotient.liftOn₂ x y f (by
      intro x y x' y' hx hy
      have hqx : (QuotientGroup.mk x : S.V) = QuotientGroup.mk x' :=
        Quotient.sound hx
      have hqy : (QuotientGroup.mk y : S.V) = QuotientGroup.mk y' :=
        Quotient.sound hy
      have hxmem : x / x' ∈ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range :=
        (QuotientGroup.eq_iff_div_mem).mp hqx
      have hymem : y / y' ∈ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range :=
        (QuotientGroup.eq_iff_div_mem).mp hqy
      obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hxmem
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hymem
      have hxpow : x / x' = u ^ 6 := by simpa only [powMonoidHom_apply] using hu.symm
      have hypow : y / y' = v ^ 6 := by simpa only [powMonoidHom_apply] using hv.symm
      have hxfactor : x = u ^ 6 * x' := by
        calc
          x = (x / x') * x' := by simp
          _ = u ^ 6 * x' := by rw [hxpow]
      have hyfactor : y = v ^ 6 * y' := by
        calc
          y = (y / y') * y' := by simp
          _ = v ^ 6 * y' := by rw [hypow]
      have hxinv (z : S.FSˣ) : f x z = f x' z := by
        rw [hxfactor, hmulLeft, hsixLeft, one_mul]
      have hyinv : f x' y = f x' y' := by
        rw [hyfactor, hmulRight, hsixRight, one_mul]
      exact (hxinv y).trans hyinv)
  refine ⟨pair, ?_, ?_⟩
  · intro x y
    rfl
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro x y
    exact hnorm x y


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
