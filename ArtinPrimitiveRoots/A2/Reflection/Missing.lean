import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».All
import ArtinPrimitiveRoots.Proofs.th_factor_b.Analytic

/-! A2 statement interfaces derived from the design lane. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Pointwise
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- T6 presentation, chosen once for each row character. -/
structure RotatedPresentation (S : SData F CE condη) (δ : ℝ) where
  J : ℕ
  ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ
  fc : Fin J → InfinitePlace F → ℂ → ℂ
  finite_bound : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v)
  complex_bound : ∀ ℓ w, SheetHypCInfinity δ (fc ℓ w)

/-- Fixed reflection data. No reflection conclusion is included among these fields. -/
structure ReflectionSetup (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (Bd : BData S H) (A : AddCharData F)
    (ϑ : HeckeChar F) (bc : BalancedChoices D S H Bd)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F) where
  vartheta_unitary : ∀ x, ‖((ϑ x : ℂˣ) : ℂ)‖ = 1
  vartheta_unramified : ∀ v, v ∉ S.Sf → ϑ.UnramifiedAt v
  /-- Angular admissibility needed by the corrected `reflectionCharacters_exists` producer;
  included with the setup producer from `sol-gate-a2b` (02:606-625; 04:51-65). -/
  vartheta_angular : HeckeChar.HasAngularType D ϑ
  vartheta_generator : ∀ I : S.ExtIdeal, ϑ.idealValue I.1 = S.LS ϑ (S.diagU (bc.gen I))
  exterior : ExteriorArithmetic D S H Bd bc
  sheets : SheetGeometry D S μ v0
  chars : ReflectionCharacters D S H Bd bc ϑ
  pairing : ClassPairing D S H
  C : ThetaCover D S H A
  family : Finset (SChar S)
  T : ThetaFamily C family
  mem_family : ∀ u, chars.L u ∈ family
  rotated : UnitSix S → RotatedPresentation S T.δ
  rotated_eq : ∀ u y, T.WS (chars.L u) (C.aS y * C.wS) =
    Theta.sumProd S (rotated u).J (rotated u).ff (rotated u).fc (y : S.FS)
  K : ℝ → ℂ
  K_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K (Set.Ioi 0)
  K_moments : ∀ β : ℝ, IntegrableOn (fun t => ‖K t‖ * t ^ β / t) (Set.Ioi 0)
  K_bounds : ∀ N : ℝ, ∀ j : ℕ, ∃ C : ℝ, ∀ t, 0 < t →
    ‖Theta.normDerivR j K t‖ ≤ C * min (t ^ N) (t ^ (-N))
  K_gaussian : ∀ u, 0 < u →
    ∫ t in Set.Ioi (0 : ℝ), K t * Theta.thetaV S μ v0 T.U T.cS (u * t) / (t : ℂ) = (PG u : ℂ)

/-- A1/Theta producer obligation for the composite reflection input (02:606-625; 03:474-659;
04:51-65). Corrected by `sol-gate-a2b`: it supplies the split Gauss data and the complete setup,
including angular admissibility, without assuming a reflection estimate. -/
theorem reflectionSetup_exists (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (Bd : BData S H) (A : AddCharData F)
    (bc : BalancedChoices D S H Bd) (μ : ∀ v : FinPlace F, Theta.LocHaar v)
    (v0 : InfinitePlace F) :
    ∀ η Λ G : HeckeChar F, IsOfFinOrder η →
      (∀ v, v ∉ S.Sf → η.UnramifiedAt v) →
      (∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1) → HeckeChar.HasAngularType D Λ →
      IsOfFinOrder G →
      (∀ v, v ∉ S.Sf → Λ.UnramifiedAt v ∧ G.UnramifiedAt v ∧
        ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
          gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p =
            -(Λ.primeValue v * G.primeValue v)) →
      Nonempty (ReflectionSetup D S H Bd A (vartheta Λ G η) bc μ v0) := by
  sorry

section Reflection
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)

/-- The split Gauss characters consumed by the legacy `prop_reflection` route. The same angular
field supplies admissibility for `ReflectionCharacters`; corrected by `sol-gate-a2b` (04:51-65,
05:194-246). -/
structure GaussSplit (η : HeckeChar F) where
  Λ : HeckeChar F
  G : HeckeChar F
  eta_finite : IsOfFinOrder η
  eta_exterior : ∀ v, v ∉ S.Sf → η.UnramifiedAt v
  lambda_unitary : ∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1
  lambda_angular : HeckeChar.HasAngularType D Λ
  G_finite : IsOfFinOrder G
  vartheta_eq : ϑ = vartheta Λ G η
  gauss : ∀ v, v ∉ S.Sf → Λ.UnramifiedAt v ∧ G.UnramifiedAt v ∧
    ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
      gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p =
        -(Λ.primeValue v * G.primeValue v)

/-- Package the exact Gauss-character hypotheses used by `reflectionSetup_exists` into the
split input consumed by `prop:probe-low` (04:51–65; 05:194–246). -/
def gaussSplit_of_data (η Λ G : HeckeChar F)
    (hη : IsOfFinOrder η) (heta : ∀ v, v ∉ S.Sf → η.UnramifiedAt v)
    (hΛunit : ∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1)
    (hΛangular : HeckeChar.HasAngularType D Λ) (hG : IsOfFinOrder G)
    (hGauss : ∀ v, v ∉ S.Sf → Λ.UnramifiedAt v ∧ G.UnramifiedAt v ∧
      ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
        gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p =
          -(Λ.primeValue v * G.primeValue v)) :
    GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A)
      (ϑ := vartheta Λ G η) η := by
  exact ⟨Λ, G, hη, heta, hΛunit, hΛangular, hG, rfl, hGauss⟩

def primeGen (v : FinPlace F) : Fˣ :=
  if hv : v ∉ S.Sf then bc.gen (R.exterior.prime v hv) else 1

def rowClass (r : ReflectionRow S) : UnitSix S := unitSixClass S (R.chars.rowEps r)
def Lvalue (u : UnitSix S) (y : S.FSˣ) : ℂ := ((R.chars.L u).L y : ℂ)
def bCut (y : S.FSˣ) : ℂ := if cls y ∈ Bd.B then 1 else 0

def omegaAt (l : ℝ) : Set S.FS :=
  {y | ∃ x ∈ R.sheets.omega, y = (R.sheets.ellU l : S.FS) * x}

def omegaInt (l : ℝ) (f : S.FSˣ → ℂ) : ℂ :=
  ∫ y in omegaAt R l, onUnits f y ∂(R.sheets.sheet l)

def sheetIntegral (l : ℝ) (f : S.FSˣ → ℂ) : ℂ :=
  ∫ y, onUnits f y ∂(R.sheets.sheet l)

/-- def:rf-digit-sums, 04:99–132. Digits range over every residue, including zero. -/
abbrev Digits (r : ReflectionRow S) :=
  (v : {v : FinPlace F // v ∈ R.exterior.support r.ideal}) → 𝓞 F ⧸ v.1.asIdeal

def digitExponent (r : ReflectionRow S) (v : FinPlace F) : Fin 6 :=
  ⟨idealExp v r.ideal.1 % 6, Nat.mod_lt _ (by norm_num)⟩

def digitAlpha (r : ReflectionRow S) (d : Digits R r) : ℂ :=
  ∏ v : {v : FinPlace F // v ∈ R.exterior.support r.ideal},
    maskAlpha D A v.1 (primeGen R v.1) (digitExponent r v.1) (d v)

def digitPoint (r : ReflectionRow S) (y : S.FSˣ) (d : Digits R r) : R.C.G :=
  R.C.aS y * ((R.exterior.support r.ideal).attach.toList.map (fun v =>
    R.C.n v.1 (Multiplicative.ofAdd (algebraMap F _
      (algebraMap (𝓞 F) F (d v).out / (primeGen R v.1 : F)))))).prod

/-- `minus = true` uses the rational Weyl lift, before the digit point. -/
def digitSum (r : ReflectionRow S) (minus constant : Bool) (y : S.FSˣ) : ℂ :=
  ∑ᶠ d : Digits R r, digitAlpha R r d *
    (if constant then R.T.θN else R.T.θ) (R.chars.L (rowClass R r))
      ((if minus then R.C.rat weylGL else 1) * digitPoint R r y d)

def thetaAverage (r : ReflectionRow S) (l : ℝ) : ℂ :=
  omegaInt R l (fun y => bCut (Bd := Bd) y * (Lvalue R (rowClass R r) y)⁻¹ * digitSum R r false false y)

private theorem rf_gamma_residue_six (D : FieldData F) (γ : Gamma S)
    (v : FinPlace F) (hv : v ∉ S.Sf) :
    ∃ a : 𝓞 F ⧸ v.asIdeal, a ≠ 0 ∧
      residue v ((γ.1 : Fˣ) : F) = a ^ 6 := by
  classical
  letI := bridgeResidueField v
  obtain ⟨ε, hε⟩ : ∃ ε : S.US, (γ.1 : S.US) = ε ^ 6 := by
    have hmem : (γ.1 : S.US) ∈ (sixthPowerOnUS S).range := γ.2
    rcases MonoidHom.mem_range.mp hmem with ⟨ε, hε⟩
    change ε ^ 6 = γ.1 at hε
    exact ⟨ε, hε.symm⟩
  have hεval : HeightOneSpectrum.valuation F v ((ε : Fˣ) : F) = 1 :=
    Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F) ε hv
  have hglobal : ((γ.1 : S.US) : Fˣ) = (ε : Fˣ) ^ 6 :=
    congrArg (fun z : S.US => (z : Fˣ)) hε
  have hglobalF : ((γ.1 : Fˣ) : F) = ((ε : Fˣ) : F) ^ 6 :=
    congrArg (fun z : Fˣ => (z : F)) hglobal
  have hresPow (n : ℕ) :
      residue v (((ε : Fˣ) : F) ^ n) = residue v ((ε : Fˣ) : F) ^ n := by
    induction n with
    | zero =>
        have h := (a2_bridge_SYMBOL D S).residue_algebraMap v (1 : 𝓞 F)
        simpa using h
    | succ n ih =>
        have hvaln : HeightOneSpectrum.valuation F v
            (((ε : Fˣ) : F) ^ n) ≤ 1 := by
          rw [map_pow, hεval]
          simp
        rw [pow_succ, (a2_bridge_SYMBOL D S).residue_mul v
          (((ε : Fˣ) : F) ^ n) ((ε : Fˣ) : F) hvaln hεval.le, ih, pow_succ]
  have hεres : residue v ((ε : Fˣ) : F) ≠ 0 := by
    exact ((a2_bridge_SYMBOL D S).residue_ne_zero v ((ε : Fˣ) : F)
      hεval.le).mpr hεval
  refine ⟨residue v ((ε : Fˣ) : F), hεres, ?_⟩
  calc
    residue v ((γ.1 : Fˣ) : F) =
        residue v (((ε : Fˣ) : F) ^ 6) := by rw [hglobalF]
    _ = residue v ((ε : Fˣ) : F) ^ 6 := hresPow 6

private theorem rf_gamma_chi_one (D : FieldData F) (γ : Gamma S)
    (v : FinPlace F) (hv : v ∉ S.Sf) :
    chi D v ((γ.1 : Fˣ) : F) = 1 := by
  classical
  letI := bridgeResidueField v
  obtain ⟨a, ha, hγres⟩ := rf_gamma_residue_six D γ v hv
  let z : F := algebraMap (𝓞 F) F a.out
  have hzres : residue v z = a := by
    simpa [z] using (a2_bridge_SYMBOL D S).residue_algebraMap v a.out
  have hzpow : residue v (z ^ 6) = a ^ 6 := by
    dsimp [z]
    rw [← map_pow, (a2_bridge_SYMBOL D S).residue_algebraMap]
    simp
  have hresEq : residue v ((γ.1 : Fˣ) : F) = residue v (z ^ 6) := by
    rw [hγres, hzpow]
  have hvalOne : HeightOneSpectrum.valuation F v (1 : F) ≤ 1 := by simp
  have hresOne : residue v (1 : F) ≠ 0 := by
    apply ((a2_bridge_SYMBOL D S).residue_ne_zero v 1 hvalOne).2
    simp
  have hchiOneNe : chi D v 1 ≠ 0 := by
    intro hzero
    have hnorm := (a2_bridge_SYMBOL D S).chi_norm v 1 hresOne
    rw [hzero] at hnorm
    norm_num at hnorm
  have hchiMulOne := (a2_bridge_SYMBOL D S).chi_mul v hv (1 : F) 1
    hvalOne hvalOne
  have hchiOne : chi D v 1 = 1 := by
    have hcc : chi D v 1 = chi D v 1 * chi D v 1 := by simpa using hchiMulOne
    have hcancel : chi D v 1 * chi D v 1 = chi D v 1 * 1 := by
      calc
        chi D v 1 * chi D v 1 = chi D v 1 := hcc.symm
        _ = chi D v 1 * 1 := by simp
    exact mul_left_cancel₀ hchiOneNe hcancel
  have hchiPow (n : ℕ) : chi D v (z ^ n) = chi D v z ^ n := by
    induction n with
    | zero => simpa [hchiOne]
    | succ n ih =>
        have hzval : HeightOneSpectrum.valuation F v z ≤ 1 := by
          dsimp [z]
          exact v.valuation_le_one a.out
        have hznval : HeightOneSpectrum.valuation F v (z ^ n) ≤ 1 := by
          rw [← map_pow]
          exact v.valuation_le_one (a.out ^ n)
        rw [pow_succ, (a2_bridge_SYMBOL D S).chi_mul v hv (z ^ n) z hznval hzval,
          ih, pow_succ]
  have hzresNe : residue v z ≠ 0 := by simpa [hzres] using ha
  have hchiSix : chi D v z ^ 6 = 1 :=
    (a2_bridge_SYMBOL D S).chi_six v z hzresNe
  rw [(a2_bridge_SYMBOL D S).chi_congr v ((γ.1 : Fˣ) : F) (z ^ 6) hresEq,
    hchiPow 6, hchiSix]

private theorem rf_maskAlpha_gamma_residue_mul (D : FieldData F)
    (A : AddCharData F) (v : FinPlace F) (hv : v ∉ S.Sf) (p : Fˣ)
    (γ : Gamma S) (j : Fin 6) (x : 𝓞 F ⧸ v.asIdeal) :
    maskAlpha D A v p j (residue v ((γ.1 : Fˣ) : F) * x) =
      maskAlpha D A v p j x := by
  classical
  letI := bridgeResidueField v
  let g : F := (γ.1 : Fˣ)
  have hγval : HeightOneSpectrum.valuation F v g = 1 :=
    Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F)
      (γ.1 : S.US) hv
  have hγresNe : residue v g ≠ 0 := by
    exact ((a2_bridge_SYMBOL D S).residue_ne_zero v g hγval.le).mpr hγval
  have hzero : residue v g * x = 0 ↔ x = 0 := by
    constructor
    · intro h
      exact (mul_eq_zero.mp h).resolve_left hγresNe
    · rintro rfl
      simp
  by_cases hj : j = 0
  · simp [maskAlpha, hj, hzero, g]
  · by_cases hx : x = 0
    · have hy : residue v g * x = 0 := by simp [hx]
      simp [maskAlpha, hj, hx, hy, g]
    · have hy : residue v g * x ≠ 0 := by
        intro h
        exact hx ((mul_eq_zero.mp h).resolve_left hγresNe)
      let x' := residue v g * x
      have hvalx : HeightOneSpectrum.valuation F v
          (algebraMap (𝓞 F) F x.out) ≤ 1 := v.valuation_le_one x.out
      have hresx : residue v (algebraMap (𝓞 F) F x.out) = x := by
        simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v x.out
      have hresx' : residue v (algebraMap (𝓞 F) F x'.out) = x' := by
        simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v x'.out
      have hresProduct : residue v (g * algebraMap (𝓞 F) F x.out) =
          residue v g * x := by
        rw [(a2_bridge_SYMBOL D S).residue_mul v g
          (algebraMap (𝓞 F) F x.out) hγval.le hvalx, hresx]
      have hresEq : residue v (algebraMap (𝓞 F) F x'.out) =
          residue v (g * algebraMap (𝓞 F) F x.out) := by
        rw [hresx', hresProduct]
      have hchi : chi D v (algebraMap (𝓞 F) F x'.out) =
          chi D v (algebraMap (𝓞 F) F x.out) := by
        calc
          chi D v (algebraMap (𝓞 F) F x'.out) =
              chi D v (g * algebraMap (𝓞 F) F x.out) :=
            (a2_bridge_SYMBOL D S).chi_congr v _ _ hresEq
          _ = chi D v g * chi D v (algebraMap (𝓞 F) F x.out) :=
            (a2_bridge_SYMBOL D S).chi_mul v hv g
              (algebraMap (𝓞 F) F x.out) hγval.le hvalx
          _ = chi D v (algebraMap (𝓞 F) F x.out) := by
            rw [rf_gamma_chi_one D γ v hv]
            simp
      simp [maskAlpha, hj, hx, hy, x', g, hchi]

private lemma rf_count_spanSingleton_div (v : FinPlace F) (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) -
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv]
  ring

private lemma rf_count_spanSingleton_eq_neg_log_intValuation (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private lemma rf_count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
    (z : F) (hz : z ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
      -WithZero.log (HeightOneSpectrum.valuation F v z) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
  have hn : n ≠ 0 := by
    intro hn
    apply hz
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : (algebraMap (𝓞 F) F n) ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hmapd : (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hval : HeightOneSpectrum.valuation F v z =
      v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    rf_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    rf_count_spanSingleton_eq_neg_log_intValuation v n hn,
    rf_count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

local instance rfResidueMaximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance rfResidueField (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

private lemma rf_residue_rep (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal)
    (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b := by
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply (IsFractionRing.injective (𝓞 F) F)
    simp only [map_mul]
    rw [← hex.choose_spec.2, ← hab]
    ring
  have hqcross := congrArg (Ideal.Quotient.mk v.asIdeal) hcross
  have hqcross' : Ideal.Quotient.mk v.asIdeal hex.choose.1 *
      Ideal.Quotient.mk v.asIdeal b = Ideal.Quotient.mk v.asIdeal a *
        Ideal.Quotient.mk v.asIdeal hex.choose.2 := by
    simpa only [map_mul] using hqcross
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hdq : Ideal.Quotient.mk v.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold residue
  rw [dif_pos hex]
  calc
    Ideal.Quotient.mk v.asIdeal hex.choose.1 *
        (Ideal.Quotient.mk v.asIdeal hex.choose.2)⁻¹ =
    Ideal.Quotient.mk v.asIdeal hex.choose.1 / Ideal.Quotient.mk v.asIdeal hex.choose.2 := by
      rw [div_eq_mul_inv]
    _ = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b :=
      (div_eq_div_iff hdq hbq).2 hqcross'

private theorem rf_residue_div_prime_integral (v : FinPlace F)
    (hv : v ∉ S.Sf)
    (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal) (z : F)
    (hz : HeightOneSpectrum.valuation F v z ≤ 1) (x : 𝓞 F ⧸ v.asIdeal)
    (hx : residue v z = x) :
    HeightOneSpectrum.valuation F v ((z - (x.out : F)) / (p : F)) ≤ 1 := by
  letI := bridgeResidueField v
  obtain ⟨a, ⟨b, hb⟩, hzb⟩ := v.exists_primeCompl_mul_eq_of_integer z hz
  change b ∉ v.asIdeal at hb
  have hrep : residue v z = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b :=
    rf_residue_rep v z a b hb hzb
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hquot : x * Ideal.Quotient.mk v.asIdeal b = Ideal.Quotient.mk v.asIdeal a := by
    rw [← hx, hrep]
    exact div_mul_cancel₀ _ hbq
  have hmem : a - x.out * b ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    calc
      Ideal.Quotient.mk v.asIdeal (a - x.out * b) =
          Ideal.Quotient.mk v.asIdeal a - x * Ideal.Quotient.mk v.asIdeal b := by simp
      _ = 0 := by rw [hquot]; simp
  have hnumVal : HeightOneSpectrum.valuation F v
      (algebraMap (𝓞 F) F (a - x.out * b)) ≤ WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have hmemPow : a - x.out * b ∈ v.asIdeal ^ (1 : ℕ) := by simpa using hmem
    exact (v.intValuation_le_pow_iff_mem _ 1).2 hmemPow
  have hbF : algebraMap (𝓞 F) F b ≠ 0 := by
    intro h
    have hbzero : b = 0 := (IsFractionRing.injective (𝓞 F) F) (by simpa using h)
    exact hb (by rw [hbzero]; exact Ideal.zero_mem _)
  have hbVal : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F b) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := b)).2 hb
  have hdiffEq : z - (x.out : F) =
      algebraMap (𝓞 F) F (a - x.out * b) / algebraMap (𝓞 F) F b := by
    apply (eq_div_iff hbF).2
    calc
      (z - (x.out : F)) * algebraMap (𝓞 F) F b =
          z * algebraMap (𝓞 F) F b - (x.out : F) * algebraMap (𝓞 F) F b := by ring
      _ = algebraMap (𝓞 F) F a - (x.out : F) * algebraMap (𝓞 F) F b := by rw [hzb]
      _ = algebraMap (𝓞 F) F (a - x.out * b) := by simp [map_sub, map_mul]
  have hdiffVal : HeightOneSpectrum.valuation F v (z - (x.out : F)) ≤
      WithZero.exp (-1 : ℤ) := by
    rw [hdiffEq, map_div₀, hbVal, div_one]
    exact hnumVal
  have hpCount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      _ = FractionalIdeal.count F v (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
        hp.2.2 v hv
      _ = 1 := FractionalIdeal.count_self F v
  have hpLog : WithZero.log (HeightOneSpectrum.valuation F v (p : F)) = -1 := by
    have h := rf_count_spanSingleton_eq_neg_log_valuation v (p : F) (Units.ne_zero p)
    rw [hpCount] at h
    linarith
  have hpne : HeightOneSpectrum.valuation F v (p : F) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr (Units.ne_zero p)
  have hpVal : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ) := by
    calc
      _ = WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (p : F))) :=
        (WithZero.exp_log hpne).symm
      _ = WithZero.exp (-1 : ℤ) := by rw [hpLog]
  rw [map_div₀, hpVal]
  have hpos : 0 < WithZero.exp (-1 : ℤ) :=
    lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
  exact (div_le_one₀ hpos).2 hdiffVal

private theorem rf_list_interleave {α G : Type} [Monoid G] (l : List α)
    (f g : α → G) (hnodup : l.Nodup)
    (hcross : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → Commute (f a) (g b)) :
    (l.map f).prod * (l.map g).prod = (l.map (fun a => f a * g a)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have haNot : a ∉ l := (List.nodup_cons.mp hnodup).1
      have hcrossTail : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → Commute (f x) (g y) := by
        intro x hx y hy hxy
        exact hcross x (by simp [hx]) y (by simp [hy]) hxy
      have hcrossHead : ∀ x ∈ l, Commute (f x) (g a) := by
        intro x hx
        apply hcross x (by simp [hx]) a (by simp)
        intro h
        subst x
        exact haNot hx
      have hmoveAux : ∀ l' : List α,
          (∀ x ∈ l', Commute (f x) (g a)) →
          (l'.map f).prod * g a = g a * (l'.map f).prod := by
        intro l' h
        induction l' with
        | nil => simp
        | cons b l' ihMove =>
            have hba : Commute (f b) (g a) := h b (by simp)
            have htail : ∀ x ∈ l', Commute (f x) (g a) := by
              intro x hx
              exact h x (by simp [hx])
            have hmoveTail := ihMove htail
            simp only [List.map_cons, List.prod_cons]
            calc
              (f b * (l'.map f).prod) * g a =
                  f b * ((l'.map f).prod * g a) := by rw [mul_assoc]
              _ = f b * (g a * (l'.map f).prod) := by rw [hmoveTail]
              _ = (f b * g a) * (l'.map f).prod := by rw [← mul_assoc]
              _ = (g a * f b) * (l'.map f).prod := by rw [hba.eq]
              _ = g a * (f b * (l'.map f).prod) := by rw [mul_assoc]
      have hmove := hmoveAux l hcrossHead
      have hih := ih (List.nodup_cons.mp hnodup).2 hcrossTail
      simp only [List.map_cons, List.prod_cons]
      calc
        (f a * (l.map f).prod) * (g a * (l.map g).prod) =
            f a * ((l.map f).prod * (g a * (l.map g).prod)) := by rw [mul_assoc]
        _ = f a * (((l.map f).prod * g a) * (l.map g).prod) := by
          congr 1
          exact (mul_assoc _ _ _).symm
        _ = f a * ((g a * (l.map f).prod) * (l.map g).prod) := by
          congr 1
          rw [hmove]
        _ = f a * (g a * ((l.map f).prod * (l.map g).prod)) := by
          congr 1
          exact mul_assoc _ _ _
        _ = (f a * g a) * ((l.map f).prod * (l.map g).prod) := by
          exact (mul_assoc _ _ _).symm
        _ = (f a * g a) * (l.map (fun x => f x * g x)).prod := by rw [hih]

private theorem rf_commute_left_list_prod {α G : Type} [Monoid G]
    (k : G) (l : List α) (f : α → G)
    (hcomm : ∀ x ∈ l, k * f x = f x * k) :
    k * (l.map f).prod = (l.map f).prod * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := hcomm a (by simp)
      have htail : ∀ x ∈ l, k * f x = f x * k := by
        intro x hx
        exact hcomm x (by simp [hx])
      have hrest := ih htail
      simp only [List.map_cons, List.prod_cons]
      calc
        k * (f a * (l.map f).prod) = (k * f a) * (l.map f).prod := by rw [mul_assoc]
        _ = (f a * k) * (l.map f).prod := by rw [ha]
        _ = f a * (k * (l.map f).prod) := by rw [← mul_assoc]
        _ = f a * ((l.map f).prod * k) := by rw [hrest]
        _ = (f a * (l.map f).prod) * k := by rw [mul_assoc]

private theorem rf_list_prod_mem {α G : Type} [Group G]
    (H : Subgroup G) (l : List α) (f : α → G)
    (hmem : ∀ x ∈ l, f x ∈ H) : (l.map f).prod ∈ H := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have htail : ∀ x ∈ l, f x ∈ H := by
        intro x hx
        exact hmem x (by simp [hx])
      simp only [List.map_cons, List.prod_cons]
      exact H.mul_mem (hmem a (by simp)) (ih htail)

/-- rf:descent, 04:133–183: automorphy and all four Γ-invariances. -/
theorem rf_descent :
  (∀ r y, digitSum R r false false y = digitSum R r true false y) ∧
  (∀ r (γ : Gamma S) y (minus constant : Bool),
    digitSum R r minus constant (S.diagU (γ.1 : Fˣ) * y) = digitSum R r minus constant y) ∧
  (∀ (γ : Gamma S) y, bCut (Bd := Bd) (S.diagU (γ.1 : Fˣ) * y) = bCut (Bd := Bd) y) ∧
  (∀ u (γ : Gamma S), Lvalue R u (S.diagU (γ.1 : Fˣ)) = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r y
    unfold digitSum
    apply finsum_congr
    intro d
    simp only [Bool.false_eq_true, if_false, one_mul]
    congr 1
    exact (R.T.automorphic (R.chars.L (rowClass R r))
      (R.mem_family (rowClass R r)) weylGL (digitPoint R r y d)).symm
  · intro r γ y minus constant
    classical
    let T0 := R.exterior.support r.ideal
    let V := {v : FinPlace F // v ∈ T0}
    letI : ∀ v : V, Field (𝓞 F ⧸ v.1.asIdeal) := fun v => bridgeResidueField v.1
    letI : ∀ v : V, Fintype (𝓞 F ⧸ v.1.asIdeal) := fun v => bridgeResidueFintype v.1
    letI : Fintype (Digits R r) := inferInstance
    have hvS (v : V) : v.1 ∉ S.Sf :=
      R.exterior.support_exterior r.ideal v.1 v.2
    have hroot (v : V) : ∃ a : 𝓞 F ⧸ v.1.asIdeal, a ≠ 0 ∧
        residue v.1 ((γ.1 : Fˣ) : F) = a ^ 6 :=
      rf_gamma_residue_six D γ v.1 (hvS v)
    choose a ha hresRoot using hroot
    let rho : ∀ v : V, (𝓞 F ⧸ v.1.asIdeal)ˣ := fun v =>
      Units.mk0 (a v ^ 6) (pow_ne_zero 6 (ha v))
    have hrhoVal (v : V) : (rho v : 𝓞 F ⧸ v.1.asIdeal) =
        residue v.1 ((γ.1 : Fˣ) : F) := by
      calc
        (rho v : 𝓞 F ⧸ v.1.asIdeal) = a v ^ 6 := by
          change (a v) ^ 6 = a v ^ 6
          rfl
        _ = residue v.1 ((γ.1 : Fˣ) : F) := (hresRoot v).symm
    let e : Digits R r ≃ Digits R r := {
      toFun := fun d v => (rho v : 𝓞 F ⧸ v.1.asIdeal) * d v
      invFun := fun d v => ((rho v)⁻¹ : 𝓞 F ⧸ v.1.asIdeal) * d v
      left_inv := by
        intro d
        funext v
        exact Units.inv_mul_cancel_left (rho v) (d v)
      right_inv := by
        intro d
        funext v
        exact Units.mul_inv_cancel_left (rho v) (d v) }
    have hmask (v : V) (x : 𝓞 F ⧸ v.1.asIdeal) :
        maskAlpha D A v.1 (primeGen R v.1) (digitExponent r v.1)
          ((rho v : 𝓞 F ⧸ v.1.asIdeal) * x) =
        maskAlpha D A v.1 (primeGen R v.1) (digitExponent r v.1) x := by
      rw [hrhoVal v]
      exact rf_maskAlpha_gamma_residue_mul D A v.1 (hvS v) (primeGen R v.1)
        γ (digitExponent r v.1) x
    have hAlpha (d : Digits R r) : digitAlpha R r (e d) = digitAlpha R r d := by
      unfold digitAlpha
      apply Finset.prod_congr rfl
      intro v hv
      simpa [e] using hmask v (d v)
    let gammaF : Fˣ := γ.1
    let digitLocArg : (d : Digits R r) → (v : FinPlace F) →
        (hv : v ∈ T0) → v.adicCompletion F := fun d v hv =>
      algebraMap F (v.adicCompletion F)
        (algebraMap (𝓞 F) F (d ⟨v, hv⟩).out / (primeGen R v : F))
    let nOld : Digits R r → FinPlace F → R.C.G := fun d0 v =>
      if hv : v ∈ T0 then R.C.n v (Multiplicative.ofAdd (digitLocArg d0 v hv)) else 1
    let nNew : Digits R r → FinPlace F → R.C.G := fun d0 v =>
      if hv : v ∈ T0 then R.C.n v (Multiplicative.ofAdd (digitLocArg (e d0) v hv)) else 1
    let aLoc : FinPlace F → R.C.G := fun v => R.C.a v (toLoc v gammaF)
    let err : Digits R r → ∀ v : FinPlace F, v.adicCompletion F := fun d0 v =>
      if hv : v ∈ T0 then
        digitLocArg d0 v hv * (toLoc v gammaF : v.adicCompletion F) -
          digitLocArg (e d0) v hv
      else 0
    let kLoc : Digits R r → FinPlace F → R.C.G := fun d0 v =>
      R.C.n v (Multiplicative.ofAdd (err d0 v)) * aLoc v
    have hT0 : ∀ v ∈ T0, v ∉ S.Sf := by
      intro v hv
      exact R.exterior.support_exterior r.ideal v hv
    have hgammaVal (v : FinPlace F) (hv : v ∉ S.Sf) :
        HeightOneSpectrum.valuation F v (gammaF : F) = 1 :=
      Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F)
        (γ.1 : S.US) hv
    have hgammaLocVal (v : FinPlace F) (hv : v ∉ S.Sf) :
        Valued.v (toLoc v gammaF : v.adicCompletion F) = 1 := by
      change Valued.v (algebraMap F (v.adicCompletion F) (gammaF : F)) = 1
      simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation',
        hgammaVal v hv]
    have hgammaLocInt (v : FinPlace F) (hv : v ∉ S.Sf) :
        (toLoc v gammaF : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hgammaLocVal v hv]
    have hgammaLocInvInt (v : FinPlace F) (hv : v ∉ S.Sf) :
        (((toLoc v gammaF)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
          v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [Units.val_inv_eq_inv_val, map_inv₀, hgammaLocVal v hv, inv_one, le_refl]
    have herrInt (d0 : Digits R r) (v : FinPlace F) (hvT : v ∈ T0) :
        err d0 v ∈ v.adicCompletionIntegers F := by
      classical
      let dv : 𝓞 F ⧸ v.asIdeal := d0 ⟨v, hvT⟩
      let dv' : 𝓞 F ⧸ v.asIdeal := e d0 ⟨v, hvT⟩
      let p : Fˣ := primeGen R v
      have hv : v ∉ S.Sf := hT0 v hvT
      have hvalD : HeightOneSpectrum.valuation F v
          (algebraMap (𝓞 F) F dv.out) ≤ 1 := v.valuation_le_one dv.out
      have hresD : residue v (algebraMap (𝓞 F) F dv.out) = dv := by
        simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v dv.out
      have hresZ : residue v
          ((gammaF : F) * algebraMap (𝓞 F) F dv.out) = dv' := by
        calc
          residue v ((gammaF : F) * algebraMap (𝓞 F) F dv.out) =
              residue v (gammaF : F) * residue v (algebraMap (𝓞 F) F dv.out) :=
            (a2_bridge_SYMBOL D S).residue_mul v (gammaF : F)
              (algebraMap (𝓞 F) F dv.out) (hgammaVal v hv).le hvalD
          _ = residue v (gammaF : F) * dv := by rw [hresD]
          _ = (rho ⟨v, hvT⟩ : 𝓞 F ⧸ v.asIdeal) * dv := by rw [← hrhoVal ⟨v, hvT⟩]
          _ = dv' := by
            dsimp [dv, dv', e]
      have hvalZ : HeightOneSpectrum.valuation F v
          ((gammaF : F) * algebraMap (𝓞 F) F dv.out) ≤ 1 := by
        rw [map_mul]
        calc
          _ ≤ 1 * 1 := mul_le_mul (hgammaVal v hv).le hvalD (by exact bot_le) (by exact bot_le)
          _ = 1 := by simp
      have hpgen : S.IsGen (p : F) v.asIdeal := by
        have h := bc.gen_spec (R.exterior.prime v hv)
        simpa [p, primeGen, hv, R.exterior.prime_val] using h.1
      have hquotVal := rf_residue_div_prime_integral v hv p hpgen
        ((gammaF : F) * algebraMap (𝓞 F) F dv.out) hvalZ dv' hresZ
      have hargEq : err d0 v = algebraMap F (v.adicCompletion F)
          (((gammaF : F) * algebraMap (𝓞 F) F dv.out - (dv'.out : F)) / (p : F)) := by
        simp only [err, dif_pos hvT, digitLocArg, dv, dv', p]
        rw [show (toLoc v gammaF : v.adicCompletion F) =
          algebraMap F (v.adicCompletion F) (gammaF : F) by rfl]
        simp only [map_div₀, map_mul, map_sub]
        ring_nf
      rw [hargEq, HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation']
      exact hquotVal
    have hlocal (d0 : Digits R r) (v : FinPlace F) (hvT : v ∈ T0) :
        aLoc v * nOld d0 v = nNew d0 v * kLoc d0 v := by
      let xold := digitLocArg d0 v hvT
      let xnew := digitLocArg (e d0) v hvT
      let gval := (toLoc v gammaF : v.adicCompletion F)
      have hparam : xold * gval = xnew + err d0 v := by
        dsimp only [xold, xnew, err]
        rw [dif_pos hvT]
        abel
      have hNadd : R.C.n v (Multiplicative.ofAdd (xold * gval)) =
          R.C.n v (Multiplicative.ofAdd xnew) * R.C.n v (Multiplicative.ofAdd (err d0 v)) := by
        calc
          R.C.n v (Multiplicative.ofAdd (xold * gval)) =
              R.C.n v (Multiplicative.ofAdd (xnew + err d0 v)) := by rw [hparam]
          _ = R.C.n v (Multiplicative.ofAdd xnew * Multiplicative.ofAdd (err d0 v)) := by
            congr 1
          _ = _ := map_mul _ _ _
      have hLift := R.C.lift_na v (xold * gval) (toLoc v gammaF)
      have hmove : R.C.n v (Multiplicative.ofAdd (xold * gval)) * aLoc v =
          aLoc v * R.C.n v (Multiplicative.ofAdd xold) := by
        simpa [aLoc, gval, mul_assoc] using hLift
      calc
        aLoc v * nOld d0 v = R.C.n v (Multiplicative.ofAdd (xold * gval)) * aLoc v := by
          simpa [nOld, xold, digitLocArg, hvT] using hmove.symm
        _ = (R.C.n v (Multiplicative.ofAdd xnew) *
              R.C.n v (Multiplicative.ofAdd (err d0 v))) * aLoc v := by rw [hNadd]
        _ = nNew d0 v * kLoc d0 v := by
          simp [nNew, kLoc, xnew, digitLocArg, hvT, mul_assoc]
    have haLocMem (v : FinPlace F) : aLoc v ∈ R.C.Gloc v :=
      R.C.a_mem v (toLoc v gammaF)
    have hnOldMem (d0 : Digits R r) (v : FinPlace F) (hvT : v ∈ T0) :
        nOld d0 v ∈ R.C.Gloc v := by
      simp only [nOld, dif_pos hvT]
      exact R.C.n_mem v _
    have hnNewMem (d0 : Digits R r) (v : FinPlace F) (hvT : v ∈ T0) :
        nNew d0 v ∈ R.C.Gloc v := by
      simp only [nNew, dif_pos hvT]
      exact R.C.n_mem v _
    have hkLocGloc (d0 : Digits R r) (v : FinPlace F) : kLoc d0 v ∈ R.C.Gloc v := by
      change R.C.n v (Multiplicative.ofAdd (err d0 v)) * aLoc v ∈ R.C.Gloc v
      exact (R.C.Gloc v).mul_mem (R.C.n_mem v _) (haLocMem v)
    have hkLocKext (d0 : Digits R r) (v : FinPlace F) (hvT : v ∈ T0) :
        kLoc d0 v ∈ R.C.Kext := by
      change R.C.n v (Multiplicative.ofAdd (err d0 v)) * aLoc v ∈ R.C.Kext
      exact R.C.Kext.mul_mem
        (R.C.n_Kext v (hT0 v hvT) (err d0 v) (herrInt d0 v hvT))
        (R.C.a_Kext v (hT0 v hvT) (toLoc v gammaF)
          (hgammaLocInt v (hT0 v hvT))
          (by simpa only [Units.val_inv_eq_inv_val] using hgammaLocInvInt v (hT0 v hvT)))
    have hgammaUS : gammaF ∈ S.US := (γ.1 : S.US).property
    have haExtK : R.C.aExt gammaF ∈ R.C.Kext :=
      R.C.aExt_unit gammaF hgammaUS
    have hresOutside : ∀ v : FinPlace F, v ∉ S.Sf → v ∉ T0 →
        residue v (gammaF : F) ≠ 0 ∧ residue v ((gammaF⁻¹ : Fˣ) : F) ≠ 0 := by
      intro v hvS hvT
      have hγv := hgammaVal v hvS
      have hγinv : HeightOneSpectrum.valuation F v ((gammaF⁻¹ : Fˣ) : F) = 1 := by
        exact Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F)
          ((γ.1 : S.US)⁻¹) hvS
      constructor
      · exact ((a2_bridge_SYMBOL D S).residue_ne_zero v (gammaF : F) hγv.le).mpr hγv
      · exact ((a2_bridge_SYMBOL D S).residue_ne_zero v
          ((gammaF⁻¹ : Fˣ) : F) hγinv.le).mpr hγinv
    obtain ⟨k0, hk0Mem, hk0Comm, hsplitA⟩ :=
      R.C.aExt_split gammaF T0 hT0 hresOutside
    obtain ⟨ε, hε⟩ : ∃ ε : S.US, (γ.1 : S.US) = ε ^ 6 := by
      have hmem : (γ.1 : S.US) ∈ (sixthPowerOnUS S).range := γ.2
      rcases MonoidHom.mem_range.mp hmem with ⟨ε, hε⟩
      change ε ^ 6 = γ.1 at hε
      exact ⟨ε, hε.symm⟩
    have hglobalPow : gammaF = (ε : Fˣ) ^ 6 :=
      congrArg (fun z : S.US => (z : Fˣ)) hε
    have hHSone : S.HS H (S.diagU gammaF) y = 1 := by
      unfold SData.HS
      apply Finset.prod_eq_one
      intro v hv
      have hcomp : S.compU v (S.diagU gammaF) =
          (S.compU v (S.diagU (ε : Fˣ))) ^ 6 := by
        rw [hglobalPow]
        simp only [map_pow]
      exact H.sixth_power v.1 (S.compU v (S.diagU gammaF)) (S.compU v y)
        ⟨S.compU v (S.diagU (ε : Fˣ)), hcomp⟩
    have hmu : muThree D (S.HS H (S.diagU gammaF) y) = 1 := by
      rw [hHSone]
      apply Subtype.ext
      apply Units.ext
      simp [muThree]
    have hSprod : R.C.aS (S.diagU gammaF) * R.C.aS y =
        R.C.aS (S.diagU gammaF * y) := by
      have h := R.C.aS_mul (S.diagU gammaF) y
      rw [hmu] at h
      simpa using h
    have hk0OldComm (d0 : Digits R r) :
        k0 * (T0.toList.map (nOld d0)).prod =
          (T0.toList.map (nOld d0)).prod * k0 := by
      apply rf_commute_left_list_prod
      intro v hvList
      have hvT : v ∈ T0 := Finset.mem_toList.mp hvList
      exact hk0Comm v hvT (nOld d0 v) (hnOldMem d0 v hvT)
    have hcrossAOld (d0 : Digits R r) :
        ∀ v ∈ T0.toList, ∀ w ∈ T0.toList, v ≠ w →
          Commute (aLoc v) (nOld d0 w) := by
      intro v hvList w hwList hvw
      have hvT : v ∈ T0 := Finset.mem_toList.mp hvList
      have hwT : w ∈ T0 := Finset.mem_toList.mp hwList
      exact R.C.comm_loc v w hvw (aLoc v) (haLocMem v) (nOld d0 w)
        (hnOldMem d0 w hwT)
    have hcrossNewK (d0 : Digits R r) :
        ∀ v ∈ T0.toList, ∀ w ∈ T0.toList, v ≠ w →
          Commute (nNew d0 v) (kLoc d0 w) := by
      intro v hvList w hwList hvw
      have hvT : v ∈ T0 := Finset.mem_toList.mp hvList
      have hwT : w ∈ T0 := Finset.mem_toList.mp hwList
      exact R.C.comm_loc v w hvw (nNew d0 v) (hnNewMem d0 v hvT) (kLoc d0 w)
        (hkLocGloc d0 w)
    have hpairLocal (d0 : Digits R r) :
        T0.toList.map (fun v => aLoc v * nOld d0 v) =
          T0.toList.map (fun v => nNew d0 v * kLoc d0 v) := by
      apply List.map_congr_left
      intro v hvList
      exact hlocal d0 v (Finset.mem_toList.mp hvList)
    let kTot : Digits R r → R.C.G := fun d0 =>
      (T0.toList.map (kLoc d0)).prod * k0
    have hkTot (d0 : Digits R r) : kTot d0 ∈ R.C.Kext := by
      dsimp [kTot]
      exact R.C.Kext.mul_mem
        (rf_list_prod_mem R.C.Kext T0.toList (kLoc d0)
          (fun v hvList => hkLocKext d0 v (Finset.mem_toList.mp hvList))) hk0Mem
    have hExtTimesN (d0 : Digits R r) :
        R.C.aExt gammaF * (T0.toList.map (nOld d0)).prod =
          (T0.toList.map (nNew d0)).prod * kTot d0 := by
      dsimp [kTot]
      rw [hsplitA]
      calc
        ((T0.toList.map aLoc).prod * k0) * (T0.toList.map (nOld d0)).prod =
            (T0.toList.map aLoc).prod *
              (k0 * (T0.toList.map (nOld d0)).prod) := by rw [mul_assoc]
        _ = (T0.toList.map aLoc).prod *
              ((T0.toList.map (nOld d0)).prod * k0) := by rw [hk0OldComm d0]
        _ = ((T0.toList.map aLoc).prod * (T0.toList.map (nOld d0)).prod) * k0 := by
              rw [← mul_assoc]
        _ = ((T0.toList.map (fun v => aLoc v * nOld d0 v)).prod) * k0 := by
              rw [rf_list_interleave T0.toList aLoc (nOld d0) T0.nodup_toList
                (hcrossAOld d0)]
        _ = ((T0.toList.map (fun v => nNew d0 v * kLoc d0 v)).prod) * k0 := by
              rw [hpairLocal d0]
        _ = ((T0.toList.map (nNew d0)).prod * (T0.toList.map (kLoc d0)).prod) * k0 := by
              rw [← rf_list_interleave T0.toList (nNew d0) (kLoc d0)
                T0.nodup_toList (hcrossNewK d0)]
        _ = (T0.toList.map (nNew d0)).prod *
              ((T0.toList.map (kLoc d0)).prod * k0) := by rw [mul_assoc]
    have hmapPerm : (T0.attach.toList.map Subtype.val).Perm T0.toList := by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact (T0.attach.nodup_toList).map Subtype.val_injective
      · exact T0.nodup_toList
      · ext v
        simp
    have hmapOld (d0 : Digits R r) :
        T0.attach.toList.map (fun v =>
          R.C.n v.1 (Multiplicative.ofAdd (digitLocArg d0 v.1 v.2))) =
        T0.attach.toList.map (fun v => nOld d0 v.1) := by
      apply List.map_congr_left
      intro v hvList
      simp [nOld, digitLocArg, v.2]
    have hmapNew (d0 : Digits R r) :
        T0.attach.toList.map (fun v =>
          R.C.n v.1 (Multiplicative.ofAdd (digitLocArg (e d0) v.1 v.2))) =
        T0.attach.toList.map (fun v => nNew d0 v.1) := by
      apply List.map_congr_left
      intro v hvList
      simp [nNew, digitLocArg, v.2]
    have hpermOld (d0 : Digits R r) :
        (T0.attach.toList.map (fun v => nOld d0 v.1)).Perm
          (T0.toList.map (nOld d0)) := by
      change List.Perm (List.map (nOld d0 ∘ Subtype.val) T0.attach.toList)
        (List.map (nOld d0) T0.toList)
      simpa only [List.map_map] using hmapPerm.map (nOld d0)
    have hpermNew (d0 : Digits R r) :
        (T0.attach.toList.map (fun v => nNew d0 v.1)).Perm
          (T0.toList.map (nNew d0)) := by
      change List.Perm (List.map (nNew d0 ∘ Subtype.val) T0.attach.toList)
        (List.map (nNew d0) T0.toList)
      simpa only [List.map_map] using hmapPerm.map (nNew d0)
    have hpairOld (d0 : Digits R r) :
        (T0.attach.toList.map (fun v => nOld d0 v.1)).Pairwise Commute := by
      have hcomm : ∀ v w : V, v ≠ w → Commute (nOld d0 v.1) (nOld d0 w.1) := by
        intro v w hvw
        change nOld d0 v.1 * nOld d0 w.1 = nOld d0 w.1 * nOld d0 v.1
        have hvw' : v.1 ≠ w.1 := by
          intro hEq
          apply hvw
          exact Subtype.ext hEq
        exact R.C.comm_loc v.1 w.1 hvw' (nOld d0 v.1) (hnOldMem d0 v.1 v.2)
          (nOld d0 w.1) (hnOldMem d0 w.1 w.2)
      exact List.Pairwise.map (fun v => nOld d0 v.1) hcomm
        (List.nodup_iff_pairwise_ne.mp T0.attach.nodup_toList)
    have hpairNew (d0 : Digits R r) :
        (T0.attach.toList.map (fun v => nNew d0 v.1)).Pairwise Commute := by
      have hcomm : ∀ v w : V, v ≠ w → Commute (nNew d0 v.1) (nNew d0 w.1) := by
        intro v w hvw
        change nNew d0 v.1 * nNew d0 w.1 = nNew d0 w.1 * nNew d0 v.1
        have hvw' : v.1 ≠ w.1 := by
          intro hEq
          apply hvw
          exact Subtype.ext hEq
        exact R.C.comm_loc v.1 w.1 hvw' (nNew d0 v.1) (hnNewMem d0 v.1 v.2)
          (nNew d0 w.1) (hnNewMem d0 w.1 w.2)
      exact List.Pairwise.map (fun v => nNew d0 v.1) hcomm
        (List.nodup_iff_pairwise_ne.mp T0.attach.nodup_toList)
    have hpointOld (d0 : Digits R r) :
        digitPoint R r y d0 = R.C.aS y * (T0.toList.map (nOld d0)).prod := by
      unfold digitPoint
      rw [hmapOld d0]
      congr 1
      exact List.Perm.prod_eq' (hpermOld d0) (hpairOld d0)
    have hpointNew (d0 : Digits R r) :
        digitPoint R r (S.diagU gammaF * y) (e d0) =
          R.C.aS (S.diagU gammaF * y) * (T0.toList.map (nNew d0)).prod := by
      unfold digitPoint
      rw [hmapNew d0]
      congr 1
      exact List.Perm.prod_eq' (hpermNew d0) (hpairNew d0)
    let kTotFun : Digits R r → R.C.G := kTot
    have hmain (d0 : Digits R r) :
        R.C.rat (diagGL gammaF) * digitPoint R r y d0 =
          digitPoint R r (S.diagU gammaF * y) (e d0) * kTotFun d0 := by
      have hcommAS : R.C.aExt gammaF * R.C.aS y = R.C.aS y * R.C.aExt gammaF :=
        R.C.Kext_comm_S (R.C.aExt gammaF) haExtK (R.C.aS y) (R.C.aS_mem y)
      calc
        _ = (R.C.aS (S.diagU gammaF) * R.C.aExt gammaF) *
              (R.C.aS y * (T0.toList.map (nOld d0)).prod) := by
                rw [R.C.rat_diag, hpointOld d0]
        _ = (R.C.aS (S.diagU gammaF) * R.C.aS y) *
              (R.C.aExt gammaF * (T0.toList.map (nOld d0)).prod) := by
                calc
                  _ = R.C.aS (S.diagU gammaF) *
                        (R.C.aExt gammaF * R.C.aS y) * (T0.toList.map (nOld d0)).prod := by
                          group
                  _ = R.C.aS (S.diagU gammaF) *
                        (R.C.aS y * R.C.aExt gammaF) * (T0.toList.map (nOld d0)).prod := by
                          rw [hcommAS]
                  _ = (R.C.aS (S.diagU gammaF) * R.C.aS y) *
                        (R.C.aExt gammaF * (T0.toList.map (nOld d0)).prod) := by group
        _ = R.C.aS (S.diagU gammaF * y) *
              ((T0.toList.map (nNew d0)).prod * kTotFun d0) := by
                rw [hSprod, hExtTimesN d0]
        _ = digitPoint R r (S.diagU gammaF * y) (e d0) * kTotFun d0 := by
                rw [hpointNew d0]
                exact (mul_assoc (R.C.aS (S.diagU gammaF * y))
                  (T0.toList.map (nNew d0)).prod (kTotFun d0)).symm
    have hpoint (d0 : Digits R r) :
        ∃ k ∈ R.C.Kext, digitPoint R r (S.diagU gammaF * y) (e d0) =
          R.C.rat (diagGL gammaF) * digitPoint R r y d0 * k⁻¹ := by
      refine ⟨kTotFun d0, hkTot d0, ?_⟩
      have hmul := congrArg (fun z : R.C.G => z * (kTotFun d0)⁻¹) (hmain d0)
      have hmul' : (R.C.rat (diagGL gammaF) * digitPoint R r y d0) *
            (kTotFun d0)⁻¹ = digitPoint R r (S.diagU gammaF * y) (e d0) := by
        simpa [mul_assoc] using hmul
      exact hmul'.symm
    have hWeylDiag : R.C.rat weylGL * R.C.rat (diagGL gammaF) =
        R.C.rat (diagGL (gammaF⁻¹)) * R.C.rat weylGL := by
      have hm : weylGL * diagGL gammaF =
          scalarGL gammaF * (diagGL (gammaF⁻¹) * weylGL) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [weylGL, diagGL, scalarGL, Matrix.mul_apply]
      calc
        _ = R.C.rat (weylGL * diagGL gammaF) := by rw [← map_mul]
        _ = R.C.rat (scalarGL gammaF * (diagGL (gammaF⁻¹) * weylGL)) := by rw [hm]
        _ = R.C.rat (scalarGL gammaF) * R.C.rat (diagGL (gammaF⁻¹) * weylGL) := by
          rw [map_mul]
        _ = 1 * (R.C.rat (diagGL (gammaF⁻¹)) * R.C.rat weylGL) := by
          rw [R.C.rat_scalar, map_mul]
        _ = _ := by simp
    have hthetaTrans (f : R.C.G → ℂ)
        (hleft : ∀ δ : Fˣ, ∀ g : R.C.G,
          f (R.C.rat (diagGL δ) * g) = f g)
        (hright : ∀ g k, k ∈ R.C.Kext → f (g * k) = f g)
        (d0 : Digits R r) :
        f ((if minus then R.C.rat weylGL else 1) *
            digitPoint R r (S.diagU gammaF * y) (e d0)) =
          f ((if minus then R.C.rat weylGL else 1) * digitPoint R r y d0) := by
      obtain ⟨k, hk, hpt⟩ := hpoint d0
      have hki : k⁻¹ ∈ R.C.Kext := R.C.Kext.inv_mem hk
      cases minus with
      | false =>
          simp only [Bool.false_eq_true, if_false, one_mul]
          calc
            f (digitPoint R r (S.diagU gammaF * y) (e d0)) =
                f (R.C.rat (diagGL gammaF) * digitPoint R r y d0 * k⁻¹) := by rw [hpt]
            _ =
                f (R.C.rat (diagGL gammaF) * digitPoint R r y d0) :=
              hright _ _ hki
            _ = f (digitPoint R r y d0) := hleft gammaF _
      | true =>
          have hptW : R.C.rat weylGL *
                (digitPoint R r (S.diagU gammaF * y) (e d0)) =
              (R.C.rat (diagGL (gammaF⁻¹)) *
                (R.C.rat weylGL * digitPoint R r y d0)) * k⁻¹ := by
            calc
              _ = R.C.rat weylGL *
                    (R.C.rat (diagGL gammaF) * digitPoint R r y d0 * k⁻¹) := by rw [hpt]
              _ = (R.C.rat weylGL * R.C.rat (diagGL gammaF) *
                    digitPoint R r y d0) * k⁻¹ := by group
              _ = (R.C.rat (diagGL (gammaF⁻¹)) *
                    (R.C.rat weylGL * digitPoint R r y d0)) * k⁻¹ := by
                      rw [hWeylDiag]
                      group
          calc
            f (R.C.rat weylGL * digitPoint R r (S.diagU gammaF * y) (e d0)) =
                f ((R.C.rat (diagGL (gammaF⁻¹)) *
                  (R.C.rat weylGL * digitPoint R r y d0)) * k⁻¹) := by rw [hptW]
            _ = f (R.C.rat (diagGL (gammaF⁻¹)) *
                  (R.C.rat weylGL * digitPoint R r y d0)) := hright _ _ hki
            _ = f (R.C.rat weylGL * digitPoint R r y d0) := hleft (gammaF⁻¹) _
    let L := R.chars.L (rowClass R r)
    have htheta (d0 : Digits R r) :
        ((if constant then R.T.θN else R.T.θ) L)
            ((if minus then R.C.rat weylGL else 1) *
              digitPoint R r (S.diagU gammaF * y) (e d0)) =
        ((if constant then R.T.θN else R.T.θ) L)
            ((if minus then R.C.rat weylGL else 1) * digitPoint R r y d0) := by
      cases constant
      · exact hthetaTrans (R.T.θ L)
          (fun δ g => R.T.automorphic L (R.mem_family (rowClass R r)) (diagGL δ) g)
          (fun g k hk => R.T.right_Kext L (R.mem_family (rowClass R r)) g k hk) d0
      · exact hthetaTrans (R.T.θN L)
          (fun δ g => R.T.θN_left L (R.mem_family (rowClass R r)) (diagGL δ)
            (by simp [diagGL]) g)
          (fun g k hk => R.T.θN_right L (R.mem_family (rowClass R r)) g k hk) d0
    let newTerm : Digits R r → ℂ := fun d0 => digitAlpha R r d0 *
      (if constant then R.T.θN else R.T.θ) (R.chars.L (rowClass R r))
        ((if minus then R.C.rat weylGL else 1) *
          digitPoint R r (S.diagU (γ.1 : Fˣ) * y) d0)
    let oldTerm : Digits R r → ℂ := fun d0 => digitAlpha R r d0 *
      (if constant then R.T.θN else R.T.θ) (R.chars.L (rowClass R r))
        ((if minus then R.C.rat weylGL else 1) * digitPoint R r y d0)
    have hterm (d0 : Digits R r) : newTerm (e d0) = oldTerm d0 := by
      dsimp [newTerm, oldTerm]
      calc
        _ = digitAlpha R r d0 *
              ((if constant then R.T.θN else R.T.θ) L)
                ((if minus then R.C.rat weylGL else 1) *
                  digitPoint R r (S.diagU gammaF * y) (e d0)) := by rw [hAlpha d0]
        _ = digitAlpha R r d0 *
              ((if constant then R.T.θN else R.T.θ) L)
                ((if minus then R.C.rat weylGL else 1) * digitPoint R r y d0) := by
          rw [htheta d0]
    unfold digitSum
    change (∑ᶠ d0 : Digits R r, newTerm d0) = ∑ᶠ d0 : Digits R r, oldTerm d0
    calc
      (∑ᶠ d0 : Digits R r, newTerm d0) = ∑ d0 : Digits R r, newTerm d0 :=
        finsum_eq_sum_of_fintype _
      _ = ∑ d0 : Digits R r, newTerm (e d0) := (Equiv.sum_comp e newTerm).symm
      _ = ∑ d0 : Digits R r, oldTerm d0 := by
        apply Finset.sum_congr rfl
        intro d0 hd0
        exact hterm d0
      _ = ∑ᶠ d0 : Digits R r, oldTerm d0 :=
        (finsum_eq_sum_of_fintype _).symm
  · intro γ y
    have hroot : ∃ ε : S.US, (γ.1 : S.US) = ε ^ 6 := by
      have hmem : (γ.1 : S.US) ∈ (sixthPowerOnUS S).range := γ.2
      rcases MonoidHom.mem_range.mp hmem with ⟨ε, hε⟩
      change ε ^ 6 = γ.1 at hε
      exact ⟨ε, hε.symm⟩
    obtain ⟨ε, hε⟩ := hroot
    have hdiag : cls (S.diagU (γ.1 : Fˣ)) = 1 := by
      have hpow : S.diagU (γ.1 : Fˣ) = S.diagU (ε : Fˣ) ^ 6 := by
        have hε' : (γ.1 : Fˣ) = ((ε ^ 6 : S.US) : Fˣ) :=
          congrArg (fun z : S.US => (z : Fˣ)) hε
        rw [hε']
        exact map_pow (S.diagU) (ε : Fˣ) 6
      change (QuotientGroup.mk (S.diagU (γ.1 : Fˣ)) : S.V) = 1
      rw [QuotientGroup.eq_one_iff]
      change S.diagU (γ.1 : Fˣ) ∈ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range
      exact MonoidHom.mem_range.mpr ⟨S.diagU (ε : Fˣ), hpow.symm⟩
    have hclass : cls (S.diagU (γ.1 : Fˣ) * y) = cls y := by
      calc
        cls (S.diagU (γ.1 : Fˣ) * y) =
            cls (S.diagU (γ.1 : Fˣ)) * cls y := by simp [cls]
        _ = cls y := by rw [hdiag]; exact one_mul (cls y)
    unfold bCut
    rw [hclass]
  · intro u γ
    change (((R.chars.L u).L (S.diagU (γ.1 : S.US)) : ℂˣ) : ℂ) = 1
    have h := (R.chars.L u).trivial_US (γ.1 : S.US) (γ.1).property
    exact congrArg (fun z : ℂˣ => (z : ℂ)) h
/-- Fundamental sets are measurable and use the actual diagonal Γ, with unique representatives. -/
def IsFundamentalAt (O : Set S.FS) (l : ℝ) : Prop :=
  MeasurableSet O ∧ (∀ y ∈ O, IsUnit y ∧ S.absS y = l) ∧
  ∀ y : S.FSˣ, S.absS (y : S.FS) = l →
    ∃! γ : Gamma S, ((S.diagU (γ.1 : Fˣ))⁻¹ * y : S.FSˣ).val ∈ O

private theorem rf_measurable_leftMul (a : S.FS) :
    Measurable (fun y : S.FS => a * y) := by
  apply Measurable.prod
  · apply measurable_pi_iff.mpr
    intro v
    exact (measurable_const_mul (a.1 v)).comp
      ((measurable_pi_apply v).comp measurable_fst)
  · apply measurable_pi_iff.mpr
    intro w
    exact (measurable_const_mul (a.2 w)).comp
      ((measurable_pi_apply w).comp measurable_snd)

private def rfGammaDiag : Gamma S →* S.FSˣ :=
  S.diagU.comp (S.US.subtype.comp (Gamma S).subtype)

private theorem rfGammaDiag_eq (γ : Gamma S) :
    rfGammaDiag (S := S) γ = S.diagU (γ.1 : Fˣ) := rfl

/-- rf:descent, 04:133-183. The integral identity uses the same sheet measure on the chosen domain. -/
theorem rf_descent_integral :
  ∀ r l, 0 < l → ∀ O, IsFundamentalAt O l →
    ∫ y in O, onUnits (fun y => bCut (Bd := Bd) y * (Lvalue R (rowClass R r) y)⁻¹ *
      digitSum R r false false y) y ∂(R.sheets.sheet l) = thetaAverage R r l := by
  intro r l hl O hO
  letI : SMul (Gamma S) S.FS := ⟨fun γ y =>
    (rfGammaDiag (S := S) γ : S.FS) * y⟩
  letI : MulAction (Gamma S) S.FS := {
    one_smul := by
      intro y
      change (rfGammaDiag (S := S) 1 : S.FS) * y = y
      simp
    mul_smul := by
      intro γ γ' y
      change (rfGammaDiag (S := S) (γ * γ') : S.FS) * y =
        (rfGammaDiag (S := S) γ : S.FS) *
          ((rfGammaDiag (S := S) γ' : S.FS) * y)
      rw [map_mul]
      simp [mul_assoc] }
  have hact (γ : Gamma S) (y : S.FS) :
      γ • y = (S.diagU (γ.1 : Fˣ) : S.FS) * y := by
    change (rfGammaDiag (S := S) γ : S.FS) * y = _
    rw [rfGammaDiag_eq]
  letI : MeasurableConstSMul (Gamma S) S.FS := ⟨fun γ => by
    change Measurable (fun y : S.FS => (rfGammaDiag (S := S) γ : S.FS) * y)
    exact rf_measurable_leftMul _⟩
  letI : Countable (Gamma S) :=
    (a2_bridge_SHEET (D := D) (S := S) (G := R.sheets) l hl).2.2
  have hgammaNorm (γ : Gamma S) :
      S.absS (rfGammaDiag (S := S) γ : S.FS) = 1 := by
    rw [rfGammaDiag_eq]
    exact (a2_bridge_NORM D S).2.2.2.1 (γ.1 : S.US)
  have hpres (γ : Gamma S) : MeasurePreserving (fun y : S.FS => γ • y)
      (R.sheets.sheet l) (R.sheets.sheet l) := by
    refine ⟨measurable_const_smul γ, ?_⟩
    change Measure.map (fun y : S.FS =>
      (rfGammaDiag (S := S) γ : S.FS) * y) (R.sheets.sheet l) = R.sheets.sheet l
    simpa [hgammaNorm γ] using R.sheets.sheet_translate (rfGammaDiag (S := S) γ) l hl
  letI : SMulInvariantMeasure (Gamma S) S.FS (R.sheets.sheet l) := ⟨fun γ t ht => by
    calc
      R.sheets.sheet l ((fun y : S.FS => γ • y) ⁻¹' t) =
          Measure.map (fun y : S.FS => γ • y) (R.sheets.sheet l) t :=
        (Measure.map_apply (measurable_const_smul γ) ht).symm
      _ = R.sheets.sheet l t := by rw [(hpres γ).map_eq]⟩
  have hactInv (γ : Gamma S) (y : S.FS) :
      γ⁻¹ • y = ((S.diagU (γ.1 : Fˣ))⁻¹ : S.FS) * y := by
    calc
      γ⁻¹ • y = (S.diagU ((γ⁻¹).1 : Fˣ) : S.FS) * y := hact γ⁻¹ y
      _ = (rfGammaDiag (S := S) γ⁻¹ : S.FS) * y := by rw [← rfGammaDiag_eq]
      _ = ((rfGammaDiag (S := S) γ)⁻¹ : S.FSˣ) * y := by rw [map_inv]
      _ = ((S.diagU (γ.1 : Fˣ))⁻¹ : S.FS) * y := by
        congr 1
        exact Units.val_inv_eq_inv_val _
  have mkDomain (O' : Set S.FS) (hO' : IsFundamentalAt O' l) :
      MeasureTheory.IsFundamentalDomain (Gamma S) O' (R.sheets.sheet l) := by
    have hcover : ∀ᵐ y ∂ (R.sheets.sheet l), ∃ γ : Gamma S, γ • y ∈ O' := by
      filter_upwards [R.sheets.sheet_support l hl] with y hy
      rcases hy with ⟨hyunit, hynorm⟩
      let yu : S.FSˣ := hyunit.unit
      obtain ⟨γ, hγ, -⟩ := hO'.2.2 yu hynorm
      refine ⟨γ⁻¹, ?_⟩
      rw [hactInv]
      simpa [yu, hyunit.unit_spec] using hγ
    have hdis : ∀ γ : Gamma S, γ ≠ 1 →
        MeasureTheory.AEDisjoint (R.sheets.sheet l) (γ • O') O' := by
      intro γ hγ
      apply Disjoint.aedisjoint
      apply Set.disjoint_left.mpr
      intro y hleft hright
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hleft
      obtain ⟨hyunit, hynorm⟩ := hO'.2.1 y hright
      let yu : S.FSˣ := hyunit.unit
      obtain ⟨δ, -, huniq⟩ := hO'.2.2 yu hynorm
      have hγmem : ((S.diagU (γ.1 : Fˣ))⁻¹ * yu : S.FSˣ).val ∈ O' := by
        rw [hactInv] at hleft
        simpa [yu, hyunit.unit_spec] using hleft
      have h1mem : ((S.diagU ((1 : Gamma S).1 : Fˣ))⁻¹ * yu : S.FSˣ).val ∈ O' := by
        simpa [yu, hyunit.unit_spec] using hright
      have hγδ := huniq γ hγmem
      have h1δ := huniq 1 h1mem
      exact hγ (hγδ.trans h1δ.symm)
    refine MeasureTheory.IsFundamentalDomain.mk'' hO'.1.nullMeasurableSet hcover hdis ?_
    intro γ
    exact (hpres γ).quasiMeasurePreserving
  have hOdom := mkDomain O hO
  have hOmegaAt : IsFundamentalAt (omegaAt R l) l := by
    simpa [IsFundamentalAt, omegaAt, bridgeFundamentalAt, bridgeOmegaAt] using
      (a2_bridge_SHEET (D := D) (S := S) (G := R.sheets) l hl).1
  have hOmegadom := mkDomain (omegaAt R l) hOmegaAt
  let f : S.FSˣ → ℂ := fun y =>
    bCut (Bd := Bd) y * (Lvalue R (rowClass R r) y)⁻¹ * digitSum R r false false y
  rcases rf_descent R with ⟨_, hDigit, hCut, hL⟩
  have hLmul (γ : Gamma S) (y : S.FSˣ) :
      Lvalue R (rowClass R r) (S.diagU (γ.1 : Fˣ) * y) =
        Lvalue R (rowClass R r) (S.diagU (γ.1 : Fˣ)) *
          Lvalue R (rowClass R r) y := by
    simp [Lvalue, map_mul]
  have hinv (γ : Gamma S) (y : S.FS) :
      onUnits f (γ • y) = onUnits f y := by
    change onUnits f ((S.diagU (γ.1 : Fˣ) : S.FS) * y) = onUnits f y
    by_cases hy : IsUnit y
    · have hmul : IsUnit ((S.diagU (γ.1 : Fˣ) : S.FS) * y) :=
        (S.diagU (γ.1 : Fˣ)).isUnit_units_mul y |>.2 hy
      have hmulval : hmul.unit = S.diagU (γ.1 : Fˣ) * hy.unit := by
        apply Units.ext
        simp [hy.unit_spec]
      have hleft : onUnits f ((S.diagU (γ.1 : Fˣ) : S.FS) * y) = f hmul.unit := by
        simp [onUnits, hmul]
      have hright : onUnits f y = f hy.unit := by simp [onUnits, hy]
      rw [hleft, hright, hmulval]
      dsimp [f]
      rw [hCut γ hy.unit, hLmul γ hy.unit, hL (rowClass R r) γ,
        hDigit r γ hy.unit false false]
      simp
    · have hmul : ¬ IsUnit ((S.diagU (γ.1 : Fˣ) : S.FS) * y) :=
        fun h => hy ((S.diagU (γ.1 : Fˣ)).isUnit_units_mul y |>.1 h)
      simp [onUnits, hy, hmul]
  change (∫ y in O, onUnits f y ∂(R.sheets.sheet l)) =
    thetaAverage R r l
  calc
    (∫ y in O, onUnits f y ∂(R.sheets.sheet l)) =
        ∫ y in omegaAt R l, onUnits f y ∂(R.sheets.sheet l) :=
      hOdom.setIntegral_eq hOmegadom hinv
    _ = thetaAverage R r l := by rfl
/-- rf:angular-cancellation, 04:185–220. Neither constant term is claimed Weyl-invariant. -/
theorem rf_angular_cancellation :
  ∀ r l, 0 < l →
    (∀ minus : Bool, omegaInt R l (fun y => bCut (Bd := Bd) y * (Lvalue R (rowClass R r) y)⁻¹ *
      digitSum R r minus true y) = 0) ∧
    thetaAverage R r l = omegaInt R l (fun y => bCut (Bd := Bd) y *
      (Lvalue R (rowClass R r) y)⁻¹ * digitSum R r true false y) := by
  sorry
def unrotated (u : UnitSix S) (y : S.FSˣ) : ℂ := R.T.WS (R.chars.L u) (R.C.aS y)
def rotated (u : UnitSix S) (y : S.FSˣ) : ℂ := R.T.WS (R.chars.L u) (R.C.aS y * R.C.wS)
def sCocycle (x y : S.FSˣ) : ℂ := D.σ0 (((S.HS H x y : Fˣ) : F)) ^ 2

def forwardTerm (r : ReflectionRow S) (ν : Fˣ) (y : S.FSˣ) : ℂ :=
  bCut (Bd := Bd) y * ∑ᶠ d : Digits R r, digitAlpha R r d *
    R.T.W (R.chars.L (rowClass R r)) (R.C.rat (diagGL ν) * digitPoint R r y d)

private theorem rf_local_phase_eq_residue (v : FinPlace F) (hv : v ∉ S.Sf)
    (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal) (z : F)
    (hz : HeightOneSpectrum.valuation F v z ≤ 1) (x : 𝓞 F ⧸ v.asIdeal) :
    A.ψ v (algebraMap F (v.adicCompletion F) (z * (x.out : F) / (p : F))) =
    A.ψ v (algebraMap F (v.adicCompletion F)
        ((x.out : F) * ((residue v z).out : F) / (p : F))) := by
  obtain ⟨a, ⟨b, hb⟩, hzb⟩ := v.exists_primeCompl_mul_eq_of_integer z hz
  change b ∉ v.asIdeal at hb
  have ht : residue v z = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b :=
    rf_residue_rep v z a b hb hzb
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hquot : residue v z * Ideal.Quotient.mk v.asIdeal b =
      Ideal.Quotient.mk v.asIdeal a := by
    calc
      residue v z * Ideal.Quotient.mk v.asIdeal b =
          (Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b) *
            Ideal.Quotient.mk v.asIdeal b := by rw [ht]
      _ = Ideal.Quotient.mk v.asIdeal a := div_mul_cancel₀ _ hbq
  have hmem : a - (residue v z).out * b ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    calc
      Ideal.Quotient.mk v.asIdeal (a - (residue v z).out * b) =
          Ideal.Quotient.mk v.asIdeal a -
            (residue v z) * Ideal.Quotient.mk v.asIdeal b := by simp
      _ = 0 := by rw [hquot]; simp
  have hnumVal : HeightOneSpectrum.valuation F v
      (algebraMap (𝓞 F) F (a - (residue v z).out * b)) ≤ WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have hmemPow : a - (residue v z).out * b ∈ v.asIdeal ^ (1 : ℕ) := by
      simpa using hmem
    exact (v.intValuation_le_pow_iff_mem _ 1).2 hmemPow
  have hbF : algebraMap (𝓞 F) F b ≠ 0 := by
    intro h
    have hbzero : b = 0 := (IsFractionRing.injective (𝓞 F) F) (by simpa using h)
    exact hb (by rw [hbzero]; exact Ideal.zero_mem _)
  have hbVal : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F b) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := b)).2 hb
  have hdiffEq : z - ((residue v z).out : F) =
      algebraMap (𝓞 F) F (a - (residue v z).out * b) / algebraMap (𝓞 F) F b := by
    apply (eq_div_iff hbF).2
    calc
      (z - ((residue v z).out : F)) * algebraMap (𝓞 F) F b =
          z * algebraMap (𝓞 F) F b -
            ((residue v z).out : F) * algebraMap (𝓞 F) F b := by ring
      _ = algebraMap (𝓞 F) F a -
            ((residue v z).out : F) * algebraMap (𝓞 F) F b := by rw [hzb]
      _ = algebraMap (𝓞 F) F (a - (residue v z).out * b) := by simp [map_sub, map_mul]
  have hdiffVal : HeightOneSpectrum.valuation F v
      (z - ((residue v z).out : F)) ≤ WithZero.exp (-1 : ℤ) := by
    rw [hdiffEq, map_div₀, hbVal, div_one]
    exact hnumVal
  have hxVal : HeightOneSpectrum.valuation F v (x.out : F) ≤ 1 := v.valuation_le_one x.out
  have hprodVal : HeightOneSpectrum.valuation F v
      ((z - ((residue v z).out : F)) * (x.out : F)) ≤ WithZero.exp (-1 : ℤ) := by
    rw [map_mul]
    calc
      _ ≤ WithZero.exp (-1 : ℤ) * 1 :=
        mul_le_mul hdiffVal hxVal (by exact bot_le) (by exact bot_le)
      _ = WithZero.exp (-1 : ℤ) := by simp
  have hp_count : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      _ = FractionalIdeal.count F v (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
        hp.2.2 v hv
      _ = 1 := FractionalIdeal.count_self F v
  have hp_log : WithZero.log (HeightOneSpectrum.valuation F v (p : F)) = -1 := by
    have h := rf_count_spanSingleton_eq_neg_log_valuation v (p : F) (Units.ne_zero p)
    rw [hp_count] at h
    linarith
  have hp_ne : HeightOneSpectrum.valuation F v (p : F) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr (Units.ne_zero p)
  have hp_val : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ) := by
    calc
      _ = WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (p : F))) :=
        (WithZero.exp_log hp_ne).symm
      _ = WithZero.exp (-1 : ℤ) := by rw [hp_log]
  have hargVal : HeightOneSpectrum.valuation F v
      (((z - ((residue v z).out : F)) * (x.out : F)) / (p : F)) ≤ 1 := by
    rw [map_div₀, hp_val]
    have hpos : 0 < WithZero.exp (-1 : ℤ) :=
      lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
    exact (div_le_one₀ hpos).2 hprodVal
  have hlocal : A.ψ v (algebraMap F (v.adicCompletion F)
      (((z - ((residue v z).out : F)) * (x.out : F)) / (p : F))) = 1 := by
    have hmemLoc : algebraMap F (v.adicCompletion F)
        (((z - ((residue v z).out : F)) * (x.out : F)) / (p : F)) ∈
          v.adicCompletionIntegers F := by
      change ((((z - ((residue v z).out : F)) * (x.out : F)) / (p : F) : F) :
        v.adicCompletion F) ∈ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hargVal
    exact A.integral v _ hmemLoc
  have harg : algebraMap F (v.adicCompletion F)
      (((z - ((residue v z).out : F)) * (x.out : F)) / (p : F)) =
    algebraMap F (v.adicCompletion F) (z * (x.out : F) / (p : F)) -
      algebraMap F (v.adicCompletion F)
        ((x.out : F) * ((residue v z).out : F) / (p : F)) := by
    calc
      _ = algebraMap F (v.adicCompletion F)
          (z * (x.out : F) / (p : F) -
            (x.out : F) * ((residue v z).out : F) / (p : F)) := by
        congr 1
        ring
      _ = _ := map_sub _ _ _
  have hdiv := (A.ψ v).map_sub_eq_div
    (algebraMap F (v.adicCompletion F) (z * (x.out : F) / (p : F)))
    (algebraMap F (v.adicCompletion F)
      ((x.out : F) * ((residue v z).out : F) / (p : F)))
  have hψb : A.ψ v (algebraMap F (v.adicCompletion F)
      ((x.out : F) * ((residue v z).out : F) / (p : F))) ≠ 0 :=
    (AddChar.val_isUnit (A.ψ v)
      (algebraMap F (v.adicCompletion F)
        ((x.out : F) * ((residue v z).out : F) / (p : F)))).ne_zero
  calc
    A.ψ v (algebraMap F (v.adicCompletion F) (z * (x.out : F) / (p : F))) =
        (A.ψ v (algebraMap F (v.adicCompletion F) (z * (x.out : F) / (p : F))) /
          A.ψ v (algebraMap F (v.adicCompletion F)
            ((x.out : F) * ((residue v z).out : F) / (p : F)))) *
          A.ψ v (algebraMap F (v.adicCompletion F)
            ((x.out : F) * ((residue v z).out : F) / (p : F))) := by
      rw [div_mul_cancel₀ _ hψb]
    _ = A.ψ v (algebraMap F (v.adicCompletion F)
          (((z - ((residue v z).out : F)) * (x.out : F)) / (p : F))) *
          A.ψ v (algebraMap F (v.adicCompletion F)
            ((x.out : F) * ((residue v z).out : F) / (p : F))) := by
      rw [← hdiv, ← harg]
    _ = _ := by rw [hlocal, one_mul]

private theorem rf_Wv_one_of_valuation_one (v : FinPlace F) (hv : v ∉ S.Sf)
    (ν : Fˣ) (hν : HeightOneSpectrum.valuation F v (ν : F) = 1) :
    R.T.Wv v (R.C.a v (toLoc v ν)) = 1 := by
  let u := toLoc v ν
  have hval : Valued.v (u : v.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (ν : F)) = 1
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hν]
  have hu : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
  have huinv : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one, le_refl]
  have htable := R.T.Wv_table v hv 0 u hu huinv
  simpa [u, sphericalTable] using htable

private theorem rf_Wv_nonzero_implies_integral (v : FinPlace F) (hv : v ∉ S.Sf)
    (ν : Fˣ) (hW : R.T.Wv v (R.C.a v (toLoc v ν)) ≠ 0) :
    HeightOneSpectrum.valuation F v (ν : F) ≤ 1 := by
  by_contra hnot
  have hgt : 1 < HeightOneSpectrum.valuation F v (ν : F) := lt_of_not_ge hnot
  have hval : Valued.v (toLoc v ν : v.adicCompletion F) =
      HeightOneSpectrum.valuation F v (ν : F) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (ν : F)) = _
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation']
  have hvalNe : Valued.v (toLoc v ν : v.adicCompletion F) ≠ 0 := by
    rw [hval]
    exact (v.valuation F).ne_zero_iff.mpr (Units.ne_zero ν)
  have hlog : 0 < WithZero.log (Valued.v (toLoc v ν : v.adicCompletion F)) := by
    have hh := (WithZero.log_lt_log (x := (1 : WithZero (Multiplicative ℤ)))
      one_ne_zero hvalNe).2 (by simpa [hval] using hgt)
    simpa using hh
  have hlog' : 0 < WithZero.log (HeightOneSpectrum.valuation F v (ν : F)) := by
    simpa [hval] using hlog
  have hord : ArtinPrimitiveRoots.A1.ordv v (toLoc v ν) < 0 := by
    unfold ArtinPrimitiveRoots.A1.ordv
    rw [WithZero.toAdd_unzero_eq_log hvalNe, hval]
    linarith [hlog']
  have hunit := ArtinPrimitiveRoots.A1.Theta.thFactorB_unitPart_isLocUnit v (toLoc v ν)
  have htable := R.T.Wv_table v hv (ArtinPrimitiveRoots.A1.ordv v (toLoc v ν))
      (ArtinPrimitiveRoots.A1.unitPart v (toLoc v ν)) hunit.1 hunit.2
  have hfactor := ArtinPrimitiveRoots.A1.Theta.unitPart_factor v (toLoc v ν)
  have hWtable : R.T.Wv v (R.C.a v (toLoc v ν)) =
      sphericalTable D A v (ArtinPrimitiveRoots.A1.ordv v (toLoc v ν))
        (ArtinPrimitiveRoots.A1.unitPart v (toLoc v ν)) := by
    calc
      R.T.Wv v (R.C.a v (toLoc v ν)) =
          R.T.Wv v (R.C.a v (ArtinPrimitiveRoots.A1.Theta.unifLoc v ^
            ArtinPrimitiveRoots.A1.ordv v (toLoc v ν) *
              ArtinPrimitiveRoots.A1.unitPart v (toLoc v ν))) := by
        congr 1
        rw [hfactor]
      _ = sphericalTable D A v (ArtinPrimitiveRoots.A1.ordv v (toLoc v ν))
          (ArtinPrimitiveRoots.A1.unitPart v (toLoc v ν)) := by
        simpa [ArtinPrimitiveRoots.A1.Theta.unifLoc] using htable
  have hz : sphericalTable D A v (ArtinPrimitiveRoots.A1.ordv v (toLoc v ν))
      (ArtinPrimitiveRoots.A1.unitPart v (toLoc v ν)) = 0 := by
    simp [sphericalTable, hord]
  rw [hWtable, hz] at hW
  exact hW rfl

private theorem rf_class_eq_one_of_T5_support (z : S.FSˣ)
    (hzU : z.val.1 ∈ R.T.U) : cls z = 1 := by
  classical
  have hcFin := R.T.U_spec.2.2.2.2.2.1 z.val.1 hzU
  rcases hcFin with ⟨cFinVal, hcFinVal⟩
  have hzFin (v : S.Sf) : z.val.1 v ≠ 0 := by
    have hprod := (Prod.isUnit_iff.mp z.isUnit).1
    have hpi := (Pi.isUnit_iff.mp hprod) v
    exact (isUnit_iff_ne_zero.mp hpi)
  have hcFinNe (v : S.Sf) : cFinVal v ≠ 0 := by
    intro hz
    have hpow : cFinVal v ^ 6 = z.val.1 v := by
      simpa using (congrFun hcFinVal v).symm
    apply hzFin v
    simpa [hz] using hpow.symm
  let cFinUnit : ∀ v : S.Sf, (v.1.adicCompletion F)ˣ :=
    fun v => Units.mk0 (cFinVal v) (hcFinNe v)
  choose cArchVal hcArchVal using fun w : InfinitePlace F =>
    IsAlgClosed.exists_pow_nat_eq (z.val.2 w) (by norm_num : 0 < 6)
  have hzArch (w : InfinitePlace F) : z.val.2 w ≠ 0 := by
    have hprod := (Prod.isUnit_iff.mp z.isUnit).2
    have hpi := (Pi.isUnit_iff.mp hprod) w
    exact (isUnit_iff_ne_zero.mp hpi)
  have hcArchNe (w : InfinitePlace F) : cArchVal w ≠ 0 := by
    intro hz
    have hpow := hcArchVal w
    apply hzArch w
    simpa [hz] using hpow.symm
  let cArchUnit : ∀ w : InfinitePlace F, ℂˣ :=
    fun w => Units.mk0 (cArchVal w) (hcArchNe w)
  let c : S.FSˣ := {
    val := (fun v => (cFinUnit v : v.1.adicCompletion F),
      fun w => (cArchUnit w : ℂ))
    inv := (fun v => ((cFinUnit v)⁻¹ : v.1.adicCompletion F),
      fun w => ((cArchUnit w)⁻¹ : ℂ))
    val_inv := by
      ext v
      · exact congrArg (fun x => x.toCompletion) (Units.val_inv (cFinUnit v))
      · exact Units.val_inv (cArchUnit v)
    inv_val := by
      ext v
      · exact congrArg (fun x => x.toCompletion) (Units.inv_val (cFinUnit v))
      · exact Units.inv_val (cArchUnit v)
  }
  have hcPow : c ^ (6 : ℕ) = z := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val]
    ext v
    · exact congrArg (fun x => x.toCompletion) ((congrFun hcFinVal v).symm)
    · simpa [c, cArchUnit] using hcArchVal v
  change (QuotientGroup.mk z : S.V) = 1
  rw [QuotientGroup.eq_one_iff]
  change z ∈ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range
  exact MonoidHom.mem_range.mpr ⟨c, hcPow⟩

/-- rf:forward-frequencies, 04:244–271: the B-class condition is after the B cutoff.
An unweighted Fourier coefficient need not have an allowed frequency. -/
theorem rf_forward_frequencies :
  (∀ r ν y, forwardTerm R r ν y ≠ 0 →
    (ν : F) ∈ S.R ∧ Bd.Allowed ν ∧
    ∃ I : S.ExtIdeal, S.IsGen (ν : F) I.1 ∧ ∃ γ : Gamma S, ν = (γ.1 : Fˣ) * bc.gen I) ∧
  (∀ r ν, (ν : F) ∈ S.R →
      (∑ᶠ d : Digits R r, digitAlpha R r d *
        ∏ v : {v : FinPlace F // v ∈ R.exterior.support r.ideal},
          A.ψ v.1 (algebraMap F _ ((ν : F) * algebraMap (𝓞 F) F (d v).out /
            (primeGen R v.1 : F)))) =
        ∏ v ∈ R.exterior.support r.ideal, chiPow D v (ν : F) (digitExponent r v).1) ∧
      (∀ u ν y, bCut (Bd := Bd) y * unrotated R u (S.diagU ν * y) ≠ 0 → sCocycle (D := D) (H := H) (S.diagU ν) y = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r ν y hForward
    classical
    let T0 := R.exterior.support r.ideal
    have hcut : bCut (Bd := Bd) y ≠ 0 := by
      intro hz
      apply hForward
      simp [forwardTerm, hz]
    have hsumNZ :
        (∑ᶠ d : Digits R r, digitAlpha R r d *
          R.T.W (R.chars.L (rowClass R r))
            (R.C.rat (diagGL ν) * digitPoint R r y d)) ≠ 0 := by
      intro hz
      apply hForward
      simp [forwardTerm, hz]
    letI : ∀ v : {v : FinPlace F // v ∈ T0},
        Fintype (𝓞 F ⧸ v.1.asIdeal) := fun v => bridgeResidueFintype v.1
    letI : Fintype (Digits R r) := inferInstance
    have hsome : ∃ d : Digits R r, digitAlpha R r d *
        R.T.W (R.chars.L (rowClass R r))
          (R.C.rat (diagGL ν) * digitPoint R r y d) ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hsumNZ
      rw [finsum_eq_sum_of_fintype]
      exact Finset.sum_eq_zero fun d hd => hn d
    obtain ⟨d, hdNZ⟩ := hsome
    have hW : R.T.W (R.chars.L (rowClass R r))
        (R.C.rat (diagGL ν) * digitPoint R r y d) ≠ 0 := by
      intro hz
      apply hdNZ
      rw [hz]
      simp
    let hνsupp := finitePlace_mk_hasFiniteMulSupport (x := (ν : F)) (Units.ne_zero ν)
    let V := hνsupp.toFinset
    let wbase : FinPlace F → ℂ := fun v => R.T.Wv v (R.C.a v (toLoc v ν))
    have hvaluation_one (v : FinPlace F) (hvV : v ∉ V) :
        HeightOneSpectrum.valuation F v (ν : F) = 1 := by
      have hnorm : FinitePlace.mk v (ν : F) = 1 := by
        by_contra hne
        apply hvV
        exact hνsupp.mem_toFinset.mpr (by
          simpa only [Function.mem_mulSupport] using hne)
      have hnorm' : ‖FinitePlace.embedding v (ν : F)‖ = 1 := by
        simpa only [FinitePlace.mk_apply] using hnorm
      have hnn : WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
          (HeightOneSpectrum.valuation F v (ν : F)) = 1 := by
        apply NNReal.coe_injective
        simpa only [FinitePlace.norm_embedding', NNReal.coe_one] using hnorm'
      have hq : (Ideal.absNorm v.asIdeal : NNReal) ≠ 1 := by
        intro h
        have hn : Ideal.absNorm v.asIdeal = 1 := by exact_mod_cast h
        have hlt := HeightOneSpectrum.one_lt_absNorm v
        omega
      exact (WithZeroMulInt.toNNReal_eq_one_iff _
        (HeightOneSpectrum.absNorm_ne_zero v) hq).mp hnn
    let wbaseExt : FinPlace F → ℂ := fun v => if v ∉ S.Sf then wbase v else 1
    have hwbaseFinite : (Function.mulSupport wbaseExt).Finite := by
      apply V.finite_toSet.subset
      intro v hv
      by_contra hvV
      have hnotone : wbaseExt v ≠ 1 := by
        simpa only [Function.mem_mulSupport] using hv
      by_cases hvS : v ∈ S.Sf
      · exact hnotone (by simp [wbaseExt, hvS])
      · have hwone := rf_Wv_one_of_valuation_one R v hvS ν (hvaluation_one v hvV)
        exact hnotone (by simp [wbaseExt, hvS, wbase, hwone])
    have htailEq :
        (∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T0), wbaseExt v) =
          ∏ v ∈ hwbaseFinite.toFinset with v ∉ S.Sf ∧ v ∉ T0, wbaseExt v := by
      simpa using
        (finprod_mem_eq_prod_filter wbaseExt
          {v : FinPlace F | v ∉ S.Sf ∧ v ∉ T0} hwbaseFinite)
    have htailW_eq :
        (∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T0), wbase v) =
          ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T0), wbaseExt v := by
      apply finprod_mem_congr rfl
      intro v hv
      simp [wbaseExt, hv.1]
    let g : FinPlace F → R.C.G := fun v =>
      if hv : v ∈ T0 then
        R.C.n v (Multiplicative.ofAdd (algebraMap F (v.adicCompletion F)
          (algebraMap (𝓞 F) F (d ⟨v, hv⟩).out / (primeGen R v : F))))
      else 1
    have hg : ∀ v ∈ T0, g v ∈ R.C.Gloc v := by
      intro v hv
      simp [g, hv]
      exact R.C.n_mem v _
    have hT0ext : ∀ v ∈ T0, v ∉ S.Sf :=
      fun v hv => R.exterior.support_exterior r.ideal v hv
    have hmapDigit : T0.attach.toList.map (fun v =>
        R.C.n v.1 (Multiplicative.ofAdd (algebraMap F (v.1.adicCompletion F)
          (algebraMap (𝓞 F) F (d v).out / (primeGen R v.1 : F))))) =
        T0.attach.toList.map (fun v => g v.1) := by
      apply List.map_congr_left
      intro v hv
      simp [g, v.2]
    have hperm0 : (T0.attach.toList.map Subtype.val).Perm T0.toList := by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact (T0.attach.nodup_toList).map Subtype.val_injective
      · exact T0.nodup_toList
      · ext v
        simp
    have hpermG :
        (T0.attach.toList.map (fun v => g v.1)).Perm (T0.toList.map g) := by
      change List.Perm (List.map (g ∘ Subtype.val) T0.attach.toList) (List.map g T0.toList)
      simpa only [List.map_map] using hperm0.map g
    have hpairNe : (T0.attach.toList).Pairwise (· ≠ ·) :=
      List.nodup_iff_pairwise_ne.mp T0.attach.nodup_toList
    have hpairG : (T0.attach.toList.map (fun v => g v.1)).Pairwise Commute := by
      exact List.Pairwise.map (fun v : {v // v ∈ T0} => g v.1)
        (by
          intro v w hne
          have hplaces : v.1 ≠ w.1 := by
            intro heq
            apply hne
            exact Subtype.ext heq
          exact R.C.comm_loc v.1 w.1 hplaces (g v.1) (hg v.1 v.2)
            (g w.1) (hg w.1 w.2))
        hpairNe
    have harg : R.C.rat (diagGL ν) * digitPoint R r y d =
        (R.C.rat (diagGL ν) * R.C.aS y) * (T0.toList.map g).prod := by
      rw [digitPoint, hmapDigit]
      calc
        R.C.rat (diagGL ν) * (R.C.aS y *
            (T0.attach.toList.map (fun v => g v.1)).prod) =
            (R.C.rat (diagGL ν) * R.C.aS y) *
              (T0.attach.toList.map (fun v => g v.1)).prod := by rw [mul_assoc]
        _ = _ := by rw [List.Perm.prod_eq' hpermG hpairG]
    have hFactor := R.T.factor (R.chars.L (rowClass R r))
      (R.mem_family (rowClass R r)) ν false (R.C.aS y) (R.C.aS_mem y)
      T0 hT0ext g hg
    simp only [Bool.false_eq_true, if_false, mul_one, one_mul] at hFactor
    rw [← harg] at hFactor
    have hFactor' : R.T.W (R.chars.L (rowClass R r))
        (R.C.rat (diagGL ν) * digitPoint R r y d) =
        R.T.WS (R.chars.L (rowClass R r))
            (R.C.aS (S.diagU ν) * R.C.aS y) *
          (∏ v ∈ T0, R.T.Wv v (R.C.a v (toLoc v ν) * g v)) *
          ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T0), wbase v := by
      simpa [wbase] using hFactor
    have hfactNZ : R.T.WS (R.chars.L (rowClass R r))
            (R.C.aS (S.diagU ν) * R.C.aS y) *
          (∏ v ∈ T0, R.T.Wv v (R.C.a v (toLoc v ν) * g v)) *
          (∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T0), wbase v) ≠ 0 := by
      rw [← hFactor']
      exact hW
    have htailNZ : (∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T0), wbase v) ≠ 0 := by
      intro hz
      apply hfactNZ
      rw [hz]
      simp
    have hlocalProdNZ : (∏ v ∈ T0, R.T.Wv v (R.C.a v (toLoc v ν) * g v)) ≠ 0 := by
      intro hz
      apply hfactNZ
      rw [hz]
      simp
    have hlocalNZ (v : FinPlace F) (hv : v ∈ T0) :
        R.T.Wv v (R.C.a v (toLoc v ν) * g v) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hlocalProdNZ) v hv
    have hbaseNZ_of_tail (v : FinPlace F) (hvS : v ∉ S.Sf) (hvT : v ∉ T0) :
        wbase v ≠ 0 := by
      intro hz
      have hvSupp : v ∈ hwbaseFinite.toFinset := by
        apply hwbaseFinite.mem_toFinset.mpr
        change wbaseExt v ≠ 1
        simp [wbaseExt, hvS, wbase, hz]
      have hvFiltered : v ∈ hwbaseFinite.toFinset.filter
          (fun v => v ∉ S.Sf ∧ v ∉ T0) :=
        Finset.mem_filter.mpr ⟨hvSupp, ⟨hvS, hvT⟩⟩
      have hzero : (∏ v ∈ hwbaseFinite.toFinset.filter
          (fun v => v ∉ S.Sf ∧ v ∉ T0), wbaseExt v) = 0 :=
        Finset.prod_eq_zero hvFiltered (by simp [wbaseExt, hvS, wbase, hz])
      apply htailNZ
      rw [htailW_eq, htailEq]
      exact hzero
    have hbaseNZ (v : FinPlace F) (hv : v ∉ S.Sf) : wbase v ≠ 0 := by
      by_cases hvT : v ∈ T0
      · have hloc := hlocalNZ v hvT
        have hgval : g v = R.C.n v (Multiplicative.ofAdd
            (algebraMap F (v.adicCompletion F)
              (algebraMap (𝓞 F) F (d ⟨v, hvT⟩).out / (primeGen R v : F)))) := by
          simp [g, hvT]
        have hLift : R.C.a v (toLoc v ν) * g v =
            R.C.n v (Multiplicative.ofAdd
              ((algebraMap F (v.adicCompletion F)
                (algebraMap (𝓞 F) F (d ⟨v, hvT⟩).out / (primeGen R v : F))) *
                (toLoc v ν : v.adicCompletion F))) * R.C.a v (toLoc v ν) := by
          rw [hgval]
          have h := R.C.lift_na v
            (algebraMap F (v.adicCompletion F)
              (algebraMap (𝓞 F) F (d ⟨v, hvT⟩).out / (primeGen R v : F)) *
                (toLoc v ν : v.adicCompletion F)) (toLoc v ν)
          simpa [mul_assoc] using h.symm
        have hargLocal : algebraMap F (v.adicCompletion F)
            ((ν : F) * algebraMap (𝓞 F) F (d ⟨v, hvT⟩).out /
              (primeGen R v : F)) =
            (algebraMap F (v.adicCompletion F)
                (algebraMap (𝓞 F) F (d ⟨v, hvT⟩).out /
                  (primeGen R v : F))) * (toLoc v ν : v.adicCompletion F) := by
          let a : F := algebraMap (𝓞 F) F (d ⟨v, hvT⟩).out
          let p : F := (primeGen R v : F)
          have hmapDiv : algebraMap F (v.adicCompletion F) (a / p) =
              algebraMap F (v.adicCompletion F) a /
                algebraMap F (v.adicCompletion F) p := map_div₀ _ _ _
          change algebraMap F (v.adicCompletion F) ((ν : F) * a / p) =
            algebraMap F (v.adicCompletion F) (a / p) *
              (toLoc v ν : v.adicCompletion F)
          calc
            algebraMap F (v.adicCompletion F) ((ν : F) * a / p) =
                algebraMap F (v.adicCompletion F) ((ν : F) * a) /
                  algebraMap F (v.adicCompletion F) p := map_div₀ _ _ _
            _ = (algebraMap F (v.adicCompletion F) (ν : F) *
                  algebraMap F (v.adicCompletion F) a) /
                  algebraMap F (v.adicCompletion F) p := by rw [map_mul]
            _ = algebraMap F (v.adicCompletion F) (ν : F) *
                  (algebraMap F (v.adicCompletion F) a /
                    algebraMap F (v.adicCompletion F) p) := by ring
            _ = _ := by
              rw [← hmapDiv, show (toLoc v ν : v.adicCompletion F) =
                algebraMap F (v.adicCompletion F) (ν : F) by rfl]
              ac_rfl
        have hlocEq : R.T.Wv v (R.C.a v (toLoc v ν) * g v) =
            A.ψ v (algebraMap F (v.adicCompletion F)
              ((ν : F) * algebraMap (𝓞 F) F (d ⟨v, hvT⟩).out / (primeGen R v : F))) *
              wbase v := by
          rw [hLift, ← hargLocal, R.T.Wv_equiv v hv]
        intro hz
        apply hloc
        rw [hlocEq, hz]
        simp
      · exact hbaseNZ_of_tail v hv hvT
    have hvalOutside : ∀ v : FinPlace F, v ∉ S.Sf →
        HeightOneSpectrum.valuation F v (ν : F) ≤ 1 := by
      intro v hv
      exact rf_Wv_nonzero_implies_integral R v hv ν (by simpa [wbase] using hbaseNZ v hv)
    have hR : (ν : F) ∈ S.R := by
      change ∀ v : FinPlace F, v ∉ S.Sf →
        HeightOneSpectrum.valuation F v (ν : F) ≤ 1
      exact hvalOutside
    have hWSprod : R.T.WS (R.chars.L (rowClass R r))
          (R.C.aS (S.diagU ν) * R.C.aS y) ≠ 0 := by
      intro hz
      apply hfactNZ
      rw [hz]
      simp
    let z : S.FSˣ := S.diagU ν * y
    have hWSbase : R.T.WS (R.chars.L (rowClass R r)) (R.C.aS z) ≠ 0 := by
      have hmul := R.C.aS_mul (S.diagU ν) y
      have hgen := R.T.WS_genuine (R.chars.L (rowClass R r))
        (R.mem_family (rowClass R r)) (muThree D (S.HS H (S.diagU ν) y))
        (R.C.aS z)
      rw [hmul, hgen] at hWSprod
      intro hz
      apply hWSprod
      rw [hz]
      simp
    have hT5 := R.T.T5 (R.chars.L (rowClass R r))
      (R.mem_family (rowClass R r)) z
    have hzU : z.val.1 ∈ R.T.U := by
      by_contra hout
      have hz0 : R.T.WS (R.chars.L (rowClass R r)) (R.C.aS z) = 0 := by
        rw [hT5]
        simp [hout]
      exact hWSbase (by simpa [z] using hz0)
    have hzClass := rf_class_eq_one_of_T5_support R z hzU
    have hyB : cls y ∈ Bd.B := by
      by_contra hnot
      apply hcut
      simp [bCut, hnot]
    have hclassProd : cls (S.diagU ν) * cls y = 1 := by
      simpa [cls, z] using hzClass
    have hνB : cls (S.diagU ν) ∈ Bd.B := by
      rw [mul_eq_one_iff_eq_inv.mp hclassProd]
      exact Bd.B.inv_mem hyB
    have hAllowed : Bd.Allowed ν := by
      change (QuotientGroup.mk (S.diagU ν) : S.V) ∈ Bd.B
      exact hνB
    refine ⟨hR, hAllowed, ?_⟩
    let principalCount : FinPlace F → ℤ := fun v =>
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (ν : F))
    have hcountZero (v : FinPlace F) (hvV : v ∉ V) : principalCount v = 0 := by
      dsimp [principalCount]
      rw [rf_count_spanSingleton_eq_neg_log_valuation v (ν : F) (Units.ne_zero ν),
        hvaluation_one v hvV]
      simp
    let exponentFun : FinPlace F → ℤ := fun v => if v ∉ S.Sf then principalCount v else 0
    have hexponentSupport : ∀ v, exponentFun v ≠ 0 → v ∈ V := by
      intro v hv
      by_cases hvS : v ∈ S.Sf
      · simp [exponentFun, hvS] at hv
      · by_contra hvV
        have hzero := hcountZero v hvV
        simp [exponentFun, hvS, hzero] at hv
    let exponent : FinPlace F →₀ ℤ := Finsupp.onFinset V exponentFun hexponentSupport
    have hexponent_nonneg (v : FinPlace F) : 0 ≤ exponent v := by
      rw [Finsupp.onFinset_apply]
      by_cases hvS : v ∈ S.Sf
      · simp [exponentFun, hvS]
      · have hlog : WithZero.log (HeightOneSpectrum.valuation F v (ν : F)) ≤ 0 := by
          apply (WithZero.log_le_iff_le_exp
            ((v.valuation F).ne_zero_iff.mpr (Units.ne_zero ν))).2
          simpa using hvalOutside v hvS
        change 0 ≤ exponentFun v
        simp only [exponentFun, if_pos hvS]
        dsimp [principalCount]
        rw [rf_count_spanSingleton_eq_neg_log_valuation v (ν : F) (Units.ne_zero ν)]
        linarith
    let Jfrac : FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
      exponent.prod (HeightOneSpectrum.asIdeal · ^ ·)
    have hJle : Jfrac ≤ 1 := by
      dsimp [Jfrac]
      rw [Finsupp.prod]
      apply Finset.prod_le_one
      intro v hv
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (hexponent_nonneg v)
      rw [hn, zpow_natCast]
      exact Left.pow_le_one_of_le FractionalIdeal.coeIdeal_le_one _
    have hJne : Jfrac ≠ 0 := by
      dsimp [Jfrac]
      rw [Finsupp.prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro v hv
      exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
    have hcountJ (v : FinPlace F) : FractionalIdeal.count F v Jfrac = exponent v := by
      simpa [Jfrac] using FractionalIdeal.count_finsuppProd F v exponent
    obtain ⟨I, hIco⟩ := (FractionalIdeal.le_one_iff_exists_coeIdeal).mp hJle
    have hIne : I ≠ ⊥ := by
      intro h
      apply hJne
      rw [← hIco, h, FractionalIdeal.coeIdeal_bot]
    have hIexterior : S.IsExterior I := by
      refine ⟨hIne, ?_⟩
      intro v hvS hle
      have hleFrac : Jfrac ≤ (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
        rw [← hIco]
        exact (FractionalIdeal.coeIdeal_le_coeIdeal F).2 hle
      have hmono := FractionalIdeal.count_mono (K := F) (v := v) hJne hleFrac
      have hexpZero : exponent v = 0 := by
        simp [exponent, exponentFun, hvS]
      have hbad : (1 : ℤ) ≤ 0 := by
        calc
          1 = FractionalIdeal.count F v
              (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
            (FractionalIdeal.count_self F v).symm
          _ ≤ FractionalIdeal.count F v Jfrac := hmono
          _ = exponent v := hcountJ v
          _ = 0 := hexpZero
      norm_num at hbad
    have hgenI : S.IsGen (ν : F) I := by
      refine ⟨hIexterior, Units.ne_zero ν, ?_⟩
      intro v hvS
      have hexp : exponent v = principalCount v := by
        simp [exponent, exponentFun, hvS]
      calc
        FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (ν : F)) =
            principalCount v := rfl
        _ = exponent v := hexp.symm
        _ = FractionalIdeal.count F v Jfrac := (hcountJ v).symm
        _ = FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
          rw [← hIco]
    let Iext : S.ExtIdeal := ⟨I, hIexterior⟩
    have hgenChoice := bc.gen_spec Iext
    obtain ⟨ε, hε, hEq⟩ := Bd.allowed_unique I (ν : Fˣ) (bc.gen Iext)
      ⟨hgenI, hνB⟩ hgenChoice
    let εUS : S.US := ⟨ε, hε⟩
    have hγmem : εUS ^ 6 ∈ Gamma S := by
      change εUS ^ 6 ∈ (sixthPowerOnUS S).range
      exact MonoidHom.mem_range.mpr ⟨εUS, rfl⟩
    let γ : Gamma S := ⟨εUS ^ 6, hγmem⟩
    refine ⟨Iext, hgenI, γ, ?_⟩
    simpa [γ] using hEq
  · intro r ν hν
    classical
    change ∀ v : FinPlace F, v ∉ S.Sf →
      HeightOneSpectrum.valuation F v (ν : F) ≤ 1 at hν
    let V := {v : FinPlace F // v ∈ R.exterior.support r.ideal}
    letI : ∀ v : V, Fintype (𝓞 F ⧸ v.1.asIdeal) := fun v => bridgeResidueFintype v.1
    letI : Fintype (Digits R r) := inferInstance
    have hvOut (v : V) : v.1 ∉ S.Sf :=
      R.exterior.support_exterior r.ideal v.1 v.2
    have hpgen (v : V) :
        S.IsGen (primeGen R v.1 : F) v.1.asIdeal ∧ Bd.Allowed (primeGen R v.1) := by
      have hgen := bc.gen_spec (R.exterior.prime v.1 (hvOut v))
      simpa [primeGen, hvOut v, R.exterior.prime_val] using hgen
    have hphase (v : V) (d : 𝓞 F ⧸ v.1.asIdeal) :
        A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
          ((ν : F) * algebraMap (𝓞 F) F d.out / (primeGen R v.1 : F))) =
        maskPhase A v.1 (primeGen R v.1) (residue v.1 (ν : F)) d := by
      unfold maskPhase
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (rf_local_phase_eq_residue v.1 (hvOut v) (primeGen R v.1) (hpgen v).1
          (ν : F) (hν v.1 (hvOut v)) d)
    have hlocal (v : V) :
        (∑ᶠ d : 𝓞 F ⧸ v.1.asIdeal, maskAlpha D A v.1 (primeGen R v.1)
          (digitExponent r v.1) d *
          A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
            ((ν : F) * algebraMap (𝓞 F) F d.out / (primeGen R v.1 : F)))) =
          chiPow D v.1 (ν : F) (digitExponent r v.1).1 := by
      let t := residue v.1 (ν : F)
      have htAlg : residue v.1 (algebraMap (𝓞 F) F t.out) = t := by
        simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v.1 t.out
      have hres : residue v.1 (ν : F) =
          residue v.1 (algebraMap (𝓞 F) F t.out) := by
        rw [show residue v.1 (ν : F) = t by rfl, htAlg]
      have hchi : chiPow D v.1 (ν : F) (digitExponent r v.1).1 =
          chiPow D v.1 (algebraMap (𝓞 F) F t.out) (digitExponent r v.1).1 := by
        have hchiRaw := (a2_bridge_SYMBOL D S).chi_congr v.1 (ν : F)
          (algebraMap (𝓞 F) F t.out) hres
        unfold chiPow
        rw [hres]
        by_cases hz : residue v.1 (algebraMap (𝓞 F) F t.out) = 0
        · simp [hz]
        · simp [hz, hchiRaw]
      have hmask := rf_mask_identity D S H Bd A v.1 (hvOut v)
        (primeGen R v.1) (hpgen v) (digitExponent r v.1) t
      calc
        _ = ∑ᶠ d : 𝓞 F ⧸ v.1.asIdeal, maskAlpha D A v.1 (primeGen R v.1)
              (digitExponent r v.1) d * maskPhase A v.1 (primeGen R v.1) t d := by
          apply finsum_congr
          intro d
          rw [hphase v d]
        _ = chiPow D v.1 (algebraMap (𝓞 F) F t.out) (digitExponent r v.1).1 := hmask
        _ = chiPow D v.1 (ν : F) (digitExponent r v.1).1 := hchi.symm
    have hterm (d : Digits R r) :
        digitAlpha R r d *
            ∏ v : V, A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
              ((ν : F) * algebraMap (𝓞 F) F (d v).out / (primeGen R v.1 : F))) =
          ∏ v : V, maskAlpha D A v.1 (primeGen R v.1)
            (digitExponent r v.1) (d v) *
              A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
                ((ν : F) * algebraMap (𝓞 F) F (d v).out / (primeGen R v.1 : F))) := by
      classical
      change (∏ v ∈ (Finset.univ : Finset V),
            maskAlpha D A v.1 (primeGen R v.1) (digitExponent r v.1) (d v)) *
          ∏ v ∈ (Finset.univ : Finset V),
            A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
              ((ν : F) * algebraMap (𝓞 F) F (d v).out / (primeGen R v.1 : F))) =
        ∏ v ∈ (Finset.univ : Finset V),
          maskAlpha D A v.1 (primeGen R v.1) (digitExponent r v.1) (d v) *
            A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
              ((ν : F) * algebraMap (𝓞 F) F (d v).out / (primeGen R v.1 : F)))
      rw [← Finset.prod_mul_distrib (s := Finset.univ)]
    have hprod :
        (∑ᶠ d : Digits R r, digitAlpha R r d *
          ∏ v : V, A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
            ((ν : F) * algebraMap (𝓞 F) F (d v).out / (primeGen R v.1 : F)))) =
        ∏ v : V, chiPow D v.1 (ν : F) (digitExponent r v.1).1 := by
      calc
        _ = ∑ d : Digits R r, digitAlpha R r d *
              ∏ v : V, A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
                ((ν : F) * algebraMap (𝓞 F) F (d v).out / (primeGen R v.1 : F))) :=
          finsum_eq_sum_of_fintype _
        _ = ∑ d : Digits R r, ∏ v : V,
              maskAlpha D A v.1 (primeGen R v.1) (digitExponent r v.1) (d v) *
                A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
                  ((ν : F) * algebraMap (𝓞 F) F (d v).out / (primeGen R v.1 : F))) := by
          apply Finset.sum_congr rfl
          intro d hd
          exact hterm d
        _ = ∏ v : V, ∑ d : 𝓞 F ⧸ v.1.asIdeal,
              maskAlpha D A v.1 (primeGen R v.1) (digitExponent r v.1) d *
                A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
                  ((ν : F) * algebraMap (𝓞 F) F d.out / (primeGen R v.1 : F))) := by
          let f : ∀ v : V, (𝓞 F ⧸ v.1.asIdeal) → ℂ := fun v d =>
            maskAlpha D A v.1 (primeGen R v.1) (digitExponent r v.1) d *
              A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
                ((ν : F) * algebraMap (𝓞 F) F d.out / (primeGen R v.1 : F)) )
          have hprodSum : (∏ v : V, ∑ d : 𝓞 F ⧸ v.1.asIdeal, f v d) =
              ∑ d : Digits R r, ∏ v : V, f v (d v) := Fintype.prod_sum f
          simpa [f] using hprodSum.symm
        _ = ∏ v : V, ∑ᶠ d : 𝓞 F ⧸ v.1.asIdeal,
              maskAlpha D A v.1 (primeGen R v.1) (digitExponent r v.1) d *
                A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
                  ((ν : F) * algebraMap (𝓞 F) F d.out / (primeGen R v.1 : F))) := by
          simp only [finsum_eq_sum_of_fintype]
        _ = ∏ v : V, chiPow D v.1 (ν : F) (digitExponent r v.1).1 := by
          apply Finset.prod_congr rfl
          intro v hv
          exact hlocal v
    calc
      (∑ᶠ d : Digits R r, digitAlpha R r d *
          ∏ v : V, A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
            ((ν : F) * algebraMap (𝓞 F) F (d v).out / (primeGen R v.1 : F)))) =
        ∏ v : V, chiPow D v.1 (ν : F) (digitExponent r v.1).1 := hprod
      _ = ∏ v ∈ R.exterior.support r.ideal, chiPow D v (ν : F) (digitExponent r v).1 := by
        simpa [V] using (Finset.prod_attach (R.exterior.support r.ideal)
          (fun v : FinPlace F => chiPow D v (ν : F) (digitExponent r v).1))
  · intro u ν y hne
    have hb : bCut (Bd := Bd) y ≠ 0 := by
      intro hz
      apply hne
      simp [hz]
    have hUrot : unrotated R u (S.diagU ν * y) ≠ 0 := by
      intro hz
      apply hne
      simp [hz]
    have hsc : sCocycle (D := D) (H := H) (S.diagU ν) y ≠ 0 := by
      unfold sCocycle
      apply pow_ne_zero
      have hHS : ((S.HS H (S.diagU ν) y : Fˣ) : F) ≠ 0 := Units.ne_zero _
      intro hz
      exact hHS (D.σ0.injective (by simpa using hz))
    have hfac : R.T.WS (R.chars.L u)
        (R.C.aS (S.diagU ν) * R.C.aS y) =
          sCocycle (D := D) (H := H) (S.diagU ν) y *
            unrotated R u (S.diagU ν * y) := by
      rw [R.C.aS_mul]
      rw [R.T.WS_genuine (R.chars.L u) (R.mem_family u)]
      simp [sCocycle, unrotated, muThree, map_pow]
    have hWSprod : R.T.WS (R.chars.L u)
        (R.C.aS (S.diagU ν) * R.C.aS y) ≠ 0 := by
      rw [hfac]
      exact mul_ne_zero hsc hUrot
    have hWSbase : R.T.WS (R.chars.L u)
        (R.C.aS (S.diagU ν * y)) ≠ 0 := by
      have hmul := R.C.aS_mul (S.diagU ν) y
      have hgen := R.T.WS_genuine (R.chars.L u) (R.mem_family u)
        (muThree D (S.HS H (S.diagU ν) y)) (R.C.aS (S.diagU ν * y))
      rw [hmul, hgen] at hWSprod
      have hζ : (((muThree D (S.HS H (S.diagU ν) y) : rootsOfUnity 3 ℂ) : ℂˣ) : ℂ) ≠ 0 :=
        Units.ne_zero _
      intro hz
      apply hWSprod
      rw [hz]
      simp
    let z : S.FSˣ := S.diagU ν * y
    have hT5 := R.T.T5 (R.chars.L u) (R.mem_family u) z
    have hzU : z.val.1 ∈ R.T.U := by
      by_contra hout
      have hz0 : R.T.WS (R.chars.L u) (R.C.aS z) = 0 := by
        rw [hT5]
        simp [hout]
      exact hWSbase (by simpa [z] using hz0)
    have hbClass : cls y ∈ Bd.B := by
      by_contra hnot
      apply hb
      simp [bCut, hnot]
    have hcFin := R.T.U_spec.2.2.2.2.2.1 z.val.1 hzU
    rcases hcFin with ⟨cFinVal, hcFinVal⟩
    have hzFin (v : S.Sf) : z.val.1 v ≠ 0 := by
      have hprod := (Prod.isUnit_iff.mp z.isUnit).1
      have hpi := (Pi.isUnit_iff.mp hprod) v
      exact (isUnit_iff_ne_zero.mp hpi)
    have hcFinNe (v : S.Sf) : cFinVal v ≠ 0 := by
      intro hz
      have hpow : cFinVal v ^ 6 = z.val.1 v := by
        simpa using (congrFun hcFinVal v).symm
      apply hzFin v
      simpa [hz] using hpow.symm
    let cFinUnit : ∀ v : S.Sf, (v.1.adicCompletion F)ˣ :=
      fun v => Units.mk0 (cFinVal v) (hcFinNe v)
    choose cArchVal hcArchVal using fun w : InfinitePlace F =>
      IsAlgClosed.exists_pow_nat_eq (z.val.2 w) (by norm_num : 0 < 6)
    have hzArch (w : InfinitePlace F) : z.val.2 w ≠ 0 := by
      have hprod := (Prod.isUnit_iff.mp z.isUnit).2
      have hpi := (Pi.isUnit_iff.mp hprod) w
      exact (isUnit_iff_ne_zero.mp hpi)
    have hcArchNe (w : InfinitePlace F) : cArchVal w ≠ 0 := by
      intro hz
      have hpow := hcArchVal w
      apply hzArch w
      simpa [hz] using hpow.symm
    let cArchUnit : ∀ w : InfinitePlace F, ℂˣ :=
      fun w => Units.mk0 (cArchVal w) (hcArchNe w)
    let c : S.FSˣ := {
      val := (fun v => (cFinUnit v : v.1.adicCompletion F),
        fun w => (cArchUnit w : ℂ))
      inv := (fun v => ((cFinUnit v)⁻¹ : v.1.adicCompletion F),
        fun w => ((cArchUnit w)⁻¹ : ℂ))
      val_inv := by
        ext v
        · exact congrArg (fun x => x.toCompletion) (Units.val_inv (cFinUnit v))
        · exact Units.val_inv (cArchUnit v)
      inv_val := by
        ext v
        · exact congrArg (fun x => x.toCompletion) (Units.inv_val (cFinUnit v))
        · exact Units.inv_val (cArchUnit v)
    }
    have hcPow : c ^ (6 : ℕ) = z := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val]
      ext v
      · exact congrArg (fun x => x.toCompletion) ((congrFun hcFinVal v).symm)
      · simpa [c, cArchUnit] using hcArchVal v
    have hzClass : cls z = 1 := by
      change (QuotientGroup.mk z : S.V) = 1
      rw [QuotientGroup.eq_one_iff]
      change z ∈ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range
      exact MonoidHom.mem_range.mpr ⟨c, hcPow⟩
    have hclassProd : cls (S.diagU ν) * cls y = 1 := by
      simpa [cls, z] using hzClass
    have hνClass : cls (S.diagU ν) = (cls y)⁻¹ := by
      exact (mul_eq_one_iff_eq_inv.mp hclassProd)
    have hνB : cls (S.diagU ν) ∈ Bd.B := by
      rw [hνClass]
      exact Bd.B.inv_mem hbClass
    have hHS := Bd.isotropic (S.diagU ν) y hνB hbClass
    simp [sCocycle, hHS]
/-- rf:forward-unfolding, 04:272–301. Integrability accompanies equalities to avoid total-integral traps. -/
theorem rf_forward_unfolding :
  ∀ σ : ℝ, 1 / 2 < σ → ∃ C : ℝ, 0 < C ∧ ∀ u (I : S.ExtIdeal) l, 0 < l →
    let a := S.diagU (bc.gen I)
    let f := fun γ : Gamma S => fun y : S.FSˣ => unrotated R u (S.diagU (γ.1 : Fˣ) * a * y)
    (∀ γ, IntegrableOn (onUnits (f γ)) (omegaAt R l) (R.sheets.sheet l)) ∧
    Summable (fun γ => (omegaInt R l (fun y => (‖f γ y‖ : ℂ))).re) ∧
    (∑' γ, (omegaInt R l (fun y => (‖f γ y‖ : ℂ))).re) =
      (sheetIntegral R (qI I.1 * l) (fun y => (‖unrotated R u y‖ : ℂ))).re ∧
    (sheetIntegral R (qI I.1 * l) (fun y => (‖unrotated R u y‖ : ℂ))).re ≤
      C * (qI I.1 * l) ^ (-σ) ∧
    Summable (fun γ => omegaInt R l (fun y => bCut (Bd := Bd) y * (Lvalue R u y)⁻¹ * f γ y)) ∧
    (∑' γ, omegaInt R l (fun y => bCut (Bd := Bd) y * (Lvalue R u y)⁻¹ * f γ y)) =
      Lvalue R u a * Theta.thetaV S μ v0 R.T.U R.T.cS (qI I.1 * l) := by
  sorry
def cgen (c : S.SqfExtIdeal) : F := (bc.gen (R.exterior.ofSqf c) : F)

/-- The setup already records balanced generators, so the `cgen` witness required by the
reflection consumer is a proved projection (04:1198-1228). -/
theorem cgen_valid : ∀ I : S.SqfExtIdeal, ∃ c : Fˣ,
    (c : F) = cgen R I ∧ S.IsGen (c : F) I.1 ∧ Bd.Allowed c := by
  intro I
  refine ⟨bc.gen (R.exterior.ofSqf I), rfl, ?_, (bc.gen_spec _).2⟩
  simpa only [R.exterior.ofSqf_val] using (bc.gen_spec (R.exterior.ofSqf I)).1
def Aideal (c : S.SqfExtIdeal) (n : S.ExtIdeal) : S.ExtIdeal :=
  R.exterior.mul (R.exterior.ofSqf c) (R.exterior.pow n 3)
def Agen (c : S.SqfExtIdeal) (n : S.ExtIdeal) : Fˣ := bc.gen (R.exterior.ofSqf c) * bc.gen n ^ 3

def forwardCoeff (r : ReflectionRow S) (p : S.SqfExtIdeal × S.ExtIdeal) : ℂ :=
  gamma D S A 2 p.1.1 (cgen R p.1) * (qI p.1.1 ^ (-(1 / 2 : ℝ)) / qI p.2.1 : ℝ) *
    Lvalue R (rowClass R r) (S.diagU (Agen R p.1 p.2)) *
      ∏ v ∈ R.exterior.support r.ideal,
        chiPow D v (Agen R p.1 p.2 : F) (digitExponent r v).1

def sphericalMajorant (σ : ℝ) : ℝ :=
  ∑' p : S.SqfExtIdeal × S.ExtIdeal, qI p.1.1 ^ (-1 / 2 - σ) * qI p.2.1 ^ (-1 - 3 * σ)

/-- rf:forward-assembly, 04:303–327. Constants fixed before l,Z,r; pre-digit cost remains row-dependent. -/
theorem rf_forward_assembly :
  (∀ v, v ∉ S.Sf → ∀ j : Fin 6,
    let mass := ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, ‖maskAlpha D A v (primeGen R v) j x‖
    (j ≠ 0 → mass ≤ (qI v.asIdeal) ^ (1 / 2 : ℝ)) ∧ (j = 0 → mass < 2)) ∧
  ∀ σ : ℝ, 1 / 2 < σ →
    Summable (fun p : S.SqfExtIdeal × S.ExtIdeal => qI p.1.1 ^ (-1 / 2 - σ) * qI p.2.1 ^ (-1 - 3 * σ)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ r Z, 0 < Z →
      IntegrableOn (fun t : ℝ => ‖R.K t‖ *
        (∑' p : S.SqfExtIdeal × S.ExtIdeal, ‖forwardCoeff R r p *
          Theta.thetaV S μ v0 R.T.U R.T.cS (qI (Aideal R p.1 p.2).1 * t / Z)‖) / t) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0 : ℝ), ‖R.K t‖ *
        (∑' p : S.SqfExtIdeal × S.ExtIdeal, ‖forwardCoeff R r p *
          Theta.thetaV S μ v0 R.T.U R.T.cS (qI (Aideal R p.1 p.2).1 * t / Z)‖) / t) ≤
        C * Z ^ σ * Theta.absMoment R.K (-σ) * sphericalMajorant (S := S) σ := by
  sorry
/-- lem:reflection-theta-representation, 04:222–328: both series and averaged integral are absolute. -/
theorem lem_reflection_theta_representation :
  ∀ r l Z, 0 < l → 0 < Z →
    let term := fun p : S.SqfExtIdeal × S.ExtIdeal => forwardCoeff R r p *
      Theta.thetaV S μ v0 R.T.U R.T.cS (qI (Aideal R p.1 p.2).1 * l)
    Summable (fun p => ‖term p‖) ∧ thetaAverage R r l = ∑' p, term p ∧
    IntegrableOn (fun t => R.K t * thetaAverage R r (t / Z) / (t : ℂ)) (Set.Ioi 0) ∧
    Bm D S A ϑ (cgen R) (r.m : F) Z =
      ∫ t in Set.Ioi (0 : ℝ), R.K t * thetaAverage R r (t / Z) / (t : ℂ) := by
  sorry
/-- lem:reflection-local-Weyl, 04:339–431. Use actual local units, not arbitrary elements. -/
def localR (v : FinPlace F) (j : Fin 6) (e : ℤ) (t : (v.adicCompletion F)ˣ) : ℂ :=
  ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
    maskAlpha D A v (primeGen R v) j x *
      R.T.Wv v (R.C.a v (toLoc v (primeGen R v) ^ (e - 2) * t) * R.C.w v *
        R.C.n v (Multiplicative.ofAdd (algebraMap F _
          (algebraMap (𝓞 F) F x.out / (primeGen R v : F)))))

def localW (v : FinPlace F) (e : ℤ) : ℂ := R.T.Wv v (R.C.a v (toLoc v (primeGen R v) ^ e))
def localOmega (v : FinPlace F) : ℂ :=
  (∑ᶠ x : 𝓞 F ⧸ v.asIdeal, chiPow D v (algebraMap (𝓞 F) F x.out) 3 *
    A.ψ v (algebraMap F _ (algebraMap (𝓞 F) F x.out / (primeGen R v : F)))) /
      maskTau D A v (primeGen R v) 1

def localB (j : Fin 6) (e : ℕ) : ℤ := if e = 0 then 8 - (j.1 : ℤ) else 4 + 2 * (e : ℤ)

/-- lem:reflection-local-Weyl, 04:339-431. The three power ranges and zero digit are separate. -/
theorem lem_reflection_local_Weyl :
  ∀ v, v ∉ S.Sf → ∀ j : Fin 6, ∀ e : ℤ, ∀ t : (v.adicCompletion F)ˣ,
    (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    (e < 0 → localR R v j e t = 0) ∧
    (0 ≤ e → localR R v j e t = localW R v e * localChi D v t ^ (4 + 2 * e) *
      ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
        maskAlpha D A v (primeGen R v) j x * chi D v (algebraMap (𝓞 F) F x.out) ^ 4 *
          A.ψ v (((toLoc v (primeGen R v) ^ (e - 1) * t : (v.adicCompletion F)ˣ) : _) /
            algebraMap F _ (algebraMap (𝓞 F) F x.out))) ∧
    (j = 1 → 0 < e → localR R v j e t = 0) ∧
    (j = 1 → e = 0 → localR R v j e t = localOmega R v * localChi D v t) ∧
    ‖localOmega R v‖ = 1 ∧ ‖localR R v j 0 t‖ ≤ 1 ∧
    (0 < e → ‖localR R v j e t‖ ≤ qI v.asIdeal ^ (1 / 2 : ℝ) * ‖localW R v e‖) ∧
    (0 ≤ e → localR R v j e t = localR R v j e 1 * localChi D v t ^ localB j e.toNat) ∧
    (0 < e → j ≠ 4 → localR R v j e 1 = 0) ∧
    (0 ≤ e → e % 3 = 2 → localR R v j e 1 = 0) := by
  sorry
/-- lem:reflection-local-Weyl, 04:339-431. The zero residue has its own masked value. -/
theorem rf_local_zero_digit : ∀ v, v ∉ S.Sf → ∀ ν : Fˣ,
  maskAlpha D A v (primeGen R v) 0 0 * R.T.Wv v (R.C.a v (toLoc v ν) * R.C.w v) =
    (1 - (qI v.asIdeal : ℂ)⁻¹) * R.T.Wv v (R.C.a v (toLoc v ν)) := by
  sorry
/-- def:rf-active: ideal support and inactive scalar, completing the old partial node. -/
def activeFactor (h f : S.ExtIdeal) : Prop :=
  Squarefree f.1 ∧ (∀ v ∈ R.exterior.support f, v ∈ R.exterior.support h) ∧
    ∀ v ∈ R.exterior.support h, idealExp v h.1 % 6 ≠ 0 → v ∈ R.exterior.support f

def activeNumerator (f a : S.ExtIdeal) : Prop :=
  (∀ v ∈ R.exterior.support a, v ∈ R.exterior.support f) ∧
    ∀ v ∈ R.exterior.support f, idealExp v a.1 % 3 = 0 ∨ idealExp v a.1 % 3 = 1

def inactiveScalar (h f : S.ExtIdeal) : ℂ :=
  ((R.exterior.support h).filter (fun v => v ∉ R.exterior.support f)).prod
    (fun v : FinPlace F => 1 - (qI v.asIdeal : ℂ)⁻¹)

theorem qI_prime_gt_one (v : FinPlace F) : 1 < qI v.asIdeal := by
  dsimp [qI]
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

def betaIdeal (f a : S.ExtIdeal) : ℝ :=
  ∏ v ∈ R.exterior.support f, betaPrime (qI v.asIdeal) (qI_prime_gt_one v) (idealExp v a.1)
def Eprime (v : FinPlace F) (σ : ℝ) : ℝ :=
  ∑' e : ℕ, betaPrime (qI v.asIdeal) (qI_prime_gt_one v) e * qI v.asIdeal ^ (-σ * (e : ℝ))
def Eideal (f : S.ExtIdeal) (σ : ℝ) : ℝ := ∏ v ∈ R.exterior.support f, Eprime v σ

/-- rf:active-support, 04:433-503. Prime support and norm bounds use one uniform exponent range. -/
theorem rf_active_support_bounds :
  (∀ h f, IsPowerful h.1 → activeFactor R h f → (qI f.1) ^ 2 ≤ qI h.1) ∧
  (∀ v, v ∉ S.Sf → ∀ j : Fin 6, ∀ e : ℕ,
    ‖localR R v j e 1‖ ≤ betaPrime (qI v.asIdeal) (qI_prime_gt_one v) e) ∧
  (∀ v, v ∉ S.Sf → ∀ σ, 0 ≤ σ →
    Summable (fun e : ℕ => betaPrime (qI v.asIdeal) (qI_prime_gt_one v) e *
      qI v.asIdeal ^ (-σ * (e : ℝ))) ∧
    Eprime v σ = 1 + (qI v.asIdeal ^ (-σ) + qI v.asIdeal ^ (-1 / 2 - 3 * σ)) /
      (1 - qI v.asIdeal ^ (-1 - 3 * σ)) ∧ Eprime v σ ≤ 3 + Real.sqrt 2) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ h σ, 0 ≤ σ →
    (∑ᶠ f : {f : S.ExtIdeal // Squarefree f.1 ∧
      ∀ v ∈ R.exterior.support f, v ∈ R.exterior.support h}, Eideal R f.1 σ) ≤ C * qI h.1 ^ ε := by
  sorry
/-- def:rf-profiles, 04:507–534. The multiplier has the positive L exponent. -/
def profileH (u : UnitSix S) (κ : S.V) (ℓ : Fin (R.rotated u).J) (x : ℝ) : ℂ :=
  sheetIntegral R x (fun y => (if κ * (cls y)⁻¹ ∈ Bd.B then 1 else 0) *
    R.pairing.pair κ (cls y) ^ 2 * Lvalue R u y *
      (∏ v : S.Sf, (R.rotated u).ff ℓ v ((y : S.FS).1 v)) *
      ∏ w : InfinitePlace F, (R.rotated u).fc ℓ w ((y : S.FS).2 w))

def profilePhiTerm (u : UnitSix S) (κ : S.V) (ℓ : Fin (R.rotated u).J) (x : ℝ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), R.K t * profileH R u κ ℓ (x / t) / (t : ℂ)
def profilePhi (u : UnitSix S) (κ : S.V) (x : ℝ) : ℂ :=
  ∑ ℓ : Fin (R.rotated u).J, profilePhiTerm R u κ ℓ x

def rotatedAbs (u : UnitSix S) (y : S.FSˣ) : ℝ :=
  ∑ ℓ : Fin (R.rotated u).J, (∏ v : S.Sf, ‖(R.rotated u).ff ℓ v ((y : S.FS).1 v)‖) *
    ∏ w : InfinitePlace F, ‖(R.rotated u).fc ℓ w ((y : S.FS).2 w)‖
def profileAbs (u : UnitSix S) (x : ℝ) : ℝ :=
  (sheetIntegral R x (fun y => (rotatedAbs R u y : ℂ))).re

/-- rf:profile-bound, 04:535–548, including smoothness needed by Fourier separation. -/
theorem rf_profile_bound :
  (∀ u κ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (profilePhi R u κ) (Set.Ioi 0)) ∧
  (∃ α : ℝ, 0 < α ∧ ∀ N : ℝ, 0 < N → ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ u κ x, 0 < x → ‖Theta.normDerivR j (profilePhi R u κ) x‖ ≤ C * min (x ^ α) (x ^ (-N))) ∧
  ∀ σ : ℝ, 1 / 2 < σ → ∃ C : ℝ, 0 < C ∧ ∀ u x, 0 < x → profileAbs R u x ≤ C * x ^ (-σ) := by
  sorry
/-- def:rf-frozen-factors, 04:550–623. Frequency unit and row unit are distinct indices. -/
structure FrozenIndex (h : S.ExtIdeal) where
  f : S.ExtIdeal
  a : S.ExtIdeal
  n : S.ExtIdeal
  u : UnitSix S
  active : activeFactor R h f
  numerator : activeNumerator R f a
  coprime : IsCoprime n.1 f.1

variable {R}
def frozenJ {h : S.ExtIdeal} (_t : FrozenIndex R h) (v : FinPlace F) : Fin 6 :=
  ⟨idealExp v h.1 % 6, Nat.mod_lt _ (by norm_num)⟩
def frozenB {h : S.ExtIdeal} (t : FrozenIndex R h) (v : FinPlace F) : ℤ := localB (frozenJ t v) (idealExp v t.a.1)
variable (R)

def kappaSix {h : S.ExtIdeal} (t : FrozenIndex R h) (sd sc : Bd.B) : S.V :=
  cls (S.diagU (R.sheets.eps t.u)) * cls (S.diagU (bc.gen t.a)) * sc.1 *
    cls (S.diagU (bc.gen t.n)) ^ 3 * sd.1 ^ (-2 : ℤ) * cls (S.diagU (bc.gen t.f)) ^ (-2 : ℤ)

def frozenOmega (υ : UnitSix S) {h : S.ExtIdeal} (t : FrozenIndex R h) : ℂ :=
  inactiveScalar R h t.f * (Lvalue R υ (S.diagU (bc.gen t.a)))⁻¹ *
    Lvalue R υ (S.diagU (bc.gen t.n)) ^ (-3 : ℤ) * Lvalue R υ (S.diagU (bc.gen t.f)) ^ 2 *
      ∏ v ∈ R.exterior.support t.f,
        localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
          chi D v (((R.sheets.eps t.u : Fˣ) : F) *
            (bc.gen t.a : F) / (primeGen R v : F) ^ idealExp v t.a.1 *
              (bc.gen t.n : F) ^ 3 * ((bc.gen t.f : F) / (primeGen R v : F)) ^ (-2 : ℤ)) ^ frozenB t v

def frozenRho (υ : UnitSix S) {h : S.ExtIdeal} (t : FrozenIndex R h) (sd : Bd.B) (d : S.ExtIdeal) : ℂ :=
  if Squarefree d.1 ∧ IsCoprime d.1 (h.1 * t.n.1) ∧ cls (S.diagU (bc.gen d)) = sd.1 then
    Lvalue R υ (S.diagU (bc.gen d)) ^ 2 *
      (∏ v ∈ R.exterior.support d, localOmega R v * chi D v
        (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) * (bc.gen t.n : F) ^ 3 *
          ((bc.gen d : F) / (primeGen R v : F)) ^ (-2 : ℤ) * (bc.gen t.f : F) ^ (-2 : ℤ))) *
      ∏ v ∈ R.exterior.support t.f, chi D v (bc.gen d : F) ^ (-2 * frozenB t v)
  else 0

def frozenLambda (υ : UnitSix S) {h : S.ExtIdeal} (t : FrozenIndex R h) (sc : Bd.B) (c : S.SqfExtIdeal) : ℂ :=
  if IsCoprime c.1 t.f.1 ∧ cls (S.diagU (bc.gen (R.exterior.ofSqf c))) = sc.1 then
    (Lvalue R υ (S.diagU (bc.gen (R.exterior.ofSqf c))))⁻¹ *
      (∏ v ∈ R.exterior.support t.f, chi D v (cgen R c) ^ frozenB t v) *
      ∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
        gamma D S A 2 v.asIdeal (primeGen R v : F) * chi D v
          (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) *
            (cgen R c / (primeGen R v : F)) * (bc.gen t.f : F) ^ (-2 : ℤ)) ^ 2
  else 0

/-- Exact frequency in 04:708–802. -/
def frozenFrequency {h : S.ExtIdeal} (t : FrozenIndex R h) (d : S.ExtIdeal) (c : S.SqfExtIdeal) : Fˣ :=
  (R.sheets.eps t.u : Fˣ) * bc.gen t.a * bc.gen (R.exterior.ofSqf c) * bc.gen t.n ^ 3 /
    (bc.gen d * bc.gen t.f) ^ 2

def groupedExterior {h : S.ExtIdeal} (t : FrozenIndex R h) (d : S.ExtIdeal) (ν : Fˣ) : ℂ :=
  inactiveScalar R h t.f *
    (∏ v ∈ R.exterior.support d, localR R v 1 0 (toLoc v ν * toLoc v (primeGen R v) ^ 2)) *
    (∏ v ∈ R.exterior.support t.f, localR R v (frozenJ t v) (idealExp v t.a.1)
      (toLoc v ν * toLoc v (primeGen R v) ^ (2 - (idealExp v t.a.1 : ℤ)))) *
    ∏ᶠ v : FinPlace F, if v ∉ S.Sf ∧ v ∉ R.exterior.support d ∧ v ∉ R.exterior.support t.f then
      R.T.Wv v (R.C.a v (toLoc v ν)) else 1

/-- rf:active-support, 04:433-503. The fixed digit partition determines each frequency class. -/
theorem rf_active_support_frequencies :
  ∀ r (f : S.ExtIdeal), activeFactor R r.h f → ∀ ν : Fˣ,
    let coefficient := inactiveScalar R r.h f *
      (∏ v ∈ R.exterior.support r.d, localR R v 1 0 (toLoc v ν * toLoc v (primeGen R v) ^ 2)) *
      (∏ v ∈ R.exterior.support f,
        localR R v (digitExponent r v) (ordv v (toLoc v ν) + 2)
          (toLoc v ν * toLoc v (primeGen R v) ^ (-ordv v (toLoc v ν)))) *
      ∏ᶠ v : FinPlace F, if v ∉ S.Sf ∧ v ∉ R.exterior.support r.d ∧ v ∉ R.exterior.support f then
        R.T.Wv v (R.C.a v (toLoc v ν)) else 1
    coefficient ≠ 0 → ∃! acn : S.ExtIdeal × S.SqfExtIdeal × S.ExtIdeal,
      activeNumerator R f acn.1 ∧ IsCoprime (acn.2.1.1 * acn.2.2.1) (r.d.1 * f.1) ∧
        ∃ ε : S.US, ν = (ε : Fˣ) * bc.gen acn.1 * bc.gen (R.exterior.ofSqf acn.2.1) *
          bc.gen acn.2.2 ^ 3 / (bc.gen r.d * bc.gen f) ^ 2 := by
  sorry
/-- rf:reflected-absolute, 04:659–706. -/
theorem rf_reflected_absolute :
  ∀ σ : ℝ, 1 / 2 < σ → ∃ C : ℝ, 0 < C ∧ ∀ u ν l, 0 < l →
    (∀ γ : Gamma S, IntegrableOn (onUnits (fun y =>
      (rotatedAbs R u (S.diagU ((γ.1 : Fˣ) * ν) / y) : ℂ))) (omegaAt R l) (R.sheets.sheet l)) ∧
    Summable (fun γ : Gamma S => (omegaInt R l (fun y =>
      (rotatedAbs R u (S.diagU ((γ.1 : Fˣ) * ν) / y) : ℂ))).re) ∧
    (∑' γ : Gamma S, (omegaInt R l (fun y =>
      (rotatedAbs R u (S.diagU ((γ.1 : Fˣ) * ν) / y) : ℂ))).re) =
        profileAbs R u (S.absS (S.diagU ν : S.FS) / l) ∧
    profileAbs R u (S.absS (S.diagU ν : S.FS) / l) ≤
      C * (S.absS (S.diagU ν : S.FS) / l) ^ (-σ) := by
  sorry
/-- rf:exterior-factorization, 04:708–802: independently computed local product equals separation. -/
theorem rf_exterior_factorization :
  (∀ υ h (t : FrozenIndex R h), ‖frozenOmega R υ t‖ ≤ betaIdeal R t.f t.a ∧
    (∀ sd d, ‖frozenRho R υ t sd d‖ ≤ 1) ∧ (∀ sc c, ‖frozenLambda R υ t sc c‖ ≤ 1)) ∧
  ∀ υ h (t : FrozenIndex R h) sd sc d c,
    Squarefree d.1 → IsCoprime d.1 (h.1 * t.n.1) → IsCoprime c.1 t.f.1 → IsCoprime d.1 c.1 →
    cls (S.diagU (bc.gen d)) = sd.1 → cls (S.diagU (bc.gen (R.exterior.ofSqf c))) = sc.1 →
    groupedExterior R t d (frozenFrequency R t d c) *
        (Lvalue R υ (S.diagU (frozenFrequency R t d c)))⁻¹ =
      frozenOmega R υ t * frozenRho R υ t sd d * frozenLambda R υ t sc c *
        (qI c.1 ^ (-(1 / 2 : ℝ)) / qI t.n.1 : ℝ) * chiIdealPow D d.1 (cgen R c) 3 := by
  sorry
/-- rf:S-unfolding, 04:804–857. Inversion changes l to 1/l without a norm Jacobian. -/
theorem rf_S_unfolding : ∀ u ν l, 0 < l →
  let term := fun γ : Gamma S => omegaInt R l (fun y => bCut (Bd := Bd) y * (Lvalue R u y)⁻¹ *
    sCocycle (D := D) (H := H) (S.diagU ((γ.1 : Fˣ) * ν)) y⁻¹ * rotated R u (S.diagU ((γ.1 : Fˣ) * ν) / y))
  Summable term ∧ (∑' γ, term γ) = (Lvalue R u (S.diagU ν))⁻¹ *
    ∑ ℓ : Fin (R.rotated u).J, profileH R u (cls (S.diagU ν)) ℓ (S.absS (S.diagU ν : S.FS) / l) := by
  sorry
/-- Nonnegative reflected Dirichlet mass in 04:859–910. -/
def reflectedDirichletTerm (f : S.ExtIdeal) (σ : ℝ)
    (p : {a : S.ExtIdeal // activeNumerator R f a} × S.SqfExtIdeal × S.ExtIdeal) : ℝ :=
  betaIdeal R f p.1 * qI p.2.1.1 ^ (-(1 / 2 : ℝ)) / qI p.2.2.1 *
    (qI p.1.1.1 * qI p.2.1.1 * qI p.2.2.1 ^ 3) ^ (-σ)

/-- rf:grouped-absolute, 04:659-706. Absolute sums and the averaged integral use the same majorant. -/
theorem rf_grouped_absolute : ∀ σ : ℝ, 1 / 2 < σ → ∃ C : ℝ, 0 < C ∧ ∀ f,
  Summable (reflectedDirichletTerm R f σ) ∧
  (∑' p, reflectedDirichletTerm R f σ p) ≤
    sphericalMajorant (S := S) σ * Eideal R f σ ∧
  ∀ u t, 0 < t →
    IntegrableOn (fun T : ℝ => ‖R.K T‖ *
      (∑' p : {a : S.ExtIdeal // activeNumerator R f a} × S.SqfExtIdeal × S.ExtIdeal,
        betaIdeal R f p.1 * qI p.2.1.1 ^ (-(1 / 2 : ℝ)) / qI p.2.2.1 *
          profileAbs R u (qI p.1.1.1 * qI p.2.1.1 * qI p.2.2.1 ^ 3 / (t * T))) / T) (Set.Ioi 0) ∧
    (∫ T in Set.Ioi (0 : ℝ), ‖R.K T‖ *
      (∑' p : {a : S.ExtIdeal // activeNumerator R f a} × S.SqfExtIdeal × S.ExtIdeal,
        betaIdeal R f p.1 * qI p.2.1.1 ^ (-(1 / 2 : ℝ)) / qI p.2.2.1 *
          profileAbs R u (qI p.1.1.1 * qI p.2.1.1 * qI p.2.2.1 ^ 3 / (t * T))) / T) ≤
      C * t ^ σ * Theta.absMoment R.K σ * ∑' p, reflectedDirichletTerm R f σ p := by
  sorry
/-- A single summand of the full reflected expansion; no conclusion is used in this definition. -/
def reflectedTerm (υ : UnitSix S) (h d : S.ExtIdeal) (Z : ℝ)
    (p : FrozenIndex R h × Bd.B × Bd.B × S.SqfExtIdeal) : ℂ :=
  let t := p.1
  let sd := p.2.1
  let sc := p.2.2.1
  let c := p.2.2.2
  frozenOmega R υ t * frozenRho R υ t sd d * frozenLambda R υ t sc c *
    (qI c.1 ^ (-(1 / 2 : ℝ)) / qI t.n.1 : ℝ) * chiIdealPow D d.1 (cgen R c) 3 *
    profilePhi R υ (kappaSix R t sd sc)
      (Z * qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 / (qI d.1 ^ 2 * qI t.f.1 ^ 2))

/-- lem:reflection-quadratic-pairing, 04:625–657. -/
theorem lem_reflection_quadratic_pairing : ∀ r Z, 0 < Z →
  Summable (fun p => ‖reflectedTerm R (rowClass R r) r.h r.d Z p‖) ∧
  Bm D S A ϑ (cgen R) (r.m : F) Z = ∑' p, reflectedTerm R (rowClass R r) r.h r.d Z p := by
  sorry
/-- Retained and discarded masses use the same dyadic threshold, with the row support explicit. -/
def splitReflection (retained : Bool) (υ : UnitSix S) (h d : S.ExtIdeal) (Z R0 : ℝ) : ℂ :=
  if Squarefree d.1 ∧ IsCoprime d.1 h.1 then
    ∑' p : FrozenIndex R h × Bd.B × Bd.B × S.SqfExtIdeal,
      if (qI p.1.a.1 * qI p.2.2.2.1 * qI p.1.n.1 ^ 3 ≤ R0) = retained then
        reflectedTerm R υ h d Z p else 0
  else 0

/-- Sum over actual ideals, not ReflectionRow structures with auxiliary choices. -/
def reflectionMass (retained : Bool) (υ : UnitSix S) (P D0 Z δ : ℝ) : ℝ :=
  ∑' hd : S.ExtIdeal × S.ExtIdeal, if IsPowerful hd.1.1 ∧ P ≤ qI hd.1.1 ∧ qI hd.1.1 < 2 * P ∧
    D0 ≤ qI hd.2.1 ∧ qI hd.2.1 < 2 * D0 then
      ‖splitReflection R retained υ hd.1 hd.2 Z (reflectionColumnCutoff P D0 Z δ)‖ ^ 2 else 0

/-- rf:tail-mass, 04:1046–1117, uniformly including R₀<1. -/
theorem rf_tail_mass : ∀ δ δ₁ σ N : ℝ, 0 < δ → 0 < δ₁ → 1 / 2 < σ → σ < N →
  ∃ C : ℝ, 0 < C ∧ ∀ υ P D0 Z, 1 ≤ P → 1 ≤ D0 → 2 ≤ Z →
    reflectionMass R false υ P D0 Z δ ≤ C * P ^ (1 / 2 + 2 * δ₁) * D0 *
      reflectionColumnLength P D0 Z ^ (2 * σ) *
        max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-2 * (N - σ)) := by
  sorry
/-- rf:retained-mass, 04:1119–1196. The constant can depend on fixed δ. -/
theorem rf_retained_mass : ∀ δ δ₁ δ₂ : ℝ, 0 < δ → 0 < δ₁ → 0 < δ₂ →
  ∃ C : ℝ, 0 < C ∧ ∀ υ P D0 Z, 1 ≤ P → 1 ≤ D0 → 2 ≤ Z →
    let R0 := reflectionColumnCutoff P D0 Z δ
    (R0 < 1 → reflectionMass R true υ P D0 Z δ = 0) ∧
    (1 ≤ R0 → reflectionMass R true υ P D0 Z δ ≤
      C * P ^ (1 / 2 + 2 * δ₁) * Real.log (2 * R0) ^ 4 * (D0 + R0) * (D0 * R0) ^ δ₂) := by
  sorry
/-- rf:reflection-assembly, 04:1198–1228. Compact shape and translation sets are fixed first. -/
theorem rf_reflection_assembly : ∀ K T : Set S.FSˣ, IsCompact K → IsCompact T →
  (∀ t ∈ T, S.absS (t : S.FS) = 1) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ Z : ℝ, ∀ hZ : 2 ≤ Z, ∀ t ∈ T, ∀ rows : Finset (ReflectionRow S),
      Set.InjOn (fun r : ReflectionRow S => (r.m : F)) (↑rows : Set (ReflectionRow S)) →
      (∀ r ∈ rows, InReflectionBox D S K t Z (by linarith) r) →
      (∑ r ∈ rows, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2) ≤ C * Z ^ (2 * M0 - 1 + ε) := by
  sorry
end Reflection

section SupplementaryClauses
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)

def forwardExterior (ν : Fˣ) : ℂ :=
  ∏ᶠ v : FinPlace F, if v ∉ S.Sf then R.T.Wv v (R.C.a v (toLoc v ν)) else 1

/-- rf:forward-frequencies: remaining S-factor and exterior Γ-invariance clauses. -/
theorem rf_forward_frequency_factors :
  (∀ u ν y, R.T.WS (R.chars.L u) (R.C.aS (S.diagU ν) * R.C.aS y) =
    sCocycle (D := D) (H := H) (S.diagU ν) y * unrotated R u (S.diagU ν * y)) ∧
  ∀ (γ : Gamma S) ν, forwardExterior R ((γ.1 : Fˣ) * ν) = forwardExterior R ν := by
  constructor
  · intro u ν y
    rw [R.C.aS_mul]
    rw [R.T.WS_genuine (R.chars.L u) (R.mem_family u)]
    simp [sCocycle, unrotated, muThree, map_pow]
  · intro γ ν
    classical
    have hroot : ∃ u : S.US, (γ.1 : S.US) = u ^ 6 := by
      have hmem : (γ.1 : S.US) ∈ (sixthPowerOnUS S).range := γ.2
      rcases MonoidHom.mem_range.mp hmem with ⟨u, hu⟩
      change u ^ 6 = γ.1 at hu
      exact ⟨u, hu.symm⟩
    obtain ⟨u, hu⟩ := hroot
    have localVal (v : FinPlace F) (hv : v ∉ S.Sf) (e : S.US) :
        Valued.v (toLoc v (e : Fˣ) : v.adicCompletion F) = 1 := by
      have hglob : HeightOneSpectrum.valuation F v ((e : Fˣ) : F) = 1 :=
        Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F) e hv
      change Valued.v (algebraMap F (v.adicCompletion F) ((e : Fˣ) : F)) = 1
      simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hglob]
    have hglobalPow : (γ.1 : Fˣ) = (u : Fˣ) ^ 6 := by
      exact congrArg (fun e : S.US => (e : Fˣ)) hu
    have hlocal (v : FinPlace F) (hv : v ∉ S.Sf) :
        R.T.Wv v (R.C.a v (toLoc v ((γ.1 : Fˣ) * ν))) =
          R.T.Wv v (R.C.a v (toLoc v ν)) := by
      let g : (v.adicCompletion F)ˣ := toLoc v (γ.1 : Fˣ)
      let t : (v.adicCompletion F)ˣ := toLoc v (u : Fˣ)
      have hvalg : Valued.v (g : v.adicCompletion F) = 1 := by
        exact localVal v hv (γ.1 : S.US)
      have hvalt : Valued.v (t : v.adicCompletion F) = 1 := by
        exact localVal v hv u
      have hgintegral : (g : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvalg]
      have hginvIntegral : ((g⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
          v.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        simp only [Units.val_inv_eq_inv_val, map_inv₀, hvalg, inv_one, le_refl]
      have hK : R.C.a v g ∈ R.C.Kext :=
        R.C.a_Kext v hv g hgintegral hginvIntegral
      have hv6 : (6 : 𝓞 F) ∉ v.asIdeal := by
        intro h
        exact hv (S.over6 v h)
      have hbasic := ArtinPrimitiveRoots.A1.Theta.localChi_basic (D := D) hv6
      have htLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v t := by
        constructor
        · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvalt]
        · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
          simp only [Units.val_inv_eq_inv_val, map_inv₀, hvalt, inv_one, le_refl]
      have htPowLoc (n : ℕ) : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (t ^ n) := by
        have hpowval : Valued.v ((t ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
          simp only [Units.val_pow_eq_pow_val, map_pow, hvalt, one_pow]
        constructor
        · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hpowval]
        · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
          have hinv : Valued.v (((t ^ n)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
            simp only [Units.val_inv_eq_inv_val, map_inv₀, hpowval, inv_one]
          rw [hinv]
      have hchiPow : ∀ n : ℕ,
          ArtinPrimitiveRoots.A1.localChi D v (t ^ n) =
            ArtinPrimitiveRoots.A1.localChi D v t ^ n := by
        intro n
        induction n with
        | zero => simpa using hbasic.1
        | succ n ih =>
          calc
            ArtinPrimitiveRoots.A1.localChi D v (t ^ (n + 1)) =
                ArtinPrimitiveRoots.A1.localChi D v (t ^ n * t) := by rw [pow_succ]
            _ = ArtinPrimitiveRoots.A1.localChi D v (t ^ n) *
                ArtinPrimitiveRoots.A1.localChi D v t :=
              hbasic.2.2.1 _ _ (htPowLoc n) htLoc
            _ = _ := by rw [ih, pow_succ]
      have hgammaLocalPow : g = t ^ 6 := by
        change toLoc v ((γ.1 : Fˣ)) = (toLoc v (u : Fˣ)) ^ 6
        rw [← map_pow]
        exact congrArg (toLoc v) hglobalPow
      have hchiG : ArtinPrimitiveRoots.A1.localChi D v g = 1 := by
        calc
          ArtinPrimitiveRoots.A1.localChi D v g =
              ArtinPrimitiveRoots.A1.localChi D v (t ^ 6) := by rw [hgammaLocalPow]
          _ = ArtinPrimitiveRoots.A1.localChi D v t ^ 6 := hchiPow 6
          _ = 1 := hbasic.2.2.2.1 t htLoc
      have hordG : ArtinPrimitiveRoots.A1.ordv v g = 0 := by
        have hne : Valued.v (g : v.adicCompletion F) ≠ 0 := by
          rw [hvalg]
          exact one_ne_zero
        unfold ArtinPrimitiveRoots.A1.ordv
        rw [WithZero.toAdd_unzero_eq_log hne, hvalg]
        simp
      have hunitPartG : ArtinPrimitiveRoots.A1.unitPart v g = g := by
        simp [ArtinPrimitiveRoots.A1.unitPart, hordG]
      have hCocLeft : ArtinPrimitiveRoots.A1.extCocycle D v g (toLoc v ν) = 1 := by
        simp [ArtinPrimitiveRoots.A1.extCocycle, hunitPartG, hchiG, hordG]
      have hCocRight : ArtinPrimitiveRoots.A1.extCocycle D v (toLoc v ν) g = 1 := by
        simp [ArtinPrimitiveRoots.A1.extCocycle, hunitPartG, hchiG, hordG]
      obtain ⟨ζ₁, hζ₁, hmul₁⟩ := R.C.a_mul v hv g (toLoc v ν)
      have hζ₁ : ζ₁ = 1 := by
        apply Subtype.ext
        apply Units.ext
        exact hζ₁.trans hCocLeft
      have hmul₁ : R.C.a v g * R.C.a v (toLoc v ν) = R.C.a v (g * toLoc v ν) := by
        simpa [hζ₁] using hmul₁
      obtain ⟨ζ₂, hζ₂, hmul₂⟩ := R.C.a_mul v hv (toLoc v ν) g
      have hζ₂ : ζ₂ = 1 := by
        apply Subtype.ext
        apply Units.ext
        exact hζ₂.trans hCocRight
      have hmul₂ : R.C.a v (toLoc v ν) * R.C.a v g =
          R.C.a v (toLoc v ν * g) := by
        simpa [hζ₂] using hmul₂
      have hcomm : R.C.a v g * R.C.a v (toLoc v ν) =
          R.C.a v (toLoc v ν) * R.C.a v g := by
        calc
          _ = R.C.a v (g * toLoc v ν) := hmul₁
          _ = R.C.a v (toLoc v ν * g) := by rw [mul_comm]
          _ = _ := hmul₂.symm
      calc
        R.T.Wv v (R.C.a v (toLoc v ((γ.1 : Fˣ) * ν))) =
            R.T.Wv v (R.C.a v g * R.C.a v (toLoc v ν)) := by
              rw [map_mul]
              exact congrArg (R.T.Wv v) hmul₁.symm
        _ = R.T.Wv v (R.C.a v (toLoc v ν) * R.C.a v g) := by rw [hcomm]
        _ = R.T.Wv v (R.C.a v (toLoc v ν)) :=
          R.T.Wv_right v hv (R.C.a v (toLoc v ν)) (R.C.a v g) hK (R.C.a_mem v g)
    apply finprod_congr
    intro v
    by_cases hv : v ∉ S.Sf
    · simpa [forwardExterior, hv] using hlocal v hv
    · simp [forwardExterior, hv]
/-- rf:reflected-absolute: spherical series and convergence BEFORE digit evaluation. -/
theorem rf_reflected_pre_digit_absolute :
  (∀ v, v ∉ S.Sf → ∀ σ : ℝ, 1 / 2 < σ →
    Summable (fun e : ℕ => ‖localW R v e‖ * qI v.asIdeal ^ (-σ * (e : ℝ))) ∧
    (∑' e : ℕ, ‖localW R v e‖ * qI v.asIdeal ^ (-σ * (e : ℝ))) =
      (1 + qI v.asIdeal ^ (-1 / 2 - σ)) / (1 - qI v.asIdeal ^ (-1 - 3 * σ))) ∧
  ∀ r l, 0 < l → Summable (fun p : Digits R r × Fˣ =>
    ‖digitAlpha R r p.1‖ * (omegaInt R l (fun y =>
      (‖R.T.W (R.chars.L (rowClass R r))
        (R.C.rat (diagGL p.2) * R.C.rat weylGL * digitPoint R r y p.1)‖ : ℂ))).re) := by
  sorry
/-- rf:grouped-absolute: explicit incomplete zeta majorant. -/
def exteriorZeta (σ : ℝ) : ℝ := ∑' I : S.ExtIdeal, qI I.1 ^ (-σ)
/-- rf:grouped-absolute, 04:659-706. The original incomplete zeta majorant is explicit. -/
theorem rf_original_majorant : ∀ σ : ℝ, 1 / 2 < σ →
  sphericalMajorant (S := S) σ ≤ exteriorZeta (S := S) (σ + 1 / 2) * exteriorZeta (S := S) (3 * σ + 1) ∧
  Summable (fun I : S.ExtIdeal => qI I.1 ^ (-(σ + 1 / 2))) ∧
  Summable (fun I : S.ExtIdeal => qI I.1 ^ (-(3 * σ + 1))) := by
  intro σ hσ
  let a : S.ExtIdeal → ℝ := fun I => qI I.1 ^ (-1 / 2 - σ)
  let b : S.ExtIdeal → ℝ := fun I => qI I.1 ^ (-1 - 3 * σ)
  have haBase := a2_bridge_COUNT_summable (S := S) (σ + 1 / 2) (by linarith)
  have hbBase := a2_bridge_COUNT_summable (S := S) (3 * σ + 1) (by linarith)
  have ha : Summable a := by
    apply haBase.congr
    intro I
    dsimp [a, qI, idealNorm]
    congr 1
    ring
  have hb : Summable b := by
    apply hbBase.congr
    intro I
    dsimp [b, qI, idealNorm]
    congr 1
    ring
  have haResult : Summable (fun I : S.ExtIdeal => qI I.1 ^ (-(σ + 1 / 2))) := by
    simpa [qI, idealNorm] using haBase
  have hbResult : Summable (fun I : S.ExtIdeal => qI I.1 ^ (-(3 * σ + 1))) := by
    simpa [qI, idealNorm] using hbBase
  have ha_nonneg : ∀ I, 0 ≤ a I := by
    intro I
    change 0 ≤ Real.rpow (Ideal.absNorm I.1 : ℝ) _
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hb_nonneg : ∀ I, 0 ≤ b I := by
    intro I
    change 0 ≤ Real.rpow (Ideal.absNorm I.1 : ℝ) _
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  let incl : S.SqfExtIdeal → S.ExtIdeal := fun I => ⟨I.1, I.2.1⟩
  have hincl : Function.Injective incl := by
    intro I J h
    apply Subtype.ext
    change (incl I).1 = (incl J).1
    exact congrArg (fun x : S.ExtIdeal => x.1) h
  let aSqf : S.SqfExtIdeal → ℝ := fun I => a (incl I)
  have haSqf : Summable aSqf := by
    let e : S.SqfExtIdeal ≃ {I : S.ExtIdeal // Squarefree I.1} :=
      { toFun := fun I => ⟨incl I, I.2.2⟩
        invFun := fun I => ⟨I.1.1, ⟨I.1.2, I.2⟩⟩
        left_inv := by intro I; apply Subtype.ext; rfl
        right_inv := by intro I; apply Subtype.ext; apply Subtype.ext; rfl }
    have hsub : Summable (fun I : {I : S.ExtIdeal // Squarefree I.1} => a I.1) :=
      ha.subtype (fun I : S.ExtIdeal => Squarefree I.1)
    have heq : aSqf = fun I : S.SqfExtIdeal => a (e I).1 := by
      funext I
      rfl
    rw [heq]
    exact (Equiv.summable_iff e).mpr hsub
  have hpair : Summable (fun p : S.SqfExtIdeal × S.ExtIdeal => aSqf p.1 * b p.2) :=
    haSqf.mul_of_nonneg hb (fun I => ha_nonneg (incl I)) hb_nonneg
  have hprod :
      (∑' p : S.SqfExtIdeal × S.ExtIdeal, aSqf p.1 * b p.2) =
        (∑' I : S.SqfExtIdeal, aSqf I) * (∑' I : S.ExtIdeal, b I) := by
    calc
      _ = ∑' I : S.SqfExtIdeal, ∑' J : S.ExtIdeal, aSqf I * b J := hpair.tsum_prod
      _ = _ := by simp [tsum_mul_left, tsum_mul_right]
  have hsub : (∑' I : S.SqfExtIdeal, aSqf I) ≤ ∑' I : S.ExtIdeal, a I :=
    tsum_comp_le_tsum_of_inj ha ha_nonneg hincl
  have hb_tsum_nonneg : 0 ≤ ∑' I : S.ExtIdeal, b I := tsum_nonneg hb_nonneg
  have hbound :
      (∑' p : S.SqfExtIdeal × S.ExtIdeal, aSqf p.1 * b p.2) ≤
        (∑' I : S.ExtIdeal, a I) * (∑' I : S.ExtIdeal, b I) := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_right hsub hb_tsum_nonneg
  have hmaj_eq : sphericalMajorant (S := S) σ =
      ∑' p : S.SqfExtIdeal × S.ExtIdeal, aSqf p.1 * b p.2 := by
    unfold sphericalMajorant
    apply tsum_congr
    intro p
    rfl
  have hza : (∑' I : S.ExtIdeal, a I) = exteriorZeta (S := S) (σ + 1 / 2) := by
    unfold exteriorZeta
    apply tsum_congr
    intro I
    dsimp [a]
    congr 1
    ring
  have hzb : (∑' I : S.ExtIdeal, b I) = exteriorZeta (S := S) (3 * σ + 1) := by
    unfold exteriorZeta
    apply tsum_congr
    intro I
    dsimp [b]
    congr 1
    ring
  refine ⟨?_, haResult, hbResult⟩
  calc
    sphericalMajorant (S := S) σ = _ := hmaj_eq
    _ ≤ (∑' I : S.ExtIdeal, a I) * (∑' I : S.ExtIdeal, b I) := hbound
    _ = _ := by rw [hza, hzb]
/-- rf:S-unfolding, 04:804-857. The norm identity and selected frequency class are fixed together. -/
theorem rf_frozen_frequency_norm_class : ∀ h (t : FrozenIndex R h) d c sd sc,
  cls (S.diagU (bc.gen d)) = sd.1 → cls (S.diagU (bc.gen (R.exterior.ofSqf c))) = sc.1 →
    S.absS (S.diagU (frozenFrequency R t d c) : S.FS) =
      qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 / (qI d.1 ^ 2 * qI t.f.1 ^ 2) ∧
    cls (S.diagU (frozenFrequency R t d c)) = kappaSix R t sd sc := by
  sorry
def activePartial (retained : Bool) (υ : UnitSix S) (h d f : S.ExtIdeal)
    (u : UnitSix S) (sd sc : Bd.B) (Z R0 : ℝ) : ℂ :=
  ∑' p : {t : FrozenIndex R h // t.f = f ∧ t.u = u} × S.SqfExtIdeal,
    if (qI p.1.1.a.1 * qI p.2.1 * qI p.1.1.n.1 ^ 3 ≤ R0) = retained then
      reflectedTerm R υ h d Z (p.1.1, sd, sc, p.2) else 0

/-- rf:tail-mass: pointwise active/slice bound, before summing squares over powerful parts. -/
theorem rf_tail_bound : ∀ δ σ N : ℝ, 0 < δ → 1 / 2 < σ → σ < N →
  ∃ C : ℝ, 0 < C ∧ ∀ υ P D0 Z h d f u sd sc,
    1 ≤ P → 1 ≤ D0 → 2 ≤ Z → P ≤ qI h.1 → qI h.1 < 2 * P →
    D0 ≤ qI d.1 → qI d.1 < 2 * D0 → IsPowerful h.1 → activeFactor R h f →
    ‖activePartial R false υ h d f u sd sc Z (reflectionColumnCutoff P D0 Z δ)‖ ≤
      C * reflectionColumnLength P D0 Z ^ σ *
        max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-(N - σ)) *
          sphericalMajorant (S := S) σ * Eideal R f σ := by
  sorry
/-- rf:tail-mass: the explicit large-N condition giving arbitrary negative powers of Z. -/
theorem rf_tail_negligible : ∀ C0 δ δ₁ σ N A0 : ℝ, 0 < C0 → 0 < δ → 0 < δ₁ →
  1 / 2 < σ → σ < N → 0 < A0 →
  A0 + 2 * M0 * δ₁ + 2 * σ * (2 * M0 - 1) < 2 * δ * (N - σ) →
    ∃ C : ℝ, 0 < C ∧ ∀ υ P D0 Z, 1 ≤ P → 1 ≤ D0 → 2 ≤ Z → P * D0 ≤ C0 * Z ^ M0 →
      reflectionMass R false υ P D0 Z δ ≤ C * Z ^ (-A0) * P ^ (1 / 2 : ℝ) * D0 := by
  sorry
/-- Fourier transform with the 2π convention; only its L1 bound is used by retained mass. -/
def separatedFourier (ρ : ℝ → ℂ) (υ : UnitSix S) (κ : S.V) (v τ : ℝ) : ℂ :=
  ∫ x : ℝ, ρ x * profilePhi R υ κ (v * Real.exp x) * Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * τ)

/-- rf:retained-mass: the fixed profile separation estimate (04:1120–1141). -/
theorem rf_retained_fourier_separation : ∃ α : ℝ, 0 < α ∧ ∀ N : ℝ, 0 < N →
  ∀ ρ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ → HasCompactSupport ρ →
    ∃ C : ℝ, 0 < C ∧ ∀ υ κ v, 0 < v →
      Integrable (fun τ => ‖separatedFourier R ρ υ κ v τ‖) ∧
      (∫ τ : ℝ, ‖separatedFourier R ρ υ κ v τ‖) ≤ C * min (v ^ α) (v ^ (-N)) := by
  sorry
/-- rf:reflection-assembly: dyadic clause, restoring bounded element multiplicity. -/
theorem rf_reflection_dyadic_assembly : ∀ K T : Set S.FSˣ, IsCompact K → IsCompact T →
  (∀ t ∈ T, S.absS (t : S.FS) = 1) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
  ∀ Z : ℝ, ∀ hZ : 2 ≤ Z, ∀ P D0 : ℝ, 1 ≤ P → 1 ≤ D0 → ∀ t ∈ T,
    ∀ rows : Finset (ReflectionRow S),
      Set.InjOn (fun r : ReflectionRow S => (r.m : F)) (↑rows : Set (ReflectionRow S)) →
      (∀ r ∈ rows, InReflectionBox D S K t Z (by linarith) r ∧
        P ≤ qI r.h.1 ∧ qI r.h.1 < 2 * P ∧ D0 ≤ qI r.d.1 ∧ qI r.d.1 < 2 * D0) →
      (∑ r ∈ rows, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2) ≤
        C * Z ^ ε * P ^ (1 / 2 : ℝ) * (D0 + D0 ^ 2 * P / Z) := by
  sorry
end SupplementaryClauses
section FinalSourceClauses
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)

/-- def:rf-active and rf:active-support, 04:433-503. The empty factor and Euler bound are included. -/
theorem rf_active_empty_and_product :
  (∀ a, activeNumerator R R.exterior.one a ↔ a = R.exterior.one) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ f σ, 0 ≤ σ → Eideal R f σ ≤ C * qI f.1 ^ ε := by
  sorry
/-- rf:exterior-factorization, 04:708-802. The 1-4≡3 identity is checked before multiplying over primes. -/
theorem rf_one_minus_four : ∀ v w : FinPlace F, v ∉ S.Sf → w ∉ S.Sf → v ≠ w →
  chi D v (primeGen R w : F) * chi D w (primeGen R v : F) ^ (-4 : ℤ) =
    chi D v (primeGen R w : F) ^ 3 := by
  sorry
/-- rf:S-unfolding: averaging the signed orbit gives the combined Φ profile. -/
theorem rf_S_averaged : ∀ u (ν : Fˣ) Z, 0 < Z →
  (∫ T in Set.Ioi (0 : ℝ), R.K T *
    (∑' γ : Gamma S, omegaInt R (T / Z) (fun y => bCut (Bd := Bd) y * (Lvalue R u y)⁻¹ *
      sCocycle (D := D) (H := H) (S.diagU ((γ.1 : Fˣ) * ν)) y⁻¹ *
        rotated R u (S.diagU ((γ.1 : Fˣ) * ν) / y))) / (T : ℂ)) =
      (Lvalue R u (S.diagU ν))⁻¹ * profilePhi R u (cls (S.diagU ν)) (Z * S.absS (S.diagU ν : S.FS)) := by
  sorry
/-- rf:retained-mass, 04:1143-1167. A single retained column with its fixed profile. -/
def retainedColumn (υ : UnitSix S) {h : S.ExtIdeal} (t : FrozenIndex R h) (sd sc : Bd.B)
    (d : S.ExtIdeal) (C Z R0 : ℝ) : ℂ :=
  frozenRho R υ t sd d * ∑' c : S.SqfExtIdeal,
    if C ≤ qI c.1 ∧ qI c.1 < 2 * C ∧ qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 ≤ R0 then
      frozenLambda R υ t sc c * (qI c.1 ^ (-(1 / 2 : ℝ)) : ℝ) * chiIdealPow D d.1 (cgen R c) 3 *
        profilePhi R υ (kappaSix R t sd sc)
          (Z * qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 / (qI d.1 ^ 2 * qI t.f.1 ^ 2))
    else 0

/-- rf:retained-mass, 04:1143-1167. The one-column dyadic estimate precedes summing over rows. -/
theorem rf_retained_column_dyad : ∃ α : ℝ, 0 < α ∧ ∀ N ε : ℝ, 0 < N → 0 < ε →
  ∃ K : ℝ, 0 < K ∧ ∀ υ h (t : FrozenIndex R h) sd sc C D0 Z R0,
    1 ≤ C → 1 ≤ D0 → 2 ≤ Z → 1 ≤ R0 →
    let v := Z * qI t.a.1 * qI t.n.1 ^ 3 * C / (D0 ^ 2 * qI t.f.1 ^ 2)
    Real.sqrt (∑' d : S.ExtIdeal, if D0 ≤ qI d.1 ∧ qI d.1 < 2 * D0 then
      ‖retainedColumn R υ t sd sc d C Z R0‖ ^ 2 else 0) ≤
      K * (D0 + C) ^ (1 / 2 : ℝ) * (D0 * C) ^ (ε / 2) * min (v ^ α) (v ^ (-N)) := by
  sorry
/-- rf:reflection-assembly: all scale comparisons and the loss-selection inequality. -/
theorem rf_assembly_scale_bounds :
  (∀ ε : ℝ, 0 < ε → ∃ δ δ₁ δ₂ δ₃ : ℝ, 0 < δ ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ 0 < δ₃ ∧
    δ + 2 * M0 * δ₁ + (3 * M0 - 1 + δ) * δ₂ + δ₃ < ε) ∧
  ∀ C0 δ δ₃ : ℝ, 0 < C0 → 0 < δ → 0 < δ₃ → ∃ C : ℝ, 0 < C ∧ ∀ P D0 Z,
    1 ≤ P → 1 ≤ D0 → 2 ≤ Z → P * D0 ≤ C0 * Z ^ M0 →
    let R0 := reflectionColumnCutoff P D0 Z δ
    D0 + R0 ≤ C * Z ^ δ * (D0 + D0 ^ 2 * P / Z) ∧
    D0 * R0 ≤ C * Z ^ (3 * M0 - 1 + δ) ∧ P ≤ C * Z ^ M0 ∧
    (1 ≤ R0 → Real.log (2 * R0) ^ 4 ≤ C * Z ^ δ₃) ∧
    P ^ (1 / 2 : ℝ) * (D0 + D0 ^ 2 * P / Z) ≤ C * Z ^ (2 * M0 - 1) := by
  sorry
end FinalSourceClauses
section FrequencyUnitOrbits
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)

/-- rf:active-support: once the ideals are fixed, the frequency-unit class and actual Γ element
are unique. The claim does not count different sixth roots of the same Γ element. -/
theorem rf_active_support_unit_orbit : ∀ h (t : FrozenIndex R h) d c (ν : Fˣ),
  (∃ ε : S.US, ν = (ε : Fˣ) * bc.gen t.a * bc.gen (R.exterior.ofSqf c) * bc.gen t.n ^ 3 /
    (bc.gen d * bc.gen t.f) ^ 2) →
  ∃! ug : UnitSix S × Gamma S, ν = (ug.2.1 : Fˣ) * (R.sheets.eps ug.1 : Fˣ) *
    bc.gen t.a * bc.gen (R.exterior.ofSqf c) * bc.gen t.n ^ 3 / (bc.gen d * bc.gen t.f) ^ 2 := by
  sorry
end FrequencyUnitOrbits

/-! ## Finite assembly to the legacy `prop_reflection` sum

The finite-row theorem is already available above. The remaining conversion is elementary once
the row element determines its row; that arithmetic uniqueness remains a named obligation. -/

section ReflectionAssemblyAdapter
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)

/-- `rf:reflection-assembly` to `prop:reflection` needs uniqueness of the row represented by
`m`; this stays explicit until the row-factorization theory proves it (04:1198–1228). -/
def rowElementInjectiveStatement : Prop :=
  Function.Injective (fun r : ReflectionRow S => (r.m : F))

/-- Row-factorization obligation for the finite/`tsum` bridge to `prop:reflection`
(04:1198–1228). -/
theorem reflection_row_element_injective : rowElementInjectiveStatement (S := S) := by
  sorry

/-- A uniform finite-set bound gives summability and the same bound for the subtype `tsum`.
This is the proved finite/`tsum` adapter for `prop:reflection` (04:1027–1228). -/
theorem finite_to_tsum {ι : Type*} (P : ι → Prop) (f : ι → ℝ) (B : ℝ)
    (hf : ∀ i, 0 ≤ f i)
    (hbound : ∀ s : Finset ι, (∀ i ∈ s, P i) → ∑ i ∈ s, f i ≤ B) :
    Summable (fun i : {i // P i} => f i.1) ∧ (∑' i : {i // P i}, f i.1) ≤ B := by
  have hb (s : Finset {i // P i}) : ∑ i ∈ s, f i.1 ≤ B := by
    let t := s.image Subtype.val
    have hp : ∀ i ∈ t, P i := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact j.2
    have he : ∑ i ∈ t, f i = ∑ j ∈ s, f j.1 :=
      Finset.sum_image (fun i hi j hj hij => Subtype.ext hij)
    rw [← he]
    exact hbound t hp
  exact ⟨summable_of_sum_le (fun i => hf i.1) hb,
    Real.tsum_le_of_sum_le (fun i => hf i.1) hb⟩

/-- Finite total-reflection target matching the current `rf_reflection_assembly` output. -/
def finiteReflectionStatement : Prop :=
  ∀ K T : Set S.FSˣ, IsCompact K → IsCompact T →
    (∀ t ∈ T, S.absS (t : S.FS) = 1) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, ∀ hZ : 2 ≤ Z, ∀ t ∈ T, ∀ rows : Finset (ReflectionRow S),
        Set.InjOn (fun r : ReflectionRow S => (r.m : F)) (↑rows : Set (ReflectionRow S)) →
        (∀ r ∈ rows, InReflectionBox D S K t Z (by linarith) r) →
        (∑ r ∈ rows, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2) ≤
          C * Z ^ (2 * M0 - 1 + ε)

/-- Summable subtype form consumed by the total clause of `prop:reflection`. -/
def totalReflectionStatement : Prop :=
  ∀ K T : Set S.FSˣ, IsCompact K → IsCompact T →
    (∀ t ∈ T, S.absS (t : S.FS) = 1) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, ∀ hZ : 2 ≤ Z, ∀ t ∈ T,
        Summable (fun r : {r : ReflectionRow S //
          InReflectionBox D S K t Z (by linarith) r} =>
            ‖Bm D S A ϑ (cgen R) (r.1.m : F) Z‖ ^ 2) ∧
        (∑' r : {r : ReflectionRow S //
          InReflectionBox D S K t Z (by linarith) r},
            ‖Bm D S A ϑ (cgen R) (r.1.m : F) Z‖ ^ 2) ≤ C * Z ^ (2 * M0 - 1 + ε)

/-- The finite reflection assembly theorem implies its summable total form, provided each
element of `F` comes from at most one reflection row. -/
theorem assembly_to_total (hInj : rowElementInjectiveStatement (S := S))
    (hfinite : finiteReflectionStatement R) : totalReflectionStatement R := by
  intro K T hK hT hnorm ε hε
  obtain ⟨C, hC, hb⟩ := hfinite K T hK hT hnorm ε hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ t ht
  apply finite_to_tsum
    (fun r : ReflectionRow S => InReflectionBox D S K t Z (by linarith) r)
    (fun r => ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2)
    (C * Z ^ (2 * M0 - 1 + ε))
  · intro r; positivity
  · intro rows hrows
    exact hb Z hZ t ht rows hInj.injOn hrows

/-- The total subtype-sum edge of `prop:reflection` is proved from the finite assembly output;
the dyadic part of that node remains its separate analytic obligation (04:1027–1228). -/
theorem prop_reflection_total_from_assembly
    (hInj : rowElementInjectiveStatement (S := S))
    (hfinite : finiteReflectionStatement R) : totalReflectionStatement R :=
  assembly_to_total R hInj hfinite

/-- The exact total subtype-sum clause of `prop:reflection` for the split-character notation.
The dyadic clause is supplied by its separate analytic obligation (04:1027–1228). -/
def propReflectionTotalStatement (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (η Λ G : HeckeChar F) (cgen : S.SqfExtIdeal → F) : Prop :=
  ∀ K T : Set S.FSˣ, IsCompact K → IsCompact T →
    (∀ t ∈ T, S.absS (t : S.FS) = 1) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ Z P Dlen : ℝ, (hZ : 2 ≤ Z) → 1 ≤ P → 1 ≤ Dlen → ∀ t ∈ T,
        Summable (fun r : {r : ReflectionRow S //
          InReflectionBox D S K t Z (by linarith) r} =>
            ‖Bm D S A (vartheta Λ G η) cgen (r.1.m : F) Z‖ ^ 2) ∧
        (∑' r : {r : ReflectionRow S //
          InReflectionBox D S K t Z (by linarith) r},
            ‖Bm D S A (vartheta Λ G η) cgen (r.1.m : F) Z‖ ^ 2) ≤
          C * Z ^ (2 * M0 - 1 + ε)

/-- The proved finite/`tsum` adapter specializes to the exact total clause of `prop:reflection`
once the Gauss split identifies `ϑ = vartheta Λ G η`; row uniqueness remains an explicit input. -/
theorem prop_reflection_total_from_assembly_exact
    (η : HeckeChar F)
    (hSplit : GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η)
    (hInj : rowElementInjectiveStatement (S := S))
    (hfinite : finiteReflectionStatement R) :
    propReflectionTotalStatement D S A η hSplit.Λ hSplit.G (cgen R) := by
  have htotal := prop_reflection_total_from_assembly R hInj hfinite
  intro K T hK hT hnorm ε hε
  obtain ⟨C, hC, hb⟩ := htotal K T hK hT hnorm ε hε
  refine ⟨C, hC, ?_⟩
  intro Z P Dlen hZ hP hD t ht
  obtain ⟨hsum, hbound⟩ := hb Z hZ t ht
  refine ⟨?_, ?_⟩
  · simpa [hSplit.vartheta_eq] using hsum
  · simpa [hSplit.vartheta_eq] using hbound

end ReflectionAssemblyAdapter

end ArtinPrimitiveRoots.A2
