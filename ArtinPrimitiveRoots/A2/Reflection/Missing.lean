import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».All
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import ArtinPrimitiveRoots.Proofs.th_factor_b.Analytic

/-! A2 statement interfaces derived from the design lane. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform Pointwise
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
  intro r l hl
  letI : IsTotallyComplex F := D.isTotallyComplex
  let w : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  let zminus : ℂˣ := -1
  obtain ⟨z0, hz0pow⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) (by norm_num : 0 < 6)
  have hz0ne : z0 ≠ 0 := by
    intro hz
    rw [hz] at hz0pow
    norm_num at hz0pow
  let zroot : ℂˣ := Units.mk0 z0 hz0ne
  have hzrootpow : zroot ^ 6 = zminus := by
    apply Units.ext
    change z0 ^ 6 = -1
    simpa [zminus] using hz0pow
  let a : S.FSˣ := S.atComplex w zminus
  have haSix : (S.atComplex w zroot) ^ 6 = a := by
    apply Units.ext
    apply Prod.ext
    · funext v
      simp [a, SData.atComplex]
    · funext w'
      by_cases hw' : w' = w
      · subst w'
        have hzval : (zroot : ℂ) ^ 6 = (zminus : ℂ) :=
          congrArg (fun z : ℂˣ => (z : ℂ)) hzrootpow
        simpa [a, SData.atComplex, Function.update_self] using hzval
      · simp [a, SData.atComplex, hw']
  have haInv : a⁻¹ = a := by
    apply Units.ext
    apply Prod.ext
    · funext v
      simp [a, SData.atComplex]
    · funext w'
      by_cases hw' : w' = w
      · subst w'
        simp [a, SData.atComplex, zminus]
      · simp [a, SData.atComplex, hw']
  let ai : S.FS := ((a⁻¹ : S.FSˣ) : S.FS)
  have hAbsOne (v : S.Sf) : absFin v.1 1 = 1 := by
    dsimp [absFin]
    rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v.1)]
    simp
  have hNormA : S.absS (a : S.FS) = 1 := by
    have hfinprod : (∏ v : S.Sf, absFin v.1 1) = 1 :=
      Finset.prod_eq_one fun v _ => hAbsOne v
    have harchprod :
        (∏ w' : InfinitePlace F,
          Complex.normSq (Function.update (fun _ => (1 : ℂ)) w (zminus : ℂ) w')) = 1 := by
      apply Finset.prod_eq_one
      intro w' hw'
      by_cases h : w' = w
      · subst w'
        simp [zminus]
      · simp [Function.update_of_ne h, zminus]
    change (∏ v : S.Sf, absFin v.1 1) *
        (∏ w' : InfinitePlace F,
          Complex.normSq (Function.update (fun _ => (1 : ℂ)) w (zminus : ℂ) w')) = 1
    rw [hfinprod, harchprod]
    simp
  have hzminusNorm : ‖(zminus : ℂ)‖ = 1 := by norm_num [zminus]
  have hAClass : cls a = 1 := by
    change (QuotientGroup.mk a : S.V) = 1
    rw [QuotientGroup.eq_one_iff]
    change a ∈ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range
    exact MonoidHom.mem_range.mpr ⟨S.atComplex w zroot, haSix⟩
  have hBcut (y : S.FSˣ) :
      bCut (Bd := Bd) (a * y) = bCut (Bd := Bd) y := by
    have hcls : cls (a * y) = cls y := by
      calc
        cls (a * y) = cls a * cls y := by simp [cls]
        _ = cls y := by rw [hAClass]; exact one_mul (cls y)
    unfold bCut
    rw [hcls]
  have hOmegaAt : IsFundamentalAt (omegaAt R l) l := by
    simpa [IsFundamentalAt, omegaAt, bridgeFundamentalAt, bridgeOmegaAt] using
      (a2_bridge_SHEET (D := D) (S := S) (G := R.sheets) l hl).1
  let e : S.FS ≃ᵐ S.FS := {
    toEquiv := {
      toFun := fun y => (a : S.FS) * y
      invFun := fun y => (a⁻¹ : S.FS) * y
      left_inv := by intro y; simp [mul_assoc]
      right_inv := by intro y; simp [mul_assoc] }
    measurable_toFun := rf_measurable_leftMul (a : S.FS)
    measurable_invFun := rf_measurable_leftMul (a⁻¹ : S.FS) }
  let Oa : Set S.FS := {z | ∃ x ∈ omegaAt R l, (a : S.FS) * x = z}
  have hOaeq : Oa = e '' omegaAt R l := by
    ext z
    simp [Oa, e]
  have hai : ai = (a : S.FS)⁻¹ := by
    change ((a⁻¹ : S.FSˣ) : S.FS) = (a : S.FS)⁻¹
    exact Units.val_inv_eq_inv_val a
  have hmulAI : (a : S.FS) * ai = 1 := by
    change ((a * a⁻¹ : S.FSˣ) : S.FS) = 1
    simp [ai]
  have hNormAinv : S.absS ai = 1 := by
    have hnormmul := (a2_bridge_NORM D S).2.1 (a : S.FS) ai
    rw [hmulAI] at hnormmul
    have hNormOne : S.absS (1 : S.FS) = 1 := by
      simp [SData.absS, hAbsOne]
    rw [hNormOne] at hnormmul
    simp [hNormA] at hnormmul
    exact hnormmul.symm
  have hRotMem (γ : Gamma S) (y : S.FSˣ) :
      ((S.diagU (γ.1 : Fˣ))⁻¹ * y : S.FSˣ).val ∈ Oa ↔
        ((S.diagU (γ.1 : Fˣ))⁻¹ * (a⁻¹ * y : S.FSˣ) : S.FSˣ).val ∈
          omegaAt R l := by
    constructor
    · intro hmem
      rcases hmem with ⟨x, hx, hxeq⟩
      have hxunit := (hOmegaAt.2.1 x hx).1
      let xu : S.FSˣ := hxunit.unit
      have hxu_mem : (xu : S.FS) ∈ omegaAt R l := by
        rw [← hxunit.unit_spec] at hx
        exact hx
      have hxeqUnit : a * xu = (S.diagU (γ.1 : Fˣ))⁻¹ * y := by
        have hxeq' := hxeq
        rw [← hxunit.unit_spec] at hxeq'
        apply Units.ext
        change (a : S.FS) * (xu : S.FS) =
          ((S.diagU (γ.1 : Fˣ))⁻¹ * y : S.FS)
        exact hxeq'
      have hxu : xu = (S.diagU (γ.1 : Fˣ))⁻¹ * (a⁻¹ * y) := by
        calc
          xu = 1 * xu := by simp
          _ = a⁻¹ * (a * xu) := by simp [mul_assoc]
          _ = a⁻¹ * ((S.diagU (γ.1 : Fˣ))⁻¹ * y) := by rw [hxeqUnit]
          _ = (S.diagU (γ.1 : Fˣ))⁻¹ * (a⁻¹ * y) := by ac_rfl
      rw [hxu] at hxu_mem
      exact hxu_mem
    · intro hx
      refine ⟨((S.diagU (γ.1 : Fˣ))⁻¹ * (a⁻¹ * y : S.FSˣ) : S.FS), hx, ?_⟩
      change (a : S.FS) *
          ((S.diagU (γ.1 : Fˣ))⁻¹ * (a⁻¹ * y : S.FSˣ) : S.FS) =
        ((S.diagU (γ.1 : Fˣ))⁻¹ * y : S.FS)
      simp [mul_assoc, mul_left_comm, mul_comm]
  have hOa : IsFundamentalAt Oa l := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hOaeq]
      exact e.measurableSet_image.mpr hOmegaAt.1
    · intro y hy
      rcases hy with ⟨x, hx, hxy⟩
      obtain ⟨hxunit, hxnorm⟩ := hOmegaAt.2.1 x hx
      refine ⟨?_, ?_⟩
      · rw [← hxy]
        exact (a.isUnit_units_mul x).2 hxunit
      calc
        S.absS y = S.absS ((a : S.FS) * x) := by rw [hxy]
        _ = S.absS (a : S.FS) * S.absS x :=
          (a2_bridge_NORM D S).2.1 _ _
        _ = 1 * l := by rw [hNormA, hxnorm]
        _ = l := one_mul l
    · intro y hy
      let y' : S.FSˣ := a⁻¹ * y
      have hy'val : (y' : S.FS) =
          ai * (y : S.FS) := by
        simpa [ai, y'] using congrArg (fun z : S.FSˣ => (z : S.FS)) (rfl : y' = a⁻¹ * y)
      have hy' : S.absS (y' : S.FS) = l := by
        calc
          S.absS (y' : S.FS) = S.absS ai * S.absS (y : S.FS) := by
            rw [hy'val]
            exact (a2_bridge_NORM D S).2.1 ai (y : S.FS)
          _ = 1 * l := by rw [hNormAinv, hy]
          _ = l := one_mul l
      obtain ⟨γ, hγ, hγuniq⟩ := hOmegaAt.2.2 y' hy'
      refine ⟨γ, (hRotMem γ y).2 (by simpa [y'] using hγ), ?_⟩
      intro γ' hγ'
      apply hγuniq γ'
      exact (hRotMem γ' y).1 hγ'
  have hmp : MeasurePreserving (e : S.FS → S.FS)
      (R.sheets.sheet l) (R.sheets.sheet l) := by
    refine ⟨e.measurable, ?_⟩
    change Measure.map (fun y : S.FS => (a : S.FS) * y) (R.sheets.sheet l) =
      R.sheets.sheet l
    simpa [hNormA] using R.sheets.sheet_translate a l hl
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
  have hGammaAction (γ : Gamma S) (y : S.FS) :
      γ • y = (S.diagU (γ.1 : Fˣ) : S.FS) * y := by
    change (rfGammaDiag (S := S) γ : S.FS) * y = _
    rw [rfGammaDiag_eq]
  letI : MeasurableConstSMul (Gamma S) S.FS := ⟨fun γ => by
    change Measurable (fun y : S.FS => (rfGammaDiag (S := S) γ : S.FS) * y)
    exact rf_measurable_leftMul _⟩
  letI : Countable (Gamma S) :=
    (a2_bridge_SHEET (D := D) (S := S) (G := R.sheets) l hl).2.2
  have hGammaNorm (γ : Gamma S) :
      S.absS (rfGammaDiag (S := S) γ : S.FS) = 1 := by
    rw [rfGammaDiag_eq]
    exact (a2_bridge_NORM D S).2.2.2.1 (γ.1 : S.US)
  have hGammaPres (γ : Gamma S) : MeasurePreserving (fun y : S.FS => γ • y)
      (R.sheets.sheet l) (R.sheets.sheet l) := by
    refine ⟨measurable_const_smul γ, ?_⟩
    change Measure.map (fun y : S.FS =>
      (rfGammaDiag (S := S) γ : S.FS) * y) (R.sheets.sheet l) = R.sheets.sheet l
    simpa [hGammaNorm γ] using
      R.sheets.sheet_translate (rfGammaDiag (S := S) γ) l hl
  letI : SMulInvariantMeasure (Gamma S) S.FS (R.sheets.sheet l) := ⟨fun γ t ht => by
    calc
      R.sheets.sheet l ((fun y : S.FS => γ • y) ⁻¹' t) =
          Measure.map (fun y : S.FS => γ • y) (R.sheets.sheet l) t :=
        (Measure.map_apply (measurable_const_smul γ) ht).symm
      _ = R.sheets.sheet l t := by rw [(hGammaPres γ).map_eq]⟩
  have hGammaInv (γ : Gamma S) (y : S.FS) :
      γ⁻¹ • y = ((S.diagU (γ.1 : Fˣ))⁻¹ : S.FS) * y := by
    calc
      γ⁻¹ • y = (S.diagU ((γ⁻¹).1 : Fˣ) : S.FS) * y := hGammaAction γ⁻¹ y
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
      rw [hGammaInv]
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
        rw [hGammaInv] at hleft
        simpa [yu, hyunit.unit_spec] using hleft
      have h1mem : ((S.diagU ((1 : Gamma S).1 : Fˣ))⁻¹ * yu : S.FSˣ).val ∈ O' := by
        simpa [yu, hyunit.unit_spec] using hright
      have hγδ := huniq γ hγmem
      have h1δ := huniq 1 h1mem
      exact hγ (hγδ.trans h1δ.symm)
    refine MeasureTheory.IsFundamentalDomain.mk'' hO'.1.nullMeasurableSet hcover hdis ?_
    intro γ
    exact (hGammaPres γ).quasiMeasurePreserving
  have hOmegaDomain := mkDomain (omegaAt R l) hOmegaAt
  have hOaDomain := mkDomain Oa hOa
  have hASmul (y : S.FSˣ) :
      R.C.aS a * R.C.aS y = R.C.aS (a * y) := by
    have hHS : S.HS H a y = 1 := by
      unfold SData.HS
      apply Finset.prod_eq_one
      intro v hv
      have hcomp : S.compU v a = 1 := by
        apply Units.ext
        simp [a, SData.atComplex, SData.compU]
      have hhilb : H.hilb v.1 1 (S.compU v y) = 1 := by
        let b := H.hilb v.1 1 (S.compU v y)
        have hb : b = b * b := by
          simpa only [one_mul] using H.mul_left v.1 1 1 (S.compU v y)
        have hb' : b * 1 = b * b := by simpa using hb
        exact (mul_left_cancel hb').symm
      rw [hcomp]
      exact hhilb
    have hmu : muThree D (S.HS H a y) = 1 := by
      rw [hHS]
      apply Subtype.ext
      apply Units.ext
      simp [muThree]
    have h := R.C.aS_mul a y
    rw [hmu] at h
    simpa using h
  have hLz (u : UnitSix S) : Lvalue R u a = -1 := by
    change (((R.chars.L u).L a : ℂˣ) : ℂ) = -1
    rw [(R.chars.L u).angular w zminus]
    rcases (R.chars.L u).hm w with hm | hm
    · rw [hm]
      simp [omegaAng, zminus]
    · rw [hm]
      simp [omegaAng, zminus]
  have hLmul (u : UnitSix S) (y : S.FSˣ) :
      Lvalue R u (a * y) = Lvalue R u a * Lvalue R u y := by
    simp [Lvalue, map_mul]
  have hwA : R.C.wS * R.C.aS a = R.C.aS a * R.C.wS := by
    have hwA' : R.C.wS * R.C.aS a * R.C.wS⁻¹ = R.C.aS a := by
      rw [R.C.liftS_wa a, haInv]
    calc
      R.C.wS * R.C.aS a = (R.C.wS * R.C.aS a * R.C.wS⁻¹) * R.C.wS := by
        simp [mul_assoc]
      _ = R.C.aS a * R.C.wS := by rw [hwA']
  have hRatComm : R.C.rat weylGL * R.C.aS a = R.C.aS a * R.C.rat weylGL := by
    have hExtA : R.C.wExt * R.C.aS a = R.C.aS a * R.C.wExt :=
      R.C.Kext_comm_S R.C.wExt R.C.wExt_Kext (R.C.aS a) (R.C.aS_mem a)
    calc
      R.C.rat weylGL * R.C.aS a = (R.C.wS * R.C.wExt) * R.C.aS a := by
        rw [R.C.rat_weyl]
      _ = R.C.wS * (R.C.wExt * R.C.aS a) := by simp [mul_assoc]
      _ = R.C.wS * (R.C.aS a * R.C.wExt) := by rw [hExtA]
      _ = (R.C.wS * R.C.aS a) * R.C.wExt := by simp [mul_assoc]
      _ = (R.C.aS a * R.C.wS) * R.C.wExt := by rw [hwA]
      _ = R.C.aS a * (R.C.wS * R.C.wExt) := by simp [mul_assoc]
      _ = R.C.aS a * R.C.rat weylGL := by rw [R.C.rat_weyl]
  have hThetaRadial (u : UnitSix S) (g : R.C.G) :
      R.T.θN (R.chars.L u) (R.C.aS a * g) = R.T.θN (R.chars.L u) g :=
    R.T.T7 (R.chars.L u) (R.mem_family u) w zminus hzminusNorm g
  refine ⟨?_, ?_⟩
  · intro minus
    let u := rowClass R r
    let f : S.FSˣ → ℂ := fun y =>
      bCut (Bd := Bd) y * (Lvalue R u y)⁻¹ * digitSum R r minus true y
    have hPoint (d : Digits R r) (y : S.FSˣ) :
        digitPoint R r (a * y) d = R.C.aS a * digitPoint R r y d := by
      unfold digitPoint
      rw [← hASmul y]
      simp [mul_assoc]
    have hThetaPoint (d : Digits R r) (y : S.FSˣ) :
        R.T.θN (R.chars.L u)
            ((if minus then R.C.rat weylGL else 1) * digitPoint R r (a * y) d) =
          R.T.θN (R.chars.L u)
            ((if minus then R.C.rat weylGL else 1) * digitPoint R r y d) := by
      cases minus with
      | false =>
        change R.T.θN (R.chars.L u)
            (1 * digitPoint R r (a * y) d) =
          R.T.θN (R.chars.L u) (1 * digitPoint R r y d)
        calc
          R.T.θN (R.chars.L u) (1 * digitPoint R r (a * y) d) =
              R.T.θN (R.chars.L u) (R.C.aS a * digitPoint R r y d) := by
            rw [one_mul, hPoint]
          _ = R.T.θN (R.chars.L u) (digitPoint R r y d) :=
            hThetaRadial u (digitPoint R r y d)
          _ = R.T.θN (R.chars.L u) (1 * digitPoint R r y d) := by rw [one_mul]
      | true =>
        change R.T.θN (R.chars.L u)
            (R.C.rat weylGL * digitPoint R r (a * y) d) =
          R.T.θN (R.chars.L u) (R.C.rat weylGL * digitPoint R r y d)
        rw [hPoint]
        calc
          R.T.θN (R.chars.L u)
              (R.C.rat weylGL * (R.C.aS a * digitPoint R r y d)) =
            R.T.θN (R.chars.L u)
              (R.C.aS a * (R.C.rat weylGL * digitPoint R r y d)) := by
                congr 1
                calc
                  R.C.rat weylGL * (R.C.aS a * digitPoint R r y d) =
                      (R.C.rat weylGL * R.C.aS a) * digitPoint R r y d := by
                        simp [mul_assoc]
                  _ = (R.C.aS a * R.C.rat weylGL) * digitPoint R r y d := by
                    rw [hRatComm]
                  _ = R.C.aS a * (R.C.rat weylGL * digitPoint R r y d) := by
                    simp [mul_assoc]
          _ = R.T.θN (R.chars.L u) (R.C.rat weylGL * digitPoint R r y d) :=
            hThetaRadial u (R.C.rat weylGL * digitPoint R r y d)
    have hDigitSum (y : S.FSˣ) :
        digitSum R r minus true (a * y) = digitSum R r minus true y := by
      unfold digitSum
      apply finsum_congr
      intro d
      simp only [if_true]
      rw [hThetaPoint]
    have hLinv (y : S.FSˣ) :
        (Lvalue R u (a * y))⁻¹ = -(Lvalue R u y)⁻¹ := by
      rw [hLmul, hLz]
      simp
    have hSignUnit (y : S.FSˣ) : f (a * y) = -f y := by
      dsimp [f]
      rw [hBcut, hLinv, hDigitSum]
      ring
    rcases rf_descent R with ⟨_, hDigitGamma, hCutGamma, hLGamma⟩
    have hCharMul (x y : S.FSˣ) :
        Lvalue R u (x * y) = Lvalue R u x * Lvalue R u y := by
      simp [Lvalue, map_mul]
    have hInvUnit (γ : Gamma S) (y : S.FSˣ) :
        f (S.diagU (γ.1 : Fˣ) * y) = f y := by
      dsimp [f]
      rw [hCutGamma γ y, hCharMul, hLGamma u γ,
        hDigitGamma r γ y minus true]
      simp
    have hInv (γ : Gamma S) (y : S.FS) : onUnits f (γ • y) = onUnits f y := by
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
        exact hInvUnit γ hy.unit
      · have hmul : ¬ IsUnit ((S.diagU (γ.1 : Fˣ) : S.FS) * y) :=
          fun h => hy ((S.diagU (γ.1 : Fˣ)).isUnit_units_mul y |>.1 h)
        simp [onUnits, hy, hmul]
    have hSignOnUnits (y : S.FS) : onUnits f ((a : S.FS) * y) = -onUnits f y := by
      by_cases hy : IsUnit y
      · have hmul : IsUnit ((a : S.FS) * y) := (a.isUnit_units_mul y).2 hy
        have hmulval : hmul.unit = a * hy.unit := by
          apply Units.ext
          simp [hy.unit_spec]
        have hleft : onUnits f ((a : S.FS) * y) = f hmul.unit := by
          simp [onUnits, hmul]
        have hright : onUnits f y = f hy.unit := by simp [onUnits, hy]
        rw [hleft, hright, hmulval]
        exact hSignUnit hy.unit
      · have hmul : ¬ IsUnit ((a : S.FS) * y) :=
          fun h => hy (a.isUnit_units_mul y |>.1 h)
        simp [onUnits, hy, hmul]
    have hSignIntegral :
        (∫ y in omegaAt R l, onUnits f ((a : S.FS) * y) ∂(R.sheets.sheet l)) =
          -(∫ y in omegaAt R l, onUnits f y ∂(R.sheets.sheet l)) := by
      calc
        _ = ∫ y in omegaAt R l, -onUnits f y ∂(R.sheets.sheet l) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hSignOnUnits
        _ = _ := by rw [integral_neg]
    have hCompare :
        (∫ y in Oa, onUnits f y ∂(R.sheets.sheet l)) =
          ∫ y in omegaAt R l, onUnits f y ∂(R.sheets.sheet l) :=
      hOaDomain.setIntegral_eq hOmegaDomain hInv
    have hChange :
        (∫ y in Oa, onUnits f y ∂(R.sheets.sheet l)) =
          ∫ y in omegaAt R l, onUnits f ((a : S.FS) * y) ∂(R.sheets.sheet l) := by
      rw [hOaeq]
      exact hmp.setIntegral_image_emb e.measurableEmbedding (onUnits f) (omegaAt R l)
    have hEq : omegaInt R l f = -omegaInt R l f := by
      calc
        omegaInt R l f = ∫ y in omegaAt R l, onUnits f y ∂(R.sheets.sheet l) := rfl
        _ = ∫ y in Oa, onUnits f y ∂(R.sheets.sheet l) := hCompare.symm
        _ = ∫ y in omegaAt R l, onUnits f ((a : S.FS) * y) ∂(R.sheets.sheet l) := hChange
        _ = -omegaInt R l f := by simpa [omegaInt] using hSignIntegral
    exact CharZero.eq_neg_self_iff.mp hEq
  · have hDigit := (rf_descent R).1 r
    unfold thetaAverage omegaInt
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun y => ?_
    by_cases hy : IsUnit y
    · simp [onUnits, hy, hDigit]
    · simp [onUnits, hy]
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
  intro v hv ν
  have hmask : maskAlpha D A v (primeGen R v) 0 0 =
      1 - (qI v.asIdeal : ℂ)⁻¹ := by
    simp [maskAlpha, qI]
  rw [hmask, R.T.Wv_right v hv (R.C.a v (toLoc v ν)) (R.C.w v)
    (R.C.w_Kext v hv) (R.C.w_mem v)]
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

private lemma rf_idealExp_zero_of_not_dvd (v : FinPlace F) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hnd : ¬ v.asIdeal ∣ I) : idealExp v I = 0 := by
  by_contra hne
  have hpos : 0 < idealExp v I := Nat.pos_of_ne_zero hne
  have hpowdvd : v.asIdeal ^ idealExp v I ∣ I := by
    change v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors ∣ I
    rw [← Associates.mk_dvd_mk, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le
      (Associates.mk_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hI))
      v.associates_irreducible).2 le_rfl
  exact hnd (dvd_trans (dvd_pow_self _ (Nat.ne_of_gt hpos)) hpowdvd)

private lemma rf_extIdeal_eq_of_numerator_exponents (f a b : S.ExtIdeal)
    (ha : activeNumerator R f a) (hb : activeNumerator R f b)
    (hexp : ∀ v ∈ R.exterior.support f, idealExp v a.1 = idealExp v b.1) : a = b := by
  apply Subtype.ext
  have ha0 : a.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using a.2.1
  have hb0 : b.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using b.2.1
  have hmax (v : FinPlace F) : v.maxPowDividing a.1 = v.maxPowDividing b.1 := by
    by_cases hvf : v ∈ R.exterior.support f
    · have he := hexp v hvf
      change v.asIdeal ^ idealExp v a.1 = v.asIdeal ^ idealExp v b.1
      rw [he]
    · have hnotA : ¬ v.asIdeal ∣ a.1 := by
        intro hdiv
        exact hvf (ha.1 v ((R.exterior.mem_support a v).2 hdiv))
      have hnotB : ¬ v.asIdeal ∣ b.1 := by
        intro hdiv
        exact hvf (hb.1 v ((R.exterior.mem_support b v).2 hdiv))
      have hzeroA := rf_idealExp_zero_of_not_dvd v
        (by simpa [Ideal.zero_eq_bot] using a.2.1) hnotA
      have hzeroB := rf_idealExp_zero_of_not_dvd v
        (by simpa [Ideal.zero_eq_bot] using b.2.1) hnotB
      change v.asIdeal ^ idealExp v a.1 = v.asIdeal ^ idealExp v b.1
      rw [hzeroA, hzeroB]
  calc
    a.1 = ∏ᶠ v : FinPlace F, v.maxPowDividing a.1 :=
      (Ideal.finprod_heightOneSpectrum_factorization ha0).symm
    _ = ∏ᶠ v : FinPlace F, v.maxPowDividing b.1 := finprod_congr hmax
    _ = b.1 := Ideal.finprod_heightOneSpectrum_factorization hb0

private lemma rf_betaIdeal_sum_le_Eideal (f : S.ExtIdeal) (Aset : Finset S.ExtIdeal)
    (hA : ∀ a ∈ Aset, activeNumerator R f a) :
    (∑ a ∈ Aset, betaIdeal R f a) ≤ Eideal R f 0 := by
  classical
  let V : Type := {v : FinPlace F // v ∈ R.exterior.support f}
  letI : Fintype V := Finset.Subtype.fintype (R.exterior.support f)
  let E : V → Finset ℕ := fun v => Aset.image (fun a => idealExp v.1 a.1)
  let Aidx : Type := {a : S.ExtIdeal // a ∈ Aset}
  letI : Fintype Aidx := Aset.finite_toSet.fintype
  let ExpVec : Type := V → ℕ
  let expCode (a : Aidx) : ExpVec := fun v => idealExp v.1 a.1.1
  have hExpCodeIn (a : Aidx) : expCode a ∈ Fintype.piFinset E := by
    apply Fintype.mem_piFinset.mpr
    intro v
    exact Finset.mem_image.mpr ⟨a.1, a.2, rfl⟩
  have hExpCodeInj : Function.Injective expCode := by
    intro a b hab
    apply Subtype.ext
    apply rf_extIdeal_eq_of_numerator_exponents R f a.1 b.1 (hA a.1 a.2) (hA b.1 b.2)
    intro v hv
    have h := congrFun hab ⟨v, hv⟩
    exact h
  let localBeta (v : V) (e : ℕ) : ℝ :=
    betaPrime (qI v.1.asIdeal) (qI_prime_gt_one v.1) e
  let codeWeight (x : ExpVec) : ℝ := ∏ v : V, localBeta v (x v)
  have hlocalNonneg (v : V) (e : ℕ) : 0 ≤ localBeta v e := by
    have hvS : v.1 ∉ S.Sf := R.exterior.support_exterior f v.1 v.2
    have hbound := (rf_active_support_bounds R).2.1 v.1 hvS 0 e
    exact le_trans (norm_nonneg _) hbound
  have hcodeNonneg (x : ExpVec) : 0 ≤ codeWeight x := by
    unfold codeWeight
    apply Finset.prod_nonneg
    intro v hv
    exact hlocalNonneg v (x v)
  have hBetaIdealCode (a : Aidx) : betaIdeal R f a.1 = codeWeight (expCode a) := by
    unfold betaIdeal
    rw [← Finset.prod_coe_sort]
  have hsumA (g : S.ExtIdeal → ℝ) :
      (∑ a : Aidx, g a.1) = ∑ a ∈ Aset, g a := by
    change (∑ a ∈ (Finset.univ : Finset Aidx), g a.1) = _
    refine Finset.sum_bij (fun a _ => a.1) ?_ ?_ ?_ ?_
    · intro a ha
      exact a.2
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro b hb
      exact ⟨⟨b, hb⟩, by simp, rfl⟩
    · intro a ha
      rfl
  let codeSet : Finset ExpVec := (Finset.univ : Finset Aidx).image expCode
  have hcodeSet : codeSet ⊆ Fintype.piFinset E := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    exact hExpCodeIn a
  have hsumCodes :
      (∑ a : Aidx, codeWeight (expCode a)) = ∑ x ∈ codeSet, codeWeight x := by
    dsimp [codeSet]
    symm
    exact Finset.sum_image (fun a ha b hb hab => hExpCodeInj hab)
  have hpiSum :
      (∑ x ∈ Fintype.piFinset E, codeWeight x) =
        ∏ v : V, ∑ e ∈ E v, localBeta v e := by
    dsimp [codeWeight]
    exact (Finset.prod_univ_sum E localBeta).symm
  have hlocalSum (v : V) :
      (∑ e ∈ E v, localBeta v e) ≤ Eprime v.1 0 := by
    have hvS : v.1 ∉ S.Sf := R.exterior.support_exterior f v.1 v.2
    obtain ⟨hsummable, _, _⟩ :=
      (rf_active_support_bounds R).2.2.1 v.1 hvS 0 (by norm_num)
    have hs : Summable (fun e : ℕ => localBeta v e) := by
      simpa [localBeta, zero_mul, Real.rpow_zero] using hsummable
    calc
      _ ≤ ∑' e : ℕ, localBeta v e :=
        hs.sum_le_tsum (E v) (fun e he => hlocalNonneg v e)
      _ = Eprime v.1 0 := by
        simp [Eprime, localBeta, zero_mul]
  have hlocalSumNonneg (v : V) : 0 ≤ ∑ e ∈ E v, localBeta v e := by
    apply Finset.sum_nonneg
    intro e he
    exact hlocalNonneg v e
  have hEprimeNonneg (v : V) : 0 ≤ Eprime v.1 0 :=
    (hlocalSumNonneg v).trans (hlocalSum v)
  have hprodBound :
      (∏ v : V, ∑ e ∈ E v, localBeta v e) ≤ ∏ v : V, Eprime v.1 0 := by
    apply Finset.prod_le_prod₀
    · intro v hv
      exact hlocalSumNonneg v
    · intro v hv
      exact hlocalSum v
  have hprodE : (∏ v : V, Eprime v.1 0) = Eideal R f 0 := by
    unfold Eideal
    exact Finset.prod_coe_sort (R.exterior.support f) (fun v => Eprime v 0)
  calc
    (∑ a ∈ Aset, betaIdeal R f a) = ∑ a : Aidx, betaIdeal R f a.1 :=
      (hsumA (betaIdeal R f)).symm
    _ = ∑ a : Aidx, codeWeight (expCode a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hBetaIdealCode a
    _ = ∑ x ∈ codeSet, codeWeight x := hsumCodes
    _ ≤ ∑ x ∈ Fintype.piFinset E, codeWeight x :=
      Finset.sum_le_sum_of_subset_of_nonneg hcodeSet (fun x hx hnot => hcodeNonneg x)
    _ = ∏ v : V, ∑ e ∈ E v, localBeta v e := hpiSum
    _ ≤ ∏ v : V, Eprime v.1 0 := hprodBound
    _ = Eideal R f 0 := hprodE

private lemma rf_sqf_norm_dyad_bounds (c : S.SqfExtIdeal) :
    let k := Nat.log 2 (Ideal.absNorm c.1)
    ((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧
      qI c.1 < ((2 ^ (k + 1) : ℕ) : ℝ) := by
  dsimp only
  have hI : c.1 ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using c.2.1.1
  have hnormpos : 0 < Ideal.absNorm c.1 :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨c.1, mem_nonZeroDivisors_iff_ne_zero.mpr
        (by simpa [Ideal.zero_eq_bot] using hI)⟩
  have hn : Ideal.absNorm c.1 ≠ 0 := by
    exact Nat.ne_of_gt hnormpos
  constructor
  · change ((2 ^ Nat.log 2 (Ideal.absNorm c.1) : ℕ) : ℝ) ≤
      (Ideal.absNorm c.1 : ℝ)
    exact_mod_cast Nat.pow_log_le_self 2 hn
  · change (Ideal.absNorm c.1 : ℝ) <
      ((2 ^ (Nat.log 2 (Ideal.absNorm c.1) + 1) : ℕ) : ℝ)
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _

private lemma rf_retained_cutoff_components (qa qc qn R0 : ℝ)
    (hqa : 1 ≤ qa) (hqc : 1 ≤ qc) (hqn : 1 ≤ qn)
    (hQ : qa * qc * qn ^ 3 ≤ R0) : qa ≤ R0 ∧ qc ≤ R0 ∧ qn ≤ R0 := by
  have hqn2 : 1 ≤ qn ^ 2 := one_le_pow₀ hqn
  have hqn3 : qn ≤ qn ^ 3 := by
    calc
      qn = qn * 1 := by ring
      _ ≤ qn * qn ^ 2 := mul_le_mul_of_nonneg_left hqn2 (by linarith)
      _ = qn ^ 3 := by ring
  have hone3 : 1 ≤ qn ^ 3 := by
    calc
      1 = 1 * 1 * 1 := by ring
      _ ≤ qn * qn * qn := by gcongr
      _ = qn ^ 3 := by ring
  have hqaQ : qa ≤ qa * qc * qn ^ 3 := by
    calc
      qa = qa * 1 * 1 := by ring
      _ ≤ qa * qc * qn ^ 3 := by
        gcongr
  have hqcQ : qc ≤ qa * qc * qn ^ 3 := by
    calc
      qc = 1 * qc * 1 := by ring
      _ ≤ qa * qc * qn ^ 3 := by gcongr
  have hqnQ : qn ≤ qa * qc * qn ^ 3 := by
    calc
      qn ≤ qn ^ 3 := hqn3
      _ = 1 * 1 * qn ^ 3 := by ring
      _ ≤ qa * qc * qn ^ 3 := by gcongr
  exact ⟨hqaQ.trans hQ, hqcQ.trans hQ, hqnQ.trans hQ⟩

private lemma rf_retained_qI_ge_one (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    1 ≤ qI I := by
  have hn : 0 < Ideal.absNorm I :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hI)⟩
  dsimp [qI]
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))

private lemma rf_retained_split_zero_of_cutoff_lt_one (υ : UnitSix S)
    (h d : S.ExtIdeal) (Z R0 : ℝ) (hR0 : R0 < 1) :
    splitReflection R true υ h d Z R0 = 0 := by
  classical
  have hnot (p : FrozenIndex R h × Bd.B × Bd.B × S.SqfExtIdeal) :
      ¬ qI p.1.a.1 * qI p.2.2.2.1 * qI p.1.n.1 ^ 3 ≤ R0 := by
    let qa := qI p.1.a.1
    let qc := qI p.2.2.2.1
    let qn := qI p.1.n.1
    have hqa : 1 ≤ qa := rf_retained_qI_ge_one p.1.a.1 p.1.a.2.1
    have hqc : 1 ≤ qc := rf_retained_qI_ge_one p.2.2.2.1
      (by simpa using p.2.2.2.2.1.1)
    have hqn : 1 ≤ qn := rf_retained_qI_ge_one p.1.n.1 p.1.n.2.1
    have hqn3 : 1 ≤ qn ^ 3 := one_le_pow₀ hqn
    have hQ : 1 ≤ qa * qc * qn ^ 3 := by
      calc
        1 = 1 * 1 * 1 := by ring
        _ ≤ qa * qc * qn ^ 3 := by gcongr
    exact not_le_of_gt (lt_of_lt_of_le hR0 hQ)
  by_cases hdc : Squarefree d.1 ∧ IsCoprime d.1 h.1
  · simp [splitReflection, hdc, hnot]
  · simp [splitReflection, hdc]

private lemma rf_retained_natlog_count (X : ℝ) (hX : 1 ≤ X) :
    (((Nat.log 2 ⌊X⌋₊ + 1 : ℕ) : ℝ) ≤
      (1 / Real.log 2) * Real.log (2 * X)) := by
  let n : ℕ := ⌊X⌋₊
  let N : ℕ := Nat.log 2 n
  have hn : 1 ≤ n := by
    dsimp [n]
    exact Nat.le_floor (by exact_mod_cast hX)
  have hpow : 2 ^ (N + 1) ≤ 2 * n := by
    calc
      2 ^ (N + 1) = 2 ^ N * 2 := by rw [pow_succ]
      _ ≤ n * 2 := Nat.mul_le_mul_right 2
        (Nat.pow_log_le_self 2 (by omega : n ≠ 0))
      _ = 2 * n := by omega
  have hlogNat : N + 1 ≤ Nat.log 2 (2 * n) := by
    dsimp [N]
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
  have hlogb : ((N + 1 : ℕ) : ℝ) ≤ Real.logb 2 (2 * (n : ℝ)) := by
    calc
      ((N + 1 : ℕ) : ℝ) ≤ (Nat.log 2 (2 * n) : ℝ) := by exact_mod_cast hlogNat
      _ = (Nat.log2 (2 * n) : ℝ) := by simp [Nat.log2_eq_log_two]
      _ ≤ Real.logb 2 (2 * (n : ℝ)) := by
        convert Real.log2_le_logb (2 * n) using 1 <;> norm_cast
  have hfloor : (n : ℝ) ≤ X := by
    dsimp [n]
    exact Nat.floor_le (le_trans (by norm_num) hX)
  have hlogbX : Real.logb 2 (2 * (n : ℝ)) ≤ Real.logb 2 (2 * X) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
      (by nlinarith [hfloor])
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogCount : ((N + 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (2 * X) := by
    apply (le_div_iff₀ hlog2).1
    simpa [Real.logb] using hlogb.trans hlogbX
  have hNdef : N = Nat.log 2 ⌊X⌋₊ := by rfl
  rw [← hNdef]
  have hdivide : ((Nat.log 2 ⌊X⌋₊ + 1 : ℕ) : ℝ) ≤
      Real.log (2 * X) / Real.log 2 := (le_div_iff₀ hlog2).2 hlogCount
  calc
    ((Nat.log 2 ⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (2 * X) / Real.log 2 := hdivide
    _ = (1 / Real.log 2) * Real.log (2 * X) := by ring

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
  intro h t d c sd sc hsd hsc
  constructor
  · have hbridge := a2_bridge_NORM D S
    have hmul (x y : S.FSˣ) :
        S.absS ((x * y : S.FSˣ) : S.FS) =
          S.absS (x : S.FS) * S.absS (y : S.FS) := by
      exact hbridge.2.1 (x : S.FS) (y : S.FS)
    have hdiv (x y : S.FSˣ) :
        S.absS ((x / y : S.FSˣ) : S.FS) =
          S.absS (x : S.FS) / S.absS (y : S.FS) := hbridge.2.2.2.2.1 x y
    have hpow2 (x : S.FSˣ) :
        S.absS ((x ^ 2 : S.FSˣ) : S.FS) = S.absS (x : S.FS) ^ 2 := by
      simpa [pow_succ] using hmul x x
    have hpow3 (x : S.FSˣ) :
        S.absS ((x ^ 3 : S.FSˣ) : S.FS) = S.absS (x : S.FS) ^ 3 := by
      calc
        S.absS ((x ^ 3 : S.FSˣ) : S.FS) =
            S.absS ((x ^ (3 : ℤ) : S.FSˣ) : S.FS) := by
          exact (congrArg (fun z : S.FSˣ => S.absS (z : S.FS))
            (zpow_natCast x 3)).symm
        _ = S.absS (x : S.FS) ^ (3 : ℤ) := hbridge.2.2.2.2.2 x (3 : ℤ)
        _ = S.absS (x : S.FS) ^ 3 := rfl
    have heps : S.absS (S.diagU (R.sheets.eps t.u) : S.FS) = 1 :=
      hbridge.2.2.2.1 (R.sheets.eps t.u)
    have ha := a2_bridge_NORM_gen D S H Bd bc t.a
    have hc := a2_bridge_NORM_gen D S H Bd bc (R.exterior.ofSqf c)
    have hn := a2_bridge_NORM_gen D S H Bd bc t.n
    have hd := a2_bridge_NORM_gen D S H Bd bc d
    have hf := a2_bridge_NORM_gen D S H Bd bc t.f
    change S.absS (S.diagU (frozenFrequency R t d c) : S.FS) = _
    simp only [frozenFrequency, map_div, map_mul, map_pow]
    simp only [hdiv, hmul, hpow2, hpow3]
    rw [heps, ha, hc, hn, hd, hf]
    simp only [idealNorm, qI, R.exterior.ofSqf_val]
    ring
  · simp only [frozenFrequency, kappaSix, map_div, map_mul, map_pow]
    dsimp only [cls] at hsd hsc ⊢
    simp only [QuotientGroup.mk_div, QuotientGroup.mk_mul, QuotientGroup.mk_pow] at *
    rw [hsd, hsc]
    have hden (x y : S.V) : ((x * y) ^ 2)⁻¹ = x ^ (-2 : ℤ) * y ^ (-2 : ℤ) := by
      calc
        ((x * y) ^ 2)⁻¹ = (x * y) ^ (-2 : ℤ) := by
          rw [show (-2 : ℤ) = Int.negSucc 1 by rfl, zpow_negSucc]
        _ = x ^ (-2 : ℤ) * y ^ (-2 : ℤ) := mul_zpow x y (-2 : ℤ)
    rw [div_eq_mul_inv, hden]
    let pref : S.V := cls (S.diagU (R.sheets.eps t.u)) *
      cls (S.diagU (bc.gen t.a)) * sc.1 * cls (S.diagU (bc.gen t.n)) ^ 3
    change pref * (sd.1 ^ (-2 : ℤ) * cls (S.diagU (bc.gen t.f)) ^ (-2 : ℤ)) =
      (pref * sd.1 ^ (-2 : ℤ)) * cls (S.diagU (bc.gen t.f)) ^ (-2 : ℤ)
    exact (mul_assoc pref (sd.1 ^ (-2 : ℤ))
      (cls (S.diagU (bc.gen t.f)) ^ (-2 : ℤ))).symm
def activePartial (retained : Bool) (υ : UnitSix S) (h d f : S.ExtIdeal)
    (u : UnitSix S) (sd sc : Bd.B) (Z R0 : ℝ) : ℂ :=
  ∑' p : {t : FrozenIndex R h // t.f = f ∧ t.u = u} × S.SqfExtIdeal,
    if (qI p.1.1.a.1 * qI p.2.1 * qI p.1.1.n.1 ^ 3 ≤ R0) = retained then
      reflectedTerm R υ h d Z (p.1.1, sd, sc, p.2) else 0

private lemma rf_qI_pos_ge_one (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    0 < qI I ∧ 1 ≤ qI I := by
  have hn : 0 < Ideal.absNorm I :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hI)⟩
  constructor
  · dsimp [qI]
    exact_mod_cast hn
  · dsimp [qI]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))

private lemma rf_betaIdeal_nonneg (f a : S.ExtIdeal) : 0 ≤ betaIdeal R f a := by
  unfold betaIdeal
  apply Finset.prod_nonneg
  intro v hv
  have hq : 0 < qI v.asIdeal := lt_of_lt_of_le (by norm_num) (le_of_lt (qI_prime_gt_one v))
  dsimp [betaPrime]
  split_ifs <;> positivity

set_option maxHeartbeats 4000000
/-- Absolute-summability form of the pointwise discarded-slice bound. -/
private theorem rf_tail_bound_abs : ∀ δ σ N : ℝ, 0 < δ → 1 / 2 < σ → σ < N →
  ∃ C : ℝ, 0 < C ∧ ∀ υ P D0 Z h d f u sd sc,
    1 ≤ P → 1 ≤ D0 → 2 ≤ Z → P ≤ qI h.1 → qI h.1 < 2 * P →
    D0 ≤ qI d.1 → qI d.1 < 2 * D0 → IsPowerful h.1 → activeFactor R h f →
    let R0 := reflectionColumnCutoff P D0 Z δ
    let Src := {t : FrozenIndex R h // t.f = f ∧ t.u = u} × S.SqfExtIdeal
    Summable (fun p : Src => ‖if (qI p.1.1.a.1 * qI p.2.1 * qI p.1.1.n.1 ^ 3 ≤ R0) = false then
      reflectedTerm R υ h d Z (p.1.1, sd, sc, p.2) else 0‖) ∧
    (∑' p : Src, ‖if (qI p.1.1.a.1 * qI p.2.1 * qI p.1.1.n.1 ^ 3 ≤ R0) = false then
      reflectedTerm R υ h d Z (p.1.1, sd, sc, p.2) else 0‖) ≤
      C * reflectionColumnLength P D0 Z ^ σ *
        max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-(N - σ)) *
          sphericalMajorant (S := S) σ * Eideal R f σ := by
  intro δ σ N hδ hσ hN
  have hNpos : 0 < N := by linarith
  obtain ⟨α, hα, hprofN⟩ := (rf_profile_bound R).2.1
  obtain ⟨Cprof, hCprof, hprof⟩ := hprofN N hNpos 0
  obtain ⟨_, _, hGrouped⟩ := rf_grouped_absolute R σ hσ
  refine ⟨Cprof, hCprof, ?_⟩
  intro υ P D0 Z h d f u sd sc hP hD0 hZ hPh hPhigh hDd hDhigh hPower hActive
  have hPpos : 0 < P := by linarith
  have hDpos : 0 < D0 := by linarith
  have hZpos : 0 < Z := by linarith
  rcases rf_qI_pos_ge_one h.1 h.2.1 with ⟨hqH, hqHone⟩
  rcases rf_qI_pos_ge_one d.1 d.2.1 with ⟨hqD, hqDone⟩
  rcases rf_qI_pos_ge_one f.1 f.2.1 with ⟨hqF, hqFone⟩
  have hqFSquare : qI f.1 ^ 2 ≤ qI h.1 :=
    (rf_active_support_bounds R).1 h f hPower hActive
  have hqFSquareLt : qI f.1 ^ 2 < 2 * P := lt_of_le_of_lt hqFSquare hPhigh
  let L : ℝ := reflectionColumnLength P D0 Z
  let Tscale : ℝ := qI d.1 ^ 2 * qI f.1 ^ 2 / Z
  let R0 : ℝ := reflectionColumnCutoff P D0 Z δ
  let J : ℝ := max (Z ^ δ) L⁻¹
  let Cfac : ℝ := Cprof * L ^ σ * J ^ (-(N - σ))
  have hLpos : 0 < L := by
    dsimp [L, reflectionColumnLength]
    positivity
  have hTpos : 0 < Tscale := by
    dsimp [Tscale]
    positivity
  have hZδpos : 0 < Z ^ δ := Real.rpow_pos_of_pos hZpos δ
  have hJpos : 0 < J := lt_of_lt_of_le hZδpos (le_max_left _ _)
  have hCfac : 0 < Cfac := by dsimp [Cfac]; positivity
  have hZδT : 1 ≤ Z ^ δ := Real.one_le_rpow (by linarith) hδ.le
  have hqdSquare : qI d.1 ^ 2 ≤ 4 * D0 ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * D0 - qI d.1)
      (by positivity : 0 ≤ 2 * D0 + qI d.1)]
  have hqfSquare : qI f.1 ^ 2 ≤ 2 * P := hqFSquareLt.le
  have hnum : qI d.1 ^ 2 * qI f.1 ^ 2 ≤ 8 * D0 ^ 2 * P := by
    calc
      qI d.1 ^ 2 * qI f.1 ^ 2 ≤ (4 * D0 ^ 2) * (2 * P) :=
        mul_le_mul hqdSquare hqfSquare (by positivity) (by positivity)
      _ = 8 * D0 ^ 2 * P := by ring
  have hTL : Tscale ≤ L := by
    dsimp [Tscale, L, reflectionColumnLength]
    exact div_le_div_of_nonneg_right hnum hZpos.le
  have hTpow : Tscale ^ σ ≤ L ^ σ := Real.rpow_le_rpow hTpos.le hTL (by linarith)
  have hR0formula : R0 = Z ^ δ * L := by
    rfl
  have hJpow : 0 < J ^ (-(N - σ)) := Real.rpow_pos_of_pos hJpos (-(N - σ))
  let Src : Type := {t : FrozenIndex R h // t.f = f ∧ t.u = u} × S.SqfExtIdeal
  let Dst : Type := {a : S.ExtIdeal // activeNumerator R f a} × S.SqfExtIdeal × S.ExtIdeal
  have transportNumerator (t : FrozenIndex R h) (htf : t.f = f) :
      activeNumerator R f t.a := by
    rw [← htf]
    exact t.numerator
  let ψ : Src → Dst := fun p =>
    ((⟨p.1.1.a, transportNumerator p.1.1 p.1.2.1⟩ :
        {a : S.ExtIdeal // activeNumerator R f a}), (p.2, p.1.1.n))
  have hψ : Function.Injective ψ := by
    intro p q hpq
    rcases p with ⟨⟨t, ht⟩, c⟩
    rcases q with ⟨⟨t', ht'⟩, c'⟩
    change (((⟨t.a, transportNumerator t ht.1⟩ :
        {a : S.ExtIdeal // activeNumerator R f a}), (c, t.n)) =
      ((⟨t'.a, transportNumerator t' ht'.1⟩ :
        {a : S.ExtIdeal // activeNumerator R f a}), (c', t'.n))) at hpq
    have hsub := congrArg Prod.fst hpq
    have hpair := congrArg Prod.snd hpq
    have ha := congrArg Subtype.val hsub
    have hc := congrArg Prod.fst hpair
    have hn := congrArg Prod.snd hpair
    have htf : t.f = t'.f := ht.1.trans ht'.1.symm
    have hta : t.a = t'.a := ha
    have htn : t.n = t'.n := hn
    have htu : t.u = t'.u := ht.2.trans ht'.2.symm
    have htEq : t = t' := by
      cases t
      cases t'
      simp_all
    apply Prod.ext
    · apply Subtype.ext
      exact htEq
    · exact hc
  obtain ⟨hDir, hDirBound, _⟩ := hGrouped f
  have hMappedSum : Summable (fun p : Src => reflectedDirichletTerm R f σ (ψ p)) :=
    hDir.comp_injective hψ
  have hWeightNonneg : ∀ p : Dst, 0 ≤ reflectedDirichletTerm R f σ p := by
    intro p
    have hβ : 0 ≤ betaIdeal R f p.1.1 := rf_betaIdeal_nonneg R f p.1.1
    have hqa : 0 < qI p.1.1.1 :=
      (rf_qI_pos_ge_one p.1.1.1 p.1.1.2.1).1
    have hqc : 0 < qI p.2.1.1 :=
      (rf_qI_pos_ge_one p.2.1.1 p.2.1.2.1.1).1
    have hqn : 0 < qI p.2.2.1 := (rf_qI_pos_ge_one p.2.2.1 p.2.2.2.1).1
    unfold reflectedDirichletTerm
    apply mul_nonneg
    · apply div_nonneg
      · exact mul_nonneg hβ (Real.rpow_nonneg hqc.le _)
      · exact hqn.le
    · have hQ : 0 ≤ qI p.1.1.1 * qI p.2.1.1 * qI p.2.2.1 ^ 3 := by
        exact mul_nonneg (mul_nonneg hqa.le hqc.le) (pow_nonneg hqn.le 3)
      exact Real.rpow_nonneg hQ _
  have hMappedBound :
      (∑' p : Src, reflectedDirichletTerm R f σ (ψ p)) ≤
        sphericalMajorant (S := S) σ * Eideal R f σ := by
    calc
      (∑' p : Src, reflectedDirichletTerm R f σ (ψ p)) ≤
          ∑' p : Dst, reflectedDirichletTerm R f σ p :=
        tsum_comp_le_tsum_of_inj hDir hWeightNonneg hψ
      _ ≤ sphericalMajorant (S := S) σ * Eideal R f σ := hDirBound
  have hScaledSum : Summable (fun p : Src => Cfac * reflectedDirichletTerm R f σ (ψ p)) :=
    hMappedSum.mul_left Cfac
  have hScaledNonneg : ∀ p : Src,
      0 ≤ Cfac * reflectedDirichletTerm R f σ (ψ p) := by
    intro p
    exact mul_nonneg hCfac.le (hWeightNonneg (ψ p))
  have hScaledNorm : Summable (fun p : Src => ‖Cfac * reflectedDirichletTerm R f σ (ψ p)‖) := by
    exact hScaledSum.norm.congr fun p => by
      simp [abs_of_nonneg (hScaledNonneg p)]
  let act : Src → ℂ := fun p =>
    if R0 < qI p.1.1.a.1 * qI p.2.1 * qI p.1.1.n.1 ^ 3 then
      reflectedTerm R υ h d Z (p.1.1, sd, sc, p.2) else 0
  have hpoint : ∀ p : Src, ‖act p‖ ≤ Cfac * reflectedDirichletTerm R f σ (ψ p) := by
    intro p
    rcases p with ⟨⟨t, htu⟩, c⟩
    by_cases hle : qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 ≤ R0
    · have hnot : ¬R0 < qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 := not_lt_of_ge hle
      simpa [act, hnot] using hScaledNonneg ⟨⟨t, htu⟩, c⟩
    · have hQlt : R0 < qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 := lt_of_not_ge hle
      let qa : ℝ := qI t.a.1
      let qc : ℝ := qI c.1
      let qn : ℝ := qI t.n.1
      let Q : ℝ := qa * qc * qn ^ 3
      let x : ℝ := Q / Tscale
      have hqa : 0 < qa ∧ 1 ≤ qa := rf_qI_pos_ge_one t.a.1 t.a.2.1
      have hqc : 0 < qc ∧ 1 ≤ qc :=
        rf_qI_pos_ge_one c.1 (by simpa using c.2.1.1)
      have hqn : 0 < qn ∧ 1 ≤ qn := rf_qI_pos_ge_one t.n.1 t.n.2.1
      have hQpos : 0 < Q := by
        dsimp [Q]
        exact mul_pos (mul_pos hqa.1 hqc.1) (pow_pos hqn.1 3)
      have hQone : 1 ≤ Q := by
        have hqn3 : 1 ≤ qn ^ 3 := one_le_pow₀ hqn.2
        have hqac : 1 ≤ qa * qc := by
          calc
            1 = 1 * 1 := by ring
            _ ≤ qa * qc :=
              mul_le_mul hqa.2 hqc.2 (by norm_num) (le_trans (by norm_num) hqa.2)
        calc
          1 ≤ qa * qc := hqac
          _ ≤ qa * qc * qn ^ 3 := by
            have hmul := mul_le_mul_of_nonneg_left hqn3 (by positivity : 0 ≤ qa * qc)
            simpa using hmul
      have hxpos : 0 < x := by dsimp [x]; positivity
      have hxarg :
          Z * qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 /
              (qI d.1 ^ 2 * qI t.f.1 ^ 2) = x := by
        dsimp [x, Q, qa, qc, qn, Tscale]
        rw [htu.1]
        field_simp [ne_of_gt hZpos, ne_of_gt hqD, ne_of_gt hqF]
        <;> ring
      have hR0ltQ : Z ^ δ * L < Q := by
        simpa [R0, reflectionColumnCutoff, L, Q, qa, qc, qn] using hQlt
      have hZδT : Z ^ δ * Tscale < Q := by
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left hTL (Real.rpow_nonneg hZpos.le δ)) hR0ltQ
      have hxZ : Z ^ δ < x := by
        dsimp [x]
        exact (lt_div_iff₀ hTpos).2 hZδT
      have hInv : L⁻¹ ≤ Tscale⁻¹ := (inv_le_inv₀ hLpos hTpos).2 hTL
      have hDiv : Tscale⁻¹ ≤ Q / Tscale := by
        calc
          Tscale⁻¹ = 1 / Tscale := by rw [one_div]
          _ ≤ Q / Tscale := div_le_div_of_nonneg_right hQone hTpos.le
      have hxInv : L⁻¹ ≤ x := by dsimp [x]; exact hInv.trans hDiv
      have hJle : J ≤ x := max_le_iff.mpr ⟨hxZ.le, hxInv⟩
      have hJpos : 0 < J := lt_of_lt_of_le hZδpos (le_max_left _ _)
      have hgap : 0 ≤ N - σ := by linarith
      have hdecayPow : x ^ (-N) ≤ J ^ (-(N - σ)) * Tscale ^ σ * Q ^ (-σ) := by
        have hsplit : x ^ (-N) = x ^ (-(N - σ)) * x ^ (-σ) := by
          calc
            x ^ (-N) = x ^ (-(N - σ) + (-σ)) := by congr 1 <;> ring
            _ = x ^ (-(N - σ)) * x ^ (-σ) := Real.rpow_add hxpos _ _
        have hanti := Real.rpow_le_rpow_of_nonpos hJpos hJle (neg_nonpos.mpr hgap)
        have hInvX : x⁻¹ = Tscale / Q := by
          dsimp [x]
          field_simp [ne_of_gt hTpos, ne_of_gt hQpos]
          <;> ring
        have hneg : x ^ (-σ) = Tscale ^ σ * Q ^ (-σ) := by
          rw [Real.rpow_neg_eq_inv_rpow, hInvX, Real.div_rpow hTpos.le hQpos.le] <;>
            rw [Real.rpow_neg hQpos.le σ] <;> ring
        calc
          x ^ (-N) = x ^ (-(N - σ)) * x ^ (-σ) := hsplit
          _ ≤ J ^ (-(N - σ)) * x ^ (-σ) :=
            mul_le_mul_of_nonneg_right hanti (Real.rpow_nonneg hxpos.le _)
          _ = J ^ (-(N - σ)) * Tscale ^ σ * Q ^ (-σ) := by rw [hneg] <;> ring
      have hPhi :
          ‖profilePhi R υ (kappaSix R t sd sc) x‖ ≤
            Cprof * min (x ^ α) (x ^ (-N)) := by
        have h := hprof υ (kappaSix R t sd sc) x hxpos
        simpa [Theta.normDerivR, Real.exp_log hxpos] using h
      have hPhiTail :
          ‖profilePhi R υ (kappaSix R t sd sc) x‖ ≤
            Cprof * (J ^ (-(N - σ)) * Tscale ^ σ * Q ^ (-σ)) := by
        calc
          ‖profilePhi R υ (kappaSix R t sd sc) x‖ ≤
              Cprof * min (x ^ α) (x ^ (-N)) := hPhi
          _ ≤ Cprof * x ^ (-N) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hCprof.le
          _ ≤ Cprof * (J ^ (-(N - σ)) * Tscale ^ σ * Q ^ (-σ)) :=
            mul_le_mul_of_nonneg_left hdecayPow hCprof.le
      have hPhiTailAssoc :
          ‖profilePhi R υ (kappaSix R t sd sc) x‖ ≤
            Cprof * J ^ (-(N - σ)) * Tscale ^ σ * Q ^ (-σ) := by
        calc
          _ ≤ Cprof * (J ^ (-(N - σ)) * Tscale ^ σ * Q ^ (-σ)) := hPhiTail
          _ = Cprof * J ^ (-(N - σ)) * Tscale ^ σ * Q ^ (-σ) := by ring
      let coeff : ℝ := qc ^ (-(1 / 2 : ℝ)) / qn
      have hcoeffPos : 0 < coeff := by
        change 0 < qc ^ (-(1 / 2 : ℝ)) / qn
        exact div_pos (Real.rpow_pos_of_pos hqc.1 _) hqn.1
      have hcoeffNorm : ‖(coeff : ℂ)‖ = coeff := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcoeffPos]
      have hfac := (rf_exterior_factorization R).1 υ h t
      have hOmega : ‖frozenOmega R υ t‖ ≤ betaIdeal R f t.a := by
        simpa [htu.1] using hfac.1
      have hRho : ‖frozenRho R υ t sd d‖ ≤ 1 := hfac.2.1 sd d
      have hLambda : ‖frozenLambda R υ t sc c‖ ≤ 1 := hfac.2.2 sc c
      have hBeta : 0 ≤ betaIdeal R f t.a := le_trans (norm_nonneg _) hOmega
      have hchi : ‖chiIdealPow D d.1 (cgen R c) 3‖ ≤ 1 :=
        (a2_bridge_SYMBOL D S).ideal_norm_le d.1 (cgen R c) 3
      have hcoeffProduct :
          ‖frozenOmega R υ t * frozenRho R υ t sd d * frozenLambda R υ t sc c *
              (coeff : ℝ) * chiIdealPow D d.1 (cgen R c) 3‖ ≤
            betaIdeal R f t.a * coeff := by
        have hprod :
            ‖frozenOmega R υ t * frozenRho R υ t sd d * frozenLambda R υ t sc c *
                (coeff : ℝ) * chiIdealPow D d.1 (cgen R c) 3‖ =
              ‖frozenOmega R υ t‖ * ‖frozenRho R υ t sd d‖ *
                ‖frozenLambda R υ t sc c‖ * coeff *
                  ‖chiIdealPow D d.1 (cgen R c) 3‖ := by
          simp only [norm_mul, hcoeffNorm]
        rw [hprod]
        calc
          ‖frozenOmega R υ t‖ * ‖frozenRho R υ t sd d‖ *
              ‖frozenLambda R υ t sc c‖ * coeff * ‖chiIdealPow D d.1 (cgen R c) 3‖ ≤
            betaIdeal R f t.a * 1 * 1 * coeff * 1 := by
              gcongr
          _ = betaIdeal R f t.a * coeff := by ring
      have htermExpr :
          reflectedTerm R υ h d Z (t, sd, sc, c) =
            (frozenOmega R υ t * frozenRho R υ t sd d * frozenLambda R υ t sc c *
              (coeff : ℝ) * chiIdealPow D d.1 (cgen R c) 3) *
                profilePhi R υ (kappaSix R t sd sc) x := by
        simp [reflectedTerm, coeff, qc, qn, hxarg]
      have hdirEval :
          reflectedDirichletTerm R f σ (ψ ((⟨t, htu⟩, c))) =
            betaIdeal R f t.a * coeff * Q ^ (-σ) := by
        change betaIdeal R f t.a * qI c.1 ^ (-(1 / 2 : ℝ)) / qI t.n.1 *
            (qI t.a.1 * qI c.1 * qI t.n.1 ^ 3) ^ (-σ) =
          betaIdeal R f t.a * coeff * Q ^ (-σ)
        dsimp [coeff, Q, qa, qc, qn] <;> ring
      have hTfac : Cprof * J ^ (-(N - σ)) * Tscale ^ σ ≤
          Cprof * L ^ σ * J ^ (-(N - σ)) := by
        calc
          Cprof * J ^ (-(N - σ)) * Tscale ^ σ ≤
              Cprof * J ^ (-(N - σ)) * L ^ σ :=
            mul_le_mul_of_nonneg_left hTpow (by positivity)
          _ = Cprof * L ^ σ * J ^ (-(N - σ)) := by ring
      have hterm :
          ‖reflectedTerm R υ h d Z (t, sd, sc, c)‖ ≤
            Cfac * reflectedDirichletTerm R f σ (ψ ((⟨t, htu⟩, c))) := by
        calc
          ‖reflectedTerm R υ h d Z (t, sd, sc, c)‖ =
              ‖frozenOmega R υ t * frozenRho R υ t sd d * frozenLambda R υ t sc c *
                (coeff : ℝ) * chiIdealPow D d.1 (cgen R c) 3‖ *
                  ‖profilePhi R υ (kappaSix R t sd sc) x‖ := by
            rw [htermExpr, norm_mul]
          _ ≤ betaIdeal R f t.a * coeff *
                (Cprof * J ^ (-(N - σ)) * Tscale ^ σ * Q ^ (-σ)) :=
              mul_le_mul hcoeffProduct hPhiTailAssoc (norm_nonneg _)
                (mul_nonneg hBeta hcoeffPos.le)
          _ ≤ Cprof * L ^ σ * J ^ (-(N - σ)) *
                (betaIdeal R f t.a * coeff * Q ^ (-σ)) := by
              calc
                betaIdeal R f t.a * coeff *
                    (Cprof * J ^ (-(N - σ)) * Tscale ^ σ * Q ^ (-σ)) =
                  (betaIdeal R f t.a * coeff * Q ^ (-σ)) *
                    (Cprof * J ^ (-(N - σ)) * Tscale ^ σ) := by ring
                _ ≤ (betaIdeal R f t.a * coeff * Q ^ (-σ)) *
                    (Cprof * L ^ σ * J ^ (-(N - σ))) := by
                  exact mul_le_mul_of_nonneg_left hTfac (by positivity)
                _ = Cprof * L ^ σ * J ^ (-(N - σ)) *
                    (betaIdeal R f t.a * coeff * Q ^ (-σ)) := by ring
          _ = Cfac * (betaIdeal R f t.a * coeff * Q ^ (-σ)) := by
              dsimp [Cfac] <;> ring
          _ = Cfac * reflectedDirichletTerm R f σ (ψ ((⟨t, htu⟩, c))) := by
              rw [hdirEval] <;> rfl
      simpa [act, hQlt, ψ] using hterm
  have hpointNorm : ∀ p : Src,
      ‖act p‖ ≤ ‖(Cfac * reflectedDirichletTerm R f σ (ψ p) : ℝ)‖ := by
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (hScaledNonneg p)]
    exact hpoint p
  have hActSummable : Summable act :=
    Summable.of_norm_bounded hScaledNorm hpointNorm
  have hActNorm : Summable (fun p : Src => ‖act p‖) := hActSummable.norm
  have hsumPoint :
      (∑' p : Src, ‖act p‖) ≤
        ∑' p : Src, Cfac * reflectedDirichletTerm R f σ (ψ p) :=
    hActNorm.tsum_le_tsum hpoint hScaledSum
  have hsumScaled :
      (∑' p : Src, Cfac * reflectedDirichletTerm R f σ (ψ p)) =
        Cfac * ∑' p : Src, reflectedDirichletTerm R f σ (ψ p) := by
    rw [tsum_mul_left]
  have hsumDir :
      Cfac * ∑' p : Src, reflectedDirichletTerm R f σ (ψ p) ≤
        Cfac * (sphericalMajorant (S := S) σ * Eideal R f σ) :=
    mul_le_mul_of_nonneg_left hMappedBound (le_of_lt hCfac)
  have hsumAct :
      (∑' p : Src, ‖act p‖) ≤
        Cprof * L ^ σ * J ^ (-(N - σ)) * sphericalMajorant (S := S) σ * Eideal R f σ := by
    calc
      (∑' p : Src, ‖act p‖) ≤ ∑' p : Src, Cfac * reflectedDirichletTerm R f σ (ψ p) := hsumPoint
      _ = Cfac * ∑' p : Src, reflectedDirichletTerm R f σ (ψ p) := hsumScaled
      _ ≤ Cfac * (sphericalMajorant (S := S) σ * Eideal R f σ) := hsumDir
      _ = Cprof * L ^ σ * J ^ (-(N - σ)) * sphericalMajorant (S := S) σ * Eideal R f σ := by
        simp [Cfac, mul_assoc]
  refine ⟨?_, ?_⟩
  · simpa [act, not_le] using hActNorm
  · simpa [act, not_le] using hsumAct

/-- rf:tail-mass: pointwise active/slice bound, before summing squares over powerful parts. -/
theorem rf_tail_bound : ∀ δ σ N : ℝ, 0 < δ → 1 / 2 < σ → σ < N →
  ∃ C : ℝ, 0 < C ∧ ∀ υ P D0 Z h d f u sd sc,
    1 ≤ P → 1 ≤ D0 → 2 ≤ Z → P ≤ qI h.1 → qI h.1 < 2 * P →
    D0 ≤ qI d.1 → qI d.1 < 2 * D0 → IsPowerful h.1 → activeFactor R h f →
    ‖activePartial R false υ h d f u sd sc Z (reflectionColumnCutoff P D0 Z δ)‖ ≤
      C * reflectionColumnLength P D0 Z ^ σ *
        max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-(N - σ)) *
          sphericalMajorant (S := S) σ * Eideal R f σ := by
  intro δ σ N hδ hσ hN
  obtain ⟨C, hC, hbound⟩ := rf_tail_bound_abs R δ σ N hδ hσ hN
  refine ⟨C, hC, ?_⟩
  intro υ P D0 Z h d f u sd sc hP hD0 hZ hPh hPhigh hDd hDhigh hPower hActive
  obtain ⟨hSummable, hNormBound⟩ :=
    hbound υ P D0 Z h d f u sd sc hP hD0 hZ hPh hPhigh hDd hDhigh hPower hActive
  let Src := {t : FrozenIndex R h // t.f = f ∧ t.u = u} × S.SqfExtIdeal
  have hpartial :
      activePartial R false υ h d f u sd sc Z (reflectionColumnCutoff P D0 Z δ) =
        ∑' p : Src, if (qI p.1.1.a.1 * qI p.2.1 * qI p.1.1.n.1 ^ 3 ≤
            reflectionColumnCutoff P D0 Z δ) = false then
          reflectedTerm R υ h d Z (p.1.1, sd, sc, p.2) else 0 := by
    rfl
  rw [hpartial]
  exact (norm_tsum_le_tsum_norm hSummable).trans hNormBound

set_option maxHeartbeats 8000000 in
private lemma rf_squarefree_support_finite (h : S.ExtIdeal) (hh : IsPowerful h.1) :
    Finite {f : S.ExtIdeal // Squarefree f.1 ∧
      ∀ v ∈ R.exterior.support f, v ∈ R.exterior.support h} := by
  classical
  let h6 : S.ExtIdeal := R.exterior.pow h 6
  have h6power : IsPowerful h6.1 := by
    intro v hv
    have hvh : v.asIdeal ∣ h.1 := by
      have hv' : v.asIdeal ∣ h.1 ^ 6 := by
        simpa [h6, R.exterior.pow_val] using hv
      exact v.prime.dvd_of_dvd_pow hv'
    have hp2 : v.asIdeal ^ 2 ∣ h.1 := hh v hvh
    have hh6 : h.1 ∣ h6.1 := by
      dsimp [h6]
      rw [R.exterior.pow_val]
      exact dvd_pow_self h.1 (by norm_num : (6 : ℕ) ≠ 0)
    exact dvd_trans hp2 hh6
  have hexp (v : FinPlace F) : idealExp v h6.1 = 6 * idealExp v h.1 := by
    dsimp [idealExp, h6]
    rw [R.exterior.pow_val]
    exact Associates.count_pow (Associates.mk_ne_zero.mpr h.2.1)
      v.associates_irreducible 6
  have hactive (f : {f : S.ExtIdeal // Squarefree f.1 ∧
      ∀ v ∈ R.exterior.support f, v ∈ R.exterior.support h}) : activeFactor R h6 f.1 := by
    refine ⟨f.2.1, ?_, ?_⟩
    · intro v hv
      apply (R.exterior.mem_support h6 v).2
      rw [R.exterior.pow_val]
      exact dvd_trans ((R.exterior.mem_support h v).1 (f.2.2 v hv))
        (dvd_pow_self h.1 (by norm_num : (6 : ℕ) ≠ 0))
    · intro v hv hn
      have hzero : idealExp v h6.1 % 6 = 0 := by rw [hexp]; simp
      exact (hn hzero).elim
  have hqfsq (f : {f : S.ExtIdeal // Squarefree f.1 ∧
      ∀ v ∈ R.exterior.support f, v ∈ R.exterior.support h}) :
      qI f.1.1 ^ 2 ≤ qI h6.1 :=
    (rf_active_support_bounds R).1 h6 f.1 h6power (hactive f)
  have hqh6 : qI h6.1 = qI h.1 ^ 6 := by
    simp [h6, qI, R.exterior.pow_val]
  have hnormBound (f : {f : S.ExtIdeal // Squarefree f.1 ∧
      ∀ v ∈ R.exterior.support f, v ∈ R.exterior.support h}) :
      qI f.1.1 ≤ qI h.1 ^ 3 := by
    have hqf : 0 ≤ qI f.1.1 := by
      change 0 ≤ (Ideal.absNorm f.1.1 : ℝ)
      exact Nat.cast_nonneg _
    have hqh : 0 ≤ qI h.1 := by
      change 0 ≤ (Ideal.absNorm h.1 : ℝ)
      exact Nat.cast_nonneg _
    have hsquare : qI f.1.1 ^ 2 ≤ qI h.1 ^ 6 := by
      rw [← hqh6]
      exact hqfsq f
    calc
      qI f.1.1 = Real.sqrt (qI f.1.1 ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hqf]
      _ ≤ Real.sqrt (qI h.1 ^ 6) := Real.sqrt_le_sqrt hsquare
      _ = qI h.1 ^ 3 := by
        rw [show qI h.1 ^ 6 = (qI h.1 ^ 3) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  let X : ℝ := qI h.1 ^ 3
  have hX : 0 ≤ X := by
    dsimp [X]
    exact pow_nonneg (le_of_lt (rf_qI_pos_ge_one h.1 h.2.1).1) 3
  have hnormFinite : {f : S.ExtIdeal | qI f.1 ≤ X}.Finite := by
    have hfinite := (a2_bridge_COUNT_finite S X hX).1
    simpa [X, qI, idealNorm] using hfinite
  letI : Fintype {f : S.ExtIdeal // qI f.1 ≤ X} := hnormFinite.fintype
  apply Finite.of_injective (fun f => (⟨f.1, by simpa [X] using hnormBound f⟩ :
      {f : S.ExtIdeal // qI f.1 ≤ X}))
  intro f g hfg
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  have hfg' : f = g := congrArg
    (fun z : {f : S.ExtIdeal // qI f.1 ≤ X} => z.1) hfg
  subst g
  rfl

private lemma rf_Eideal_nonneg (f : S.ExtIdeal) {σ : ℝ} (hσ : 0 ≤ σ) :
    0 ≤ Eideal R f σ := by
  unfold Eideal
  apply Finset.prod_nonneg
  intro v hv
  have hvS : v ∉ S.Sf := R.exterior.support_exterior f v hv
  obtain ⟨hsum, _, _⟩ := (rf_active_support_bounds R).2.2.1 v hvS σ hσ
  have hq : 1 < qI v.asIdeal := qI_prime_gt_one v
  have hqpos : 0 < qI v.asIdeal := lt_trans (by norm_num) hq
  apply tsum_nonneg
  intro e
  have hbeta : 0 ≤ betaPrime (qI v.asIdeal) (qI_prime_gt_one v) e := by
    unfold betaPrime
    by_cases h0 : e = 0
    · rw [if_pos h0]
      norm_num
    · by_cases h1 : e % 3 = 1
      · rw [if_neg h0, if_pos h1]
        exact Real.rpow_nonneg hqpos.le _
      · by_cases h2 : e % 3 = 0
        · rw [if_neg h0, if_neg h1, if_pos h2]
          exact Real.rpow_nonneg hqpos.le _
        · rw [if_neg h0, if_neg h1, if_neg h2]
  exact mul_nonneg hbeta (Real.rpow_nonneg hqpos.le _)

private lemma rf_sphericalMajorant_nonneg (σ : ℝ) :
    0 ≤ sphericalMajorant (S := S) σ := by
  unfold sphericalMajorant
  apply tsum_nonneg
  intro p
  have hq1 : 0 ≤ qI p.1.1 := by
    change 0 ≤ (Ideal.absNorm p.1.1 : ℝ)
    exact Nat.cast_nonneg _
  have hq2 : 0 ≤ qI p.2.1 := by
    change 0 ≤ (Ideal.absNorm p.2.1 : ℝ)
    exact Nat.cast_nonneg _
  exact mul_nonneg (Real.rpow_nonneg hq1 _) (Real.rpow_nonneg hq2 _)

set_option maxHeartbeats 4000000 in
private lemma rf_tail_split_bound : ∀ δ δ₁ σ N : ℝ, 0 < δ → 0 < δ₁ →
  1 / 2 < σ → σ < N → ∃ C : ℝ, 0 < C ∧ ∀ υ P D0 Z h d,
    1 ≤ P → 1 ≤ D0 → 2 ≤ Z → P ≤ qI h.1 → qI h.1 < 2 * P →
    D0 ≤ qI d.1 → qI d.1 < 2 * D0 → IsPowerful h.1 →
    ‖splitReflection R false υ h d Z (reflectionColumnCutoff P D0 Z δ)‖ ≤
      C * P ^ δ₁ * reflectionColumnLength P D0 Z ^ σ *
        max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-(N - σ)) := by
  intro δ δ₁ σ N hδ hδ₁ hσ hN
  obtain ⟨Ctail, hCtail, hTail⟩ := rf_tail_bound_abs R δ σ N hδ hσ hN
  obtain ⟨Cact, hCact, hActBound⟩ := (rf_active_support_bounds R).2.2.2 δ₁ hδ₁
  classical
  letI : Fintype (UnitSix S) := R.sheets.unitSixFinite
  letI : Fintype S.V := R.sheets.classFinite
  letI : Fintype Bd.B := inferInstance
  let Slice : Type := UnitSix S × Bd.B × Bd.B
  let Cslice : ℝ := Fintype.card Slice
  refine ⟨max 1 (Ctail * Cact * Cslice * 2 ^ δ₁ *
    sphericalMajorant (S := S) σ), ?_, ?_⟩
  · positivity
  · intro υ P D0 Z h d hP hD0 hZ hPh hPhigh hDd hDhigh hPower
    let R0 := reflectionColumnCutoff P D0 Z δ
    let L := reflectionColumnLength P D0 Z
    let J := max (Z ^ δ) L⁻¹
    have hPpos : 0 < P := by linarith
    have hDpos : 0 < D0 := by linarith
    have hZpos : 0 < Z := by linarith
    have hqHpos : 0 < qI h.1 := (rf_qI_pos_ge_one h.1 h.2.1).1
    have hLpos : 0 < L := by dsimp [L, reflectionColumnLength]; positivity
    have hJpos : 0 < J := by
      apply lt_of_lt_of_le (Real.rpow_pos_of_pos hZpos δ)
      exact le_max_left _ _
    have hJpow : 0 < J ^ (-(N - σ)) := Real.rpow_pos_of_pos hJpos _
    have hMaj : 0 ≤ sphericalMajorant (S := S) σ := rf_sphericalMajorant_nonneg σ
    let F0 : Type := {f : S.ExtIdeal // Squarefree f.1 ∧
      ∀ v ∈ R.exterior.support f, v ∈ R.exterior.support h}
    letI : Finite F0 := rf_squarefree_support_finite R h hPower
    letI : Fintype F0 := Fintype.ofFinite F0
    let Active : Type := {f : F0 // activeFactor R h f.1}
    letI : Fintype Active := Subtype.fintype (fun f : F0 => activeFactor R h f.1)
    let Base : Type := Active × Slice
    let Fiber (b : Base) : Type :=
      {t : FrozenIndex R h // t.f = b.1.1.1 ∧ t.u = b.2.1} × S.SqfExtIdeal
    let Source : Type := FrozenIndex R h × Bd.B × Bd.B × S.SqfExtIdeal
    let mkActive (t : FrozenIndex R h) : Active :=
      ⟨⟨t.f, ⟨t.active.1, t.active.2.1⟩⟩, t.active⟩
    let baseOf (p : Source) : Base :=
      (mkActive p.1, p.1.u, p.2.1, p.2.2.1)
    let tailTerm (p : Source) : ℂ :=
      if (qI p.1.a.1 * qI p.2.2.2.1 * qI p.1.n.1 ^ 3 ≤ R0) = false then
        reflectedTerm R υ h d Z (p.1, p.2.1, p.2.2.1, p.2.2.2) else 0
    let blockTerm (b : Base) (x : Fiber b) : ℂ :=
      if (qI x.1.1.a.1 * qI x.2.1 * qI x.1.1.n.1 ^ 3 ≤ R0) = false then
        reflectedTerm R υ h d Z (x.1.1, b.2.2.1, b.2.2.2, x.2) else 0
    let e : Source ≃ Σ b : Base, Fiber b :=
      { toFun := fun p => ⟨baseOf p,
          (⟨p.1, ⟨rfl, rfl⟩⟩, p.2.2.2)⟩
        invFun := fun z =>
          (z.2.1.1, (z.1.2.2.1, (z.1.2.2.2, z.2.2)))
        left_inv := by
          intro p
          rcases p with ⟨t, sd, sc, c⟩
          rfl
        right_inv := by
          intro z
          rcases z with ⟨b, x⟩
          rcases b with ⟨a, u, sd, sc⟩
          rcases a with ⟨f0, ha⟩
          rcases f0 with ⟨f, hf⟩
          rcases x with ⟨⟨t, htf, htu⟩, c⟩
          have hf0 : (⟨t.f, ⟨t.active.1, t.active.2.1⟩⟩ : F0) = ⟨f, hf⟩ := by
            apply Subtype.ext
            exact htf
          have ha' : mkActive t = ⟨⟨f, hf⟩, ha⟩ := by
            apply Subtype.ext
            exact hf0
          have hb : (mkActive t, t.u, sd, sc) = (⟨⟨f, hf⟩, ha⟩, u, sd, sc) := by
            apply Prod.ext ha'
            apply Prod.ext htu
            rfl
          cases hb
          rfl
      }
    have hterm : ∀ z : (Σ b : Base, Fiber b),
        tailTerm (e.symm z) = blockTerm z.1 z.2 := by
      intro z
      rcases z with ⟨b, x⟩
      rcases b with ⟨a, u, sd, sc⟩
      rcases x with ⟨⟨t, ht⟩, c⟩
      simp [tailTerm, blockTerm, e]
    have hσ0 : 0 ≤ σ := by linarith
    have hAllActive : (∑ f : F0, Eideal R f.1 σ) ≤ Cact * qI h.1 ^ δ₁ := by
      have h := hActBound h σ hσ0
      simpa [F0, finsum_eq_sum_of_fintype] using h
    have hActiveSum : (∑ f : Active, Eideal R f.1.1 σ) ≤ Cact * qI h.1 ^ δ₁ := by
      have hsplit := Fintype.sum_subtype_add_sum_subtype
        (fun f : F0 => activeFactor R h f.1) (fun f : F0 => Eideal R f.1 σ)
      have hdecomp :
          (∑ f : Active, Eideal R f.1.1 σ) +
            ∑ f : {f : F0 // ¬ activeFactor R h f.1}, Eideal R f.1.1 σ =
              ∑ f : F0, Eideal R f.1 σ := by
        simpa [Active] using hsplit
      have hcompl : 0 ≤
          ∑ f : {f : F0 // ¬ activeFactor R h f.1}, Eideal R f.1.1 σ := by
        apply Finset.sum_nonneg
        intro f hf
        exact rf_Eideal_nonneg R f.1.1 hσ0
      linarith
    have hFiberNorm (b : Base) : Summable (fun x : Fiber b => ‖blockTerm b x‖) := by
      obtain ⟨hs, _⟩ := hTail υ P D0 Z h d b.1.1.1 b.2.1 b.2.2.1 b.2.2.2
        hP hD0 hZ hPh hPhigh hDd hDhigh hPower b.1.2
      simpa [Fiber, blockTerm, R0] using hs
    have hOuterNorm : Summable (fun b : Base => ∑' x : Fiber b, ‖blockTerm b x‖) := by
      exact Summable.of_finite
    have hSigmaNorm : Summable (fun z : (Σ b : Base, Fiber b) =>
        ‖blockTerm z.1 z.2‖) := by
      apply (summable_sigma_of_nonneg (fun z => norm_nonneg _)).2
      exact ⟨hFiberNorm, by simpa using hOuterNorm⟩
    have hSourceNorm : Summable (fun p : Source => ‖tailTerm p‖) := by
      have hs := hSigmaNorm.comp_injective e.injective
      apply hs.congr
      intro p
      exact congrArg (fun z : ℂ => ‖z‖) (hterm (e p)).symm
    have hNormTsum :
        (∑' p : Source, ‖tailTerm p‖) =
          ∑ b : Base, ∑' x : Fiber b, ‖blockTerm b x‖ := by
      calc
        _ = ∑' p : Source, ‖tailTerm (e.symm (e p))‖ := by
          apply tsum_congr
          intro p
          simp
        _ = ∑' z : (Σ b : Base, Fiber b), ‖tailTerm (e.symm z)‖ :=
          Equiv.tsum_eq e (fun z : (Σ b : Base, Fiber b) =>
            ‖tailTerm (e.symm z)‖)
        _ = ∑' z : (Σ b : Base, Fiber b), ‖blockTerm z.1 z.2‖ := by
          apply tsum_congr
          intro z
          rw [hterm z]
        _ = ∑' b : Base, ∑' x : Fiber b, ‖blockTerm b x‖ :=
          Summable.tsum_sigma' hFiberNorm hSigmaNorm
        _ = ∑ b : Base, ∑' x : Fiber b, ‖blockTerm b x‖ := by rw [tsum_fintype]
    have hFiberBound (b : Base) :
        (∑' x : Fiber b, ‖blockTerm b x‖) ≤
          Ctail * L ^ σ * J ^ (-(N - σ)) * sphericalMajorant (S := S) σ *
            Eideal R b.1.1.1 σ := by
      obtain ⟨_, hb⟩ := hTail υ P D0 Z h d b.1.1.1 b.2.1 b.2.2.1 b.2.2.2
        hP hD0 hZ hPh hPhigh hDd hDhigh hPower b.1.2
      simpa [Fiber, blockTerm, R0, L, J, mul_assoc] using hb
    have hsumFibers :
        (∑ b : Base, ∑' x : Fiber b, ‖blockTerm b x‖) ≤
          ∑ b : Base,
            Ctail * L ^ σ * J ^ (-(N - σ)) * sphericalMajorant (S := S) σ *
              Eideal R b.1.1.1 σ := by
      apply Finset.sum_le_sum
      intro b hb
      exact hFiberBound b
    let K : ℝ := Ctail * L ^ σ * J ^ (-(N - σ)) * sphericalMajorant (S := S) σ
    have hfactor :
        (∑ b : Base, K * Eideal R b.1.1.1 σ) =
          Cslice * K * (∑ f : Active, Eideal R f.1.1 σ) := by
      dsimp [Base]
      rw [Fintype.sum_prod_type]
      calc
        _ = ∑ f : Active, ∑ s : Slice, K * Eideal R f.1.1 σ := rfl
        _ = ∑ f : Active, Cslice * (K * Eideal R f.1.1 σ) := by
          apply Finset.sum_congr rfl
          intro f hf
          simp [Cslice, Finset.sum_const, nsmul_eq_mul]
        _ = Cslice * K * (∑ f : Active, Eideal R f.1.1 σ) := by
          calc
            _ = ∑ f : Active, (Cslice * K) * Eideal R f.1.1 σ := by
              apply Finset.sum_congr rfl
              intro f hf
              ring
            _ = (Cslice * K) * (∑ f : Active, Eideal R f.1.1 σ) := by
              rw [Finset.mul_sum]
            _ = _ := by ring
    have hKnonneg : 0 ≤ K := by dsimp [K]; positivity
    have hCslice : 0 ≤ Cslice := by positivity
    have hsumUpper :
        (∑ b : Base, ∑' x : Fiber b, ‖blockTerm b x‖) ≤
          Cslice * K * (Cact * qI h.1 ^ δ₁) := by
      calc
        _ ≤ ∑ b : Base, K * Eideal R b.1.1.1 σ := by
          apply Finset.sum_le_sum
          intro b hb
          simpa [K, mul_assoc] using hFiberBound b
        _ = Cslice * K * (∑ f : Active, Eideal R f.1.1 σ) := hfactor
        _ ≤ Cslice * K * (Cact * qI h.1 ^ δ₁) :=
          mul_le_mul_of_nonneg_left hActiveSum (mul_nonneg hCslice hKnonneg)
    have hqhpow : qI h.1 ^ δ₁ ≤ (2 * P) ^ δ₁ :=
      Real.rpow_le_rpow (by positivity) hPhigh.le hδ₁.le
    have hmulPow : (2 * P) ^ δ₁ = 2 ^ δ₁ * P ^ δ₁ := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
    have hcoef : Ctail * Cact * Cslice * 2 ^ δ₁ *
        sphericalMajorant (S := S) σ ≤
          max 1 (Ctail * Cact * Cslice * 2 ^ δ₁ *
            sphericalMajorant (S := S) σ) := le_max_right _ _
    have hboundNorm : ‖splitReflection R false υ h d Z R0‖ ≤
        max 1 (Ctail * Cact * Cslice * 2 ^ δ₁ *
          sphericalMajorant (S := S) σ) * P ^ δ₁ * L ^ σ * J ^ (-(N - σ)) := by
      by_cases hdc : Squarefree d.1 ∧ IsCoprime d.1 h.1
      · have hsplitEq : splitReflection R false υ h d Z R0 = ∑' p : Source, tailTerm p := by
          unfold splitReflection
          simp only [hdc, ↓reduceIte]
          apply tsum_congr
          intro p
          rfl
        rw [hsplitEq]
        calc
          ‖∑' p : Source, tailTerm p‖ ≤ ∑' p : Source, ‖tailTerm p‖ :=
            norm_tsum_le_tsum_norm hSourceNorm
          _ = ∑ b : Base, ∑' x : Fiber b, ‖blockTerm b x‖ := hNormTsum
          _ ≤ Cslice * K * (Cact * qI h.1 ^ δ₁) := hsumUpper
          _ ≤ Cslice * K * (Cact * ((2 * P) ^ δ₁)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hqhpow hCact.le)
              (mul_nonneg hCslice hKnonneg)
          _ = (Ctail * Cact * Cslice * 2 ^ δ₁ *
              sphericalMajorant (S := S) σ) * P ^ δ₁ * L ^ σ *
                J ^ (-(N - σ)) := by rw [hmulPow]; dsimp [K]; ring
          _ ≤ max 1 (Ctail * Cact * Cslice * 2 ^ δ₁ *
              sphericalMajorant (S := S) σ) * P ^ δ₁ * L ^ σ *
                J ^ (-(N - σ)) := by
            calc
              _ = (Ctail * Cact * Cslice * 2 ^ δ₁ *
                    sphericalMajorant (S := S) σ) *
                    (P ^ δ₁ * L ^ σ * J ^ (-(N - σ))) := by ring
              _ ≤ max 1 (Ctail * Cact * Cslice * 2 ^ δ₁ *
                    sphericalMajorant (S := S) σ) *
                    (P ^ δ₁ * L ^ σ * J ^ (-(N - σ))) :=
                mul_le_mul_of_nonneg_right hcoef (by positivity)
              _ = _ := by ring
      · simp [splitReflection, hdc]
        positivity
    change ‖splitReflection R false υ h d Z R0‖ ≤
      max 1 (Ctail * Cact * Cslice * 2 ^ δ₁ * sphericalMajorant (S := S) σ) *
        P ^ δ₁ * L ^ σ * J ^ (-(N - σ))
    exact hboundNorm

set_option maxHeartbeats 8000000 in
/-- rf:tail-mass, 04:1046–1117, uniformly including R₀<1. -/
theorem rf_tail_mass : ∀ δ δ₁ σ N : ℝ, 0 < δ → 0 < δ₁ → 1 / 2 < σ → σ < N →
  ∃ C : ℝ, 0 < C ∧ ∀ υ P D0 Z, 1 ≤ P → 1 ≤ D0 → 2 ≤ Z →
    reflectionMass R false υ P D0 Z δ ≤ C * P ^ (1 / 2 + 2 * δ₁) * D0 *
      reflectionColumnLength P D0 Z ^ (2 * σ) *
        max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-2 * (N - σ)) := by
  intro δ δ₁ σ N hδ hδ₁ hσ hN
  obtain ⟨Csplit, hCsplit, hsplit⟩ :=
    rf_tail_split_bound R δ δ₁ σ N hδ hδ₁ hσ hN
  obtain ⟨Cpow, hCpow, hpow⟩ := rf_powerful_count S
  obtain ⟨Ccnt, hCcnt, hcount⟩ := a2_bridge_COUNT S
  refine ⟨4 * Cpow * Ccnt * Csplit ^ 2, ?_, ?_⟩
  · positivity
  · intro υ P D0 Z hP hD0 hZ
    have hPpos : 0 < P := by linarith
    have hDpos : 0 < D0 := by linarith
    have hZpos : 0 < Z := by linarith
    let Hset : Finset S.ExtIdeal :=
      (bridgeNormFinset S (2 * P)).filter (fun h => IsPowerful h.1)
    let Dset : Finset S.ExtIdeal := bridgeNormFinset S (2 * D0)
    let Kset : Finset (S.ExtIdeal × S.ExtIdeal) := Hset.product Dset
    let massTerm (hd : S.ExtIdeal × S.ExtIdeal) : ℝ :=
      if IsPowerful hd.1.1 ∧ P ≤ qI hd.1.1 ∧ qI hd.1.1 < 2 * P ∧
          D0 ≤ qI hd.2.1 ∧ qI hd.2.1 < 2 * D0 then
        ‖splitReflection R false υ hd.1 hd.2 Z (reflectionColumnCutoff P D0 Z δ)‖ ^ 2
      else 0
    have hFinP := a2_bridge_COUNT_finite S (2 * P) (by positivity)
    have hFinD := a2_bridge_COUNT_finite S (2 * D0) (by positivity)
    have hHnorm (h : S.ExtIdeal) (hh : h ∈ Hset) : idealNorm h.1 ≤ 2 * P := by
      exact (hFinP.2 h).mp (Finset.mem_filter.mp hh).1
    have hmemH (h : S.ExtIdeal) (hh : IsPowerful h.1) (hhi : qI h.1 < 2 * P) :
        h ∈ Hset := by
      apply Finset.mem_filter.mpr
      constructor
      · exact (hFinP.2 h).mpr (by simpa [idealNorm, qI] using hhi.le)
      · exact hh
    have hmemD (d : S.ExtIdeal) (dhi : qI d.1 < 2 * D0) : d ∈ Dset := by
      exact (hFinD.2 d).mpr (by simpa [idealNorm, qI] using dhi.le)
    have hImgSub : Hset.image (fun h : S.ExtIdeal => h.1) ⊆
        powerfulExteriorIdeals S P := by
      intro I hI
      rcases Finset.mem_image.mp hI with ⟨h, hh, rfl⟩
      have hnorm : idealNorm h.1 ≤ 2 * P := hHnorm h hh
      have hpow' := (Finset.mem_filter.mp hh).2
      change h.1 ∈ powerfulExteriorIdeals S P
      unfold powerfulExteriorIdeals
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      constructor
      · apply (Nat.le_floor_iff (by positivity : 0 ≤ 2 * P)).mpr
        simpa [idealNorm] using hnorm
      · exact ⟨h.2, hpow'⟩
    have hImgCard : (Hset.image (fun h : S.ExtIdeal => h.1)).card = Hset.card := by
      apply Finset.card_image_iff.mpr
      intro h hh d hd heq
      exact Subtype.ext heq
    have hHcard : (Hset.card : ℝ) ≤ Cpow * P ^ (1 / 2 : ℝ) := by
      calc
        (Hset.card : ℝ) = ((Hset.image (fun h : S.ExtIdeal => h.1)).card : ℝ) := by
          rw [hImgCard]
        _ ≤ ((powerfulExteriorIdeals S P).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hImgSub
        _ ≤ Cpow * P ^ (1 / 2 : ℝ) := by
          exact_mod_cast hpow P hP
    have hDfinsetEq : hFinD.1.toFinset = Dset := by
      ext d
      rw [Set.Finite.mem_toFinset]
      exact (hFinD.2 d).symm
    have hDcardNat : {d : S.ExtIdeal | idealNorm d.1 ≤ 2 * D0}.ncard = Dset.card := by
      rw [Set.ncard_eq_toFinset_card _ hFinD.1, hDfinsetEq]
    have hDcard : (Dset.card : ℝ) ≤ Ccnt * (2 * D0) := by
      have hc := hcount (2 * D0) (by linarith)
      rw [hDcardNat] at hc
      exact hc
    have hzero : ∀ hd : S.ExtIdeal × S.ExtIdeal, hd ∉ Kset → massTerm hd = 0 := by
      rintro ⟨h, d⟩ hnot
      by_cases hc : IsPowerful h.1 ∧ P ≤ qI h.1 ∧ qI h.1 < 2 * P ∧
          D0 ≤ qI d.1 ∧ qI d.1 < 2 * D0
      · rcases hc with ⟨hh, _, hhi, _, dhi⟩
        have hhm := hmemH h hh hhi
        have hdm := hmemD d dhi
        have hmem : (h, d) ∈ Kset := by simp [Kset, hhm, hdm]
        exact (hnot hmem).elim
      · simp [massTerm, hc]
    have hmassEq : reflectionMass R false υ P D0 Z δ =
        ∑ hd ∈ Kset, massTerm hd := by
      calc
        reflectionMass R false υ P D0 Z δ = ∑' hd : S.ExtIdeal × S.ExtIdeal, massTerm hd := by
          unfold reflectionMass
          rfl
        _ = ∑ hd ∈ Kset, massTerm hd := tsum_eq_sum hzero
    let L := reflectionColumnLength P D0 Z
    let J := max (Z ^ δ) L⁻¹
    let Ksplit := Csplit * P ^ δ₁ * L ^ σ * J ^ (-(N - σ))
    let Bmass := Ksplit ^ 2
    have hLpos : 0 < L := by dsimp [L, reflectionColumnLength]; positivity
    have hJpos : 0 < J := by
      apply lt_of_lt_of_le (Real.rpow_pos_of_pos hZpos δ)
      exact le_max_left _ _
    have hKsplit : 0 ≤ Ksplit := by dsimp [Ksplit]; positivity
    have hBmass : 0 ≤ Bmass := sq_nonneg _
    have hpoint : ∀ hd ∈ Kset, massTerm hd ≤ Bmass := by
      intro hd hhd
      rcases hd with ⟨h, d⟩
      by_cases hc : IsPowerful h.1 ∧ P ≤ qI h.1 ∧ qI h.1 < 2 * P ∧
          D0 ≤ qI d.1 ∧ qI d.1 < 2 * D0
      · have hcond := hc
        rcases hc with ⟨hh, hPl, hPh, hDl, hDh⟩
        have hsplit' := hsplit υ P D0 Z h d hP hD0 hZ hPl hPh hDl hDh hh
        have hmul :
            0 ≤ (Ksplit - ‖splitReflection R false υ h d Z
              (reflectionColumnCutoff P D0 Z δ)‖) *
              (Ksplit + ‖splitReflection R false υ h d Z
                (reflectionColumnCutoff P D0 Z δ)‖) :=
          mul_nonneg (sub_nonneg.mpr (by simpa [Ksplit, L, J] using hsplit'))
            (add_nonneg hKsplit (norm_nonneg _))
        have hsq : ‖splitReflection R false υ h d Z
            (reflectionColumnCutoff P D0 Z δ)‖ ^ 2 ≤ Bmass := by
          dsimp [Bmass]
          nlinarith [hmul]
        simpa [massTerm, hcond] using hsq
      · simp [massTerm, hc, Bmass]
        positivity
    have hsumBound : (∑ hd ∈ Kset, massTerm hd) ≤ (Kset.card : ℝ) * Bmass := by
      calc
        _ ≤ ∑ hd ∈ Kset, Bmass := Finset.sum_le_sum fun hd hhd => hpoint hd hhd
        _ = (Kset.card : ℝ) * Bmass := by simp [Finset.sum_const, nsmul_eq_mul]
    have hcardK : (Kset.card : ℝ) ≤
        (Cpow * P ^ (1 / 2 : ℝ)) * (Ccnt * (2 * D0)) := by
      calc
        (Kset.card : ℝ) = (Hset.card : ℝ) * (Dset.card : ℝ) := by simp [Kset]
        _ ≤ (Cpow * P ^ (1 / 2 : ℝ)) * (Ccnt * (2 * D0)) :=
          mul_le_mul hHcard hDcard (by positivity) (by positivity)
    have hcardK' : (Kset.card : ℝ) ≤ 4 * Cpow * Ccnt * P ^ (1 / 2 : ℝ) * D0 := by
      calc
        _ ≤ (Cpow * P ^ (1 / 2 : ℝ)) * (Ccnt * (2 * D0)) := hcardK
        _ = 2 * Cpow * Ccnt * P ^ (1 / 2 : ℝ) * D0 := by ring
        _ ≤ 4 * Cpow * Ccnt * P ^ (1 / 2 : ℝ) * D0 := by
          have hbase : 0 ≤ Cpow * Ccnt * P ^ (1 / 2 : ℝ) * D0 := by positivity
          nlinarith
    have hrpowTwo (x a : ℝ) (hx : 0 ≤ x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
      congr 1 <;> ring
    have hBmassEq : Bmass = Csplit ^ 2 * P ^ (2 * δ₁) * L ^ (2 * σ) *
        J ^ (-2 * (N - σ)) := by
      dsimp [Bmass, Ksplit]
      rw [mul_pow, mul_pow, mul_pow, hrpowTwo P δ₁ (by positivity),
        hrpowTwo L σ (by positivity), hrpowTwo J (-(N - σ)) (by positivity)]
      congr 1 <;> ring
    have hPadd : P ^ (1 / 2 : ℝ) * P ^ (2 * δ₁) = P ^ (1 / 2 + 2 * δ₁) := by
      rw [← Real.rpow_add hPpos]
    have hCpos : 0 < 4 * Cpow * Ccnt * Csplit ^ 2 := by positivity
    calc
      reflectionMass R false υ P D0 Z δ = ∑ hd ∈ Kset, massTerm hd := hmassEq
      _ ≤ (Kset.card : ℝ) * Bmass := hsumBound
      _ ≤ (4 * Cpow * Ccnt * P ^ (1 / 2 : ℝ) * D0) * Bmass :=
        mul_le_mul_of_nonneg_right hcardK' hBmass
      _ = (4 * Cpow * Ccnt * Csplit ^ 2) * P ^ (1 / 2 + 2 * δ₁) * D0 *
          L ^ (2 * σ) * J ^ (-2 * (N - σ)) := by
        rw [hBmassEq, ← hPadd]
        ring
      _ = (4 * Cpow * Ccnt * Csplit ^ 2) * P ^ (1 / 2 + 2 * δ₁) * D0 *
          reflectionColumnLength P D0 Z ^ (2 * σ) *
            max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-2 * (N - σ)) := by
        simp [L, J]

set_option maxHeartbeats 800000
/-- rf:tail-mass: the explicit large-N condition giving arbitrary negative powers of Z. -/
theorem rf_tail_negligible : ∀ C0 δ δ₁ σ N A0 : ℝ, 0 < C0 → 0 < δ → 0 < δ₁ →
  1 / 2 < σ → σ < N → 0 < A0 →
  A0 + 2 * M0 * δ₁ + 2 * σ * (2 * M0 - 1) < 2 * δ * (N - σ) →
    ∃ C : ℝ, 0 < C ∧ ∀ υ P D0 Z, 1 ≤ P → 1 ≤ D0 → 2 ≤ Z → P * D0 ≤ C0 * Z ^ M0 →
      reflectionMass R false υ P D0 Z δ ≤ C * Z ^ (-A0) * P ^ (1 / 2 : ℝ) * D0 := by
  intro C0 δ δ₁ σ N A0 hC0 hδ hδ₁ hσ hσN hA0 hExp
  obtain ⟨Cm, hCm, htail⟩ := rf_tail_mass (R := R) δ δ₁ σ N hδ hδ₁ hσ hσN
  let K : ℝ := 8 * C0 ^ 2
  let a : ℝ := 2 * M0 * δ₁
  let b : ℝ := 2 * σ * (2 * M0 - 1)
  let c : ℝ := -2 * δ * (N - σ)
  let e : ℝ := a + b + c
  let C : ℝ := Cm * C0 ^ (2 * δ₁) * K ^ (2 * σ)
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have he : e < -A0 := by
    dsimp [e, a, b, c]
    linarith
  refine ⟨C, hC, ?_⟩
  intro υ P D0 Z hP hD0 hZ hPD
  have hPpos : 0 < P := by linarith
  have hDpos : 0 < D0 := by linarith
  have hZpos : 0 < Z := by linarith
  have hPbound : P ≤ C0 * Z ^ M0 := by
    calc
      P = P * 1 := by ring
      _ ≤ P * D0 := mul_le_mul_of_nonneg_left hD0 hPpos.le
      _ ≤ C0 * Z ^ M0 := hPD
  have hP2 : P ≤ P ^ 2 := by
    calc
      P = P * 1 := by ring
      _ ≤ P * P := mul_le_mul_of_nonneg_left hP hPpos.le
      _ = P ^ 2 := by ring
  have hD2P : D0 ^ 2 * P ≤ (P * D0) ^ 2 := by
    calc
      D0 ^ 2 * P ≤ D0 ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_left hP2 (by positivity)
      _ = (P * D0) ^ 2 := by ring
  have hPDsquare : (P * D0) ^ 2 ≤ C0 ^ 2 * Z ^ (2 * M0) := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ P * D0) hPD 2
    calc
      (P * D0) ^ 2 ≤ (C0 * Z ^ M0) ^ 2 := hpow
      _ = C0 ^ 2 * Z ^ (2 * M0) := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZpos.le]
        congr 1 <;> ring
  have hLpos : 0 < reflectionColumnLength P D0 Z := by
    dsimp [reflectionColumnLength]
    positivity
  have hLbound : reflectionColumnLength P D0 Z ≤ K * Z ^ (2 * M0 - 1) := by
    have hcoef : 0 ≤ 8 / Z := by positivity
    have hdivPow (x : ℝ) : Z ^ x / Z = Z ^ (x - 1) := by
      calc
        Z ^ x / Z = Z ^ x * Z ^ (-1 : ℝ) := by rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        _ = Z ^ (x + (-1 : ℝ)) := by rw [← Real.rpow_add hZpos]
        _ = Z ^ (x - 1) := by congr 1 <;> ring
    calc
      reflectionColumnLength P D0 Z = (8 / Z) * (D0 ^ 2 * P) := by
        dsimp [reflectionColumnLength]
        ring
      _ ≤ (8 / Z) * (C0 ^ 2 * Z ^ (2 * M0)) := by
        exact mul_le_mul_of_nonneg_left (hD2P.trans hPDsquare) hcoef
      _ = K * Z ^ (2 * M0) / Z := by dsimp [K]; ring
      _ = K * Z ^ (2 * M0 - 1) := by
        calc
          K * Z ^ (2 * M0) / Z = K * (Z ^ (2 * M0) / Z) := by ring
          _ = K * Z ^ (2 * M0 - 1) := by rw [hdivPow]
  have hPpow : P ^ (2 * δ₁) ≤ C0 ^ (2 * δ₁) * Z ^ a := by
    have hδpow : 0 < 2 * δ₁ := by positivity
    calc
      P ^ (2 * δ₁) ≤ (C0 * Z ^ M0) ^ (2 * δ₁) :=
        Real.rpow_le_rpow hPpos.le hPbound hδpow.le
      _ = C0 ^ (2 * δ₁) * Z ^ a := by
        rw [Real.mul_rpow hC0.le (Real.rpow_nonneg hZpos.le M0), ← Real.rpow_mul hZpos.le]
        congr 1 <;> dsimp [a] <;> ring
  have hLpow : reflectionColumnLength P D0 Z ^ (2 * σ) ≤
      K ^ (2 * σ) * Z ^ b := by
    have hσpow : 0 < 2 * σ := by linarith
    calc
      reflectionColumnLength P D0 Z ^ (2 * σ) ≤ (K * Z ^ (2 * M0 - 1)) ^ (2 * σ) :=
        Real.rpow_le_rpow hLpos.le hLbound hσpow.le
      _ = K ^ (2 * σ) * Z ^ b := by
        rw [Real.mul_rpow hK.le (Real.rpow_nonneg hZpos.le _), ← Real.rpow_mul hZpos.le]
        congr 1 <;> dsimp [b] <;> ring
  have hJpow :
      max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-2 * (N - σ)) ≤
        Z ^ c := by
    have hZδpos : 0 < Z ^ δ := Real.rpow_pos_of_pos hZpos δ
    have hbase : Z ^ δ ≤ max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ := le_max_left _ _
    have hexp : -2 * (N - σ) ≤ 0 := by linarith
    calc
      max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-2 * (N - σ)) ≤
          (Z ^ δ) ^ (-2 * (N - σ)) :=
        Real.rpow_le_rpow_of_nonpos hZδpos hbase hexp
      _ = Z ^ c := by
        rw [← Real.rpow_mul hZpos.le]
        congr 1 <;> dsimp [c] <;> ring
  have hprod :
      P ^ (1 / 2 + 2 * δ₁) * reflectionColumnLength P D0 Z ^ (2 * σ) *
          max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-2 * (N - σ)) ≤
        P ^ (1 / 2 : ℝ) * (C0 ^ (2 * δ₁) * Z ^ a) * (K ^ (2 * σ) * Z ^ b) * Z ^ c := by
    rw [Real.rpow_add hPpos]
    gcongr
  have hZprod : Z ^ a * Z ^ b * Z ^ c = Z ^ e := by
    calc
      Z ^ a * Z ^ b * Z ^ c = Z ^ (a + b) * Z ^ c := by rw [← Real.rpow_add hZpos]
      _ = Z ^ ((a + b) + c) := by rw [← Real.rpow_add hZpos]
      _ = Z ^ e := by congr 1 <;> dsimp [e] <;> ring
  have hmass := htail υ P D0 Z hP hD0 hZ
  calc
    reflectionMass R false υ P D0 Z δ ≤
        Cm * P ^ (1 / 2 + 2 * δ₁) * D0 *
          reflectionColumnLength P D0 Z ^ (2 * σ) *
            max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-2 * (N - σ)) := hmass
    _ = Cm * D0 * (P ^ (1 / 2 + 2 * δ₁) *
          reflectionColumnLength P D0 Z ^ (2 * σ) *
            max (Z ^ δ) (reflectionColumnLength P D0 Z)⁻¹ ^ (-2 * (N - σ)) ) := by ring
    _ ≤ Cm * D0 * (P ^ (1 / 2 : ℝ) * (C0 ^ (2 * δ₁) * Z ^ a) *
          (K ^ (2 * σ) * Z ^ b) * Z ^ c) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = C * Z ^ e * P ^ (1 / 2 : ℝ) * D0 := by
      rw [← hZprod]
      dsimp [C]
      ring
    _ ≤ C * Z ^ (-A0) * P ^ (1 / 2 : ℝ) * D0 := by
      have hZpow : Z ^ e ≤ Z ^ (-A0) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) he.le
      have hfactor : 0 ≤ C * P ^ (1 / 2 : ℝ) * D0 := by positivity
      calc
        C * Z ^ e * P ^ (1 / 2 : ℝ) * D0 =
            (C * P ^ (1 / 2 : ℝ) * D0) * Z ^ e := by ring
        _ ≤ (C * P ^ (1 / 2 : ℝ) * D0) * Z ^ (-A0) :=
          mul_le_mul_of_nonneg_left hZpow hfactor
        _ = C * Z ^ (-A0) * P ^ (1 / 2 : ℝ) * D0 := by ring
/-- Fourier transform with the 2π convention; only its L1 bound is used by retained mass. -/
def separatedFourier (ρ : ℝ → ℂ) (υ : UnitSix S) (κ : S.V) (v τ : ℝ) : ℂ :=
  ∫ x : ℝ, ρ x * profilePhi R υ κ (v * Real.exp x) * Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * τ)

/-- rf:retained-mass: the fixed profile separation estimate (04:1120–1141). -/
theorem rf_retained_fourier_separation : ∃ α : ℝ, 0 < α ∧ ∀ N : ℝ, 0 < N →
  ∀ ρ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ → HasCompactSupport ρ →
    ∃ C : ℝ, 0 < C ∧ ∀ υ κ v, 0 < v →
      Integrable (fun τ => ‖separatedFourier R ρ υ κ v τ‖) ∧
      (∫ τ : ℝ, ‖separatedFourier R ρ υ κ v τ‖) ≤ C * min (v ^ α) (v ^ (-N)) := by
  obtain ⟨α, hα, hprofile⟩ := (rf_profile_bound R).2.1
  refine ⟨α, hα, ?_⟩
  intro N hN ρ hρ hρc
  classical
  letI : Fintype (UnitSix S) := R.sheets.unitSixFinite
  letI : Fintype S.V := R.sheets.classFinite
  let Pairs : Type := UnitSix S × S.V
  have hPhiDeriv (u : UnitSix S) (κ : S.V) :
      ∀ j : ℕ, j ≤ 2 → ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, ∀ x : ℝ, 0 < x →
          ‖Theta.normDerivR j (profilePhi R u κ) x‖ ≤ C * min (x ^ α) (x ^ (-A)) := by
    intro j hj A hA
    obtain ⟨C, _, hbound⟩ := hprofile A hA j
    exact ⟨C, fun x hx => hbound u κ x hx⟩
  have hPhiSmooth (u : UnitSix S) (κ : S.V) :
      ContDiffOn ℝ 2 (profilePhi R u κ) (Set.Ioi 0) := by
    exact ((rf_profile_bound R).1 u κ).of_le (by norm_num)
  have hSheet (u : UnitSix S) (κ : S.V) :
      ∃ C : ℝ, ∀ v : ℝ, 0 < v →
        (∫ τ : ℝ, ‖𝓕 (fun x : ℝ => ρ x * profilePhi R u κ (v * Real.exp x)) τ‖) ≤
          C * min (v ^ α) (v ^ (-N)) := by
    exact Theta.sheet_fourier_separation ρ hρ hρc (profilePhi R u κ) α hα
      (hPhiDeriv u κ) (hPhiSmooth u κ) N hN
  let Cpair : Pairs → ℝ := fun p => Classical.choose (hSheet p.1 p.2)
  have hSheetBound (p : Pairs) (v : ℝ) (hv : 0 < v) :
      (∫ τ : ℝ, ‖𝓕 (fun x : ℝ => ρ x * profilePhi R p.1 p.2 (v * Real.exp x)) τ‖) ≤
        Cpair p * min (v ^ α) (v ^ (-N)) :=
    Classical.choose_spec (hSheet p.1 p.2) v hv
  let C : ℝ := 1 + ∑ p : Pairs, max 0 (Cpair p)
  have hCpos : 0 < C := by
    dsimp [C]
    have hnonneg : 0 ≤ ∑ p : Pairs, max 0 (Cpair p) := by
      apply Finset.sum_nonneg
      intro p hp
      exact le_max_left 0 _
    linarith
  have hCpairLe (p : Pairs) : Cpair p ≤ C := by
    have hsum : max 0 (Cpair p) ≤ ∑ q : Pairs, max 0 (Cpair q) := by
      exact Finset.single_le_sum (fun q hq => le_max_left 0 (Cpair q))
        (Finset.mem_univ p)
    have hmax : Cpair p ≤ max 0 (Cpair p) := le_max_right _ _
    dsimp [C]
    linarith
  have hprofileFourierEq (u : UnitSix S) (κ : S.V) (v : ℝ) (τ : ℝ) :
      separatedFourier R ρ u κ v τ =
        𝓕 (fun x : ℝ => ρ x * profilePhi R u κ (v * Real.exp x)) τ := by
    rw [separatedFourier, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [smul_eq_mul]
    have hexp : -2 * Real.pi * Complex.I * (x : ℂ) * τ =
        ((-2 * Real.pi * x * τ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp]
    ring
  have hFourierIntegrable (u : UnitSix S) (κ : S.V) (v : ℝ) (hv : 0 < v) :
      Integrable (fun τ : ℝ => ‖separatedFourier R ρ u κ v τ‖) := by
    let g : ℝ → ℂ := fun x => ρ x * profilePhi R u κ (v * Real.exp x)
    have hargSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => v * Real.exp x) := by fun_prop
    have hargPos (x : ℝ) : v * Real.exp x ∈ Set.Ioi (0 : ℝ) :=
      Set.mem_Ioi.mpr (mul_pos hv (Real.exp_pos x))
    have hprofileComp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => profilePhi R u κ (v * Real.exp x)) := by
      exact (rf_profile_bound R).1 u κ |>.comp_contDiff hargSmooth hargPos
    have hgsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
      dsimp [g]
      exact hρ.mul hprofileComp
    have hgcompact : HasCompactSupport g := by
      dsimp [g]
      exact hρc.mul_right
    let G : SchwartzMap ℝ ℂ := hgcompact.toSchwartzMap hgsmooth
    have hGFourier : Integrable (fun τ : ℝ => (𝓕 G) τ) := (𝓕 G).integrable
    have hGFourierEq (τ : ℝ) :
        separatedFourier R ρ u κ v τ = (𝓕 G) τ := by
      rw [SchwartzMap.fourier_coe]
      exact hprofileFourierEq u κ v τ
    exact hGFourier.norm.congr (Filter.Eventually.of_forall fun τ => by
      change ‖(𝓕 G) τ‖ = ‖separatedFourier R ρ u κ v τ‖
      exact congrArg (fun z : ℂ => ‖z‖) (hGFourierEq τ).symm)
  refine ⟨C, hCpos, ?_⟩
  intro u κ v hv
  refine ⟨hFourierIntegrable u κ v hv, ?_⟩
  have hnum :
      (∫ τ : ℝ, ‖separatedFourier R ρ u κ v τ‖) ≤
        Cpair (u, κ) * min (v ^ α) (v ^ (-N)) := by
    calc
      _ = ∫ τ : ℝ, ‖𝓕 (fun x : ℝ => ρ x * profilePhi R u κ (v * Real.exp x)) τ‖ := by
        apply integral_congr_ae
        filter_upwards with τ
        rw [hprofileFourierEq u κ v τ]
      _ ≤ Cpair (u, κ) * min (v ^ α) (v ^ (-N)) := hSheetBound (u, κ) v hv
  have hmin : 0 ≤ min (v ^ α) (v ^ (-N)) := by
    apply le_min <;> positivity
  exact le_trans hnum (mul_le_mul_of_nonneg_right (hCpairLe (u, κ)) hmin)

private def rf_retained_log_cutoff_bump : ContDiffBump (0 : ℝ) :=
  ⟨2, 3, by norm_num, by norm_num⟩

private noncomputable def rf_retained_log_cutoff (x : ℝ) : ℂ :=
  (rf_retained_log_cutoff_bump x : ℂ)

private lemma rf_retained_log_cutoff_smooth :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rf_retained_log_cutoff := by
  exact Complex.ofRealCLM.contDiff.comp rf_retained_log_cutoff_bump.contDiff

private lemma rf_retained_log_cutoff_compact : HasCompactSupport rf_retained_log_cutoff := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) 3)
  intro x hx
  have hx' : rf_retained_log_cutoff_bump x ≠ 0 := by
    simpa [rf_retained_log_cutoff, Complex.ofReal_eq_zero] using hx
  have hx'' : x ∈ Function.support rf_retained_log_cutoff_bump := by
    simpa only [Function.mem_support] using hx'
  rw [rf_retained_log_cutoff_bump.support_eq] at hx''
  exact Metric.ball_subset_closedBall hx''

private lemma rf_retained_log_cutoff_one {x : ℝ} (hx : |x| ≤ 2) :
    rf_retained_log_cutoff x = 1 := by
  have hball : x ∈ Metric.closedBall (0 : ℝ) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact hx
  change (rf_retained_log_cutoff_bump x : ℂ) = 1
  rw [rf_retained_log_cutoff_bump.one_of_mem_closedBall hball]
  simp

private lemma rf_retained_fourier_inversion (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (υ : UnitSix S) (κ : S.V) (v : ℝ) (hv : 0 < v) (x : ℝ) :
    Integrable (fun τ : ℝ => separatedFourier R ρ υ κ v τ) ∧
    ρ x * profilePhi R υ κ (v * Real.exp x) =
      ∫ τ : ℝ, separatedFourier R ρ υ κ v τ *
        Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) := by
  let g : ℝ → ℂ := fun x => ρ x * profilePhi R υ κ (v * Real.exp x)
  have hargSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => v * Real.exp x) := by fun_prop
  have hargPos (x : ℝ) : v * Real.exp x ∈ Set.Ioi (0 : ℝ) :=
    Set.mem_Ioi.mpr (mul_pos hv (Real.exp_pos x))
  have hprofileComp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => profilePhi R υ κ (v * Real.exp x)) := by
    exact (rf_profile_bound R).1 υ κ |>.comp_contDiff hargSmooth hargPos
  have hgsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    dsimp [g]
    exact hρ.mul hprofileComp
  have hgcompact : HasCompactSupport g := by
    dsimp [g]
    exact hρc.mul_right
  let G : SchwartzMap ℝ ℂ := hgcompact.toSchwartzMap hgsmooth
  have hprofileFourierEq (τ : ℝ) :
      separatedFourier R ρ υ κ v τ =
        𝓕 (fun y : ℝ => ρ y * profilePhi R υ κ (v * Real.exp y)) τ := by
    rw [separatedFourier, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    simp only [smul_eq_mul]
    have hexp : -2 * Real.pi * Complex.I * (y : ℂ) * τ =
        ((-2 * Real.pi * y * τ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp]
    ring
  have hFourierEq (τ : ℝ) : separatedFourier R ρ υ κ v τ = (𝓕 G) τ := by
    rw [SchwartzMap.fourier_coe]
    exact hprofileFourierEq τ
  have hFourierInt : Integrable (fun τ : ℝ => 𝓕 (G : ℝ → ℂ) τ) := (𝓕 G).integrable
  have hFourierIntSch : Integrable (fun τ : ℝ => (𝓕 G) τ) := by
    simpa only [SchwartzMap.fourier_coe] using hFourierInt
  have hFourierEq' (τ : ℝ) : (𝓕 G) τ = separatedFourier R ρ υ κ v τ :=
    (hFourierEq τ).symm
  have hSeparatedInt : Integrable (fun τ : ℝ => separatedFourier R ρ υ κ v τ) :=
    hFourierIntSch.congr (Filter.Eventually.of_forall hFourierEq')
  have hInvSch : 𝓕⁻ (𝓕 G) = G := by
    ext y
    rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe]
    exact congrFun (G.continuous.fourierInv_fourier_eq G.integrable (𝓕 G).integrable) y
  have hInv : 𝓕⁻ (𝓕 (G : ℝ → ℂ)) x = G x := by
    have h := congrArg (fun H : SchwartzMap ℝ ℂ => (H : ℝ → ℂ)) hInvSch
    simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using congrFun h x
  have hInvIntegral :
      𝓕⁻ (𝓕 (G : ℝ → ℂ)) x =
        ∫ τ : ℝ, Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) *
          𝓕 (G : ℝ → ℂ) τ := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards [] with τ
    rw [Real.inner_apply]
    simp only [smul_eq_mul]
    have harg : (2 * Real.pi * (τ * x) : ℝ) = 2 * Real.pi * τ * x := by ring
    rw [harg]
  refine ⟨hSeparatedInt, ?_⟩
  calc
    ρ x * profilePhi R υ κ (v * Real.exp x) = G x := rfl
    _ = 𝓕⁻ (𝓕 (G : ℝ → ℂ)) x := hInv.symm
    _ = ∫ τ : ℝ, Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) *
          𝓕 (G : ℝ → ℂ) τ := hInvIntegral
    _ = ∫ τ : ℝ, separatedFourier R ρ υ κ v τ *
          Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I) := by
      apply integral_congr_ae
      filter_upwards [] with τ
      rw [hFourierEq]
      exact mul_comm _ _

private def rf_retained_fourier_phase (τ x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * τ * x : ℝ) : ℂ) * Complex.I)

private lemma rf_retained_fourier_phase_norm (τ x : ℝ) :
    ‖rf_retained_fourier_phase τ x‖ = 1 := by
  simp [rf_retained_fourier_phase, Complex.norm_exp]

@[continuity]
private lemma rf_retained_fourier_phase_continuous (x : ℝ) :
    Continuous (fun τ : ℝ => rf_retained_fourier_phase τ x) := by
  unfold rf_retained_fourier_phase
  fun_prop

private lemma rf_retained_fourier_phase_sub (τ x y : ℝ) :
    rf_retained_fourier_phase τ (x - y) =
      rf_retained_fourier_phase τ x * rf_retained_fourier_phase τ (-y) := by
  unfold rf_retained_fourier_phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
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
  intro v w hv hw hne
  have idealExp_zero_iff (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
      (P : FinPlace F) :
      idealExp P I = 0 ↔ ¬ P.asIdeal ∣ I := by
    unfold idealExp
    constructor
    · intro h hdiv
      exact ((Associates.count_ne_zero_iff_dvd hI P.irreducible).mpr hdiv) h
    · intro h
      by_contra hne0
      exact h ((Associates.count_ne_zero_iff_dvd hI P.irreducible).mp hne0)
  have gen_valuation (P : FinPlace F) (p : Fˣ) (I : Ideal (𝓞 F))
      (hgen : S.IsGen (p : F) I) (hP : P ∉ S.Sf)
      (hzero : idealExp P I = 0) : P.valuation F (p : F) = 1 := by
    have hcount : FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) =
          (idealExp P I : ℤ) := by
      rw [hgen.2.2 P hP, FractionalIdeal.count_coe F P hgen.1.1]
      rfl
    have hlog := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
      P (p : F) p.ne_zero
    rw [hcount, hzero] at hlog
    have hLog : WithZero.log (P.valuation F (p : F)) = 0 := by
      have hlogneg : -(WithZero.log (P.valuation F (p : F))) = 0 := by
        simpa using hlog.symm
      exact neg_eq_zero.mp hlogneg
    have hval0 : P.valuation F (p : F) ≠ 0 :=
      (Valuation.ne_zero_iff (P.valuation F)).mpr p.ne_zero
    calc
      P.valuation F (p : F) = WithZero.exp (WithZero.log (P.valuation F (p : F))) :=
        (WithZero.exp_log hval0).symm
      _ = 1 := by rw [hLog, WithZero.exp_zero]
  let pv := primeGen R v
  let pw := primeGen R w
  have hpv : S.IsGen (pv : F) v.asIdeal ∧ Bd.Allowed pv := by
    simpa [pv, primeGen, hv, R.exterior.prime_val] using
      (bc.gen_spec (R.exterior.prime v hv))
  have hpw : S.IsGen (pw : F) w.asIdeal ∧ Bd.Allowed pw := by
    simpa [pw, primeGen, hw, R.exterior.prime_val] using
      (bc.gen_spec (R.exterior.prime w hw))
  have hnotdiv_vw : ¬ v.asIdeal ∣ w.asIdeal := by
    intro hdiv
    have hle : w.asIdeal ≤ v.asIdeal := Ideal.le_of_dvd hdiv
    have heq : w.asIdeal = v.asIdeal := w.isMaximal.eq_of_le v.isPrime.ne_top hle
    exact hne (HeightOneSpectrum.ext heq.symm)
  have hzero_v : idealExp v w.asIdeal = 0 :=
    (idealExp_zero_iff w.asIdeal w.ne_bot v).2 hnotdiv_vw
  have hpwVal : v.valuation F (pw : F) = 1 :=
    gen_valuation v pw w.asIdeal hpw.1 hv hzero_v
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hpwRes : residue v (pw : F) ≠ 0 := by
    exact (SB.residue_ne_zero v (pw : F) (by simp [hpwVal])).2 hpwVal
  have hrecip : chi D v (pw : F) = chi D w (pv : F) :=
    ArtinPrimitiveRoots.A1.sextic_reciprocity D S H Bd v w hv hw hne pv pw hpv hpw
  let z : ℂ := chi D v (pw : F)
  have hz6 : z ^ (6 : ℕ) = 1 := by
    dsimp [z]
    exact SB.chi_six v (pw : F) hpwRes
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at hz6
    norm_num at hz6
  have hpow6z : z ^ (6 : ℤ) = 1 := by
    calc
      z ^ (6 : ℤ) = z ^ (6 : ℕ) := zpow_natCast z 6
      _ = 1 := hz6
  have hmul : z * z ^ (-4 : ℤ) = z ^ (-3 : ℤ) := by
    calc
      z * z ^ (-4 : ℤ) = z ^ (1 : ℤ) * z ^ (-4 : ℤ) := by simp
      _ = z ^ ((1 : ℤ) + (-4 : ℤ)) := (zpow_add₀ hz0 _ _).symm
      _ = z ^ (-3 : ℤ) := by congr 1 <;> norm_num
  have hneg3 : z ^ (3 : ℕ) = z ^ (-3 : ℤ) := by
    calc
      z ^ (3 : ℕ) = z ^ (3 : ℤ) := (zpow_natCast z 3).symm
      _ = z ^ ((6 : ℤ) + (-3 : ℤ)) := by congr 1 <;> norm_num
      _ = z ^ (6 : ℤ) * z ^ (-3 : ℤ) := zpow_add₀ hz0 _ _
      _ = 1 * z ^ (-3 : ℤ) := by rw [hpow6z]
      _ = z ^ (-3 : ℤ) := by simp
  change z * (chi D w (pv : F)) ^ (-4 : ℤ) = z ^ (3 : ℕ)
  rw [hrecip.symm]
  change z * z ^ (-4 : ℤ) = z ^ (3 : ℕ)
  calc
    z * z ^ (-4 : ℤ) = z ^ (-3 : ℤ) := hmul
    _ = z ^ (3 : ℕ) := hneg3.symm
/-- rf:S-unfolding: averaging the signed orbit gives the combined Φ profile. -/
theorem rf_S_averaged : ∀ u (ν : Fˣ) Z, 0 < Z →
  (∫ T in Set.Ioi (0 : ℝ), R.K T *
    (∑' γ : Gamma S, omegaInt R (T / Z) (fun y => bCut (Bd := Bd) y * (Lvalue R u y)⁻¹ *
      sCocycle (D := D) (H := H) (S.diagU ((γ.1 : Fˣ) * ν)) y⁻¹ *
        rotated R u (S.diagU ((γ.1 : Fˣ) * ν) / y))) / (T : ℂ)) =
      (Lvalue R u (S.diagU ν))⁻¹ * profilePhi R u (cls (S.diagU ν)) (Z * S.absS (S.diagU ν : S.FS)) := by
  intro u ν Z hZ
  let κ : S.V := cls (S.diagU ν)
  let m : S.FSˣ → ℂ := fun y =>
    (if κ * (cls y)⁻¹ ∈ Bd.B then 1 else 0) *
      R.pairing.pair κ (cls y) ^ 2 * Lvalue R u y
  let b : S.V → ℂ := fun x =>
    (if κ * x⁻¹ ∈ Bd.B then 1 else 0) * R.pairing.pair κ x ^ 2
  have hb : ∀ x, ‖b x‖ ≤ 1 := by
    intro x
    by_cases hx : κ * x⁻¹ ∈ Bd.B <;> simp [b, hx, R.pairing.unitary κ x]
  have hm : Theta.SheetMultiplier S (onUnits m) := by
    refine ⟨R.chars.L u, 1, b, ⟨1, hb⟩, ?_⟩
    intro y
    have hunit : IsUnit (y : S.FS) := Units.isUnit y
    have hunit_eq : hunit.unit = y := by
      apply Units.ext
      exact hunit.unit_spec
    change (if h : IsUnit (y : S.FS) then m h.unit else 0) =
      (((R.chars.L u).L y : ℂˣ) : ℂ) ^ (1 : ℤ) * b (cls y)
    rw [dif_pos hunit, hunit_eq]
    by_cases hy : κ * (cls y)⁻¹ ∈ Bd.B
    · simp [m, b, Lvalue, hy, mul_comm, mul_left_comm]
    · simp [m, b, Lvalue, hy]
  have hprofile (ℓ : Fin (R.rotated u).J) (x : ℝ) :
      profileH R u κ ℓ x =
        bridgeProfileH R.sheets m (R.rotated u).J (R.rotated u).ff (R.rotated u).fc ℓ x := by
    rfl
  have hKmeas : AEStronglyMeasurable R.K (volume.restrict (Set.Ioi (0 : ℝ))) :=
    R.K_smooth.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hff : ∀ ℓ v, SheetHypFin v.1 R.T.δ ((R.rotated u).ff ℓ v) :=
    (R.rotated u).finite_bound
  have hfc : ∀ ℓ w, SheetHypC R.T.δ ((R.rotated u).fc ℓ w) :=
    (R.rotated u).complex_bound
  have hconv := a2_bridge_ANALYSIS_convolution (G := R.sheets) R.T.δ R.T.δ_pos
    (R.rotated u).J (R.rotated u).ff (R.rotated u).fc hff hfc R.K hKmeas
    R.K_moments m hm
  have hnormν : 0 < S.absS (S.diagU ν : S.FS) :=
    (a2_bridge_NORM D S).2.2.1 (S.diagU ν)
  let x : ℝ := Z * S.absS (S.diagU ν : S.FS)
  have hx : 0 < x := mul_pos hZ hnormν
  have hprofInt (ℓ : Fin (R.rotated u).J) :
      IntegrableOn (fun T : ℝ =>
        R.K T * profileH R u κ ℓ (x / T) / (T : ℂ)) (Set.Ioi 0) := by
    simpa only [← hprofile] using (hconv x hx).2.2 ℓ
  have hpoint (T : ℝ) (hT : 0 < T) :
      (∑' γ : Gamma S, omegaInt R (T / Z) (fun y => bCut (Bd := Bd) y *
        (Lvalue R u y)⁻¹ *
          sCocycle (D := D) (H := H) (S.diagU ((γ.1 : Fˣ) * ν)) y⁻¹ *
            rotated R u (S.diagU ((γ.1 : Fˣ) * ν) / y))) =
        (Lvalue R u (S.diagU ν))⁻¹ *
          ∑ ℓ : Fin (R.rotated u).J, profileH R u κ ℓ (x / T) := by
    have hu := rf_S_unfolding R u ν (T / Z) (div_pos hT hZ)
    have harg : S.absS (S.diagU ν : S.FS) / (T / Z) = x / T := by
      dsimp [x]
      field_simp [ne_of_gt hT, ne_of_gt hZ]
    simpa only [harg] using hu.2
  have hcongr :
      (fun T : ℝ => R.K T *
        (∑' γ : Gamma S, omegaInt R (T / Z) (fun y => bCut (Bd := Bd) y *
          (Lvalue R u y)⁻¹ *
            sCocycle (D := D) (H := H) (S.diagU ((γ.1 : Fˣ) * ν)) y⁻¹ *
              rotated R u (S.diagU ((γ.1 : Fˣ) * ν) / y))) / (T : ℂ)) =ᵐ[
        volume.restrict (Set.Ioi (0 : ℝ))]
      fun T => (Lvalue R u (S.diagU ν))⁻¹ *
        ∑ ℓ : Fin (R.rotated u).J,
          R.K T * profileH R u κ ℓ (x / T) / (T : ℂ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    calc
      _ = (Lvalue R u (S.diagU ν))⁻¹ *
          ((R.K T / (T : ℂ)) *
            ∑ ℓ : Fin (R.rotated u).J, profileH R u κ ℓ (x / T)) := by
        rw [hpoint T hT]
        ring
      _ = (Lvalue R u (S.diagU ν))⁻¹ *
          ∑ ℓ : Fin (R.rotated u).J,
            R.K T * profileH R u κ ℓ (x / T) / (T : ℂ) := by
        rw [Finset.mul_sum]
        apply congrArg (fun z : ℂ => (Lvalue R u (S.diagU ν))⁻¹ * z)
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        ring
  calc
    (∫ T in Set.Ioi (0 : ℝ), R.K T *
        (∑' γ : Gamma S, omegaInt R (T / Z) (fun y => bCut (Bd := Bd) y *
          (Lvalue R u y)⁻¹ *
            sCocycle (D := D) (H := H) (S.diagU ((γ.1 : Fˣ) * ν)) y⁻¹ *
              rotated R u (S.diagU ((γ.1 : Fˣ) * ν) / y))) / (T : ℂ)) =
        ∫ T in Set.Ioi (0 : ℝ), (Lvalue R u (S.diagU ν))⁻¹ *
          ∑ ℓ : Fin (R.rotated u).J,
            R.K T * profileH R u κ ℓ (x / T) / (T : ℂ) := by
      exact integral_congr_ae hcongr
    _ = (Lvalue R u (S.diagU ν))⁻¹ *
        ∑ ℓ : Fin (R.rotated u).J,
          ∫ T in Set.Ioi (0 : ℝ),
            R.K T * profileH R u κ ℓ (x / T) / (T : ℂ) := by
      rw [integral_const_mul, integral_finsetSum]
      intro ℓ hℓ
      exact hprofInt ℓ
    _ = (Lvalue R u (S.diagU ν))⁻¹ * profilePhi R u κ x := by
      simp [profilePhi, profilePhiTerm]
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
  classical
  obtain ⟨α, hα, hsep⟩ := rf_retained_fourier_separation R
  refine ⟨α, hα, ?_⟩
  intro N ε hN hε
  let ρ : ℝ → ℂ := rf_retained_log_cutoff
  have hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := rf_retained_log_cutoff_smooth
  have hρc : HasCompactSupport ρ := rf_retained_log_cutoff_compact
  obtain ⟨CFT, hCFT, hFT⟩ := hsep N hN ρ hρ hρc
  obtain ⟨Csieve, hCsieve, hSieve⟩ := lem_reflection_quadratic_sieve D S H Bd ε hε
  obtain ⟨Ccnt, hCcnt, hCount⟩ := a2_bridge_COUNT S
  refine ⟨CFT * Real.sqrt (4 * Ccnt * Csieve) * 4 ^ (ε / 2), ?_, ?_⟩
  · positivity
  · intro υ h t sd sc C D0 Z R0 hC hD hZ hR0
    dsimp only
    let v : ℝ := Z * qI t.a.1 * qI t.n.1 ^ 3 * C / (D0 ^ 2 * qI t.f.1 ^ 2)
    have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
    have hDpos : 0 < D0 := lt_of_lt_of_le (by norm_num) hD
    have hZpos : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
    have hqA := rf_qI_pos_ge_one t.a.1 t.a.2.1
    have hqN := rf_qI_pos_ge_one t.n.1 t.n.2.1
    have hqF := rf_qI_pos_ge_one t.f.1 t.f.2.1
    have hv : 0 < v := by
      dsimp [v]
      have hnum : 0 < Z * qI t.a.1 * qI t.n.1 ^ 3 * C :=
        mul_pos (mul_pos (mul_pos hZpos hqA.1) (pow_pos hqN.1 3)) hCpos
      have hden : 0 < D0 ^ 2 * qI t.f.1 ^ 2 :=
        mul_pos (pow_pos hDpos 2) (pow_pos hqF.1 2)
      exact div_pos hnum hden
    let extOfSqf : S.SqfExtIdeal → S.ExtIdeal := fun c => ⟨c.1, c.2.1⟩
    let rowDyad : S.ExtIdeal → Prop := fun d => D0 ≤ qI d.1 ∧ qI d.1 < 2 * D0
    let rowPred : S.SqfExtIdeal → Prop := fun d => rowDyad (extOfSqf d)
    let rowSet : Set S.SqfExtIdeal := {d | rowPred d}
    let colPred : S.SqfExtIdeal → Prop := fun c => C ≤ qI c.1 ∧ qI c.1 < 2 * C
    let colSet : Set S.SqfExtIdeal := {c | colPred c}
    have hextOfSqfInj : Function.Injective extOfSqf := by
      intro c c' he
      apply Subtype.ext
      have h := congrArg (fun I : S.ExtIdeal => I.1) he
      simpa [extOfSqf] using h
    have hcutD := a2_bridge_COUNT_finite S (2 * D0) (by positivity)
    have hrowFinite : rowSet.Finite := by
      have hpre : {d : S.SqfExtIdeal | idealNorm (extOfSqf d).1 ≤ 2 * D0}.Finite :=
        hcutD.1.preimage (f := extOfSqf) (fun _ _ _ _ h => hextOfSqfInj h)
      apply hpre.subset
      intro d hd
      change idealNorm (extOfSqf d).1 ≤ 2 * D0
      simpa [rowPred, qI, idealNorm, extOfSqf] using
        (show qI d.1 < 2 * D0 from hd.2).le
    let rows : Finset S.SqfExtIdeal := hrowFinite.toFinset
    have hmemRows (d : S.SqfExtIdeal) : d ∈ rows ↔ rowPred d := by
      exact Set.Finite.mem_toFinset hrowFinite
    have hcutC := a2_bridge_COUNT_finite S (2 * C) (by positivity)
    have hcolFinite : colSet.Finite := by
      have hpre : {c : S.SqfExtIdeal | idealNorm (extOfSqf c).1 ≤ 2 * C}.Finite :=
        hcutC.1.preimage (f := extOfSqf) (fun _ _ _ _ h => hextOfSqfInj h)
      apply hpre.subset
      intro c hc
      change idealNorm (extOfSqf c).1 ≤ 2 * C
      simpa [colPred, qI, idealNorm, extOfSqf] using
        (show qI c.1 ≤ 2 * C from hc.2.le)
    let cols : Finset S.SqfExtIdeal := hcolFinite.toFinset
    have hmemCols (c : S.SqfExtIdeal) : c ∈ cols ↔ colPred c := by
      exact Set.Finite.mem_toFinset hcolFinite
    have hDsetEq : hcutC.1.toFinset = bridgeNormFinset S (2 * C) := by
      ext I
      rw [Set.Finite.mem_toFinset]
      exact (hcutC.2 I).symm
    have hcolImageSub : cols.image extOfSqf ⊆ bridgeNormFinset S (2 * C) := by
      intro I hI
      rcases Finset.mem_image.mp hI with ⟨c, hc, rfl⟩
      apply (hcutC.2 (extOfSqf c)).2
      have hc' := (hmemCols c).mp hc
      simpa [qI, idealNorm, extOfSqf] using hc'.2.le
    have hcolCard : (cols.card : ℝ) ≤ Ccnt * (2 * C) := by
      have hnat : {I : S.ExtIdeal | idealNorm I.1 ≤ 2 * C}.ncard =
          (bridgeNormFinset S (2 * C)).card := by
        rw [Set.ncard_eq_toFinset_card _ hcutC.1, hDsetEq]
      have hcount := hCount (2 * C) (by linarith)
      calc
        (cols.card : ℝ) = ((cols.image extOfSqf).card : ℝ) := by
          exact_mod_cast (Finset.card_image_of_injective cols hextOfSqfInj).symm
        _ ≤ ((bridgeNormFinset S (2 * C)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hcolImageSub
        _ = ({I : S.ExtIdeal | idealNorm I.1 ≤ 2 * C}.ncard : ℝ) := by
          exact_mod_cast hnat.symm
        _ ≤ Ccnt * (2 * C) := hcount
    let keep : S.SqfExtIdeal → Prop := fun c =>
      qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 ≤ R0
    let coeff : S.SqfExtIdeal → ℂ := fun c =>
      frozenLambda R υ t sc c * (qI c.1 ^ (-(1 / 2 : ℝ)) : ℝ)
    let z : ℝ → S.SqfExtIdeal → ℂ := fun τ c =>
      if keep c then coeff c * rf_retained_fourier_phase τ (Real.log (qI c.1 / C)) else 0
    let matrix : ℝ → S.SqfExtIdeal → ℂ := fun τ d =>
      ∑ c ∈ cols, z τ c * chiIdealPow D (extOfSqf d).1 (cgen R c) 3
    let rowPhase : ℝ → S.SqfExtIdeal → ℂ := fun τ d =>
      rf_retained_fourier_phase τ (-2 * Real.log (qI d.1 / D0))
    let rowWeight : ℝ → S.SqfExtIdeal → ℂ := fun τ d =>
      frozenRho R υ t sd (extOfSqf d) * rowPhase τ d
    let rowValue : ℝ → S.SqfExtIdeal → ℂ := fun τ d => rowWeight τ d * matrix τ d
    have hLambda (c : S.SqfExtIdeal) : ‖frozenLambda R υ t sc c‖ ≤ 1 :=
      (rf_exterior_factorization R).1 υ h t |>.2.2 sc c
    have hchi (d : S.ExtIdeal) (c : S.SqfExtIdeal) :
        ‖chiIdealPow D d.1 (cgen R c) 3‖ ≤ 1 :=
      (a2_bridge_SYMBOL D S).ideal_norm_le d.1 (cgen R c) 3
    have hcoeffNorm (c : S.SqfExtIdeal) :
        ‖coeff c‖ ≤ qI c.1 ^ (-(1 / 2 : ℝ)) := by
      have hq := rf_qI_pos_ge_one c.1 (by simpa using c.2.1.1)
      have hpow : 0 ≤ qI c.1 ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg hq.1.le _
      have hreal : ‖((qI c.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ =
          qI c.1 ^ (-(1 / 2 : ℝ)) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpow]
      dsimp [coeff]
      rw [norm_mul, hreal]
      calc
        ‖frozenLambda R υ t sc c‖ * qI c.1 ^ (-(1 / 2 : ℝ)) ≤
            1 * qI c.1 ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (hLambda c) hpow
        _ = qI c.1 ^ (-(1 / 2 : ℝ)) := by ring
    have hcoeffCut (c : S.SqfExtIdeal) (hc : c ∈ cols) :
        ‖coeff c‖ ≤ C ^ (-(1 / 2 : ℝ)) := by
      have hc' := (hmemCols c).mp hc
      have hqC := rf_qI_pos_ge_one c.1 (by simpa using c.2.1.1)
      exact (hcoeffNorm c).trans
        (Real.rpow_le_rpow_of_nonpos hCpos hc'.1 (by norm_num))
    have hpowCutSq : (C ^ (-(1 / 2 : ℝ))) ^ 2 = C⁻¹ := by
      calc
        (C ^ (-(1 / 2 : ℝ))) ^ 2 = C ^ ((-(1 / 2 : ℝ)) * 2) :=
          (Real.rpow_mul_natCast hCpos.le _ 2).symm
        _ = C ^ (-1 : ℝ) := by congr 1 <;> norm_num
        _ = C⁻¹ := Real.rpow_neg_one C
    have hzNormSq (τ : ℝ) (c : S.SqfExtIdeal) (hc : c ∈ cols) :
        ‖z τ c‖ ^ 2 ≤ C⁻¹ := by
      by_cases hk : keep c
      · have hnorm : ‖z τ c‖ ≤ C ^ (-(1 / 2 : ℝ)) := by
          simpa [z, hk, rf_retained_fourier_phase_norm] using hcoeffCut c hc
        have hpowNonneg : 0 ≤ C ^ (-(1 / 2 : ℝ)) := by positivity
        have hsq := (sq_le_sq₀ (norm_nonneg _) hpowNonneg).2 hnorm
        rwa [hpowCutSq] at hsq
      · simp [z, hk]
        positivity
    have hzMass (τ : ℝ) : ∑ c ∈ cols, ‖z τ c‖ ^ 2 ≤ 2 * Ccnt := by
      calc
        _ ≤ ∑ c ∈ cols, C⁻¹ := by
          apply Finset.sum_le_sum
          intro c hc
          exact hzNormSq τ c hc
        _ = (cols.card : ℝ) * C⁻¹ := by simp
        _ ≤ (Ccnt * (2 * C)) * C⁻¹ :=
          mul_le_mul_of_nonneg_right hcolCard (by positivity)
        _ = 2 * Ccnt := by
          rw [inv_eq_one_div]
          field_simp [ne_of_gt hCpos]
          <;> ring
    have hRowsNorm (d : S.SqfExtIdeal) (hd : d ∈ rows) :
        idealNorm d.1 ≤ 2 * D0 := by
      have hd' := (hmemRows d).mp hd
      simpa [rowPred, idealNorm, qI] using hd'.2.le
    have hColsNorm (c : S.SqfExtIdeal) (hc : c ∈ cols) :
        idealNorm c.1 ≤ 2 * C ∧
          ∃ g : Fˣ, (g : F) = cgen R c ∧ S.IsGen (g : F) c.1 ∧ Bd.Allowed g := by
      have hc' := (hmemCols c).mp hc
      refine ⟨?_, cgen_valid R c⟩
      simpa [idealNorm, qI] using hc'.2.le
    let B : ℝ := Csieve * (2 * C + 2 * D0) * (4 * C * D0) ^ ε * (2 * Ccnt)
    have hBpos : 0 < B := by dsimp [B]; positivity
    have hSieveAt (τ : ℝ) : ∑ d ∈ rows, ‖matrix τ d‖ ^ 2 ≤ B := by
      have hraw := hSieve (2 * C) (2 * D0) (by linarith) (by linarith)
        rows cols (cgen R) hRowsNorm hColsNorm (z τ)
      calc
        _ ≤ Csieve * (2 * C + 2 * D0) * (4 * C * D0) ^ ε *
              ∑ c ∈ cols, ‖z τ c‖ ^ 2 := by
          have harg : (2 * C) * (2 * D0) = 4 * C * D0 := by ring
          simpa [harg] using hraw
        _ ≤ B := by
          dsimp [B]
          have hfac : 0 ≤ Csieve * (2 * C + 2 * D0) * (4 * C * D0) ^ ε := by positivity
          exact mul_le_mul_of_nonneg_left (hzMass τ) hfac
    let Rows : Type := {d : S.SqfExtIdeal // d ∈ rows}
    letI : Fintype Rows := (rows.finite_toSet).fintype
    have hsumRows (f : S.SqfExtIdeal → ℝ) :
        (∑ d : Rows, f d.1) = ∑ d ∈ rows, f d := by
      change (∑ d ∈ (Finset.univ : Finset Rows), f d.1) = _
      refine Finset.sum_bij (fun d _ => d.1) ?_ ?_ ?_ ?_
      · intro d hd
        exact d.2
      · intro d hd e he hde
        exact Subtype.ext hde
      · intro d hd
        exact ⟨⟨d, hd⟩, by simp, rfl⟩
      · intro d hd
        rfl
    let κ : S.V := kappaSix R t sd sc
    have hFourierData := hFT υ κ v hv
    have hSepL1 : ∫ τ : ℝ, ‖separatedFourier R ρ υ κ v τ‖ ≤
        CFT * min (v ^ α) (v ^ (-N)) := hFourierData.2
    have hSepComplexInt : Integrable (fun τ : ℝ => separatedFourier R ρ υ κ v τ) :=
      (rf_retained_fourier_inversion R ρ hρ hρc υ κ v hv 0).1
    have hRhoNorm (d : S.SqfExtIdeal) :
        ‖frozenRho R υ t sd (extOfSqf d)‖ ≤ 1 :=
      (rf_exterior_factorization R).1 υ h t |>.2.1 sd (extOfSqf d)
    have hrowWeightNorm (τ : ℝ) (d : S.SqfExtIdeal) :
        ‖rowWeight τ d‖ ≤ 1 := by
      change ‖frozenRho R υ t sd (extOfSqf d) *
        rf_retained_fourier_phase τ (-2 * Real.log (qI d.1 / D0))‖ ≤ 1
      calc
        _ = ‖frozenRho R υ t sd (extOfSqf d)‖ *
            ‖rf_retained_fourier_phase τ (-2 * Real.log (qI d.1 / D0))‖ := by rw [norm_mul]
        _ = ‖frozenRho R υ t sd (extOfSqf d)‖ := by
          rw [rf_retained_fourier_phase_norm, mul_one]
        _ ≤ 1 := hRhoNorm d
    let coefMass : ℝ := ∑ c ∈ cols, ‖coeff c‖
    have hcoefMassNonneg : 0 ≤ coefMass := by
      dsimp [coefMass]
      apply Finset.sum_nonneg
      intro c hc
      exact norm_nonneg _
    have hzCoeff (τ : ℝ) (c : S.SqfExtIdeal) (hc : c ∈ cols) :
        ‖z τ c‖ ≤ ‖coeff c‖ := by
      by_cases hk : keep c
      · simpa [z, hk, rf_retained_fourier_phase_norm] using (le_of_eq rfl : ‖coeff c‖ ≤ ‖coeff c‖)
      · simp [z, hk]
    have hmatrixNorm (τ : ℝ) (d : S.SqfExtIdeal) :
        ‖matrix τ d‖ ≤ coefMass := by
      dsimp [matrix, coefMass]
      calc
        ‖∑ c ∈ cols, z τ c * chiIdealPow D (extOfSqf d).1 (cgen R c) 3‖ ≤
            ∑ c ∈ cols, ‖z τ c * chiIdealPow D (extOfSqf d).1 (cgen R c) 3‖ :=
          norm_sum_le _ _
        _ ≤ ∑ c ∈ cols, ‖coeff c‖ := by
          apply Finset.sum_le_sum
          intro c hc
          rw [norm_mul]
          have hz := hzCoeff τ c hc
          have hχ := hchi (extOfSqf d) c
          calc
            ‖z τ c‖ * ‖chiIdealPow D (extOfSqf d).1 (cgen R c) 3‖ ≤
                ‖coeff c‖ * 1 := mul_le_mul hz hχ (norm_nonneg _) (norm_nonneg _)
            _ = ‖coeff c‖ := by ring
    have hrowValueNorm (τ : ℝ) (d : S.SqfExtIdeal) :
        ‖rowValue τ d‖ ≤ coefMass := by
      change ‖rowWeight τ d * matrix τ d‖ ≤ coefMass
      calc
        _ = ‖rowWeight τ d‖ * ‖matrix τ d‖ := by rw [norm_mul]
        _ ≤ 1 * ‖matrix τ d‖ := mul_le_mul_of_nonneg_right (hrowWeightNorm τ d) (norm_nonneg _)
        _ ≤ coefMass := by simpa using hmatrixNorm τ d
    have hrowValueMatrixNorm (τ : ℝ) (d : S.SqfExtIdeal) :
        ‖rowValue τ d‖ ≤ ‖matrix τ d‖ := by
      change ‖rowWeight τ d * matrix τ d‖ ≤ ‖matrix τ d‖
      calc
        _ = ‖rowWeight τ d‖ * ‖matrix τ d‖ := by rw [norm_mul]
        _ ≤ 1 * ‖matrix τ d‖ := mul_le_mul_of_nonneg_right (hrowWeightNorm τ d) (norm_nonneg _)
        _ = ‖matrix τ d‖ := by ring
    have hrowValueContinuous (d : S.SqfExtIdeal) :
        Continuous (fun τ : ℝ => rowValue τ d) := by
      have hphase : Continuous (fun τ : ℝ => rowPhase τ d) := by
        change Continuous (fun τ : ℝ =>
          rf_retained_fourier_phase τ (-2 * Real.log (qI d.1 / D0)))
        exact rf_retained_fourier_phase_continuous _
      have hzphase (c : S.SqfExtIdeal) : Continuous (fun τ : ℝ => z τ c) := by
        have hphasec : Continuous (fun τ : ℝ =>
            coeff c * rf_retained_fourier_phase τ (Real.log (qI c.1 / C))) :=
          continuous_const.mul (rf_retained_fourier_phase_continuous _)
        by_cases hk : keep c
        · simp only [z, if_pos hk]
          exact hphasec
        · simp only [z, if_neg hk]
          exact continuous_const
      have hmatrix : Continuous (fun τ : ℝ => matrix τ d) := by
        change Continuous (fun τ : ℝ =>
          ∑ c ∈ cols, z τ c * chiIdealPow D (extOfSqf d).1 (cgen R c) 3)
        exact continuous_finsetSum cols (fun c hc => (hzphase c).mul continuous_const)
      change Continuous (fun τ : ℝ =>
        frozenRho R υ t sd (extOfSqf d) * rowPhase τ d * matrix τ d)
      exact (continuous_const.mul hphase).mul hmatrix
    have hrowL2 (τ : ℝ) : ∑ d ∈ rows, ‖rowValue τ d‖ ^ 2 ≤ B := by
      calc
        ∑ d ∈ rows, ‖rowValue τ d‖ ^ 2 ≤ ∑ d ∈ rows, ‖matrix τ d‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro d hd
          exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hrowValueMatrixNorm τ d)
        _ ≤ B := hSieveAt τ
    let V : ℝ → PiLp 2 (fun _ : Rows => ℂ) := fun τ =>
      WithLp.toLp 2 (fun d : Rows => separatedFourier R ρ υ κ v τ * rowValue τ d.1)
    have hcoordIntegrable (d : Rows) :
        Integrable (fun τ : ℝ => separatedFourier R ρ υ κ v τ * rowValue τ d.1) := by
      exact hSepComplexInt.mul_bdd (hrowValueContinuous d.1).aestronglyMeasurable
        (Filter.Eventually.of_forall fun τ => hrowValueNorm τ d.1)
    have hVIntegrable : Integrable V := by
      rw [MeasureTheory.integrable_piLp_iff]
      intro d
      exact hcoordIntegrable d
    have hVNormBound (τ : ℝ) :
        ‖V τ‖ ≤ ‖separatedFourier R ρ υ κ v τ‖ * Real.sqrt B := by
      let W : PiLp 2 (fun _ : Rows => ℂ) :=
        WithLp.toLp 2 (fun d : Rows => rowValue τ d.1)
      have hWsq : ‖W‖ ^ 2 ≤ B := by
        calc
          ‖W‖ ^ 2 = ∑ d : Rows, ‖rowValue τ d.1‖ ^ 2 := by
            rw [PiLp.norm_sq_eq_of_L2]
          _ = ∑ d ∈ rows, ‖rowValue τ d‖ ^ 2 := hsumRows (fun d => ‖rowValue τ d‖ ^ 2)
          _ ≤ B := hrowL2 τ
      have hWnorm : ‖W‖ ≤ Real.sqrt B := by
        have h := Real.sqrt_le_sqrt hWsq
        have hnorm : Real.sqrt (‖W‖ ^ 2) = ‖W‖ := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
        simpa [hnorm] using h
      have hVeq : V τ = separatedFourier R ρ υ κ v τ • W := by
        ext d
        simp [V, W]
      rw [hVeq, norm_smul]
      exact mul_le_mul_of_nonneg_left hWnorm (norm_nonneg _)
    have htermMultiplierContinuous (d c : S.SqfExtIdeal) :
        Continuous (fun τ : ℝ => rowPhase τ d * z τ c * chiIdealPow D
          (extOfSqf d).1 (cgen R c) 3) := by
      have hrowphase : Continuous (fun τ : ℝ => rowPhase τ d) := by
        change Continuous (fun τ : ℝ => rf_retained_fourier_phase τ
          (-2 * Real.log (qI d.1 / D0)))
        exact rf_retained_fourier_phase_continuous _
      have hzphase : Continuous (fun τ : ℝ => z τ c) := by
        have hphasec : Continuous (fun τ : ℝ =>
            coeff c * rf_retained_fourier_phase τ (Real.log (qI c.1 / C))) :=
          continuous_const.mul (rf_retained_fourier_phase_continuous _)
        by_cases hk : keep c
        · simp only [z, if_pos hk]
          exact hphasec
        · simp only [z, if_neg hk]
          exact continuous_const
      exact (hrowphase.mul hzphase).mul continuous_const
    have htermMultiplierBound (d c : S.SqfExtIdeal) (τ : ℝ) :
        ‖rowPhase τ d * z τ c * chiIdealPow D (extOfSqf d).1 (cgen R c) 3‖ ≤
          ‖coeff c‖ + 1 := by
      by_cases hk : keep c
      · have hz : ‖z τ c‖ = ‖coeff c‖ := by
          simp [z, hk, rf_retained_fourier_phase_norm]
        calc
          ‖rowPhase τ d * z τ c * chiIdealPow D (extOfSqf d).1 (cgen R c) 3‖ =
              ‖coeff c‖ * ‖chiIdealPow D (extOfSqf d).1 (cgen R c) 3‖ := by
            simp [norm_mul, rowPhase, hz, rf_retained_fourier_phase_norm]
          _ ≤ ‖coeff c‖ * 1 :=
            mul_le_mul_of_nonneg_left (hchi (extOfSqf d) c) (norm_nonneg (coeff c))
          _ = ‖coeff c‖ := by ring
          _ ≤ ‖coeff c‖ + 1 := by linarith
      · simp [z, hk]
        positivity
    have htermIntegrable (d c : S.SqfExtIdeal) :
        Integrable (fun τ : ℝ => separatedFourier R ρ υ κ v τ * rowPhase τ d * z τ c *
          chiIdealPow D (extOfSqf d).1 (cgen R c) 3) := by
      have hi := hSepComplexInt.mul_bdd (htermMultiplierContinuous d c).aestronglyMeasurable
        (Filter.Eventually.of_forall (htermMultiplierBound d c))
      simpa only [mul_assoc] using hi
    have hretainedIntegral (d : Rows) :
        retainedColumn R υ t sd sc (extOfSqf d.1) C Z R0 =
          ∫ τ : ℝ, separatedFourier R ρ υ κ v τ * rowValue τ d.1 := by
      let d0 : S.SqfExtIdeal := d.1
      have hdrow := (hmemRows d0).mp d.2
      have hqd := rf_qI_pos_ge_one d0.1 (by simpa using d0.2.1.1)
      let x : S.SqfExtIdeal → ℝ := fun c =>
        Real.log (qI c.1 / C) - 2 * Real.log (qI d0.1 / D0)
      have hcRange (c : S.SqfExtIdeal) (hc : c ∈ cols) :
          C ≤ qI c.1 ∧ qI c.1 < 2 * C := (hmemCols c).mp hc
      have hdRange : D0 ≤ qI d0.1 ∧ qI d0.1 < 2 * D0 := by
        simpa [rowPred, extOfSqf, qI, rowDyad] using hdrow
      have hqcRatioPos (c : S.SqfExtIdeal) (hc : c ∈ cols) : 0 < qI c.1 / C :=
        div_pos (rf_qI_pos_ge_one c.1 (by simpa using c.2.1.1)).1 hCpos
      have hqdRatioPos : 0 < qI d0.1 / D0 := div_pos hqd.1 hDpos
      have hqCRatio (c : S.SqfExtIdeal) (hc : c ∈ cols) :
          1 ≤ qI c.1 / C ∧ qI c.1 / C ≤ 2 := by
        have hcr := hcRange c hc
        constructor
        · apply (le_div_iff₀ hCpos).2
          simpa using hcr.1
        · apply (div_le_iff₀ hCpos).2
          exact le_of_lt (by nlinarith [hcr.2])
      have hqdRatio : 1 ≤ qI d0.1 / D0 ∧ qI d0.1 / D0 ≤ 2 := by
        constructor
        · apply (le_div_iff₀ hDpos).2
          simpa using hdRange.1
        · apply (div_le_iff₀ hDpos).2
          exact le_of_lt (by nlinarith [hdRange.2])
      have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlog2le : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have hlogC (c : S.SqfExtIdeal) (hc : c ∈ cols) :
          0 ≤ Real.log (qI c.1 / C) ∧ Real.log (qI c.1 / C) ≤ Real.log 2 := by
        refine ⟨Real.log_nonneg (hqCRatio c hc).1, ?_⟩
        exact Real.log_le_log (hqcRatioPos c hc) (hqCRatio c hc).2
      have hlogD : 0 ≤ Real.log (qI d0.1 / D0) ∧
          Real.log (qI d0.1 / D0) ≤ Real.log 2 := by
        refine ⟨Real.log_nonneg hqdRatio.1, ?_⟩
        exact Real.log_le_log hqdRatioPos hqdRatio.2
      have hxabs (c : S.SqfExtIdeal) (hc : c ∈ cols) : |x c| ≤ 2 := by
        change |Real.log (qI c.1 / C) - 2 * Real.log (qI d0.1 / D0)| ≤ 2
        rw [abs_le]
        constructor <;> linarith [hlogC c hc, hlogD, hlog2le]
      have hexpD : Real.exp (2 * Real.log (qI d0.1 / D0)) =
          (qI d0.1 / D0) ^ 2 := by
        calc
          Real.exp (2 * Real.log (qI d0.1 / D0)) =
              Real.exp (Real.log (qI d0.1 / D0) + Real.log (qI d0.1 / D0)) := by
                congr 1 <;> ring
          _ = Real.exp (Real.log (qI d0.1 / D0)) *
                Real.exp (Real.log (qI d0.1 / D0)) := Real.exp_add _ _
          _ = (qI d0.1 / D0) ^ 2 := by rw [Real.exp_log hqdRatioPos]; ring
      have hexpX (c : S.SqfExtIdeal) (hc : c ∈ cols) :
          Real.exp (x c) = (qI c.1 / C) / (qI d0.1 / D0) ^ 2 := by
        change Real.exp (Real.log (qI c.1 / C) - 2 * Real.log (qI d0.1 / D0)) = _
        rw [Real.exp_sub, Real.exp_log (hqcRatioPos c hc), hexpD]
      have hargEq (c : S.SqfExtIdeal) (hc : c ∈ cols) :
          v * Real.exp (x c) =
            Z * qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 /
              (qI d0.1 ^ 2 * qI t.f.1 ^ 2) := by
        dsimp [v]
        rw [hexpX c hc]
        field_simp [ne_of_gt hCpos, ne_of_gt hDpos, ne_of_gt hqd.1, ne_of_gt hqF.1]
        <;> ring
      have hphaseSplit (c : S.SqfExtIdeal) (hc : c ∈ cols) (τ : ℝ) :
          rf_retained_fourier_phase τ (x c) =
            rf_retained_fourier_phase τ (Real.log (qI c.1 / C)) *
              rf_retained_fourier_phase τ (-2 * Real.log (qI d0.1 / D0)) := by
        change rf_retained_fourier_phase τ
            (Real.log (qI c.1 / C) - 2 * Real.log (qI d0.1 / D0)) = _
        calc
          _ = rf_retained_fourier_phase τ (Real.log (qI c.1 / C)) *
                rf_retained_fourier_phase τ (-(2 * Real.log (qI d0.1 / D0))) :=
            rf_retained_fourier_phase_sub τ _ _
          _ = _ := by
            rw [show -(2 * Real.log (qI d0.1 / D0)) =
              -2 * Real.log (qI d0.1 / D0) by ring]
      have hTsum :
          (∑' c : S.SqfExtIdeal,
            if C ≤ qI c.1 ∧ qI c.1 < 2 * C ∧ keep c then
              coeff c * chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 *
                profilePhi R υ κ
                  (Z * qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 /
                    (qI d0.1 ^ 2 * qI t.f.1 ^ 2))
            else 0) =
            ∑ c ∈ cols, if keep c then
              coeff c * chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 *
                profilePhi R υ κ
                  (Z * qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 /
                    (qI d0.1 ^ 2 * qI t.f.1 ^ 2))
              else 0 := by
        calc
          _ = ∑ c ∈ cols,
                if C ≤ qI c.1 ∧ qI c.1 < 2 * C ∧ keep c then
                  coeff c * chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 *
                    profilePhi R υ κ
                      (Z * qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 /
                        (qI d0.1 ^ 2 * qI t.f.1 ^ 2))
                else 0 := by
            apply tsum_eq_sum
            intro c hc
            have hnot : ¬ (C ≤ qI c.1 ∧ qI c.1 < 2 * C) := by
              intro hdyad
              exact hc ((hmemCols c).2 hdyad)
            have hfalse : ¬ (C ≤ qI c.1 ∧ qI c.1 < 2 * C ∧ keep c) := by
              intro h
              exact hnot ⟨h.1, h.2.1⟩
            simp [hfalse]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro c hc
            have hc' := (hmemCols c).mp hc
            rcases hc' with ⟨hc₁, hc₂⟩
            by_cases hk : keep c
            · have hleft : C ≤ qI c.1 ∧ qI c.1 < 2 * C ∧ keep c := ⟨hc₁, hc₂, hk⟩
              simp [hleft, hk]
            · have hleft : ¬ (C ≤ qI c.1 ∧ qI c.1 < 2 * C ∧ keep c) := by
                intro h
                exact hk h.2.2
              simp [hleft, hk]
      have hterm (c : S.SqfExtIdeal) (hc : c ∈ cols) :
          (if keep c then
            coeff c * chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 *
              profilePhi R υ κ
                (Z * qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 /
                  (qI d0.1 ^ 2 * qI t.f.1 ^ 2))
          else 0) =
            ∫ τ : ℝ, separatedFourier R ρ υ κ v τ * rowPhase τ d0 * z τ c *
              chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 := by
        by_cases hk : keep c
        · rw [if_pos hk]
          have hFourierInv :=
            (rf_retained_fourier_inversion R ρ hρ hρc υ κ v hv (x c)).2
          have hprofileInv : profilePhi R υ κ
              (Z * qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 /
                (qI d0.1 ^ 2 * qI t.f.1 ^ 2)) =
                ∫ τ : ℝ, separatedFourier R ρ υ κ v τ *
                  rf_retained_fourier_phase τ (x c) := by
            calc
              _ = profilePhi R υ κ (v * Real.exp (x c)) := by rw [← hargEq c hc]
              _ = ρ (x c) * profilePhi R υ κ (v * Real.exp (x c)) := by
                rw [show ρ (x c) = 1 by simpa [ρ] using rf_retained_log_cutoff_one (hxabs c hc)]
                simp
              _ = _ := hFourierInv
          calc
            _ = coeff c * chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 *
                  (∫ τ : ℝ, separatedFourier R ρ υ κ v τ *
                    rf_retained_fourier_phase τ (x c)) := by rw [hprofileInv]
            _ = ∫ τ : ℝ, coeff c * chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 *
                  (separatedFourier R ρ υ κ v τ * rf_retained_fourier_phase τ (x c)) :=
                by rw [integral_const_mul]
            _ = ∫ τ : ℝ, separatedFourier R ρ υ κ v τ * rowPhase τ d0 * z τ c *
                  chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 := by
                apply integral_congr_ae
                filter_upwards [] with τ
                simp [z, hk]
                rw [hphaseSplit c hc τ]
                ring
        · simp [hk, z]
      have hsumTermInt : ∀ c ∈ cols,
          Integrable (fun τ : ℝ => separatedFourier R ρ υ κ v τ * rowPhase τ d0 * z τ c *
            chiIdealPow D (extOfSqf d0).1 (cgen R c) 3) := by
        intro c hc
        exact htermIntegrable d0 c
      have hsumFourier :
          ∫ τ : ℝ, ∑ c ∈ cols, separatedFourier R ρ υ κ v τ * rowPhase τ d0 * z τ c *
            chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 =
          ∑ c ∈ cols, ∫ τ : ℝ, separatedFourier R ρ υ κ v τ * rowPhase τ d0 * z τ c *
            chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 :=
        integral_finsetSum cols (f := fun c τ => separatedFourier R ρ υ κ v τ * rowPhase τ d0 *
          z τ c * chiIdealPow D (extOfSqf d0).1 (cgen R c) 3) hsumTermInt
      calc
        retainedColumn R υ t sd sc (extOfSqf d0) C Z R0 =
            frozenRho R υ t sd (extOfSqf d0) *
              ∑ c ∈ cols, if keep c then
                coeff c * chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 *
                  profilePhi R υ κ
                    (Z * qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 /
                      (qI d0.1 ^ 2 * qI t.f.1 ^ 2))
              else 0 := by
          rw [retainedColumn, hTsum]
        _ = frozenRho R υ t sd (extOfSqf d0) *
              ∑ c ∈ cols, ∫ τ : ℝ,
                separatedFourier R ρ υ κ v τ * rowPhase τ d0 * z τ c *
                  chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 := by
          congr 1
          apply Finset.sum_congr rfl
          intro c hc
          exact hterm c hc
        _ = frozenRho R υ t sd (extOfSqf d0) *
              ∫ τ : ℝ, ∑ c ∈ cols,
                separatedFourier R ρ υ κ v τ * rowPhase τ d0 * z τ c *
                  chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 := by
          rw [← hsumFourier]
        _ = ∫ τ : ℝ, frozenRho R υ t sd (extOfSqf d0) *
              ∑ c ∈ cols,
                separatedFourier R ρ υ κ v τ * rowPhase τ d0 * z τ c *
                  chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 := by
          rw [integral_const_mul]
        _ = ∫ τ : ℝ, separatedFourier R ρ υ κ v τ * rowValue τ d0 := by
          apply integral_congr_ae
          filter_upwards [] with τ
          change frozenRho R υ t sd (extOfSqf d0) *
              ∑ c ∈ cols,
                separatedFourier R ρ υ κ v τ * rowPhase τ d0 * z τ c *
                  chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 =
            separatedFourier R ρ υ κ v τ *
              (frozenRho R υ t sd (extOfSqf d0) * rowPhase τ d0 *
                ∑ c ∈ cols, z τ c * chiIdealPow D (extOfSqf d0).1 (cgen R c) 3)
          rw [Finset.mul_sum]
          calc
            ∑ c ∈ cols, frozenRho R υ t sd (extOfSqf d0) *
                (separatedFourier R ρ υ κ v τ * rowPhase τ d0 * z τ c *
                  chiIdealPow D (extOfSqf d0).1 (cgen R c) 3) =
              ∑ c ∈ cols, (separatedFourier R ρ υ κ v τ *
                  (frozenRho R υ t sd (extOfSqf d0) * rowPhase τ d0)) *
                  (z τ c * chiIdealPow D (extOfSqf d0).1 (cgen R c) 3) := by
                apply Finset.sum_congr rfl
                intro c hc
                ring
        _ = (separatedFourier R ρ υ κ v τ *
                  (frozenRho R υ t sd (extOfSqf d0) * rowPhase τ d0)) *
                  ∑ c ∈ cols, z τ c * chiIdealPow D (extOfSqf d0).1 (cgen R c) 3 := by
                rw [← Finset.mul_sum]
            _ = _ := by ring
    let rowsD : Finset S.ExtIdeal := rows.image extOfSqf
    let massTerm : S.ExtIdeal → ℝ := fun d =>
      if rowDyad d then ‖retainedColumn R υ t sd sc d C Z R0‖ ^ 2 else 0
    have hzeroRow (d : S.ExtIdeal) (hd : d ∉ rowsD) : massTerm d = 0 := by
      by_cases hdyad : rowDyad d
      · by_cases hsqf : Squarefree d.1
        · let c : S.SqfExtIdeal := ⟨d.1, ⟨d.2, hsqf⟩⟩
          have hext : extOfSqf c = d := by
            apply Subtype.ext
            rfl
          have hcRows : c ∈ rows := by
            apply (hmemRows c).2
            simpa [rowPred, extOfSqf] using hdyad
          have hdRows : d ∈ rowsD := Finset.mem_image.mpr ⟨c, hcRows, hext⟩
          exact (hd hdRows).elim
        · have hrhoZero : frozenRho R υ t sd d = 0 := by
            simp [frozenRho, hsqf]
          have hcolumnZero : retainedColumn R υ t sd sc d C Z R0 = 0 := by
            simp [retainedColumn, hrhoZero]
          simp [massTerm, hdyad, hcolumnZero]
      · simp [massTerm, hdyad]
    have houterSum :
        (∑' d : S.ExtIdeal, massTerm d) = ∑ d ∈ rowsD, massTerm d :=
      tsum_eq_sum hzeroRow
    have hsumImage (f : S.ExtIdeal → ℝ) :
        ∑ d ∈ rowsD, f d = ∑ d ∈ rows, f (extOfSqf d) := by
      dsimp [rowsD]
      exact Finset.sum_image (fun d hd e he hde => hextOfSqfInj hde)
    have houterFinite :
        ∑ d ∈ rowsD, massTerm d =
          ∑ d ∈ rows, ‖retainedColumn R υ t sd sc (extOfSqf d) C Z R0‖ ^ 2 := by
      rw [hsumImage]
      apply Finset.sum_congr rfl
      intro d hd
      have hdyad : rowDyad (extOfSqf d) := by
        simpa [rowPred] using (hmemRows d).mp hd
      simp [massTerm, hdyad]
    let retVec : PiLp 2 (fun _ : Rows => ℂ) :=
      WithLp.toLp 2 (fun d : Rows => retainedColumn R υ t sd sc (extOfSqf d.1) C Z R0)
    have houterSubtype :
        (∑ d : Rows, ‖retainedColumn R υ t sd sc (extOfSqf d.1) C Z R0‖ ^ 2) =
          ∑ d ∈ rows, ‖retainedColumn R υ t sd sc (extOfSqf d) C Z R0‖ ^ 2 := by
      exact hsumRows (fun d => ‖retainedColumn R υ t sd sc (extOfSqf d) C Z R0‖ ^ 2)
    have hrootEq :
        Real.sqrt (∑' d : S.ExtIdeal, massTerm d) = ‖retVec‖ := by
      calc
        Real.sqrt (∑' d : S.ExtIdeal, massTerm d) =
            Real.sqrt (∑ d : Rows,
              ‖retainedColumn R υ t sd sc (extOfSqf d.1) C Z R0‖ ^ 2) := by
                congr 1
                rw [houterSum, houterFinite, ← houterSubtype]
        _ = ‖retVec‖ := by
          symm
          rw [PiLp.norm_eq_of_L2]
    have hvectorEq : (∫ τ : ℝ, V τ) = retVec := by
      ext d
      rw [MeasureTheory.eval_integral_piLp hcoordIntegrable d]
      exact (hretainedIntegral d).symm
    have hnormVector : ‖∫ τ : ℝ, V τ‖ ≤ Real.sqrt B *
        ∫ τ : ℝ, ‖separatedFourier R ρ υ κ v τ‖ := by
      calc
        ‖∫ τ : ℝ, V τ‖ ≤ ∫ τ : ℝ, ‖V τ‖ := norm_integral_le_integral_norm V
        _ ≤ ∫ τ : ℝ, ‖separatedFourier R ρ υ κ v τ‖ * Real.sqrt B :=
          integral_mono_ae hVIntegrable.norm (hFourierData.1.mul_const (Real.sqrt B))
            (Filter.Eventually.of_forall hVNormBound)
        _ = Real.sqrt B * ∫ τ : ℝ, ‖separatedFourier R ρ υ κ v τ‖ := by
          rw [integral_mul_const]
          ring
    have hBroot : Real.sqrt B =
        Real.sqrt (4 * Ccnt * Csieve) * 4 ^ (ε / 2) *
          (D0 + C) ^ (1 / 2 : ℝ) * (D0 * C) ^ (ε / 2) := by
      let K₀ : ℝ := Real.sqrt (4 * Ccnt * Csieve) * 4 ^ (ε / 2)
      have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
      have hBnonneg : 0 ≤ B := le_of_lt hBpos
      have hBsq : B =
          (K₀ * (D0 + C) ^ (1 / 2 : ℝ) * (D0 * C) ^ (ε / 2)) ^ 2 := by
        dsimp [B, K₀]
        have hArg : 4 * C * D0 = 4 * (C * D0) := by ring
        rw [hArg, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
        have hpow4 : (4 ^ (ε / 2)) ^ 2 = (4 : ℝ) ^ ε := by
          calc
            (4 ^ (ε / 2)) ^ 2 = 4 ^ ((ε / 2) * 2) :=
              (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 4) _ 2).symm
            _ = 4 ^ ε := by congr 1 <;> ring
        have hpowSum : ((D0 + C) ^ (1 / 2 : ℝ)) ^ 2 = D0 + C := by
          calc
            ((D0 + C) ^ (1 / 2 : ℝ)) ^ 2 = (D0 + C) ^ ((1 / 2 : ℝ) * 2) :=
              (Real.rpow_mul_natCast (by positivity) _ 2).symm
            _ = D0 + C := by norm_num
        have hpowDC : ((D0 * C) ^ (ε / 2)) ^ 2 = (D0 * C) ^ ε := by
          calc
            ((D0 * C) ^ (ε / 2)) ^ 2 = (D0 * C) ^ ((ε / 2) * 2) :=
              (Real.rpow_mul_natCast (by positivity) _ 2).symm
            _ = (D0 * C) ^ ε := by congr 1 <;> ring
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hpow4, hpowSum, hpowDC]
        ring
      apply (Real.sqrt_eq_iff_eq_sq hBnonneg (by positivity)).2
      exact hBsq
    calc
      Real.sqrt (∑' d : S.ExtIdeal,
          if rowDyad d then ‖retainedColumn R υ t sd sc d C Z R0‖ ^ 2 else 0) = ‖retVec‖ := by
        apply hrootEq
      _ = ‖∫ τ : ℝ, V τ‖ := by rw [hvectorEq]
      _ ≤ Real.sqrt B * ∫ τ : ℝ, ‖separatedFourier R ρ υ κ v τ‖ := hnormVector
      _ ≤ Real.sqrt B * (CFT * min (v ^ α) (v ^ (-N))) :=
        mul_le_mul_of_nonneg_left hSepL1 (Real.sqrt_nonneg B)
      _ = CFT * Real.sqrt (4 * Ccnt * Csieve) * 4 ^ (ε / 2) *
            (D0 + C) ^ (1 / 2 : ℝ) * (D0 * C) ^ (ε / 2) * min (v ^ α) (v ^ (-N)) := by
        rw [hBroot]
        ring

private lemma rf_retained_sqf_norm_cut_finite (X : ℝ) (hX : 0 ≤ X) :
    {c : S.SqfExtIdeal | qI c.1 ≤ X}.Finite := by
  classical
  let extOfSqf : S.SqfExtIdeal → S.ExtIdeal := fun c => ⟨c.1, c.2.1⟩
  have hinj : Function.Injective extOfSqf := by
    intro c c' he
    apply Subtype.ext
    have h := congrArg (fun I : S.ExtIdeal => I.1) he
    exact h
  have hcut := a2_bridge_COUNT_finite S X hX
  have hpre : {c : S.SqfExtIdeal | idealNorm (extOfSqf c).1 ≤ X}.Finite :=
    hcut.1.preimage (f := extOfSqf) (fun _ _ _ _ he => hinj he)
  simpa [extOfSqf, idealNorm, qI] using hpre

private lemma rf_retained_frozen_cut_finite (h : S.ExtIdeal) (hh : IsPowerful h.1)
    (X : ℝ) (hX : 0 ≤ X) :
    {t : FrozenIndex R h | qI t.a.1 ≤ X ∧ qI t.n.1 ≤ X}.Finite := by
  classical
  let F0 : Type := {f : S.ExtIdeal // Squarefree f.1 ∧
    ∀ v ∈ R.exterior.support f, v ∈ R.exterior.support h}
  letI : Finite F0 := rf_squarefree_support_finite R h hh
  letI : Fintype F0 := Fintype.ofFinite F0
  let Active : Type := {f : F0 // activeFactor R h f.1}
  letI : Fintype Active := Subtype.fintype (fun f : F0 => activeFactor R h f.1)
  let Aset : Finset S.ExtIdeal := bridgeNormFinset S X
  let Nset : Finset S.ExtIdeal := bridgeNormFinset S X
  let hcut := a2_bridge_COUNT_finite S X hX
  let Aidx : Type := {a : S.ExtIdeal // a ∈ Aset}
  let Nidx : Type := {n : S.ExtIdeal // n ∈ Nset}
  letI : Fintype Aidx := Aset.finite_toSet.fintype
  letI : Fintype Nidx := Nset.finite_toSet.fintype
  letI : Fintype (UnitSix S) := R.sheets.unitSixFinite
  let Tcut : Type := {t : FrozenIndex R h // qI t.a.1 ≤ X ∧ qI t.n.1 ≤ X}
  let toIndex (t : Tcut) : Active × UnitSix S × Aidx × Nidx :=
    (⟨⟨t.1.f, ⟨t.1.active.1, t.1.active.2.1⟩⟩, t.1.active⟩,
      t.1.u,
      ⟨t.1.a, (hcut.2 t.1.a).2 (by simpa [qI, idealNorm] using t.2.1)⟩,
      ⟨t.1.n, (hcut.2 t.1.n).2 (by simpa [qI, idealNorm] using t.2.2)⟩)
  apply Finite.of_injective toIndex
  intro x y hxy
  rcases x with ⟨tx, hx⟩
  rcases y with ⟨ty, hy⟩
  apply Subtype.ext
  have hf : tx.f = ty.f := by
    have h := congrArg Prod.fst hxy
    exact congrArg (fun z : Active => z.1.1) h
  have hu : tx.u = ty.u := by
    exact congrArg Prod.fst (congrArg Prod.snd hxy)
  have ha : tx.a = ty.a := by
    have h := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd hxy))
    exact congrArg Subtype.val h
  have hn : tx.n = ty.n := by
    have h := congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd hxy))
    exact congrArg Subtype.val h
  cases tx with
  | mk fx ax nx ux factx numx copx =>
    cases ty with
    | mk fy ay ny uy facty numy copy =>
      have hfx : fx = fy := by simpa using hf
      subst fy
      have hax : ax = ay := by simpa using ha
      subst ay
      have hnx : nx = ny := by simpa using hn
      subst ny
      have hux : ux = uy := by simpa using hu
      subst uy
      rfl

private lemma rf_retained_c_dyad_decomp (qa qn R0 : ℝ)
    (hqa : 1 ≤ qa) (hqn : 1 ≤ qn) (hR0 : 0 ≤ R0)
    (g : S.SqfExtIdeal → ℂ) :
    (∑' c : S.SqfExtIdeal,
      if qa * qI c.1 * qn ^ 3 ≤ R0 then g c else 0) =
      ∑ k ∈ Finset.range (Nat.log 2 ⌊R0⌋₊ + 1),
        ∑' c : S.SqfExtIdeal,
          if ((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧ qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) ∧
              qa * qI c.1 * qn ^ 3 ≤ R0 then g c else 0 := by
  classical
  have hCfinite := rf_retained_sqf_norm_cut_finite (S := S) R0 hR0
  let Cset : Finset S.SqfExtIdeal := hCfinite.toFinset
  have hCmem (c : S.SqfExtIdeal) : c ∈ Cset ↔ qI c.1 ≤ R0 := by
    exact Set.Finite.mem_toFinset hCfinite
  let dyad (c : S.SqfExtIdeal) : ℕ := Nat.log 2 (Ideal.absNorm c.1)
  let N : ℕ := Nat.log 2 ⌊R0⌋₊
  let G (c : S.SqfExtIdeal) : ℂ :=
    if qa * qI c.1 * qn ^ 3 ≤ R0 then g c else 0
  have hzero (c : S.SqfExtIdeal) (hc : c ∉ Cset) : G c = 0 := by
    by_cases hQ : qa * qI c.1 * qn ^ 3 ≤ R0
    · have hqc : qI c.1 ≤ R0 :=
        (rf_retained_cutoff_components qa (qI c.1) qn R0 hqa
          (rf_retained_qI_ge_one c.1 (by simpa using c.2.1.1)) hqn hQ).2.1
      exact (hc ((hCmem c).2 hqc)).elim
    · simp [G, hQ]
  have hmaps : (Cset : Set S.SqfExtIdeal).MapsTo dyad (Finset.range (N + 1)) := by
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_range]
    have hq : qI c.1 ≤ R0 := (hCmem c).1 hc
    have hn : Ideal.absNorm c.1 ≤ ⌊R0⌋₊ := by
      apply (Nat.le_floor_iff hR0).2
      simpa [qI] using hq
    dsimp [N, dyad]
    exact Nat.lt_succ_of_le (Nat.log_mono_right hn)
  have hdecomp :
      (∑ c ∈ Cset, G c) =
        ∑ k ∈ Finset.range (N + 1), ∑ c ∈ Cset with dyad c = k, G c := by
    exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hdyadShell (c : S.SqfExtIdeal) (k : ℕ) :
      (dyad c = k) ↔
        ((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧ qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) := by
    have hI : c.1 ≠ ⊥ := by
      simpa [Ideal.zero_eq_bot] using c.2.1.1
    have hn : Ideal.absNorm c.1 ≠ 0 := by
      exact Nat.ne_of_gt (Ideal.absNorm_pos_of_nonZeroDivisors
        ⟨c.1, mem_nonZeroDivisors_iff_ne_zero.mpr
          (by simpa [Ideal.zero_eq_bot] using hI)⟩)
    constructor
    · intro hk
      have hb := rf_sqf_norm_dyad_bounds (S := S) c
      dsimp [dyad] at hk
      rw [hk] at hb
      constructor
      · simpa [qI] using hb.1
      · calc
          qI c.1 < ((2 ^ (k + 1) : ℕ) : ℝ) := by simpa [qI] using hb.2
          _ = 2 * ((2 ^ k : ℕ) : ℝ) := by
            norm_cast
            rw [pow_succ]
            ring
    · intro hs
      have hs1 : ((2 ^ k : ℕ) : ℝ) ≤ (Ideal.absNorm c.1 : ℝ) := by
        simpa [qI] using hs.1
      have hs2 : (Ideal.absNorm c.1 : ℝ) <
          ((2 ^ k * 2 : ℕ) : ℝ) := by
        simpa [qI, Nat.pow_succ, mul_comm, mul_left_comm, mul_assoc] using hs.2
      have hsNat : 2 ^ k ≤ Ideal.absNorm c.1 ∧
          Ideal.absNorm c.1 < 2 ^ (k + 1) := by
        constructor
        · exact_mod_cast hs1
        · simpa [Nat.pow_succ, mul_comm] using (show
            Ideal.absNorm c.1 < 2 ^ k * 2 by exact_mod_cast hs2)
      simpa [dyad] using
        (Nat.log_eq_iff (Or.inr ⟨by norm_num, hn⟩)).2 hsNat
  calc
    (∑' c : S.SqfExtIdeal, G c) = ∑ c ∈ Cset, G c := tsum_eq_sum hzero
    _ = ∑ k ∈ Finset.range (N + 1), ∑ c ∈ Cset with dyad c = k, G c := hdecomp
    _ = ∑ k ∈ Finset.range (N + 1),
          ∑' c : S.SqfExtIdeal,
            if ((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧ qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) ∧
                qa * qI c.1 * qn ^ 3 ≤ R0 then g c else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hzeroShell (c : S.SqfExtIdeal)
          (hc : c ∉ Cset) :
          (if ((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧
              qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) ∧
              qa * qI c.1 * qn ^ 3 ≤ R0 then g c else 0) = 0 := by
        by_cases hQ : qa * qI c.1 * qn ^ 3 ≤ R0
        · have hqc : qI c.1 ≤ R0 :=
            (rf_retained_cutoff_components qa (qI c.1) qn R0 hqa
              (rf_retained_qI_ge_one c.1 (by simpa using c.2.1.1)) hqn hQ).2.1
          exact (hc ((hCmem c).2 hqc)).elim
        · simp [hQ]
      have hfiber :=
        (tsum_eq_sum hzeroShell :
          (∑' c : S.SqfExtIdeal,
            if ((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧
                qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) ∧
                qa * qI c.1 * qn ^ 3 ≤ R0 then g c else 0) =
          ∑ c ∈ Cset,
            if ((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧
                qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) ∧
                qa * qI c.1 * qn ^ 3 ≤ R0 then g c else 0)
      rw [Finset.sum_filter]
      calc
        (∑ c ∈ Cset, if dyad c = k then G c else 0) =
            ∑ c ∈ Cset,
              if ((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧
                  qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) ∧
                  qa * qI c.1 * qn ^ 3 ≤ R0 then g c else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          by_cases hdyad : dyad c = k
          · have hs := (hdyadShell c k).1 hdyad
            by_cases hQ : qa * qI c.1 * qn ^ 3 ≤ R0
            · have hcond : ((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧
                  qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) ∧
                    qa * qI c.1 * qn ^ 3 ≤ R0 := ⟨hs.1, hs.2, hQ⟩
              rw [if_pos hdyad, if_pos hcond]
              simp [G, hQ]
            · have hnotcond : ¬ (((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧
                  qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) ∧
                    qa * qI c.1 * qn ^ 3 ≤ R0) := by
                intro h
                exact hQ h.2.2
              rw [if_pos hdyad, if_neg hnotcond]
              simp [G, hQ]
          · have hs : ¬ (((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧
                qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ)) := by
              intro hs
              exact hdyad ((hdyadShell c k).2 hs)
            by_cases hQ : qa * qI c.1 * qn ^ 3 ≤ R0
            · have hnotcond : ¬ (((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧
                  qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) ∧
                    qa * qI c.1 * qn ^ 3 ≤ R0) := by
                intro h
                exact hs ⟨h.1, h.2.1⟩
              rw [if_neg hdyad, if_neg hnotcond]
            · rw [if_neg hdyad]
              simp [G, hQ]
        _ = ∑' c : S.SqfExtIdeal,
              if ((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧
                  qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) ∧
                  qa * qI c.1 * qn ^ 3 ≤ R0 then g c else 0 := hfiber.symm

set_option maxHeartbeats 8000000 in
private lemma rf_retained_split_finite_decomp (υ : UnitSix S) (h d : S.ExtIdeal)
    (Z R0 : ℝ) (hR0 : 1 ≤ R0) [Fintype Bd.B]
    (Tset : Finset (FrozenIndex R h)) (Cset : Finset S.SqfExtIdeal)
    (Kset : Finset ℕ)
    (hT : ∀ t, t ∈ Tset ↔ qI t.a.1 ≤ R0 ∧ qI t.n.1 ≤ R0)
    (hC : ∀ c, c ∈ Cset ↔ qI c.1 ≤ R0)
    (hK : Kset = Finset.range (Nat.log 2 ⌊R0⌋₊ + 1)) :
    splitReflection R true υ h d Z R0 =
      ∑ t ∈ Tset, ∑ sd : Bd.B, ∑ sc : Bd.B, ∑ k ∈ Kset,
        if Squarefree d.1 ∧ IsCoprime d.1 h.1 then
          frozenOmega R υ t * ((qI t.n.1)⁻¹ : ℝ) * retainedColumn R υ t sd sc d
            ((2 ^ k : ℕ) : ℝ) Z R0
        else 0 := by
  classical
  letI : Fintype S.V := R.sheets.classFinite
  letI : Fintype Bd.B := inferInstance
  let Bset : Finset Bd.B := Finset.univ
  let Source : Type := FrozenIndex R h × Bd.B × Bd.B × S.SqfExtIdeal
  let Pset : Finset Source := Tset.product (Bset.product (Bset.product Cset))
  let sourceTerm (p : Source) : ℂ :=
    if qI p.1.a.1 * qI p.2.2.2.1 * qI p.1.n.1 ^ 3 ≤ R0 then
      reflectedTerm R υ h d Z (p.1, p.2.1, p.2.2.1, p.2.2.2)
    else 0
  have hsourceZero (p : Source) (hp : p ∉ Pset) : sourceTerm p = 0 := by
    by_cases hQ : qI p.1.a.1 * qI p.2.2.2.1 * qI p.1.n.1 ^ 3 ≤ R0
    · have hbounds := rf_retained_cutoff_components
        (qI p.1.a.1) (qI p.2.2.2.1) (qI p.1.n.1) R0
        (rf_retained_qI_ge_one p.1.a.1 p.1.a.2.1)
        (rf_retained_qI_ge_one p.2.2.2.1 (by simpa using p.2.2.2.2.1.1))
        (rf_retained_qI_ge_one p.1.n.1 p.1.n.2.1) hQ
      have ht : p.1 ∈ Tset := (hT p.1).2 ⟨hbounds.1, hbounds.2.2⟩
      have hc : p.2.2.2 ∈ Cset := (hC p.2.2.2).2 hbounds.2.1
      have hmem : p ∈ Pset := by
        rcases p with ⟨t, sd, sc, c⟩
        have ht' : t ∈ Tset := by simpa using ht
        have hc' : c ∈ Cset := by simpa using hc
        change (t, (sd, (sc, c))) ∈ Tset.product (Bset.product (Bset.product Cset))
        exact Finset.mem_product.mpr
          ⟨ht', Finset.mem_product.mpr
            ⟨Finset.mem_univ sd, Finset.mem_product.mpr ⟨Finset.mem_univ sc, hc'⟩⟩⟩
      exact (hp hmem).elim
    · simp [sourceTerm, hQ]
  have hsourceSum :
      (∑' p : Source, sourceTerm p) = ∑ p ∈ Pset, sourceTerm p :=
    tsum_eq_sum hsourceZero
  have hsourceSumExpanded :
      (∑' p : Source,
        if (qI p.1.a.1 * qI p.2.2.2.1 * qI p.1.n.1 ^ 3 ≤ R0) = true then
          reflectedTerm R υ h d Z (p.1, p.2.1, p.2.2.1, p.2.2.2) else 0) =
        ∑ p ∈ Pset, sourceTerm p := by
    simpa [sourceTerm] using hsourceSum
  have hinner (t : FrozenIndex R h) (sd sc : Bd.B) :
      (∑ c ∈ Cset,
        if qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 ≤ R0 then
          reflectedTerm R υ h d Z (t, sd, sc, c) else 0) =
      ∑ k ∈ Kset,
        if Squarefree d.1 ∧ IsCoprime d.1 h.1 then
          frozenOmega R υ t * ((qI t.n.1)⁻¹ : ℝ) * retainedColumn R υ t sd sc d
            ((2 ^ k : ℕ) : ℝ) Z R0
        else 0 := by
    let qa := qI t.a.1
    let qn := qI t.n.1
    let omega := frozenOmega R υ t * ((qI t.n.1)⁻¹ : ℝ)
    let rho := frozenRho R υ t sd d
    let coeff (c : S.SqfExtIdeal) : ℂ :=
      frozenLambda R υ t sc c * (qI c.1 ^ (-(1 / 2 : ℝ)) : ℝ) *
        chiIdealPow D d.1 (cgen R c) 3 *
        profilePhi R υ (kappaSix R t sd sc)
          (Z * qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 /
            (qI d.1 ^ 2 * qI t.f.1 ^ 2))
    have hterm (c : S.SqfExtIdeal) :
        reflectedTerm R υ h d Z (t, sd, sc, c) = omega * rho * coeff c := by
      simp [reflectedTerm, omega, rho, coeff]
      ring
    have hcoeffZero (c : S.SqfExtIdeal) (hc : c ∉ Cset) :
        (if qa * qI c.1 * qn ^ 3 ≤ R0 then coeff c else 0) = 0 := by
      by_cases hQ : qa * qI c.1 * qn ^ 3 ≤ R0
      · have hqc := (rf_retained_cutoff_components qa (qI c.1) qn R0
          (by simpa [qa] using rf_retained_qI_ge_one t.a.1 t.a.2.1)
          (rf_retained_qI_ge_one c.1 (by simpa using c.2.1.1))
          (by simpa [qn] using rf_retained_qI_ge_one t.n.1 t.n.2.1) hQ).2.1
        exact (hc ((hC c).2 hqc)).elim
      · simp [hQ]
    have hfiniteCoeff :
        (∑' c : S.SqfExtIdeal,
          if qa * qI c.1 * qn ^ 3 ≤ R0 then coeff c else 0) =
          ∑ c ∈ Cset,
            if qa * qI c.1 * qn ^ 3 ≤ R0 then coeff c else 0 :=
      tsum_eq_sum hcoeffZero
    have hdyads := rf_retained_c_dyad_decomp qa qn R0
      (by simpa [qa] using rf_retained_qI_ge_one t.a.1 t.a.2.1)
      (by simpa [qn] using rf_retained_qI_ge_one t.n.1 t.n.2.1)
      (by linarith) coeff
    calc
      _ = omega * rho *
          (∑ c ∈ Cset,
            if qa * qI c.1 * qn ^ 3 ≤ R0 then coeff c else 0) := by
        calc
          _ = ∑ c ∈ Cset, (omega * rho) *
                (if qa * qI c.1 * qn ^ 3 ≤ R0 then coeff c else 0) := by
              apply Finset.sum_congr rfl
              intro c hc
              by_cases hQ : qa * qI c.1 * qn ^ 3 ≤ R0
              · simp [qa, qn, hterm c, hQ]
              · simp [qa, qn, hterm c, hQ]
          _ = omega * rho *
                (∑ c ∈ Cset,
                  if qa * qI c.1 * qn ^ 3 ≤ R0 then coeff c else 0) := by
              rw [Finset.mul_sum]
      _ = omega * rho *
          (∑' c : S.SqfExtIdeal,
            if qa * qI c.1 * qn ^ 3 ≤ R0 then coeff c else 0) := by
        exact congrArg (fun x : ℂ => omega * rho * x) hfiniteCoeff.symm
      _ = omega * rho *
          (∑ k ∈ Kset,
            ∑' c : S.SqfExtIdeal,
              if ((2 ^ k : ℕ) : ℝ) ≤ qI c.1 ∧
                  qI c.1 < 2 * ((2 ^ k : ℕ) : ℝ) ∧
                  qa * qI c.1 * qn ^ 3 ≤ R0 then coeff c else 0) := by
        rw [hK]
        exact congrArg (fun x : ℂ => omega * rho * x) hdyads
      _ = ∑ k ∈ Kset,
          if Squarefree d.1 ∧ IsCoprime d.1 h.1 then
            omega * retainedColumn R υ t sd sc d
              ((2 ^ k : ℕ) : ℝ) Z R0
          else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hdc : Squarefree d.1 ∧ IsCoprime d.1 h.1
        · simp [hdc, retainedColumn, omega, rho, coeff]
          ring
        · have hrhoZero : frozenRho R υ t sd d = 0 := by
            by_cases hsq : Squarefree d.1
            · have hcopH : ¬ IsCoprime d.1 h.1 := by
                intro hc
                exact hdc ⟨hsq, hc⟩
              by_cases hcop : IsCoprime d.1 (h.1 * t.n.1)
              · have hcop' : IsCoprime d.1 h.1 := (IsCoprime.mul_right_iff.mp hcop).1
                exact (hcopH hcop').elim
              · simp [frozenRho, hsq, hcop]
            · simp [frozenRho, hsq]
          simp [hdc, retainedColumn, rho, hrhoZero]
  by_cases hdc : Squarefree d.1 ∧ IsCoprime d.1 h.1
  · simp only [splitReflection, if_pos hdc]
    calc
      _ = ∑ p ∈ Pset, sourceTerm p := by
          simpa [sourceTerm] using hsourceSum
      _ = ∑ t ∈ Tset, ∑ sd ∈ Bset, ∑ sc ∈ Bset,
            ∑ c ∈ Cset,
              if qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 ≤ R0 then
                reflectedTerm R υ h d Z (t, sd, sc, c) else 0 := by
          calc
            (∑ p ∈ Pset, sourceTerm p) =
                ∑ t ∈ Tset, ∑ u ∈ Bset.product (Bset.product Cset),
                  sourceTerm (t, u) := by
                    simpa [Pset, Source] using
                      (Finset.sum_product Tset (Bset.product (Bset.product Cset))
                        (fun p => sourceTerm p))
            _ = ∑ t ∈ Tset, ∑ sd ∈ Bset, ∑ u ∈ Bset.product Cset,
                  sourceTerm (t, sd, u.1, u.2) := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    simpa using
                      (Finset.sum_product Bset (Bset.product Cset)
                        (fun p => sourceTerm (t, p)))
            _ = ∑ t ∈ Tset, ∑ sd ∈ Bset, ∑ sc ∈ Bset, ∑ c ∈ Cset,
                  sourceTerm (t, sd, sc, c) := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    apply Finset.sum_congr rfl
                    intro sd hsd
                    simpa using
                      (Finset.sum_product Bset Cset
                        (fun p => sourceTerm (t, sd, p)))
            _ = ∑ t ∈ Tset, ∑ sd ∈ Bset, ∑ sc ∈ Bset, ∑ c ∈ Cset,
                  if qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 ≤ R0 then
                    reflectedTerm R υ h d Z (t, sd, sc, c) else 0 := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    apply Finset.sum_congr rfl
                    intro sd hsd
                    apply Finset.sum_congr rfl
                    intro sc hsc
                    apply Finset.sum_congr rfl
                    intro c hc
                    by_cases hQ : qI t.a.1 * qI c.1 * qI t.n.1 ^ 3 ≤ R0 <;>
                      simp [sourceTerm, hQ]
      _ = ∑ t ∈ Tset, ∑ sd ∈ Bset, ∑ sc ∈ Bset, ∑ k ∈ Kset,
            frozenOmega R υ t * ((qI t.n.1)⁻¹ : ℝ) * retainedColumn R υ t sd sc d
              ((2 ^ k : ℕ) : ℝ) Z R0 := by
          apply Finset.sum_congr rfl
          intro t ht
          apply Finset.sum_congr rfl
          intro sd hsd
          apply Finset.sum_congr rfl
          intro sc hsc
          simpa [hdc] using hinner t sd sc
      _ = ∑ t ∈ Tset, ∑ sd : Bd.B, ∑ sc : Bd.B, ∑ k ∈ Kset,
            frozenOmega R υ t * ((qI t.n.1)⁻¹ : ℝ) * retainedColumn R υ t sd sc d
              ((2 ^ k : ℕ) : ℝ) Z R0 := by
          simp [Bset]
  · simp [splitReflection, hdc]

set_option maxHeartbeats 8000000 in
private theorem rf_retained_t_weight_bound (δ₁ : ℝ) (hδ₁ : 0 < δ₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ h (hh : IsPowerful h.1) R0,
      (hR0 : 1 ≤ R0) →
      let Tset :=
        (rf_retained_frozen_cut_finite R h hh R0 (by linarith : 0 ≤ R0)).toFinset
      (∑ t ∈ Tset, betaIdeal R t.f t.a / qI t.n.1) ≤
        C * qI h.1 ^ δ₁ * Real.log (2 * R0) := by
  obtain ⟨Cact, hCact, hActBound⟩ := (rf_active_support_bounds R).2.2.2 δ₁ hδ₁
  obtain ⟨Charm, hCharm, hHarm⟩ := a2_bridge_COUNT_harmonic S
  letI : Fintype (UnitSix S) := R.sheets.unitSixFinite
  refine ⟨Fintype.card (UnitSix S) * Cact * Charm, by positivity, ?_⟩
  intro h hh R0 hR0
  classical
  let Aset : Finset S.ExtIdeal := bridgeNormFinset S R0
  let Nset : Finset S.ExtIdeal := bridgeNormFinset S R0
  let hcut := a2_bridge_COUNT_finite S R0 (by linarith)
  let AType : Type := {a : S.ExtIdeal // a ∈ Aset}
  let NType : Type := {n : S.ExtIdeal // n ∈ Nset}
  letI : Fintype AType := Aset.finite_toSet.fintype
  letI : Fintype NType := Nset.finite_toSet.fintype
  let F0 : Type := {f : S.ExtIdeal // Squarefree f.1 ∧
    ∀ v ∈ R.exterior.support f, v ∈ R.exterior.support h}
  letI : Finite F0 := rf_squarefree_support_finite R h hh
  letI : Fintype F0 := Fintype.ofFinite F0
  let Active : Type := {f : F0 // activeFactor R h f.1}
  letI : Fintype Active := Subtype.fintype (fun f : F0 => activeFactor R h f.1)
  let Index : Type := Active × UnitSix S × AType × NType
  letI : Fintype Index := inferInstance
  let Tfin := rf_retained_frozen_cut_finite R h hh R0 (by linarith : 0 ≤ R0)
  let Tset : Finset (FrozenIndex R h) := Tfin.toFinset
  have hTmem (t : FrozenIndex R h) :
      t ∈ Tset ↔ qI t.a.1 ≤ R0 ∧ qI t.n.1 ≤ R0 := by
    exact Set.Finite.mem_toFinset Tfin
  let Tcut : Type := {t : FrozenIndex R h // qI t.a.1 ≤ R0 ∧ qI t.n.1 ≤ R0}
  letI : Fintype Tcut := Tfin.fintype
  let toIndex (t : Tcut) : Index :=
    (⟨⟨t.1.f, ⟨t.1.active.1, t.1.active.2.1⟩⟩, t.1.active⟩,
      t.1.u,
      ⟨t.1.a, (hcut.2 t.1.a).2 (by
        simpa [qI, idealNorm] using t.2.1)⟩,
      ⟨t.1.n, (hcut.2 t.1.n).2 (by
        simpa [qI, idealNorm] using t.2.2)⟩)
  have htoIndexInj : Function.Injective toIndex := by
    intro x y hxy
    rcases x with ⟨tx, hx⟩
    rcases y with ⟨ty, hy⟩
    apply Subtype.ext
    have hf : tx.f = ty.f := congrArg (fun z : Index => z.1.1.1) hxy
    have hu : tx.u = ty.u := congrArg (fun z : Index => z.2.1) hxy
    have ha : tx.a = ty.a := congrArg (fun z : Index => z.2.2.1.1) hxy
    have hn : tx.n = ty.n := congrArg (fun z : Index => z.2.2.2.1) hxy
    cases tx with
    | mk fx ax nx ux factx numx copx =>
      cases ty with
      | mk fy ay ny uy facty numy copy =>
        have hfx : fx = fy := by simpa using hf
        subst fy
        have hax : ax = ay := by simpa using ha
        subst ay
        have hnx : nx = ny := by simpa using hn
        subst ny
        have hux : ux = uy := by simpa using hu
        subst uy
        rfl
  let imageT : Finset Index := (Finset.univ : Finset Tcut).image toIndex
  let activePred (i : Index) : Prop := activeNumerator R i.1.1.1 i.2.2.1.1
  let weight (i : Index) : ℝ :=
    betaIdeal R i.1.1.1 i.2.2.1.1 / qI i.2.2.2.1.1
  have hImageSub : imageT ⊆ (Finset.univ : Finset Index).filter activePred := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨t, ht, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · simp
    · simpa [activePred, toIndex] using t.1.numerator
  have hweightNonneg (i : Index) : 0 ≤ weight i := by
    dsimp [weight]
    apply div_nonneg
    · exact rf_betaIdeal_nonneg R i.1.1.1 i.2.2.1.1
    · exact le_of_lt (rf_qI_pos_ge_one i.2.2.2.1.1 i.2.2.2.1.2.1).1
  have hsumT :
      (∑ t ∈ Tset, betaIdeal R t.f t.a / qI t.n.1) =
        ∑ i ∈ imageT, weight i := by
    have hsumTsub (g : FrozenIndex R h → ℝ) :
        (∑ t : Tcut, g t.1) = ∑ t ∈ Tset, g t := by
      change (∑ t ∈ (Finset.univ : Finset Tcut), g t.1) = _
      refine Finset.sum_bij (fun t _ => t.1) ?_ ?_ ?_ ?_
      · intro t ht
        exact (hTmem t.1).2 t.2
      · intro t ht t' ht' he
        exact Subtype.ext he
      · intro t ht
        exact ⟨⟨t, (hTmem t).1 ht⟩, by simp, rfl⟩
      · intro t ht
        rfl
    calc
      _ = ∑ t : Tcut, weight (toIndex t) := (hsumTsub _).symm
      _ = ∑ i ∈ imageT, weight i := by
        dsimp [imageT]
        symm
        exact Finset.sum_image (fun t ht t' ht' he => htoIndexInj he)
  have hImageBound :
      (∑ i ∈ imageT, weight i) ≤
        ∑ i ∈ (Finset.univ : Finset Index).filter activePred, weight i :=
    Finset.sum_le_sum_of_subset_of_nonneg hImageSub (fun i hi hnot => hweightNonneg i)
  have hfilterEq :
      (∑ i ∈ (Finset.univ : Finset Index).filter activePred, weight i) =
        ∑ i : Index, if activePred i then weight i else 0 := by
    rw [Finset.sum_filter]
  have hprodEq :
      (∑ i : Index, if activePred i then weight i else 0) =
        ∑ f : Active, ∑ u : UnitSix S, ∑ a : AType, ∑ n : NType,
          if activeNumerator R f.1.1 a.1 then
            betaIdeal R f.1.1 a.1 / qI n.1.1 else 0 := by
    simp [Index, activePred, weight, Fintype.sum_prod_type]
  have hsumN (g : S.ExtIdeal → ℝ) :
      (∑ n : NType, g n.1) = ∑ n ∈ Nset, g n := by
    change (∑ n ∈ (Finset.univ : Finset NType), g n.1) = _
    refine Finset.sum_bij (fun n _ => n.1) ?_ ?_ ?_ ?_
    · intro n hn
      exact n.2
    · intro n hn n' hn' he
      exact Subtype.ext he
    · intro n hn
      exact ⟨⟨n, hn⟩, by simp, rfl⟩
    · intro n hn
      rfl
  have hsumA (g : S.ExtIdeal → ℝ) :
      (∑ a : AType, g a.1) = ∑ a ∈ Aset, g a := by
    change (∑ a ∈ (Finset.univ : Finset AType), g a.1) = _
    refine Finset.sum_bij (fun a _ => a.1) ?_ ?_ ?_ ?_
    · intro a ha
      exact a.2
    · intro a ha a' ha' he
      exact Subtype.ext he
    · intro a ha
      exact ⟨⟨a, ha⟩, by simp, rfl⟩
    · intro a ha
      rfl
  let Harm : ℝ := ∑ n : NType, (qI n.1.1)⁻¹
  have hHarmNonneg : 0 ≤ Harm := by
    dsimp [Harm]
    apply Finset.sum_nonneg
    intro n hn
    apply inv_nonneg.mpr
    change 0 ≤ (Ideal.absNorm n.1.1 : ℝ)
    exact Nat.cast_nonneg _
  have hHarmBound : Harm ≤ Charm * Real.log (2 * R0) := by
    have h := hHarm R0 hR0
    have hs := hsumN (fun n => (qI n.1)⁻¹)
    have hH : Harm = ∑ n ∈ Nset, (qI n.1)⁻¹ := by
      simpa [Harm] using hs
    have hN' : (∑ n ∈ Nset, (qI n.1)⁻¹) ≤ Charm * Real.log (2 * R0) := by
      simpa [Nset, idealNorm, qI] using h
    rw [hH]
    exact hN'
  have hBetaBound (f : Active) :
      (∑ a ∈ Aset.filter (activeNumerator R f.1.1), betaIdeal R f.1.1 a) ≤
        Eideal R f.1.1 0 := by
    apply rf_betaIdeal_sum_le_Eideal R f.1.1 _
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hA_N (f : Active) :
      (∑ a : AType, ∑ n : NType,
        if activeNumerator R f.1.1 a.1 then
          betaIdeal R f.1.1 a.1 / qI n.1.1 else 0) ≤
        Eideal R f.1.1 0 * Harm := by
    have hterm (a : AType) (n : NType) :
        (if activeNumerator R f.1.1 a.1 then
          betaIdeal R f.1.1 a.1 / qI n.1.1 else 0) =
        (if activeNumerator R f.1.1 a.1 then betaIdeal R f.1.1 a.1 else 0) *
          (qI n.1.1)⁻¹ := by
      by_cases ha : activeNumerator R f.1.1 a.1 <;> simp [ha, div_eq_mul_inv]
    have hsumFactor :
        (∑ a : AType, ∑ n : NType,
          if activeNumerator R f.1.1 a.1 then
            betaIdeal R f.1.1 a.1 / qI n.1.1 else 0) =
          (∑ a : AType,
            if activeNumerator R f.1.1 a.1 then betaIdeal R f.1.1 a.1 else 0) * Harm := by
      calc
        _ = ∑ a : AType, ∑ n : NType,
              (if activeNumerator R f.1.1 a.1 then betaIdeal R f.1.1 a.1 else 0) *
                (qI n.1.1)⁻¹ := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro n hn
              exact hterm a n
        _ = ∑ a : AType,
              (if activeNumerator R f.1.1 a.1 then betaIdeal R f.1.1 a.1 else 0) * Harm := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum]
        _ = _ := by rw [Finset.sum_mul]
    have hsumAfilter :
        (∑ a : AType,
          if activeNumerator R f.1.1 a.1 then betaIdeal R f.1.1 a.1 else 0) =
          ∑ a ∈ Aset.filter (activeNumerator R f.1.1), betaIdeal R f.1.1 a := by
      calc
        _ = ∑ a ∈ Aset,
            if activeNumerator R f.1.1 a then betaIdeal R f.1.1 a else 0 := by
              exact hsumA (fun a =>
                if activeNumerator R f.1.1 a then betaIdeal R f.1.1 a else 0)
        _ = ∑ a ∈ Aset.filter (activeNumerator R f.1.1), betaIdeal R f.1.1 a := by
              rw [← Finset.sum_filter]
    calc
      _ = (∑ a ∈ Aset.filter (activeNumerator R f.1.1),
            betaIdeal R f.1.1 a) * Harm := by
              exact hsumFactor.trans (congrArg (fun x : ℝ => x * Harm) hsumAfilter)
      _ ≤ Eideal R f.1.1 0 * Harm :=
        mul_le_mul_of_nonneg_right (hBetaBound f) hHarmNonneg
  have hActiveSum : (∑ f : Active, Eideal R f.1.1 0) ≤ Cact * qI h.1 ^ δ₁ := by
    have hAllActive : (∑ f : F0, Eideal R f.1 0) ≤ Cact * qI h.1 ^ δ₁ := by
      have h := hActBound h 0 (by norm_num)
      simpa [F0, finsum_eq_sum_of_fintype] using h
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun f : F0 => activeFactor R h f.1) (fun f : F0 => Eideal R f.1 0)
    have hdecomp :
        (∑ f : Active, Eideal R f.1.1 0) +
          ∑ f : {f : F0 // ¬ activeFactor R h f.1}, Eideal R f.1.1 0 =
            ∑ f : F0, Eideal R f.1 0 := by
      simpa [Active] using hsplit
    have hcompl : 0 ≤
        ∑ f : {f : F0 // ¬ activeFactor R h f.1}, Eideal R f.1.1 0 := by
      apply Finset.sum_nonneg
      intro f hf
      exact rf_Eideal_nonneg R f.1.1 (by norm_num)
    linarith
  calc
    (∑ t ∈ Tset, betaIdeal R t.f t.a / qI t.n.1) =
        ∑ i ∈ imageT, weight i := hsumT
    _ ≤ ∑ i ∈ (Finset.univ : Finset Index).filter activePred, weight i := hImageBound
    _ = ∑ f : Active, ∑ u : UnitSix S, ∑ a : AType, ∑ n : NType,
        if activeNumerator R f.1.1 a.1 then
          betaIdeal R f.1.1 a.1 / qI n.1.1 else 0 := by
      rw [hfilterEq, hprodEq]
    _ ≤ ∑ f : Active, ∑ u : UnitSix S, Eideal R f.1.1 0 * Harm := by
      apply Finset.sum_le_sum
      intro f hf
      exact Finset.sum_le_sum (fun u hu => hA_N f)
    _ = ∑ f : Active, Fintype.card (UnitSix S) *
          (Eideal R f.1.1 0 * Harm) := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = Fintype.card (UnitSix S) *
          (∑ f : Active, Eideal R f.1.1 0 * Harm) := by rw [Finset.mul_sum]
    _ = Fintype.card (UnitSix S) * Harm *
          (∑ f : Active, Eideal R f.1.1 0) := by
      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ Fintype.card (UnitSix S) * Harm * (Cact * qI h.1 ^ δ₁) := by
      apply mul_le_mul_of_nonneg_left hActiveSum
      positivity
    _ ≤ Fintype.card (UnitSix S) * (Charm * Real.log (2 * R0)) *
          (Cact * qI h.1 ^ δ₁) := by
      have hcard : 0 ≤ (Fintype.card (UnitSix S) : ℝ) := Nat.cast_nonneg _
      have hpow : 0 ≤ qI h.1 ^ δ₁ :=
        Real.rpow_nonneg (le_of_lt (rf_qI_pos_ge_one h.1 h.2.1).1) _
      have hnonneg : 0 ≤ Fintype.card (UnitSix S) * (Cact * qI h.1 ^ δ₁) :=
        mul_nonneg hcard (mul_nonneg hCact.le hpow)
      nlinarith [mul_le_mul_of_nonneg_right hHarmBound hnonneg]
    _ = (Fintype.card (UnitSix S) * Cact * Charm) *
          qI h.1 ^ δ₁ * Real.log (2 * R0) := by ring

set_option maxHeartbeats 8000000 in
private theorem rf_retained_fixed_h_bound (δ₁ δ₂ : ℝ)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ υ (D0 Z : ℝ) (h : S.ExtIdeal) (R0 : ℝ),
      1 ≤ D0 → 2 ≤ Z → IsPowerful h.1 → 1 ≤ R0 →
      Real.sqrt (∑' d : S.ExtIdeal,
        if D0 ≤ qI d.1 ∧ qI d.1 < 2 * D0 then
          ‖splitReflection R true υ h d Z R0‖ ^ 2 else 0) ≤
        C * qI h.1 ^ δ₁ * Real.log (2 * R0) ^ 2 *
          (D0 + R0) ^ (1 / 2 : ℝ) * (D0 * R0) ^ (δ₂ / 2) := by
  obtain ⟨α, hα, hcol⟩ := rf_retained_column_dyad R
  obtain ⟨Kcol, hKcol, hColumn⟩ := hcol 1 δ₂ (by norm_num) hδ₂
  obtain ⟨Ctw, hCtw, hTweight⟩ := rf_retained_t_weight_bound R δ₁ hδ₁
  letI : Fintype S.V := R.sheets.classFinite
  letI : Fintype Bd.B := inferInstance
  let Cdyad : ℝ := (Real.log 2)⁻¹
  let C : ℝ := Kcol * (Fintype.card Bd.B : ℝ) ^ 2 * Cdyad * Ctw
  refine ⟨C, ?_, ?_⟩
  · dsimp [C, Cdyad]
    positivity
  · intro υ D0 Z h R0 hD0 hZ hPower hR0
    classical
    let Tfin := rf_retained_frozen_cut_finite R h hPower R0 (by linarith : 0 ≤ R0)
    let Tset : Finset (FrozenIndex R h) := Tfin.toFinset
    have hTmem (t : FrozenIndex R h) :
        t ∈ Tset ↔ qI t.a.1 ≤ R0 ∧ qI t.n.1 ≤ R0 := by
      exact Set.Finite.mem_toFinset Tfin
    let Cfin := rf_retained_sqf_norm_cut_finite (S := S) R0 (by linarith)
    let Cset : Finset S.SqfExtIdeal := Cfin.toFinset
    have hCmem (c : S.SqfExtIdeal) : c ∈ Cset ↔ qI c.1 ≤ R0 :=
      Set.Finite.mem_toFinset Cfin
    let Kset : Finset ℕ := Finset.range (Nat.log 2 ⌊R0⌋₊ + 1)
    let Bset : Finset Bd.B := Finset.univ
    let Wset : Finset (FrozenIndex R h × Bd.B × Bd.B × ℕ) :=
      Tset.product (Bset.product (Bset.product Kset))
    let block (w : FrozenIndex R h × Bd.B × Bd.B × ℕ) (d : S.ExtIdeal) : ℂ :=
      if Squarefree d.1 ∧ IsCoprime d.1 h.1 then
        frozenOmega R υ w.1 * ((qI w.1.n.1)⁻¹ : ℝ) *
          retainedColumn R υ w.1 w.2.1 w.2.2.1 d
            ((2 ^ w.2.2.2 : ℕ) : ℝ) Z R0
      else 0
    have hsplit (d : S.ExtIdeal) :
        splitReflection R true υ h d Z R0 = ∑ w ∈ Wset, block w d := by
      have hd := rf_retained_split_finite_decomp R υ h d Z R0 hR0
        Tset Cset Kset hTmem hCmem rfl
      simpa [Wset, Bset, block, Finset.sum_product] using hd
    let rowDyad (d : S.ExtIdeal) : Prop :=
      D0 ≤ qI d.1 ∧ qI d.1 < 2 * D0
    let rowSet : Set S.ExtIdeal := {d | rowDyad d}
    have hrowFinite : rowSet.Finite := by
      have hcut := a2_bridge_COUNT_finite S (2 * D0) (by positivity)
      apply hcut.1.subset
      intro d hd
      change idealNorm d.1 ≤ 2 * D0
      simpa [rowDyad, qI, idealNorm] using hd.2.le
    let Rows : Finset S.ExtIdeal := hrowFinite.toFinset
    have hRows (d : S.ExtIdeal) : d ∈ Rows ↔ rowDyad d :=
      Set.Finite.mem_toFinset hrowFinite
    let massTerm (d : S.ExtIdeal) : ℝ :=
      if rowDyad d then ‖splitReflection R true υ h d Z R0‖ ^ 2 else 0
    have hzeroRow (d : S.ExtIdeal) (hd : d ∉ Rows) : massTerm d = 0 := by
      by_cases hrow : rowDyad d
      · exact (hd ((hRows d).2 hrow)).elim
      · simp [massTerm, hrow]
    have hrootEq :
        Real.sqrt (∑' d : S.ExtIdeal, massTerm d) =
          bridgeL2 Rows (fun d => splitReflection R true υ h d Z R0) := by
      rw [bridgeL2]
      congr 1
      calc
        (∑' d : S.ExtIdeal, massTerm d) = ∑ d ∈ Rows, massTerm d :=
          tsum_eq_sum hzeroRow
        _ = ∑ d ∈ Rows, ‖splitReflection R true υ h d Z R0‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro d hd
          simp [massTerm, (hRows d).mp hd]
    have hsplitFun :
        (fun d => splitReflection R true υ h d Z R0) =
          fun d => ∑ w ∈ Wset, block w d := by
      funext d
      exact hsplit d
    have hMink :
        bridgeL2 Rows (fun d => splitReflection R true υ h d Z R0) ≤
          ∑ w ∈ Wset, bridgeL2 Rows (block w) := by
      rw [hsplitFun]
      exact a2_bridge_FINITE_L2 Rows Wset block
    let Kscale : ℝ := Kcol * (D0 + R0) ^ (1 / 2 : ℝ) * (D0 * R0) ^ (δ₂ / 2)
    have hKscaleNonneg : 0 ≤ Kscale := by dsimp [Kscale]; positivity
    have hblockBound (w : FrozenIndex R h × Bd.B × Bd.B × ℕ) (hw : w ∈ Wset) :
        bridgeL2 Rows (block w) ≤
          (betaIdeal R w.1.f w.1.a / qI w.1.n.1) * Kscale := by
      rcases w with ⟨t, sd, sc, k⟩
      have hk : k ∈ Kset := by
        have hp := Finset.mem_product.mp hw
        exact (Finset.mem_product.mp (Finset.mem_product.mp hp.2).2).2
      have hfloorOne : 1 ≤ ⌊R0⌋₊ := by
        apply (Nat.le_floor_iff (by linarith : 0 ≤ R0)).2
        exact_mod_cast hR0
      have hkLe : k ≤ Nat.log 2 ⌊R0⌋₊ :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hpowLog : 2 ^ Nat.log 2 ⌊R0⌋₊ ≤ ⌊R0⌋₊ :=
        Nat.pow_log_le_self 2 (by omega)
      have hkPow : 2 ^ k ≤ ⌊R0⌋₊ :=
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) hkLe).trans hpowLog
      let Cdyad : ℝ := ((2 ^ k : ℕ) : ℝ)
      have hCdyadOne : 1 ≤ Cdyad := by
        dsimp [Cdyad]
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
          (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)))
      have hCdyadR : Cdyad ≤ R0 := by
        dsimp [Cdyad]
        calc
          ((2 ^ k : ℕ) : ℝ) ≤ (⌊R0⌋₊ : ℝ) := by exact_mod_cast hkPow
          _ ≤ R0 := Nat.floor_le (by linarith)
      have hqA := rf_qI_pos_ge_one t.a.1 t.a.2.1
      have hqN := rf_qI_pos_ge_one t.n.1 t.n.2.1
      have hqF := rf_qI_pos_ge_one t.f.1 t.f.2.1
      have hDpos : 0 < D0 := lt_of_lt_of_le (by norm_num) hD0
      have hCpos : 0 < Cdyad := by
        dsimp [Cdyad]
        have hp : 0 < 2 ^ k := Nat.pow_pos (by norm_num : 0 < (2 : ℕ))
        exact_mod_cast hp
      let v : ℝ := Z * qI t.a.1 * qI t.n.1 ^ 3 * Cdyad /
        (D0 ^ 2 * qI t.f.1 ^ 2)
      have hZpos : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
      have hv : 0 < v := by
        dsimp [v]
        apply div_pos
        · exact mul_pos
            (mul_pos (mul_pos hZpos hqA.1) (pow_pos hqN.1 3)) hCpos
        · exact mul_pos (pow_pos hDpos 2) (pow_pos hqF.1 2)
      have hmin : min (v ^ α) (v ^ (-1 : ℝ)) ≤ 1 := by
        rcases le_total v 1 with hvle | h1v
        · exact (min_le_left _ _).trans
            (Real.rpow_le_one hv.le hvle hα.le)
        · exact (min_le_right _ _).trans
            (Real.rpow_le_one_of_one_le_of_nonpos h1v (by norm_num))
      have hcol := hColumn υ h t sd sc Cdyad D0 Z R0 hCdyadOne hD0 hZ hR0
      have hcolScale :
          Real.sqrt (∑' d : S.ExtIdeal,
            if rowDyad d then ‖retainedColumn R υ t sd sc d Cdyad Z R0‖ ^ 2 else 0) ≤
          Kscale := by
        have hsumScale :
            (D0 + Cdyad) ^ (1 / 2 : ℝ) * (D0 * Cdyad) ^ (δ₂ / 2) ≤
              (D0 + R0) ^ (1 / 2 : ℝ) * (D0 * R0) ^ (δ₂ / 2) := by
          have hplus : D0 + Cdyad ≤ D0 + R0 := by linarith
          have hmult : D0 * Cdyad ≤ D0 * R0 :=
            mul_le_mul_of_nonneg_left hCdyadR (by positivity)
          exact mul_le_mul
            (Real.rpow_le_rpow (by positivity) hplus (by norm_num))
            (Real.rpow_le_rpow (by positivity) hmult (by positivity))
            (by positivity) (by positivity)
        have hcol' :
            Real.sqrt (∑' d : S.ExtIdeal,
              if rowDyad d then ‖retainedColumn R υ t sd sc d Cdyad Z R0‖ ^ 2 else 0) ≤
              Kcol * (D0 + Cdyad) ^ (1 / 2 : ℝ) * (D0 * Cdyad) ^ (δ₂ / 2) *
                min (v ^ α) (v ^ (-1 : ℝ)) := by
          simpa [v] using hcol
        calc
          _ ≤ Kcol * (D0 + Cdyad) ^ (1 / 2 : ℝ) *
                (D0 * Cdyad) ^ (δ₂ / 2) * min (v ^ α) (v ^ (-1 : ℝ)) := hcol'
          _ ≤ Kcol * (D0 + Cdyad) ^ (1 / 2 : ℝ) * (D0 * Cdyad) ^ (δ₂ / 2) := by
            have hfac : 0 ≤ Kcol * (D0 + Cdyad) ^ (1 / 2 : ℝ) *
                (D0 * Cdyad) ^ (δ₂ / 2) := by positivity
            calc
              _ ≤ Kcol * (D0 + Cdyad) ^ (1 / 2 : ℝ) *
                    (D0 * Cdyad) ^ (δ₂ / 2) * 1 :=
                mul_le_mul_of_nonneg_left hmin hfac
              _ = _ := by ring
          _ ≤ Kscale := by
            dsimp [Kscale]
            calc
              _ = Kcol * ((D0 + Cdyad) ^ (1 / 2 : ℝ) *
                    (D0 * Cdyad) ^ (δ₂ / 2)) := by ring
              _ ≤ Kcol * ((D0 + R0) ^ (1 / 2 : ℝ) *
                    (D0 * R0) ^ (δ₂ / 2)) :=
                mul_le_mul_of_nonneg_left hsumScale hKcol.le
              _ = Kcol * (D0 + R0) ^ (1 / 2 : ℝ) *
                    (D0 * R0) ^ (δ₂ / 2) := by ring
      let column (d : S.ExtIdeal) := retainedColumn R υ t sd sc d Cdyad Z R0
      let rowTerm (d : S.ExtIdeal) := if rowDyad d then ‖column d‖ ^ 2 else 0
      have hzeroCol (d : S.ExtIdeal) (hd : d ∉ Rows) : rowTerm d = 0 := by
        by_cases hrow : rowDyad d
        · exact (hd ((hRows d).2 hrow)).elim
        · simp [rowTerm, hrow]
      have hcolTsum : (∑' d : S.ExtIdeal, rowTerm d) =
          ∑ d ∈ Rows, ‖column d‖ ^ 2 := by
        calc
          _ = ∑ d ∈ Rows, rowTerm d := tsum_eq_sum hzeroCol
          _ = _ := by
            apply Finset.sum_congr rfl
            intro d hd
            simp [rowTerm, (hRows d).mp hd]
      have hcolBridge :
          bridgeL2 Rows column = Real.sqrt (∑' d : S.ExtIdeal, rowTerm d) := by
        unfold bridgeL2
        rw [← hcolTsum]
      have hOmega : ‖frozenOmega R υ t‖ ≤ betaIdeal R t.f t.a :=
        (rf_exterior_factorization R).1 υ h t |>.1
      have hqNpos : 0 < qI t.n.1 := hqN.1
      have hbeta : 0 ≤ betaIdeal R t.f t.a := rf_betaIdeal_nonneg R t.f t.a
      have homega :
          ‖frozenOmega R υ t * ((qI t.n.1)⁻¹ : ℝ)‖ ≤
            betaIdeal R t.f t.a / qI t.n.1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hqNpos.le)]
        calc
          ‖frozenOmega R υ t‖ * (qI t.n.1)⁻¹ ≤
              betaIdeal R t.f t.a * (qI t.n.1)⁻¹ :=
            mul_le_mul_of_nonneg_right hOmega (inv_nonneg.mpr hqNpos.le)
          _ = betaIdeal R t.f t.a / qI t.n.1 := by rw [div_eq_mul_inv]
      have hblockL2 : bridgeL2 Rows (block (t, sd, sc, k)) ≤
          (betaIdeal R t.f t.a / qI t.n.1) * Kscale := by
        let omega : ℂ := frozenOmega R υ t * ((qI t.n.1)⁻¹ : ℝ)
        have hpoint (d : S.ExtIdeal) :
            ‖block (t, sd, sc, k) d‖ ≤
              (betaIdeal R t.f t.a / qI t.n.1) * ‖column d‖ := by
          by_cases hdc : Squarefree d.1 ∧ IsCoprime d.1 h.1
          · simp only [block, if_pos hdc]
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right homega (norm_nonneg _)
          · simp [block, hdc]
            positivity
        have hsumSq :
            (∑ d ∈ Rows, ‖block (t, sd, sc, k) d‖ ^ 2) ≤
              (betaIdeal R t.f t.a / qI t.n.1) ^ 2 *
                ∑ d ∈ Rows, ‖column d‖ ^ 2 := by
          calc
            _ ≤ ∑ d ∈ Rows,
                (betaIdeal R t.f t.a / qI t.n.1) ^ 2 * ‖column d‖ ^ 2 := by
                  apply Finset.sum_le_sum
                  intro d hd
                  have hupper : 0 ≤ betaIdeal R t.f t.a / qI t.n.1 := by positivity
                  calc
                    _ ≤ ((betaIdeal R t.f t.a / qI t.n.1) * ‖column d‖) ^ 2 :=
                      (sq_le_sq₀ (norm_nonneg _)
                        (mul_nonneg hupper (norm_nonneg _))).2 (hpoint d)
                    _ = (betaIdeal R t.f t.a / qI t.n.1) ^ 2 *
                          ‖column d‖ ^ 2 := by ring
            _ = (betaIdeal R t.f t.a / qI t.n.1) ^ 2 *
                  ∑ d ∈ Rows, ‖column d‖ ^ 2 := by rw [Finset.mul_sum]
        unfold bridgeL2
        calc
          Real.sqrt (∑ d ∈ Rows, ‖block (t, sd, sc, k) d‖ ^ 2) ≤
              Real.sqrt ((betaIdeal R t.f t.a / qI t.n.1) ^ 2 *
                ∑ d ∈ Rows, ‖column d‖ ^ 2) := Real.sqrt_le_sqrt hsumSq
          _ = (betaIdeal R t.f t.a / qI t.n.1) *
                Real.sqrt (∑ d ∈ Rows, ‖column d‖ ^ 2) := by
              rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
                abs_of_nonneg (by positivity)]
          _ = (betaIdeal R t.f t.a / qI t.n.1) *
                Real.sqrt (∑' d : S.ExtIdeal, rowTerm d) := by rw [hcolTsum]
          _ ≤ (betaIdeal R t.f t.a / qI t.n.1) * Kscale :=
            mul_le_mul_of_nonneg_left hcolScale (by positivity)
      exact hblockL2
    have hblockSum :
        (∑ w ∈ Wset, bridgeL2 Rows (block w)) ≤
          Kscale * (∑ w ∈ Wset, betaIdeal R w.1.f w.1.a / qI w.1.n.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro w hw
      simpa [mul_comm] using hblockBound w hw
    have hTwt := hTweight h hPower R0 hR0
    let blockWeight (t : FrozenIndex R h) : ℝ :=
      betaIdeal R t.f t.a / qI t.n.1
    have hWweight :
        (∑ w ∈ Wset, blockWeight w.1) =
          (Fintype.card Bd.B : ℝ) ^ 2 * Kset.card *
            (∑ t ∈ Tset, blockWeight t) := by
      calc
        _ = ∑ t ∈ Tset, ∑ u ∈ Bset.product (Bset.product Kset),
              blockWeight t := by
                simpa [Wset] using
                  (Finset.sum_product Tset (Bset.product (Bset.product Kset))
                    (fun p => blockWeight p.1))
        _ = ∑ t ∈ Tset, ∑ sd ∈ Bset, ∑ u ∈ Bset.product Kset,
              blockWeight t := by
                apply Finset.sum_congr rfl
                intro t ht
                simpa using
                  (Finset.sum_product Bset (Bset.product Kset) (fun p => blockWeight t))
        _ = ∑ t ∈ Tset, ∑ sd ∈ Bset, ∑ sc ∈ Bset, ∑ k ∈ Kset,
              blockWeight t := by
                apply Finset.sum_congr rfl
                intro t ht
                apply Finset.sum_congr rfl
                intro sd hsd
                simpa using (Finset.sum_product Bset Kset (fun p => blockWeight t))
        _ = ∑ t ∈ Tset, ∑ sd ∈ Bset, ∑ sc ∈ Bset,
              (Kset.card : ℝ) * blockWeight t := by
                apply Finset.sum_congr rfl
                intro t ht
                apply Finset.sum_congr rfl
                intro sd hsd
                apply Finset.sum_congr rfl
                intro sc hsc
                simp [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ t ∈ Tset,
              (Bset.card : ℝ) ^ 2 * Kset.card * blockWeight t := by
                apply Finset.sum_congr rfl
                intro t ht
                simp [Finset.sum_const, nsmul_eq_mul]
                ring
        _ = (Bset.card : ℝ) ^ 2 * Kset.card *
              (∑ t ∈ Tset, blockWeight t) := by rw [Finset.mul_sum]
        _ = (Fintype.card Bd.B : ℝ) ^ 2 * Kset.card *
              (∑ t ∈ Tset, blockWeight t) := by simp [Bset]
    have hWsum :
        (∑ w ∈ Wset, betaIdeal R w.1.f w.1.a / qI w.1.n.1) ≤
          (Fintype.card Bd.B : ℝ) ^ 2 * Kset.card *
            (Ctw * qI h.1 ^ δ₁ * Real.log (2 * R0)) := by
      calc
        _ = (Fintype.card Bd.B : ℝ) ^ 2 * Kset.card *
              (∑ t ∈ Tset, blockWeight t) := by
                simpa [blockWeight] using hWweight
        _ ≤ (Fintype.card Bd.B : ℝ) ^ 2 * Kset.card *
              (Ctw * qI h.1 ^ δ₁ * Real.log (2 * R0)) := by
                have hfac : 0 ≤ (Fintype.card Bd.B : ℝ) ^ 2 * (Kset.card : ℝ) :=
                  mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
                exact mul_le_mul_of_nonneg_left hTwt hfac
    have hKcard : (Kset.card : ℝ) ≤ Cdyad * Real.log (2 * R0) := by
      dsimp [Kset]
      have hcard : (Finset.range (Nat.log 2 ⌊R0⌋₊ + 1)).card =
          Nat.log 2 ⌊R0⌋₊ + 1 := Finset.card_range _
      rw [hcard]
      simpa [Cdyad] using rf_retained_natlog_count R0 hR0
    have hscaleBound :
        Kscale * ((Fintype.card Bd.B : ℝ) ^ 2 * Kset.card *
          (Ctw * qI h.1 ^ δ₁ * Real.log (2 * R0))) ≤
          C * qI h.1 ^ δ₁ * Real.log (2 * R0) ^ 2 *
            (D0 + R0) ^ (1 / 2 : ℝ) * (D0 * R0) ^ (δ₂ / 2) := by
      calc
        _ ≤ Kscale * ((Fintype.card Bd.B : ℝ) ^ 2 *
              (Cdyad * Real.log (2 * R0)) *
              (Ctw * qI h.1 ^ δ₁ * Real.log (2 * R0))) := by
                apply mul_le_mul_of_nonneg_left _ hKscaleNonneg
                have hfac : 0 ≤ (Fintype.card Bd.B : ℝ) ^ 2 *
                    (Ctw * qI h.1 ^ δ₁ * Real.log (2 * R0)) := by
                  have hqh : 0 ≤ qI h.1 ^ δ₁ :=
                    Real.rpow_nonneg (le_of_lt (rf_qI_pos_ge_one h.1 h.2.1).1) _
                  have hlog : 0 ≤ Real.log (2 * R0) :=
                    Real.log_nonneg (by nlinarith [hR0])
                  exact mul_nonneg (sq_nonneg _) <|
                    mul_nonneg (mul_nonneg hCtw.le hqh) hlog
                calc
                  _ = ((Fintype.card Bd.B : ℝ) ^ 2 *
                        (Ctw * qI h.1 ^ δ₁ * Real.log (2 * R0))) * Kset.card := by ring
                  _ ≤ ((Fintype.card Bd.B : ℝ) ^ 2 *
                        (Ctw * qI h.1 ^ δ₁ * Real.log (2 * R0))) *
                        (Cdyad * Real.log (2 * R0)) :=
                    mul_le_mul_of_nonneg_left hKcard hfac
                  _ = _ := by ring
      _ = C * qI h.1 ^ δ₁ * Real.log (2 * R0) ^ 2 *
              (D0 + R0) ^ (1 / 2 : ℝ) * (D0 * R0) ^ (δ₂ / 2) := by
                dsimp [C, Kscale]
                ring
    calc
      _ = bridgeL2 Rows (fun d => splitReflection R true υ h d Z R0) := hrootEq
      _ ≤ ∑ w ∈ Wset, bridgeL2 Rows (block w) := hMink
      _ ≤ Kscale * (∑ w ∈ Wset, betaIdeal R w.1.f w.1.a / qI w.1.n.1) := hblockSum
      _ ≤ Kscale * ((Fintype.card Bd.B : ℝ) ^ 2 * Kset.card *
            (Ctw * qI h.1 ^ δ₁ * Real.log (2 * R0))) := by
          exact mul_le_mul_of_nonneg_left hWsum hKscaleNonneg
      _ ≤ _ := hscaleBound

set_option maxHeartbeats 8000000 in
/-- rf:retained-mass, 04:1119-1196. The constant can depend on fixed δ. -/
theorem rf_retained_mass : ∀ δ δ₁ δ₂ : ℝ, 0 < δ → 0 < δ₁ → 0 < δ₂ →
  ∃ C : ℝ, 0 < C ∧ ∀ υ P D0 Z, 1 ≤ P → 1 ≤ D0 → 2 ≤ Z →
    let R0 := reflectionColumnCutoff P D0 Z δ
    (R0 < 1 → reflectionMass R true υ P D0 Z δ = 0) ∧
    (1 ≤ R0 → reflectionMass R true υ P D0 Z δ ≤
      C * P ^ (1 / 2 + 2 * δ₁) * Real.log (2 * R0) ^ 4 * (D0 + R0) * (D0 * R0) ^ δ₂) := by
  intro δ δ₁ δ₂ hδ hδ₁ hδ₂
  obtain ⟨Cfixed, hCfixed, hfixed⟩ :=
    rf_retained_fixed_h_bound R δ₁ δ₂ hδ₁ hδ₂
  obtain ⟨Cpow, hCpow, hpower⟩ := rf_powerful_count S
  let C : ℝ := Cpow * 2 ^ (2 * δ₁) * Cfixed ^ 2
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  ·
    intro υ P D0 Z hP hD0 hZ
    dsimp only
    let R0 := reflectionColumnCutoff P D0 Z δ
    constructor
    · intro hR0
      have hzero (hd : S.ExtIdeal × S.ExtIdeal) :
          (if IsPowerful hd.1.1 ∧ P ≤ qI hd.1.1 ∧ qI hd.1.1 < 2 * P ∧
            D0 ≤ qI hd.2.1 ∧ qI hd.2.1 < 2 * D0 then
            ‖splitReflection R true υ hd.1 hd.2 Z R0‖ ^ 2 else 0) = 0 := by
        by_cases hc : IsPowerful hd.1.1 ∧ P ≤ qI hd.1.1 ∧ qI hd.1.1 < 2 * P ∧
            D0 ≤ qI hd.2.1 ∧ qI hd.2.1 < 2 * D0
        · simp [hc, rf_retained_split_zero_of_cutoff_lt_one R υ hd.1 hd.2 Z R0 hR0]
        · simp [hc]
      unfold reflectionMass
      calc
        (∑' hd : S.ExtIdeal × S.ExtIdeal,
          if IsPowerful hd.1.1 ∧ P ≤ qI hd.1.1 ∧ qI hd.1.1 < 2 * P ∧
              D0 ≤ qI hd.2.1 ∧ qI hd.2.1 < 2 * D0 then
            ‖splitReflection R true υ hd.1 hd.2 Z R0‖ ^ 2 else 0) =
            ∑' hd, 0 := by
              apply tsum_congr
              exact hzero
        _ = 0 := tsum_zero
    · intro hR0
      have hPpos : 0 < P := by linarith
      have hDpos : 0 < D0 := by linarith
      have hZpos : 0 < Z := by linarith
      let Hset : Finset S.ExtIdeal :=
        (bridgeNormFinset S (2 * P)).filter (fun h => IsPowerful h.1)
      let Dset : Finset S.ExtIdeal := bridgeNormFinset S (2 * D0)
      let Kset : Finset (S.ExtIdeal × S.ExtIdeal) := Hset.product Dset
      let massTerm (hd : S.ExtIdeal × S.ExtIdeal) : ℝ :=
        if IsPowerful hd.1.1 ∧ P ≤ qI hd.1.1 ∧ qI hd.1.1 < 2 * P ∧
            D0 ≤ qI hd.2.1 ∧ qI hd.2.1 < 2 * D0 then
          ‖splitReflection R true υ hd.1 hd.2 Z R0‖ ^ 2
        else 0
      have hFinP := a2_bridge_COUNT_finite S (2 * P) (by positivity)
      have hFinD := a2_bridge_COUNT_finite S (2 * D0) (by positivity)
      have hHnorm (h : S.ExtIdeal) (hh : h ∈ Hset) : idealNorm h.1 ≤ 2 * P := by
        exact (hFinP.2 h).mp (Finset.mem_filter.mp hh).1
      have hmemH (h : S.ExtIdeal) (hh : IsPowerful h.1) (hhi : qI h.1 < 2 * P) :
          h ∈ Hset := by
        apply Finset.mem_filter.mpr
        constructor
        · exact (hFinP.2 h).mpr (by simpa [idealNorm, qI] using hhi.le)
        · exact hh
      have hmemD (d : S.ExtIdeal) (dhi : qI d.1 < 2 * D0) : d ∈ Dset := by
        exact (hFinD.2 d).mpr (by simpa [idealNorm, qI] using dhi.le)
      have hImgSub : Hset.image (fun h : S.ExtIdeal => h.1) ⊆
          powerfulExteriorIdeals S P := by
        intro I hI
        rcases Finset.mem_image.mp hI with ⟨h, hh, rfl⟩
        have hnorm : idealNorm h.1 ≤ 2 * P := hHnorm h hh
        have hpow' := (Finset.mem_filter.mp hh).2
        change h.1 ∈ powerfulExteriorIdeals S P
        unfold powerfulExteriorIdeals
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        constructor
        · apply (Nat.le_floor_iff (by positivity : 0 ≤ 2 * P)).mpr
          simpa [idealNorm] using hnorm
        · exact ⟨h.2, hpow'⟩
      have hImgCard : (Hset.image (fun h : S.ExtIdeal => h.1)).card = Hset.card := by
        apply Finset.card_image_iff.mpr
        intro h hh d hd heq
        exact Subtype.ext heq
      have hHcard : (Hset.card : ℝ) ≤ Cpow * P ^ (1 / 2 : ℝ) := by
        calc
          (Hset.card : ℝ) = ((Hset.image (fun h : S.ExtIdeal => h.1)).card : ℝ) := by
            rw [hImgCard]
          _ ≤ ((powerfulExteriorIdeals S P).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hImgSub
          _ ≤ Cpow * P ^ (1 / 2 : ℝ) := by
            exact_mod_cast hpower P hP
      have hzero : ∀ hd : S.ExtIdeal × S.ExtIdeal, hd ∉ Kset → massTerm hd = 0 := by
        rintro ⟨h, d⟩ hnot
        by_cases hc : IsPowerful h.1 ∧ P ≤ qI h.1 ∧ qI h.1 < 2 * P ∧
            D0 ≤ qI d.1 ∧ qI d.1 < 2 * D0
        · rcases hc with ⟨hh, _, hhi, _, dhi⟩
          have hhm := hmemH h hh hhi
          have hdm := hmemD d dhi
          have hmem : (h, d) ∈ Kset := by simp [Kset, hhm, hdm]
          exact (hnot hmem).elim
        · simp [massTerm, hc]
      have hmassEq : reflectionMass R true υ P D0 Z δ =
          ∑ hd ∈ Kset, massTerm hd := by
        calc
          reflectionMass R true υ P D0 Z δ =
              ∑' hd : S.ExtIdeal × S.ExtIdeal, massTerm hd := by
                unfold reflectionMass
                rfl
          _ = ∑ hd ∈ Kset, massTerm hd := tsum_eq_sum hzero
      have hproduct :
          (∑ hd ∈ Kset, massTerm hd) =
            ∑ h ∈ Hset, ∑ d ∈ Dset, massTerm (h, d) := by
        simpa [Kset] using (Finset.sum_product Hset Dset massTerm)
      let Bmass : ℝ := Cfixed * (2 * P) ^ δ₁ * Real.log (2 * R0) ^ 2 *
        (D0 + R0) ^ (1 / 2 : ℝ) * (D0 * R0) ^ (δ₂ / 2)
      have hBmassNonneg : 0 ≤ Bmass := by dsimp [Bmass]; positivity
      have hBmassSq : Bmass ^ 2 =
          Cfixed ^ 2 * 2 ^ (2 * δ₁) * P ^ (2 * δ₁) * Real.log (2 * R0) ^ 4 *
            (D0 + R0) * (D0 * R0) ^ δ₂ := by
        dsimp [Bmass]
        have hrpowTwo (x a : ℝ) (hx : 0 ≤ x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
          congr 1 <;> ring
        rw [mul_pow, mul_pow, mul_pow, mul_pow,
          hrpowTwo (2 * P) δ₁ (by positivity),
          hrpowTwo (D0 + R0) (1 / 2) (by positivity),
          hrpowTwo (D0 * R0) (δ₂ / 2) (by positivity)]
        have htwoP : (2 * P) ^ (2 * δ₁) = 2 ^ (2 * δ₁) * P ^ (2 * δ₁) :=
          Real.mul_rpow (by norm_num) (by positivity)
        rw [htwoP]
        rw [show (Real.log (2 * R0) ^ 2) ^ 2 = Real.log (2 * R0) ^ 4 by
          rw [← pow_mul]]
        rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
        rw [show 2 * (δ₂ / 2) = δ₂ by ring]
        ring
      let rowTerm (h d : S.ExtIdeal) : ℝ :=
        if D0 ≤ qI d.1 ∧ qI d.1 < 2 * D0 then
          ‖splitReflection R true υ h d Z R0‖ ^ 2 else 0
      have hzeroD (h : S.ExtIdeal) (d : S.ExtIdeal) (hd : d ∉ Dset) : rowTerm h d = 0 := by
        by_cases hr : D0 ≤ qI d.1 ∧ qI d.1 < 2 * D0
        · have hdm := hmemD d hr.2
          exact (hd hdm).elim
        · simp [rowTerm, hr]
      have hrowTsum (h : S.ExtIdeal) :
          (∑' d : S.ExtIdeal, rowTerm h d) = ∑ d ∈ Dset, rowTerm h d :=
        tsum_eq_sum (hzeroD h)
      have hinnerBound (h : S.ExtIdeal) (hh : h ∈ Hset) :
          (∑ d ∈ Dset, massTerm (h, d)) ≤ Bmass ^ 2 := by
        have hpowH : IsPowerful h.1 := (Finset.mem_filter.mp hh).2
        by_cases hrange : P ≤ qI h.1 ∧ qI h.1 < 2 * P
        · have hmassRow : ∀ d ∈ Dset, massTerm (h, d) = rowTerm h d := by
            intro d hd
            by_cases hrow : D0 ≤ qI d.1 ∧ qI d.1 < 2 * D0
            · simp [massTerm, rowTerm, hpowH, hrange, hrow]
            · simp [massTerm, rowTerm, hpowH, hrange, hrow]
          have hmassTsum :
              (∑ d ∈ Dset, massTerm (h, d)) = ∑' d : S.ExtIdeal, rowTerm h d := by
            rw [Finset.sum_congr rfl hmassRow]
            exact (hrowTsum h).symm
          have hfixed' := hfixed υ D0 Z h R0 hD0 hZ hpowH hR0
          have hqhpos : 0 < qI h.1 := (rf_qI_pos_ge_one h.1 h.2.1).1
          have hqH : qI h.1 ≤ 2 * P := by
            have hn := hHnorm h hh
            simpa [qI, idealNorm] using hn
          have hpowHle : qI h.1 ^ δ₁ ≤ (2 * P) ^ δ₁ :=
            Real.rpow_le_rpow hqhpos.le hqH hδ₁.le
          have hrootBound :
              Real.sqrt (∑' d : S.ExtIdeal, rowTerm h d) ≤ Bmass := by
            dsimp [Bmass]
            calc
              _ ≤ Cfixed * qI h.1 ^ δ₁ * Real.log (2 * R0) ^ 2 *
                    (D0 + R0) ^ (1 / 2 : ℝ) * (D0 * R0) ^ (δ₂ / 2) := hfixed'
              _ ≤ Cfixed * (2 * P) ^ δ₁ * Real.log (2 * R0) ^ 2 *
                    (D0 + R0) ^ (1 / 2 : ℝ) * (D0 * R0) ^ (δ₂ / 2) := by
                have hfactor : 0 ≤ Cfixed * Real.log (2 * R0) ^ 2 *
                    (D0 + R0) ^ (1 / 2 : ℝ) * (D0 * R0) ^ (δ₂ / 2) := by positivity
                nlinarith [mul_le_mul_of_nonneg_right hpowHle hfactor]
              _ = Bmass := by ring
          have hmassNonneg : 0 ≤ ∑' d : S.ExtIdeal, rowTerm h d := by
            apply tsum_nonneg
            intro d
            dsimp [rowTerm]
            split_ifs <;> positivity
          have hsq : (Real.sqrt (∑' d : S.ExtIdeal, rowTerm h d)) ^ 2 ≤ Bmass ^ 2 :=
            (sq_le_sq₀ (Real.sqrt_nonneg _) hBmassNonneg).2 hrootBound
          have hsumSq := hsq
          rw [Real.sq_sqrt hmassNonneg] at hsumSq
          rw [hmassTsum]
          exact hsumSq
        · have hmassZero : ∀ d ∈ Dset, massTerm (h, d) = 0 := by
            intro d hd
            by_cases hlow : P ≤ qI h.1
            · have hhigh : ¬ qI h.1 < 2 * P := by
                intro hhigh
                exact hrange ⟨hlow, hhigh⟩
              simp [massTerm, hpowH, hlow, hhigh]
            · simp [massTerm, hpowH, hlow]
          rw [Finset.sum_eq_zero hmassZero]
          positivity
      have hsumHBound :
          (∑ h ∈ Hset, ∑ d ∈ Dset, massTerm (h, d)) ≤
            (Hset.card : ℝ) * Bmass ^ 2 := by
        calc
          _ ≤ ∑ h ∈ Hset, Bmass ^ 2 :=
            Finset.sum_le_sum fun h hh => hinnerBound h hh
          _ = (Hset.card : ℝ) * Bmass ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
      have hsumCardBound :
          (Hset.card : ℝ) * Bmass ^ 2 ≤ Cpow * P ^ (1 / 2 : ℝ) * Bmass ^ 2 :=
        mul_le_mul_of_nonneg_right hHcard (sq_nonneg Bmass)
      calc
        reflectionMass R true υ P D0 Z δ = ∑ hd ∈ Kset, massTerm hd := hmassEq
        _ = ∑ h ∈ Hset, ∑ d ∈ Dset, massTerm (h, d) := hproduct
        _ ≤ (Hset.card : ℝ) * Bmass ^ 2 := hsumHBound
        _ ≤ Cpow * P ^ (1 / 2 : ℝ) * Bmass ^ 2 := hsumCardBound
        _ = Cpow * Cfixed ^ 2 * 2 ^ (2 * δ₁) *
              P ^ (1 / 2 + 2 * δ₁) * Real.log (2 * R0) ^ 4 *
                (D0 + R0) * (D0 * R0) ^ δ₂ := by
          rw [hBmassSq]
          have hPpos : 0 < P := by linarith
          rw [Real.rpow_add hPpos]
          ring
        _ = C * P ^ (1 / 2 + 2 * δ₁) * Real.log (2 * R0) ^ 4 *
              (D0 + R0) * (D0 * R0) ^ δ₂ := by dsimp [C]; ring

private lemma rf_log_four_absorb {x β : ℝ} (hβ : 0 < β) (hx : 1 ≤ x) :
    Real.log x ^ 4 ≤ ((β / 4) ^ 4)⁻¹ * x ^ β := by
  let γ : ℝ := β / 4
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hlog := Real.log_le_rpow_div (by linarith : 0 ≤ x) hγ
  have hpowExp : Real.rpow x γ ^ 4 = x ^ β := by
    calc
      Real.rpow x γ ^ 4 = Real.rpow x (γ * 4) :=
        (Real.rpow_mul_natCast (by linarith : 0 ≤ x) γ 4).symm
      _ = x ^ β := by congr 1 <;> dsimp [γ] <;> ring
  calc
    Real.log x ^ 4 ≤ (Real.rpow x γ / γ) ^ 4 := by
      have hlognonneg : 0 ≤ Real.log x := Real.log_nonneg hx
      exact pow_le_pow_left₀ hlognonneg hlog 4
    _ = x ^ β / γ ^ 4 := by rw [div_pow, hpowExp]
    _ = ((β / 4) ^ 4)⁻¹ * x ^ β := by dsimp [γ]; ring

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
  constructor
  · intro ε hε
    let η : ℝ := min 1 (ε / 16)
    have hη : 0 < η := by dsimp [η]; exact lt_min (by norm_num) (by positivity)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηε : η ≤ ε / 16 := min_le_right _ _
    refine ⟨η, η, η, η, hη, hη, hη, hη, ?_⟩
    have hM : M0 = 1033 / 1000 := by norm_num [M0, a, b]
    rw [hM]
    have hηsq : η ^ 2 ≤ η := by nlinarith
    nlinarith
  · intro C0 δ δ₃ hC0 hδ hδ₃
    let E : ℝ := 2 * M0 - 1 + δ
    let β : ℝ := δ₃ / E
    let K₀ : ℝ := 16 * C0 ^ 2
    let Clog : ℝ := ((β / 4) ^ 4)⁻¹ * K₀ ^ β
    let C : ℝ := 9 + 8 * C0 ^ 3 + C0 + (C0 + C0 ^ 2) + Clog
    have hM0 : 1 < M0 := by norm_num [M0, a, b]
    have hE : 0 < E := by dsimp [E]; linarith
    have hβ : 0 < β := by dsimp [β]; exact div_pos hδ₃ hE
    have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
    have hClog : 0 < Clog := by dsimp [Clog]; positivity
    have hC : 0 < C := by dsimp [C]; positivity
    have hC8 : 8 ≤ C := by dsimp [C]; nlinarith [hC0, hClog]
    have hCcube : 8 * C0 ^ 3 ≤ C := by dsimp [C]; nlinarith [hC0, hClog]
    have hC0' : C0 ≤ C := by dsimp [C]; nlinarith [hC0, hClog]
    have hCsum : C0 + C0 ^ 2 ≤ C := by dsimp [C]; nlinarith [hC0, hClog]
    have hClog' : Clog ≤ C := by dsimp [C]; nlinarith [hC0, hClog]
    refine ⟨C, hC, ?_⟩
    intro P D0 Z hP hD0 hZ hPD
    dsimp only
    let R0 : ℝ := reflectionColumnCutoff P D0 Z δ
    have hPpos : 0 < P := by linarith
    have hDpos : 0 < D0 := by linarith
    have hZpos : 0 < Z := by linarith
    have hZδ : 1 ≤ Z ^ δ := Real.one_le_rpow (by linarith) hδ.le
    have hZδpos : 0 < Z ^ δ := Real.rpow_pos_of_pos hZpos δ
    have hDposB : 0 ≤ D0 ^ 2 * P / Z := by positivity
    have hR0formula : R0 = 8 * Z ^ δ * (D0 ^ 2 * P / Z) := by
      dsimp [R0, reflectionColumnCutoff, reflectionColumnLength]
      ring
    have hdivPow (e : ℝ) : Z ^ e / Z = Z ^ (e - 1) := by
      calc
        Z ^ e / Z = Z ^ e * Z ^ (-1 : ℝ) := by rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        _ = Z ^ (e + (-1 : ℝ)) := by rw [← Real.rpow_add hZpos]
        _ = Z ^ (e - 1) := by congr 1 <;> ring
    have hdivPowMul (A e : ℝ) : A * Z ^ e / Z = A * Z ^ (e - 1) := by
      calc
        A * Z ^ e / Z = A * (Z ^ e / Z) := by ring
        _ = A * Z ^ (e - 1) := by rw [hdivPow]
    have hPDsquare : (P * D0) ^ 2 ≤ C0 ^ 2 * Z ^ (2 * M0) := by
      have hbase : P * D0 ≤ C0 * Z ^ M0 := hPD
      have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ P * D0) hbase 2
      calc
        (P * D0) ^ 2 ≤ (C0 * Z ^ M0) ^ 2 := hpow
        _ = C0 ^ 2 * Z ^ (2 * M0) := by
          rw [mul_pow]
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hZpos.le]
          congr 1 <;> ring
    have hPbound : P ≤ C0 * Z ^ M0 := by
      calc
        P = P * 1 := by ring
        _ ≤ P * D0 := mul_le_mul_of_nonneg_left hD0 hPpos.le
        _ ≤ C0 * Z ^ M0 := hPD
    have hP2 : P ≤ P ^ 2 := by
      calc
        P = P * 1 := by ring
        _ ≤ P * P := mul_le_mul_of_nonneg_left hP hPpos.le
        _ = P ^ 2 := by ring
    have hP3 : P ≤ P ^ 3 := by
      calc
        P = P * 1 := by ring
        _ ≤ P * P ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith [hP2]) hPpos.le
        _ = P ^ 3 := by ring
    have hD3P : D0 ^ 3 * P ≤ (P * D0) ^ 3 := by
      calc
        D0 ^ 3 * P ≤ D0 ^ 3 * P ^ 3 := mul_le_mul_of_nonneg_left hP3 (by positivity)
        _ = (P * D0) ^ 3 := by ring
    have hPDcube : (P * D0) ^ 3 ≤ C0 ^ 3 * Z ^ (3 * M0) := by
      have hbase : P * D0 ≤ C0 * Z ^ M0 := hPD
      have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ P * D0) hbase 3
      calc
        (P * D0) ^ 3 ≤ (C0 * Z ^ M0) ^ 3 := hpow
        _ = C0 ^ 3 * Z ^ (3 * M0) := by
          rw [mul_pow]
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hZpos.le]
          congr 1 <;> ring
    have hD3Pbound : D0 ^ 3 * P ≤ C0 ^ 3 * Z ^ (3 * M0) := hD3P.trans hPDcube
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · calc
        D0 + R0 = D0 + 8 * Z ^ δ * (D0 ^ 2 * P / Z) := by rw [hR0formula]
        _ ≤ 8 * Z ^ δ * D0 + 8 * Z ^ δ * (D0 ^ 2 * P / Z) := by
          have hscale : D0 ≤ Z ^ δ * D0 := by
            calc
              D0 = 1 * D0 := by ring
              _ ≤ Z ^ δ * D0 := mul_le_mul_of_nonneg_right hZδ hDpos.le
          have hscale' : Z ^ δ * D0 ≤ 8 * Z ^ δ * D0 := by
            nlinarith [mul_nonneg hZδpos.le hDpos.le]
          exact add_le_add_left (hscale.trans hscale') _
        _ = 8 * Z ^ δ * (D0 + D0 ^ 2 * P / Z) := by ring
        _ ≤ C * Z ^ δ * (D0 + D0 ^ 2 * P / Z) := by
          calc
            8 * Z ^ δ * (D0 + D0 ^ 2 * P / Z) =
                8 * (Z ^ δ * (D0 + D0 ^ 2 * P / Z)) := by ring
            _ ≤ C * (Z ^ δ * (D0 + D0 ^ 2 * P / Z)) :=
              mul_le_mul_of_nonneg_right hC8 (mul_nonneg hZδpos.le (add_nonneg hDpos.le hDposB))
            _ = C * Z ^ δ * (D0 + D0 ^ 2 * P / Z) := by ring
    · have hD2P : D0 ^ 2 * P ≤ (P * D0) ^ 2 := by
        calc
          D0 ^ 2 * P ≤ D0 ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_left hP2 (by positivity)
          _ = (P * D0) ^ 2 := by ring
      have hB : D0 ^ 2 * P / Z ≤ C0 ^ 2 * Z ^ (2 * M0 - 1) := by
        calc
          D0 ^ 2 * P / Z ≤ (P * D0) ^ 2 / Z := div_le_div_of_nonneg_right hD2P hZpos.le
          _ ≤ C0 ^ 2 * Z ^ (2 * M0) / Z := div_le_div_of_nonneg_right hPDsquare hZpos.le
          _ = C0 ^ 2 * Z ^ (2 * M0 - 1) := by rw [hdivPowMul]
      have hD3Pdiv : D0 ^ 3 * P / Z ≤ C0 ^ 3 * Z ^ (3 * M0 - 1) := by
        calc
          D0 ^ 3 * P / Z ≤ C0 ^ 3 * Z ^ (3 * M0) / Z := div_le_div_of_nonneg_right hD3Pbound hZpos.le
          _ = C0 ^ 3 * Z ^ (3 * M0 - 1) := by rw [hdivPowMul]
      calc
        D0 * R0 = 8 * Z ^ δ * (D0 ^ 3 * P / Z) := by rw [hR0formula]; ring
        _ ≤ 8 * Z ^ δ * (C0 ^ 3 * Z ^ (3 * M0 - 1)) :=
          mul_le_mul_of_nonneg_left hD3Pdiv (by positivity)
        _ = 8 * C0 ^ 3 * (Z ^ δ * Z ^ (3 * M0 - 1)) := by ring
        _ = 8 * C0 ^ 3 * Z ^ (3 * M0 - 1 + δ) := by
          rw [← Real.rpow_add hZpos]
          congr 1 <;> ring
        _ ≤ C * Z ^ (3 * M0 - 1 + δ) :=
          mul_le_mul_of_nonneg_right hCcube (Real.rpow_nonneg hZpos.le _)
    · calc
        P ≤ C0 * Z ^ M0 := hPbound
        _ ≤ C * Z ^ M0 := mul_le_mul_of_nonneg_right hC0' (Real.rpow_nonneg hZpos.le M0)
    · intro hR0
      have hD2P : D0 ^ 2 * P ≤ (P * D0) ^ 2 := by
        calc
          D0 ^ 2 * P ≤ D0 ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_left hP2 (by positivity)
          _ = (P * D0) ^ 2 := by ring
      have hB : D0 ^ 2 * P / Z ≤ C0 ^ 2 * Z ^ (2 * M0 - 1) := by
        calc
          D0 ^ 2 * P / Z ≤ (P * D0) ^ 2 / Z := div_le_div_of_nonneg_right hD2P hZpos.le
          _ ≤ C0 ^ 2 * Z ^ (2 * M0) / Z := div_le_div_of_nonneg_right hPDsquare hZpos.le
          _ = C0 ^ 2 * Z ^ (2 * M0 - 1) := by rw [hdivPowMul]
      have hR0bound : R0 ≤ 8 * C0 ^ 2 * Z ^ E := by
        rw [hR0formula]
        calc
          8 * Z ^ δ * (D0 ^ 2 * P / Z) ≤ 8 * Z ^ δ * (C0 ^ 2 * Z ^ (2 * M0 - 1)) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
          _ = 8 * C0 ^ 2 * (Z ^ δ * Z ^ (2 * M0 - 1)) := by ring
          _ = 8 * C0 ^ 2 * Z ^ E := by
            rw [← Real.rpow_add hZpos]
            congr 1
            dsimp [E]
            ring
      have hy : 1 ≤ 2 * R0 := by nlinarith [hR0]
      have hypos : 0 < 2 * R0 := by linarith
      have hKbound : 2 * R0 ≤ K₀ * Z ^ E := by
        calc
          2 * R0 ≤ 16 * C0 ^ 2 * Z ^ E := by nlinarith [hR0bound]
          _ = K₀ * Z ^ E := by rfl
      have hpower : (2 * R0) ^ β ≤ K₀ ^ β * Z ^ δ₃ := by
        calc
          (2 * R0) ^ β ≤ (K₀ * Z ^ E) ^ β := Real.rpow_le_rpow hypos.le hKbound hβ.le
          _ = K₀ ^ β * Z ^ δ₃ := by
            rw [Real.mul_rpow hK₀.le (by positivity), ← Real.rpow_mul hZpos.le]
            congr 1
            dsimp [β]
            field_simp
      have hcoef : 0 ≤ ((β / 4) ^ 4)⁻¹ := by positivity
      have hpowerScaled : ((β / 4) ^ 4)⁻¹ * (2 * R0) ^ β ≤ Clog * Z ^ δ₃ := by
        calc
          ((β / 4) ^ 4)⁻¹ * (2 * R0) ^ β ≤
              ((β / 4) ^ 4)⁻¹ * (K₀ ^ β * Z ^ δ₃) :=
            mul_le_mul_of_nonneg_left hpower hcoef
          _ = Clog * Z ^ δ₃ := by dsimp [Clog]; ring
      calc
        Real.log (2 * R0) ^ 4 ≤ ((β / 4) ^ 4)⁻¹ * (2 * R0) ^ β :=
          rf_log_four_absorb hβ hy
        _ ≤ Clog * Z ^ δ₃ := hpowerScaled
        _ ≤ C * Z ^ δ₃ := mul_le_mul_of_nonneg_right hClog' (Real.rpow_nonneg (by linarith) δ₃)
    · have hsqrt : Real.sqrt P ≤ P := (Real.sqrt_le_self_iff).2 (Or.inr hP)
      have hterm₁ : Real.sqrt P * D0 ≤ P * D0 := mul_le_mul_of_nonneg_right hsqrt hDpos.le
      have hterm₂ : Real.sqrt P * (D0 ^ 2 * P / Z) ≤ P * (D0 ^ 2 * P / Z) :=
        mul_le_mul_of_nonneg_right hsqrt hDposB
      have hexp : M0 ≤ 2 * M0 - 1 := by linarith [hM0]
      have hPterm : P * D0 ≤ C0 * Z ^ (2 * M0 - 1) := by
        calc
          P * D0 ≤ C0 * Z ^ M0 := hPD
          _ ≤ C0 * Z ^ (2 * M0 - 1) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) hC0.le
      have hP2term : P * (D0 ^ 2 * P / Z) ≤ C0 ^ 2 * Z ^ (2 * M0 - 1) := by
        calc
          P * (D0 ^ 2 * P / Z) = (P * D0) ^ 2 / Z := by ring
          _ ≤ C0 ^ 2 * Z ^ (2 * M0) / Z := div_le_div_of_nonneg_right hPDsquare hZpos.le
          _ = C0 ^ 2 * Z ^ (2 * M0 - 1) := by rw [hdivPowMul]
      calc
        P ^ (1 / 2 : ℝ) * (D0 + D0 ^ 2 * P / Z) =
            Real.sqrt P * D0 + Real.sqrt P * (D0 ^ 2 * P / Z) := by rw [Real.sqrt_eq_rpow]; ring
        _ ≤ P * D0 + P * (D0 ^ 2 * P / Z) := add_le_add hterm₁ hterm₂
        _ ≤ (C0 + C0 ^ 2) * Z ^ (2 * M0 - 1) := by
          nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ Z) (2 * M0 - 1)]
        _ ≤ C * Z ^ (2 * M0 - 1) :=
          mul_le_mul_of_nonneg_right hCsum (Real.rpow_nonneg (by linarith) (2 * M0 - 1))
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
  intro h t d c ν hdecomp
  rcases hdecomp with ⟨ε, hν⟩
  let u : UnitSix S := unitSixClass S ε
  have hepsClass : unitSixClass S (R.sheets.eps u) = unitSixClass S ε := by
    simpa [u] using R.sheets.eps_class u
  have hclass : unitSixClass S ε = unitSixClass S (R.sheets.eps u) :=
    hepsClass.symm
  have hmem : ε / R.sheets.eps u ∈ Gamma S :=
    (QuotientGroup.eq_iff_div_mem).mp (by simpa [unitSixClass] using hclass)
  let γ : Gamma S := ⟨ε / R.sheets.eps u, hmem⟩
  have hεUS : ε = γ.1 * R.sheets.eps u := by
    dsimp [γ]
    exact (div_mul_cancel _ _).symm
  have hεF : (ε : Fˣ) = (γ.1 : Fˣ) * (R.sheets.eps u : Fˣ) :=
    congrArg (fun x : S.US => (x : Fˣ)) hεUS
  let tail : Fˣ :=
    (bc.gen t.a * bc.gen (R.exterior.ofSqf c) * bc.gen t.n ^ 3) /
      (bc.gen d * bc.gen t.f) ^ 2
  have hνtail : ν = (ε : Fˣ) * tail := by
    calc
      ν = ((ε : Fˣ) * bc.gen t.a * bc.gen (R.exterior.ofSqf c) *
          bc.gen t.n ^ 3) / (bc.gen d * bc.gen t.f) ^ 2 := hν
      _ = (ε : Fˣ) * tail := by
        dsimp [tail]
        rw [show (ε : Fˣ) * bc.gen t.a * bc.gen (R.exterior.ofSqf c) *
            bc.gen t.n ^ 3 = (ε : Fˣ) *
              (bc.gen t.a * bc.gen (R.exterior.ofSqf c) * bc.gen t.n ^ 3) by group]
        exact mul_div_assoc _ _ _
  refine ⟨(u, γ), ?_, ?_⟩
  · rw [hν]
    rw [hεF]
  · intro ug' hEq
    rcases ug' with ⟨u', γ'⟩
    have hEqTail : ν = ((γ'.1 : Fˣ) * (R.sheets.eps u' : Fˣ)) * tail := by
      calc
        ν = ((γ'.1 : Fˣ) * (R.sheets.eps u' : Fˣ) * bc.gen t.a *
            bc.gen (R.exterior.ofSqf c) * bc.gen t.n ^ 3) /
            (bc.gen d * bc.gen t.f) ^ 2 := hEq
        _ = ((γ'.1 : Fˣ) * (R.sheets.eps u' : Fˣ)) * tail := by
          dsimp [tail]
          rw [show (γ'.1 : Fˣ) * (R.sheets.eps u' : Fˣ) * bc.gen t.a *
              bc.gen (R.exterior.ofSqf c) * bc.gen t.n ^ 3 =
                ((γ'.1 : Fˣ) * (R.sheets.eps u' : Fˣ)) *
                  (bc.gen t.a * bc.gen (R.exterior.ofSqf c) * bc.gen t.n ^ 3) by group]
          exact mul_div_assoc _ _ _
    have hεeqF : (ε : Fˣ) = (γ'.1 : Fˣ) * (R.sheets.eps u' : Fˣ) :=
      mul_right_cancel (hνtail.symm.trans hEqTail)
    have hεeqUS : ε = γ'.1 * R.sheets.eps u' := by
      exact Subtype.ext hεeqF
    have hratio : ε / R.sheets.eps u' = γ'.1 := by
      rw [hεeqUS]
      simp
    have hclass' : unitSixClass S ε = unitSixClass S (R.sheets.eps u') := by
      apply (QuotientGroup.eq_iff_div_mem).2
      rw [hratio]
      exact γ'.property
    have hu' : u' = u := by
      dsimp [u]
      exact (hclass'.trans (R.sheets.eps_class u')).symm
    have hεeqUS' : ε = γ'.1 * R.sheets.eps u := by
      simpa [hu'] using hεeqUS
    have hγ : γ.1 = γ'.1 := mul_right_cancel (hεUS.symm.trans hεeqUS')
    apply Prod.ext
    · exact hu'
    · apply Subtype.ext
      exact hγ.symm
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

section ReflectionAssemblyResults
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)

private lemma rf_diagR_closed (D : FieldData F) : IsClosed (S.diagR : Set S.FS) := by
  let f : S.R →+ S.FS := {
    toFun := fun x => S.diag (x : F)
    map_zero' := by simp [SData.diag]
    map_add' := by intro x y; simp [SData.diag]
  }
  have hRange : (f.range : Set S.FS) = S.diagR := by
    rfl
  have hdisc := (SData.diagR_discrete_cocompact S D).1
  have hdisc' : IsDiscrete (f.range : Set S.FS) := by
    simpa [hRange] using hdisc
  rw [← hRange]
  exact f.range.isClosed_of_isDiscrete hdisc'

private lemma rf_reflectionRowFiber_finite (K : Set S.FSˣ) (hK : IsCompact K)
    (t : S.FSˣ) (Z : ℝ) (hZ : 0 < Z) (I : S.ExtIdeal) :
    (reflectionRowFiber D S K t Z hZ I).Finite := by
  classical
  let scale := S.ell D (Real.rpow Z M0) (Real.rpow_pos_of_pos hZ M0)
  let B : Set S.FS := (fun y : S.FSˣ => scale * ((t * y : S.FSˣ) : S.FS)) '' K
  have hmap : Continuous (fun y : S.FSˣ => scale * ((t * y : S.FSˣ) : S.FS)) := by fun_prop
  have hB : IsCompact B := hK.image hmap
  have hclosed : IsClosed (S.diagR : Set S.FS) := rf_diagR_closed (D := D) (S := S)
  have hdisc : IsDiscrete (B ∩ S.diagR : Set S.FS) :=
    (SData.diagR_discrete_cocompact S D).1 |>.mono (fun _ hx => hx.2)
  have htarget : (B ∩ S.diagR : Set S.FS).Finite :=
    (hB.inter_right hclosed).finite hdisc
  let e : ReflectionRow S → S.FS := fun r => S.diag (r.m : F)
  have hmaps : Set.MapsTo e (reflectionRowFiber D S K t Z hZ I) (B ∩ S.diagR) := by
    intro r hr
    rcases hr.1 with ⟨y, hy, hbox⟩
    constructor
    · refine ⟨y, hy, ?_⟩
      simpa [e, B, scale] using hbox.symm
    · exact ⟨r.m, rfl⟩
  have hinj : Set.InjOn e (reflectionRowFiber D S K t Z hZ I) := by
    intro r hr s hs hrs
    apply reflection_row_element_injective (S := S)
    exact S.diag.injective hrs
  exact htarget.of_injOn hmaps hinj

private lemma rf_reflection_mass_finite_sum (retained : Bool) (υ : UnitSix S)
    (P D0 Z δ : ℝ) (hP : 1 ≤ P) (hD0 : 1 ≤ D0) (hZ : 2 ≤ Z) :
    reflectionMass R retained υ P D0 Z δ =
      ∑ hd ∈ ((bridgeNormFinset S (2 * P)).filter (fun h => IsPowerful h.1)).product
          (bridgeNormFinset S (2 * D0)),
        if IsPowerful hd.1.1 ∧ P ≤ qI hd.1.1 ∧ qI hd.1.1 < 2 * P ∧
            D0 ≤ qI hd.2.1 ∧ qI hd.2.1 < 2 * D0 then
          ‖splitReflection R retained υ hd.1 hd.2 Z (reflectionColumnCutoff P D0 Z δ)‖ ^ 2
        else 0 := by
  classical
  let Hset : Finset S.ExtIdeal :=
    (bridgeNormFinset S (2 * P)).filter (fun h => IsPowerful h.1)
  let Dset : Finset S.ExtIdeal := bridgeNormFinset S (2 * D0)
  let Kset : Finset (S.ExtIdeal × S.ExtIdeal) := Hset.product Dset
  have hFinP := a2_bridge_COUNT_finite S (2 * P) (by positivity)
  have hFinD := a2_bridge_COUNT_finite S (2 * D0) (by positivity)
  have hmemH (h : S.ExtIdeal) (hh : IsPowerful h.1) (hhi : qI h.1 < 2 * P) :
      h ∈ Hset := by
    apply Finset.mem_filter.mpr
    constructor
    · exact (hFinP.2 h).mpr (by simpa [qI, idealNorm] using hhi.le)
    · exact hh
  have hmemD (d : S.ExtIdeal) (hhi : qI d.1 < 2 * D0) : d ∈ Dset :=
    (hFinD.2 d).mpr (by simpa [qI, idealNorm] using hhi.le)
  have hzero (hd : S.ExtIdeal × S.ExtIdeal) (hnot : hd ∉ Kset) :
      (if IsPowerful hd.1.1 ∧ P ≤ qI hd.1.1 ∧ qI hd.1.1 < 2 * P ∧
          D0 ≤ qI hd.2.1 ∧ qI hd.2.1 < 2 * D0 then
        ‖splitReflection R retained υ hd.1 hd.2 Z (reflectionColumnCutoff P D0 Z δ)‖ ^ 2
      else 0) = 0 := by
    by_cases hc : IsPowerful hd.1.1 ∧ P ≤ qI hd.1.1 ∧ qI hd.1.1 < 2 * P ∧
        D0 ≤ qI hd.2.1 ∧ qI hd.2.1 < 2 * D0
    · rcases hc with ⟨hh, _, hhi, _, dhi⟩
      have hm : hd.1 ∈ Hset := hmemH hd.1 hh hhi
      have hdmem : hd.2 ∈ Dset := hmemD hd.2 dhi
      exact (hnot (Finset.mem_product.mpr ⟨hm, hdmem⟩)).elim
    · simp [hc]
  unfold reflectionMass
  change (∑' hd : S.ExtIdeal × S.ExtIdeal,
      if IsPowerful hd.1.1 ∧ P ≤ qI hd.1.1 ∧ qI hd.1.1 < 2 * P ∧
          D0 ≤ qI hd.2.1 ∧ qI hd.2.1 < 2 * D0 then
        ‖splitReflection R retained υ hd.1 hd.2 Z (reflectionColumnCutoff P D0 Z δ)‖ ^ 2
      else 0) = _
  exact tsum_eq_sum hzero

private lemma rf_reflection_row_split (r : ReflectionRow S) (Z R0 : ℝ) (hZ : 0 < Z) :
    Bm D S A ϑ (cgen R) (r.m : F) Z =
      splitReflection R true (rowClass R r) r.h r.d Z R0 +
        splitReflection R false (rowClass R r) r.h r.d Z R0 := by
  classical
  have hpair := lem_reflection_quadratic_pairing (R := R) r Z hZ
  let term := fun p : FrozenIndex R r.h × Bd.B × Bd.B × S.SqfExtIdeal =>
    reflectedTerm R (rowClass R r) r.h r.d Z p
  let cut := fun p : FrozenIndex R r.h × Bd.B × Bd.B × S.SqfExtIdeal =>
    qI p.1.a.1 * qI p.2.2.2.1 * qI p.1.n.1 ^ 3 ≤ R0
  have hret : Summable (fun p => if cut p then term p else 0) :=
    hpair.1.of_norm_bounded (fun p => by
      by_cases hp : cut p <;> simp [hp, term])
  have htail : Summable (fun p => if cut p then 0 else term p) :=
    hpair.1.of_norm_bounded (fun p => by
      by_cases hp : cut p <;> simp [hp, term])
  have hparts :
      (∑' p, if cut p then term p else 0) +
        (∑' p, if cut p then 0 else term p) = ∑' p, term p := by
    rw [← hret.tsum_add htail]
    apply tsum_congr
    intro p
    by_cases hp : cut p <;> simp [hp]
  have hdc : Squarefree r.d.1 ∧ IsCoprime r.d.1 r.h.1 :=
    ⟨r.d_squarefree, r.coprime.symm⟩
  have hsplitRet : splitReflection R true (rowClass R r) r.h r.d Z R0 =
      ∑' p, if cut p then term p else 0 := by
    unfold splitReflection
    rw [if_pos hdc]
    apply tsum_congr
    intro p
    by_cases hp : cut p <;> simp [cut, hp, term]
  have hsplitTail : splitReflection R false (rowClass R r) r.h r.d Z R0 =
      ∑' p, if cut p then 0 else term p := by
    unfold splitReflection
    rw [if_pos hdc]
    apply tsum_congr
    intro p
    by_cases hp : cut p <;> simp [cut, hp, term]
  calc
    Bm D S A ϑ (cgen R) (r.m : F) Z = ∑' p, term p := by
      simpa [term] using hpair.2
    _ = (∑' p, if cut p then term p else 0) +
          (∑' p, if cut p then 0 else term p) := hparts.symm
    _ = _ := by rw [hsplitRet, hsplitTail]

end ReflectionAssemblyResults

section ReflectionAssemblyMain
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)

private lemma rf_ext_norm_dyad_bounds (I : S.ExtIdeal) :
    ((2 ^ Nat.log 2 (Ideal.absNorm I.1) : ℕ) : ℝ) ≤ qI I.1 ∧
      qI I.1 < ((2 ^ (Nat.log 2 (Ideal.absNorm I.1) + 1) : ℕ) : ℝ) := by
  have hI : I.1 ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using I.2.1
  have hnormpos : 0 < Ideal.absNorm I.1 :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr
        (by simpa [Ideal.zero_eq_bot] using hI)⟩
  have hn : Ideal.absNorm I.1 ≠ 0 := Nat.ne_of_gt hnormpos
  constructor
  · change ((2 ^ Nat.log 2 (Ideal.absNorm I.1) : ℕ) : ℝ) ≤
      (Ideal.absNorm I.1 : ℝ)
    exact_mod_cast Nat.pow_log_le_self 2 hn
  · change (Ideal.absNorm I.1 : ℝ) <
      ((2 ^ (Nat.log 2 (Ideal.absNorm I.1) + 1) : ℕ) : ℝ)
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _

set_option maxHeartbeats 8000000 in
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
  classical
  intro K T hK hT hTnorm ε hε
  letI : Fintype (UnitSix S) := R.sheets.unitSixFinite
  obtain ⟨δ, δ₁, δ₂, δ₃, hδ, hδ₁, hδ₂, hδ₃, hLoss⟩ :=
    (rf_assembly_scale_bounds).1 ε hε
  obtain ⟨c₁, c₂, Cmult, hc₁, hc₂, hCmult, K', hK', hK'norm, hElem⟩ :=
    rf_element_to_ideal D S H Bd bc K T hK hT hTnorm
  let C₀ : ℝ := c₂
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith [hc₁, hc₂]
  obtain ⟨Cscale, hCscale, hScale⟩ :=
    (rf_assembly_scale_bounds).2 C₀ δ δ₃ hC₀ hδ hδ₃
  obtain ⟨Cret, hCret, hRetMass⟩ := rf_retained_mass R δ δ₁ δ₂ hδ hδ₁ hδ₂
  let σ : ℝ := 3 / 4
  have hσ : 1 / 2 < σ := by norm_num [σ]
  have hM0 : 1 < M0 := by norm_num [M0, a, b]
  let N : ℝ := (2 + 2 * M0 * δ₁ + 2 * σ * (2 * M0 - 1)) / (2 * δ) + σ
  have hNval : 2 * δ * (N - σ) = 2 + 2 * M0 * δ₁ + 2 * σ * (2 * M0 - 1) := by
    dsimp [N]
    field_simp [ne_of_gt hδ]
    ring
  have hσN : σ < N := by
    have h2δ : 0 < 2 * δ := by positivity
    have hdiff : 0 < 2 * δ * (N - σ) := by
      rw [hNval]
      have hMpos : 0 < M0 := by linarith
      have hσpos : 0 < σ := by norm_num [σ]
      have hfactor : 0 < 2 * M0 - 1 := by linarith
      positivity
    have hNminus : 0 < N - σ := (mul_pos_iff_of_pos_left h2δ).mp hdiff
    linarith
  have hTailExp : 1 + 2 * M0 * δ₁ + 2 * σ * (2 * M0 - 1) < 2 * δ * (N - σ) := by
    rw [hNval]
    linarith
  obtain ⟨Ctail, hCtail, hTailMass⟩ :=
    rf_tail_negligible R C₀ δ δ₁ σ N 1 hC₀ hδ hδ₁ hσ hσN (by norm_num) hTailExp
  let M : ℝ := (max 1 ⌊Cmult⌋₊ : ℕ)
  let U : ℝ := Fintype.card (UnitSix S)
  let CscaleFactor : ℝ := Cscale ^ (2 * δ₁) * Cscale * Cscale * Cscale ^ δ₂
  let CretFinal : ℝ := Cret * CscaleFactor
  let Cfinal : ℝ := 2 * M * U * (CretFinal + Ctail)
  have hM : 0 < M := by dsimp [M]; positivity
  have hU : 0 < U := by
    dsimp [U]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨unitSixClass S 1⟩)
  have hCfinal : 0 < Cfinal := by
    dsimp [Cfinal]
    positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro Z hZ P D₀ hP hD₀ t ht rows hinj hrows
  have hZpos : 0 < Z := by linarith
  by_cases hrowsEmpty : rows = ∅
  · simp [hrowsEmpty]
    positivity
  · have hrowsNE : rows.Nonempty := Finset.nonempty_iff_ne_empty.mpr hrowsEmpty
    obtain ⟨r₀, hr₀⟩ := hrowsNE
    have hrow₀ := hrows r₀ hr₀
    have hElem₀ := hElem Z hZ t ht r₀ hrow₀.1
    have hNormIdeal : qI r₀.ideal.1 ≤ C₀ * Z ^ M0 := by
      simpa [C₀, qI, idealNorm] using hElem₀.2.1
    have hqMul : qI r₀.h.1 * qI r₀.d.1 = qI (r₀.h.1 * r₀.d.1) := by
      simp [qI, map_mul]
    have hqHpos := rf_qI_pos_ge_one r₀.h.1 r₀.h.2.1
    have hPD : P * D₀ ≤ C₀ * Z ^ M0 := by
      calc
        P * D₀ ≤ qI r₀.h.1 * qI r₀.d.1 :=
          mul_le_mul hrow₀.2.1 hrow₀.2.2.2.1 (by linarith [hD₀])
            (le_of_lt hqHpos.1)
        _ = qI (r₀.h.1 * r₀.d.1) := hqMul
        _ = qI r₀.ideal.1 := by rw [← r₀.factorization]
        _ ≤ C₀ * Z ^ M0 := hNormIdeal
    let R₀ : ℝ := reflectionColumnCutoff P D₀ Z δ
    let shape : ℝ := D₀ + D₀ ^ 2 * P / Z
    let key : ReflectionRow S → UnitSix S × (S.ExtIdeal × S.ExtIdeal) :=
      fun r => (rowClass R r, (r.h, r.d))
    let keys : Finset (UnitSix S × (S.ExtIdeal × S.ExtIdeal)) := rows.image key
    let Hset : Finset S.ExtIdeal :=
      (bridgeNormFinset S (2 * P)).filter (fun h => IsPowerful h.1)
    let Dset : Finset S.ExtIdeal := bridgeNormFinset S (2 * D₀)
    let Kset : Finset (S.ExtIdeal × S.ExtIdeal) := Hset.product Dset
    let keysAll : Finset (UnitSix S × (S.ExtIdeal × S.ExtIdeal)) := Finset.univ.product Kset
    let massTerm (retained : Bool) (k : UnitSix S × (S.ExtIdeal × S.ExtIdeal)) : ℝ :=
      if IsPowerful k.2.1.1 ∧ P ≤ qI k.2.1.1 ∧ qI k.2.1.1 < 2 * P ∧
          D₀ ≤ qI k.2.2.1 ∧ qI k.2.2.1 < 2 * D₀ then
        ‖splitReflection R retained k.1 k.2.1 k.2.2 Z R₀‖ ^ 2
      else 0
    let retVal (k : UnitSix S × (S.ExtIdeal × S.ExtIdeal)) : ℝ :=
      ‖splitReflection R true k.1 k.2.1 k.2.2 Z R₀‖ ^ 2
    let tailVal (k : UnitSix S × (S.ExtIdeal × S.ExtIdeal)) : ℝ :=
      ‖splitReflection R false k.1 k.2.1 k.2.2 Z R₀‖ ^ 2
    have hCountP := a2_bridge_COUNT_finite S (2 * P) (by positivity)
    have hCountD := a2_bridge_COUNT_finite S (2 * D₀) (by positivity)
    have hmemH (h : S.ExtIdeal) (hh : IsPowerful h.1) (hhi : qI h.1 < 2 * P) :
        h ∈ Hset := by
      apply Finset.mem_filter.mpr
      constructor
      · exact (hCountP.2 h).mpr (by simpa [qI, idealNorm] using hhi.le)
      · exact hh
    have hmemD (d : S.ExtIdeal) (hhi : qI d.1 < 2 * D₀) : d ∈ Dset :=
      (hCountD.2 d).mpr (by simpa [qI, idealNorm] using hhi.le)
    have hkeysMaps : (rows : Set (ReflectionRow S)).MapsTo key keys := by
      intro r hr
      exact Finset.mem_image_of_mem key hr
    have hkeysSub : keys ⊆ keysAll := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨r, hr, rfl⟩
      have hdyad := (hrows r hr).2
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_univ _
      · apply Finset.mem_product.mpr
        exact ⟨hmemH r.h r.h_powerful hdyad.2.1,
          hmemD r.d hdyad.2.2.2⟩
    have hkeysRetMass (k : UnitSix S × (S.ExtIdeal × S.ExtIdeal)) (hk : k ∈ keys) :
        retVal k = massTerm true k := by
      rcases Finset.mem_image.mp hk with ⟨r, hr, rfl⟩
      have hdyad := (hrows r hr).2
      have hc : IsPowerful r.h.1 ∧ P ≤ qI r.h.1 ∧ qI r.h.1 < 2 * P ∧
          D₀ ≤ qI r.d.1 ∧ qI r.d.1 < 2 * D₀ := ⟨r.h_powerful, hdyad⟩
      simp [retVal, massTerm, key, hc]
    have hkeysTailMass (k : UnitSix S × (S.ExtIdeal × S.ExtIdeal)) (hk : k ∈ keys) :
        tailVal k = massTerm false k := by
      rcases Finset.mem_image.mp hk with ⟨r, hr, rfl⟩
      have hdyad := (hrows r hr).2
      have hc : IsPowerful r.h.1 ∧ P ≤ qI r.h.1 ∧ qI r.h.1 < 2 * P ∧
          D₀ ≤ qI r.d.1 ∧ qI r.d.1 < 2 * D₀ := ⟨r.h_powerful, hdyad⟩
      simp [tailVal, massTerm, key, hc]
    have hretAll :
        (∑ k ∈ keysAll, massTerm true k) =
          ∑ υ ∈ (Finset.univ : Finset (UnitSix S)), reflectionMass R true υ P D₀ Z δ := by
      calc
        _ = ∑ υ ∈ (Finset.univ : Finset (UnitSix S)),
              ∑ hd ∈ Kset, massTerm true (υ, hd) := by
          simpa [keysAll] using
            (Finset.sum_product (Finset.univ : Finset (UnitSix S)) Kset
              (massTerm true))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro υ hυ
          simpa [massTerm, Hset, Dset, Kset] using
            (rf_reflection_mass_finite_sum R true υ P D₀ Z δ hP hD₀ hZ).symm
    have htailAll :
        (∑ k ∈ keysAll, massTerm false k) =
          ∑ υ ∈ (Finset.univ : Finset (UnitSix S)), reflectionMass R false υ P D₀ Z δ := by
      calc
        _ = ∑ υ ∈ (Finset.univ : Finset (UnitSix S)),
              ∑ hd ∈ Kset, massTerm false (υ, hd) := by
          simpa [keysAll] using
            (Finset.sum_product (Finset.univ : Finset (UnitSix S)) Kset
              (massTerm false))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro υ hυ
          simpa [massTerm, Hset, Dset, Kset] using
            (rf_reflection_mass_finite_sum R false υ P D₀ Z δ hP hD₀ hZ).symm
    let grp (k : UnitSix S × (S.ExtIdeal × S.ExtIdeal)) : Finset (ReflectionRow S) :=
      rows.filter (fun r => key r = k)
    have hgroupCard (k : UnitSix S × (S.ExtIdeal × S.ExtIdeal)) (hk : k ∈ keys) :
        ((grp k).card : ℝ) ≤ M := by
      rcases Finset.mem_image.mp hk with ⟨r₀, hr₀, hkEq⟩
      have hFiber := rf_reflectionRowFiber_finite (D := D) (S := S)
        K hK t Z (by linarith) r₀.ideal
      have hFiberBound :
          (reflectionRowFiber D S K t Z (by linarith) r₀.ideal).ncard ≤ ⌊Cmult⌋₊ := by
        exact (hElem Z hZ t ht r₀ (hrows r₀ hr₀).1).2.2.2
      have hgrpSub :
          (grp k : Set (ReflectionRow S)) ⊆ reflectionRowFiber D S K t Z (by linarith) r₀.ideal := by
        intro r hr
        have hrf := Finset.mem_filter.mp hr
        have hEqKey : key r = key r₀ := hrf.2.trans hkEq.symm
        have hEqHD : (r.h, r.d) = (r₀.h, r₀.d) := by
          simpa [key] using congrArg Prod.snd hEqKey
        have hh : r.h = r₀.h := congrArg Prod.fst hEqHD
        have hd : r.d = r₀.d := congrArg Prod.snd hEqHD
        have hIdeal : r.ideal = r₀.ideal := by
          apply Subtype.ext
          rw [r.factorization, r₀.factorization, hh, hd]
        change InReflectionBox D S K t Z (by linarith) r ∧ r.ideal = r₀.ideal
        exact ⟨(hrows r hrf.1).1, hIdeal⟩
      have hgrpSubFinset : grp k ⊆ hFiber.toFinset := by
        intro r hr
        exact hFiber.mem_toFinset.mpr (hgrpSub hr)
      have hgrpNat : (grp k).card ≤ ⌊Cmult⌋₊ := by
        calc
          (grp k).card ≤ hFiber.toFinset.card := Finset.card_le_card hgrpSubFinset
          _ = (reflectionRowFiber D S K t Z (by linarith) r₀.ideal).ncard :=
            (Set.ncard_eq_toFinset_card _ hFiber).symm
          _ ≤ ⌊Cmult⌋₊ := hFiberBound
      have hgrpMax : (grp k).card ≤ max 1 ⌊Cmult⌋₊ :=
        le_trans hgrpNat (Nat.le_max_right 1 ⌊Cmult⌋₊)
      change ((grp k).card : ℝ) ≤ ((max 1 ⌊Cmult⌋₊ : ℕ) : ℝ)
      exact_mod_cast hgrpMax
    have hgrpRet (k : UnitSix S × (S.ExtIdeal × S.ExtIdeal)) :
        (∑ r ∈ grp k, retVal (key r)) ≤ M * retVal k := by
      have hconst : ∀ r ∈ grp k, retVal (key r) = retVal k := by
        intro r hr
        exact congrArg retVal (Finset.mem_filter.mp hr).2
      rw [Finset.sum_congr rfl hconst]
      rw [Finset.sum_const, nsmul_eq_mul]
      by_cases hk : k ∈ keys
      · exact mul_le_mul_of_nonneg_right (hgroupCard k hk) (by positivity)
      · have hz : grp k = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro r hr
          exact hk (Finset.mem_image.mpr ⟨r, (Finset.mem_filter.mp hr).1,
            (Finset.mem_filter.mp hr).2⟩)
        simp [hz]
        positivity
    have hgrpTail (k : UnitSix S × (S.ExtIdeal × S.ExtIdeal)) :
        (∑ r ∈ grp k, tailVal (key r)) ≤ M * tailVal k := by
      have hconst : ∀ r ∈ grp k, tailVal (key r) = tailVal k := by
        intro r hr
        exact congrArg tailVal (Finset.mem_filter.mp hr).2
      rw [Finset.sum_congr rfl hconst]
      rw [Finset.sum_const, nsmul_eq_mul]
      by_cases hk : k ∈ keys
      · exact mul_le_mul_of_nonneg_right (hgroupCard k hk) (by positivity)
      · have hz : grp k = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro r hr
          exact hk (Finset.mem_image.mpr ⟨r, (Finset.mem_filter.mp hr).1,
            (Finset.mem_filter.mp hr).2⟩)
        simp [hz]
        positivity
    have hretRowDecomp :
        (∑ r ∈ rows, retVal (key r)) =
          ∑ k ∈ keys, ∑ r ∈ grp k, retVal (key r) := by
      exact (Finset.sum_fiberwise_of_maps_to hkeysMaps _).symm
    have htailRowDecomp :
        (∑ r ∈ rows, tailVal (key r)) =
          ∑ k ∈ keys, ∑ r ∈ grp k, tailVal (key r) := by
      exact (Finset.sum_fiberwise_of_maps_to hkeysMaps _).symm
    have hretRows :
        (∑ r ∈ rows, retVal (key r)) ≤ M * (∑ k ∈ keys, retVal k) := by
      calc
        _ = ∑ k ∈ keys, ∑ r ∈ grp k, retVal (key r) := hretRowDecomp
        _ ≤ ∑ k ∈ keys, M * retVal k := Finset.sum_le_sum fun k hk => hgrpRet k
        _ = M * (∑ k ∈ keys, retVal k) := by rw [Finset.mul_sum]
    have htailRows :
        (∑ r ∈ rows, tailVal (key r)) ≤ M * (∑ k ∈ keys, tailVal k) := by
      calc
        _ = ∑ k ∈ keys, ∑ r ∈ grp k, tailVal (key r) := htailRowDecomp
        _ ≤ ∑ k ∈ keys, M * tailVal k := Finset.sum_le_sum fun k hk => hgrpTail k
        _ = M * (∑ k ∈ keys, tailVal k) := by rw [Finset.mul_sum]
    have hretKeys :
        (∑ k ∈ keys, retVal k) ≤
          ∑ υ ∈ (Finset.univ : Finset (UnitSix S)), reflectionMass R true υ P D₀ Z δ := by
      calc
        _ = ∑ k ∈ keys, massTerm true k := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hkeysRetMass k hk
        _ ≤ ∑ k ∈ keysAll, massTerm true k :=
          Finset.sum_le_sum_of_subset_of_nonneg hkeysSub (by
            intro k hk hnot
            dsimp [massTerm]
            split_ifs <;> positivity)
        _ = _ := hretAll
    have htailKeys :
        (∑ k ∈ keys, tailVal k) ≤
          ∑ υ ∈ (Finset.univ : Finset (UnitSix S)), reflectionMass R false υ P D₀ Z δ := by
      calc
        _ = ∑ k ∈ keys, massTerm false k := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hkeysTailMass k hk
        _ ≤ ∑ k ∈ keysAll, massTerm false k :=
          Finset.sum_le_sum_of_subset_of_nonneg hkeysSub (by
            intro k hk hnot
            dsimp [massTerm]
            split_ifs <;> positivity)
        _ = _ := htailAll
    have hretMassBound (υ : UnitSix S) :
        reflectionMass R true υ P D₀ Z δ ≤
          CretFinal * Z ^ ε * P ^ (1 / 2 : ℝ) * shape := by
      have hretData := hRetMass υ P D₀ Z hP hD₀ hZ
      by_cases hsmall : R₀ < 1
      · rw [hretData.1 hsmall]
        dsimp [CretFinal, CscaleFactor, shape]
        positivity
      · have hlarge : 1 ≤ R₀ := le_of_not_gt hsmall
        obtain ⟨hDsum, hDprod, hPbound, hLog, hShape⟩ :=
          hScale P D₀ Z hP hD₀ hZ hPD
        have hLog' : Real.log (2 * R₀) ^ 4 ≤ Cscale * Z ^ δ₃ := by
          apply hLog
          exact hlarge
        have hPexp : P ^ (2 * δ₁) ≤ Cscale ^ (2 * δ₁) * Z ^ (2 * M0 * δ₁) := by
          calc
            P ^ (2 * δ₁) ≤ (Cscale * Z ^ M0) ^ (2 * δ₁) :=
              Real.rpow_le_rpow (by positivity) hPbound (by positivity)
            _ = Cscale ^ (2 * δ₁) * Z ^ (2 * M0 * δ₁) := by
              rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
              congr 1
              ring
        have hDprodexp : (D₀ * R₀) ^ δ₂ ≤
            Cscale ^ δ₂ * Z ^ ((3 * M0 - 1 + δ) * δ₂) := by
          calc
            (D₀ * R₀) ^ δ₂ ≤ (Cscale * Z ^ (3 * M0 - 1 + δ)) ^ δ₂ :=
              Real.rpow_le_rpow (by positivity) hDprod hδ₂.le
            _ = Cscale ^ δ₂ * Z ^ ((3 * M0 - 1 + δ) * δ₂) := by
              rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
        have hscaleProduct :
            P ^ (2 * δ₁) * Real.log (2 * R₀) ^ 4 * (D₀ + R₀) * (D₀ * R₀) ^ δ₂ ≤
              (Cscale ^ (2 * δ₁) * Z ^ (2 * M0 * δ₁)) *
                (Cscale * Z ^ δ₃) * (Cscale * Z ^ δ * shape) *
                  (Cscale ^ δ₂ * Z ^ ((3 * M0 - 1 + δ) * δ₂)) := by
          gcongr
        let Eloss : ℝ := δ + 2 * M0 * δ₁ + (3 * M0 - 1 + δ) * δ₂ + δ₃
        have hEloss : Eloss < ε := by dsimp [Eloss]; linarith [hLoss]
        have hZprod :
            Z ^ (2 * M0 * δ₁) * Z ^ δ₃ * Z ^ δ *
              Z ^ ((3 * M0 - 1 + δ) * δ₂) = Z ^ Eloss := by
          calc
            _ = Z ^ (2 * M0 * δ₁ + δ₃) * Z ^ δ *
                Z ^ ((3 * M0 - 1 + δ) * δ₂) := by rw [← Real.rpow_add hZpos]
            _ = Z ^ (2 * M0 * δ₁ + δ₃ + δ) *
                Z ^ ((3 * M0 - 1 + δ) * δ₂) := by rw [← Real.rpow_add hZpos]
            _ = Z ^ (2 * M0 * δ₁ + δ₃ + δ + (3 * M0 - 1 + δ) * δ₂) :=
              by rw [← Real.rpow_add hZpos]
            _ = Z ^ Eloss := by congr 1; dsimp [Eloss]; ring
        have hfactorEq :
            (Cscale ^ (2 * δ₁) * Z ^ (2 * M0 * δ₁)) *
                (Cscale * Z ^ δ₃) * (Cscale * Z ^ δ * shape) *
                  (Cscale ^ δ₂ * Z ^ ((3 * M0 - 1 + δ) * δ₂)) =
              CscaleFactor * Z ^ Eloss * shape := by
          dsimp [CscaleFactor]
          calc
            _ = (Cscale ^ (2 * δ₁) * Cscale * Cscale * Cscale ^ δ₂) *
                  (Z ^ (2 * M0 * δ₁) * Z ^ δ₃ * Z ^ δ *
                    Z ^ ((3 * M0 - 1 + δ) * δ₂)) * shape := by ring
            _ = _ := by rw [hZprod]
        have hZexp : Z ^ Eloss ≤ Z ^ ε :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hEloss.le
        have hRaw := hretData.2 hlarge
        calc
          reflectionMass R true υ P D₀ Z δ ≤
              Cret * P ^ (1 / 2 + 2 * δ₁) * Real.log (2 * R₀) ^ 4 *
                (D₀ + R₀) * (D₀ * R₀) ^ δ₂ := hRaw
          _ = Cret * P ^ (1 / 2 : ℝ) *
                (P ^ (2 * δ₁) * Real.log (2 * R₀) ^ 4 *
                  (D₀ + R₀) * (D₀ * R₀) ^ δ₂) := by
              rw [Real.rpow_add (by positivity)]
              ring
          _ ≤ Cret * P ^ (1 / 2 : ℝ) *
                ((Cscale ^ (2 * δ₁) * Z ^ (2 * M0 * δ₁)) *
                  (Cscale * Z ^ δ₃) * (Cscale * Z ^ δ * shape) *
                    (Cscale ^ δ₂ * Z ^ ((3 * M0 - 1 + δ) * δ₂))) := by
              exact mul_le_mul_of_nonneg_left hscaleProduct (by positivity)
          _ = CretFinal * Z ^ Eloss * P ^ (1 / 2 : ℝ) * shape := by
              rw [hfactorEq]
              dsimp [CretFinal]
              ring
          _ ≤ CretFinal * Z ^ ε * P ^ (1 / 2 : ℝ) * shape := by
              have hfac : 0 ≤ CretFinal * P ^ (1 / 2 : ℝ) * shape := by positivity
              calc
                CretFinal * Z ^ Eloss * P ^ (1 / 2 : ℝ) * shape =
                    (CretFinal * P ^ (1 / 2 : ℝ) * shape) * Z ^ Eloss := by ring
                _ ≤ (CretFinal * P ^ (1 / 2 : ℝ) * shape) * Z ^ ε :=
                  mul_le_mul_of_nonneg_left hZexp hfac
                _ = CretFinal * Z ^ ε * P ^ (1 / 2 : ℝ) * shape := by ring
    have htailMassBound (υ : UnitSix S) :
        reflectionMass R false υ P D₀ Z δ ≤
          Ctail * Z ^ ε * P ^ (1 / 2 : ℝ) * shape := by
      have hraw := hTailMass υ P D₀ Z hP hD₀ hZ hPD
      have hZexp : Z ^ (-1 : ℝ) ≤ Z ^ ε :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith : (-1 : ℝ) ≤ ε)
      have hDshape : D₀ ≤ shape := by
        dsimp [shape]
        exact le_add_of_nonneg_right (by positivity)
      calc
        reflectionMass R false υ P D₀ Z δ ≤
            Ctail * Z ^ (-1 : ℝ) * P ^ (1 / 2 : ℝ) * D₀ := hraw
        _ ≤ Ctail * Z ^ ε * P ^ (1 / 2 : ℝ) * shape := by
          gcongr
    have hretTotal :
        (∑ υ ∈ (Finset.univ : Finset (UnitSix S)), reflectionMass R true υ P D₀ Z δ) ≤
          U * (CretFinal * Z ^ ε * P ^ (1 / 2 : ℝ) * shape) := by
      calc
        _ ≤ ∑ υ ∈ (Finset.univ : Finset (UnitSix S)),
              CretFinal * Z ^ ε * P ^ (1 / 2 : ℝ) * shape :=
          Finset.sum_le_sum fun υ hυ => hretMassBound υ
        _ = _ := by simp [U, Finset.sum_const, nsmul_eq_mul]
    have htailTotal :
        (∑ υ ∈ (Finset.univ : Finset (UnitSix S)), reflectionMass R false υ P D₀ Z δ) ≤
          U * (Ctail * Z ^ ε * P ^ (1 / 2 : ℝ) * shape) := by
      calc
        _ ≤ ∑ υ ∈ (Finset.univ : Finset (UnitSix S)),
              Ctail * Z ^ ε * P ^ (1 / 2 : ℝ) * shape :=
          Finset.sum_le_sum fun υ hυ => htailMassBound υ
        _ = _ := by simp [U, Finset.sum_const, nsmul_eq_mul]
    have hpoint (r : ReflectionRow S) (hr : r ∈ rows) :
        ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2 ≤
          2 * retVal (key r) + 2 * tailVal (key r) := by
      have hsplit := rf_reflection_row_split R r Z R₀ hZpos
      let x := splitReflection R true (rowClass R r) r.h r.d Z R₀
      let y := splitReflection R false (rowClass R r) r.h r.d Z R₀
      calc
        _ = ‖x + y‖ ^ 2 := by rw [hsplit]
        _ ≤ (‖x‖ + ‖y‖) ^ 2 := by gcongr; exact norm_add_le x y
        _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
          nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    have hpointSum :
        (∑ r ∈ rows, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2) ≤
          2 * (∑ r ∈ rows, retVal (key r)) +
            2 * (∑ r ∈ rows, tailVal (key r)) := by
      calc
        _ ≤ ∑ r ∈ rows, (2 * retVal (key r) + 2 * tailVal (key r)) :=
          Finset.sum_le_sum fun r hr => hpoint r hr
        _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]
    have hmain :
        (∑ r ∈ rows, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2) ≤
          2 * M * U * (CretFinal + Ctail) * Z ^ ε * P ^ (1 / 2 : ℝ) * shape := by
      calc
        _ ≤ 2 * (∑ r ∈ rows, retVal (key r)) +
              2 * (∑ r ∈ rows, tailVal (key r)) := hpointSum
        _ ≤ 2 * (M * (∑ k ∈ keys, retVal k)) +
              2 * (M * (∑ k ∈ keys, tailVal k)) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hretRows (by norm_num))
            (mul_le_mul_of_nonneg_left htailRows (by norm_num))
        _ = 2 * M * ((∑ k ∈ keys, retVal k) + (∑ k ∈ keys, tailVal k)) := by ring
        _ ≤ 2 * M * ((∑ υ ∈ (Finset.univ : Finset (UnitSix S)),
              reflectionMass R true υ P D₀ Z δ) +
            (∑ υ ∈ (Finset.univ : Finset (UnitSix S)),
              reflectionMass R false υ P D₀ Z δ)) := by
          gcongr
        _ ≤ 2 * M * (U * (CretFinal * Z ^ ε * P ^ (1 / 2 : ℝ) * shape) +
              U * (Ctail * Z ^ ε * P ^ (1 / 2 : ℝ) * shape)) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hretTotal htailTotal)
            (by positivity)
        _ = 2 * M * U * (CretFinal + Ctail) * Z ^ ε * P ^ (1 / 2 : ℝ) * shape := by
          ring
    simpa [Cfinal, R₀, shape] using hmain

/-- rf:reflection-assembly, 04:1198–1228. Compact shape and translation sets are fixed first. -/
theorem rf_reflection_assembly : ∀ K T : Set S.FSˣ, IsCompact K → IsCompact T →
  (∀ t ∈ T, S.absS (t : S.FS) = 1) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ Z : ℝ, ∀ hZ : 2 ≤ Z, ∀ t ∈ T, ∀ rows : Finset (ReflectionRow S),
      Set.InjOn (fun r : ReflectionRow S => (r.m : F)) (↑rows : Set (ReflectionRow S)) →
      (∀ r ∈ rows, InReflectionBox D S K t Z (by linarith) r) →
      (∑ r ∈ rows, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2) ≤ C * Z ^ (2 * M0 - 1 + ε) := by
  classical
  intro K T hK hT hTnorm ε hε
  letI : Fintype (UnitSix S) := R.sheets.unitSixFinite
  obtain ⟨Cdyad, hCdyad, hDyadic⟩ :=
    rf_reflection_dyadic_assembly R K T hK hT hTnorm (ε / 2) (by linarith)
  obtain ⟨c₁, C₀, Cmult, hc₁, hC₀upper, hCmult, K', hK', hK'norm, hElement⟩ :=
    rf_element_to_ideal D S H Bd bc K T hK hT hTnorm
  have hC₀ : 0 < C₀ := by linarith [hc₁, hC₀upper]
  obtain ⟨Cscale, hCscale, hScale⟩ :=
    (rf_assembly_scale_bounds).2 C₀ (ε / 8) (ε / 8) hC₀ (by linarith) (by linarith)
  let β : ℝ := ε / (4 * M0)
  have hM0 : 1 < M0 := by norm_num [M0, a, b]
  have hβ : 0 < β := by dsimp [β]; positivity
  let Clog : ℝ := 1 / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hClog : 0 < Clog := by dsimp [Clog]; positivity
  let Cabs : ℝ := ((β / 4) ^ 4)⁻¹
  let Cnum : ℝ := Clog ^ 2 * (1 + Cabs * (2 * C₀) ^ β)
  let Cbin : ℝ := Cdyad * Cscale
  let Cfinal : ℝ := Cnum * Cbin
  have hCnum : 0 < Cnum := by dsimp [Cnum, Cabs]; positivity
  have hCbin : 0 < Cbin := by dsimp [Cbin]; positivity
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro Z hZ t ht rows hinj hrows
  have hZpos : 0 < Z := by linarith
  by_cases hrowsEmpty : rows = ∅
  · simp [hrowsEmpty]
    positivity
  · have hrowsNE : rows.Nonempty := Finset.nonempty_iff_ne_empty.mpr hrowsEmpty
    obtain ⟨r₀, hr₀⟩ := hrowsNE
    let X : ℝ := C₀ * Z ^ M0
    have hX : 1 ≤ X := by
      have hnormone : 1 ≤ qI r₀.ideal.1 :=
        (rf_qI_pos_ge_one r₀.ideal.1 r₀.ideal.2.1).2
      have hnormup : qI r₀.ideal.1 ≤ X := by
        have h := hElement Z hZ t ht r₀ (hrows r₀ hr₀)
        simpa [X, qI, idealNorm] using h.2.1
      exact hnormone.trans hnormup
    have hxbase : 1 ≤ 2 * X := by dsimp [X]; nlinarith [hX]
    have hlog4 := rf_log_four_absorb hβ hxbase
    let N : ℕ := Nat.log 2 ⌊X⌋₊
    let dyad (r : ReflectionRow S) : ℕ × ℕ :=
      (Nat.log 2 (Ideal.absNorm r.h.1), Nat.log 2 (Ideal.absNorm r.d.1))
    let bins : Finset (ℕ × ℕ) := rows.image dyad
    let allBins : Finset (ℕ × ℕ) := Finset.range (N + 1) ×ˢ Finset.range (N + 1)
    let rowsBin (b : ℕ × ℕ) : Finset (ReflectionRow S) :=
      rows.filter (fun r => dyad r = b)
    let countLog : ℝ := Clog * Real.log (2 * X)
    have hcountLog : ((N + 1 : ℕ) : ℝ) ≤ countLog := by
      simpa [N, countLog, Clog] using rf_retained_natlog_count X hX
    have hZpower : 1 ≤ Z ^ (ε / 4) := Real.one_le_rpow (by linarith) (by positivity)
    have hRealLog : 0 ≤ Real.log (2 * X) := Real.log_nonneg hxbase
    have hLogSq : Real.log (2 * X) ^ 2 ≤
        (1 + Cabs * (2 * C₀) ^ β) * Z ^ (ε / 4) := by
      have hPowerX : (2 * X) ^ β = (2 * C₀) ^ β * Z ^ (ε / 4) := by
        have hXeq : 2 * X = (2 * C₀) * Z ^ M0 := by dsimp [X]; ring
        rw [hXeq, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
        congr 1
        dsimp [β]
        field_simp [ne_of_gt (by linarith : 0 < M0)]
      calc
        Real.log (2 * X) ^ 2 ≤ 1 + Real.log (2 * X) ^ 4 := by
          nlinarith [sq_nonneg (Real.log (2 * X) ^ 2 - 1)]
        _ ≤ 1 + Cabs * (2 * X) ^ β := by
          have hcoef : 0 ≤ Cabs := by dsimp [Cabs]; positivity
          nlinarith [hlog4, hcoef]
        _ = 1 + Cabs * (2 * C₀) ^ β * Z ^ (ε / 4) := by rw [hPowerX]; ring
        _ ≤ (1 + Cabs * (2 * C₀) ^ β) * Z ^ (ε / 4) := by
          nlinarith [mul_nonneg (by positivity : 0 ≤ Cabs * (2 * C₀) ^ β) (sub_nonneg.mpr hZpower)]
    have hbinsMaps : (rows : Set (ReflectionRow S)).MapsTo dyad bins := by
      intro r hr
      exact Finset.mem_image_of_mem dyad hr
    have hrowNormUpper (r : ReflectionRow S) (hr : r ∈ rows) :
        qI r.h.1 ≤ X ∧ qI r.d.1 ≤ X := by
      have hElem := hElement Z hZ t ht r (hrows r hr)
      have hIup : qI r.ideal.1 ≤ X := by simpa [X, qI, idealNorm] using hElem.2.1
      have hqMul : qI r.h.1 * qI r.d.1 = qI r.ideal.1 := by
        calc
          qI r.h.1 * qI r.d.1 = qI (r.h.1 * r.d.1) := by simp [qI, map_mul]
          _ = qI r.ideal.1 := by rw [← r.factorization]
      have hqh1 : 1 ≤ qI r.h.1 := (rf_qI_pos_ge_one r.h.1 r.h.2.1).2
      have hqd1 : 1 ≤ qI r.d.1 := (rf_qI_pos_ge_one r.d.1 r.d.2.1).2
      constructor
      · calc
          qI r.h.1 = qI r.h.1 * 1 := by ring
          _ ≤ qI r.h.1 * qI r.d.1 := mul_le_mul_of_nonneg_left hqd1 (by positivity)
          _ = qI r.ideal.1 := hqMul
          _ ≤ X := hIup
      · calc
          qI r.d.1 = 1 * qI r.d.1 := by ring
          _ ≤ qI r.h.1 * qI r.d.1 := mul_le_mul_of_nonneg_right hqh1 (by positivity)
          _ = qI r.ideal.1 := hqMul
          _ ≤ X := hIup
    have hrowNormNat (r : ReflectionRow S) (hr : r ∈ rows) :
        Ideal.absNorm r.h.1 ≤ ⌊X⌋₊ ∧ Ideal.absNorm r.d.1 ≤ ⌊X⌋₊ := by
      have hreal := hrowNormUpper r hr
      constructor
      · apply (Nat.le_floor_iff (by positivity : 0 ≤ X)).2
        simpa [qI] using hreal.1
      · apply (Nat.le_floor_iff (by positivity : 0 ≤ X)).2
        simpa [qI] using hreal.2
    have hbinsSub : bins ⊆ allBins := by
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨r, hr, rfl⟩
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_range.mpr
        exact Nat.lt_succ_of_le (by
          simpa [dyad, N] using Nat.log_mono_right (hrowNormNat r hr).1)
      · apply Finset.mem_range.mpr
        exact Nat.lt_succ_of_le (by
          simpa [dyad, N] using Nat.log_mono_right (hrowNormNat r hr).2)
    have hbinsCard : (bins.card : ℝ) ≤ Cnum * Z ^ (ε / 2) := by
      have hcardNat : bins.card ≤ (N + 1) * (N + 1) := by
        calc
          bins.card ≤ allBins.card := Finset.card_le_card hbinsSub
          _ = (N + 1) * (N + 1) := by simp [allBins, Finset.card_product]
      have hcardReal : (bins.card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
        calc
          (bins.card : ℝ) ≤ (((N + 1) * (N + 1) : ℕ) : ℝ) := by exact_mod_cast hcardNat
          _ = ((N + 1 : ℕ) : ℝ) ^ 2 := by norm_cast; ring
      have hcountSquared : (bins.card : ℝ) ≤ Clog ^ 2 * Real.log (2 * X) ^ 2 := by
        calc
          (bins.card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := hcardReal
          _ ≤ countLog ^ 2 := pow_le_pow_left₀ (by positivity) hcountLog 2
          _ = Clog ^ 2 * Real.log (2 * X) ^ 2 := by simp [countLog, mul_pow]
      calc
        (bins.card : ℝ) ≤ Clog ^ 2 * Real.log (2 * X) ^ 2 := hcountSquared
        _ ≤ Cnum * Z ^ (ε / 4) := by
          dsimp [Cnum]
          calc
            Clog ^ 2 * Real.log (2 * X) ^ 2 ≤
                Clog ^ 2 * ((1 + Cabs * (2 * C₀) ^ β) * Z ^ (ε / 4)) :=
              mul_le_mul_of_nonneg_left hLogSq (sq_nonneg Clog)
            _ = Clog ^ 2 * (1 + Cabs * (2 * C₀) ^ β) * Z ^ (ε / 4) := by ring
        _ ≤ Cnum * Z ^ (ε / 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hsumDecomp :
        (∑ r ∈ rows, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2) =
          ∑ b ∈ bins, ∑ r ∈ rowsBin b, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2 := by
      exact (Finset.sum_fiberwise_of_maps_to hbinsMaps _).symm
    have hbinBound (b : ℕ × ℕ) (hb : b ∈ bins) :
        (∑ r ∈ rowsBin b, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2) ≤
          Cbin * Z ^ (2 * M0 - 1 + ε / 2) := by
      rcases Finset.mem_image.mp hb with ⟨r₀, hr₀, hbEq⟩
      let P : ℝ := ((2 ^ b.1 : ℕ) : ℝ)
      let Dlen : ℝ := ((2 ^ b.2 : ℕ) : ℝ)
      have hPpos : 1 ≤ P := by
        dsimp [P]
        exact_mod_cast (Nat.one_le_pow b.1 2 (by decide))
      have hDpos : 1 ≤ Dlen := by
        dsimp [Dlen]
        exact_mod_cast (Nat.one_le_pow b.2 2 (by decide))
      have hrowShell (r : ReflectionRow S) (hr : r ∈ rowsBin b) :
          P ≤ qI r.h.1 ∧ qI r.h.1 < 2 * P ∧ Dlen ≤ qI r.d.1 ∧ qI r.d.1 < 2 * Dlen := by
        have hfilter := Finset.mem_filter.mp hr
        have hbinEq : dyad r = b := hfilter.2
        have hi : Nat.log 2 (Ideal.absNorm r.h.1) = b.1 := by
          simpa [dyad] using congrArg Prod.fst hbinEq
        have hj : Nat.log 2 (Ideal.absNorm r.d.1) = b.2 := by
          simpa [dyad] using congrArg Prod.snd hbinEq
        have hsh := rf_ext_norm_dyad_bounds r.h
        have hsd := rf_ext_norm_dyad_bounds r.d
        have hPupper : ((2 ^ (b.1 + 1) : ℕ) : ℝ) = 2 * P := by
          have hn : 2 ^ (b.1 + 1) = 2 * 2 ^ b.1 := by rw [pow_succ]; ring
          dsimp [P]
          exact_mod_cast hn
        have hDupper : ((2 ^ (b.2 + 1) : ℕ) : ℝ) = 2 * Dlen := by
          have hn : 2 ^ (b.2 + 1) = 2 * 2 ^ b.2 := by rw [pow_succ]; ring
          dsimp [Dlen]
          exact_mod_cast hn
        constructor
        · simpa [P, hi] using hsh.1
        · constructor
          · simpa [hi, hPupper] using hsh.2
          · constructor
            · simpa [Dlen, hj] using hsd.1
            · simpa [hj, hDupper] using hsd.2
      have hPD : P * Dlen ≤ X := by
        have hShell := hrowShell r₀ (Finset.mem_filter.mpr ⟨hr₀, by simpa [dyad] using hbEq⟩)
        have hElem₀ := hElement Z hZ t ht r₀ (hrows r₀ hr₀)
        have hIup : qI r₀.ideal.1 ≤ X := by
          simpa [X, qI, idealNorm] using hElem₀.2.1
        have hqMul : qI r₀.h.1 * qI r₀.d.1 = qI r₀.ideal.1 := by
          calc
            qI r₀.h.1 * qI r₀.d.1 = qI (r₀.h.1 * r₀.d.1) := by simp [qI, map_mul]
            _ = qI r₀.ideal.1 := by rw [← r₀.factorization]
        calc
          P * Dlen ≤ qI r₀.h.1 * qI r₀.d.1 :=
            mul_le_mul hShell.1 hShell.2.2.1 (by linarith [hDpos])
              (by linarith [hPpos, hShell.1])
          _ = qI r₀.ideal.1 := hqMul
          _ ≤ X := hIup
      have hInjBin : Set.InjOn (fun r : ReflectionRow S => (r.m : F))
          (↑(rowsBin b) : Set (ReflectionRow S)) := by
        intro r hr s hs heq
        exact hinj (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hs).1 heq
      have hRowsBin : ∀ r ∈ rowsBin b,
          InReflectionBox D S K t Z (by linarith) r ∧
            P ≤ qI r.h.1 ∧ qI r.h.1 < 2 * P ∧ Dlen ≤ qI r.d.1 ∧ qI r.d.1 < 2 * Dlen := by
        intro r hr
        exact ⟨(hrows r (Finset.mem_filter.mp hr).1), hrowShell r hr⟩
      have hDya := hDyadic Z hZ P Dlen hPpos hDpos t ht (rowsBin b) hInjBin hRowsBin
      obtain ⟨hDsum, hDprod, hPbound, hLog, hShape⟩ := hScale P Dlen Z hPpos hDpos hZ hPD
      calc
        (∑ r ∈ rowsBin b, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2) ≤
            Cdyad * Z ^ (ε / 2) * P ^ (1 / 2 : ℝ) *
              (Dlen + Dlen ^ 2 * P / Z) := hDya
        _ ≤ Cdyad * Z ^ (ε / 2) * (Cscale * Z ^ (2 * M0 - 1)) := by
          calc
            _ = (Cdyad * Z ^ (ε / 2)) *
                  (P ^ (1 / 2 : ℝ) * (Dlen + Dlen ^ 2 * P / Z)) := by ring
            _ ≤ (Cdyad * Z ^ (ε / 2)) * (Cscale * Z ^ (2 * M0 - 1)) :=
              mul_le_mul_of_nonneg_left hShape (by positivity)
        _ = Cbin * Z ^ (2 * M0 - 1 + ε / 2) := by
          dsimp [Cbin]
          calc
            Cdyad * Z ^ (ε / 2) * (Cscale * Z ^ (2 * M0 - 1)) =
                Cdyad * Cscale * (Z ^ (ε / 2) * Z ^ (2 * M0 - 1)) := by ring
            _ = Cdyad * Cscale * Z ^ (ε / 2 + (2 * M0 - 1)) := by
              rw [← Real.rpow_add hZpos]
            _ = Cdyad * Cscale * Z ^ (2 * M0 - 1 + ε / 2) := by congr 1 <;> ring
    have hsumBound :
        (∑ r ∈ rows, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2) ≤
          (bins.card : ℝ) * (Cbin * Z ^ (2 * M0 - 1 + ε / 2)) := by
      calc
        _ = ∑ b ∈ bins, ∑ r ∈ rowsBin b,
              ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2 := hsumDecomp
        _ ≤ ∑ b ∈ bins, Cbin * Z ^ (2 * M0 - 1 + ε / 2) :=
          Finset.sum_le_sum fun b hb => hbinBound b hb
        _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
    calc
      (∑ r ∈ rows, ‖Bm D S A ϑ (cgen R) (r.m : F) Z‖ ^ 2) ≤
          Cnum * Z ^ (ε / 2) * (Cbin * Z ^ (2 * M0 - 1 + ε / 2)) := by
        exact hsumBound.trans (mul_le_mul_of_nonneg_right hbinsCard (by positivity))
      _ = Cfinal * Z ^ (2 * M0 - 1 + ε) := by
        dsimp [Cfinal]
        calc
          Cnum * Z ^ (ε / 2) * (Cbin * Z ^ (2 * M0 - 1 + ε / 2)) =
              Cnum * Cbin * (Z ^ (ε / 2) * Z ^ (2 * M0 - 1 + ε / 2)) := by ring
          _ = Cnum * Cbin * Z ^ (ε / 2 + (2 * M0 - 1 + ε / 2)) := by
            rw [← Real.rpow_add hZpos]
          _ = Cnum * Cbin * Z ^ (2 * M0 - 1 + ε) := by congr 1 <;> ring
end ReflectionAssemblyMain

end ArtinPrimitiveRoots.A2
