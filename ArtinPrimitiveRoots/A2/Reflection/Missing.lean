import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».All

/-! A2 statement interfaces derived from the design lane. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
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

/-- rf:descent, 04:133–183: automorphy and all four Γ-invariances. -/
theorem rf_descent :
  (∀ r y, digitSum R r false false y = digitSum R r true false y) ∧
  (∀ r (γ : Gamma S) y (minus constant : Bool),
    digitSum R r minus constant (S.diagU (γ.1 : Fˣ) * y) = digitSum R r minus constant y) ∧
  (∀ (γ : Gamma S) y, bCut (Bd := Bd) (S.diagU (γ.1 : Fˣ) * y) = bCut (Bd := Bd) y) ∧
  (∀ u (γ : Gamma S), Lvalue R u (S.diagU (γ.1 : Fˣ)) = 1) := by
  sorry
/-- Fundamental sets are measurable and use the actual diagonal Γ, with unique representatives. -/
def IsFundamentalAt (O : Set S.FS) (l : ℝ) : Prop :=
  MeasurableSet O ∧ (∀ y ∈ O, IsUnit y ∧ S.absS y = l) ∧
  ∀ y : S.FSˣ, S.absS (y : S.FS) = l →
    ∃! γ : Gamma S, ((S.diagU (γ.1 : Fˣ))⁻¹ * y : S.FSˣ).val ∈ O

/-- rf:descent, 04:133-183. The integral identity uses the same sheet measure on the chosen domain. -/
theorem rf_descent_integral :
  ∀ r l, 0 < l → ∀ O, IsFundamentalAt O l →
    ∫ y in O, onUnits (fun y => bCut (Bd := Bd) y * (Lvalue R (rowClass R r) y)⁻¹ *
      digitSum R r false false y) y ∂(R.sheets.sheet l) = thetaAverage R r l := by
  sorry
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
  sorry
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
