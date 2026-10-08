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
  sorry
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
