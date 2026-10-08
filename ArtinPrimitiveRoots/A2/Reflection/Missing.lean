import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».All
import ArtinPrimitiveRoots.Theta.Assemble

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
private theorem rf_trace_eq_pair_sum_re [IsTotallyComplex F] (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      ∑ w : InfinitePlace F, (w.embedding z + ComplexEmbedding.conjugate w.embedding z) := by
  classical
  have htrace := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := z)
  have hring : (∑ φ : F →+* ℂ, φ z) = ∑ σ : F →ₐ[ℚ] ℂ, σ z := by
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
  have hall : (Algebra.trace ℚ F z : ℂ) = ∑ φ : F →+* ℂ, φ z := by
    rw [hring.symm] at htrace
    exact htrace
  rw [hall]
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun φ : F →+* ℂ => InfinitePlace.mk φ) (f := fun φ => φ z)]
  apply Finset.sum_congr rfl
  intro w hw
  have hmk (φ : F →+* ℂ) : InfinitePlace.mk φ = w ↔
      φ = w.embedding ∨ φ = ComplexEmbedding.conjugate w.embedding := by
    constructor
    · intro h
      rw [← InfinitePlace.mk_embedding w] at h
      have h' := InfinitePlace.mk_eq_iff.mp h
      rcases h' with h' | h'
      · exact Or.inl (by simpa using h')
      · right
        have hc := congrArg ComplexEmbedding.conjugate h'
        simpa using hc
    · intro h
      rw [← InfinitePlace.mk_embedding w]
      apply InfinitePlace.mk_eq_iff.mpr
      rcases h with h | h
      · exact Or.inl (by simpa using h)
      · right
        have hc := congrArg ComplexEmbedding.conjugate h
        simpa using hc
  have hneq : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    apply IsTotallyComplex.complexEmbedding_not_isReal w.embedding
    rw [ComplexEmbedding.isReal_iff]
    exact h.symm
  have hset : Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
      ({w.embedding, ComplexEmbedding.conjugate w.embedding} : Finset (F →+* ℂ)) := by
    ext φ
    simp [hmk]
  change (∑ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), φ z) = _
  rw [hset, Finset.sum_pair hneq]

private theorem rf_trace_eq_two_real_sum [IsTotallyComplex F] (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      (2 : ℂ) * ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ) := by
  rw [rf_trace_eq_pair_sum_re]
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [Finset.mul_sum]

private theorem rf_arch_exp_eq_trace [IsTotallyComplex F] (z : F) :
    (∏ w : InfinitePlace F,
        Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)))) =
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
  rw [← Complex.exp_sum]
  apply congrArg Complex.exp
  calc
    ∑ w : InfinitePlace F, -(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)) =
        -(4 * Real.pi * Complex.I *
          ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ)) := by
            rw [Finset.sum_neg_distrib, Finset.mul_sum]
    _ = -(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)) := by
      rw [rf_trace_eq_two_real_sum]
      ring

private theorem rf_local_additive_phase_congr (v : FinPlace F) (p : Fˣ)
    (hp : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ))
    (a b : 𝓞 F) (hab : a - b ∈ v.asIdeal) :
    A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) =
      A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
  have hvalNum : HeightOneSpectrum.valuation F v ((a : F) - b) ≤
      WithZero.exp (-1 : ℤ) := by
    change v.valuation F (algebraMap (𝓞 F) F (a - b)) ≤ WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    apply (v.intValuation_le_pow_iff_mem (a - b) 1).2
    simpa using hab
  have hvalDiv : HeightOneSpectrum.valuation F v (((a : F) - b) / (p : F)) ≤ 1 := by
    rw [map_div₀, hp]
    have hexpPos : 0 < WithZero.exp (-1 : ℤ) :=
      lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
    exact (div_le_one₀ hexpPos).2 hvalNum
  have hlocal :
      algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F)) ∈
        v.adicCompletionIntegers F := by
    change ((((a : F) - b) / (p : F) : F) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hvalDiv
  have harg : algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F)) =
      algebraMap F (v.adicCompletion F) ((a : F) / (p : F)) -
        algebraMap F (v.adicCompletion F) ((b : F) / (p : F)) := by
    have hF : ((a : F) - b) / (p : F) =
        (a : F) / (p : F) - (b : F) / (p : F) := by
      field_simp [Units.ne_zero p]
    rw [hF, map_sub]
  have hdiv := (A.ψ v).map_sub_eq_div
    (algebraMap F (v.adicCompletion F) ((a : F) / (p : F)))
    (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))
  have hbne : A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) ≠ 0 :=
    (AddChar.val_isUnit (A.ψ v)
      (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))).ne_zero
  calc
    A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) =
        (A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) /
          A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))) *
            A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) :=
      (div_mul_cancel₀ _ hbne).symm
    _ = A.ψ v (algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F))) *
          A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
      rw [← hdiv, ← harg]
    _ = A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
      rw [A.integral v _ hlocal, one_mul]

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

private lemma rf_count_spanSingleton_intValuation (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private lemma rf_count_spanSingleton_eq_neg_log_valuation (v : FinPlace F) (z : F)
    (hz : z ≠ 0) :
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
    rf_count_spanSingleton_intValuation v n hn,
    rf_count_spanSingleton_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn)
      (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private theorem rf_gamma_prime_norm_one (v : FinPlace F) (hv : v ∉ S.Sf)
    (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal) :
    ‖gamma D S A 2 v.asIdeal (p : F)‖ = 1 := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let Q := 𝓞 F ⧸ v.asIdeal
  letI : Field Q := bridgeResidueField v
  letI : Fintype Q := bridgeResidueFintype v
  obtain ⟨χ₁, hχ₁ord, hχ₁⟩ := (a2_bridge_FINITE_CHAR D S A v hv p hp).2.1
  obtain ⟨ψ, hψprim, hψspec⟩ := (a2_bridge_FINITE_CHAR D S A v hv p hp).2.2
  let χ : MulChar Q ℂ := χ₁ ^ 2
  have hχval (x : Q) : χ x = chiPow D v (algebraMap (𝓞 F) F x.out) 2 := by
    change (χ₁ ^ 2) x = chiPow D v (algebraMap (𝓞 F) F x.out) 2
    rw [MulChar.pow_apply' χ₁ (by norm_num : (2 : ℕ) ≠ 0) x]
    by_cases hx : x = 0
    · subst x
      have hres := (a2_bridge_SYMBOL D S).residue_algebraMap v (0 : 𝓞 F)
      simp only [map_zero] at hres
      simp [hχ₁, chiPow, hres]
    · have hres := (a2_bridge_SYMBOL D S).residue_algebraMap v x.out
      have hr : residue v (algebraMap (𝓞 F) F x.out) ≠ 0 := by
        rw [hres, Ideal.Quotient.mk_out]
        exact hx
      rw [hχ₁ x,
        (a2_bridge_SYMBOL D S).chiPow_nonzero v
          (algebraMap (𝓞 F) F x.out) 1 hr,
        (a2_bridge_SYMBOL D S).chiPow_nonzero v
          (algebraMap (𝓞 F) F x.out) 2 hr]
      simp
  have hχne : χ ≠ 1 := by
    intro h
    have hpow : χ₁ ^ 2 = 1 := by simpa [χ] using h
    have hdiv : orderOf χ₁ ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
    rw [hχ₁ord] at hdiv
    norm_num at hdiv
  have hψne : ψ ≠ 1 := by
    intro h
    have hs := hψprim (a := (1 : Q)) (by simp)
    apply hs
    ext x
    simp [h]
  have hψinvprim : (ψ⁻¹).IsPrimitive := AddChar.IsPrimitive.of_ne_one (by
    intro h
    have h' : ψ = 1 := by
      ext x
      have hx := congrArg (fun φ : AddChar Q ℂ => φ x) h
      rw [AddChar.inv_apply'] at hx
      exact inv_eq_one.mp hx
    exact hψne h')
  have hvalP (w : FinPlace F) (hw : w ∉ S.Sf) (hwv : w ≠ v) :
      HeightOneSpectrum.valuation F w (p : F) = 1 := by
    have hcount : FractionalIdeal.count F w
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 0 := by
      calc
        _ = FractionalIdeal.count F w
            (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hp.2.2 w hw
        _ = 0 := FractionalIdeal.count_maximal_coprime F w
          (w := v) hwv.symm
    have hlog : WithZero.log (HeightOneSpectrum.valuation F w (p : F)) = 0 := by
      have h := rf_count_spanSingleton_eq_neg_log_valuation w (p : F) p.ne_zero
      rw [hcount] at h
      simpa only [neg_eq_zero] using h.symm
    have hne : HeightOneSpectrum.valuation F w (p : F) ≠ 0 :=
      (w.valuation F).ne_zero_iff.mpr p.ne_zero
    calc
      HeightOneSpectrum.valuation F w (p : F) =
          WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F w (p : F))) :=
        (WithZero.exp_log hne).symm
      _ = 1 := by simp [hlog]
  have hcountP : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      _ = FractionalIdeal.count F v
          (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hp.2.2 v hv
      _ = 1 := FractionalIdeal.count_self F v
  have hlogP : WithZero.log (HeightOneSpectrum.valuation F v (p : F)) = -1 := by
    have h := rf_count_spanSingleton_eq_neg_log_valuation v (p : F) p.ne_zero
    rw [hcountP] at h
    linarith
  have hvalPV : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ) := by
    have hne : HeightOneSpectrum.valuation F v (p : F) ≠ 0 :=
      (v.valuation F).ne_zero_iff.mpr p.ne_zero
    calc
      HeightOneSpectrum.valuation F v (p : F) =
          WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (p : F))) :=
        (WithZero.exp_log hne).symm
      _ = WithZero.exp (-1 : ℤ) := by rw [hlogP]
  have hSadd (x : Q) :
      S.e A (S.diag (algebraMap (𝓞 F) F x.out / (p : F))) = ψ⁻¹ x := by
    let z : F := algebraMap (𝓞 F) F x.out / (p : F)
    let f : FinPlace F → ℂ := fun w => A.ψ w (algebraMap F (w.adicCompletion F) z)
    have hvalz (w : FinPlace F) (hw : w ∉ S.Sf) (hwv : w ≠ v) :
        HeightOneSpectrum.valuation F w z ≤ 1 := by
      by_cases hx : x.out = 0
      · simp [z, hx]
      have hxval : HeightOneSpectrum.valuation F w
          (algebraMap (𝓞 F) F x.out) ≤ 1 := w.valuation_le_one x.out
      calc
        HeightOneSpectrum.valuation F w z =
            HeightOneSpectrum.valuation F w (algebraMap (𝓞 F) F x.out) /
              HeightOneSpectrum.valuation F w (p : F) := by
                dsimp [z]
                rw [map_div₀]
        _ = HeightOneSpectrum.valuation F w (algebraMap (𝓞 F) F x.out) := by
              rw [hvalP w hw hwv, div_one]
        _ ≤ 1 := hxval
    have hsupport : Function.mulSupport f ⊆
        ((insert v S.Sf : Finset (FinPlace F)) : Set (FinPlace F)) := by
      intro w hw
      simp only [Function.mem_mulSupport] at hw
      by_cases hws : w ∈ S.Sf
      · exact Finset.mem_insert_of_mem hws
      · by_cases hwv : w = v
        · simp [hwv]
        · have hmem : (algebraMap F (w.adicCompletion F) z) ∈
              w.adicCompletionIntegers F := by
            rw [HeightOneSpectrum.mem_adicCompletionIntegers,
              HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
              Algebra.algebraMap_self, RingHom.id_apply,
              w.valuedAdicCompletion_eq_valuation']
            exact hvalz w hws hwv
          exact (hw (A.integral w _ hmem)).elim
    have hfinprod : (∏ᶠ w : FinPlace F, f w) = ∏ w ∈ insert v S.Sf, f w :=
      finprod_eq_prod_of_mulSupport_subset f hsupport
    have hglobal := (A.trivial_on_F z).2
    have hattach : (∏ w : S.Sf, f w) = ∏ w ∈ S.Sf, f w := by
      simp [Finset.prod_attach]
    have hglobal' : f v *
        ((∏ w : S.Sf, f w) *
          Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)))) = 1 := by
      rw [hfinprod, Finset.prod_insert (by simpa using hv)] at hglobal
      rw [← hattach] at hglobal
      simpa [f, z, mul_assoc] using hglobal
    have hSprod : (∏ w : S.Sf, f w) *
        Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) =
          (f v)⁻¹ := by
      have hcomm :
          ((∏ w : S.Sf, f w) *
            Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)))) * f v = 1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hglobal'
      exact eq_inv_of_mul_eq_one_left hcomm
    have hE : S.e A (S.diag z) =
        (∏ w : S.Sf, f w) *
          Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
      change (∏ w : S.Sf, f w) *
          ∏ w : InfinitePlace F,
            Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ))) = _
      rw [rf_arch_exp_eq_trace z]
    have honeOut : (1 : Q).out - 1 ∈ v.asIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, Ideal.Quotient.mk_out]
      simp
    have hrepMul : x.out * (1 : Q).out - x.out ∈ v.asIdeal := by
      have h := v.asIdeal.mul_mem_left x.out honeOut
      convert h using 1 <;> ring
    have hψx : ψ x = A.ψ v (algebraMap F (v.adicCompletion F)
        (algebraMap (𝓞 F) F x.out / (p : F))) := by
      calc
        ψ x = ψ (1 * x) := by simp
        _ = A.ψ v (algebraMap F (v.adicCompletion F)
            (algebraMap (𝓞 F) F x.out * algebraMap (𝓞 F) F (1 : Q).out / (p : F))) :=
              hψspec 1 x
        _ = A.ψ v (algebraMap F (v.adicCompletion F)
            (algebraMap (𝓞 F) F (x.out * (1 : Q).out) / (p : F))) := by
              simp only [map_mul]
        _ = A.ψ v (algebraMap F (v.adicCompletion F)
            (algebraMap (𝓞 F) F x.out / (p : F))) :=
              rf_local_additive_phase_congr v p hvalPV _ _ hrepMul
    rw [hE, hSprod, AddChar.inv_apply', hψx]
  have hideal (x : Q) :
      chiIdealPow D v.asIdeal (algebraMap (𝓞 F) F x.out) 2 = χ x := by
    have hvprime : Prime v.asIdeal := (Ideal.prime_iff_isPrime v.ne_bot).2 v.isPrime
    rw [chiIdealPow, UniqueFactorizationMonoid.normalizedFactors_irreducible
      hvprime.irreducible]
    simp [χ, hχval, v.isPrime, v.ne_bot]
  have hsum :
      (∑ᶠ x : Q, chiIdealPow D v.asIdeal (algebraMap (𝓞 F) F x.out) 2 *
        S.e A (S.diag (algebraMap (𝓞 F) F x.out / (p : F)))) =
      gaussSum χ (ψ⁻¹) := by
    rw [finsum_eq_sum_of_fintype, gaussSum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hideal x, hSadd x]
  have hqcard : (Ideal.absNorm v.asIdeal : ℝ) = (Fintype.card Q : ℝ) := by
    exact_mod_cast (by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card])
  have hGprod : gaussSum χ (ψ⁻¹) * star (gaussSum χ (ψ⁻¹)) =
      (Fintype.card Q : ℂ) := by
    calc
      _ = gaussSum χ (ψ⁻¹) * gaussSum χ⁻¹ (ψ⁻¹)⁻¹ := by
        rw [star_gaussSum_eq]
      _ = _ := gaussSum_mul_gaussSum_eq_card hχne hψinvprim
  have hnormsq : ‖gaussSum χ (ψ⁻¹)‖ ^ 2 = (Fintype.card Q : ℝ) := by
    have hC : ((‖gaussSum χ (ψ⁻¹)‖ ^ 2 : ℝ) : ℂ) = (Fintype.card Q : ℂ) := by
      simpa [Complex.mul_conj'] using hGprod
    exact_mod_cast hC
  have hqpos : 0 < qI v.asIdeal := lt_trans zero_lt_one (qI_prime_gt_one v)
  have hscale : ‖((qI v.asIdeal ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ =
      qI v.asIdeal ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = |qI v.asIdeal ^ (-(1 / 2 : ℝ))| := Complex.norm_real _
      _ = qI v.asIdeal ^ (-(1 / 2 : ℝ)) :=
        abs_of_nonneg (Real.rpow_nonneg hqpos.le _)
  have hgammasum : gamma D S A 2 v.asIdeal (p : F) =
      ((qI v.asIdeal ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * gaussSum χ (ψ⁻¹) := by
    simp only [gamma, qI]
    rw [hsum]
  have hgammasq : ‖gamma D S A 2 v.asIdeal (p : F)‖ ^ 2 = 1 := by
    rw [hgammasum, norm_mul, hscale, mul_pow, hnormsq, ← hqcard]
    have hpw : (qI v.asIdeal ^ (-(1 / 2 : ℝ))) ^ 2 * qI v.asIdeal = 1 := by
      calc
        (qI v.asIdeal ^ (-(1 / 2 : ℝ))) ^ 2 * qI v.asIdeal =
            qI v.asIdeal ^ ((-(1 / 2 : ℝ)) * (2 : ℝ)) * qI v.asIdeal := by
              rw [← Real.rpow_mul_natCast hqpos.le (-(1 / 2 : ℝ)) 2]
              congr 1
        _ = qI v.asIdeal ^ (-1 : ℝ) * qI v.asIdeal := by
          congr 1
          norm_num
        _ = 1 := by
          rw [Real.rpow_neg hqpos.le, Real.rpow_one]
          exact inv_mul_cancel₀ (ne_of_gt hqpos)
    exact hpw
  have hnonneg := norm_nonneg (gamma D S A 2 v.asIdeal (p : F))
  nlinarith [hgammasq]

private theorem rf_norm_finset_product_le_one {α : Type*} (s : Finset α) (f : α → ℂ)
    (hf : ∀ a ∈ s, ‖f a‖ ≤ 1) : ‖∏ a ∈ s, f a‖ ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, norm_mul]
      exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _) (ih (by
        intro b hb
        exact hf b (Finset.mem_insert_of_mem hb)))

private theorem rf_betaPrime_nonneg (v : FinPlace F) (e : ℕ) :
    0 ≤ betaPrime (qI v.asIdeal) (qI_prime_gt_one v) e := by
  have hq : 0 < qI v.asIdeal := lt_trans zero_lt_one (qI_prime_gt_one v)
  by_cases h0 : e = 0
  · simp [betaPrime, h0]
  · by_cases h1 : e % 3 = 1
    · simp [betaPrime, h0, h1]
      positivity
    · by_cases h3 : e % 3 = 0
      · simp [betaPrime, h0, h1, h3]
        positivity
      · simp [betaPrime, h0, h1, h3]

private theorem rf_betaIdeal_nonneg (f a : S.ExtIdeal) : 0 ≤ betaIdeal R f a := by
  unfold betaIdeal
  apply Finset.prod_nonneg
  intro v hv
  exact rf_betaPrime_nonneg v (idealExp v a.1)

private theorem rf_exterior_factor_bounds :
    ∀ υ h (t : FrozenIndex R h), ‖frozenOmega R υ t‖ ≤ betaIdeal R t.f t.a ∧
      (∀ sd d, ‖frozenRho R υ t sd d‖ ≤ 1) ∧
      (∀ sc c, ‖frozenLambda R υ t sc c‖ ≤ 1) := by
  intro υ h t
  have hsym := a2_bridge_SYMBOL D S
  have hlocal (v : FinPlace F) (hv : v ∉ S.Sf) (j : Fin 6) (e : ℕ) :
      ‖localR R v j (e : ℤ) 1‖ ≤ betaPrime (qI v.asIdeal) (qI_prime_gt_one v) e :=
    (rf_active_support_bounds R).2.1 v hv j e
  have hL (x : S.FSˣ) : ‖Lvalue R υ x‖ = 1 := by
    simpa [Lvalue] using (R.chars.L υ).unitary x
  have hLinv (x : S.FSˣ) : ‖(Lvalue R υ x)⁻¹‖ = 1 := by
    rw [norm_inv, hL]
    norm_num
  have hLpow (x : S.FSˣ) (e : ℤ) : ‖Lvalue R υ x ^ e‖ = 1 := by
    rw [norm_zpow, hL]
    norm_num
  have hlocalOmega (v : FinPlace F) (hv : v ∉ S.Sf) : ‖localOmega R v‖ = 1 := by
    have ht : (1 : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      simp
    have hw := lem_reflection_local_Weyl R v hv 1 0 1 ht ht
    exact hw.2.2.2.2.1
  constructor
  · dsimp [frozenOmega]
    have hinactive : ‖inactiveScalar R h t.f‖ ≤ 1 := by
      dsimp [inactiveScalar]
      apply rf_norm_finset_product_le_one
      intro v hv
      have hq : 1 < qI v.asIdeal := qI_prime_gt_one v
      have hqpos : 0 < qI v.asIdeal := lt_trans zero_lt_one hq
      have hinv0 : 0 ≤ (qI v.asIdeal)⁻¹ := inv_nonneg.mpr hqpos.le
      have hinvlt : (qI v.asIdeal)⁻¹ < 1 := (inv_lt_one₀ hqpos).2 hq
      have hfactor : 0 ≤ 1 - (qI v.asIdeal)⁻¹ := by linarith
      have hcast : (1 : ℂ) - (qI v.asIdeal : ℂ)⁻¹ =
          ((1 - (qI v.asIdeal)⁻¹ : ℝ) : ℂ) := by norm_cast
      calc
        ‖(1 : ℂ) - (qI v.asIdeal : ℂ)⁻¹‖ =
            ‖((1 - (qI v.asIdeal)⁻¹ : ℝ) : ℂ)‖ := by rw [hcast]
        _ = |1 - (qI v.asIdeal)⁻¹| := Complex.norm_real _
        _ = 1 - (qI v.asIdeal)⁻¹ := abs_of_nonneg hfactor
        _ ≤ 1 := by linarith
    have hprod : ‖∏ v ∈ R.exterior.support t.f,
        localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
          chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) /
            (primeGen R v : F) ^ idealExp v t.a.1 * (bc.gen t.n : F) ^ 3 *
            ((bc.gen t.f : F) / (primeGen R v : F)) ^ (-2 : ℤ)) ^ frozenB t v‖ ≤
        betaIdeal R t.f t.a := by
      rw [norm_prod]
      unfold betaIdeal
      apply Finset.prod_le_prod₀
      · intro v hv
        exact norm_nonneg _
      · intro v hv
        have hvS : v ∉ S.Sf := R.exterior.support_exterior t.f v hv
        have hχ := hsym.chi_zpow_norm_le v
          (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) /
            (primeGen R v : F) ^ idealExp v t.a.1 * (bc.gen t.n : F) ^ 3 *
            ((bc.gen t.f : F) / (primeGen R v : F)) ^ (-2 : ℤ)) (frozenB t v)
        calc
          ‖localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
              chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) /
                (primeGen R v : F) ^ idealExp v t.a.1 * (bc.gen t.n : F) ^ 3 *
                ((bc.gen t.f : F) / (primeGen R v : F)) ^ (-2 : ℤ)) ^ frozenB t v‖
              = ‖localR R v (frozenJ t v) (idealExp v t.a.1) 1‖ *
                ‖chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) /
                  (primeGen R v : F) ^ idealExp v t.a.1 * (bc.gen t.n : F) ^ 3 *
                  ((bc.gen t.f : F) / (primeGen R v : F)) ^ (-2 : ℤ)) ^ frozenB t v‖ := norm_mul _ _
          _ ≤ betaPrime (qI v.asIdeal) (qI_prime_gt_one v) (idealExp v t.a.1) * 1 := by
            calc
              _ ≤ betaPrime (qI v.asIdeal) (qI_prime_gt_one v) (idealExp v t.a.1) *
                    ‖chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) /
                      (primeGen R v : F) ^ idealExp v t.a.1 * (bc.gen t.n : F) ^ 3 *
                      ((bc.gen t.f : F) / (primeGen R v : F)) ^ (-2 : ℤ)) ^ frozenB t v‖ :=
                  mul_le_mul_of_nonneg_right (hlocal v hvS (frozenJ t v) (idealExp v t.a.1))
                    (norm_nonneg _)
              _ ≤ betaPrime (qI v.asIdeal) (qI_prime_gt_one v) (idealExp v t.a.1) * 1 :=
                  mul_le_mul_of_nonneg_left hχ
                    (rf_betaPrime_nonneg v (idealExp v t.a.1))
          _ = betaPrime (qI v.asIdeal) (qI_prime_gt_one v) (idealExp v t.a.1) := mul_one _
    calc
      ‖inactiveScalar R h t.f * (Lvalue R υ (S.diagU (bc.gen t.a)))⁻¹ *
          Lvalue R υ (S.diagU (bc.gen t.n)) ^ (-3 : ℤ) *
          Lvalue R υ (S.diagU (bc.gen t.f)) ^ 2 *
          ∏ v ∈ R.exterior.support t.f,
            localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
              chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) /
                (primeGen R v : F) ^ idealExp v t.a.1 * (bc.gen t.n : F) ^ 3 *
                ((bc.gen t.f : F) / (primeGen R v : F)) ^ (-2 : ℤ)) ^ frozenB t v‖
          = ‖inactiveScalar R h t.f‖ *
              ‖(Lvalue R υ (S.diagU (bc.gen t.a)))⁻¹‖ *
              ‖Lvalue R υ (S.diagU (bc.gen t.n)) ^ (-3 : ℤ)‖ *
              ‖Lvalue R υ (S.diagU (bc.gen t.f)) ^ 2‖ *
              ‖∏ v ∈ R.exterior.support t.f,
                localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
                  chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) /
                    (primeGen R v : F) ^ idealExp v t.a.1 * (bc.gen t.n : F) ^ 3 *
                    ((bc.gen t.f : F) / (primeGen R v : F)) ^ (-2 : ℤ)) ^ frozenB t v‖ := by
            repeat rw [norm_mul]
      _ = ‖inactiveScalar R h t.f‖ *
              ‖∏ v ∈ R.exterior.support t.f,
                localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
                  chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) /
                    (primeGen R v : F) ^ idealExp v t.a.1 * (bc.gen t.n : F) ^ 3 *
                    ((bc.gen t.f : F) / (primeGen R v : F)) ^ (-2 : ℤ)) ^ frozenB t v‖ := by
            simp [norm_inv, norm_zpow, hL]
      _ ≤ 1 * betaIdeal R t.f t.a := by
            calc
              ‖inactiveScalar R h t.f‖ *
                  ‖∏ v ∈ R.exterior.support t.f,
                    localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
                      chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) /
                        (primeGen R v : F) ^ idealExp v t.a.1 * (bc.gen t.n : F) ^ 3 *
                        ((bc.gen t.f : F) / (primeGen R v : F)) ^ (-2 : ℤ)) ^ frozenB t v‖
                ≤ 1 * ‖∏ v ∈ R.exterior.support t.f,
                    localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
                      chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) /
                        (primeGen R v : F) ^ idealExp v t.a.1 * (bc.gen t.n : F) ^ 3 *
                        ((bc.gen t.f : F) / (primeGen R v : F)) ^ (-2 : ℤ)) ^ frozenB t v‖ :=
                  mul_le_mul_of_nonneg_right hinactive (norm_nonneg _)
              _ ≤ 1 * betaIdeal R t.f t.a :=
                  mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = betaIdeal R t.f t.a := one_mul _
  · constructor
    · intro sd d
      by_cases hρ : Squarefree d.1 ∧ IsCoprime d.1 (h.1 * t.n.1) ∧
          cls (S.diagU (bc.gen d)) = sd.1
      · rw [frozenRho, if_pos hρ]
        have hprod1 : ‖∏ v ∈ R.exterior.support d, localOmega R v *
            chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) *
              (bc.gen t.n : F) ^ 3 * ((bc.gen d : F) / (primeGen R v : F)) ^ (-2 : ℤ) *
              (bc.gen t.f : F) ^ (-2 : ℤ))‖ ≤ 1 := by
          apply rf_norm_finset_product_le_one
          intro v hv
          have hvS := R.exterior.support_exterior d v hv
          calc
            ‖localOmega R v * chi D v _‖ = ‖localOmega R v‖ * ‖chi D v _‖ := norm_mul _ _
            _ ≤ 1 := mul_le_one₀ (by simpa [hlocalOmega v hvS]) (norm_nonneg _)
              (hsym.chi_norm_le v
                (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) *
                  (bc.gen t.n : F) ^ 3 * ((bc.gen d : F) / (primeGen R v : F)) ^ (-2 : ℤ) *
                  (bc.gen t.f : F) ^ (-2 : ℤ)))
        have hprod2 : ‖∏ v ∈ R.exterior.support t.f,
            chi D v (bc.gen d : F) ^ (-2 * frozenB t v)‖ ≤ 1 := by
          apply rf_norm_finset_product_le_one
          intro v hv
          exact hsym.chi_zpow_norm_le v _ _
        have hmul :
            ‖∏ v ∈ R.exterior.support d, localOmega R v *
              chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) *
                (bc.gen t.n : F) ^ 3 * ((bc.gen d : F) / (primeGen R v : F)) ^ (-2 : ℤ) *
                (bc.gen t.f : F) ^ (-2 : ℤ))‖ *
            ‖∏ v ∈ R.exterior.support t.f,
              chi D v (bc.gen d : F) ^ (-2 * frozenB t v)‖ ≤ 1 :=
          mul_le_one₀ hprod1 (norm_nonneg _) hprod2
        change ‖Lvalue R υ (S.diagU (bc.gen d)) ^ 2 *
          (∏ v ∈ R.exterior.support d, localOmega R v *
            chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) *
              (bc.gen t.n : F) ^ 3 * ((bc.gen d : F) / (primeGen R v : F)) ^ (-2 : ℤ) *
              (bc.gen t.f : F) ^ (-2 : ℤ))) *
          ∏ v ∈ R.exterior.support t.f,
            chi D v (bc.gen d : F) ^ (-2 * frozenB t v)‖ ≤ 1
        rw [norm_mul, norm_mul]
        simpa [norm_pow, hL] using hmul
      · rw [frozenRho, if_neg hρ]
        simp
    · intro sc c
      by_cases hLam : IsCoprime c.1 t.f.1 ∧
          cls (S.diagU (bc.gen (R.exterior.ofSqf c))) = sc.1
      · rw [frozenLambda, if_pos hLam]
        have hprodF : ‖∏ v ∈ R.exterior.support t.f,
            chi D v (cgen R c) ^ frozenB t v‖ ≤ 1 := by
          apply rf_norm_finset_product_le_one
          intro v hv
          exact hsym.chi_zpow_norm_le v (cgen R c) (frozenB t v)
        have hprodC : ‖∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
            gamma D S A 2 v.asIdeal (primeGen R v : F) *
              chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) *
                (cgen R c / (primeGen R v : F)) * (bc.gen t.f : F) ^ (-2 : ℤ)) ^ 2‖ ≤ 1 := by
          apply rf_norm_finset_product_le_one
          intro v hv
          have hvS := R.exterior.support_exterior (R.exterior.ofSqf c) v hv
          have hpgen : S.IsGen (primeGen R v : F) v.asIdeal := by
            simpa [primeGen, hvS, R.exterior.prime_val v hvS] using
              (bc.gen_spec (R.exterior.prime v hvS)).1
          have hgamma := rf_gamma_prime_norm_one (D := D) (S := S) (A := A)
            v hvS (primeGen R v) hpgen
          have hχ := hsym.chi_zpow_norm_le v
            (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) *
              (cgen R c / (primeGen R v : F)) * (bc.gen t.f : F) ^ (-2 : ℤ)) 2
          calc
            ‖gamma D S A 2 v.asIdeal (primeGen R v : F) *
                chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) *
                  (cgen R c / (primeGen R v : F)) * (bc.gen t.f : F) ^ (-2 : ℤ)) ^ 2‖
                = ‖gamma D S A 2 v.asIdeal (primeGen R v : F)‖ *
                  ‖chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) *
                    (cgen R c / (primeGen R v : F)) * (bc.gen t.f : F) ^ (-2 : ℤ)) ^ 2‖ :=
                    norm_mul _ _
            _ ≤ 1 := mul_le_one₀ (by rw [hgamma]) (norm_nonneg _)
              hχ
        have hmul : ‖∏ v ∈ R.exterior.support t.f,
            chi D v (cgen R c) ^ frozenB t v‖ *
            ‖∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
              gamma D S A 2 v.asIdeal (primeGen R v : F) *
                chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) *
                  (cgen R c / (primeGen R v : F)) * (bc.gen t.f : F) ^ (-2 : ℤ)) ^ 2‖ ≤ 1 :=
          mul_le_one₀ hprodF (norm_nonneg _) hprodC
        change ‖(Lvalue R υ (S.diagU (bc.gen (R.exterior.ofSqf c))))⁻¹ *
          (∏ v ∈ R.exterior.support t.f,
            chi D v (cgen R c) ^ frozenB t v) *
          ∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
            gamma D S A 2 v.asIdeal (primeGen R v : F) *
              chi D v (((R.sheets.eps t.u : Fˣ) : F) * (bc.gen t.a : F) *
                (cgen R c / (primeGen R v : F)) * (bc.gen t.f : F) ^ (-2 : ℤ)) ^ 2‖ ≤ 1
        rw [norm_mul, norm_mul, hLinv]
        simpa only [one_mul] using hmul
      · rw [frozenLambda, if_neg hLam]
        simp

private theorem rf_spanSingleton_pow (a : Fˣ) (n : ℕ) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((a ^ n : Fˣ) : F) =
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
        ih, pow_succ]

private theorem rf_isGen_extPow (I : S.ExtIdeal) (a : Fˣ)
    (ha : S.IsGen (a : F) I.1) (n : ℕ) :
    S.IsGen (a ^ n : F) (R.exterior.pow I n).1 := by
  refine ⟨(R.exterior.pow I n).property, Units.ne_zero (a ^ n), ?_⟩
  intro v hv
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((a : F) ^ n) =
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) ^ n := by
    simpa only [Units.val_pow_eq_pow_val] using rf_spanSingleton_pow a n
  rw [hspan, FractionalIdeal.count_pow, ha.2.2 v hv,
    R.exterior.pow_val, FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow]

private theorem rf_isGen_extMul (I J : S.ExtIdeal) (a b : Fˣ)
    (ha : S.IsGen (a : F) I.1) (hb : S.IsGen (b : F) J.1) :
    S.IsGen (a * b : F) (R.exterior.mul I J).1 := by
  refine ⟨(R.exterior.mul I J).property, mul_ne_zero (Units.ne_zero a) (Units.ne_zero b), ?_⟩
  intro v hv
  have hI0 : (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa only [Ideal.zero_eq_bot] using I.property.1)
  have hJ0 : (J.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa only [Ideal.zero_eq_bot] using J.property.1)
  calc
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((a * b : Fˣ) : F)) =
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) := by
              rw [Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    _ = FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) +
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) := by
            rw [FractionalIdeal.count_mul F v
              (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero a))
              (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero b))]
    _ = FractionalIdeal.count F v (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
        FractionalIdeal.count F v (J.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
            rw [ha.2.2 v hv, hb.2.2 v hv]
    _ = FractionalIdeal.count F v
          ((R.exterior.mul I J).1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
            rw [R.exterior.mul_val]
            rw [FractionalIdeal.coeIdeal_mul]
            exact (FractionalIdeal.count_mul F v hI0 hJ0).symm

private theorem rf_generator_valuation_other (v w : FinPlace F)
    (hv : v ∉ S.Sf) (hw : w ∉ S.Sf) (hvw : v ≠ w)
    (p : Fˣ) (hp : S.IsGen (p : F) w.asIdeal) :
    HeightOneSpectrum.valuation F v (p : F) = 1 := by
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 0 := by
    calc
      _ = FractionalIdeal.count F v
          (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hp.2.2 v hv
      _ = 0 := FractionalIdeal.count_maximal_coprime F v hvw.symm
  have hlog : WithZero.log (HeightOneSpectrum.valuation F v (p : F)) = 0 := by
    have h := rf_count_spanSingleton_eq_neg_log_valuation v (p : F) p.ne_zero
    rw [hcount] at h
    simpa only [neg_eq_zero] using h.symm
  have hne : HeightOneSpectrum.valuation F v (p : F) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr p.ne_zero
  calc
    HeightOneSpectrum.valuation F v (p : F) =
        WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (p : F))) :=
      (WithZero.exp_log hne).symm
    _ = 1 := by simp [hlog]

private theorem rf_prime_pairing_identity (v w : FinPlace F)
    (hv : v ∉ S.Sf) (hw : w ∉ S.Sf) (hvw : v ≠ w) :
    chi D v (primeGen R w : F) * chi D w (primeGen R v : F) ^ (-4 : ℤ) =
      chi D v (primeGen R w : F) ^ 3 := by
  have hpv : S.IsGen (primeGen R v : F) v.asIdeal ∧ Bd.Allowed (primeGen R v) := by
    simpa [primeGen, hv, R.exterior.prime_val v hv] using
      (bc.gen_spec (R.exterior.prime v hv))
  have hpw : S.IsGen (primeGen R w : F) w.asIdeal ∧ Bd.Allowed (primeGen R w) := by
    simpa [primeGen, hw, R.exterior.prime_val w hw] using
      (bc.gen_spec (R.exterior.prime w hw))
  have hrec := sextic_reciprocity D S H Bd v w hv hw hvw
    (primeGen R v) (primeGen R w) hpv hpw
  let z := chi D v (primeGen R w : F)
  have hval : HeightOneSpectrum.valuation F v (primeGen R w : F) = 1 :=
    rf_generator_valuation_other v w hv hw hvw (primeGen R w) hpw.1
  have hzres : residue v (primeGen R w : F) ≠ 0 := by
    exact ((a2_bridge_SYMBOL D S).residue_ne_zero v _ (by rw [hval])).mpr hval
  have hz6 : z ^ (6 : ℕ) = 1 := by
    exact (a2_bridge_SYMBOL D S).chi_six v _ hzres
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz6
    norm_num at hz6
  have hz6z : z ^ (6 : ℤ) = 1 := by simpa using hz6
  have hneg : z ^ (-3 : ℤ) = z ^ (3 : ℤ) := by
    have h := zpow_add₀ hz0 (6 : ℤ) (-3 : ℤ)
    rw [show (6 : ℤ) + (-3 : ℤ) = 3 by norm_num, hz6z, one_mul] at h
    exact h.symm
  calc
    chi D v (primeGen R w : F) * chi D w (primeGen R v : F) ^ (-4 : ℤ) =
        z * z ^ (-4 : ℤ) := by rw [← hrec]
    _ = z ^ (-3 : ℤ) := by
      simpa using (zpow_add₀ hz0 (1 : ℤ) (-4 : ℤ)).symm
    _ = z ^ (3 : ℤ) := hneg
    _ = z ^ 3 := by simp [z]

private theorem rf_idealExp_mul (v : FinPlace F) (I J : Ideal (𝓞 F))
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    idealExp v (I * J) = idealExp v I + idealExp v J := by
  unfold idealExp
  rw [← Associates.mk_mul_mk,
    Associates.count_mul (Associates.mk_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hI))
      (Associates.mk_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hJ)) v.associates_irreducible]

private theorem rf_idealExp_eq_count (v : FinPlace F) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) :
    idealExp v I = FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
  unfold idealExp
  rw [FractionalIdeal.count_coe F v hI]

private theorem rf_idealExp_pow (v : FinPlace F) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) (n : ℕ) : idealExp v (I ^ n) = n * idealExp v I := by
  have hI0 : (Associates.mk I : Associates (Ideal (𝓞 F))) ≠ 0 :=
    Associates.mk_ne_zero.mpr (by simpa only [Ideal.zero_eq_bot] using hI)
  unfold idealExp
  rw [Associates.mk_pow]
  exact Associates.count_pow (a := Associates.mk I) hI0
    (p := Associates.mk v.asIdeal) v.associates_irreducible n

private theorem rf_idealExp_ne_zero_iff_support (v : FinPlace F) (I : S.ExtIdeal) :
    idealExp v I.1 ≠ 0 ↔ v ∈ R.exterior.support I := by
  have hvIrr : Irreducible v.asIdeal :=
    ((Ideal.prime_iff_isPrime v.ne_bot).2 v.isPrime).irreducible
  unfold idealExp
  rw [Associates.count_ne_zero_iff_dvd (a := I.1) (p := v.asIdeal)
    (by simpa [Ideal.zero_eq_bot] using I.property.1) hvIrr,
    R.exterior.mem_support]

private theorem rf_idealExp_zero_of_not_support (v : FinPlace F) (I : S.ExtIdeal)
    (hv : v ∉ R.exterior.support I) : idealExp v I.1 = 0 := by
  by_contra h
  exact hv ((rf_idealExp_ne_zero_iff_support R v I).mp h)

private theorem rf_not_support_of_idealExp_zero (v : FinPlace F) (I : S.ExtIdeal)
    (hv : idealExp v I.1 = 0) : v ∉ R.exterior.support I := by
  intro hm
  exact (rf_idealExp_ne_zero_iff_support R v I).mpr hm hv

private theorem rf_no_common_prime (v : FinPlace F) (I J : Ideal (𝓞 F))
    (hcop : IsCoprime I J) (hI : v.asIdeal ∣ I) (hJ : v.asIdeal ∣ J) : False := by
  have hu := hcop.isUnit_of_dvd' hI hJ
  exact v.isPrime.ne_top (Ideal.isUnit_iff.mp hu)

private theorem rf_idealExp_eq_one_of_squarefree_support (v : FinPlace F)
    (I : S.ExtIdeal) (hsq : Squarefree I.1) (hv : v ∈ R.exterior.support I) :
    idealExp v I.1 = 1 := by
  have hI0 : Associates.mk I.1 ≠ 0 :=
    Associates.mk_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using I.property.1)
  have hdiv : v.asIdeal ∣ I.1 := (R.exterior.mem_support I v).1 hv
  have hvIrr : Irreducible v.asIdeal :=
    ((Ideal.prime_iff_isPrime v.ne_bot).2 v.isPrime).irreducible
  have hcountne : idealExp v I.1 ≠ 0 := by
    unfold idealExp
    exact (Associates.count_ne_zero_iff_dvd (a := I.1) (p := v.asIdeal)
      (by simpa [Ideal.zero_eq_bot] using I.property.1) hvIrr).2 hdiv
  have hcountle : idealExp v I.1 ≤ 1 := by
    by_contra hle
    have hge : 2 ≤ idealExp v I.1 := by omega
    have hpowAssoc : (Associates.mk v.asIdeal) ^ 2 ≤ Associates.mk I.1 := by
      rw [Associates.prime_pow_dvd_iff_le hI0 v.associates_irreducible]
      exact hge
    have hpow' : Associates.mk (v.asIdeal ^ 2) ≤ Associates.mk I.1 := by
      simpa only [Associates.mk_pow] using hpowAssoc
    have hpow : v.asIdeal ^ 2 ∣ I.1 := Associates.mk_le_mk_iff_dvd.mp hpow'
    have hunit := hsq v.asIdeal (by simpa [pow_two] using hpow)
    exact v.isPrime.ne_top ((Ideal.isUnit_iff).mp hunit)
  omega

private theorem rf_ordv_toLoc_ofGen (v : FinPlace F) (hv : v ∉ S.Sf)
    (I : S.ExtIdeal) (x : Fˣ) (hx : S.IsGen (x : F) I.1) :
    ordv v (toLoc v x) = idealExp v I.1 := by
  have hxne : HeightOneSpectrum.valuation F v (x : F) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr (Units.ne_zero x)
  have hxcount := rf_count_spanSingleton_eq_neg_log_valuation v (x : F) (Units.ne_zero x)
  have hlocval : Valued.v ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      HeightOneSpectrum.valuation F v (x : F) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = _
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation']
  have hlocne : Valued.v ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≠ 0 := by
    rw [hlocval]
    exact hxne
  calc
    ordv v (toLoc v x) =
        -WithZero.log (Valued.v ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F)) := by
      dsimp [ordv]
      rw [WithZero.toAdd_unzero_eq_log hlocne]
    _ = -WithZero.log (HeightOneSpectrum.valuation F v (x : F)) := by rw [hlocval]
    _ = FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F)) := hxcount.symm
    _ = FractionalIdeal.count F v (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hx.2.2 v hv
    _ = idealExp v I.1 := by
      rw [FractionalIdeal.count_coe F v (by simpa only [Ideal.zero_eq_bot] using I.property.1)]
      rfl

private theorem rf_ordv_local_log (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
    ordv v x = -WithZero.log (Valued.v (x : v.adicCompletion F)) := by
  have hxne : Valued.v (x : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr x.ne_zero
  dsimp [ordv]
  exact congrArg Neg.neg (WithZero.toAdd_unzero_eq_log hxne)

private theorem rf_localVal_one_of_ordv_zero (v : FinPlace F)
    (x : (v.adicCompletion F)ˣ) (hx : ordv v x = 0) :
    Valued.v (x : v.adicCompletion F) = 1 := by
  have hxne : Valued.v (x : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hlog : WithZero.log (Valued.v (x : v.adicCompletion F)) = 0 := by
    have h := rf_ordv_local_log v x
    rw [hx] at h
    simpa only [neg_eq_zero] using h.symm
  calc
    Valued.v (x : v.adicCompletion F) =
        WithZero.exp (WithZero.log (Valued.v (x : v.adicCompletion F))) :=
      (WithZero.exp_log hxne).symm
    _ = 1 := by simp [hlog]

private theorem rf_ordv_mul (v : FinPlace F) (x y : (v.adicCompletion F)ˣ) :
    ordv v (x * y) = ordv v x + ordv v y := by
  have hxne : Valued.v (x : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hyne : Valued.v (y : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr y.ne_zero
  calc
    ordv v (x * y) = -WithZero.log (Valued.v ((x * y : (v.adicCompletion F)ˣ) : v.adicCompletion F)) :=
      rf_ordv_local_log v (x * y)
    _ = -(WithZero.log (Valued.v (x : v.adicCompletion F)) +
        WithZero.log (Valued.v (y : v.adicCompletion F))) := by
          rw [Units.val_mul, map_mul, WithZero.log_mul hxne hyne]
    _ = ordv v x + ordv v y := by
          rw [rf_ordv_local_log v x, rf_ordv_local_log v y]
          ring

private theorem rf_ordv_zpow (v : FinPlace F) (x : (v.adicCompletion F)ˣ) (n : ℤ) :
    ordv v (x ^ n) = n * ordv v x := by
  rw [rf_ordv_local_log, Units.val_zpow_eq_zpow_val, map_zpow₀,
    WithZero.log_zpow, rf_ordv_local_log]
  simp only [zsmul_eq_mul]
  rw [mul_neg]
  congr 1

private theorem rf_globalVal_one_of_ordv_zero (v : FinPlace F) (x : Fˣ)
    (hx : ordv v (toLoc v x) = 0) : HeightOneSpectrum.valuation F v (x : F) = 1 := by
  have hloc := rf_localVal_one_of_ordv_zero v (toLoc v x) hx
  have hmap : Valued.v (toLoc v x : v.adicCompletion F) =
      HeightOneSpectrum.valuation F v (x : F) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = _
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation']
  rw [hmap] at hloc
  exact hloc

private theorem rf_localChi_toLoc (v : FinPlace F) (hv : v ∉ S.Sf) (x : Fˣ)
    (hx : HeightOneSpectrum.valuation F v (x : F) = 1) :
    localChi D v (toLoc v x) = chi D v (x : F) := by
  have hxv : Valued.v ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hx]
  have hloc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (toLoc v x) := by
    constructor
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      rw [hxv]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [Units.val_inv_eq_inv_val, map_inv₀, hxv, inv_one, le_refl]
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hx.le
    (1 : (WithZero (Multiplicative ℤ))ˣ)
  simp only [Units.val_one] at ha
  have haval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a) = 1 := by
    have hlt : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a - (x : F)) <
        HeightOneSpectrum.valuation F v (x : F) := by rwa [hx]
    exact ((HeightOneSpectrum.valuation F v).map_eq_of_sub_lt hlt).trans hx
  have hamem : a ∉ v.asIdeal := (v.valuation_eq_one_iff_notMem (K := F)).1 haval
  have hta : Valued.v ((toLoc v x : (v.adicCompletion F)ˣ).val -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F) -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1
    rw [← map_sub]
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation',
      Valuation.map_sub_swap] using ha
  rw [(a2_bridge_SYMBOL D S).localChi_approximant v hv (toLoc v x) hloc a hamem hta]
  apply (a2_bridge_SYMBOL D S).chi_congr
  have hglobal : HeightOneSpectrum.valuation F v
      (algebraMap (𝓞 F) F a - (x : F)) < 1 := by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation',
      Valuation.map_sub_swap] using ha
  exact (a2_bridge_SYMBOL D S).residue_congr v _ _ (v.valuation_le_one a) hx.le hglobal

private theorem rf_chi_zpow_mul (v : FinPlace F) (hv : v ∉ S.Sf) (x y : F)
    (hxv : residue v x ≠ 0) (hyv : residue v y ≠ 0)
    (hx : HeightOneSpectrum.valuation F v x ≤ 1)
    (hy : HeightOneSpectrum.valuation F v y ≤ 1) (e : ℤ) :
    chi D v (x * y) ^ e = chi D v x ^ e * chi D v y ^ e := by
  have hmul := (a2_bridge_SYMBOL D S).chi_mul v hv x y hx hy
  have hxyv : residue v (x * y) ≠ 0 := by
    have hres := (a2_bridge_SYMBOL D S).residue_mul v x y hx hy
    rw [hres]
    exact mul_ne_zero hxv hyv
  have hχx : chi D v x ≠ 0 := by
    intro h
    have h6 := (a2_bridge_SYMBOL D S).chi_six v x hxv
    rw [h] at h6
    norm_num at h6
  have hχy : chi D v y ≠ 0 := by
    intro h
    have h6 := (a2_bridge_SYMBOL D S).chi_six v y hyv
    rw [h] at h6
    norm_num at h6
  have hχxy : chi D v (x * y) ≠ 0 := by
    intro h
    have h6 := (a2_bridge_SYMBOL D S).chi_six v (x * y) hxyv
    rw [h] at h6
    norm_num at h6
  let ux : ℂˣ := Units.mk0 (chi D v x) hχx
  let uy : ℂˣ := Units.mk0 (chi D v y) hχy
  let uxy : ℂˣ := Units.mk0 (chi D v (x * y)) hχxy
  have hunit : uxy = ux * uy := by
    apply Units.ext
    simp [uxy, ux, uy, hmul]
  calc
    chi D v (x * y) ^ e = (↑(uxy ^ e) : ℂ) := by simp [uxy]
    _ = (↑((ux * uy) ^ e) : ℂ) := by rw [hunit]
    _ = (↑(ux ^ e * uy ^ e) : ℂ) := by rw [mul_zpow]
    _ = chi D v x ^ e * chi D v y ^ e := by simp [ux, uy]

private theorem rf_chi_argument_zpow (v : FinPlace F) (hv : v ∉ S.Sf) (x : Fˣ)
    (hx : HeightOneSpectrum.valuation F v (x : F) = 1) (e : ℤ) :
    chi D v ((x ^ e : Fˣ) : F) = chi D v (x : F) ^ e := by
  have hxres : residue v (x : F) ≠ 0 := by
    exact ((a2_bridge_SYMBOL D S).residue_ne_zero v (x : F)
      (by rw [hx])).mpr hx
  have hχx : chi D v (x : F) ≠ 0 := by
    intro hz
    have h6 := (a2_bridge_SYMBOL D S).chi_six v (x : F) hxres
    rw [hz] at h6
    norm_num at h6
  have hvalOne : HeightOneSpectrum.valuation F v (1 : F) = 1 := by simp
  have hresOne : residue v (1 : F) ≠ 0 := by
    exact ((a2_bridge_SYMBOL D S).residue_ne_zero v (1 : F)
      (by rw [hvalOne])).mpr hvalOne
  have hχOneNe : chi D v (1 : F) ≠ 0 := by
    intro hz
    have h6 := (a2_bridge_SYMBOL D S).chi_six v (1 : F) hresOne
    rw [hz] at h6
    norm_num at h6
  have hχOne : chi D v (1 : F) = 1 := by
    have hmul := (a2_bridge_SYMBOL D S).chi_mul v hv (1 : F) 1
      (by simpa [hvalOne]) (by simpa [hvalOne])
    have hcancel : (1 : ℂ) = chi D v (1 : F) :=
      mul_left_cancel₀ hχOneNe (by simpa using hmul)
    exact hcancel.symm
  have hvalInv : HeightOneSpectrum.valuation F v ((x⁻¹ : Fˣ) : F) = 1 := by
    calc
      HeightOneSpectrum.valuation F v ((x⁻¹ : Fˣ) : F) =
          (HeightOneSpectrum.valuation F v (x : F))⁻¹ := by
            rw [Units.val_inv_eq_inv_val, Valuation.map_inv]
      _ = 1 := by rw [hx]; simp
  have hχInv : chi D v ((x⁻¹ : Fˣ) : F) = (chi D v (x : F))⁻¹ := by
    have hmul := (a2_bridge_SYMBOL D S).chi_mul v hv (x : F)
      ((x⁻¹ : Fˣ) : F) hx.le hvalInv.le
    have hprod : chi D v (x : F) * chi D v ((x⁻¹ : Fˣ) : F) = 1 := by
      calc
        _ = chi D v (((x * x⁻¹ : Fˣ) : F)) := hmul.symm
        _ = chi D v (1 : F) := by simp
        _ = 1 := hχOne
    exact mul_left_cancel₀ hχx (by
      calc
        chi D v (x : F) * chi D v ((x⁻¹ : Fˣ) : F) = 1 := hprod
        _ = chi D v (x : F) * (chi D v (x : F))⁻¹ := by
          exact (mul_inv_cancel₀ hχx).symm)
  have hNat (y : Fˣ) (hy : HeightOneSpectrum.valuation F v (y : F) = 1) :
      ∀ n : ℕ, chi D v ((y ^ n : Fˣ) : F) = chi D v (y : F) ^ n := by
    intro n
    induction n with
    | zero => simpa [hχOne]
    | succ n ih =>
      have hyPow : HeightOneSpectrum.valuation F v ((y ^ n : Fˣ) : F) = 1 := by
        simp [Units.val_pow_eq_pow_val, map_pow, hy]
      have hmul := (a2_bridge_SYMBOL D S).chi_mul v hv
        ((y ^ n : Fˣ) : F) (y : F) hyPow.le hy.le
      calc
        chi D v ((y ^ (n + 1) : Fˣ) : F) =
            chi D v (((y ^ n : Fˣ) : F) * (y : F)) := by simp [pow_succ]
        _ = chi D v ((y ^ n : Fˣ) : F) * chi D v (y : F) := hmul
        _ = chi D v (y : F) ^ n * chi D v (y : F) := by rw [ih]
        _ = chi D v (y : F) ^ (n + 1) := by rw [pow_succ]
  cases e with
  | ofNat n =>
      simpa [zpow_natCast] using hNat x hx n
  | negSucc n =>
      have hpow := hNat (x⁻¹) hvalInv (n + 1)
      rw [hχInv, inv_pow] at hpow
      simpa [zpow_negSucc] using hpow

private theorem rf_Wv_sphericalTable (v : FinPlace F) (hv : v ∉ S.Sf)
    (x : (v.adicCompletion F)ˣ) :
    R.T.Wv v (R.C.a v x) =
      sphericalTable D A v (ordv v x) (unitPart v x) := by
  have hu := ArtinPrimitiveRoots.A1.Theta.thFactorB_unitPart_isLocUnit v x
  have htable := R.T.Wv_table v hv (ordv v x) (unitPart v x) hu.1 hu.2
  calc
    R.T.Wv v (R.C.a v x) =
        R.T.Wv v (R.C.a v (ArtinPrimitiveRoots.A1.Theta.unifLoc v ^ ordv v x *
          unitPart v x)) := by
            exact congrArg (R.T.Wv v) (congrArg (R.C.a v)
              (ArtinPrimitiveRoots.A1.Theta.unitPart_factor v x).symm)
    _ = sphericalTable D A v (ordv v x) (unitPart v x) := by
      simpa [ArtinPrimitiveRoots.A1.Theta.unifLoc] using htable

private theorem rf_sphericalTable_unit_mul (v : FinPlace F) (hv : v ∉ S.Sf)
    (e : ℤ) (uρ u : (v.adicCompletion F)ˣ)
    (hρ : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v uρ)
    (hu : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v u) :
    sphericalTable D A v e (uρ * u) =
      localChi D v uρ ^ (2 * e) * sphericalTable D A v e u := by
  have hv6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  have hbasic := ArtinPrimitiveRoots.A1.Theta.localChi_basic (D := D) (v := v) hv6
  have hmul := hbasic.2.2.1 uρ u hρ hu
  have hρ6 := hbasic.2.2.2.1 uρ hρ
  have hu6 := hbasic.2.2.2.1 u hu
  have hρne : localChi D v uρ ≠ 0 := by
    intro h
    rw [h] at hρ6
    norm_num at hρ6
  have hune : localChi D v u ≠ 0 := by
    intro h
    rw [h] at hu6
    norm_num at hu6
  let ξρ : ℂˣ := Units.mk0 (localChi D v uρ) hρne
  let ξu : ℂˣ := Units.mk0 (localChi D v u) hune
  have hpow : localChi D v (uρ * u) ^ (2 * e) =
      localChi D v uρ ^ (2 * e) * localChi D v u ^ (2 * e) := by
    have h := congrArg (fun z : ℂˣ => (z : ℂ)) (mul_zpow ξρ ξu (2 * e))
    simpa [ξρ, ξu, hmul, Units.val_mul, Units.val_zpow_eq_zpow_val] using h
  unfold sphericalTable
  rw [hpow]
  ring

private theorem rf_unitPart_mul_of_ord_zero (v : FinPlace F)
    (x y : (v.adicCompletion F)ˣ) (hx : ordv v x = 0) :
    unitPart v (x * y) = x * unitPart v y := by
  simp only [unitPart, rf_ordv_mul, hx, zero_add, neg_zero, zpow_zero, mul_one]
  simp [mul_assoc]

private theorem rf_chiIdealPow_primeProduct (s : Finset (FinPlace F)) (x : F) (e : ℤ)
    (hunit : ∀ v ∈ s, residue v x ≠ 0) :
    chiIdealPow D (∏ v ∈ s, v.asIdeal) x e = ∏ v ∈ s, chi D v x ^ e := by
  classical
  have hprod0 : ∀ s : Finset (FinPlace F), (∏ v ∈ s, v.asIdeal) ≠ ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert v s hvs ih =>
        rw [Finset.prod_insert hvs]
        intro h
        rcases (Ideal.mul_eq_bot.mp h) with hv | hs
        · exact v.ne_bot hv
        · exact ih hs
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      simp [chiIdealPow, ← Ideal.one_eq_top]
  | @insert v s hvs ih =>
      have hv0 : v.asIdeal ≠ (0 : Ideal (𝓞 F)) := by
        simpa only [Ideal.zero_eq_bot] using v.ne_bot
      have hs0 : (∏ w ∈ s, w.asIdeal) ≠ (0 : Ideal (𝓞 F)) := by
        simpa only [Ideal.zero_eq_bot] using hprod0 s
      have hprime : chiIdealPow D v.asIdeal x e = chi D v x ^ e := by
        have hvprime : Prime v.asIdeal := (Ideal.prime_iff_isPrime v.ne_bot).2 v.isPrime
        have hnorm : normalize v.asIdeal = v.asIdeal :=
          associated_iff_eq.mp (normalize_associated v.asIdeal)
        rw [chiIdealPow, UniqueFactorizationMonoid.normalizedFactors_irreducible
          hvprime.irreducible]
        rw [hnorm]
        simp only [Multiset.map_singleton, Multiset.prod_singleton]
        have hcond : v.asIdeal.IsPrime ∧ v.asIdeal ≠ ⊥ := ⟨v.isPrime, v.ne_bot⟩
        rw [dif_pos hcond]
        have hplace : (⟨v.asIdeal, hcond.1, hcond.2⟩ : FinPlace F) = v := by
          apply HeightOneSpectrum.ext
          rfl
        rw [hplace]
        simp [chiPow, hunit v (Finset.mem_insert_self v s)]
      calc
        chiIdealPow D (∏ w ∈ insert v s, w.asIdeal) x e =
            chiIdealPow D v.asIdeal x e *
              chiIdealPow D (∏ w ∈ s, w.asIdeal) x e := by
          rw [Finset.prod_insert hvs, chiIdealPow,
            UniqueFactorizationMonoid.normalizedFactors_mul hv0 hs0,
            Multiset.map_add, Multiset.prod_add]
          rfl
        _ = ∏ w ∈ insert v s, chi D w x ^ e := by
          rw [hprime, ih (fun w hw => hunit w (Finset.mem_insert_of_mem hw))]
          simp [Finset.prod_insert hvs]

private theorem rf_isGen_one : S.IsGen (1 : F) (⊤ : Ideal (𝓞 F)) := by
  refine ⟨?_, one_ne_zero, ?_⟩
  · constructor
    · exact top_ne_bot
    · intro v hv hle
      exact v.isPrime.ne_top (top_le_iff.mp hle)
  · intro v hv
    simp [FractionalIdeal.spanSingleton_one]

private theorem rf_allowed_one : Bd.Allowed (1 : Fˣ) := by
  change (cls (S.diagU (1 : Fˣ)) : S.V) ∈ Bd.B
  simpa [cls] using (Bd.B.one_mem : (1 : S.V) ∈ Bd.B)

private theorem rf_isGen_US (e : S.US) : S.IsGen ((e : Fˣ) : F) (⊤ : Ideal (𝓞 F)) := by
  have htop : S.IsExterior (⊤ : Ideal (𝓞 F)) := by
    refine ⟨top_ne_bot, ?_⟩
    intro v hv hle
    exact v.isPrime.ne_top (top_le_iff.mp hle)
  refine ⟨htop, Units.ne_zero (e : Fˣ), ?_⟩
  intro v hv
  have hval : HeightOneSpectrum.valuation F v ((e : Fˣ) : F) = 1 :=
    Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F) e hv
  rw [rf_count_spanSingleton_eq_neg_log_valuation v ((e : Fˣ) : F)
    (Units.ne_zero (e : Fˣ)), hval]
  simpa using (FractionalIdeal.count_one F v).symm

private theorem rf_allowed_six (e : Fˣ) : Bd.Allowed (e ^ (6 : ℕ)) := by
  change (cls (S.diagU (e ^ (6 : ℕ))) : S.V) ∈ Bd.B
  have hmem : (S.diagU e) ^ 6 ∈ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range := by
    exact ⟨S.diagU e, rfl⟩
  have hclass : cls (S.diagU (e ^ (6 : ℕ))) = 1 := by
    rw [map_pow]
    exact (QuotientGroup.eq_one_iff ((S.diagU e) ^ 6)).2 hmem
  rw [hclass]
  exact Bd.B.one_mem

private theorem rf_gamma_top_US (e : S.US) :
    gamma D S A 2 (⊤ : Ideal (𝓞 F)) (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) = 1 := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let Q := 𝓞 F ⧸ (⊤ : Ideal (𝓞 F))
  have htop0 : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot
  letI : Finite Q := Ring.HasFiniteQuotients.finiteQuotient htop0
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Unique Q :=
    { default := 0
      uniq := fun x => by
        calc
          x = Ideal.Quotient.mk (⊤ : Ideal (𝓞 F)) x.out := (Ideal.Quotient.mk_out x).symm
          _ = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 Submodule.mem_top }
  have hterm (x : Q) :
      chiIdealPow D (⊤ : Ideal (𝓞 F)) (algebraMap (𝓞 F) F x.out) 2 *
        S.e A (S.diag (algebraMap (𝓞 F) F x.out /
          (((e ^ (6 : ℕ) : S.US) : Fˣ) : F))) = 1 := by
    have hchi : chiIdealPow D (⊤ : Ideal (𝓞 F))
        (algebraMap (𝓞 F) F x.out) 2 = 1 := by
      simp [chiIdealPow, ← Ideal.one_eq_top]
    have hvalA (v : FinPlace F) (hv : v ∉ S.Sf) :
        HeightOneSpectrum.valuation F v
          ((((e ^ (6 : ℕ) : S.US) : Fˣ) : F)) = 1 := by
      exact Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F)
        (e ^ (6 : ℕ)) hv
    have hlocal (v : FinPlace F) (hv : v ∉ S.Sf) :
        HeightOneSpectrum.valuation F v
          (algebraMap (𝓞 F) F x.out /
            (((e ^ (6 : ℕ) : S.US) : Fˣ) : F)) ≤ 1 := by
      have hxval : HeightOneSpectrum.valuation F v
          (algebraMap (𝓞 F) F x.out) ≤ 1 := v.valuation_le_one x.out
      calc
        HeightOneSpectrum.valuation F v
            (algebraMap (𝓞 F) F x.out /
              (((e ^ (6 : ℕ) : S.US) : Fˣ) : F)) =
            HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F x.out) /
              HeightOneSpectrum.valuation F v
                (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) := by rw [map_div₀]
        _ = HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F x.out) := by
              rw [hvalA v hv, div_one]
        _ ≤ 1 := hxval
    have he := SData.e_diag_eq S A
      (algebraMap (𝓞 F) F x.out /
        (((e ^ (6 : ℕ) : S.US) : Fˣ) : F)) 0
      (by
        intro v hv
        simpa using hlocal v hv)
      (by
        intro v hv
        simp)
    rw [hchi, he]
    simp
  rw [gamma]
  have hnorm : ((Ideal.absNorm (⊤ : Ideal (𝓞 F)) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) = 1 := by
    simp
  rw [hnorm]
  rw [finsum_eq_sum_of_fintype]
  simp only [Fintype.sum_unique]
  simpa [Units.val_pow_eq_pow_val] using hterm (default : Q)

private theorem rf_prime_product_ext (s : Finset (FinPlace F))
    (hgood : ∀ v ∈ s, v ∉ S.Sf) :
    ∃ I : S.ExtIdeal, I.1 = ∏ v ∈ s, v.asIdeal ∧
      S.IsGen ((∏ v ∈ s, primeGen R v : Fˣ) : F) I.1 ∧
      Bd.Allowed (∏ v ∈ s, primeGen R v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨R.exterior.one, ?_, ?_, ?_⟩
      · simp [R.exterior.one_val]
      · simpa [Finset.prod_empty, R.exterior.one_val] using rf_isGen_one (S := S)
      · simpa only [Finset.prod_empty] using rf_allowed_one (S := S)
  | @insert v s hvs ih =>
      have hvS : v ∉ S.Sf := hgood v (Finset.mem_insert_self v s)
      have hsGood : ∀ w ∈ s, w ∉ S.Sf := fun w hw =>
        hgood w (Finset.mem_insert_of_mem hw)
      obtain ⟨I, hIval, hIgen, hIallow⟩ := ih hsGood
      let J := R.exterior.prime v hvS
      have hπ : primeGen R v = bc.gen J := by simp [primeGen, J, hvS]
      have hJgen : S.IsGen (bc.gen J : F) J.1 := (bc.gen_spec J).1
      have hJallow : Bd.Allowed (bc.gen J) := (bc.gen_spec J).2
      let Inew := R.exterior.mul I J
      have hInewVal : Inew.1 = ∏ w ∈ insert v s, w.asIdeal := by
        rw [show Inew = R.exterior.mul I J by rfl, R.exterior.mul_val,
          hIval, show J.1 = v.asIdeal by simp [J, R.exterior.prime_val],
          Finset.prod_insert hvs]
        exact mul_comm _ _
      have hgenMul : S.IsGen (((∏ w ∈ s, primeGen R w) * bc.gen J : Fˣ) : F) Inew.1 := by
        simpa [Inew, hπ, mul_comm, mul_left_comm, mul_assoc] using
          (rf_isGen_extMul (R := R) I J (∏ w ∈ s, primeGen R w) (bc.gen J)
            hIgen hJgen)
      have hgenEq : (∏ w ∈ insert v s, primeGen R w) =
          (∏ w ∈ s, primeGen R w) * bc.gen J := by
        rw [Finset.prod_insert hvs, hπ]
        ac_rfl
      have hallowMul : Bd.Allowed ((∏ w ∈ s, primeGen R w) * bc.gen J) := by
        change (cls (S.diagU ((∏ w ∈ s, primeGen R w) * bc.gen J)) : S.V) ∈ Bd.B
        rw [map_mul]
        exact Bd.B.mul_mem hIallow hJallow
      refine ⟨Inew, hInewVal, ?_, ?_⟩
      · simpa only [hgenEq] using hgenMul
      · simpa only [hgenEq] using hallowMul

private theorem rf_prime_product_not_le (v : FinPlace F) (s : Finset (FinPlace F))
    (hne : ∀ w ∈ s, w ≠ v) : ¬ (∏ w ∈ s, w.asIdeal) ≤ v.asIdeal := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro h
      exact v.isPrime.ne_top (top_le_iff.mp (by simpa using h))
  | @insert w s hws ih =>
      have hneq : ∀ z ∈ s, z ≠ v := fun z hz => hne z (Finset.mem_insert_of_mem hz)
      intro hle
      have hsplit : w.asIdeal ≤ v.asIdeal ∨ (∏ z ∈ s, z.asIdeal) ≤ v.asIdeal :=
        v.isPrime.mul_le.mp (by simpa [Finset.prod_insert hws] using hle)
      rcases hsplit with hw | hs
      · have heq : w.asIdeal = v.asIdeal := w.isMaximal.eq_of_le v.isPrime.ne_top hw
        exact hne w (Finset.mem_insert_self w s) (HeightOneSpectrum.ext heq)
      · exact ih hneq hs

private theorem rf_prime_product_coprime (v : FinPlace F) (s : Finset (FinPlace F))
    (hne : ∀ w ∈ s, w ≠ v) : IsCoprime (∏ w ∈ s, w.asIdeal) v.asIdeal := by
  apply Ideal.coprime_of_no_prime_ge
  intro P hprod hplace hP
  have hEq : P = v.asIdeal := (v.isMaximal.eq_of_le hP.ne_top hplace).symm
  subst P
  exact rf_prime_product_not_le v s hne hprod

private theorem rf_primeGen_globalVal_one_of_ne (v w : FinPlace F)
    (hv : v ∉ S.Sf) (hw : w ∉ S.Sf) (hne : v ≠ w) :
    HeightOneSpectrum.valuation F w (primeGen R v : F) = 1 := by
  let J := R.exterior.prime v hv
  have hπ : primeGen R v = bc.gen J := by simp [primeGen, J, hv]
  have hJval : J.1 = v.asIdeal := by simp [J, R.exterior.prime_val]
  have hJgen : S.IsGen (bc.gen J : F) J.1 := (bc.gen_spec J).1
  have hwNot : w ∉ R.exterior.support J := by
    intro hmem
    have hdvd : w.asIdeal ∣ v.asIdeal := by
      simpa only [hJval] using (R.exterior.mem_support J w).1 hmem
    have hle : v.asIdeal ≤ w.asIdeal := Ideal.dvd_iff_le.mp hdvd
    have heq : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top hle
    exact hne (HeightOneSpectrum.ext heq)
  have hExp := rf_idealExp_zero_of_not_support R w J hwNot
  have hOrd : ordv w (toLoc w (primeGen R v)) = 0 := by
    calc
      ordv w (toLoc w (primeGen R v)) = ordv w (toLoc w (bc.gen J)) := by rw [hπ]
      _ = idealExp w J.1 := rf_ordv_toLoc_ofGen w hw J (bc.gen J) hJgen
      _ = 0 := by exact_mod_cast hExp
  exact rf_globalVal_one_of_ordv_zero w (primeGen R v) hOrd

private theorem rf_prime_product_gen_unit_at (s : Finset (FinPlace F))
    (hgood : ∀ w ∈ s, w ∉ S.Sf) (v : FinPlace F) (hv : v ∉ S.Sf)
    (hvnot : v ∉ s) :
    HeightOneSpectrum.valuation F v ((∏ w ∈ s, primeGen R w : Fˣ) : F) = 1 := by
  obtain ⟨I, hIval, hIgen, _⟩ := rf_prime_product_ext R s hgood
  have hvNotI : v ∉ R.exterior.support I := by
    intro hmem
    have hdvd := (R.exterior.mem_support I v).1 hmem
    have hdvdProd : v.asIdeal ∣ ∏ w ∈ s, w.asIdeal := by
      simpa only [hIval] using hdvd
    have hne : ∀ w ∈ s, w ≠ v := by
      intro w hw hEq
      exact hvnot (hEq ▸ hw)
    exact rf_prime_product_not_le v s hne (Ideal.dvd_iff_le.mp hdvdProd)
  have hExp := rf_idealExp_zero_of_not_support R v I hvNotI
  have hOrd : ordv v (toLoc v (∏ w ∈ s, primeGen R w)) = 0 := by
    calc
      ordv v (toLoc v (∏ w ∈ s, primeGen R w)) = idealExp v I.1 :=
        rf_ordv_toLoc_ofGen v hv I (∏ w ∈ s, primeGen R w) hIgen
      _ = 0 := by exact_mod_cast hExp
  exact rf_globalVal_one_of_ordv_zero v (∏ w ∈ s, primeGen R w) hOrd

private theorem rf_sqfIdeal_factorization (c : S.SqfExtIdeal) :
    c.1 = ∏ v ∈ R.exterior.support (R.exterior.ofSqf c), v.asIdeal := by
  classical
  let J := R.exterior.ofSqf c
  have hJ0 : J.1 ≠ 0 := by
    simpa only [Ideal.zero_eq_bot] using J.property.1
  have hsqJ : Squarefree J.1 := by
    simpa [J, R.exterior.ofSqf_val] using c.property.2
  have hfac := Ideal.finprod_heightOneSpectrum_factorization (I := J.1) hJ0
  have hsupp : Function.mulSupport (fun v : FinPlace F => v.maxPowDividing J.1) ⊆
      R.exterior.support J := by
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    by_contra hnot
    have he0 := rf_idealExp_zero_of_not_support R v J hnot
    have htop : v.maxPowDividing J.1 = ⊤ := by
      rw [show v.maxPowDividing J.1 = v.asIdeal ^ idealExp v J.1 by rfl,
        he0]
      simp
    simp [htop] at hv
  have hprod := finprod_eq_prod_of_mulSupport_subset
    (fun v : FinPlace F => v.maxPowDividing J.1) hsupp
  have hmax (v : FinPlace F) (hv : v ∈ R.exterior.support J) :
      v.maxPowDividing J.1 = v.asIdeal := by
    have he := rf_idealExp_eq_one_of_squarefree_support R v J hsqJ hv
    rw [show v.maxPowDividing J.1 = v.asIdeal ^ idealExp v J.1 by rfl, he, pow_one]
  have hresult : J.1 = ∏ v ∈ R.exterior.support J, v.asIdeal := by
    calc
      J.1 = ∏ᶠ v : FinPlace F, v.maxPowDividing J.1 := hfac.symm
      _ = ∏ v ∈ R.exterior.support J, v.maxPowDividing J.1 := hprod
      _ = ∏ v ∈ R.exterior.support J, v.asIdeal := by
        apply Finset.prod_congr rfl
        intro v hv
        exact hmax v hv
  simpa [J, R.exterior.ofSqf_val] using hresult

private theorem rf_chiIdealPow_US_six
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (c : S.SqfExtIdeal) (e : S.US) :
    chiIdealPow D c.1 (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) 2 = 1 := by
  classical
  let s := R.exterior.support (R.exterior.ofSqf c)
  have hfactor := rf_sqfIdeal_factorization (R := R) c
  have hunit : ∀ v ∈ s,
      residue v (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) ≠ 0 := by
    intro v hv
    have hvS := R.exterior.support_exterior (R.exterior.ofSqf c) v hv
    have hval : HeightOneSpectrum.valuation F v
        (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) = 1 :=
      Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F)
        (e ^ (6 : ℕ)) hvS
    exact ((a2_bridge_SYMBOL D S).residue_ne_zero v
      (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) (by rw [hval])).mpr hval
  have hlocal (v : FinPlace F) (hv : v ∈ s) :
      chi D v (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) ^ (2 : ℤ) = 1 := by
    have hvS := R.exterior.support_exterior (R.exterior.ofSqf c) v hv
    have hval : HeightOneSpectrum.valuation F v ((e : Fˣ) : F) = 1 :=
      Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F) e hvS
    have hres : residue v ((e : Fˣ) : F) ≠ 0 := by
      exact ((a2_bridge_SYMBOL D S).residue_ne_zero v ((e : Fˣ) : F)
        (by rw [hval])).mpr hval
    have hχ6 := (a2_bridge_SYMBOL D S).chi_six v ((e : Fˣ) : F) hres
    have hχpow := rf_chi_argument_zpow (D := D) (S := S) v hvS (e : Fˣ) hval 6
    have hcoe : (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) =
        (((e : Fˣ) ^ (6 : ℕ) : Fˣ) : F) := by simp
    have hχe6 : chi D v (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) = 1 := by
      calc
        chi D v (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) =
            chi D v (((e : Fˣ) ^ (6 : ℕ) : Fˣ) : F) := by rw [hcoe]
        _ = chi D v ((e : Fˣ) : F) ^ (6 : ℤ) := hχpow
        _ = 1 := by simpa [zpow_natCast] using hχ6
    rw [hχe6]
    norm_num
  calc
    chiIdealPow D c.1 (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) 2 =
        chiIdealPow D (∏ v ∈ s, v.asIdeal)
          (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) 2 := by rw [hfactor]
    _ = ∏ v ∈ s, chi D v (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) ^ (2 : ℤ) :=
      rf_chiIdealPow_primeProduct s _ 2 hunit
    _ = 1 := by
      apply Finset.prod_eq_one
      intro v hv
      exact hlocal v hv

private theorem rf_gamma_six_scale
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (c : S.SqfExtIdeal) (e : S.US) (g : Fˣ)
    (hg : S.IsGen (g : F) c.1) (hallowed : Bd.Allowed g) :
    gamma D S A 2 c.1 ((((e ^ (6 : ℕ) : S.US) : Fˣ) * g : Fˣ) : F) =
      gamma D S A 2 c.1 (g : F) := by
  have he6 : S.IsGen (((e ^ (6 : ℕ) : S.US) : Fˣ) : F) ⊤ := rf_isGen_US (e ^ 6)
  have he6allowed : Bd.Allowed ((e ^ (6 : ℕ) : S.US) : Fˣ) :=
    rf_allowed_six (e : Fˣ)
  have htopSquarefree : Squarefree (⊤ : Ideal (𝓞 F)) := by
    simpa [Ideal.one_eq_top] using (squarefree_one : Squarefree (1 : Ideal (𝓞 F)))
  have hcoprime : IsCoprime (⊤ : Ideal (𝓞 F)) c.1 := by
    rw [Ideal.isCoprime_iff_add]
    simp
  have hcrt := gamma_crt D S A H Bd 2 (⊤ : Ideal (𝓞 F)) c.1
    he6.1 c.property.1 htopSquarefree c.property.2 hcoprime
    ((e ^ (6 : ℕ) : S.US) : Fˣ) g ⟨he6, he6allowed⟩ ⟨hg, hallowed⟩
  have hchiTop : chiIdealPow D (⊤ : Ideal (𝓞 F)) (g : F) 2 = 1 := by
    simp [chiIdealPow, ← Ideal.one_eq_top]
  have hchiC := rf_chiIdealPow_US_six R c e
  have hgammaTop := rf_gamma_top_US (D := D) (S := S) (A := A) e
  rw [hchiC, hgammaTop] at hcrt
  simpa [hchiTop, Ideal.top_mul] using hcrt

private theorem rf_gamma_prime_product
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (s : Finset (FinPlace F))
    (hgood : ∀ v ∈ s, v ∉ S.Sf)
    (hsquarefree : ∀ t ⊆ s, Squarefree (∏ v ∈ t, v.asIdeal)) :
    gamma D S A 2 (∏ v ∈ s, v.asIdeal) ((∏ v ∈ s, primeGen R v : Fˣ) : F) =
      (∏ v ∈ s, gamma D S A 2 v.asIdeal (primeGen R v : F)) *
        (∏ v ∈ s, chi D v
          (((∏ w ∈ s.erase v, primeGen R w : Fˣ) : F)) ^ (2 : ℤ)) := by
  classical
  let pI : Finset (FinPlace F) → Ideal (𝓞 F) := fun t => ∏ v ∈ t, v.asIdeal
  let pG : Finset (FinPlace F) → Fˣ := fun t => ∏ v ∈ t, primeGen R v
  let cross : Finset (FinPlace F) → ℂ := fun t =>
    ∏ v ∈ t, chi D v (((∏ w ∈ t.erase v, primeGen R w : Fˣ) : F)) ^ (2 : ℤ)
  have hAll : ∀ t ⊆ s,
      gamma D S A 2 (pI t) ((pG t : Fˣ) : F) =
        (∏ v ∈ t, gamma D S A 2 v.asIdeal (primeGen R v : F)) * cross t := by
    intro t hts
    induction t using Finset.induction_on with
    | empty =>
        have htop : gamma D S A 2 (⊤ : Ideal (𝓞 F)) (1 : F) = 1 := by
          simpa using rf_gamma_top_US (D := D) (S := S) (A := A) (1 : S.US)
        simpa [pI, pG, cross, htop]
    | @insert v t hvt ih =>
        have htTail : t ⊆ s := Finset.Subset.trans (Finset.subset_insert v t) hts
        have hgoodV : v ∉ S.Sf := hgood v (hts (Finset.mem_insert_self v t))
        have hgoodTail : ∀ w ∈ t, w ∉ S.Sf := fun w hw => hgood w (hts (Finset.mem_insert_of_mem hw))
        have hne : ∀ w ∈ t, w ≠ v := by
          intro w hw heq
          exact hvt (heq ▸ hw)
        obtain ⟨I, hIval, hIgen, hIallow⟩ := rf_prime_product_ext R t hgoodTail
        have hIext : S.IsExterior (pI t) := by simpa [pI, hIval] using I.property
        have hIgen' : S.IsGen ((pG t : Fˣ) : F) (pI t) := by
          simpa [pG, hIval] using hIgen
        have hIsq : Squarefree (pI t) := by simpa [pI] using
          (hsquarefree t htTail)
        have hIcop : IsCoprime (pI t) v.asIdeal := by
          simpa [pI] using rf_prime_product_coprime v t hne
        let J := R.exterior.prime v hgoodV
        have hπ : primeGen R v = bc.gen J := by simp [primeGen, J, hgoodV]
        have hJval : J.1 = v.asIdeal := by simp [J, R.exterior.prime_val]
        have hJext : S.IsExterior v.asIdeal := by simpa [hJval] using J.property
        have hJprime : Prime v.asIdeal := (Ideal.prime_iff_isPrime v.ne_bot).2 v.isPrime
        have hJsq : Squarefree v.asIdeal := hJprime.squarefree
        have hJgen : S.IsGen (primeGen R v : F) v.asIdeal := by
          simpa [hπ, hJval] using (bc.gen_spec J).1
        have hJallow : Bd.Allowed (primeGen R v) := by
          simpa [hπ] using (bc.gen_spec J).2
        have hcrt := gamma_crt D S A H Bd 2 (pI t) v.asIdeal
          hIext hJext hIsq hJsq hIcop (pG t) (primeGen R v)
          ⟨hIgen', hIallow⟩ ⟨hJgen, hJallow⟩
        have hIprod : pI (insert v t) = pI t * v.asIdeal := by
          simp [pI, Finset.prod_insert hvt, mul_comm]
        have hGprod : pG (insert v t) = pG t * primeGen R v := by
          simp [pG, Finset.prod_insert hvt, mul_comm]
        have hvalV : HeightOneSpectrum.valuation F v ((pG t : Fˣ) : F) = 1 :=
          rf_prime_product_gen_unit_at R t hgoodTail v hgoodV hvt
        have hresV : residue v ((pG t : Fˣ) : F) ≠ 0 := by
          exact ((a2_bridge_SYMBOL D S).residue_ne_zero v ((pG t : Fˣ) : F)
            (by rw [hvalV])).mpr hvalV
        have hunitJ : ∀ w ∈ ({v} : Finset (FinPlace F)), residue w ((pG t : Fˣ) : F) ≠ 0 := by
          intro w hw
          have : w = v := Finset.mem_singleton.mp hw
          subst w
          exact hresV
        have hchiJ' := rf_chiIdealPow_primeProduct (D := D) ({v} : Finset (FinPlace F))
          ((pG t : Fˣ) : F) (2 : ℤ) hunitJ
        have hchiJ : chiIdealPow D v.asIdeal ((pG t : Fˣ) : F) 2 =
            chi D v ((pG t : Fˣ) : F) ^ (2 : ℤ) := by
          simpa using hchiJ'
        have hunitI : ∀ w ∈ t, residue w (primeGen R v : F) ≠ 0 := by
          intro w hw
          have hval := rf_primeGen_globalVal_one_of_ne R v w hgoodV
            (hgoodTail w hw) (Ne.symm (hne w hw))
          exact ((a2_bridge_SYMBOL D S).residue_ne_zero w (primeGen R v : F)
            (by rw [hval])).mpr hval
        have hchiI' := rf_chiIdealPow_primeProduct (D := D) t (primeGen R v : F) (2 : ℤ) hunitI
        have hchiI : chiIdealPow D (pI t) (primeGen R v : F) 2 =
            ∏ w ∈ t, chi D w (primeGen R v : F) ^ (2 : ℤ) := by
          simpa [pI] using hchiI'
        have hErase (w : FinPlace F) (hw : w ∈ t) :
            (insert v t).erase w = insert v (t.erase w) := by
          have hvw : v ≠ w := (hne w hw).symm
          ext z
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨hzw, rfl | hz⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hzw, hz⟩
          · intro hz
            rcases hz with rfl | ⟨hzw, hz⟩
            · exact ⟨hvw, Or.inl rfl⟩
            · exact ⟨hzw, Or.inr hz⟩
        have hcrossTail :
            (∏ w ∈ t, chi D w
              (((∏ z ∈ (insert v t).erase w, primeGen R z : Fˣ) : F)) ^ (2 : ℤ)) =
              (∏ w ∈ t, chi D w (primeGen R v : F) ^ (2 : ℤ)) * cross t := by
          calc
            _ = ∏ w ∈ t,
                (chi D w (primeGen R v : F) ^ (2 : ℤ) *
                  chi D w (((∏ z ∈ t.erase w, primeGen R z : Fˣ) : F)) ^ (2 : ℤ)) := by
                    apply Finset.prod_congr rfl
                    intro w hw
                    have hvw : v ∉ t.erase w := by
                      intro hmem
                      exact hvt (Finset.mem_of_mem_erase hmem)
                    have hargs : (∏ z ∈ (insert v t).erase w, primeGen R z) =
                        primeGen R v * (∏ z ∈ t.erase w, primeGen R z) := by
                      rw [hErase w hw, Finset.prod_insert hvw]
                    rw [hargs]
                    have hvalπ := rf_primeGen_globalVal_one_of_ne R v w hgoodV
                      (hgoodTail w hw) (Ne.symm (hne w hw))
                    have hvalOther := rf_prime_product_gen_unit_at R (t.erase w)
                      (fun z hz => hgoodTail z (Finset.mem_of_mem_erase hz))
                      w (hgoodTail w hw) (by simp)
                    have hresπ : residue w (primeGen R v : F) ≠ 0 := by
                      exact ((a2_bridge_SYMBOL D S).residue_ne_zero w
                        (primeGen R v : F) (by rw [hvalπ])).mpr hvalπ
                    have hresOther : residue w
                        ((∏ z ∈ t.erase w, primeGen R z : Fˣ) : F) ≠ 0 := by
                      exact ((a2_bridge_SYMBOL D S).residue_ne_zero w
                        ((∏ z ∈ t.erase w, primeGen R z : Fˣ) : F)
                        (by rw [hvalOther])).mpr hvalOther
                    have hmul := rf_chi_zpow_mul (D := D) (S := S) w (hgoodTail w hw)
                      (primeGen R v : F) ((∏ z ∈ t.erase w, primeGen R z : Fˣ) : F)
                      hresπ hresOther (by rw [hvalπ]) (by rw [hvalOther]) 2
                    simpa only [Units.val_mul] using hmul
            _ = (∏ w ∈ t, chi D w (primeGen R v : F) ^ (2 : ℤ)) * cross t := by
                  rw [Finset.prod_mul_distrib]
        have hcrossRec : cross (insert v t) =
            (∏ w ∈ t, chi D w (primeGen R v : F) ^ (2 : ℤ)) *
              chi D v ((pG t : Fˣ) : F) ^ (2 : ℤ) * cross t := by
          change (∏ w ∈ insert v t, chi D w
            ((∏ z ∈ (insert v t).erase w, primeGen R z : Fˣ) : F) ^ (2 : ℤ)) = _
          rw [Finset.prod_insert hvt,
            show (insert v t).erase v = t by simp [hvt], hcrossTail]
          simp only [pG]
          ac_rfl
        have hGammaInsert :
            gamma D S A 2 (pI (insert v t)) ((pG (insert v t) : Fˣ) : F) =
              (∏ w ∈ insert v t, gamma D S A 2 w.asIdeal (primeGen R w : F)) *
                cross (insert v t) := by
          calc
            _ = chiIdealPow D (pI t) (primeGen R v : F) 2 *
                  chiIdealPow D v.asIdeal ((pG t : Fˣ) : F) 2 *
                    gamma D S A 2 (pI t) ((pG t : Fˣ) : F) *
                    gamma D S A 2 v.asIdeal (primeGen R v : F) := by
                    simpa [hIprod, hGprod, mul_comm, mul_left_comm, mul_assoc] using hcrt
            _ = _ := by
              rw [hchiI, hchiJ, ih htTail, hcrossRec, Finset.prod_insert hvt]
              ring
        exact hGammaInsert
  exact hAll s (Finset.Subset.refl s)

private theorem rf_gamma_sqf_factorization
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (c : S.SqfExtIdeal) :
    gamma D S A 2 c.1 (cgen R c) =
      ∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
        gamma D S A 2 v.asIdeal (primeGen R v : F) *
          chi D v (cgen R c / (primeGen R v : F)) ^ (2 : ℤ) := by
  classical
  let s := R.exterior.support (R.exterior.ofSqf c)
  let g : Fˣ := ∏ v ∈ s, primeGen R v
  have hgood : ∀ v ∈ s, v ∉ S.Sf :=
    fun v hv => R.exterior.support_exterior (R.exterior.ofSqf c) v hv
  have hfactor : c.1 = ∏ v ∈ s, v.asIdeal := rf_sqfIdeal_factorization R c
  have hsquarefree : ∀ t ⊆ s, Squarefree (∏ v ∈ t, v.asIdeal) := by
    intro t ht
    apply c.property.2.squarefree_of_dvd
    rw [hfactor]
    exact Finset.prod_dvd_prod_of_subset t s (fun v => v.asIdeal) ht
  obtain ⟨I, hIval, hIgen, hIallow⟩ := rf_prime_product_ext R s hgood
  have hgen : S.IsGen (g : F) c.1 := by
    simpa only [g, hIval, hfactor] using hIgen
  have hallow : Bd.Allowed g := hIallow
  have hcgen : S.IsGen (bc.gen (R.exterior.ofSqf c) : F) c.1 ∧
      Bd.Allowed (bc.gen (R.exterior.ofSqf c)) := by
    simpa only [R.exterior.ofSqf_val] using bc.gen_spec (R.exterior.ofSqf c)
  obtain ⟨e, he, heq⟩ := Bd.allowed_unique c.1
    (bc.gen (R.exterior.ofSqf c)) g hcgen ⟨hgen, hallow⟩
  let ε : S.US := ⟨e, he⟩
  have hceq : bc.gen (R.exterior.ofSqf c) =
      ((ε ^ (6 : ℕ) : S.US) : Fˣ) * g := by
    simpa only [ε, SubgroupClass.coe_pow] using heq
  have hgamma : gamma D S A 2 c.1 (cgen R c) =
      gamma D S A 2 c.1 (g : F) := by
    unfold cgen
    rw [hceq]
    exact rf_gamma_six_scale R c ε g hgen hallow
  have hcrt := rf_gamma_prime_product R s hgood hsquarefree
  have hchi (v : FinPlace F) (hv : v ∈ s) :
      chi D v (cgen R c / (primeGen R v : F)) ^ (2 : ℤ) =
        chi D v ((∏ w ∈ s.erase v, primeGen R w : Fˣ) : F) ^ (2 : ℤ) := by
    let gv : Fˣ := ∏ w ∈ s.erase v, primeGen R w
    have hvalε : HeightOneSpectrum.valuation F v ((ε : Fˣ) : F) = 1 :=
      Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F) ε (hgood v hv)
    have hvalε6 : HeightOneSpectrum.valuation F v
        (((ε ^ (6 : ℕ) : S.US) : Fˣ) : F) = 1 :=
      Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F)
        (ε ^ (6 : ℕ)) (hgood v hv)
    have hvalgv : HeightOneSpectrum.valuation F v (gv : F) = 1 :=
      rf_prime_product_gen_unit_at R (s.erase v)
        (fun w hw => hgood w (Finset.mem_of_mem_erase hw)) v (hgood v hv) (by simp)
    have hresε : residue v ((ε : Fˣ) : F) ≠ 0 :=
      ((a2_bridge_SYMBOL D S).residue_ne_zero v ((ε : Fˣ) : F)
        (by rw [hvalε])).mpr hvalε
    have hresε6 : residue v (((ε ^ (6 : ℕ) : S.US) : Fˣ) : F) ≠ 0 :=
      ((a2_bridge_SYMBOL D S).residue_ne_zero v
        (((ε ^ (6 : ℕ) : S.US) : Fˣ) : F) (by rw [hvalε6])).mpr hvalε6
    have hresgv : residue v (gv : F) ≠ 0 :=
      ((a2_bridge_SYMBOL D S).residue_ne_zero v (gv : F)
        (by rw [hvalgv])).mpr hvalgv
    have hχ6 : chi D v (((ε ^ (6 : ℕ) : S.US) : Fˣ) : F) = 1 := by
      have hp := rf_chi_argument_zpow (D := D) (S := S) v (hgood v hv)
        (ε : Fˣ) hvalε (6 : ℤ)
      have h6 := (a2_bridge_SYMBOL D S).chi_six v ((ε : Fˣ) : F) hresε
      calc
        chi D v (((ε ^ (6 : ℕ) : S.US) : Fˣ) : F) =
            chi D v ((ε : Fˣ) : F) ^ (6 : ℤ) := by
          simpa using hp
        _ = 1 := by simpa using h6
    have hg : g = gv * primeGen R v := (Finset.prod_erase_mul s (primeGen R) hv).symm
    have harg : cgen R c / (primeGen R v : F) =
        (((ε ^ (6 : ℕ) : S.US) : Fˣ) : F) * (gv : F) := by
      unfold cgen
      rw [hceq, hg]
      simp only [Units.val_mul]
      field_simp
    rw [harg]
    have hmul := rf_chi_zpow_mul (D := D) (S := S) v (hgood v hv)
      (((ε ^ (6 : ℕ) : S.US) : Fˣ) : F) (gv : F) hresε6 hresgv
      (by rw [hvalε6]) (by rw [hvalgv]) (2 : ℤ)
    simpa only [hχ6, one_zpow, one_mul, gv] using hmul
  calc
    gamma D S A 2 c.1 (cgen R c) = gamma D S A 2 c.1 (g : F) := hgamma
    _ = (∏ v ∈ s, gamma D S A 2 v.asIdeal (primeGen R v : F)) *
        ∏ v ∈ s, chi D v ((∏ w ∈ s.erase v, primeGen R w : Fˣ) : F) ^ (2 : ℤ) := by
      simpa only [← hfactor, g] using hcrt
    _ = ∏ v ∈ s, gamma D S A 2 v.asIdeal (primeGen R v : F) *
        chi D v (cgen R c / (primeGen R v : F)) ^ (2 : ℤ) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hv
      rw [hchi v hv]

private theorem rf_chi_sqf_gen_product
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (c : S.SqfExtIdeal)
    (v : FinPlace F) (hv : v ∉ S.Sf)
    (hvc : v ∉ R.exterior.support (R.exterior.ofSqf c)) (e : ℤ) :
    chi D v (cgen R c) ^ e =
      ∏ w ∈ R.exterior.support (R.exterior.ofSqf c),
        chi D v (primeGen R w : F) ^ e := by
  classical
  let s := R.exterior.support (R.exterior.ofSqf c)
  let g : Fˣ := ∏ w ∈ s, primeGen R w
  have hgood : ∀ w ∈ s, w ∉ S.Sf :=
    fun w hw => R.exterior.support_exterior (R.exterior.ofSqf c) w hw
  have hχone : chi D v (1 : F) = 1 := by
    simpa using rf_chi_argument_zpow (D := D) (S := S) v hv (1 : Fˣ)
      (by simp) (0 : ℤ)
  have hprod : ∀ t ⊆ s,
      chi D v ((∏ w ∈ t, primeGen R w : Fˣ) : F) =
        ∏ w ∈ t, chi D v (primeGen R w : F) := by
    intro t hts
    induction t using Finset.induction_on with
    | empty => simp [hχone]
    | @insert w t hwt ih =>
      have htTail : t ⊆ s := Finset.Subset.trans (Finset.subset_insert w t) hts
      have hwS : w ∉ S.Sf := hgood w (hts (Finset.mem_insert_self w t))
      have hwv : w ≠ v := by
        intro heq
        subst w
        exact hvc (hts (Finset.mem_insert_self v t))
      have hvNotT : v ∉ t := by
        intro hmem
        exact hvc (htTail hmem)
      have hvalπ := rf_primeGen_globalVal_one_of_ne R w v hwS hv hwv
      have hvalT := rf_prime_product_gen_unit_at R t
        (fun z hz => hgood z (htTail hz)) v hv hvNotT
      have hmul := (a2_bridge_SYMBOL D S).chi_mul v hv
        (primeGen R w : F) ((∏ z ∈ t, primeGen R z : Fˣ) : F)
        hvalπ.le hvalT.le
      calc
        chi D v ((∏ z ∈ insert w t, primeGen R z : Fˣ) : F) =
            chi D v (primeGen R w : F) *
              chi D v ((∏ z ∈ t, primeGen R z : Fˣ) : F) := by
          simpa only [Finset.prod_insert hwt, Units.val_mul] using hmul
        _ = ∏ z ∈ insert w t, chi D v (primeGen R z : F) := by
          rw [ih htTail, Finset.prod_insert hwt]
  have hfactor : c.1 = ∏ w ∈ s, w.asIdeal := rf_sqfIdeal_factorization R c
  obtain ⟨I, hIval, hIgen, hIallow⟩ := rf_prime_product_ext R s hgood
  have hgen : S.IsGen (g : F) c.1 := by
    simpa only [g, hIval, hfactor] using hIgen
  have hcgen : S.IsGen (bc.gen (R.exterior.ofSqf c) : F) c.1 ∧
      Bd.Allowed (bc.gen (R.exterior.ofSqf c)) := by
    simpa only [R.exterior.ofSqf_val] using bc.gen_spec (R.exterior.ofSqf c)
  obtain ⟨ε₀, hε₀, heq⟩ := Bd.allowed_unique c.1
    (bc.gen (R.exterior.ofSqf c)) g hcgen ⟨hgen, hIallow⟩
  let ε : S.US := ⟨ε₀, hε₀⟩
  have hceq : bc.gen (R.exterior.ofSqf c) =
      ((ε ^ (6 : ℕ) : S.US) : Fˣ) * g := by
    simpa only [ε, SubgroupClass.coe_pow] using heq
  have hvalε : HeightOneSpectrum.valuation F v ((ε : Fˣ) : F) = 1 :=
    Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F) ε hv
  have hvalε6 : HeightOneSpectrum.valuation F v
      (((ε ^ (6 : ℕ) : S.US) : Fˣ) : F) = 1 :=
    Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F)
      (ε ^ (6 : ℕ)) hv
  have hvalg : HeightOneSpectrum.valuation F v (g : F) = 1 :=
    rf_prime_product_gen_unit_at R s hgood v hv hvc
  have hresε : residue v ((ε : Fˣ) : F) ≠ 0 :=
    ((a2_bridge_SYMBOL D S).residue_ne_zero v ((ε : Fˣ) : F)
      hvalε.le).mpr hvalε
  have hχ6 : chi D v (((ε ^ (6 : ℕ) : S.US) : Fˣ) : F) = 1 := by
    have hp := rf_chi_argument_zpow (D := D) (S := S) v hv
      (ε : Fˣ) hvalε (6 : ℤ)
    have h6 := (a2_bridge_SYMBOL D S).chi_six v ((ε : Fˣ) : F) hresε
    calc
      chi D v (((ε ^ (6 : ℕ) : S.US) : Fˣ) : F) =
          chi D v ((ε : Fˣ) : F) ^ (6 : ℤ) := by simpa using hp
      _ = 1 := by simpa using h6
  have hχcg : chi D v (cgen R c) = chi D v (g : F) := by
    unfold cgen
    rw [hceq, Units.val_mul,
      (a2_bridge_SYMBOL D S).chi_mul v hv
        (((ε ^ (6 : ℕ) : S.US) : Fˣ) : F) (g : F) hvalε6.le hvalg.le,
      hχ6, one_mul]
  rw [hχcg, show chi D v (g : F) = ∏ w ∈ s, chi D v (primeGen R w : F)
    from hprod s (Finset.Subset.refl s)]
  exact (Finset.prod_zpow (fun w => chi D v (primeGen R w : F)) s e).symm

private theorem rf_sqf_pairing_product
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (d : S.ExtIdeal) (c : S.SqfExtIdeal)
    (hd : Squarefree d.1) (hdc : IsCoprime d.1 c.1) :
    (∏ v ∈ R.exterior.support d, chi D v (cgen R c)) *
      (∏ w ∈ R.exterior.support (R.exterior.ofSqf c),
        chi D w (bc.gen d : F) ^ (-4 : ℤ)) =
      chiIdealPow D d.1 (cgen R c) 3 := by
  classical
  let dSqf : S.SqfExtIdeal := ⟨d.1, d.property, hd⟩
  have hdExt : R.exterior.ofSqf dSqf = d := by
    apply Subtype.ext
    exact R.exterior.ofSqf_val dSqf
  have hgenD : cgen R dSqf = (bc.gen d : F) := by
    simp only [cgen, hdExt]
  let ds := R.exterior.support d
  let cs := R.exterior.support (R.exterior.ofSqf c)
  have hnotC (v : FinPlace F) (hvd : v ∈ ds) : v ∉ cs := by
    intro hvc
    exact rf_no_common_prime v d.1 c.1 hdc
      ((R.exterior.mem_support d v).1 hvd)
      (by simpa only [R.exterior.ofSqf_val] using
        (R.exterior.mem_support (R.exterior.ofSqf c) v).1 hvc)
  have hnotD (w : FinPlace F) (hwc : w ∈ cs) : w ∉ ds := by
    intro hwd
    exact hnotC w hwd hwc
  have hleft : (∏ v ∈ ds, chi D v (cgen R c)) =
      ∏ v ∈ ds, ∏ w ∈ cs, chi D v (primeGen R w : F) := by
    apply Finset.prod_congr rfl
    intro v hvd
    simpa using rf_chi_sqf_gen_product R c v
      (R.exterior.support_exterior d v hvd) (hnotC v hvd) (1 : ℤ)
  have hright : (∏ w ∈ cs, chi D w (bc.gen d : F) ^ (-4 : ℤ)) =
      ∏ w ∈ cs, ∏ v ∈ ds, chi D w (primeGen R v : F) ^ (-4 : ℤ) := by
    apply Finset.prod_congr rfl
    intro w hwc
    have hwNot : w ∉ R.exterior.support (R.exterior.ofSqf dSqf) := by
      rw [hdExt]
      exact hnotD w hwc
    have h := rf_chi_sqf_gen_product R dSqf w
      (R.exterior.support_exterior (R.exterior.ofSqf c) w hwc) hwNot (-4 : ℤ)
    simpa only [hgenD, hdExt] using h
  have hrightSwap :
      (∏ w ∈ cs, ∏ v ∈ ds, chi D w (primeGen R v : F) ^ (-4 : ℤ)) =
        ∏ v ∈ ds, ∏ w ∈ cs, chi D w (primeGen R v : F) ^ (-4 : ℤ) :=
    Finset.prod_comm
  have hfactorD : d.1 = ∏ v ∈ ds, v.asIdeal := by
    simpa only [hdExt] using rf_sqfIdeal_factorization R dSqf
  have hunit : ∀ v ∈ ds, residue v (cgen R c) ≠ 0 := by
    intro v hvd
    have hvS := R.exterior.support_exterior d v hvd
    have hOrd : ordv v (toLoc v (bc.gen (R.exterior.ofSqf c))) = 0 := by
      rw [rf_ordv_toLoc_ofGen v hvS (R.exterior.ofSqf c)
        (bc.gen (R.exterior.ofSqf c)) (bc.gen_spec (R.exterior.ofSqf c)).1,
        rf_idealExp_zero_of_not_support R v (R.exterior.ofSqf c) (hnotC v hvd)]
      norm_num
    have hval : HeightOneSpectrum.valuation F v (cgen R c) = 1 :=
      rf_globalVal_one_of_ordv_zero v (bc.gen (R.exterior.ofSqf c)) hOrd
    exact ((a2_bridge_SYMBOL D S).residue_ne_zero v (cgen R c) hval.le).mpr hval
  calc
    (∏ v ∈ ds, chi D v (cgen R c)) *
        (∏ w ∈ cs, chi D w (bc.gen d : F) ^ (-4 : ℤ)) =
      (∏ v ∈ ds, ∏ w ∈ cs, chi D v (primeGen R w : F)) *
        (∏ v ∈ ds, ∏ w ∈ cs, chi D w (primeGen R v : F) ^ (-4 : ℤ)) := by
      rw [hleft, hright, hrightSwap]
    _ = ∏ v ∈ ds, ∏ w ∈ cs,
        chi D v (primeGen R w : F) * chi D w (primeGen R v : F) ^ (-4 : ℤ) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hvd
      rw [Finset.prod_mul_distrib]
    _ = ∏ v ∈ ds, ∏ w ∈ cs, chi D v (primeGen R w : F) ^ (3 : ℤ) := by
      apply Finset.prod_congr rfl
      intro v hvd
      apply Finset.prod_congr rfl
      intro w hwc
      have hvw : v ≠ w := by
        intro heq
        subst w
        exact hnotC v hvd hwc
      simpa using rf_prime_pairing_identity R v w
        (R.exterior.support_exterior d v hvd)
        (R.exterior.support_exterior (R.exterior.ofSqf c) w hwc) hvw
    _ = ∏ v ∈ ds, chi D v (cgen R c) ^ (3 : ℤ) := by
      apply Finset.prod_congr rfl
      intro v hvd
      exact (rf_chi_sqf_gen_product R c v
        (R.exterior.support_exterior d v hvd) (hnotC v hvd) (3 : ℤ)).symm
    _ = chiIdealPow D (∏ v ∈ ds, v.asIdeal) (cgen R c) 3 :=
      (rf_chiIdealPow_primeProduct (D := D) ds (cgen R c) 3 hunit).symm
    _ = chiIdealPow D d.1 (cgen R c) 3 := by rw [← hfactorD]

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
  constructor
  · exact rf_exterior_factor_bounds R
  · intro υ h t sd sc d c hd hdh hcf hdc hsd hsc
    let I := Aideal R c t.n
    have hgenA : S.IsGen (Agen R c t.n : F) I.1 := by
      have hcgen := (bc.gen_spec (R.exterior.ofSqf c)).1
      have hngen := (bc.gen_spec t.n).1
      have hngen3 := rf_isGen_extPow R t.n (bc.gen t.n) hngen 3
      have hmul := rf_isGen_extMul R (R.exterior.ofSqf c) (R.exterior.pow t.n 3)
        (bc.gen (R.exterior.ofSqf c)) (bc.gen t.n ^ 3) hcgen hngen3
      change S.IsGen ((bc.gen (R.exterior.ofSqf c) : F) * (bc.gen t.n : F) ^ 3)
        (R.exterior.mul (R.exterior.ofSqf c) (R.exterior.pow t.n 3)).1
      simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using hmul
    have hAallowed : Bd.Allowed (Agen R c t.n) := by
      have hcAllowed := (bc.gen_spec (R.exterior.ofSqf c)).2
      have hnAllowed := (bc.gen_spec t.n).2
      change (cls (S.diagU (bc.gen (R.exterior.ofSqf c) * bc.gen t.n ^ 3)) : S.V) ∈ Bd.B
      rw [map_mul, map_pow]
      exact Bd.B.mul_mem hcAllowed (Bd.B.pow_mem hnAllowed 3)
    have hdecomp : I.1 = c.1 * t.n.1 ^ 3 := by
      dsimp [I, Aideal]
      rw [R.exterior.mul_val, R.exterior.ofSqf_val, R.exterior.pow_val]
    have hcgenC : S.IsGen (bc.gen (R.exterior.ofSqf c) : F) c.1 ∧
        Bd.Allowed (bc.gen (R.exterior.ofSqf c)) := by
      simpa only [R.exterior.ofSqf_val] using
        (bc.gen_spec (R.exterior.ofSqf c))
    have htableData :=
      ArtinPrimitiveRoots.A1.Theta.sphericalTable_product D S A H Bd I.1 I.property
        (Agen R c t.n) ⟨hgenA, hAallowed⟩
    have htableFinite := htableData.1
    have htable := htableData.2.1 c.1 t.n.1
      (bc.gen (R.exterior.ofSqf c)) c.property.2 hdecomp hcgenC
    let ρ : Fˣ := (R.sheets.eps t.u : Fˣ) * bc.gen t.a /
      (bc.gen d * bc.gen t.f) ^ (2 : ℕ)
    have hνfactor : frozenFrequency R t d c = ρ * Agen R c t.n := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
        frozenFrequency, Agen, ρ]
      field_simp
    have hExpA (v : FinPlace F) :
        idealExp v I.1 = idealExp v c.1 + 3 * idealExp v t.n.1 := by
      rw [hdecomp, rf_idealExp_mul v c.1 (t.n.1 ^ 3)
        (by simpa only [Ideal.zero_eq_bot] using c.property.1.1)
        (pow_ne_zero _ (by simpa only [Ideal.zero_eq_bot] using t.n.property.1))]
      rw [rf_idealExp_pow v t.n.1
        (by simpa only [Ideal.zero_eq_bot] using t.n.property.1) 3]
    have hcop_dn : IsCoprime d.1 t.n.1 := hdh.of_mul_right_right
    have hcop_dh : IsCoprime d.1 h.1 := hdh.of_mul_right_left
    have hnotA (v : FinPlace F) (hvf : v ∉ R.exterior.support t.f) :
        v ∉ R.exterior.support t.a := by
      intro hva
      exact hvf (t.numerator.1 v hva)
    have hgenAOrd0 (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∉ R.exterior.support t.f) :
        ordv v (toLoc v (bc.gen t.a)) = 0 := by
      rw [rf_ordv_toLoc_ofGen v hv t.a (bc.gen t.a)
        (bc.gen_spec t.a).1,
        rf_idealExp_zero_of_not_support R v t.a (hnotA v hvf)]
      norm_num
    have hgenDOrd0 (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∉ R.exterior.support d) :
        ordv v (toLoc v (bc.gen d)) = 0 := by
      rw [rf_ordv_toLoc_ofGen v hv d (bc.gen d) (bc.gen_spec d).1,
        rf_idealExp_zero_of_not_support R v d hvd]
      norm_num
    have hgenFOrd0 (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∉ R.exterior.support t.f) :
        ordv v (toLoc v (bc.gen t.f)) = 0 := by
      rw [rf_ordv_toLoc_ofGen v hv t.f (bc.gen t.f) (bc.gen_spec t.f).1,
        rf_idealExp_zero_of_not_support R v t.f hvf]
      norm_num
    have hεOrd0 (v : FinPlace F) (hv : v ∉ S.Sf) :
        ordv v (toLoc v (R.sheets.eps t.u : Fˣ)) = 0 := by
      have hval : HeightOneSpectrum.valuation F v
          ((R.sheets.eps t.u : Fˣ) : F) = 1 :=
        Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F)
          (R.sheets.eps t.u) hv
      have hloc : Valued.v (toLoc v (R.sheets.eps t.u : Fˣ) : v.adicCompletion F) = 1 := by
        change Valued.v (algebraMap F (v.adicCompletion F)
          ((R.sheets.eps t.u : Fˣ) : F)) = 1
        simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
          Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hval]
      rw [rf_ordv_local_log, hloc]
      simp
    have hcop_nf : IsCoprime t.n.1 t.f.1 := t.coprime
    have hno_d_c (v : FinPlace F) (hvd : v ∈ R.exterior.support d) :
        v ∉ R.exterior.support (R.exterior.ofSqf c) := by
      intro hvc
      apply rf_no_common_prime v d.1 c.1 hdc
        ((R.exterior.mem_support d v).1 hvd)
      simpa only [R.exterior.ofSqf_val] using (R.exterior.mem_support (R.exterior.ofSqf c) v).1 hvc
    have hno_d_n (v : FinPlace F) (hvd : v ∈ R.exterior.support d) :
        v ∉ R.exterior.support t.n := by
      intro hvn
      exact rf_no_common_prime v d.1 t.n.1 hcop_dn
        ((R.exterior.mem_support d v).1 hvd) ((R.exterior.mem_support t.n v).1 hvn)
    have hno_d_f (v : FinPlace F) (hvd : v ∈ R.exterior.support d) :
        v ∉ R.exterior.support t.f := by
      intro hvf
      have hvh : v ∈ R.exterior.support h := t.active.2.1 v hvf
      exact rf_no_common_prime v d.1 h.1 hcop_dh
        ((R.exterior.mem_support d v).1 hvd) ((R.exterior.mem_support h v).1 hvh)
    have hno_f_c (v : FinPlace F) (hvf : v ∈ R.exterior.support t.f) :
        v ∉ R.exterior.support (R.exterior.ofSqf c) := by
      intro hvc
      exact rf_no_common_prime v c.1 t.f.1 hcf
        (by simpa only [R.exterior.ofSqf_val] using
          (R.exterior.mem_support (R.exterior.ofSqf c) v).1 hvc)
        ((R.exterior.mem_support t.f v).1 hvf)
    have hno_f_n (v : FinPlace F) (hvf : v ∈ R.exterior.support t.f) :
        v ∉ R.exterior.support t.n := by
      intro hvn
      exact rf_no_common_prime v t.f.1 t.n.1 t.coprime.symm
        ((R.exterior.mem_support t.f v).1 hvf) ((R.exterior.mem_support t.n v).1 hvn)
    have hno_f_d (v : FinPlace F) (hvf : v ∈ R.exterior.support t.f) :
        v ∉ R.exterior.support d := by
      intro hvd
      have hvh : v ∈ R.exterior.support h := t.active.2.1 v hvf
      exact rf_no_common_prime v h.1 d.1 hcop_dh.symm
        ((R.exterior.mem_support h v).1 hvh) ((R.exterior.mem_support d v).1 hvd)
    have hI_support : ∀ v : FinPlace F, v ∈ R.exterior.support I →
        v ∈ R.exterior.support (R.exterior.ofSqf c) ∨ v ∈ R.exterior.support t.n := by
      intro v hvI
      by_contra hn
      have hnotc : v ∉ R.exterior.support (R.exterior.ofSqf c) := by
        intro hc
        exact hn (Or.inl hc)
      have hnotn : v ∉ R.exterior.support t.n := by
        intro hn'
        exact hn (Or.inr hn')
      have hc0' := rf_idealExp_zero_of_not_support R v (R.exterior.ofSqf c) hnotc
      have hc0 : idealExp v c.1 = 0 := by
        simpa only [R.exterior.ofSqf_val] using hc0'
      have hn0 := rf_idealExp_zero_of_not_support R v t.n hnotn
      have hI0 : idealExp v I.1 = 0 := by rw [hExpA v, hc0, hn0]
      exact ((rf_idealExp_ne_zero_iff_support R v I).mpr hvI) hI0
    have hOrdInv (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
        ordv v x⁻¹ = -ordv v x := by
      have hm := rf_ordv_mul v x x⁻¹
      have hone : ordv v (1 : (v.adicCompletion F)ˣ) = 0 := by
        simp [ordv]
        rfl
      rw [mul_inv_cancel, hone] at hm
      linarith
    have hOrdDiv (v : FinPlace F) (x y : (v.adicCompletion F)ˣ) :
        ordv v (x / y) = ordv v x - ordv v y := by
      rw [div_eq_mul_inv, rf_ordv_mul, hOrdInv]
      ring
    have hOrdPow2 (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
        ordv v (x ^ (2 : ℕ)) = 2 * ordv v x := by
      calc
        ordv v (x ^ (2 : ℕ)) = ordv v (x * x) := by rw [pow_two]
        _ = ordv v x + ordv v x := rf_ordv_mul v x x
        _ = 2 * ordv v x := by ring
    have hρmap (v : FinPlace F) : toLoc v ρ =
        (toLoc v (R.sheets.eps t.u : Fˣ) * toLoc v (bc.gen t.a)) /
          (toLoc v (bc.gen d) * toLoc v (bc.gen t.f)) ^ (2 : ℕ) := by
      dsimp [ρ]
      simp [map_mul, map_div, div_eq_mul_inv, map_pow]
    have hρord (v : FinPlace F) :
        ordv v (toLoc v ρ) =
          ordv v (toLoc v (R.sheets.eps t.u : Fˣ)) +
            ordv v (toLoc v (bc.gen t.a)) -
              2 * (ordv v (toLoc v (bc.gen d)) + ordv v (toLoc v (bc.gen t.f))) := by
      rw [hρmap, hOrdDiv, rf_ordv_mul, hOrdPow2, rf_ordv_mul]
    have hρord_d (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∈ R.exterior.support d) : ordv v (toLoc v ρ) = -2 := by
      have ha0 : ordv v (toLoc v (bc.gen t.a)) = 0 := by
        rw [rf_ordv_toLoc_ofGen v hv t.a (bc.gen t.a) (bc.gen_spec t.a).1,
          rf_idealExp_zero_of_not_support R v t.a (hnotA v (hno_d_f v hvd))]
        rfl
      have hd1 : ordv v (toLoc v (bc.gen d)) = 1 := by
        rw [rf_ordv_toLoc_ofGen v hv d (bc.gen d) (bc.gen_spec d).1,
          rf_idealExp_eq_one_of_squarefree_support R v d hd hvd]
        rfl
      have hf0 : ordv v (toLoc v (bc.gen t.f)) = 0 := hgenFOrd0 v hv (hno_d_f v hvd)
      rw [hρord, hεOrd0 v hv, ha0, hd1, hf0]
      norm_num
    have hρord_f (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) :
        ordv v (toLoc v ρ) = idealExp v t.a.1 - 2 := by
      have ha : ordv v (toLoc v (bc.gen t.a)) = idealExp v t.a.1 :=
        rf_ordv_toLoc_ofGen v hv t.a (bc.gen t.a) (bc.gen_spec t.a).1
      have hd0 : ordv v (toLoc v (bc.gen d)) = 0 := hgenDOrd0 v hv (hno_f_d v hvf)
      have hf1 : ordv v (toLoc v (bc.gen t.f)) = 1 := by
        rw [rf_ordv_toLoc_ofGen v hv t.f (bc.gen t.f) (bc.gen_spec t.f).1,
          rf_idealExp_eq_one_of_squarefree_support R v t.f t.active.1 hvf]
        rfl
      rw [hρord, hεOrd0 v hv, ha, hd0, hf1]
      ring
    have hρord_out (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∉ R.exterior.support d) (hvf : v ∉ R.exterior.support t.f) :
        ordv v (toLoc v ρ) = 0 := by
      rw [hρord, hεOrd0 v hv, hgenAOrd0 v hv hvf,
        hgenDOrd0 v hv hvd, hgenFOrd0 v hv hvf]
      ring
    have hνord (v : FinPlace F) (hv : v ∉ S.Sf) :
        ordv v (toLoc v (frozenFrequency R t d c)) =
          ordv v (toLoc v ρ) + ordv v (toLoc v (Agen R c t.n)) := by
      have hmapν : toLoc v (frozenFrequency R t d c) =
          toLoc v ρ * toLoc v (Agen R c t.n) := by
        rw [← map_mul, hνfactor]
      calc
        ordv v (toLoc v (frozenFrequency R t d c)) =
            ordv v (toLoc v ρ * toLoc v (Agen R c t.n)) := by rw [hmapν]
        _ = ordv v (toLoc v ρ) + ordv v (toLoc v (Agen R c t.n)) :=
          rf_ordv_mul v _ _
    have hνord_d (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∈ R.exterior.support d) :
        ordv v (toLoc v (frozenFrequency R t d c)) = -2 := by
      have hInot : v ∉ R.exterior.support I := by
        intro hvI
        rcases hI_support v hvI with hc | hn
        · exact hno_d_c v hvd hc
        · exact hno_d_n v hvd hn
      rw [hνord v hv, hρord_d v hv hvd,
        rf_ordv_toLoc_ofGen v hv I (Agen R c t.n) hgenA,
        rf_idealExp_zero_of_not_support R v I hInot]
      norm_num
    have hνord_f (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) :
        ordv v (toLoc v (frozenFrequency R t d c)) = idealExp v t.a.1 - 2 := by
      have hInot : v ∉ R.exterior.support I := by
        intro hvI
        rcases hI_support v hvI with hc | hn
        · exact hno_f_c v hvf hc
        · exact hno_f_n v hvf hn
      rw [hνord v hv, hρord_f v hv hvf,
        rf_ordv_toLoc_ofGen v hv I (Agen R c t.n) hgenA,
        rf_idealExp_zero_of_not_support R v I hInot]
      ring
    have hρval (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∉ R.exterior.support d) (hvf : v ∉ R.exterior.support t.f) :
        Valued.v ((toLoc v ρ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      exact rf_localVal_one_of_ordv_zero v (toLoc v ρ)
        (hρord_out v hv hvd hvf)
    have hνunitPart (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∉ R.exterior.support d) (hvf : v ∉ R.exterior.support t.f) :
        unitPart v (toLoc v (frozenFrequency R t d c)) =
          toLoc v ρ * unitPart v (toLoc v (Agen R c t.n)) := by
      have hmapν : toLoc v (frozenFrequency R t d c) =
          toLoc v ρ * toLoc v (Agen R c t.n) := by
        rw [← map_mul, hνfactor]
      rw [hmapν]
      exact rf_unitPart_mul_of_ord_zero v (toLoc v ρ) (toLoc v (Agen R c t.n))
        (hρord_out v hv hvd hvf)
    have hρLocUnit (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∉ R.exterior.support d) (hvf : v ∉ R.exterior.support t.f) :
        ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (toLoc v ρ) := by
      simpa [unitPart, hρord_out v hv hvd hvf] using
        (ArtinPrimitiveRoots.A1.Theta.thFactorB_unitPart_isLocUnit v (toLoc v ρ))
    have hWν (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∉ R.exterior.support d) (hvf : v ∉ R.exterior.support t.f) :
        R.T.Wv v (R.C.a v (toLoc v (frozenFrequency R t d c))) =
          localChi D v (toLoc v ρ) ^ (2 * ordv v (toLoc v (Agen R c t.n))) *
            R.T.Wv v (R.C.a v (toLoc v (Agen R c t.n))) := by
      rw [rf_Wv_sphericalTable R v hv (toLoc v (frozenFrequency R t d c)),
        rf_Wv_sphericalTable R v hv (toLoc v (Agen R c t.n)),
        hνord v hv, hρord_out v hv hvd hvf, zero_add,
        hνunitPart v hv hvd hvf]
      exact rf_sphericalTable_unit_mul v hv (ordv v (toLoc v (Agen R c t.n)))
        (toLoc v ρ) (unitPart v (toLoc v (Agen R c t.n)))
        (hρLocUnit v hv hvd hvf)
        (ArtinPrimitiveRoots.A1.Theta.thFactorB_unitPart_isLocUnit v
          (toLoc v (Agen R c t.n)))
    have hprimeGen (v : FinPlace F) (hv : v ∉ S.Sf) :
        S.IsGen (primeGen R v : F) (R.exterior.prime v hv).1 := by
      simpa [primeGen, hv, R.exterior.prime_val v hv] using
        (bc.gen_spec (R.exterior.prime v hv)).1
    have hprimeExp (v : FinPlace F) (hv : v ∉ S.Sf) :
        idealExp v (R.exterior.prime v hv).1 = 1 := by
      rw [R.exterior.prime_val]
      unfold idealExp
      exact Associates.count_self v.associates_irreducible
    have hprimeOrd (v : FinPlace F) (hv : v ∉ S.Sf) :
        ordv v (toLoc v (primeGen R v)) = 1 := by
      calc
        ordv v (toLoc v (primeGen R v)) = idealExp v (R.exterior.prime v hv).1 :=
          rf_ordv_toLoc_ofGen v hv (R.exterior.prime v hv) (primeGen R v)
            (hprimeGen v hv)
        _ = 1 := by exact_mod_cast hprimeExp v hv
    let τd (v : FinPlace F) :=
      toLoc v (frozenFrequency R t d c) * toLoc v (primeGen R v) ^ (2 : ℕ)
    have hτdOrd (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∈ R.exterior.support d) : ordv v (τd v) = 0 := by
      dsimp [τd]
      rw [rf_ordv_mul, hOrdPow2, hνord_d v hv hvd, hprimeOrd v hv]
      norm_num
    have hτdLocUnit (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∈ R.exterior.support d) :
        ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (τd v) := by
      have hval := rf_localVal_one_of_ordv_zero v (τd v) (hτdOrd v hv hvd)
      constructor
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        have hinv : Valued.v (((τd v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
          simp [hval]
        rw [hinv]
    have hlocal_d (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∈ R.exterior.support d) :
        localR R v 1 0 (toLoc v (frozenFrequency R t d c) *
          toLoc v (primeGen R v) ^ 2) =
            localOmega R v * localChi D v (τd v) := by
      have hw := lem_reflection_local_Weyl R v hv 1 0 (τd v)
        (hτdLocUnit v hv hvd).1 (hτdLocUnit v hv hvd).2
      change localR R v 1 0 (τd v) = _
      exact hw.2.2.2.1 rfl rfl
    let τf (v : FinPlace F) := toLoc v (frozenFrequency R t d c) *
      toLoc v (primeGen R v) ^ (2 - (idealExp v t.a.1 : ℤ))
    have hτfOrd (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) : ordv v (τf v) = 0 := by
      dsimp [τf]
      rw [rf_ordv_mul, rf_ordv_zpow, hνord_f v hv hvf, hprimeOrd v hv]
      ring
    have hτfLocUnit (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) :
        ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (τf v) := by
      have hval := rf_localVal_one_of_ordv_zero v (τf v) (hτfOrd v hv hvf)
      constructor
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        have hinv : Valued.v (((τf v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
          simp [hval]
        rw [hinv]
    have hlocal_f (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) :
        localR R v (frozenJ t v) (idealExp v t.a.1)
          (toLoc v (frozenFrequency R t d c) *
            toLoc v (primeGen R v) ^ (2 - (idealExp v t.a.1 : ℤ))) =
          localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
            localChi D v (τf v) ^ frozenB t v := by
      have hw := lem_reflection_local_Weyl R v hv (frozenJ t v)
        (idealExp v t.a.1) (τf v)
        (hτfLocUnit v hv hvf).1 (hτfLocUnit v hv hvf).2
      obtain ⟨_, _, _, _, _, _, _, hpow, _, _⟩ := hw
      have he : (0 : ℤ) ≤ idealExp v t.a.1 := Int.natCast_nonneg _
      change localR R v (frozenJ t v) (idealExp v t.a.1) (τf v) = _
      exact hpow he
    let δd (v : FinPlace F) : Fˣ :=
      frozenFrequency R t d c * primeGen R v ^ (2 : ℕ)
    have hτdMap (v : FinPlace F) : toLoc v (δd v) = τd v := by
      dsimp [δd, τd]
      simp [map_mul, map_pow]
    have hτdChi (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∈ R.exterior.support d) :
        localChi D v (τd v) = chi D v (δd v : F) := by
      rw [← hτdMap v]
      apply rf_localChi_toLoc v hv (δd v)
      exact rf_globalVal_one_of_ordv_zero v (δd v) (by
        rw [hτdMap v]
        exact hτdOrd v hv hvd)
    let θd (v : FinPlace F) : Fˣ :=
      (R.sheets.eps t.u : Fˣ) * bc.gen t.a * bc.gen t.n ^ (3 : ℕ) *
        (bc.gen d / primeGen R v) ^ (-2 : ℤ) * (bc.gen t.f) ^ (-2 : ℤ)
    have hδdFactor (v : FinPlace F) :
        δd v = θd v * bc.gen (R.exterior.ofSqf c) := by
      apply Units.ext
      simp only [δd, θd, frozenFrequency, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val]
      field_simp
    have hgenCOrd_d (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∈ R.exterior.support d) :
        ordv v (toLoc v (bc.gen (R.exterior.ofSqf c))) = 0 := by
      rw [rf_ordv_toLoc_ofGen v hv (R.exterior.ofSqf c)
          (bc.gen (R.exterior.ofSqf c)) (bc.gen_spec _).1,
        rf_idealExp_zero_of_not_support R v (R.exterior.ofSqf c) (hno_d_c v hvd)]
      norm_num
    have hθdOrd (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∈ R.exterior.support d) : ordv v (toLoc v (θd v)) = 0 := by
      have hδ : ordv v (toLoc v (δd v)) = 0 := by
        rw [hτdMap v]
        exact hτdOrd v hv hvd
      have hmap : toLoc v (δd v) =
          toLoc v (θd v) * toLoc v (bc.gen (R.exterior.ofSqf c)) := by
        rw [← map_mul, hδdFactor]
      rw [hmap, rf_ordv_mul, hgenCOrd_d v hv hvd] at hδ
      linarith
    have hχdSplit (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvd : v ∈ R.exterior.support d) :
        chi D v (δd v : F) =
          chi D v (θd v : F) * chi D v (bc.gen (R.exterior.ofSqf c) : F) := by
      have hfield : (δd v : F) = (θd v : F) * (bc.gen (R.exterior.ofSqf c) : F) :=
        congrArg (fun z : Fˣ => (z : F)) (hδdFactor v)
      have htVal := rf_globalVal_one_of_ordv_zero v (θd v) (hθdOrd v hv hvd)
      have hcVal := rf_globalVal_one_of_ordv_zero v
        (bc.gen (R.exterior.ofSqf c)) (hgenCOrd_d v hv hvd)
      have htLe : HeightOneSpectrum.valuation F v (θd v : F) ≤ 1 := by
        rw [htVal]
      have hcLe : HeightOneSpectrum.valuation F v
          (bc.gen (R.exterior.ofSqf c) : F) ≤ 1 := by rw [hcVal]
      have htRes := ((a2_bridge_SYMBOL D S).residue_ne_zero v (θd v : F) htLe).mpr htVal
      have hcRes := ((a2_bridge_SYMBOL D S).residue_ne_zero v
        (bc.gen (R.exterior.ofSqf c) : F) hcLe).mpr hcVal
      have hmul := rf_chi_zpow_mul (D := D) (S := S) v hv (θd v : F)
        (bc.gen (R.exterior.ofSqf c) : F) htRes hcRes htLe hcLe 1
      calc
        chi D v (δd v : F) = chi D v ((θd v : F) * (bc.gen (R.exterior.ofSqf c) : F)) := by
          rw [hfield]
        _ = chi D v (θd v : F) * chi D v (bc.gen (R.exterior.ofSqf c) : F) := by
          simpa using hmul
    let δf (v : FinPlace F) : Fˣ :=
      frozenFrequency R t d c * primeGen R v ^ (2 - (idealExp v t.a.1 : ℤ))
    have hτfMap (v : FinPlace F) : toLoc v (δf v) = τf v := by
      dsimp [δf, τf]
      simp [map_mul, map_zpow]
    have hτfChi (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) :
        localChi D v (τf v) = chi D v (δf v : F) := by
      rw [← hτfMap v]
      apply rf_localChi_toLoc v hv (δf v)
      exact rf_globalVal_one_of_ordv_zero v (δf v) (by
        rw [hτfMap v]
        exact hτfOrd v hv hvf)
    let θf (v : FinPlace F) : Fˣ :=
      (R.sheets.eps t.u : Fˣ) * bc.gen t.a /
        (primeGen R v) ^ (idealExp v t.a.1) * bc.gen t.n ^ (3 : ℕ) *
          (bc.gen t.f / primeGen R v) ^ (-2 : ℤ)
    have hδfFactor (v : FinPlace F) :
        δf v = θf v * bc.gen (R.exterior.ofSqf c) * (bc.gen d) ^ (-2 : ℤ) := by
      apply Units.ext
      simp only [δf, θf, frozenFrequency, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val]
      field_simp
      rw [← zpow_natCast]
      rw [← zpow_add₀ (Units.ne_zero (primeGen R v))]
      rw [← zpow_natCast]
      congr 1
      ring
    have hgenCOrd_f (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) :
        ordv v (toLoc v (bc.gen (R.exterior.ofSqf c))) = 0 := by
      rw [rf_ordv_toLoc_ofGen v hv (R.exterior.ofSqf c)
          (bc.gen (R.exterior.ofSqf c)) (bc.gen_spec _).1,
        rf_idealExp_zero_of_not_support R v (R.exterior.ofSqf c) (hno_f_c v hvf)]
      norm_num
    have hgenDOrd_f (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) :
        ordv v (toLoc v (bc.gen d)) = 0 := hgenDOrd0 v hv (hno_f_d v hvf)
    have hDpowOrd_f (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) :
        ordv v (toLoc v ((bc.gen d) ^ (-2 : ℤ))) = 0 := by
      rw [show toLoc v ((bc.gen d) ^ (-2 : ℤ)) =
          (toLoc v (bc.gen d)) ^ (-2 : ℤ) by simp [map_zpow],
        rf_ordv_zpow, hgenDOrd_f v hv hvf]
      norm_num
    have hθfOrd (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) : ordv v (toLoc v (θf v)) = 0 := by
      have hδ : ordv v (toLoc v (δf v)) = 0 := by
        rw [hτfMap v]
        exact hτfOrd v hv hvf
      have hmap : toLoc v (δf v) =
          toLoc v (θf v) * toLoc v (bc.gen (R.exterior.ofSqf c)) *
            toLoc v ((bc.gen d) ^ (-2 : ℤ)) := by
        simpa [map_mul, map_zpow] using congrArg (toLoc v) (hδfFactor v)
      rw [hmap, rf_ordv_mul, rf_ordv_mul, hgenCOrd_f v hv hvf,
        hDpowOrd_f v hv hvf] at hδ
      linarith
    have hmapθgc (v : FinPlace F) : toLoc v (θf v * bc.gen (R.exterior.ofSqf c)) =
        toLoc v (θf v) * toLoc v (bc.gen (R.exterior.ofSqf c)) := by simp [map_mul]
    have hθgcOrd_f (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) :
        ordv v (toLoc v (θf v * bc.gen (R.exterior.ofSqf c))) = 0 := by
      rw [hmapθgc v, rf_ordv_mul, hθfOrd v hv hvf, hgenCOrd_f v hv hvf]
      norm_num
    have hθfChiSplit (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvf : v ∈ R.exterior.support t.f) :
        chi D v (δf v : F) ^ frozenB t v =
          chi D v (θf v : F) ^ frozenB t v *
            chi D v (bc.gen (R.exterior.ofSqf c) : F) ^ frozenB t v *
              chi D v (bc.gen d : F) ^ (-2 * frozenB t v) := by
      have hfield : (δf v : F) =
          (θf v : F) * (bc.gen (R.exterior.ofSqf c) : F) *
            (((bc.gen d) ^ (-2 : ℤ) : Fˣ) : F) :=
        congrArg (fun z : Fˣ => (z : F)) (hδfFactor v)
      have htVal := rf_globalVal_one_of_ordv_zero v (θf v) (hθfOrd v hv hvf)
      have hcVal := rf_globalVal_one_of_ordv_zero v
        (bc.gen (R.exterior.ofSqf c)) (hgenCOrd_f v hv hvf)
      have htcVal := rf_globalVal_one_of_ordv_zero v
        (θf v * bc.gen (R.exterior.ofSqf c)) (hθgcOrd_f v hv hvf)
      have hdVal := rf_globalVal_one_of_ordv_zero v (bc.gen d)
        (hgenDOrd_f v hv hvf)
      have hd2Val := rf_globalVal_one_of_ordv_zero v ((bc.gen d) ^ (-2 : ℤ))
        (hDpowOrd_f v hv hvf)
      have htLe : HeightOneSpectrum.valuation F v (θf v : F) ≤ 1 := by rw [htVal]
      have hcLe : HeightOneSpectrum.valuation F v
          (bc.gen (R.exterior.ofSqf c) : F) ≤ 1 := by rw [hcVal]
      have htcLe : HeightOneSpectrum.valuation F v
          ((θf v * bc.gen (R.exterior.ofSqf c) : Fˣ) : F) ≤ 1 := by rw [htcVal]
      have hd2Le : HeightOneSpectrum.valuation F v
          (((bc.gen d) ^ (-2 : ℤ) : Fˣ) : F) ≤ 1 := by rw [hd2Val]
      have htRes := ((a2_bridge_SYMBOL D S).residue_ne_zero v (θf v : F) htLe).mpr htVal
      have hcRes := ((a2_bridge_SYMBOL D S).residue_ne_zero v
        (bc.gen (R.exterior.ofSqf c) : F) hcLe).mpr hcVal
      have htcRes := ((a2_bridge_SYMBOL D S).residue_ne_zero v
        ((θf v * bc.gen (R.exterior.ofSqf c) : Fˣ) : F) htcLe).mpr htcVal
      have hd2Res := ((a2_bridge_SYMBOL D S).residue_ne_zero v
        (((bc.gen d) ^ (-2 : ℤ) : Fˣ) : F) hd2Le).mpr hd2Val
      have hmul₂ := rf_chi_zpow_mul (D := D) (S := S) v hv
        ((θf v * bc.gen (R.exterior.ofSqf c) : Fˣ) : F)
        (((bc.gen d) ^ (-2 : ℤ) : Fˣ) : F)
        htcRes hd2Res htcLe hd2Le (frozenB t v)
      have hmul₁ := rf_chi_zpow_mul (D := D) (S := S) v hv
        (θf v : F) (bc.gen (R.exterior.ofSqf c) : F)
        htRes hcRes htLe hcLe (frozenB t v)
      have hmul₁' :
          chi D v ((θf v * bc.gen (R.exterior.ofSqf c) : Fˣ) : F) ^ frozenB t v =
            chi D v (θf v : F) ^ frozenB t v *
              chi D v (bc.gen (R.exterior.ofSqf c) : F) ^ frozenB t v := by
        simpa only [Units.val_mul] using hmul₁
      have hchiDVal := rf_globalVal_one_of_ordv_zero v (bc.gen d)
        (hgenDOrd_f v hv hvf)
      have hchiDRes := ((a2_bridge_SYMBOL D S).residue_ne_zero v
        (bc.gen d : F) (by rw [hchiDVal])).mpr hchiDVal
      have hchiDpow := rf_chi_argument_zpow (D := D) (S := S) v hv (bc.gen d)
        hchiDVal (-2 : ℤ)
      calc
        chi D v (δf v : F) ^ frozenB t v =
            chi D v (((θf v * bc.gen (R.exterior.ofSqf c) : Fˣ) : F) *
              (((bc.gen d) ^ (-2 : ℤ) : Fˣ) : F)) ^ frozenB t v := by
                rw [hfield]
                simp only [Units.val_mul, mul_assoc]
        _ = chi D v ((θf v * bc.gen (R.exterior.ofSqf c) : Fˣ) : F) ^ frozenB t v *
              chi D v (((bc.gen d) ^ (-2 : ℤ) : Fˣ) : F) ^ frozenB t v := by
                simpa using hmul₂
        _ = chi D v (θf v : F) ^ frozenB t v *
                chi D v (bc.gen (R.exterior.ofSqf c) : F) ^ frozenB t v *
                chi D v (bc.gen d : F) ^ (-2 * frozenB t v) := by
                  rw [hmul₁', hchiDpow, zpow_mul]
    have hnotI_d (v : FinPlace F) (hvd : v ∈ R.exterior.support d) :
        v ∉ R.exterior.support I := by
      intro hvI
      rcases hI_support v hvI with hc | hn
      · exact hno_d_c v hvd hc
      · exact hno_d_n v hvd hn
    have hnotI_f (v : FinPlace F) (hvf : v ∈ R.exterior.support t.f) :
        v ∉ R.exterior.support I := by
      intro hvI
      rcases hI_support v hvI with hc | hn
      · exact hno_f_c v hvf hc
      · exact hno_f_n v hvf hn
    have hIExpZero (v : FinPlace F) (hvI : v ∉ R.exterior.support I) :
        idealExp v I.1 = 0 := rf_idealExp_zero_of_not_support R v I hvI
    have hAordZero (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvI : v ∉ R.exterior.support I) :
        ordv v (toLoc v (Agen R c t.n)) = 0 := by
      rw [rf_ordv_toLoc_ofGen v hv I (Agen R c t.n) hgenA,
        hIExpZero v hvI]
      norm_num
    have hAtableOne (v : FinPlace F) (hv : v ∉ S.Sf)
        (hvI : v ∉ R.exterior.support I) :
        sphericalTable D A v (ordv v (toLoc v (Agen R c t.n)))
          (unitPart v (toLoc v (Agen R c t.n))) = 1 := by
      rw [hAordZero v hv hvI]
      simp [sphericalTable]
    let alphaGlobal (v : FinPlace F) : ℂ :=
      if hv : v ∉ S.Sf then
        sphericalTable D A v (ordv v (toLoc v (Agen R c t.n)))
          (unitPart v (toLoc v (Agen R c t.n))) else 1
    let phaseGlobal (v : FinPlace F) : ℂ :=
      if hv : v ∉ S.Sf then
        localChi D v (toLoc v ρ) ^ (2 * ordv v (toLoc v (Agen R c t.n))) else 1
    let outsideGlobal (v : FinPlace F) : ℂ :=
      if hv : v ∉ S.Sf ∧ v ∉ R.exterior.support d ∧
          v ∉ R.exterior.support t.f then
        R.T.Wv v (R.C.a v (toLoc v (frozenFrequency R t d c))) else 1
    have hAlphaSupport : Function.mulSupport alphaGlobal ⊆ R.exterior.support I := by
      intro v hvα
      by_cases hv : v ∉ S.Sf
      · by_contra hvI
        have hone := hAtableOne v hv hvI
        apply hvα
        simp [alphaGlobal, hv, hone]
      · simp [alphaGlobal, hv] at hvα
    have hPhaseSupport : Function.mulSupport phaseGlobal ⊆ R.exterior.support I := by
      intro v hvφ
      by_cases hv : v ∉ S.Sf
      · by_contra hvI
        have hzero := hAordZero v hv hvI
        apply hvφ
        simp [phaseGlobal, hv, hzero]
      · simp [phaseGlobal, hv] at hvφ
    have hAlphaFinite : Function.HasFiniteMulSupport alphaGlobal := by
      change (Function.mulSupport alphaGlobal).Finite
      exact (R.exterior.support I).finite_toSet.subset hAlphaSupport
    have hPhaseFinite : Function.HasFiniteMulSupport phaseGlobal := by
      change (Function.mulSupport phaseGlobal).Finite
      exact (R.exterior.support I).finite_toSet.subset hPhaseSupport
    have hAlphaGlobalProd : (∏ᶠ v : FinPlace F, alphaGlobal v) =
        ∏ᶠ v : {v : FinPlace F // v ∉ S.Sf},
          sphericalTable D A v.1 (ordv v.1 (toLoc v.1 (Agen R c t.n)))
            (unitPart v.1 (toLoc v.1 (Agen R c t.n))) := by
      have hcond : (∏ᶠ v : FinPlace F, alphaGlobal v) =
          ∏ᶠ v : FinPlace F, ∏ᶠ (_ : v ∉ S.Sf),
            sphericalTable D A v (ordv v (toLoc v (Agen R c t.n)))
              (unitPart v (toLoc v (Agen R c t.n))) := by
        apply finprod_congr
        intro v
        by_cases hv : v ∉ S.Sf
        · simp [alphaGlobal, hv, finprod_eq_if]
        · simp [alphaGlobal, hv, finprod_eq_if]
      rw [hcond, ← finprod_subtype_eq_finprod_cond (p := fun v : FinPlace F => v ∉ S.Sf)]
    have hAlphaTableProd : (∏ᶠ v : FinPlace F, alphaGlobal v) =
        gamma D S A 2 c.1 (bc.gen (R.exterior.ofSqf c) : F) *
          (qI c.1 ^ (-(1 / 2 : ℝ)) / qI t.n.1 : ℝ) := by
      rw [hAlphaGlobalProd, htable]
      simp only [qI, Complex.ofReal_div, Complex.ofReal_inv]
      ring_nf
    have houtsidePoint (v : FinPlace F) :
        outsideGlobal v = alphaGlobal v * phaseGlobal v := by
      by_cases hv : v ∉ S.Sf
      · by_cases hvd : v ∈ R.exterior.support d
        · have hnotI := hnotI_d v hvd
          have hAone := hAtableOne v hv hnotI
          have hAord := hAordZero v hv hnotI
          rw [hAord] at hAone
          simp [outsideGlobal, alphaGlobal, phaseGlobal, hv, hvd, hAone, hAord]
        · by_cases hvf : v ∈ R.exterior.support t.f
          · have hnotI := hnotI_f v hvf
            have hAone := hAtableOne v hv hnotI
            have hAord := hAordZero v hv hnotI
            rw [hAord] at hAone
            simp [outsideGlobal, alphaGlobal, phaseGlobal, hv, hvd, hvf, hAone, hAord]
          · have hW := hWν v hv hvd hvf
            have hA := rf_Wv_sphericalTable R v hv (toLoc v (Agen R c t.n))
            calc
              outsideGlobal v =
                  R.T.Wv v (R.C.a v (toLoc v (frozenFrequency R t d c))) := by
                    simp [outsideGlobal, hv, hvd, hvf]
              _ = localChi D v (toLoc v ρ) ^
                    (2 * ordv v (toLoc v (Agen R c t.n))) *
                    sphericalTable D A v (ordv v (toLoc v (Agen R c t.n)))
                      (unitPart v (toLoc v (Agen R c t.n))) := by
                    rw [hW, hA]
              _ = alphaGlobal v * phaseGlobal v := by
                    simp [alphaGlobal, phaseGlobal, hv, mul_comm]
      · have hvS : v ∈ S.Sf := by
          by_contra hnot
          exact hv hnot
        simp [outsideGlobal, alphaGlobal, phaseGlobal, hvS]
    have hOutsideProd : (∏ᶠ v : FinPlace F, outsideGlobal v) =
        gamma D S A 2 c.1 (bc.gen (R.exterior.ofSqf c) : F) *
          (qI c.1 ^ (-(1 / 2 : ℝ)) / qI t.n.1 : ℝ) *
            ∏ v ∈ R.exterior.support I, phaseGlobal v := by
      calc
        (∏ᶠ v : FinPlace F, outsideGlobal v) =
            ∏ᶠ v : FinPlace F, alphaGlobal v * phaseGlobal v := by
              apply finprod_congr
              exact houtsidePoint
        _ = (∏ᶠ v : FinPlace F, alphaGlobal v) *
            ∏ᶠ v : FinPlace F, phaseGlobal v :=
              finprod_mul_distrib hAlphaFinite hPhaseFinite
        _ = gamma D S A 2 c.1 (bc.gen (R.exterior.ofSqf c) : F) *
            (qI c.1 ^ (-(1 / 2 : ℝ)) / qI t.n.1 : ℝ) *
              ∏ v ∈ R.exterior.support I, phaseGlobal v := by
              rw [hAlphaTableProd,
                finprod_eq_prod_of_mulSupport_subset phaseGlobal hPhaseSupport]
    have hsupportCsubI : R.exterior.support (R.exterior.ofSqf c) ⊆
        R.exterior.support I := by
      intro v hvC
      have hdivC : v.asIdeal ∣ c.1 := by
        simpa only [R.exterior.ofSqf_val] using
          (R.exterior.mem_support (R.exterior.ofSqf c) v).1 hvC
      have hdivI : v.asIdeal ∣ I.1 := by
        rw [hdecomp]
        exact dvd_mul_of_dvd_left hdivC _
      exact (R.exterior.mem_support I v).2 hdivI
    have hphaseC (v : FinPlace F) (hvI : v ∈ R.exterior.support I) :
        phaseGlobal v = if v ∈ R.exterior.support (R.exterior.ofSqf c) then
          localChi D v (toLoc v ρ) ^ (2 : ℤ) else 1 := by
      have hvS := R.exterior.support_exterior I v hvI
      have hvd : v ∉ R.exterior.support d := by
        intro hdv
        exact hnotI_d v hdv hvI
      have hvf : v ∉ R.exterior.support t.f := by
        intro hvf
        exact hnotI_f v hvf hvI
      have hρloc := hρLocUnit v hvS hvd hvf
      have hρsix := (a2_bridge_SYMBOL D S).localChi_six v hvS (toLoc v ρ) hρloc
      have hρsixInt : localChi D v (toLoc v ρ) ^ (6 : ℤ) = 1 := by simpa using hρsix
      have hρne : localChi D v (toLoc v ρ) ≠ 0 := by
        intro hz
        rw [hz] at hρsix
        norm_num at hρsix
      have hAord : ordv v (toLoc v (Agen R c t.n)) =
          (idealExp v c.1 : ℤ) + 3 * (idealExp v t.n.1 : ℤ) := by
        calc
          ordv v (toLoc v (Agen R c t.n)) = (idealExp v I.1 : ℤ) :=
            rf_ordv_toLoc_ofGen v hvS I (Agen R c t.n) hgenA
          _ = (idealExp v c.1 : ℤ) + 3 * (idealExp v t.n.1 : ℤ) := by
            exact_mod_cast hExpA v
      have hphaseExpr : phaseGlobal v =
          localChi D v (toLoc v ρ) ^ (2 * ordv v (toLoc v (Agen R c t.n))) := by
        simp [phaseGlobal, hvS]
      by_cases hvC : v ∈ R.exterior.support (R.exterior.ofSqf c)
      · have hcExp : idealExp v c.1 = 1 := by
          have hsq : Squarefree (R.exterior.ofSqf c).1 := by
            simpa only [R.exterior.ofSqf_val] using c.property.2
          have h := rf_idealExp_eq_one_of_squarefree_support R v
            (R.exterior.ofSqf c) hsq hvC
          simpa only [R.exterior.ofSqf_val] using h
        have hpow6 (k : ℤ) : localChi D v (toLoc v ρ) ^ (6 * k) = 1 := by
          rw [zpow_mul, hρsixInt, one_zpow]
        rw [hphaseExpr, hAord, hcExp, if_pos hvC]
        calc
          localChi D v (toLoc v ρ) ^ (2 * (1 + 3 * (idealExp v t.n.1 : ℤ))) =
              localChi D v (toLoc v ρ) ^ (2 + 6 * (idealExp v t.n.1 : ℤ)) := by
                congr 1
                ring
          _ = localChi D v (toLoc v ρ) ^ (2 : ℤ) *
                localChi D v (toLoc v ρ) ^ (6 * (idealExp v t.n.1 : ℤ)) :=
              zpow_add₀ hρne _ _
          _ = localChi D v (toLoc v ρ) ^ (2 : ℤ) := by rw [hpow6, mul_one]
      · have hcExp : idealExp v c.1 = 0 := by
          have h := rf_idealExp_zero_of_not_support R v (R.exterior.ofSqf c) hvC
          simpa only [R.exterior.ofSqf_val] using h
        have hpow6 (k : ℤ) : localChi D v (toLoc v ρ) ^ (6 * k) = 1 := by
          rw [zpow_mul, hρsixInt, one_zpow]
        rw [hphaseExpr, hAord, hcExp, if_neg hvC]
        have he : 2 * ((0 : ℕ) + 3 * idealExp v t.n.1 : ℤ) =
            6 * (idealExp v t.n.1 : ℤ) := by ring
        rw [he, hpow6]
    have hphaseProduct :
        ∏ v ∈ R.exterior.support I, phaseGlobal v =
          ∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
            localChi D v (toLoc v ρ) ^ (2 : ℤ) := by
      have hfilter : (R.exterior.support I).filter
          (fun v => v ∈ R.exterior.support (R.exterior.ofSqf c)) =
            R.exterior.support (R.exterior.ofSqf c) := by
        ext v
        simp only [Finset.mem_filter]
        constructor
        · exact And.right
        · intro hvC
          exact ⟨hsupportCsubI hvC, hvC⟩
      calc
        ∏ v ∈ R.exterior.support I, phaseGlobal v =
            ∏ v ∈ R.exterior.support I,
              if v ∈ R.exterior.support (R.exterior.ofSqf c) then
                localChi D v (toLoc v ρ) ^ (2 : ℤ) else 1 := by
                  apply Finset.prod_congr rfl
                  intro v hvI
                  exact hphaseC v hvI
        _ = ∏ v ∈ (R.exterior.support I).filter
              (fun v => v ∈ R.exterior.support (R.exterior.ofSqf c)),
              localChi D v (toLoc v ρ) ^ (2 : ℤ) := by rw [← Finset.prod_filter]
        _ = ∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
              localChi D v (toLoc v ρ) ^ (2 : ℤ) := by rw [hfilter]
    have hno_c_d (v : FinPlace F)
        (hvC : v ∈ R.exterior.support (R.exterior.ofSqf c)) :
        v ∉ R.exterior.support d := by
      intro hvd
      exact rf_no_common_prime v d.1 c.1 hdc
        ((R.exterior.mem_support d v).1 hvd)
        (by simpa only [R.exterior.ofSqf_val] using
          (R.exterior.mem_support (R.exterior.ofSqf c) v).1 hvC)
    have hno_c_f (v : FinPlace F)
        (hvC : v ∈ R.exterior.support (R.exterior.ofSqf c)) :
        v ∉ R.exterior.support t.f := by
      intro hvf
      exact rf_no_common_prime v c.1 t.f.1 hcf
        (by simpa only [R.exterior.ofSqf_val] using
          (R.exterior.mem_support (R.exterior.ofSqf c) v).1 hvC)
        ((R.exterior.mem_support t.f v).1 hvf)
    have hphaseGlobalChi :
        ∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
          localChi D v (toLoc v ρ) ^ (2 : ℤ) =
        ∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
          chi D v (ρ : F) ^ (2 : ℤ) := by
      apply Finset.prod_congr rfl
      intro v hvC
      have hvS := R.exterior.support_exterior (R.exterior.ofSqf c) v hvC
      have hval := rf_globalVal_one_of_ordv_zero v ρ
        (hρord_out v hvS (hno_c_d v hvC) (hno_c_f v hvC))
      rw [rf_localChi_toLoc v hvS ρ hval]
    have hlocalDfactor (v : FinPlace F) (hvd : v ∈ R.exterior.support d) :
        localR R v 1 0 (toLoc v (frozenFrequency R t d c) *
          toLoc v (primeGen R v) ^ (2 : ℕ)) =
          localOmega R v * chi D v (θd v : F) *
            chi D v (bc.gen (R.exterior.ofSqf c) : F) := by
      have hv := R.exterior.support_exterior d v hvd
      have hloc := hlocal_d v hv hvd
      rw [hτdChi v hv hvd, hχdSplit v hv hvd] at hloc
      simpa [τd, mul_assoc] using hloc
    have hlocalFfactor (v : FinPlace F) (hvf : v ∈ R.exterior.support t.f) :
        localR R v (frozenJ t v) (idealExp v t.a.1)
          (toLoc v (frozenFrequency R t d c) *
            toLoc v (primeGen R v) ^ (2 - (idealExp v t.a.1 : ℤ))) =
          localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
            chi D v (θf v : F) ^ frozenB t v *
              chi D v (bc.gen (R.exterior.ofSqf c) : F) ^ frozenB t v *
                chi D v (bc.gen d : F) ^ (-2 * frozenB t v) := by
      have hv := R.exterior.support_exterior t.f v hvf
      have hloc := hlocal_f v hv hvf
      rw [hτfChi v hv hvf, hθfChiSplit v hv hvf] at hloc
      simpa [τf, mul_assoc] using hloc
    have hdProduct :
        (∏ v ∈ R.exterior.support d,
          localR R v 1 0 (toLoc v (frozenFrequency R t d c) *
            toLoc v (primeGen R v) ^ 2)) =
          ∏ v ∈ R.exterior.support d,
            localOmega R v * chi D v (θd v : F) *
              chi D v (bc.gen (R.exterior.ofSqf c) : F) := by
      apply Finset.prod_congr rfl
      intro v hvd
      exact hlocalDfactor v hvd
    have hfProduct :
        (∏ v ∈ R.exterior.support t.f,
          localR R v (frozenJ t v) (idealExp v t.a.1)
            (toLoc v (frozenFrequency R t d c) *
              toLoc v (primeGen R v) ^ (2 - (idealExp v t.a.1 : ℤ)))) =
          ∏ v ∈ R.exterior.support t.f,
            localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
              chi D v (θf v : F) ^ frozenB t v *
              chi D v (bc.gen (R.exterior.ofSqf c) : F) ^ frozenB t v *
                chi D v (bc.gen d : F) ^ (-2 * frozenB t v) := by
      apply Finset.prod_congr rfl
      intro v hvf
      exact hlocalFfactor v hvf
    have hgroupBase :
        groupedExterior R t d (frozenFrequency R t d c) *
            (Lvalue R υ (S.diagU (frozenFrequency R t d c)))⁻¹ =
          inactiveScalar R h t.f *
            (∏ v ∈ R.exterior.support d,
              localOmega R v * chi D v (θd v : F) *
                chi D v (bc.gen (R.exterior.ofSqf c) : F)) *
            (∏ v ∈ R.exterior.support t.f,
              localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
                chi D v (θf v : F) ^ frozenB t v *
                chi D v (bc.gen (R.exterior.ofSqf c) : F) ^ frozenB t v *
                  chi D v (bc.gen d : F) ^ (-2 * frozenB t v)) *
            (gamma D S A 2 c.1 (bc.gen (R.exterior.ofSqf c) : F) *
              (qI c.1 ^ (-(1 / 2 : ℝ)) / qI t.n.1 : ℝ) *
              (∏ v ∈ R.exterior.support (R.exterior.ofSqf c), chi D v (ρ : F) ^ (2 : ℤ))) *
            (Lvalue R υ (S.diagU (frozenFrequency R t d c)))⁻¹ := by
      change inactiveScalar R h t.f *
          (∏ v ∈ R.exterior.support d,
            localR R v 1 0 (toLoc v (frozenFrequency R t d c) *
              toLoc v (primeGen R v) ^ (2 : ℕ))) *
          (∏ v ∈ R.exterior.support t.f,
            localR R v (frozenJ t v) (idealExp v t.a.1)
              (toLoc v (frozenFrequency R t d c) *
                toLoc v (primeGen R v) ^ (2 - (idealExp v t.a.1 : ℤ)))) *
          (∏ᶠ v : FinPlace F, outsideGlobal v) *
          (Lvalue R υ (S.diagU (frozenFrequency R t d c)))⁻¹ = _
      rw [hdProduct, hfProduct, hOutsideProd, hphaseProduct, hphaseGlobalChi]
    let Lh : Fˣ →* ℂˣ := (R.chars.L υ).L.comp S.diagU
    have hLeps : Lh (R.sheets.eps t.u : Fˣ) = 1 := by
      change (R.chars.L υ).L (S.diagU (R.sheets.eps t.u)) = 1
      exact (R.chars.L υ).trivial_US (R.sheets.eps t.u) (R.sheets.eps t.u).property
    have hLimageν : Lh (frozenFrequency R t d c) =
        Lh (R.sheets.eps t.u : Fˣ) * Lh (bc.gen t.a) *
          Lh (bc.gen (R.exterior.ofSqf c)) * Lh (bc.gen t.n) ^ (3 : ℕ) /
            (Lh (bc.gen d) * Lh (bc.gen t.f)) ^ (2 : ℕ) := by
      simp [Lh, frozenFrequency, map_mul, map_div, map_pow]
    have hLunitEq : (Lh (frozenFrequency R t d c))⁻¹ =
        (Lh (bc.gen t.a))⁻¹ * (Lh (bc.gen t.n)) ^ (-3 : ℤ) *
          (Lh (bc.gen t.f)) ^ (2 : ℤ) * (Lh (bc.gen d)) ^ (2 : ℤ) *
            (Lh (bc.gen (R.exterior.ofSqf c)))⁻¹ := by
      apply Units.ext
      have hνval : ((Lh (frozenFrequency R t d c) : ℂˣ) : ℂ) =
          ((Lh (R.sheets.eps t.u : Fˣ) : ℂˣ) : ℂ) *
            ((Lh (bc.gen t.a) : ℂˣ) : ℂ) *
            ((Lh (bc.gen (R.exterior.ofSqf c)) : ℂˣ) : ℂ) *
              ((Lh (bc.gen t.n) : ℂˣ) : ℂ) ^ (3 : ℕ) /
                (((Lh (bc.gen d) : ℂˣ) : ℂ) *
                  ((Lh (bc.gen t.f) : ℂˣ) : ℂ)) ^ (2 : ℕ) := by
        simpa only [Units.val_mul, Units.val_div_eq_div_val,
          Units.val_pow_eq_pow_val] using congrArg (fun z : ℂˣ => (z : ℂ)) hLimageν
      have hna : ((Lh (bc.gen t.a) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have hnc : ((Lh (bc.gen (R.exterior.ofSqf c)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have hnn : ((Lh (bc.gen t.n) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have hnd : ((Lh (bc.gen d) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have hnf : ((Lh (bc.gen t.f) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      simp only [Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
        Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
      rw [hνval, hLeps]
      rw [mul_pow, zpow_neg]
      field_simp [hna, hnc, hnn, hnd, hnf]
      ring
      norm_num
    have hLcomplexEq :
        (Lvalue R υ (S.diagU (frozenFrequency R t d c)))⁻¹ =
          (Lvalue R υ (S.diagU (bc.gen t.a)))⁻¹ *
            Lvalue R υ (S.diagU (bc.gen t.n)) ^ (-3 : ℤ) *
            Lvalue R υ (S.diagU (bc.gen t.f)) ^ (2 : ℤ) *
            Lvalue R υ (S.diagU (bc.gen d)) ^ (2 : ℤ) *
            (Lvalue R υ (S.diagU (bc.gen (R.exterior.ofSqf c))))⁻¹ := by
      have h := congrArg (fun z : ℂˣ => (z : ℂ)) hLunitEq
      simpa [Lvalue, Lh, Units.val_zpow_eq_zpow_val] using h
    let τc (v : FinPlace F) : Fˣ := bc.gen (R.exterior.ofSqf c) / primeGen R v
    let θc (v : FinPlace F) : Fˣ := τc v * ρ * bc.gen d ^ (2 : ℕ)
    have hθcDef (v : FinPlace F) : θc v =
        (R.sheets.eps t.u : Fˣ) * bc.gen t.a * τc v * bc.gen t.f ^ (-2 : ℤ) := by
      apply Units.ext
      simp only [θc, ρ, Units.val_mul, Units.val_div_eq_div_val,
        Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
      simp only [zpow_neg]
      norm_num
      field_simp <;> ring
    have hχcPhase (v : FinPlace F)
        (hvC : v ∈ R.exterior.support (R.exterior.ofSqf c)) :
        chi D v (τc v : F) ^ (2 : ℤ) * chi D v (ρ : F) ^ (2 : ℤ) =
          chi D v (θc v : F) ^ (2 : ℕ) * chi D v (bc.gen d : F) ^ (-4 : ℤ) := by
      have hvS := R.exterior.support_exterior (R.exterior.ofSqf c) v hvC
      have hDord := hgenDOrd0 v hvS (hno_c_d v hvC)
      have hρordC := hρord_out v hvS (hno_c_d v hvC) (hno_c_f v hvC)
      have hτord : ordv v (toLoc v (τc v)) = 0 := by
        have hsq : Squarefree (R.exterior.ofSqf c).1 := by
          simpa only [R.exterior.ofSqf_val] using c.property.2
        have hcExp := rf_idealExp_eq_one_of_squarefree_support R v
          (R.exterior.ofSqf c) hsq hvC
        simp only [τc, map_div]
        rw [hOrdDiv, rf_ordv_toLoc_ofGen v hvS (R.exterior.ofSqf c)
          (bc.gen (R.exterior.ofSqf c)) (bc.gen_spec _).1, hcExp, hprimeOrd v hvS]
        norm_num
      have hθord : ordv v (toLoc v (θc v)) = 0 := by
        simp only [θc, map_mul, map_pow]
        rw [rf_ordv_mul, rf_ordv_mul, hOrdPow2, hτord, hρordC, hDord]
        norm_num
      have hτval := rf_globalVal_one_of_ordv_zero v (τc v) hτord
      have hρvalC := rf_globalVal_one_of_ordv_zero v ρ hρordC
      have hθval := rf_globalVal_one_of_ordv_zero v (θc v) hθord
      have hDval := rf_globalVal_one_of_ordv_zero v (bc.gen d) hDord
      have hDnegVal : HeightOneSpectrum.valuation F v
          ((bc.gen d ^ (-2 : ℤ) : Fˣ) : F) = 1 := by
        simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hDval, one_zpow]
      have hargs : τc v * ρ = θc v * bc.gen d ^ (-2 : ℤ) := by
        simp [θc, zpow_neg, mul_assoc]
      have hmul1 := (a2_bridge_SYMBOL D S).chi_mul v hvS
        (τc v : F) (ρ : F) hτval.le hρvalC.le
      have hmul2 := (a2_bridge_SYMBOL D S).chi_mul v hvS
        (θc v : F) ((bc.gen d ^ (-2 : ℤ) : Fˣ) : F) hθval.le hDnegVal.le
      have hDchar := rf_chi_argument_zpow (D := D) (S := S) v hvS
        (bc.gen d) hDval (-2 : ℤ)
      have hchar : chi D v (τc v : F) * chi D v (ρ : F) =
          chi D v (θc v : F) * chi D v (bc.gen d : F) ^ (-2 : ℤ) := by
        calc
          _ = chi D v ((τc v * ρ : Fˣ) : F) := by
            simpa only [Units.val_mul] using hmul1.symm
          _ = chi D v ((θc v * bc.gen d ^ (-2 : ℤ) : Fˣ) : F) := by rw [hargs]
          _ = chi D v (θc v : F) *
              chi D v ((bc.gen d ^ (-2 : ℤ) : Fˣ) : F) := by
            simpa only [Units.val_mul] using hmul2
          _ = _ := by rw [hDchar]
      have hnegSquare : (chi D v (bc.gen d : F) ^ (-2 : ℤ)) ^ (2 : ℕ) =
          chi D v (bc.gen d : F) ^ (-4 : ℤ) := by
        rw [← zpow_natCast, ← zpow_mul]
        norm_num
      have hsq := congrArg (fun z : ℂ => z ^ (2 : ℕ)) hchar
      simp only [mul_pow, hnegSquare] at hsq
      simpa using hsq
    have hgammaC : gamma D S A 2 c.1 (cgen R c) =
        ∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
          gamma D S A 2 v.asIdeal (primeGen R v : F) * chi D v (τc v : F) ^ (2 : ℤ) := by
      simpa only [τc, cgen, Units.val_div_eq_div_val] using rf_gamma_sqf_factorization R c
    have hgammaPhase :
        gamma D S A 2 c.1 (cgen R c) *
          (∏ v ∈ R.exterior.support (R.exterior.ofSqf c), chi D v (ρ : F) ^ (2 : ℤ)) =
        (∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
          gamma D S A 2 v.asIdeal (primeGen R v : F) * chi D v (θc v : F) ^ (2 : ℕ)) *
          (∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
            chi D v (bc.gen d : F) ^ (-4 : ℤ)) := by
      rw [hgammaC, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hvC
      calc
        _ = gamma D S A 2 v.asIdeal (primeGen R v : F) *
            (chi D v (τc v : F) ^ (2 : ℤ) * chi D v (ρ : F) ^ (2 : ℤ)) := by ring
        _ = _ := by rw [hχcPhase v hvC]; ring
    have hgammaQ :
        gamma D S A 2 c.1 (bc.gen (R.exterior.ofSqf c) : F) *
          (qI c.1 ^ (-(1 / 2 : ℝ)) / qI t.n.1 : ℝ) *
          (∏ v ∈ R.exterior.support (R.exterior.ofSqf c), chi D v (ρ : F) ^ (2 : ℤ)) =
        (∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
          gamma D S A 2 v.asIdeal (primeGen R v : F) * chi D v (θc v : F) ^ (2 : ℕ)) *
          (∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
            chi D v (bc.gen d : F) ^ (-4 : ℤ)) *
          (qI c.1 ^ (-(1 / 2 : ℝ)) / qI t.n.1 : ℝ) := by
      calc
        _ = (gamma D S A 2 c.1 (cgen R c) *
            (∏ v ∈ R.exterior.support (R.exterior.ofSqf c), chi D v (ρ : F) ^ (2 : ℤ))) *
            (qI c.1 ^ (-(1 / 2 : ℝ)) / qI t.n.1 : ℝ) := by unfold cgen; ring
        _ = _ := by rw [hgammaPhase]
    have hOmegaEq : frozenOmega R υ t =
        inactiveScalar R h t.f * (Lvalue R υ (S.diagU (bc.gen t.a)))⁻¹ *
          Lvalue R υ (S.diagU (bc.gen t.n)) ^ (-3 : ℤ) *
          Lvalue R υ (S.diagU (bc.gen t.f)) ^ (2 : ℕ) *
          (∏ v ∈ R.exterior.support t.f,
            localR R v (frozenJ t v) (idealExp v t.a.1) 1 *
              chi D v (θf v : F) ^ frozenB t v) := by
      simp only [frozenOmega, θf, Units.val_mul, Units.val_div_eq_div_val,
        Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
    have hRhoEq : frozenRho R υ t sd d =
        Lvalue R υ (S.diagU (bc.gen d)) ^ (2 : ℕ) *
          (∏ v ∈ R.exterior.support d, localOmega R v * chi D v (θd v : F)) *
          (∏ v ∈ R.exterior.support t.f, chi D v (bc.gen d : F) ^ (-2 * frozenB t v)) := by
      rw [frozenRho, if_pos ⟨hd, hdh, hsd⟩]
      simp only [θd, Units.val_mul, Units.val_div_eq_div_val,
        Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
    have hLambdaEq : frozenLambda R υ t sc c =
        (Lvalue R υ (S.diagU (bc.gen (R.exterior.ofSqf c))))⁻¹ *
          (∏ v ∈ R.exterior.support t.f, chi D v (cgen R c) ^ frozenB t v) *
          (∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
            gamma D S A 2 v.asIdeal (primeGen R v : F) * chi D v (θc v : F) ^ (2 : ℕ)) := by
      rw [frozenLambda, if_pos ⟨hcf, hsc⟩]
      congr 1
      apply Finset.prod_congr rfl
      intro v hvC
      rw [hθcDef v]
      simp only [τc, cgen, Units.val_mul, Units.val_div_eq_div_val,
        Units.val_zpow_eq_zpow_val]
    have hLnatEq :
        (Lvalue R υ (S.diagU (frozenFrequency R t d c)))⁻¹ =
          (Lvalue R υ (S.diagU (bc.gen t.a)))⁻¹ *
            Lvalue R υ (S.diagU (bc.gen t.n)) ^ (-3 : ℤ) *
            Lvalue R υ (S.diagU (bc.gen t.f)) ^ (2 : ℕ) *
            Lvalue R υ (S.diagU (bc.gen d)) ^ (2 : ℕ) *
            (Lvalue R υ (S.diagU (bc.gen (R.exterior.ofSqf c))))⁻¹ := by
      simpa using hLcomplexEq
    have hPair := rf_sqf_pairing_product R d c hd hdc
    rw [hgroupBase, hLnatEq, hgammaQ, hOmegaEq, hRhoEq, hLambdaEq, ← hPair]
    simp only [Finset.prod_mul_distrib, cgen]
    ring
private theorem rf_S_orbit_multiplier
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (u : UnitSix S) (γ : Gamma S) (ν : Fˣ) (y : S.FSˣ) :
    bCut (Bd := Bd) y * (Lvalue R u y)⁻¹ *
      sCocycle (D := D) (H := H) (S.diagU ((γ.1 : Fˣ) * ν)) y⁻¹ =
    (Lvalue R u (S.diagU ν))⁻¹ *
      (if cls (S.diagU ν) * (cls (S.diagU ((γ.1 : Fˣ) * ν) / y))⁻¹ ∈ Bd.B then 1 else 0) *
      R.pairing.pair (cls (S.diagU ν)) (cls (S.diagU ((γ.1 : Fˣ) * ν) / y)) ^ 2 *
      Lvalue R u (S.diagU ((γ.1 : Fˣ) * ν) / y) := by
  classical
  let x : S.FSˣ := S.diagU ((γ.1 : Fˣ) * ν)
  obtain ⟨ε, hε⟩ := γ.property
  have hεpow : ε ^ (6 : ℕ) = γ.1 := hε
  have hγF : (γ.1 : Fˣ) = (ε : Fˣ) ^ (6 : ℕ) := by
    simpa only [SubgroupClass.coe_pow] using
      congrArg (fun z : S.US => (z : Fˣ)) hεpow.symm
  have hγclass : cls (S.diagU (γ.1 : Fˣ)) = 1 := by
    have hmem : S.diagU (γ.1 : Fˣ) ∈ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range := by
      refine ⟨S.diagU (ε : Fˣ), ?_⟩
      change (S.diagU (ε : Fˣ)) ^ (6 : ℕ) = S.diagU (γ.1 : Fˣ)
      rw [hγF, map_pow]
    exact (QuotientGroup.eq_one_iff (S.diagU (γ.1 : Fˣ))).2 hmem
  have hxclass : cls x = cls (S.diagU ν) := by
    calc
      cls x = cls (S.diagU (γ.1 : Fˣ)) * cls (S.diagU ν) := by
        simp only [x, map_mul, cls, QuotientGroup.mk_mul]
      _ = cls (S.diagU ν) := by
        rw [hγclass]
        exact one_mul (cls (S.diagU ν))
  have hyclass : cls y = cls (S.diagU ν) * (cls (x / y))⁻¹ := by
    calc
      cls y = cls (x / (x / y)) := by simp
      _ = cls x * (cls (x / y))⁻¹ := by
        simp only [cls, QuotientGroup.mk_div, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, div_eq_mul_inv]
      _ = _ := by rw [hxclass]
  have hLγ : (R.chars.L u).L (S.diagU (γ.1 : Fˣ)) = 1 :=
    (R.chars.L u).trivial_US (γ.1 : S.US) (γ.1 : S.US).property
  have hLx : (R.chars.L u).L x = (R.chars.L u).L (S.diagU ν) := by
    simp only [x, map_mul, hLγ, one_mul]
  have hLunits : ((R.chars.L u).L y)⁻¹ =
      ((R.chars.L u).L (S.diagU ν))⁻¹ * (R.chars.L u).L (x / y) := by
    rw [map_div, hLx]
    simp [div_eq_mul_inv, mul_assoc]
  have hLfact : (Lvalue R u y)⁻¹ =
      (Lvalue R u (S.diagU ν))⁻¹ * Lvalue R u (x / y) := by
    have h := congrArg (fun z : ℂˣ => (z : ℂ)) hLunits
    simpa only [Lvalue, Units.val_inv_eq_inv_val, Units.val_mul] using h
  have hHSmul (a b c : S.FSˣ) :
      S.HS H a (b * c) = S.HS H a b * S.HS H a c := by
    simp only [SData.HS, map_mul, H.mul_right, Finset.prod_mul_distrib]
  have hHSself : (S.HS H x x) ^ (2 : ℕ) = 1 := by
    simp only [pow_two, SData.HS]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro v hv
    exact H.skew v.1 (S.compU v x) (S.compU v x)
  have hσself : D.σ0 (((S.HS H x x : Fˣ) : F)) ^ (2 : ℕ) = 1 := by
    have h := congrArg (fun z : rootsOfUnity 6 F => D.σ0 (((z : Fˣ) : F))) hHSself
    simpa using h
  have hHSz : S.HS H x (x / y) = S.HS H x x * S.HS H x y⁻¹ := by
    simpa only [div_eq_mul_inv] using hHSmul x x y⁻¹
  have hσz : D.σ0 (((S.HS H x (x / y) : Fˣ) : F)) =
      D.σ0 (((S.HS H x x : Fˣ) : F)) * D.σ0 (((S.HS H x y⁻¹ : Fˣ) : F)) := by
    have h := congrArg (fun z : rootsOfUnity 6 F => D.σ0 (((z : Fˣ) : F))) hHSz
    simpa using h
  have hpair : R.pairing.pair (cls (S.diagU ν)) (cls (x / y)) =
      D.σ0 (((S.HS H x (x / y) : Fˣ) : F)) := by
    rw [← hxclass]
    exact R.pairing.pair_eq x (x / y)
  have hcocycle : sCocycle (D := D) (H := H) x y⁻¹ =
      R.pairing.pair (cls (S.diagU ν)) (cls (x / y)) ^ (2 : ℕ) := by
    rw [hpair, hσz, mul_pow, hσself, one_mul]
    rfl
  change bCut (Bd := Bd) y * (Lvalue R u y)⁻¹ * sCocycle (D := D) (H := H) x y⁻¹ =
    (Lvalue R u (S.diagU ν))⁻¹ *
      (if cls (S.diagU ν) * (cls (x / y))⁻¹ ∈ Bd.B then 1 else 0) *
      R.pairing.pair (cls (S.diagU ν)) (cls (x / y)) ^ 2 * Lvalue R u (x / y)
  rw [hLfact, hcocycle]
  unfold bCut
  rw [hyclass]
  ring

private theorem rf_S_profile_integral
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (u : UnitSix S) (κ : S.V) (l : ℝ) (hl : 0 < l) :
    let m : S.FSˣ → ℂ := fun y =>
      (if κ * (cls y)⁻¹ ∈ Bd.B then 1 else 0) *
        R.pairing.pair κ (cls y) ^ 2 * Lvalue R u y
    Integrable (onUnits (fun y => m y * rotated R u y)) (R.sheets.sheet l) ∧
      sheetIntegral R l (fun y => m y * rotated R u y) =
        ∑ ℓ : Fin (R.rotated u).J, profileH R u κ ℓ l := by
  classical
  let m : S.FSˣ → ℂ := fun y =>
    (if κ * (cls y)⁻¹ ∈ Bd.B then 1 else 0) *
      R.pairing.pair κ (cls y) ^ 2 * Lvalue R u y
  change Integrable (onUnits (fun y => m y * rotated R u y)) (R.sheets.sheet l) ∧
    sheetIntegral R l (fun y => m y * rotated R u y) =
      ∑ ℓ : Fin (R.rotated u).J, profileH R u κ ℓ l
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
  let tensor : Fin (R.rotated u).J → S.FSˣ → ℂ := fun ℓ y =>
    m y * (∏ v : S.Sf, (R.rotated u).ff ℓ v ((y : S.FS).1 v)) *
      ∏ w : InfinitePlace F, (R.rotated u).fc ℓ w ((y : S.FS).2 w)
  have hTensor (ℓ : Fin (R.rotated u).J) :
      Integrable (onUnits (tensor ℓ)) (R.sheets.sheet l) :=
    a2_bridge_ANALYSIS_tensor (G := R.sheets) R.T.δ R.T.δ_pos
      (R.rotated u).J (R.rotated u).ff (R.rotated u).fc
      (R.rotated u).finite_bound (R.rotated u).complex_bound m hm ℓ l hl
  have hSum : onUnits (fun y => m y * rotated R u y) =
      fun y => ∑ ℓ : Fin (R.rotated u).J, onUnits (tensor ℓ) y := by
    funext y
    by_cases hy : IsUnit y
    · simp only [onUnits, dif_pos hy, tensor]
      rw [show rotated R u hy.unit =
        Theta.sumProd S (R.rotated u).J (R.rotated u).ff (R.rotated u).fc
          (hy.unit : S.FS) from R.rotated_eq u hy.unit]
      simp only [Theta.sumProd, Finset.mul_sum, mul_assoc]
    · simp [onUnits, hy]
  constructor
  · rw [hSum]
    exact integrable_finsetSum Finset.univ (fun ℓ _ => hTensor ℓ)
  · unfold sheetIntegral
    rw [hSum, integral_finsetSum Finset.univ (fun ℓ _ => hTensor ℓ)]
    rfl

private theorem rf_S_profile_pullback
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (u : UnitSix S) (ν : Fˣ) (l : ℝ) (hl : 0 < l) :
    let κ : S.V := cls (S.diagU ν)
    let g : S.FSˣ → ℂ := fun y =>
      (if κ * (cls y)⁻¹ ∈ Bd.B then 1 else 0) *
        R.pairing.pair κ (cls y) ^ 2 * Lvalue R u y * rotated R u y
    Integrable (onUnits (fun y => g (S.diagU ν / y))) (R.sheets.sheet l) ∧
      sheetIntegral R l (fun y => g (S.diagU ν / y)) =
        ∑ ℓ : Fin (R.rotated u).J,
          profileH R u κ ℓ (S.absS (S.diagU ν : S.FS) / l) := by
  classical
  let κ : S.V := cls (S.diagU ν)
  let g : S.FSˣ → ℂ := fun y =>
    (if κ * (cls y)⁻¹ ∈ Bd.B then 1 else 0) *
      R.pairing.pair κ (cls y) ^ 2 * Lvalue R u y * rotated R u y
  change Integrable (onUnits (fun y => g (S.diagU ν / y))) (R.sheets.sheet l) ∧
    sheetIntegral R l (fun y => g (S.diagU ν / y)) =
      ∑ ℓ : Fin (R.rotated u).J,
        profileH R u κ ℓ (S.absS (S.diagU ν : S.FS) / l)
  have hnorm : 0 < S.absS (S.diagU ν : S.FS) :=
    (a2_bridge_NORM D S).2.2.1 (S.diagU ν)
  have hprofile := rf_S_profile_integral R u κ
    (S.absS (S.diagU ν : S.FS) / l) (div_pos hnorm hl)
  change Integrable (onUnits g)
      (R.sheets.sheet (S.absS (S.diagU ν : S.FS) / l)) ∧
    sheetIntegral R (S.absS (S.diagU ν : S.FS) / l) g =
      ∑ ℓ : Fin (R.rotated u).J,
        profileH R u κ ℓ (S.absS (S.diagU ν : S.FS) / l) at hprofile
  have htranslate := a2_bridge_SHEET_transport (G := R.sheets)
    l⁻¹ (inv_pos.mpr hl) (S.diagU ν) g
      (by simpa only [div_eq_mul_inv] using hprofile.1)
  have hinvert := a2_bridge_SHEET_inversion (G := R.sheets) l hl
    (fun y => g (S.diagU ν * y)) htranslate.1
  constructor
  · simpa only [div_eq_mul_inv] using hinvert.1
  · calc
      sheetIntegral R l (fun y => g (S.diagU ν / y)) =
          bridgeSheetIntegral R.sheets l⁻¹ (fun y => g (S.diagU ν * y)) := by
        simpa only [sheetIntegral, bridgeSheetIntegral, div_eq_mul_inv] using hinvert.2
      _ = sheetIntegral R (S.absS (S.diagU ν : S.FS) / l) g := by
        simpa only [sheetIntegral, bridgeSheetIntegral, div_eq_mul_inv] using htranslate.2
      _ = ∑ ℓ : Fin (R.rotated u).J,
          profileH R u κ ℓ (S.absS (S.diagU ν : S.FS) / l) := hprofile.2

/-- rf:S-unfolding, 04:804–857. Inversion changes l to 1/l without a norm Jacobian. -/
theorem rf_S_unfolding : ∀ u ν l, 0 < l →
  let term := fun γ : Gamma S => omegaInt R l (fun y => bCut (Bd := Bd) y * (Lvalue R u y)⁻¹ *
    sCocycle (D := D) (H := H) (S.diagU ((γ.1 : Fˣ) * ν)) y⁻¹ * rotated R u (S.diagU ((γ.1 : Fˣ) * ν) / y))
  Summable term ∧ (∑' γ, term γ) = (Lvalue R u (S.diagU ν))⁻¹ *
    ∑ ℓ : Fin (R.rotated u).J, profileH R u (cls (S.diagU ν)) ℓ (S.absS (S.diagU ν : S.FS) / l) := by
  classical
  intro u ν l hl
  let term : Gamma S → ℂ := fun γ => omegaInt R l (fun y => bCut (Bd := Bd) y *
    (Lvalue R u y)⁻¹ * sCocycle (D := D) (H := H)
      (S.diagU ((γ.1 : Fˣ) * ν)) y⁻¹ * rotated R u (S.diagU ((γ.1 : Fˣ) * ν) / y))
  change Summable term ∧ (∑' γ, term γ) = (Lvalue R u (S.diagU ν))⁻¹ *
    ∑ ℓ : Fin (R.rotated u).J, profileH R u (cls (S.diagU ν)) ℓ
      (S.absS (S.diagU ν : S.FS) / l)
  let κ : S.V := cls (S.diagU ν)
  let g : S.FSˣ → ℂ := fun y =>
    (if κ * (cls y)⁻¹ ∈ Bd.B then 1 else 0) *
      R.pairing.pair κ (cls y) ^ 2 * Lvalue R u y * rotated R u y
  let pull : S.FSˣ → ℂ := fun y => g (S.diagU ν / y)
  let orbit : Gamma S → ℂ := fun γ =>
    bridgeOmegaInt R.sheets l (fun y => pull (S.diagU (γ.1 : Fˣ) * y))
  let z : ℂ := (Lvalue R u (S.diagU ν))⁻¹
  have hprofile := rf_S_profile_pullback R u ν l hl
  change Integrable (onUnits pull) (R.sheets.sheet l) ∧
    sheetIntegral R l pull = ∑ ℓ : Fin (R.rotated u).J,
      profileH R u κ ℓ (S.absS (S.diagU ν : S.FS) / l) at hprofile
  have hunfold := a2_bridge_SHEET_unfold (G := R.sheets) l hl pull hprofile.1
  have horbit : Summable orbit := hunfold.2.1
  have horbitSum : (∑' γ, orbit γ) = sheetIntegral R l pull := hunfold.2.2
  have harg (γ : Gamma S) (y : S.FSˣ) :
      S.diagU ν / (S.diagU ((γ⁻¹).1 : Fˣ) * y) =
        S.diagU ((γ.1 : Fˣ) * ν) / y := by
    have hco : ((γ⁻¹).1 : Fˣ) = (γ.1 : Fˣ)⁻¹ := rfl
    rw [hco, map_inv, map_mul]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ac_rfl
  have hpoint (γ : Gamma S) (y : S.FSˣ) :
      bCut (Bd := Bd) y * (Lvalue R u y)⁻¹ *
        sCocycle (D := D) (H := H) (S.diagU ((γ.1 : Fˣ) * ν)) y⁻¹ *
          rotated R u (S.diagU ((γ.1 : Fˣ) * ν) / y) =
      z * pull (S.diagU ((γ⁻¹).1 : Fˣ) * y) := by
    dsimp only [pull]
    rw [harg, rf_S_orbit_multiplier R u γ ν y]
    dsimp only [z, g, κ]
    ring
  have hterm (γ : Gamma S) : term γ = z * orbit γ⁻¹ := by
    dsimp only [term, orbit, omegaInt, bridgeOmegaInt, omegaAt, bridgeOmegaAt]
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    by_cases hy : IsUnit y
    · simp only [onUnits, dif_pos hy]
      exact hpoint γ hy.unit
    · simp [onUnits, hy]
  have hinv : Summable (fun γ : Gamma S => orbit γ⁻¹) := by
    simpa only [Function.comp_def, Equiv.inv_apply] using
      ((Equiv.inv (Gamma S)).summable_iff).2 horbit
  constructor
  · exact (hinv.mul_left z).congr (fun γ => (hterm γ).symm)
  · calc
      (∑' γ, term γ) = ∑' γ : Gamma S, z * orbit γ⁻¹ := tsum_congr hterm
      _ = z * ∑' γ : Gamma S, orbit γ⁻¹ := hinv.tsum_mul_left z
      _ = z * ∑' γ : Gamma S, orbit γ :=
        congrArg (fun w : ℂ => z * w) ((Equiv.inv (Gamma S)).tsum_eq orbit)
      _ = z * sheetIntegral R l pull := congrArg (fun w : ℂ => z * w) horbitSum
      _ = (Lvalue R u (S.diagU ν))⁻¹ *
          ∑ ℓ : Fin (R.rotated u).J, profileH R u (cls (S.diagU ν)) ℓ
            (S.absS (S.diagU ν : S.FS) / l) :=
        congrArg (fun w : ℂ => z * w) hprofile.2
/-- Nonnegative reflected Dirichlet mass in 04:859–910. -/
def reflectedDirichletTerm (f : S.ExtIdeal) (σ : ℝ)
    (p : {a : S.ExtIdeal // activeNumerator R f a} × S.SqfExtIdeal × S.ExtIdeal) : ℝ :=
  betaIdeal R f p.1 * qI p.2.1.1 ^ (-(1 / 2 : ℝ)) / qI p.2.2.1 *
    (qI p.1.1.1 * qI p.2.1.1 * qI p.2.2.1 ^ 3) ^ (-σ)

private theorem rf_active_exponent_injective
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (f : S.ExtIdeal) :
    Function.Injective (fun a : {a : S.ExtIdeal // activeNumerator R f a} =>
      fun v : {v : FinPlace F // v ∈ R.exterior.support f} => idealExp v.1 a.1.1) := by
  classical
  intro a b hab
  have hexp (v : FinPlace F) : idealExp v a.1.1 = idealExp v b.1.1 := by
    by_cases hv : v ∈ R.exterior.support f
    · exact congrFun hab ⟨v, hv⟩
    · have hva : v ∉ R.exterior.support a.1 := by
        intro h
        exact hv (a.property.1 v h)
      have hvb : v ∉ R.exterior.support b.1 := by
        intro h
        exact hv (b.property.1 v h)
      rw [rf_idealExp_zero_of_not_support R v a.1 hva,
        rf_idealExp_zero_of_not_support R v b.1 hvb]
  have ha0 : a.1.1 ≠ 0 := by
    simpa only [Ideal.zero_eq_bot] using a.1.property.1
  have hb0 : b.1.1 ≠ 0 := by
    simpa only [Ideal.zero_eq_bot] using b.1.property.1
  apply Subtype.ext
  apply Subtype.ext
  calc
    a.1.1 = ∏ᶠ v : FinPlace F, v.maxPowDividing a.1.1 :=
      (Ideal.finprod_heightOneSpectrum_factorization ha0).symm
    _ = ∏ᶠ v : FinPlace F, v.maxPowDividing b.1.1 := by
      apply finprod_congr
      intro v
      change v.asIdeal ^ idealExp v a.1.1 = v.asIdeal ^ idealExp v b.1.1
      rw [hexp v]
    _ = b.1.1 := Ideal.finprod_heightOneSpectrum_factorization hb0

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
