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

private theorem rf_local_primeGen_valuation (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (v : FinPlace F) (hv : v ∉ S.Sf) :
    v.valuation F (primeGen R v : F) = WithZero.exp (-1 : ℤ) := by
  have hp : S.IsGen (primeGen R v : F) v.asIdeal := by
    simpa [primeGen, hv, R.exterior.prime_val] using
      (bc.gen_spec (R.exterior.prime v hv)).1
  have hcountSelf : (UniqueFactorizationMonoid.normalizedFactors v.asIdeal).count v.asIdeal =
      idealExp v v.asIdeal := by
    unfold idealExp
    exact (Ideal.count_associates_factors_eq v.ne_bot v.isPrime v.ne_bot).symm
  have hexp : idealExp v v.asIdeal = 1 := by
    calc
      idealExp v v.asIdeal =
          (UniqueFactorizationMonoid.normalizedFactors v.asIdeal).count v.asIdeal :=
        hcountSelf.symm
      _ = 1 := by
        rw [UniqueFactorizationMonoid.normalizedFactors_irreducible v.irreducible]
        simp
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (primeGen R v : F)) =
        (idealExp v v.asIdeal : ℤ) := by
    rw [hp.2.2 v hv, FractionalIdeal.count_coe F v hp.1.1]
    rfl
  have hlog := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    v (primeGen R v : F) (by
      intro h
      exact (primeGen R v).ne_zero h)
  rw [hcount, hexp] at hlog
  have hLog : WithZero.log (v.valuation F (primeGen R v : F)) = -1 := by
    have hlog' := congrArg (fun z : ℤ => -z) hlog.symm
    simpa using hlog'
  have hval0 : v.valuation F (primeGen R v : F) ≠ 0 :=
    (Valuation.ne_zero_iff (v.valuation F)).mpr (primeGen R v).ne_zero
  calc
    v.valuation F (primeGen R v : F) =
        WithZero.exp (WithZero.log (v.valuation F (primeGen R v : F))) :=
      (WithZero.exp_log hval0).symm
    _ = WithZero.exp (-1 : ℤ) := by rw [hLog]

private theorem rf_local_primeGen_ord (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (v : FinPlace F) (hv : v ∉ S.Sf) :
    ordv v (toLoc v (primeGen R v)) = 1 := by
  have hval : Valued.v (toLoc v (primeGen R v) : v.adicCompletion F) =
      WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (primeGen R v : F)) = _
    calc
      _ = v.valuation F (primeGen R v : F) :=
        v.valuedAdicCompletion_eq_valuation' (primeGen R v : F)
      _ = WithZero.exp (-1 : ℤ) := rf_local_primeGen_valuation R v hv
  have hne : Valued.v (toLoc v (primeGen R v) : v.adicCompletion F) ≠ 0 := by
    rw [hval]
    exact WithZero.exp_ne_zero
  unfold ordv
  rw [WithZero.toAdd_unzero_eq_log hne, hval]
  simp

private theorem rf_local_primeGen_ratio_isLocUnit
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf) :
    Valued.v ((toLoc v (primeGen R v) /
      toLoc v (Units.mk0 (unif v) (unif_ne_zero v)) : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) = 1 ∧
    ArtinPrimitiveRoots.A1.Theta.IsLocUnit v
      (toLoc v (primeGen R v) /
        toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) := by
  let pLoc := toLoc v (primeGen R v)
  let π := toLoc v (Units.mk0 (unif v) (unif_ne_zero v))
  have hpVal : Valued.v (pLoc : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (primeGen R v : F)) = _
    calc
      _ = v.valuation F (primeGen R v : F) :=
        v.valuedAdicCompletion_eq_valuation' (primeGen R v : F)
      _ = WithZero.exp (-1 : ℤ) := rf_local_primeGen_valuation R v hv
  have hπVal : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (unif v)) = _
    calc
      _ = v.valuation F (unif v) := v.valuedAdicCompletion_eq_valuation' (unif v)
      _ = WithZero.exp (-1 : ℤ) :=
        (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hratioVal : Valued.v ((pLoc / π : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    calc
      _ = Valued.v (pLoc : v.adicCompletion F) / Valued.v (π : v.adicCompletion F) := by simp
      _ = 1 := by rw [hpVal, hπVal]; simp
  refine ⟨hratioVal, ?_⟩
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hratioVal]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have hinv : Valued.v (((pLoc / π)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      simp [Units.val_inv_eq_inv_val, hpVal, hπVal]
    rw [hinv]

private theorem rf_localW_table
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf)
    (e : ℤ) : localW R v e = sphericalTable D A v e
      ((toLoc v (primeGen R v) /
        toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e) := by
  let pLoc := toLoc v (primeGen R v)
  let π := toLoc v (Units.mk0 (unif v) (unif_ne_zero v))
  let b := pLoc / π
  have hbprops := rf_local_primeGen_ratio_isLocUnit R v hv
  have hbVal : Valued.v (b : v.adicCompletion F) = 1 := by
    simpa [b, pLoc, π] using hbprops.1
  have hbpVal : Valued.v ((b ^ e : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    simp [Units.val_zpow_eq_zpow_val, hbVal]
  have hbPowLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (b ^ e) := by
    constructor
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hbpVal]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have hinv : Valued.v (((b ^ e)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
        have hvalInv : Valued.v (((b ^ e)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
            (Valued.v ((b ^ e : (v.adicCompletion F)ˣ) : v.adicCompletion F))⁻¹ := by simp
        rw [hvalInv, hbpVal]
        simp
      rw [hinv]
  have hpow : pLoc ^ e = π ^ e * b ^ e := by
    dsimp [b]
    rw [div_zpow]
    calc
      pLoc ^ e = (pLoc ^ e * π ^ e) / π ^ e := by simp
      _ = (π ^ e * pLoc ^ e) / π ^ e := by rw [mul_comm]
      _ = π ^ e * (pLoc ^ e / π ^ e) := mul_div_assoc _ _ _
  have htable : localW R v e = sphericalTable D A v e (b ^ e) := by
    dsimp [localW, pLoc]
    rw [hpow]
    simpa [π] using R.T.Wv_table v hv e (b ^ e) hbPowLoc.1 hbPowLoc.2
  simpa [b, pLoc, π] using htable

private theorem rf_localW_zero_of_negative
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf)
    (e : ℤ) (he : e < 0) : localW R v e = 0 := by
  rw [rf_localW_table R v hv e]
  simp [sphericalTable, he]

private def rf_localUnitSubgroup (v : FinPlace F) :
    Subgroup ((v.adicCompletion F)ˣ) where
  carrier := ArtinPrimitiveRoots.A1.Theta.IsLocUnit v
  one_mem' := by
    constructor <;> simp [HeightOneSpectrum.mem_adicCompletionIntegers]
  mul_mem' := by
    intro a b ha hb
    constructor
    · exact mul_mem ha.1 hb.1
    · simpa [Units.val_inv_eq_inv_val] using (mul_mem hb.2 ha.2)
  inv_mem' := by
    intro a ha
    exact ⟨ha.2, ha.1⟩

private def rf_localChiUnitHom (D : FieldData F) (v : FinPlace F)
    (hv6 : (6 : 𝓞 F) ∉ v.asIdeal) : rf_localUnitSubgroup v →* ℂˣ where
  toFun u := Units.mk0 (localChi D v u.1) (by
    have h6 := (ArtinPrimitiveRoots.A1.Theta.localChi_basic (D := D) (v := v) hv6).2.2.2.1
      u.1 u.2
    intro hzero
    rw [hzero] at h6
    norm_num at h6)
  map_one' := by
    apply Units.ext
    exact (ArtinPrimitiveRoots.A1.Theta.localChi_basic (D := D) (v := v) hv6).1
  map_mul' := by
    intro u u'
    apply Units.ext
    exact (ArtinPrimitiveRoots.A1.Theta.localChi_basic (D := D) (v := v) hv6).2.2.1
      u.1 u'.1 u.2 u'.2

private theorem rf_localChi_zpow (D : FieldData F) (v : FinPlace F)
    (hv6 : (6 : 𝓞 F) ∉ v.asIdeal) (u : (v.adicCompletion F)ˣ)
    (hu : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v u) (e : ℤ) :
    localChi D v (u ^ e) = localChi D v u ^ e := by
  let u' : rf_localUnitSubgroup v := ⟨u, hu⟩
  have h := congrArg (fun z : ℂˣ => (z : ℂ))
    ((rf_localChiUnitHom D v hv6).map_zpow u' e)
  dsimp [rf_localChiUnitHom] at h
  simpa [u', rf_localUnitSubgroup, Units.val_zpow_eq_zpow_val] using h

private theorem rf_ordv_mul (v : FinPlace F) (x y : (v.adicCompletion F)ˣ) :
    ordv v (x * y) = ordv v x + ordv v y := by
  have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hy0 : Valued.v (y : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr y.ne_zero
  have hxy0 : Valued.v ((x * y : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (mul_ne_zero x.ne_zero y.ne_zero)
  have hxy : Valued.v ((x * y : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      Valued.v (x : v.adicCompletion F) * Valued.v (y : v.adicCompletion F) := by simp
  unfold ordv
  rw [WithZero.toAdd_unzero_eq_log hxy0,
    WithZero.toAdd_unzero_eq_log hx0, WithZero.toAdd_unzero_eq_log hy0]
  rw [hxy, WithZero.log_mul hx0 hy0]
  ring

private theorem rf_ordv_zpow (v : FinPlace F) (x : (v.adicCompletion F)ˣ) (e : ℤ) :
    ordv v (x ^ e) = e * ordv v x := by
  have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr x.ne_zero
  have he0 : Valued.v ((x ^ e : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero (x ^ e))
  have hpow : Valued.v ((x ^ e : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (Valued.v (x : v.adicCompletion F)) ^ e := by simp
  unfold ordv
  rw [WithZero.toAdd_unzero_eq_log he0, WithZero.toAdd_unzero_eq_log hx0]
  rw [hpow, WithZero.log_zpow]
  simp [zsmul_eq_mul]

private theorem rf_ordv_zero_of_localUnit (v : FinPlace F) (x : (v.adicCompletion F)ˣ)
    (hx : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v x) : ordv v x = 0 := by
  have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hxle : Valued.v (x : v.adicCompletion F) ≤ 1 := by
    rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hx.1
  have hInvLe : (Valued.v (x : v.adicCompletion F))⁻¹ ≤ 1 := by
    have hle : Valued.v (((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) ≤ 1 := by
      rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hx.2
    have hvalInv : Valued.v (((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) =
        (Valued.v (x : v.adicCompletion F))⁻¹ := by simp
    rw [← hvalInv]
    exact hle
  have hxpos : 0 < Valued.v (x : v.adicCompletion F) :=
    pos_iff_ne_zero.mpr hx0
  have hxge : 1 ≤ Valued.v (x : v.adicCompletion F) :=
    (inv_le_one₀ hxpos).mp hInvLe
  have hval : Valued.v (x : v.adicCompletion F) = 1 := le_antisymm hxle hxge
  unfold ordv
  rw [WithZero.toAdd_unzero_eq_log hx0, hval]
  simp

private theorem rf_valued_eq_exp_neg_ordv (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
    Valued.v (x : v.adicCompletion F) = WithZero.exp (-ordv v x) := by
  have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr x.ne_zero
  rw [← WithZero.exp_log hx0]
  simp [ordv, WithZero.toAdd_unzero_eq_log hx0]

private theorem rf_local_addchar_trivial_of_ord_nonneg (v : FinPlace F)
    (x : (v.adicCompletion F)ˣ) (hx : 0 ≤ ordv v x) : A.ψ v (x : v.adicCompletion F) = 1 := by
  have hval : Valued.v (x : v.adicCompletion F) = WithZero.exp (-ordv v x) :=
    rf_valued_eq_exp_neg_ordv v x
  have hle : Valued.v (x : v.adicCompletion F) ≤ 1 := by
    rw [hval]
    exact WithZero.exp_le_one_iff.mpr (by omega)
  have hmem : (x : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hle
  exact A.integral v (x : v.adicCompletion F) hmem

private theorem rf_valued_lt_one_le_exp_neg_one (v : FinPlace F)
    (z : v.adicCompletion F) (hz : Valued.v z < 1) :
    Valued.v z ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hz0 : Valued.v z = 0
  · simp [hz0]
  · lift Valued.v z to ℤ using hz0 with n hn
    have hnlt : n < 0 := by
      have hz' : WithZero.exp n < WithZero.exp 0 := by simpa [hn] using hz
      exact (WithZero.exp_lt_exp).mp hz'
    have hnle : n ≤ -1 := by omega
    have hle' : WithZero.exp n ≤ WithZero.exp (-1 : ℤ) :=
      (WithZero.exp_le_exp).2 hnle
    simpa [hn] using hle'

private theorem rf_localChi_has_approximant (D : FieldData F) (v : FinPlace F)
    (hv6 : (6 : 𝓞 F) ∉ v.asIdeal) (u : (v.adicCompletion F)ˣ)
    (hu : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v u) :
    ∃ a : 𝓞 F, a ∉ v.asIdeal ∧
      Valued.v ((u : v.adicCompletion F) - algebraMap F _ (algebraMap (𝓞 F) F a)) < 1 := by
  have hchi6 :=
    ArtinPrimitiveRoots.A1.Theta.localChi_basic (D := D) (v := v) hv6 |>.2.2.2.1 u hu
  have hchiNe : localChi D v u ≠ 0 := by
    intro hzero
    rw [hzero] at hchi6
    norm_num at hchi6
  by_contra hno
  have hzero : localChi D v u = 0 := by
    rw [ArtinPrimitiveRoots.A1.localChi, dif_neg hno]
  exact hchiNe hzero

private theorem rf_local_phase_approximant
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf)
    (u : (v.adicCompletion F)ˣ) (a : 𝓞 F) (ha : a ∉ v.asIdeal)
    (hclose : Valued.v ((u : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F a)) < 1) :
    A.ψ v ((toLoc v (primeGen R v))⁻¹ * (u : v.adicCompletion F)) =
      A.ψ v (algebraMap F (v.adicCompletion F)
        ((algebraMap (𝓞 F) F a) / (primeGen R v : F))) := by
  let pLoc := toLoc v (primeGen R v)
  let aF : F := algebraMap (𝓞 F) F a
  have hpVal : Valued.v (pLoc : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (primeGen R v : F)) = _
    calc
      Valued.v (algebraMap F (v.adicCompletion F) (primeGen R v : F)) =
          v.valuation F (primeGen R v : F) :=
            v.valuedAdicCompletion_eq_valuation' (primeGen R v : F)
      _ = WithZero.exp (-1 : ℤ) := rf_local_primeGen_valuation R v hv
  have hnumle : Valued.v ((u : v.adicCompletion F) - algebraMap F _ aF) ≤
      WithZero.exp (-1 : ℤ) := rf_valued_lt_one_le_exp_neg_one v _ hclose
  have hdivval : Valued.v (((u : v.adicCompletion F) - algebraMap F _ aF) / pLoc) ≤ 1 := by
    rw [map_div₀, hpVal]
    have hpPos : 0 < WithZero.exp (-1 : ℤ) :=
      lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
    exact (div_le_one₀ hpPos).2 hnumle
  have herrorInt :
      (((u : v.adicCompletion F) - algebraMap F _ aF) / pLoc) ∈
        v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hdivval
  have herror : A.ψ v (((u : v.adicCompletion F) - algebraMap F _ aF) / pLoc) = 1 :=
    A.integral v _ herrorInt
  have hsum :
      (u : v.adicCompletion F) / pLoc =
        (algebraMap F (v.adicCompletion F) aF) / pLoc +
          ((u : v.adicCompletion F) - algebraMap F _ aF) / pLoc := by
    field_simp [pLoc, Units.ne_zero (primeGen R v)]
    ring
  have hfirst :
      (algebraMap F (v.adicCompletion F) aF) / pLoc =
        algebraMap F (v.adicCompletion F) (aF / (primeGen R v : F)) := by
    change (algebraMap F (v.adicCompletion F) aF) /
        algebraMap F (v.adicCompletion F) (primeGen R v : F) = _
    rw [← map_div₀]
  calc
    A.ψ v ((toLoc v (primeGen R v))⁻¹ * (u : v.adicCompletion F)) =
        A.ψ v ((u : v.adicCompletion F) / pLoc) := by
          congr 1
          simp [pLoc, div_eq_mul_inv, mul_comm]
    _ = A.ψ v ((algebraMap F (v.adicCompletion F) aF) / pLoc +
          ((u : v.adicCompletion F) - algebraMap F _ aF) / pLoc) := by rw [hsum]
    _ = A.ψ v ((algebraMap F (v.adicCompletion F) aF) / pLoc) *
          A.ψ v (((u : v.adicCompletion F) - algebraMap F _ aF) / pLoc) :=
            (A.ψ v).map_add_eq_mul _ _
    _ = A.ψ v (algebraMap F (v.adicCompletion F) (aF / (primeGen R v : F))) := by
          rw [hfirst, herror, mul_one]
    _ = _ := by rfl

private theorem rf_local_unitPart_primePower
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf)
    (e : ℤ) (t : (v.adicCompletion F)ˣ)
    (ht : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v t) :
    unitPart v (toLoc v (primeGen R v) ^ e * t) =
      (toLoc v (primeGen R v) /
        toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e * t := by
  let pLoc := toLoc v (primeGen R v)
  let π := toLoc v (Units.mk0 (unif v) (unif_ne_zero v))
  let b := pLoc / π
  have hbProps := rf_local_primeGen_ratio_isLocUnit R v hv
  have hbLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v b := by
    simpa [b, pLoc, π] using hbProps.2
  have hpOrd : ordv v pLoc = 1 := by
    simpa [pLoc] using rf_local_primeGen_ord R v hv
  have hbOrd : ordv v b = 0 := rf_ordv_zero_of_localUnit v b hbLoc
  have htOrd : ordv v t = 0 := rf_ordv_zero_of_localUnit v t ht
  have hOrder : ordv v (pLoc ^ e * t) = e := by
    rw [rf_ordv_mul, rf_ordv_zpow, hpOrd, htOrd]
    ring
  have hpLoc : pLoc = π * b := by
    dsimp [b]
    calc
      pLoc = (pLoc / π) * π := (div_mul_cancel _ _).symm
      _ = π * (pLoc / π) := by rw [mul_comm]
  calc
    unitPart v (pLoc ^ e * t) = pLoc ^ e * t * π ^ (-e) := by
      dsimp [unitPart, π]
      rw [hOrder]
    _ = (π ^ e * b ^ e) * t * π ^ (-e) := by rw [hpLoc, mul_zpow]
    _ = b ^ e * t := by simp [zpow_neg, mul_assoc, mul_left_comm, mul_comm]

private theorem rf_localChi_algInt_unit (D : FieldData F) (S : SData F CE condη)
    (v : FinPlace F) (hv : v ∉ S.Sf) (a : 𝓞 F) (ha : a ∉ v.asIdeal) :
    localChi D v (toLoc v (Units.mk0 (algebraMap (𝓞 F) F a)
      (by
        intro hzero
        exact ha (by
          have hmem : a ∈ v.asIdeal := by
            apply (Ideal.Quotient.eq_zero_iff_mem).1
            calc
              Ideal.Quotient.mk v.asIdeal a = residue v (algebraMap (𝓞 F) F a) :=
                ((ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S).residue_algebraMap v a).symm
              _ = residue v 0 := by rw [hzero]
              _ = 0 := by
                have h0 := (ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S).residue_algebraMap
                  v (0 : 𝓞 F)
                simpa using h0
          exact hmem)))) = chi D v (algebraMap (𝓞 F) F a) := by
  let x : F := algebraMap (𝓞 F) F a
  have hxres : residue v x ≠ 0 := by
    have h := (ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S).residue_algebraMap v a
    rw [h]
    exact fun hz => ha ((Ideal.Quotient.eq_zero_iff_mem).1 hz)
  have hxval : v.valuation F x = 1 := by
    apply ((ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S).residue_ne_zero v x
      (by simpa [x] using v.valuation_le_one a)).1
    exact hxres
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hxres
    calc
      residue v x = residue v 0 := by rw [hzero]
      _ = 0 := by
        have h0 := (ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S).residue_algebraMap
          v (0 : 𝓞 F)
        simpa using h0
  let u : Fˣ := Units.mk0 x hx0
  let t := toLoc v u
  have htLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v t := by
    have htval : Valued.v (t : v.adicCompletion F) = 1 := by
      change Valued.v (algebraMap F (v.adicCompletion F) x) = 1
      simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hxval]
    constructor
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, htval]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have hinv : Valued.v (((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) = 1 := by
        simp [Units.val_inv_eq_inv_val, htval]
      rw [hinv]
  have hclose : Valued.v ((t : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F a)) < 1 := by
    have htEq : (t : v.adicCompletion F) = algebraMap F _ x := by
      change algebraMap F _ (u : F) = algebraMap F _ x
      simp [u]
    rw [htEq]
    simp [x]
  simpa [t, u, x] using
    (ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S).localChi_approximant v hv t htLoc a ha hclose

private theorem rf_local_residue_not_mem (D : FieldData F) (S : SData F CE condη)
    (v : FinPlace F) (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) : x.out ∉ v.asIdeal := by
  intro hmem
  have hzero : (Ideal.Quotient.mk v.asIdeal x.out : 𝓞 F ⧸ v.asIdeal) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).2 hmem
  apply hx
  calc
    x = Ideal.Quotient.mk v.asIdeal x.out := by simp
    _ = 0 := hzero

private theorem rf_local_residue_val_one (D : FieldData F) (S : SData F CE condη)
    (v : FinPlace F) (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) :
    v.valuation F (algebraMap (𝓞 F) F x.out) = 1 := by
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hres : residue v (algebraMap (𝓞 F) F x.out) = x := by
    simpa using SB.residue_algebraMap v x.out
  have hxres : residue v (algebraMap (𝓞 F) F x.out) ≠ 0 := by
    rw [hres]
    exact hx
  exact (SB.residue_ne_zero v (algebraMap (𝓞 F) F x.out)
    (v.valuation_le_one x.out)).mp hxres

private theorem rf_localWeyl_phase_units {v : FinPlace F}
    (x p t : (v.adicCompletion F)ˣ) (e : ℤ) :
    (x / p)⁻¹ * (p ^ (e - 2) * t) = (p ^ (e - 1) * t) / x := by
  have hp : p * p ^ (e - 2) = p ^ (e - 1) := by
    calc
      p * p ^ (e - 2) = p ^ (1 : ℤ) * p ^ (e - 2) := by simp
      _ = p ^ ((1 : ℤ) + (e - 2)) := (zpow_add p _ _).symm
      _ = p ^ (e - 1) := by congr 1 <;> omega
  rw [inv_div]
  calc
    p / x * (p ^ (e - 2) * t) = (p * p ^ (e - 2) * t) / x := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = (p ^ (e - 1) * t) / x := by rw [hp]

private theorem rf_localWeyl_torus_units {v : FinPlace F}
    (x p t : (v.adicCompletion F)ˣ) (e : ℤ) :
    (p ^ (e - 2) * t) * -((x / p)⁻¹ * (x / p)⁻¹) =
      (p ^ e * t) * -(x ^ (-2 : ℤ)) := by
  have hsq : (p / x) * (p / x) = p ^ 2 / x ^ 2 := by
    calc
      (p / x) * (p / x) = p * p / (x * x) := div_mul_div_comm _ _ _ _
      _ = p ^ 2 / x ^ 2 := by simp [pow_two]
  have hpow : p ^ (e - 2) * p ^ 2 = p ^ e := by
    calc
      p ^ (e - 2) * p ^ 2 = p ^ (e - 2) * p ^ (2 : ℤ) := by congr 1
      _ = p ^ ((e - 2) + 2) := (zpow_add p _ _).symm
      _ = p ^ e := by congr 1 <;> omega
  have hxpow : (x ^ 2)⁻¹ = x ^ (-2 : ℤ) := by
    calc
      (x ^ (2 : ℕ))⁻¹ = (x ^ (2 : ℤ))⁻¹ :=
        congrArg Inv.inv (zpow_natCast x 2).symm
      _ = x ^ (-(2 : ℤ)) := (zpow_neg x 2).symm
      _ = x ^ (-2 : ℤ) := by norm_num
  have hpos : (p ^ (e - 2) * t) * (p ^ 2 / x ^ 2) =
      (p ^ e * t) * x ^ (-2 : ℤ) := by
    calc
      (p ^ (e - 2) * t) * (p ^ 2 / x ^ 2) =
          (p ^ (e - 2) * p ^ 2 * t) * (x ^ 2)⁻¹ := by
            rw [div_eq_mul_inv]
            ac_rfl
      _ = (p ^ e * t) * (x ^ 2)⁻¹ := by rw [hpow]
      _ = (p ^ e * t) * x ^ (-2 : ℤ) := by rw [hxpow]
  rw [inv_div, hsq]
  calc
    (p ^ (e - 2) * t) * -(p ^ 2 / x ^ 2) =
        -((p ^ (e - 2) * t) * (p ^ 2 / x ^ 2)) := by rw [mul_neg]
    _ = -((p ^ e * t) * x ^ (-2 : ℤ)) := congrArg Neg.neg hpos
    _ = (p ^ e * t) * -(x ^ (-2 : ℤ)) := (mul_neg _ _).symm

private theorem rf_localWeyl_scalar_factor (ct cx : ℂˣ) (hcx6 : cx ^ (6 : ℕ) = 1)
    (e : ℤ) :
    (ct ^ (4 : ℤ) * cx ^ (4 * (e - 2))) * (cx ^ (4 * e))⁻¹ *
        (ct ^ (-2 * e))⁻¹ = ct ^ (4 + 2 * e) * cx ^ (4 : ℤ) := by
  have hred : cx ^ (-8 : ℤ) = cx ^ (4 : ℤ) := by
    simpa using (zpow_eq_zpow_emod' (-8 : ℤ) hcx6)
  have hct : ct ^ (4 : ℤ) * (ct ^ (-2 * e))⁻¹ = ct ^ (4 + 2 * e) := by
    rw [← zpow_neg]
    rw [show -(-2 * e) = 2 * e by ring]
    exact (zpow_add ct (4 : ℤ) (2 * e)).symm
  have hcx : cx ^ (4 * (e - 2)) * (cx ^ (4 * e))⁻¹ = cx ^ (-8 : ℤ) := by
    rw [← zpow_neg]
    rw [(zpow_add cx (4 * (e - 2)) (-(4 * e))).symm]
    congr 1 <;> ring
  calc
    _ = (ct ^ (4 : ℤ) * (ct ^ (-2 * e))⁻¹) *
          (cx ^ (4 * (e - 2)) * (cx ^ (4 * e))⁻¹) := by ac_rfl
    _ = ct ^ (4 + 2 * e) * cx ^ (-8 : ℤ) := by rw [hct, hcx]
    _ = ct ^ (4 + 2 * e) * cx ^ (4 : ℤ) := by rw [hred]

private theorem rf_localWeyl_cover_group
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf)
    (Hh X : (v.adicCompletion F)ˣ) :
    ∃ ζ : rootsOfUnity 3 ℂ,
      ((ζ : ℂˣ) : ℂ) = extCocycle D v X (-(Hh⁻¹ * Hh⁻¹)) ∧
      R.C.a v X * R.C.w v * R.C.n v (Multiplicative.ofAdd (Hh : v.adicCompletion F)) =
        R.C.z ζ *
          (R.C.n v (Multiplicative.ofAdd ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : _)) *
            R.C.a v (X * (-(Hh⁻¹ * Hh⁻¹))) *
            R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _))) := by
  obtain ⟨ζ, hζ, hmul⟩ := R.C.a_mul v hv X (-(Hh⁻¹ * Hh⁻¹))
  have hna :
      R.C.n v (Multiplicative.ofAdd ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : _)) *
        R.C.a v X =
      R.C.a v X * R.C.n v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)) := by
    simpa [mul_assoc] using R.C.lift_na v
      ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : v.adicCompletion F) X
  refine ⟨ζ, hζ, ?_⟩
  calc
    R.C.a v X * R.C.w v * R.C.n v (Multiplicative.ofAdd (Hh : v.adicCompletion F)) =
        R.C.a v X * (R.C.w v * R.C.n v (Multiplicative.ofAdd (Hh : v.adicCompletion F))) := by
          rw [mul_assoc]
    _ = R.C.a v X *
        (R.C.n v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)) *
          R.C.a v (-(Hh⁻¹ * Hh⁻¹)) *
          R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _))) := by
          rw [R.C.lift_wn v Hh]
    _ = (R.C.a v X *
          R.C.n v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _))) *
          R.C.a v (-(Hh⁻¹ * Hh⁻¹)) *
          R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)) := by
          simp [mul_assoc]
    _ = (R.C.n v (Multiplicative.ofAdd ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : _)) *
          R.C.a v X) * R.C.a v (-(Hh⁻¹ * Hh⁻¹)) *
          R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)) := by
          rw [← hna]
    _ = R.C.n v (Multiplicative.ofAdd ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : _)) *
          (R.C.a v X * R.C.a v (-(Hh⁻¹ * Hh⁻¹))) *
          R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)) := by
          simp [mul_assoc]
    _ = R.C.n v (Multiplicative.ofAdd ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : _)) *
          (R.C.z ζ * R.C.a v (X * (-(Hh⁻¹ * Hh⁻¹)))) *
          R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)) := by
          rw [hmul]
    _ = R.C.z ζ *
          (R.C.n v (Multiplicative.ofAdd ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : _)) *
            R.C.a v (X * (-(Hh⁻¹ * Hh⁻¹))) *
            R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _))) := by
          calc
            _ = (R.C.n v (Multiplicative.ofAdd
                  ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : _)) * R.C.z ζ) *
                  (R.C.a v (X * (-(Hh⁻¹ * Hh⁻¹))) *
                    R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _))) := by
                  simp [mul_assoc]
            _ = (R.C.z ζ * R.C.n v (Multiplicative.ofAdd
                  ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : _))) *
                  (R.C.a v (X * (-(Hh⁻¹ * Hh⁻¹))) *
                    R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _))) := by
                  rw [R.C.z_central ζ]
            _ = _ := by simp [mul_assoc]

private theorem rf_localWeyl_nonzero_summand
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf)
    (e : ℤ) (t : (v.adicCompletion F)ˣ)
    (ht : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v t)
    (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) :
    R.T.Wv v (R.C.a v (toLoc v (primeGen R v) ^ (e - 2) * t) * R.C.w v *
      R.C.n v (Multiplicative.ofAdd (algebraMap F _
        (algebraMap (𝓞 F) F x.out / (primeGen R v : F))))) =
    localW R v e * localChi D v t ^ (4 + 2 * e) *
      chi D v (algebraMap (𝓞 F) F x.out) ^ 4 *
        A.ψ v (((toLoc v (primeGen R v) ^ (e - 1) * t :
          (v.adicCompletion F)ˣ) : _) / algebraMap F _ (algebraMap (𝓞 F) F x.out)) := by
  classical
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  let xF : F := algebraMap (𝓞 F) F x.out
  have hres : residue v xF = x := by simpa [xF] using SB.residue_algebraMap v x.out
  have hnotMem : x.out ∉ v.asIdeal := rf_local_residue_not_mem D S v x hx
  have hxFne : xF ≠ 0 := by
    intro hz
    have hzero : residue v (0 : F) = 0 := by
      have h := SB.residue_algebraMap v (0 : 𝓞 F)
      simpa using h
    apply hx
    calc
      x = residue v xF := hres.symm
      _ = residue v 0 := by rw [hz]
      _ = 0 := hzero
  let xu : Fˣ := Units.mk0 xF hxFne
  let xLoc : (v.adicCompletion F)ˣ := toLoc v xu
  have hxVal : v.valuation F xF = 1 := rf_local_residue_val_one D S v x hx
  have hxLocVal : Valued.v (xLoc : v.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) xF) = 1
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hxVal]
  have hxLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v xLoc := by
    constructor
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hxLocVal]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have hi : Valued.v (((xLoc⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) = 1 := by
        simp [Units.val_inv_eq_inv_val, hxLocVal]
      rw [hi]
  have hchiX : localChi D v xLoc = chi D v xF :=
    rf_localChi_algInt_unit D S v hv x.out hnotMem
  let p : Fˣ := primeGen R v
  let pLoc : (v.adicCompletion F)ˣ := toLoc v p
  let π : (v.adicCompletion F)ˣ := toLoc v (Units.mk0 (unif v) (unif_ne_zero v))
  let b : (v.adicCompletion F)ˣ := pLoc / π
  let X : (v.adicCompletion F)ˣ := pLoc ^ (e - 2) * t
  let Hh : (v.adicCompletion F)ˣ := xLoc / pLoc
  let Q : (v.adicCompletion F)ˣ := -(Hh⁻¹ * Hh⁻¹)
  let U : (v.adicCompletion F)ˣ := pLoc ^ e * t
  let V : (v.adicCompletion F)ˣ := -(xLoc ^ (-2 : ℤ))
  have hxLocMap : (xLoc : v.adicCompletion F) = algebraMap F (v.adicCompletion F) xF := by
    change algebraMap F (v.adicCompletion F) (xu : F) = _
    simp [xu]
  have hpLocMap : (pLoc : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (p : F) := by
    change algebraMap F (v.adicCompletion F) (p : F) = _
    rfl
  have hHroot : (Hh : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (xF / (p : F)) := by
    dsimp [Hh]
    rw [Units.val_div_eq_div_val, hxLocMap, hpLocMap, ← map_div₀]
  have hHinvRoot : (Hh⁻¹ : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((p : F) / xF) := by
    calc
      (Hh⁻¹ : v.adicCompletion F) = ((Hh : v.adicCompletion F)⁻¹) := by simp
      _ = (algebraMap F (v.adicCompletion F) (xF / (p : F)))⁻¹ := by rw [hHroot]
      _ = algebraMap F (v.adicCompletion F) ((xF / (p : F))⁻¹) := by simp
      _ = algebraMap F (v.adicCompletion F) ((p : F) / xF) := by rw [inv_div]
  have hHinvVal : Valued.v (Hh⁻¹ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [hHinvRoot]
    calc
      Valued.v (algebraMap F (v.adicCompletion F) ((p : F) / xF)) =
          v.valuation F ((p : F) / xF) := v.valuedAdicCompletion_eq_valuation' ((p : F) / xF)
      _ = v.valuation F (p : F) / v.valuation F xF := by rw [map_div₀]
      _ = WithZero.exp (-1 : ℤ) := by
        rw [rf_local_primeGen_valuation R v hv, hxVal]
        simp
  have hHinvLT : Valued.v (Hh⁻¹ : v.adicCompletion F) < 1 := by
    rw [hHinvVal, WithZero.exp_lt_one_iff]
    norm_num
  have hbProps := rf_local_primeGen_ratio_isLocUnit R v hv
  have hbLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v b := by
    simpa [b, pLoc, π, p] using hbProps.2
  have hpOrd : ordv v pLoc = 1 := by simpa [pLoc, p] using rf_local_primeGen_ord R v hv
  have htOrd : ordv v t = 0 := rf_ordv_zero_of_localUnit v t ht
  have hxOrd : ordv v xLoc = 0 := rf_ordv_zero_of_localUnit v xLoc hxLoc
  have hOrdX : ordv v X = e - 2 := by
    dsimp [X]
    rw [rf_ordv_mul, rf_ordv_zpow, hpOrd, htOrd]
    ring
  have hOrdU : ordv v U = e := by
    dsimp [U]
    rw [rf_ordv_mul, rf_ordv_zpow, hpOrd, htOrd]
    ring
  have hminusLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (-1 : (v.adicCompletion F)ˣ) := by
    constructor <;> simp [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hVLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v V := by
    change V ∈ rf_localUnitSubgroup v
    have hxPow : xLoc ^ (-2 : ℤ) ∈ rf_localUnitSubgroup v :=
      (rf_localUnitSubgroup v).zpow_mem hxLoc _
    have hneg : (-1 : (v.adicCompletion F)ˣ) ∈ rf_localUnitSubgroup v := hminusLoc
    have hmul := (rf_localUnitSubgroup v).mul_mem hneg hxPow
    change -(xLoc ^ (-2 : ℤ)) ∈ rf_localUnitSubgroup v
    rw [neg_eq_neg_one_mul]
    exact hmul
  have hOrdV : ordv v V = 0 := rf_ordv_zero_of_localUnit v V hVLoc
  have hQrel : Q = pLoc ^ (2 : ℤ) * V := by
    simpa [Q, V, Hh] using rf_localWeyl_torus_units xLoc pLoc (1 : (v.adicCompletion F)ˣ) 2
  have hOrdQ : ordv v Q = 2 := by
    rw [hQrel, rf_ordv_mul, rf_ordv_zpow, hpOrd, hOrdV]
    ring
  have hunitX : unitPart v X = b ^ (e - 2) * t := by
    dsimp [X, pLoc, p]
    exact rf_local_unitPart_primePower R v hv (e - 2) t ht
  have hunitU : unitPart v U = b ^ e * t := by
    dsimp [U, pLoc, p]
    exact rf_local_unitPart_primePower R v hv e t ht
  have hunitV : unitPart v V = V := by simp [unitPart, hOrdV]
  have hpLoc : pLoc = π * b := by
    dsimp [b]
    calc
      pLoc = (pLoc / π) * π := (div_mul_cancel _ _).symm
      _ = π * (pLoc / π) := by rw [mul_comm]
  have hunitQ : unitPart v Q = V * b ^ (2 : ℤ) := by
    calc
      unitPart v Q = Q * π ^ (-(2 : ℤ)) := by
        simp only [unitPart]
        rw [hOrdQ]
      _ = pLoc ^ (2 : ℤ) * V * π ^ (-(2 : ℤ)) := by rw [hQrel]
      _ = (π ^ (2 : ℤ) * b ^ (2 : ℤ) * V) * π ^ (-(2 : ℤ)) := by
        rw [hpLoc, mul_zpow]
      _ = V * b ^ (2 : ℤ) := by
        simp only [zpow_neg]
        calc
          π ^ (2 : ℤ) * b ^ (2 : ℤ) * V * (π ^ (2 : ℤ))⁻¹ =
              (π ^ (2 : ℤ) * (π ^ (2 : ℤ))⁻¹) * (V * b ^ (2 : ℤ)) := by ac_rfl
          _ = V * b ^ (2 : ℤ) := by simp
  let hv6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  have hbasic := ArtinPrimitiveRoots.A1.Theta.localChi_basic (D := D) (v := v) hv6
  have hchiT6 : localChi D v t ^ (6 : ℕ) = 1 := hbasic.2.2.2.1 t ht
  have hchiB6 : localChi D v b ^ (6 : ℕ) = 1 := hbasic.2.2.2.1 b hbLoc
  have hchiXLoc6 : localChi D v xLoc ^ (6 : ℕ) = 1 := hbasic.2.2.2.1 xLoc hxLoc
  have hBne : localChi D v b ≠ 0 := by
    intro hzero
    rw [hzero] at hchiB6
    norm_num at hchiB6
  have hTne : localChi D v t ≠ 0 := by
    intro hzero
    rw [hzero] at hchiT6
    norm_num at hchiT6
  have hXne : localChi D v xLoc ≠ 0 := by
    intro hzero
    rw [hzero] at hchiXLoc6
    norm_num at hchiXLoc6
  let cB : ℂˣ := Units.mk0 (localChi D v b) hBne
  let cT : ℂˣ := Units.mk0 (localChi D v t) hTne
  let cX : ℂˣ := Units.mk0 (localChi D v xLoc) hXne
  have hCB : (cB : ℂ) = localChi D v b := rfl
  have hCT : (cT : ℂ) = localChi D v t := rfl
  have hCX : (cX : ℂ) = chi D v xF := hchiX
  have hCX6 : cX ^ (6 : ℕ) = 1 := by
    apply Units.ext
    exact hchiXLoc6
  have hBpow : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (b ^ (e - 2)) := by
    change b ^ (e - 2) ∈ rf_localUnitSubgroup v
    exact (rf_localUnitSubgroup v).zpow_mem hbLoc _
  have hChiUnitX : localChi D v (unitPart v X) =
      ((cB ^ (e - 2) * cT : ℂˣ) : ℂ) := by
    rw [hunitX]
    calc
      localChi D v (b ^ (e - 2) * t) =
          localChi D v (b ^ (e - 2)) * localChi D v t := hbasic.2.2.1 _ _ hBpow ht
      _ = ((cB ^ (e - 2) : ℂˣ) : ℂ) * (cT : ℂ) := by
        rw [rf_localChi_zpow D v hv6 b hbLoc (e - 2)]
        simp only [← hCB, ← hCT, Units.val_zpow_eq_zpow_val]
      _ = ((cB ^ (e - 2) * cT : ℂˣ) : ℂ) := by simp
  have hB2Loc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (b ^ (2 : ℤ)) := by
    change b ^ (2 : ℤ) ∈ rf_localUnitSubgroup v
    exact (rf_localUnitSubgroup v).zpow_mem hbLoc _
  have hXminus2Loc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (xLoc ^ (-2 : ℤ)) := by
    change xLoc ^ (-2 : ℤ) ∈ rf_localUnitSubgroup v
    exact (rf_localUnitSubgroup v).zpow_mem hxLoc _
  have hChiV : localChi D v V = ((cX ^ (-2 : ℤ) : ℂˣ) : ℂ) := by
    have hVmul : V = (-1 : (v.adicCompletion F)ˣ) * xLoc ^ (-2 : ℤ) := by
      dsimp [V]
      exact neg_eq_neg_one_mul _
    have hmul := hbasic.2.2.1 (-1) (xLoc ^ (-2 : ℤ)) hminusLoc hXminus2Loc
    calc
      localChi D v V = localChi D v ((-1 : (v.adicCompletion F)ˣ) * xLoc ^ (-2 : ℤ)) := by
        rw [hVmul]
      _ = localChi D v (-1) * localChi D v (xLoc ^ (-2 : ℤ)) := hmul
      _ = (cX ^ (-2 : ℤ) : ℂˣ) := by
        rw [hbasic.2.1, rf_localChi_zpow D v hv6 xLoc hxLoc (-2), hchiX, ← hCX]
        simp only [one_mul, Units.val_zpow_eq_zpow_val]
      _ = ((cX ^ (-2 : ℤ) : ℂˣ) : ℂ) := rfl
  have hChiUnitQ : localChi D v (unitPart v Q) =
      ((cX ^ (-2 : ℤ) * cB ^ (2 : ℤ) : ℂˣ) : ℂ) := by
    rw [hunitQ]
    have hmul := hbasic.2.2.1 V (b ^ (2 : ℤ)) hVLoc hB2Loc
    calc
      localChi D v (V * b ^ (2 : ℤ)) = localChi D v V * localChi D v (b ^ (2 : ℤ)) := hmul
      _ = ((cX ^ (-2 : ℤ) : ℂˣ) : ℂ) *
          ((cB ^ (2 : ℤ) : ℂˣ) : ℂ) := by
        rw [hChiV, rf_localChi_zpow D v hv6 b hbLoc (2 : ℤ)]
        simp only [← hCB, Units.val_zpow_eq_zpow_val]
      _ = ((cX ^ (-2 : ℤ) * cB ^ (2 : ℤ) : ℂˣ) : ℂ) := by simp
  have hChiUnitU : localChi D v (unitPart v U) =
      ((cB ^ e * cT : ℂˣ) : ℂ) := by
    rw [hunitU]
    have hBpow' : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (b ^ e) := by
      change b ^ e ∈ rf_localUnitSubgroup v
      exact (rf_localUnitSubgroup v).zpow_mem hbLoc _
    calc
      localChi D v (b ^ e * t) = localChi D v (b ^ e) * localChi D v t :=
        hbasic.2.2.1 _ _ hBpow' ht
      _ = ((cB ^ e : ℂˣ) : ℂ) * (cT : ℂ) := by
        rw [rf_localChi_zpow D v hv6 b hbLoc e]
        simp only [← hCB, ← hCT, Units.val_zpow_eq_zpow_val]
      _ = ((cB ^ e * cT : ℂˣ) : ℂ) := by simp
  have hscalar1Unit :
      (cB ^ (e - 2) * cT) ^ (4 : ℤ) *
        (cX ^ (-2 : ℤ) * cB ^ (2 : ℤ)) ^ (-2 * (e - 2)) =
      cT ^ (4 : ℤ) * cX ^ (4 * (e - 2)) := by
    calc
      _ = (cB ^ (e - 2)) ^ (4 : ℤ) * cT ^ (4 : ℤ) *
          ((cX ^ (-2 : ℤ)) ^ (-2 * (e - 2)) *
            (cB ^ (2 : ℤ)) ^ (-2 * (e - 2))) := by
              rw [mul_zpow, mul_zpow]
      _ = cB ^ ((e - 2) * 4) * cT ^ (4 : ℤ) *
          (cX ^ ((-2 : ℤ) * (-2 * (e - 2))) *
            cB ^ (2 * (-2 * (e - 2)))) := by
              rw [← zpow_mul, ← zpow_mul, ← zpow_mul]
      _ = (cB ^ ((e - 2) * 4) * cB ^ (2 * (-2 * (e - 2)))) *
          cT ^ (4 : ℤ) * cX ^ ((-2 : ℤ) * (-2 * (e - 2))) := by ac_rfl
      _ = cB ^ ((e - 2) * 4 + 2 * (-2 * (e - 2))) * cT ^ (4 : ℤ) *
          cX ^ ((-2 : ℤ) * (-2 * (e - 2))) := by
              rw [← zpow_add]
      _ = cT ^ (4 : ℤ) * cX ^ (4 * (e - 2)) := by
            have hBexp : (e - 2) * 4 + 2 * (-2 * (e - 2)) = 0 := by ring
            have hXexp : (-2 : ℤ) * (-2 * (e - 2)) = 4 * (e - 2) := by ring
            rw [hBexp, hXexp, zpow_zero]
            simp
  have hcentral1 : extCocycle D v X Q =
      ((cT ^ (4 : ℤ) * cX ^ (4 * (e - 2)) : ℂˣ) : ℂ) := by
    unfold extCocycle
    rw [hOrdQ, hOrdX, hChiUnitX, hChiUnitQ]
    norm_num
    simpa [Units.val_mul, Units.val_zpow_eq_zpow_val] using
      congrArg (fun z : ℂˣ => (z : ℂ)) hscalar1Unit
  have hscalar2Unit :
      (cX ^ (-2 : ℤ)) ^ (-2 * e) = cX ^ (4 * e) := by
    calc
      (cX ^ (-2 : ℤ)) ^ (-2 * e) = cX ^ ((-2 : ℤ) * (-2 * e)) :=
        (zpow_mul cX (-2 : ℤ) (-2 * e)).symm
      _ = cX ^ (4 * e) := by congr 1 <;> ring
  have hcentral2 : extCocycle D v U V =
      ((cX ^ (4 * e) : ℂˣ) : ℂ) := by
    unfold extCocycle
    rw [hOrdV, hOrdU, hChiUnitU, hunitV, hChiV]
    simp only [mul_zero, zpow_zero, one_mul]
    have hmap := congrArg (fun z : ℂˣ => (z : ℂ)) hscalar2Unit
    rw [Units.val_zpow_eq_zpow_val] at hmap
    convert hmap using 1 <;> ring
  have hOneLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (1 : (v.adicCompletion F)ˣ) := by
    constructor <;> simp [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hunitP : unitPart v (pLoc ^ e) = b ^ e := by
    simpa using rf_local_unitPart_primePower R v hv e 1 hOneLoc
  have hunitT : unitPart v t = t := by
    simp [unitPart, htOrd]
  have hcentral3 : extCocycle D v (pLoc ^ e) t =
      ((cT ^ (-2 * e) : ℂˣ) : ℂ) := by
    unfold extCocycle
    rw [hunitP, hunitT, htOrd, rf_ordv_zpow v pLoc e, hpOrd]
    simp [hCT, Units.val_zpow_eq_zpow_val]
  have hscalar := rf_localWeyl_scalar_factor cT cX hCX6 e
  have htotal : extCocycle D v X Q * (extCocycle D v U V)⁻¹ *
      (extCocycle D v (pLoc ^ e) t)⁻¹ =
      localChi D v t ^ (4 + 2 * e) * chi D v xF ^ 4 := by
    calc
      _ = ((cT ^ (4 : ℤ) * cX ^ (4 * (e - 2)) : ℂˣ) : ℂ) *
          (((cX ^ (4 * e) : ℂˣ) : ℂ))⁻¹ * (((cT ^ (-2 * e) : ℂˣ) : ℂ))⁻¹ := by
            rw [hcentral1, hcentral2, hcentral3]
      _ = ((cT ^ (4 : ℤ) * cX ^ (4 * (e - 2)) *
            (cX ^ (4 * e))⁻¹ * (cT ^ (-2 * e))⁻¹ : ℂˣ) : ℂ) := by simp
      _ = ((cT ^ (4 + 2 * e) * cX ^ (4 : ℤ) : ℂˣ) : ℂ) :=
        congrArg (fun z : ℂˣ => (z : ℂ)) hscalar
      _ = localChi D v t ^ (4 + 2 * e) * chi D v xF ^ 4 := by
        simp [hCT, hCX, Units.val_zpow_eq_zpow_val, Units.val_mul]
  have hXQ : X * Q = U * V := by
    simpa [X, Q, U, V, Hh] using rf_localWeyl_torus_units xLoc pLoc t e
  obtain ⟨ζ₁, hζ₁, hcover⟩ := rf_localWeyl_cover_group R v hv Hh X
  have hnarg :
      algebraMap F (v.adicCompletion F)
          (algebraMap (𝓞 F) F x.out / (primeGen R v : F)) =
        (Hh : v.adicCompletion F) := by
    simpa [xF, p] using hHroot.symm
  have hHinvLTunit : Valued.v ((Hh⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) < 1 := by
    simpa using hHinvLT
  have hinput :
      R.C.a v X * R.C.w v * R.C.n v (Multiplicative.ofAdd
          (algebraMap F (v.adicCompletion F)
            (algebraMap (𝓞 F) F x.out / (primeGen R v : F)))) =
        R.C.a v X * R.C.w v * R.C.n v (Multiplicative.ofAdd (Hh : v.adicCompletion F)) := by
    rw [hnarg]
  have hbarK : R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)) ∈ R.C.Kext :=
    R.C.nbar_Kext v hv ((Hh⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) hHinvLTunit
  have hbarLoc : R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)) ∈ R.C.Gloc v :=
    R.C.nbar_mem v ((Hh⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
  have hbarRight := R.T.Wv_right v hv (R.C.a v (X * Q))
    (R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _))) hbarK hbarLoc
  obtain ⟨ζ₂, hζ₂, hmul₂⟩ := R.C.a_mul v hv U V
  have hVcompact : R.C.a v V ∈ R.C.Kext := R.C.a_Kext v hv V hVLoc.1 hVLoc.2
  have hVright := R.T.Wv_right v hv (R.C.a v U) (R.C.a v V) hVcompact (R.C.a_mem v V)
  have hζ₂ne : ((ζ₂ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero (ζ₂ : ℂˣ)
  have hUVlocal : R.T.Wv v (R.C.a v (U * V)) =
      ((ζ₂ : ℂˣ) : ℂ)⁻¹ * R.T.Wv v (R.C.a v U) := by
    calc
      R.T.Wv v (R.C.a v (U * V)) =
          ((ζ₂ : ℂˣ) : ℂ)⁻¹ * (((ζ₂ : ℂˣ) : ℂ) * R.T.Wv v (R.C.a v (U * V))) := by
            rw [← mul_assoc, inv_mul_cancel₀ hζ₂ne, one_mul]
      _ = ((ζ₂ : ℂˣ) : ℂ)⁻¹ * R.T.Wv v (R.C.a v U) := by
            rw [← hVright, hmul₂, R.T.Wv_genuine v hv ζ₂ (R.C.a v (U * V))]
  obtain ⟨ζ₃, hζ₃, hmul₃⟩ := R.C.a_mul v hv (pLoc ^ e) t
  have htcompact : R.C.a v t ∈ R.C.Kext := R.C.a_Kext v hv t ht.1 ht.2
  have htright := R.T.Wv_right v hv (R.C.a v (pLoc ^ e)) (R.C.a v t)
    htcompact (R.C.a_mem v t)
  have hζ₃ne : ((ζ₃ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero (ζ₃ : ℂˣ)
  have hUlocal : R.T.Wv v (R.C.a v U) =
      ((ζ₃ : ℂˣ) : ℂ)⁻¹ * localW R v e := by
    calc
      R.T.Wv v (R.C.a v U) =
          ((ζ₃ : ℂˣ) : ℂ)⁻¹ * (((ζ₃ : ℂˣ) : ℂ) * R.T.Wv v (R.C.a v U)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hζ₃ne, one_mul]
      _ = ((ζ₃ : ℂˣ) : ℂ)⁻¹ * R.T.Wv v (R.C.a v (pLoc ^ e)) := by
            rw [← htright, hmul₃, R.T.Wv_genuine v hv ζ₃ (R.C.a v U)]
      _ = ((ζ₃ : ℂˣ) : ℂ)⁻¹ * localW R v e := by rfl
  have hWeylTable : R.T.Wv v (R.C.a v (X * Q)) =
      (extCocycle D v U V)⁻¹ *
        ((extCocycle D v (pLoc ^ e) t)⁻¹ * localW R v e) := by
    calc
      R.T.Wv v (R.C.a v (X * Q)) = R.T.Wv v (R.C.a v (U * V)) := by rw [hXQ]
      _ = ((ζ₂ : ℂˣ) : ℂ)⁻¹ * R.T.Wv v (R.C.a v U) := hUVlocal
      _ = ((ζ₂ : ℂˣ) : ℂ)⁻¹ * (((ζ₃ : ℂˣ) : ℂ)⁻¹ * localW R v e) := by rw [hUlocal]
      _ = (extCocycle D v U V)⁻¹ *
          ((extCocycle D v (pLoc ^ e) t)⁻¹ * localW R v e) := by rw [hζ₂, hζ₃]
  have hfactor : ((ζ₁ : ℂˣ) : ℂ) * (extCocycle D v U V)⁻¹ *
      (extCocycle D v (pLoc ^ e) t)⁻¹ =
      localChi D v t ^ (4 + 2 * e) * chi D v xF ^ 4 := by
    rw [hζ₁]
    exact htotal
  calc
    R.T.Wv v (R.C.a v (toLoc v (primeGen R v) ^ (e - 2) * t) * R.C.w v *
        R.C.n v (Multiplicative.ofAdd (algebraMap F _
          (algebraMap (𝓞 F) F x.out / (primeGen R v : F)))) ) =
        R.T.Wv v (R.C.a v X * R.C.w v *
          R.C.n v (Multiplicative.ofAdd (Hh : v.adicCompletion F)) ) := by
            rw [← hinput]
    _ = R.T.Wv v (R.C.z ζ₁ *
          (R.C.n v (Multiplicative.ofAdd ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : _)) *
            R.C.a v (X * Q) *
            R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)))) := by
              rw [hcover]
    _ = ((ζ₁ : ℂˣ) : ℂ) *
          R.T.Wv v (R.C.n v (Multiplicative.ofAdd ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : _)) *
            (R.C.a v (X * Q) *
              R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)))) := by
              rw [R.T.Wv_genuine v hv ζ₁]
              congr 1
              simp only [mul_assoc]
    _ = ((ζ₁ : ℂˣ) : ℂ) *
          (A.ψ v ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
            R.T.Wv v (R.C.a v (X * Q) *
              R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)))) := by
              rw [R.T.Wv_equiv v hv
                ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : v.adicCompletion F)
                (R.C.a v (X * Q) *
                  R.C.nbar v (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : _)))]
    _ = ((ζ₁ : ℂˣ) : ℂ) *
          (A.ψ v ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
            R.T.Wv v (R.C.a v (X * Q))) := by rw [hbarRight]
    _ = (((ζ₁ : ℂˣ) : ℂ) *
          (A.ψ v ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : v.adicCompletion F))) *
          ((extCocycle D v U V)⁻¹ *
            ((extCocycle D v (pLoc ^ e) t)⁻¹ * localW R v e)) := by rw [hWeylTable]; ac_rfl
    _ = localW R v e * localChi D v t ^ (4 + 2 * e) * chi D v xF ^ 4 *
          A.ψ v (((toLoc v (primeGen R v) ^ (e - 1) * t : (v.adicCompletion F)ˣ) : _) /
            algebraMap F _ (algebraMap (𝓞 F) F x.out)) := by
              have hphase : Hh⁻¹ * X = (pLoc ^ (e - 1) * t) / xLoc := by
                simpa [Hh, X] using rf_localWeyl_phase_units xLoc pLoc t e
              have hphaseArg :
                  ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
                    (((pLoc ^ (e - 1) * t : (v.adicCompletion F)ˣ) : v.adicCompletion F) /
                      algebraMap F (v.adicCompletion F) xF) := by
                rw [hphase, Units.val_div_eq_div_val, hxLocMap]
              have hphaseRhs :
                  (((pLoc ^ (e - 1) * t : (v.adicCompletion F)ˣ) : v.adicCompletion F) /
                      algebraMap F (v.adicCompletion F) xF) =
                    (((toLoc v (primeGen R v) ^ (e - 1) * t : (v.adicCompletion F)ˣ) : _) /
                      algebraMap F _ (algebraMap (𝓞 F) F x.out)) := by
                simp [pLoc, p, xF]
              calc
                ((ζ₁ : ℂˣ) : ℂ) *
                    (A.ψ v ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : v.adicCompletion F)) *
                    ((extCocycle D v U V)⁻¹ *
                      ((extCocycle D v (pLoc ^ e) t)⁻¹ * localW R v e)) =
                  localW R v e *
                    (((ζ₁ : ℂˣ) : ℂ) * (extCocycle D v U V)⁻¹ *
                      (extCocycle D v (pLoc ^ e) t)⁻¹) *
                    A.ψ v ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by ac_rfl
                _ = localW R v e *
                    (localChi D v t ^ (4 + 2 * e) * chi D v xF ^ 4) *
                    A.ψ v ((Hh⁻¹ * X : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
                      rw [hfactor]
                _ = localW R v e * localChi D v t ^ (4 + 2 * e) * chi D v xF ^ 4 *
                    A.ψ v (((toLoc v (primeGen R v) ^ (e - 1) * t : (v.adicCompletion F)ˣ) : _) /
                      algebraMap F _ (algebraMap (𝓞 F) F x.out)) := by
                  have hψeq := congrArg (A.ψ v) (hphaseArg.trans hphaseRhs)
                  rw [hψeq] <;> ac_rfl

private theorem rf_localWeyl_positive_phase
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf)
    (e : ℤ) (he : 0 < e) (t : (v.adicCompletion F)ˣ)
    (ht : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v t)
    (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) :
    A.ψ v (((toLoc v (primeGen R v) ^ (e - 1) * t : (v.adicCompletion F)ˣ) : _) /
      algebraMap F _ (algebraMap (𝓞 F) F x.out)) = 1 := by
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  let xF : F := algebraMap (𝓞 F) F x.out
  have hres : residue v xF = x := by simpa [xF] using SB.residue_algebraMap v x.out
  have hnotMem : x.out ∉ v.asIdeal := rf_local_residue_not_mem D S v x hx
  have hxFne : xF ≠ 0 := by
    intro hz
    have hzero : residue v (0 : F) = 0 := by
      have h := SB.residue_algebraMap v (0 : 𝓞 F)
      simpa using h
    apply hx
    calc
      x = residue v xF := hres.symm
      _ = residue v 0 := by rw [hz]
      _ = 0 := hzero
  let xu : Fˣ := Units.mk0 xF hxFne
  let xLoc : (v.adicCompletion F)ˣ := toLoc v xu
  have hxVal : v.valuation F xF = 1 := rf_local_residue_val_one D S v x hx
  have hxLocMap : (xLoc : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) xF := by
    change algebraMap F (v.adicCompletion F) (xu : F) = _
    simp [xu]
  have hxLocVal : Valued.v (xLoc : v.adicCompletion F) = 1 := by
    calc
      Valued.v (xLoc : v.adicCompletion F) =
          Valued.v (algebraMap F (v.adicCompletion F) xF) := by rw [hxLocMap]
      _ = v.valuation F xF := v.valuedAdicCompletion_eq_valuation' xF
      _ = 1 := hxVal
  have hxLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v xLoc := by
    constructor
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hxLocVal]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have hinv : Valued.v (((xLoc⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) = 1 := by
        simp [Units.val_inv_eq_inv_val, hxLocVal]
      rw [hinv]
  let pLoc := toLoc v (primeGen R v)
  have hpOrd : ordv v pLoc = 1 := rf_local_primeGen_ord R v hv
  have htOrd : ordv v t = 0 := rf_ordv_zero_of_localUnit v t ht
  have hxOrd : ordv v xLoc = 0 := rf_ordv_zero_of_localUnit v xLoc hxLoc
  have huOrd : ordv v (pLoc ^ (e - 1) * t) = e - 1 := by
    rw [rf_ordv_mul, rf_ordv_zpow, hpOrd, htOrd]
    ring
  have hxInvOrd : ordv v xLoc⁻¹ = 0 := by
    have h := rf_ordv_zpow v xLoc (-1)
    rw [hxOrd] at h
    simpa using h
  have hphaseOrd : ordv v ((pLoc ^ (e - 1) * t) / xLoc) = e - 1 := by
    calc
      ordv v ((pLoc ^ (e - 1) * t) / xLoc) =
          ordv v ((pLoc ^ (e - 1) * t) * xLoc⁻¹) := by rw [div_eq_mul_inv]
      _ = ordv v (pLoc ^ (e - 1) * t) + ordv v xLoc⁻¹ := rf_ordv_mul _ _ _
      _ = e - 1 := by rw [huOrd, hxInvOrd]; ring
  have hphaseval :
      ((pLoc ^ (e - 1) * t / xLoc : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        (((toLoc v (primeGen R v) ^ (e - 1) * t : (v.adicCompletion F)ˣ) : _) /
          algebraMap F _ (algebraMap (𝓞 F) F x.out)) := by
    rw [Units.val_div_eq_div_val, hxLocMap]
  rw [← hphaseval]
  apply rf_local_addchar_trivial_of_ord_nonneg v _ ?_
  rw [hphaseOrd]
  omega

private theorem rf_localR_formula
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf)
    (j : Fin 6) (e : ℤ) (t : (v.adicCompletion F)ˣ)
    (ht : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v t) :
    localR R v j e t = localW R v e * localChi D v t ^ (4 + 2 * e) *
      ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
        maskAlpha D A v (primeGen R v) j x * chi D v (algebraMap (𝓞 F) F x.out) ^ 4 *
          A.ψ v (((toLoc v (primeGen R v) ^ (e - 1) * t :
            (v.adicCompletion F)ˣ) : _) /
              algebraMap F _ (algebraMap (𝓞 F) F x.out)) := by
  classical
  letI := ArtinPrimitiveRoots.A2.bridgeResidueFintype v
  let c := localW R v e * localChi D v t ^ (4 + 2 * e)
  let f : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x =>
    if x = 0 then 0 else maskAlpha D A v (primeGen R v) j x *
      R.T.Wv v (R.C.a v (toLoc v (primeGen R v) ^ (e - 2) * t) * R.C.w v *
        R.C.n v (Multiplicative.ofAdd (algebraMap F _
          (algebraMap (𝓞 F) F x.out / (primeGen R v : F)))))
  let g : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x =>
    if x = 0 then 0 else maskAlpha D A v (primeGen R v) j x *
      chi D v (algebraMap (𝓞 F) F x.out) ^ 4 *
        A.ψ v (((toLoc v (primeGen R v) ^ (e - 1) * t :
          (v.adicCompletion F)ˣ) : _) /
            algebraMap F _ (algebraMap (𝓞 F) F x.out))
  have hfinsum := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v f
  have hginsum := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v g
  have hpoint (x : 𝓞 F ⧸ v.asIdeal) : f x = c * g x := by
    by_cases hx : x = 0
    · simp [f, g, hx]
    · simp only [f, g, if_neg hx]
      rw [rf_localWeyl_nonzero_summand R v hv e t ht x hx]
      ring
  calc
    localR R v j e t = ∑ x : 𝓞 F ⧸ v.asIdeal, f x := by
      unfold localR
      rw [hfinsum]
    _ = c * ∑ x : 𝓞 F ⧸ v.asIdeal, g x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      exact hpoint x
    _ = localW R v e * localChi D v t ^ (4 + 2 * e) * ∑ᶠ x, g x := by
      rw [← hginsum]
    _ = _ := by rfl

private theorem rf_local_addchar_out_phase
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf)
    (ψ : AddChar (𝓞 F ⧸ v.asIdeal) ℂ)
    (hψval : ∀ a b, ψ (a * b) = A.ψ v (algebraMap F _
      (algebraMap (𝓞 F) F b.out * algebraMap (𝓞 F) F a.out /
        (primeGen R v : F))))
    (b : 𝓞 F) (hb : b ∉ v.asIdeal) :
    ψ (Ideal.Quotient.mk v.asIdeal b) = A.ψ v (algebraMap F (v.adicCompletion F)
      (algebraMap (𝓞 F) F b / (primeGen R v : F))) := by
  classical
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  let y : 𝓞 F ⧸ v.asIdeal := Ideal.Quotient.mk v.asIdeal b
  let yRep : 𝓞 F := y.out
  let oneRep : 𝓞 F := (1 : 𝓞 F ⧸ v.asIdeal).out
  let yF : F := algebraMap (𝓞 F) F yRep
  let oneF : F := algebraMap (𝓞 F) F oneRep
  let bF : F := algebraMap (𝓞 F) F b
  let deltaO : 𝓞 F := yRep * oneRep - b
  let deltaF : F := algebraMap (𝓞 F) F deltaO
  let pLoc := toLoc v (primeGen R v)
  have hyRep : Ideal.Quotient.mk v.asIdeal yRep = y := by
    simp [yRep]
  have hmkOne : Ideal.Quotient.mk v.asIdeal oneRep = 1 := by
    simp [oneRep]
  have hdeltaMk : Ideal.Quotient.mk v.asIdeal deltaO = 0 := by
    dsimp [deltaO]
    rw [map_sub, map_mul, hyRep, hmkOne]
    simp [y]
  have hdeltaRes : residue v deltaF = 0 := by
    rw [SB.residue_algebraMap]
    exact hdeltaMk
  have hdeltaLe : v.valuation F deltaF ≤ 1 := by
    exact v.valuation_le_one deltaO
  have hdeltaLt : v.valuation F deltaF < 1 := by
    by_contra hnot
    have heq : v.valuation F deltaF = 1 := le_antisymm hdeltaLe (le_of_not_gt hnot)
    exact ((SB.residue_ne_zero v deltaF hdeltaLe).2 heq) hdeltaRes
  have hdeltaComp : Valued.v (algebraMap F (v.adicCompletion F) deltaF) ≤
      WithZero.exp (-1 : ℤ) :=
    rf_valued_lt_one_le_exp_neg_one v _ (by
      calc
        Valued.v (algebraMap F (v.adicCompletion F) deltaF) =
            v.valuation F deltaF := v.valuedAdicCompletion_eq_valuation' deltaF
        _ < 1 := hdeltaLt)
  have hdeltaValExp : v.valuation F deltaF ≤ WithZero.exp (-1 : ℤ) := by
    calc
      v.valuation F deltaF = Valued.v (algebraMap F (v.adicCompletion F) deltaF) :=
        (v.valuedAdicCompletion_eq_valuation' deltaF).symm
      _ ≤ WithZero.exp (-1 : ℤ) := hdeltaComp
  have hpPos : 0 < WithZero.exp (-1 : ℤ) :=
    lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
  have hdeltaLoc : Valued.v
      (algebraMap F (v.adicCompletion F) (deltaF / (primeGen R v : F))) ≤ 1 := by
    calc
      Valued.v (algebraMap F (v.adicCompletion F) (deltaF / (primeGen R v : F))) =
          v.valuation F (deltaF / (primeGen R v : F)) :=
            v.valuedAdicCompletion_eq_valuation' _
      _ = v.valuation F deltaF / v.valuation F (primeGen R v : F) := by
        rw [map_div₀]
      _ ≤ 1 := by
        rw [rf_local_primeGen_valuation R v hv]
        exact (div_le_one₀ hpPos).2 hdeltaValExp
  have hdeltaInt : algebraMap F (v.adicCompletion F) (deltaF / (primeGen R v : F)) ∈
      v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hdeltaLoc
  have hargsF : yF * oneF / (primeGen R v : F) =
      bF / (primeGen R v : F) + deltaF / (primeGen R v : F) := by
    dsimp [deltaF, deltaO, yF, oneF, bF]
    rw [map_sub, map_mul]
    field_simp [Units.ne_zero (primeGen R v)]
    ring
  have hargs : algebraMap F (v.adicCompletion F) (yF * oneF / (primeGen R v : F)) =
      algebraMap F (v.adicCompletion F) (bF / (primeGen R v : F)) +
        algebraMap F (v.adicCompletion F) (deltaF / (primeGen R v : F)) := by
    calc
      _ = algebraMap F (v.adicCompletion F)
          (bF / (primeGen R v : F) + deltaF / (primeGen R v : F)) :=
            congrArg (algebraMap F (v.adicCompletion F)) hargsF
      _ = _ := by rw [map_add]
  have hψ := hψval (1 : 𝓞 F ⧸ v.asIdeal) y
  have hψ' : ψ y = A.ψ v (algebraMap F (v.adicCompletion F)
      (yF * oneF / (primeGen R v : F))) := by
    simpa [y, yF, oneF] using hψ
  calc
    ψ y = A.ψ v (algebraMap F (v.adicCompletion F)
        (yF * oneF / (primeGen R v : F))) := hψ'
    _ = A.ψ v (algebraMap F (v.adicCompletion F)
        (bF / (primeGen R v : F))) := by
          rw [hargs, (A.ψ v).map_add_eq_mul, A.integral v _ hdeltaInt, mul_one]

private theorem rf_local_inverse_phase_residue
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf)
    (xF : F) (xLoc : (v.adicCompletion F)ˣ)
    (hxLocMap : (xLoc : v.adicCompletion F) = algebraMap F _ xF)
    (t u : (v.adicCompletion F)ˣ)
    (huEq : u = t / xLoc)
    (b : 𝓞 F) (hb : b ∉ v.asIdeal)
    (hclose : Valued.v ((u : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F b)) < 1)
    (ψ : AddChar (𝓞 F ⧸ v.asIdeal) ℂ)
    (hψval : ∀ a b, ψ (a * b) = A.ψ v (algebraMap F _
      (algebraMap (𝓞 F) F b.out * algebraMap (𝓞 F) F a.out /
        (primeGen R v : F)))) :
    A.ψ v ((((toLoc v (primeGen R v))⁻¹ * t : (v.adicCompletion F)ˣ) : _) /
      algebraMap F _ xF) = ψ (Ideal.Quotient.mk v.asIdeal b) := by
  classical
  let pLoc := toLoc v (primeGen R v)
  have hunit : (pLoc⁻¹ * t) / xLoc = pLoc⁻¹ * u := by
    rw [div_eq_mul_inv, huEq, div_eq_mul_inv]
    ac_rfl
  have hphaseArg :
      ((((pLoc⁻¹ * t : (v.adicCompletion F)ˣ) : v.adicCompletion F) /
        algebraMap F (v.adicCompletion F) xF)) =
        (((pLoc⁻¹ * u : (v.adicCompletion F)ˣ) : v.adicCompletion F)) := by
    calc
      _ = ((pLoc⁻¹ * t : (v.adicCompletion F)ˣ) : v.adicCompletion F) /
          (xLoc : v.adicCompletion F) := by rw [hxLocMap]
      _ = ((((pLoc⁻¹ * t) / xLoc : (v.adicCompletion F)ˣ) :
          v.adicCompletion F)) := (Units.val_div_eq_div_val _ _).symm
      _ = (((pLoc⁻¹ * u : (v.adicCompletion F)ˣ) :
          v.adicCompletion F)) := congrArg Units.val hunit
  calc
    A.ψ v ((((pLoc⁻¹ * t : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) /
          algebraMap F (v.adicCompletion F) xF)) =
        A.ψ v (((pLoc⁻¹ * u : (v.adicCompletion F)ˣ) :
          v.adicCompletion F)) := by rw [hphaseArg]
    _ = A.ψ v (algebraMap F (v.adicCompletion F)
        (algebraMap (𝓞 F) F b / (primeGen R v : F))) :=
          rf_local_phase_approximant R v hv u b hb hclose
    _ = ψ (Ideal.Quotient.mk v.asIdeal b) := by
      exact (rf_local_addchar_out_phase R v hv ψ hψval b hb).symm

private theorem rf_local_residue_t_mul_digit
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) (hv : v ∉ S.Sf)
    (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) (xF : F)
    (hxF : xF = algebraMap (𝓞 F) F x.out)
    (xLoc : (v.adicCompletion F)ˣ)
    (hxLocMap : (xLoc : v.adicCompletion F) = algebraMap F _ xF)
    (hxLocVal : Valued.v (xLoc : v.adicCompletion F) = 1)
    (t u : (v.adicCompletion F)ˣ) (huEq : u = t / xLoc)
    (a : 𝓞 F) (ha : a ∉ v.asIdeal)
    (hcloseT : Valued.v ((t : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F a)) < 1)
    (b : 𝓞 F) (hb : b ∉ v.asIdeal)
    (hcloseU : Valued.v ((u : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F b)) < 1) :
    Ideal.Quotient.mk v.asIdeal b * x = residue v (algebraMap (𝓞 F) F a) := by
  classical
  letI := ArtinPrimitiveRoots.A2.bridgeResidueField v
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  let aF : F := algebraMap (𝓞 F) F a
  let bF : F := algebraMap (𝓞 F) F b
  have hresX : residue v xF = x := by
    rw [hxF]
    simpa using SB.residue_algebraMap v x.out
  have hxresne : residue v xF ≠ 0 := by
    rw [hresX]
    exact hx
  have hxvalLe : v.valuation F xF ≤ 1 := by
    rw [hxF]
    exact v.valuation_le_one x.out
  have hxval : v.valuation F xF = 1 :=
    (SB.residue_ne_zero v xF hxvalLe).1 hxresne
  have hxFne : xF ≠ 0 := by
    intro hz
    rw [hz] at hxval
    norm_num at hxval
  have hresAne : residue v aF ≠ 0 := by
    rw [SB.residue_algebraMap]
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using ha
  have haval : v.valuation F aF = 1 :=
    (SB.residue_ne_zero v aF (v.valuation_le_one a)).1 hresAne
  have hresBne : residue v bF ≠ 0 := by
    rw [SB.residue_algebraMap]
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hbval : v.valuation F bF = 1 :=
    (SB.residue_ne_zero v bF (v.valuation_le_one b)).1 hresBne
  have hratioVal : v.valuation F (aF / xF) = 1 := by
    rw [map_div₀, haval, hxval]
    simp
  have hratioMap : algebraMap F (v.adicCompletion F) (aF / xF) =
      algebraMap F (v.adicCompletion F) aF /
        algebraMap F (v.adicCompletion F) xF := by
    rw [map_div₀]
  have huVal : (u : v.adicCompletion F) =
      (t : v.adicCompletion F) / (xLoc : v.adicCompletion F) := by
    rw [huEq, Units.val_div_eq_div_val]
  have hcloseNeg : Valued.v
      (algebraMap F (v.adicCompletion F) aF - (t : v.adicCompletion F)) < 1 := by
    have hneg : algebraMap F (v.adicCompletion F) aF - (t : v.adicCompletion F) =
        -((t : v.adicCompletion F) - algebraMap F (v.adicCompletion F) aF) := by ring
    rw [hneg]
    simpa only [(Valued.v).map_neg] using hcloseT
  have hfracDiff :
      algebraMap F (v.adicCompletion F) (aF / xF) - (u : v.adicCompletion F) =
        (algebraMap F (v.adicCompletion F) aF - (t : v.adicCompletion F)) /
          (xLoc : v.adicCompletion F) := by
    calc
      _ = algebraMap F (v.adicCompletion F) aF /
          algebraMap F (v.adicCompletion F) xF - (t : v.adicCompletion F) /
            (xLoc : v.adicCompletion F) := by rw [hratioMap, huVal]
      _ = algebraMap F (v.adicCompletion F) aF /
          (xLoc : v.adicCompletion F) - (t : v.adicCompletion F) /
            (xLoc : v.adicCompletion F) := by rw [← hxLocMap]
      _ = (algebraMap F (v.adicCompletion F) aF - (t : v.adicCompletion F)) /
            (xLoc : v.adicCompletion F) := by rw [← sub_div]
  have hcloseFrac : Valued.v
      (algebraMap F (v.adicCompletion F) (aF / xF) - (u : v.adicCompletion F)) < 1 := by
    rw [hfracDiff, map_div₀, hxLocVal]
    simpa using hcloseNeg
  have hcloseRatio : Valued.v
      (algebraMap F (v.adicCompletion F) (aF / xF) -
        algebraMap F (v.adicCompletion F) bF) < 1 := by
    have hdecomp :
        algebraMap F (v.adicCompletion F) (aF / xF) -
            algebraMap F (v.adicCompletion F) bF =
          (algebraMap F (v.adicCompletion F) (aF / xF) - (u : v.adicCompletion F)) +
            ((u : v.adicCompletion F) - algebraMap F (v.adicCompletion F) bF) := by
      abel
    rw [hdecomp]
    exact (Valued.v).map_add_lt hcloseFrac hcloseU
  have hcloseField : v.valuation F (aF / xF - bF) < 1 := by
    calc
      v.valuation F (aF / xF - bF) =
          Valued.v (algebraMap F (v.adicCompletion F) (aF / xF - bF)) :=
            (v.valuedAdicCompletion_eq_valuation' (aF / xF - bF)).symm
      _ = Valued.v (algebraMap F (v.adicCompletion F) (aF / xF) -
          algebraMap F (v.adicCompletion F) bF) := by rw [map_sub]
      _ < 1 := hcloseRatio
  have hresRatio : residue v (aF / xF) = residue v bF :=
    SB.residue_congr v (aF / xF) bF (le_of_eq hratioVal) (le_of_eq hbval) hcloseField
  have hprod : residue v ((aF / xF) * xF) =
      residue v (aF / xF) * residue v xF :=
    SB.residue_mul v (aF / xF) xF (le_of_eq hratioVal) (le_of_eq hxval)
  have hprodF : (aF / xF) * xF = aF := by
    exact div_mul_cancel₀ aF hxFne
  calc
    Ideal.Quotient.mk v.asIdeal b * x = residue v bF * residue v xF := by
      rw [SB.residue_algebraMap, hresX]
    _ = residue v (aF / xF) * residue v xF := by rw [← hresRatio]
    _ = residue v ((aF / xF) * xF) := hprod.symm
    _ = residue v aF := by rw [hprodF]

private theorem rf_gauss_sum_norm_sq
    {K : Type*} [Field K] [Fintype K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card K : ℝ) := by
  have hprod : gaussSum χ ψ * star (gaussSum χ ψ) = (Fintype.card K : ℂ) := by
    rw [star_gaussSum_eq χ ψ]
    exact gaussSum_mul_gaussSum_eq_card hχ hψ
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hprod
  simpa [norm_mul, pow_two] using hnorm

private theorem rf_local_mulchar_zpow_eval
    (D : FieldData F) (S : SData F CE condη) (v : FinPlace F)
    (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
    (hχval : ∀ x, χ x = chiPow D v (algebraMap (𝓞 F) F x.out) 1)
    (e : ℤ) (x : 𝓞 F ⧸ v.asIdeal) :
    (χ ^ e) x = chiPow D v (algebraMap (𝓞 F) F x.out) e := by
  classical
  letI := ArtinPrimitiveRoots.A2.bridgeResidueField v
  letI := ArtinPrimitiveRoots.A2.bridgeResidueFintype v
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hres (y : 𝓞 F ⧸ v.asIdeal) :
      residue v (algebraMap (𝓞 F) F y.out) = y := by
    simpa using SB.residue_algebraMap v y.out
  by_cases hx : x = 0
  · subst x
    have hz : residue v
        (algebraMap (𝓞 F) F (0 : 𝓞 F ⧸ v.asIdeal).out) = 0 := by rw [hres]
    rw [MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : 𝓞 F ⧸ v.asIdeal)),
      SB.chiPow_zero v _ e hz]
  · let u : (𝓞 F ⧸ v.asIdeal)ˣ := Units.mk0 x hx
    have hEval : (χ ^ e) (u : 𝓞 F ⧸ v.asIdeal) = (χ u) ^ e := by
      calc
        (χ ^ e) (u : 𝓞 F ⧸ v.asIdeal) = χ (u ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) :=
          MulChar.zpow_apply_coe χ e u
        _ = (χ u) ^ e := by
          change ((χ.toUnitHom (u ^ e) : ℂˣ) : ℂ) =
            ((χ.toUnitHom u : ℂˣ) : ℂ) ^ e
          rw [map_zpow, Units.val_zpow_eq_zpow_val]
    have hresne : residue v (algebraMap (𝓞 F) F x.out) ≠ 0 := by
      rw [hres x]
      exact hx
    calc
      (χ ^ e) x = (χ x) ^ e := by
        change (χ ^ e) (u : 𝓞 F ⧸ v.asIdeal) = (χ u) ^ e
        exact hEval
      _ = (chiPow D v (algebraMap (𝓞 F) F x.out) 1) ^ e := by rw [hχval x]
      _ = chiPow D v (algebraMap (𝓞 F) F x.out) e := by
        rw [SB.chiPow_nonzero v _ 1 hresne, SB.chiPow_nonzero v _ e hresne]
        simp

private theorem rf_local_mulchar_zpow_ne_one
    {K : Type*} [Field K] {χ : MulChar K ℂ} (horder : orderOf χ = 6)
    (e : ℤ) (he : ¬ (6 : ℤ) ∣ e) : χ ^ e ≠ 1 := by
  intro hpow
  have hdiv : (orderOf χ : ℤ) ∣ e := (orderOf_dvd_iff_zpow_eq_one).2 hpow
  rw [horder] at hdiv
  exact he hdiv

private theorem rf_local_positive_alpha_chi_sum
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (v : FinPlace F)
    (p : Fˣ) (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
    (hχval : ∀ x, χ x = chiPow D v (algebraMap (𝓞 F) F x.out) 1)
    (horder : orderOf χ = 6) (j : Fin 6) :
    (∑ᶠ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
      maskAlpha D A v p j x * chi D v (algebraMap (𝓞 F) F x.out) ^ 4) =
    if j = 4 then ((Ideal.absNorm v.asIdeal : ℂ) - 1) / maskTau D A v p 4 else 0 := by
  classical
  letI := ArtinPrimitiveRoots.A2.bridgeResidueField v
  letI := ArtinPrimitiveRoots.A2.bridgeResidueFintype v
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hres (x : 𝓞 F ⧸ v.asIdeal) : residue v (algebraMap (𝓞 F) F x.out) = x := by
    simpa using SB.residue_algebraMap v x.out
  have hcharPower (k : ℤ) (x : 𝓞 F ⧸ v.asIdeal) :
      (χ ^ k) x = chiPow D v (algebraMap (𝓞 F) F x.out) k :=
    rf_local_mulchar_zpow_eval D S v χ hχval k x
  have hchiNonzero (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) :
      chi D v (algebraMap (𝓞 F) F x.out) ≠ 0 := by
    have hresne : residue v (algebraMap (𝓞 F) F x.out) ≠ 0 := by rw [hres]; exact hx
    have h6 := SB.chi_six v (algebraMap (𝓞 F) F x.out) hresne
    intro hz
    rw [hz] at h6
    norm_num at h6
  by_cases hj0 : j = 0
  · subst j
    have h4ne : χ ^ (4 : ℤ) ≠ 1 := by
      apply rf_local_mulchar_zpow_ne_one horder 4
      norm_num
    let q : ℂ := (Ideal.absNorm v.asIdeal : ℂ)
    have hsum0 :
        (∑ x : 𝓞 F ⧸ v.asIdeal,
          if x = 0 then 0 else chi D v (algebraMap (𝓞 F) F x.out) ^ 4) = 0 := by
      calc
        _ = ∑ x : 𝓞 F ⧸ v.asIdeal, (χ ^ (4 : ℤ)) x := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = 0
          · subst x
            simp only [if_pos rfl]
            exact (MulChar.map_nonunit (χ ^ (4 : ℤ))
              (by simp : ¬ IsUnit (0 : 𝓞 F ⧸ v.asIdeal))).symm
          · simp only [if_neg hx]
            have hresne : residue v (algebraMap (𝓞 F) F x.out) ≠ 0 := by rw [hres]; exact hx
            calc
              chi D v (algebraMap (𝓞 F) F x.out) ^ 4 =
                  chiPow D v (algebraMap (𝓞 F) F x.out) 4 :=
                    (SB.chiPow_nonzero v _ 4 hresne).symm
              _ = (χ ^ (4 : ℤ)) x := (hcharPower 4 x).symm
        _ = 0 := MulChar.sum_eq_zero_of_ne_one h4ne
    have hfinsum :
        (∑ᶠ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
          maskAlpha D A v p 0 x * chi D v (algebraMap (𝓞 F) F x.out) ^ 4) =
          ∑ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
            maskAlpha D A v p 0 x * chi D v (algebraMap (𝓞 F) F x.out) ^ 4 :=
      ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v _
    rw [hfinsum]
    have hsum :
        (∑ x : 𝓞 F ⧸ v.asIdeal,
          if x = 0 then 0 else maskAlpha D A v p 0 x *
            chi D v (algebraMap (𝓞 F) F x.out) ^ 4) =
          -(q⁻¹) * ∑ x : 𝓞 F ⧸ v.asIdeal,
            if x = 0 then 0 else chi D v (algebraMap (𝓞 F) F x.out) ^ 4 := by
      calc
        _ = ∑ x : 𝓞 F ⧸ v.asIdeal,
            -(q⁻¹) * (if x = 0 then 0 else chi D v (algebraMap (𝓞 F) F x.out) ^ 4) := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : x = 0 <;> simp [maskAlpha, hx, q]
        _ = _ := by rw [Finset.mul_sum]
    rw [hsum, hsum0]
    simp
  · by_cases hj4 : j = 4
    · subst j
      let f : 𝓞 F ⧸ v.asIdeal → ℂ := fun x =>
        if x = 0 then 0 else maskAlpha D A v p 4 x *
          chi D v (algebraMap (𝓞 F) F x.out) ^ 4
      have hfinsum := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v f
      rw [hfinsum]
      have hone : (∑ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then (0 : ℂ) else 1) =
          (Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ : ℂ) := by
        calc
          _ = ∑ x : 𝓞 F ⧸ v.asIdeal, (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) x := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x = 0
            · subst x
              have hzero : (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) 0 = 0 :=
                MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : 𝓞 F ⧸ v.asIdeal))
              calc
                (if (0 : 𝓞 F ⧸ v.asIdeal) = 0 then (0 : ℂ) else 1) = 0 := by simp
                _ = (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) 0 := hzero.symm
            · let u : (𝓞 F ⧸ v.asIdeal)ˣ := Units.mk0 x hx
              have hOne : (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) (u : 𝓞 F ⧸ v.asIdeal) = 1 :=
                MulChar.one_apply_coe u
              calc
                (if x = 0 then (0 : ℂ) else 1) = 1 := by simp [hx]
                _ = (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) (u : 𝓞 F ⧸ v.asIdeal) := hOne.symm
                _ = (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) x := by rfl
          _ = (Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ : ℂ) := by
            exact_mod_cast (MulChar.sum_one_eq_card_units :
              (∑ x : 𝓞 F ⧸ v.asIdeal, (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) x) =
                Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ)
      have hnormCard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
      have hcardle : 1 ≤ Fintype.card (𝓞 F ⧸ v.asIdeal) :=
        Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (Nat.ne_of_gt Fintype.card_pos))
      have hqcast : (Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ : ℂ) =
          (Ideal.absNorm v.asIdeal : ℂ) - 1 := by
        have hcardunits : Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ =
            Fintype.card (𝓞 F ⧸ v.asIdeal) - 1 := by
          calc
            Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ = Nat.card (𝓞 F ⧸ v.asIdeal)ˣ :=
              (Nat.card_eq_fintype_card (α := (𝓞 F ⧸ v.asIdeal)ˣ)).symm
            _ = Nat.card (𝓞 F ⧸ v.asIdeal) - 1 :=
              Nat.card_units (𝓞 F ⧸ v.asIdeal)
            _ = Fintype.card (𝓞 F ⧸ v.asIdeal) - 1 := by
              rw [Nat.card_eq_fintype_card]
        have hcastCard : (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℂ) =
            (Ideal.absNorm v.asIdeal : ℂ) := by exact_mod_cast hnormCard
        have habsle : 1 ≤ Ideal.absNorm v.asIdeal := by rw [← hnormCard]; exact hcardle
        calc
          (Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ : ℂ) =
              ((Fintype.card (𝓞 F ⧸ v.asIdeal) - 1 : ℕ) : ℂ) := by
                exact_mod_cast hcardunits
          _ = (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℂ) - 1 := by
                rw [Nat.cast_sub hcardle]
                norm_num
          _ = (Ideal.absNorm v.asIdeal : ℂ) - 1 := by rw [hcastCard]

      have hcancel (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) :
          chi D v (algebraMap (𝓞 F) F x.out) ^ (-4 : ℤ) *
            chi D v (algebraMap (𝓞 F) F x.out) ^ 4 = 1 := by
        have hchiNe := hchiNonzero x hx
        rw [show (-4 : ℤ) = -(4 : ℤ) by norm_num, zpow_neg]
        exact inv_mul_cancel₀ (zpow_ne_zero _ hchiNe)
      have hsum : (∑ x : 𝓞 F ⧸ v.asIdeal, f x) =
          (maskTau D A v p 4)⁻¹ * Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ := by
        calc
          _ = ∑ x : 𝓞 F ⧸ v.asIdeal, (maskTau D A v p 4)⁻¹ *
                (if x = 0 then (0 : ℂ) else 1) := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x = 0
            · simp [f, hx]
            · simp only [f, if_neg hx]
              have hα : maskAlpha D A v p 4 x =
                  (maskTau D A v p 4)⁻¹ *
                    chi D v (algebraMap (𝓞 F) F x.out) ^ (-4 : ℤ) := by
                simp [maskAlpha, hx]
              calc
                _ = (maskTau D A v p 4)⁻¹ *
                    (chi D v (algebraMap (𝓞 F) F x.out) ^ (-4 : ℤ) *
                      chi D v (algebraMap (𝓞 F) F x.out) ^ 4) := by rw [hα]; ac_rfl
                _ = (maskTau D A v p 4)⁻¹ * 1 := by rw [hcancel x hx]
          _ = (maskTau D A v p 4)⁻¹ * Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ := by
            calc
              _ = (maskTau D A v p 4)⁻¹ *
                    ∑ x : 𝓞 F ⧸ v.asIdeal, (if x = 0 then (0 : ℂ) else 1) := by
                      rw [← Finset.mul_sum]
              _ = _ := by rw [hone]
      rw [hsum, hqcast]
      simp [div_eq_mul_inv, mul_comm]
    · let k : ℤ := 4 - (j.1 : ℤ)
      have hk : ¬ (6 : ℤ) ∣ k := by
        intro hdiv
        change (6 : ℤ) ∣ 4 - (j.1 : ℤ) at hdiv
        have hjne : j.1 ≠ 0 := by
          intro h
          exact hj0 (Fin.ext h)
        have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hjne
        have hjlt : j.1 < 6 := j.isLt
        have hj4val : j.1 = 4 := by omega
        exact hj4 (Fin.ext hj4val)
      have hknontriv : χ ^ k ≠ 1 := by
        exact rf_local_mulchar_zpow_ne_one horder k hk
      have hpowMul : χ ^ (-(j.1 : ℤ)) * χ ^ (4 : ℤ) = χ ^ k := by
        dsimp [k]
        rw [← zpow_add]
        congr 1 <;> ring
      let f : 𝓞 F ⧸ v.asIdeal → ℂ := fun x =>
        if x = 0 then 0 else maskAlpha D A v p j x *
          chi D v (algebraMap (𝓞 F) F x.out) ^ 4
      have hfinsum := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v f
      rw [hfinsum]
      have hsum : (∑ x : 𝓞 F ⧸ v.asIdeal, f x) =
          (maskTau D A v p j)⁻¹ * ∑ x : 𝓞 F ⧸ v.asIdeal, (χ ^ k) x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = 0
        · have hzero : (χ ^ k) (0 : 𝓞 F ⧸ v.asIdeal) = 0 :=
            MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : 𝓞 F ⧸ v.asIdeal))
          simp [f, hx, hzero]
        · have hresne : residue v (algebraMap (𝓞 F) F x.out) ≠ 0 := by rw [hres]; exact hx
          have hglobalPow (m : ℤ) :
              chi D v (algebraMap (𝓞 F) F x.out) ^ m = (χ ^ m) x := by
            calc
              _ = chiPow D v (algebraMap (𝓞 F) F x.out) m :=
                (SB.chiPow_nonzero v _ m hresne).symm
              _ = (χ ^ m) x := (hcharPower m x).symm
          have hglobalPow4 :
              chi D v (algebraMap (𝓞 F) F x.out) ^ (4 : ℕ) =
                (χ ^ (4 : ℤ)) x := by
            calc
              _ = chi D v (algebraMap (𝓞 F) F x.out) ^ (4 : ℤ) :=
                (zpow_natCast (chi D v (algebraMap (𝓞 F) F x.out)) 4).symm
              _ = (χ ^ (4 : ℤ)) x := hglobalPow 4
          have hcoeff :
              chi D v (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) *
                chi D v (algebraMap (𝓞 F) F x.out) ^ 4 = (χ ^ k) x := by
            calc
              _ = (χ ^ (-(j.1 : ℤ))) x * (χ ^ (4 : ℤ)) x := by
                rw [hglobalPow (-(j.1 : ℤ)), hglobalPow4]
              _ = ((χ ^ (-(j.1 : ℤ))) * χ ^ (4 : ℤ)) x := by rfl
              _ = (χ ^ k) x := by rw [hpowMul]
          simp only [f, if_neg hx]
          have hα : maskAlpha D A v p j x =
              (maskTau D A v p j)⁻¹ * chi D v (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) := by
            simp [maskAlpha, hj0, hx]
          calc
            _ = (maskTau D A v p j)⁻¹ *
                (chi D v (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) *
                  chi D v (algebraMap (𝓞 F) F x.out) ^ 4) := by rw [hα]; ac_rfl
            _ = (maskTau D A v p j)⁻¹ * (χ ^ k) x := by rw [hcoeff]
      rw [hsum]
      have hsumChar : (∑ x : 𝓞 F ⧸ v.asIdeal, (χ ^ k) x) = 0 :=
        MulChar.sum_eq_zero_of_ne_one hknontriv
      rw [hsumChar]
      simp [hj4]

private theorem rf_local_maskTau_gaussSum
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (v : FinPlace F) (p : Fˣ) (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
    (ψ : AddChar (𝓞 F ⧸ v.asIdeal) ℂ)
    (hχval : ∀ x, χ x = chiPow D v (algebraMap (𝓞 F) F x.out) 1)
    (hψval : ∀ t x, ψ (t * x) = A.ψ v (algebraMap F _
      (algebraMap (𝓞 F) F x.out * algebraMap (𝓞 F) F t.out / (p : F))))
    (j : Fin 6) :
    letI := ArtinPrimitiveRoots.A2.bridgeResidueField v
    letI := ArtinPrimitiveRoots.A2.bridgeResidueFintype v
    maskTau D A v p j = gaussSum (χ ^ (-(j.1 : ℤ))) ψ := by
  classical
  letI := ArtinPrimitiveRoots.A2.bridgeResidueField v
  letI := ArtinPrimitiveRoots.A2.bridgeResidueFintype v
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hres (x : 𝓞 F ⧸ v.asIdeal) : residue v (algebraMap (𝓞 F) F x.out) = x := by
    simpa using SB.residue_algebraMap v x.out
  have hphase (t x : 𝓞 F ⧸ v.asIdeal) :
      maskPhase A v p t x = ψ (t * x) := by
    unfold maskPhase
    exact (hψval t x).symm
  have hfinsum := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v
    (fun x : 𝓞 F ⧸ v.asIdeal => if x = 0 then 0 else
      chi D v (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) *
        maskPhase A v p 1 x)
  unfold maskTau
  rw [hfinsum]
  change (∑ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
      chi D v (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) * maskPhase A v p 1 x) =
    ∑ x : 𝓞 F ⧸ v.asIdeal, (χ ^ (-(j.1 : ℤ))) x * ψ x
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = 0
  · subst x
    have hchiZero : (χ ^ (-(j.1 : ℤ))) (0 : 𝓞 F ⧸ v.asIdeal) = 0 :=
      MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : 𝓞 F ⧸ v.asIdeal))
    calc
      (if (0 : 𝓞 F ⧸ v.asIdeal) = 0 then 0 else
          chi D v (algebraMap (𝓞 F) F (Quotient.out 0)) ^ (-(j.1 : ℤ)) *
            maskPhase A v p 1 0) = 0 := by simp
      _ = (χ ^ (-(j.1 : ℤ))) 0 * ψ 0 := by
        rw [hchiZero]
        simp
  · have hresne : residue v (algebraMap (𝓞 F) F x.out) ≠ 0 := by rw [hres]; exact hx
    have hcoeff : chi D v (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) =
        (χ ^ (-(j.1 : ℤ))) x := by
      calc
        _ = chiPow D v (algebraMap (𝓞 F) F x.out) (-(j.1 : ℤ)) :=
          (SB.chiPow_nonzero v _ _ hresne).symm
        _ = (χ ^ (-(j.1 : ℤ))) x :=
          (rf_local_mulchar_zpow_eval D S v χ hχval (-(j.1 : ℤ)) x).symm
    simp only [if_neg hx]
    rw [hcoeff, hphase]
    simp

private theorem rf_gauss_sum_norm
    {K : Type*} [Field K] [Fintype K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card K : ℝ) := by
  have hsq := rf_gauss_sum_norm_sq χ ψ hχ hψ
  have hqpos : 0 < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsqrtpos : 0 < Real.sqrt (Fintype.card K : ℝ) := Real.sqrt_pos.2 hqpos
  have hsqrtsq : (Real.sqrt (Fintype.card K : ℝ)) ^ 2 =
      (Fintype.card K : ℝ) := Real.sq_sqrt hqpos.le
  have hsumpos : 0 < ‖gaussSum χ ψ‖ + Real.sqrt (Fintype.card K : ℝ) :=
    add_pos_of_nonneg_of_pos (norm_nonneg _) hsqrtpos
  have hprod :
      (‖gaussSum χ ψ‖ - Real.sqrt (Fintype.card K : ℝ)) *
        (‖gaussSum χ ψ‖ + Real.sqrt (Fintype.card K : ℝ)) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with hdiff | hsum
  · linarith
  · exact (False.elim (ne_of_gt hsumpos hsum))

private def rf_localResidueInversion
    {K : Type*} [Field K] (a x : K) : K :=
  if hx : x = 0 then 0 else a / x

private theorem rf_localResidueInversion_involutive
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    Function.Involutive (rf_localResidueInversion a) := by
  classical
  intro x
  by_cases hx : x = 0
  · simp [rf_localResidueInversion, hx]
  · have hphi : rf_localResidueInversion a x = a / x := by
      simp [rf_localResidueInversion, hx]
    have hyne : a / x ≠ 0 := div_ne_zero ha hx
    have houter : rf_localResidueInversion a (a / x) = a / (a / x) := by
      change (if h : a / x = 0 then 0 else a / (a / x)) = a / (a / x)
      exact if_neg hyne
    calc
      rf_localResidueInversion a (rf_localResidueInversion a x) =
          rf_localResidueInversion a (a / x) := congrArg (rf_localResidueInversion a) hphi
      _ = a / (a / x) := houter
      _ = x := by field_simp [ha, hx]

private theorem rf_localResidueInversion_of_mul_eq
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0)
    (x : K) (hx : x ≠ 0) (y : K) (hy : y ≠ 0)
    (hxy : y * x = a) :
    y = rf_localResidueInversion a x := by
  have hphi : rf_localResidueInversion a x = a / x := by
    change (if h : x = 0 then 0 else a / x) = a / x
    exact if_neg hx
  rw [hphi]
  apply (eq_div_iff hx).2
  exact hxy

private theorem rf_localOmega_numerator_maskTau
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F)
    (hv : v ∉ S.Sf) (ψ : AddChar (𝓞 F ⧸ v.asIdeal) ℂ)
    (hψval : ∀ a b, ψ (a * b) = A.ψ v (algebraMap F _
      (algebraMap (𝓞 F) F b.out * algebraMap (𝓞 F) F a.out /
        (primeGen R v : F)))) :
    (∑ᶠ x : 𝓞 F ⧸ v.asIdeal, chiPow D v
      (algebraMap (𝓞 F) F x.out) 3 *
        A.ψ v (algebraMap F _
          (algebraMap (𝓞 F) F x.out / (primeGen R v : F)))) =
      maskTau D A v (primeGen R v) 3 := by
  classical
  letI := ArtinPrimitiveRoots.A2.bridgeResidueField v
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hres (x : 𝓞 F ⧸ v.asIdeal) : residue v
      (algebraMap (𝓞 F) F x.out) = x := by
    simpa using SB.residue_algebraMap v x.out
  have hpoint (x : 𝓞 F ⧸ v.asIdeal) :
      chiPow D v (algebraMap (𝓞 F) F x.out) 3 *
          A.ψ v (algebraMap F _
            (algebraMap (𝓞 F) F x.out / (primeGen R v : F))) =
        if x = 0 then 0 else
          chi D v (algebraMap (𝓞 F) F x.out) ^ (-(3 : ℤ)) *
            maskPhase A v (primeGen R v) 1 x := by
    by_cases hx : x = 0
    · subst x
      have hres0 : residue v
          (algebraMap (𝓞 F) F (0 : 𝓞 F ⧸ v.asIdeal).out) = 0 := by
        rw [SB.residue_algebraMap]
        simp
      have hχ0 := SB.chiPow_zero v _ 3 hres0
      simp [hχ0]
    · have hxrep : x.out ∉ v.asIdeal := rf_local_residue_not_mem D S v x hx
      have hresne : residue v (algebraMap (𝓞 F) F x.out) ≠ 0 := by
        rw [hres x]
        exact hx
      have hχ6 := SB.chi_six v (algebraMap (𝓞 F) F x.out) hresne
      have hχne : chi D v (algebraMap (𝓞 F) F x.out) ≠ 0 := by
        intro hzero
        rw [hzero] at hχ6
        norm_num at hχ6
      have hχ6z : chi D v (algebraMap (𝓞 F) F x.out) ^ (6 : ℤ) = 1 := by
        simpa using hχ6
      have hchiPow3 : chiPow D v (algebraMap (𝓞 F) F x.out) 3 =
          chi D v (algebraMap (𝓞 F) F x.out) ^ (-(3 : ℤ)) := by
        rw [SB.chiPow_nonzero v _ (3 : ℤ) hresne]
        calc
          chi D v (algebraMap (𝓞 F) F x.out) ^ (3 : ℤ) =
              chi D v (algebraMap (𝓞 F) F x.out) ^ ((-3 : ℤ) + 6) := by
                congr 1 <;> norm_num
          _ = chi D v (algebraMap (𝓞 F) F x.out) ^ (-3 : ℤ) *
              chi D v (algebraMap (𝓞 F) F x.out) ^ (6 : ℤ) :=
                zpow_add₀ hχne _ _
          _ = _ := by rw [hχ6z]; simp
      have hphase : A.ψ v (algebraMap F _
          (algebraMap (𝓞 F) F x.out / (primeGen R v : F))) = ψ x := by
        have hmk : Ideal.Quotient.mk v.asIdeal x.out = x := by
          calc
            Ideal.Quotient.mk v.asIdeal x.out = residue v
                (algebraMap (𝓞 F) F x.out) := (SB.residue_algebraMap v x.out).symm
            _ = x := hres x
        simpa [hmk] using
          (rf_local_addchar_out_phase R v hv ψ hψval x.out hxrep).symm
      have hmask : maskPhase A v (primeGen R v) 1 x = ψ x := by
        unfold maskPhase
        simpa using (hψval 1 x).symm
      simp only [if_neg hx]
      rw [hphase, hmask, hchiPow3]
  calc
    (∑ᶠ x : 𝓞 F ⧸ v.asIdeal, chiPow D v
        (algebraMap (𝓞 F) F x.out) 3 *
          A.ψ v (algebraMap F _
            (algebraMap (𝓞 F) F x.out / (primeGen R v : F)))) =
        ∑ᶠ x : 𝓞 F ⧸ v.asIdeal,
          if x = 0 then 0 else
            chi D v (algebraMap (𝓞 F) F x.out) ^ (-(3 : ℤ)) *
              maskPhase A v (primeGen R v) 1 x :=
          finsum_congr hpoint
    _ = maskTau D A v (primeGen R v) 3 := by
      unfold maskTau
      rfl

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
  classical
  intro v hv j e t ht htinv
  letI := ArtinPrimitiveRoots.A2.bridgeResidueField v
  letI := ArtinPrimitiveRoots.A2.bridgeResidueFintype v
  have htLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v t := ⟨ht, htinv⟩
  have hOneLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v (1 : (v.adicCompletion F)ˣ) := by
    constructor <;> simp [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hpgen : S.IsGen (primeGen R v : F) v.asIdeal := by
    simpa [primeGen, hv, R.exterior.prime_val] using
      (bc.gen_spec (R.exterior.prime v hv)).1
  obtain ⟨_, ⟨χ, hχorder, hχval⟩, ⟨ψ, hψprim, hψval⟩⟩ :=
    ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR D S A v hv (primeGen R v) hpgen
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hlocalChiNorm : ‖localChi D v t‖ = 1 := SB.localChi_norm v hv t htLoc
  have htau (j' : Fin 6) :
      maskTau D A v (primeGen R v) j' = gaussSum (χ ^ (-(j'.1 : ℤ))) ψ :=
    rf_local_maskTau_gaussSum D S A v (primeGen R v) χ ψ hχval hψval j'
  have hnormCard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hphaseSum (he : 0 < e) (u : (v.adicCompletion F)ˣ)
      (hu : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v u) :
      (∑ᶠ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
        maskAlpha D A v (primeGen R v) j x * chi D v
          (algebraMap (𝓞 F) F x.out) ^ 4 *
          A.ψ v (((toLoc v (primeGen R v) ^ (e - 1) * u :
            (v.adicCompletion F)ˣ) : _) /
              algebraMap F _ (algebraMap (𝓞 F) F x.out))) =
      ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
        maskAlpha D A v (primeGen R v) j x * chi D v
          (algebraMap (𝓞 F) F x.out) ^ 4 := by
    let f : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x => if x = 0 then 0 else
      maskAlpha D A v (primeGen R v) j x * chi D v
        (algebraMap (𝓞 F) F x.out) ^ 4 *
        A.ψ v (((toLoc v (primeGen R v) ^ (e - 1) * u :
          (v.adicCompletion F)ˣ) : _) /
            algebraMap F _ (algebraMap (𝓞 F) F x.out))
    let g : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x => if x = 0 then 0 else
      maskAlpha D A v (primeGen R v) j x * chi D v
        (algebraMap (𝓞 F) F x.out) ^ 4
    have hf := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v f
    have hg := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v g
    calc
      (∑ᶠ x, f x) = ∑ x, f x := hf
      _ = ∑ x, g x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = 0
        · simp [f, g, hx]
        · simp only [f, g, if_neg hx]
          rw [rf_localWeyl_positive_phase R v hv e he u hu x hx]
          simp
      _ = ∑ᶠ x, g x := hg.symm
  have hv6 : (6 : 𝓞 F) ∉ v.asIdeal := by
    intro h6
    exact hv (S.over6 v h6)
  obtain ⟨a, ha, hcloseT⟩ := rf_localChi_has_approximant D v hv6 t htLoc
  let aF : F := algebraMap (𝓞 F) F a
  let τ : 𝓞 F ⧸ v.asIdeal := residue v aF
  have hτeq : τ = Ideal.Quotient.mk v.asIdeal a := by
    simpa [τ, aF] using SB.residue_algebraMap v a
  have hτne : τ ≠ 0 := by
    intro hzero
    apply ha
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (hτeq.symm.trans hzero)
  have hlocalChiA : localChi D v t = chi D v aF :=
    SB.localChi_approximant v hv t htLoc a ha hcloseT
  have hresτ (x : 𝓞 F ⧸ v.asIdeal) : residue v
      (algebraMap (𝓞 F) F x.out) = x := by
    simpa using SB.residue_algebraMap v x.out
  have hchiTau : χ τ = localChi D v t := by
    have hresTauNe : residue v (algebraMap (𝓞 F) F τ.out) ≠ 0 := by
      rw [hresτ]
      exact hτne
    have hresSame : residue v (algebraMap (𝓞 F) F τ.out) = residue v aF := by
      rw [hresτ]
    calc
      χ τ = chiPow D v (algebraMap (𝓞 F) F τ.out) 1 := hχval τ
      _ = chi D v (algebraMap (𝓞 F) F τ.out) := by
        rw [SB.chiPow_nonzero v _ 1 hresTauNe]
        simp
      _ = chi D v aF := SB.chi_congr v _ _ hresSame
      _ = localChi D v t := hlocalChiA.symm
  have hlocalChiSix : localChi D v t ^ (6 : ℕ) = 1 :=
    SB.localChi_six v hv t htLoc
  let phi : (𝓞 F ⧸ v.asIdeal) → (𝓞 F ⧸ v.asIdeal) :=
    rf_localResidueInversion τ
  have hphiInvol : Function.Involutive phi := rf_localResidueInversion_involutive τ hτne
  have hphiBij : Function.Bijective phi := hphiInvol.bijective
  have hphi0 : phi 0 = 0 := by
    change (if h : (0 : 𝓞 F ⧸ v.asIdeal) = 0 then 0 else τ / 0) = 0
    exact if_pos (show (0 : 𝓞 F ⧸ v.asIdeal) = 0 by rfl)
  have hphiProduct (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) : phi x * x = τ := by
    have hphiX : phi x = τ / x := by
      change (if h : x = 0 then 0 else τ / x) = τ / x
      exact if_neg hx
    rw [hphiX]
    exact div_mul_cancel₀ τ hx
  have hchiEval (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) :
      chi D v (algebraMap (𝓞 F) F x.out) = χ x := by
    have hresne : residue v (algebraMap (𝓞 F) F x.out) ≠ 0 := by
      rw [hresτ x]
      exact hx
    calc
      chi D v (algebraMap (𝓞 F) F x.out) =
          chiPow D v (algebraMap (𝓞 F) F x.out) 1 := by
            rw [SB.chiPow_nonzero v _ 1 hresne]
            simp
      _ = (χ ^ (1 : ℤ)) x :=
        (rf_local_mulchar_zpow_eval D S v χ hχval (1 : ℤ) x).symm
      _ = χ x := by simp
  have hchiMinus3 (y : 𝓞 F ⧸ v.asIdeal) (hy : y ≠ 0) :
      (χ y) ^ (-(3 : ℤ)) = (χ ^ (-(3 : ℤ))) y := by
    have hyresne : residue v (algebraMap (𝓞 F) F y.out) ≠ 0 := by
      rw [hresτ y]
      exact hy
    calc
      (χ y) ^ (-(3 : ℤ)) =
          chi D v (algebraMap (𝓞 F) F y.out) ^ (-(3 : ℤ)) := by rw [hchiEval y hy]
      _ = chiPow D v (algebraMap (𝓞 F) F y.out) (-(3 : ℤ)) :=
        (SB.chiPow_nonzero v _ _ hyresne).symm
      _ = (χ ^ (-(3 : ℤ))) y :=
        (rf_local_mulchar_zpow_eval D S v χ hχval (-(3 : ℤ)) y).symm
  have hphaseZero (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) :
      A.ψ v ((((toLoc v (primeGen R v))⁻¹ * t : (v.adicCompletion F)ˣ) : _) /
        algebraMap F _ (algebraMap (𝓞 F) F x.out)) = ψ (phi x) := by
    have hxrep : x.out ∉ v.asIdeal := rf_local_residue_not_mem D S v x hx
    let xF : F := algebraMap (𝓞 F) F x.out
    have hxFne : xF ≠ 0 := by
      intro hzero
      have hxval : v.valuation F xF = 1 := rf_local_residue_val_one D S v x hx
      rw [hzero] at hxval
      norm_num at hxval
    let xu : Fˣ := Units.mk0 xF hxFne
    let xLoc : (v.adicCompletion F)ˣ := toLoc v xu
    have hxLocMap : (xLoc : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) xF := by
      change algebraMap F (v.adicCompletion F) (xu : F) = _
      simp [xu]
    have hxLocVal : Valued.v (xLoc : v.adicCompletion F) = 1 := by
      calc
        Valued.v (xLoc : v.adicCompletion F) =
            Valued.v (algebraMap F (v.adicCompletion F) xF) := by rw [hxLocMap]
        _ = v.valuation F xF := v.valuedAdicCompletion_eq_valuation' xF
        _ = 1 := rf_local_residue_val_one D S v x hx
    have hxLocUnit : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v xLoc := by
      constructor
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hxLocVal]
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        have hinv : Valued.v
            (((xLoc⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) = 1 := by
          simp [Units.val_inv_eq_inv_val, hxLocVal]
        rw [hinv]
    let u : (v.adicCompletion F)ˣ := t / xLoc
    have huLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v u := by
      change u ∈ rf_localUnitSubgroup v
      exact Subgroup.div_mem _ htLoc hxLocUnit
    obtain ⟨b, hb, hcloseU⟩ := rf_localChi_has_approximant D v hv6 u huLoc
    have hresProduct := rf_local_residue_t_mul_digit R v hv x hx xF rfl
      xLoc hxLocMap hxLocVal t u rfl a ha hcloseT b hb hcloseU
    have hbQne : (Ideal.Quotient.mk v.asIdeal b : 𝓞 F ⧸ v.asIdeal) ≠ 0 := by
      simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
    have hphiEq := rf_localResidueInversion_of_mul_eq τ hτne x hx
      (Ideal.Quotient.mk v.asIdeal b) hbQne hresProduct
    calc
      A.ψ v ((((toLoc v (primeGen R v))⁻¹ * t : (v.adicCompletion F)ˣ) : _) /
          algebraMap F _ (algebraMap (𝓞 F) F x.out)) =
          A.ψ v ((((toLoc v (primeGen R v))⁻¹ * t : (v.adicCompletion F)ˣ) : _) /
            algebraMap F _ xF) := by rfl
      _ = ψ (Ideal.Quotient.mk v.asIdeal b) :=
        rf_local_inverse_phase_residue R v hv xF xLoc hxLocMap t u rfl b hb hcloseU
          ψ hψval
      _ = ψ (phi x) := by rw [hphiEq]
  have hphaseOne (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) :
      A.ψ v ((((toLoc v (primeGen R v))⁻¹ * (1 : (v.adicCompletion F)ˣ) :
        (v.adicCompletion F)ˣ) : _) /
          algebraMap F _ (algebraMap (𝓞 F) F x.out)) = ψ (x⁻¹) := by
    have hxrep : x.out ∉ v.asIdeal := rf_local_residue_not_mem D S v x hx
    let xF : F := algebraMap (𝓞 F) F x.out
    have hxFne : xF ≠ 0 := by
      intro hzero
      have hxval : v.valuation F xF = 1 := rf_local_residue_val_one D S v x hx
      rw [hzero] at hxval
      norm_num at hxval
    let xu : Fˣ := Units.mk0 xF hxFne
    let xLoc : (v.adicCompletion F)ˣ := toLoc v xu
    have hxLocMap : (xLoc : v.adicCompletion F) = algebraMap F _ xF := by
      change algebraMap F (v.adicCompletion F) (xu : F) = _
      simp [xu]
    have hxLocVal : Valued.v (xLoc : v.adicCompletion F) = 1 := by
      calc
        Valued.v (xLoc : v.adicCompletion F) =
            Valued.v (algebraMap F (v.adicCompletion F) xF) := by rw [hxLocMap]
        _ = v.valuation F xF := v.valuedAdicCompletion_eq_valuation' xF
        _ = 1 := rf_local_residue_val_one D S v x hx
    have hxLocUnit : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v xLoc := by
      constructor
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hxLocVal]
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        have hinv : Valued.v
            (((xLoc⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) = 1 := by
          simp [Units.val_inv_eq_inv_val, hxLocVal]
        rw [hinv]
    let u : (v.adicCompletion F)ˣ := (1 : (v.adicCompletion F)ˣ) / xLoc
    have huLoc : ArtinPrimitiveRoots.A1.Theta.IsLocUnit v u := by
      change u ∈ rf_localUnitSubgroup v
      exact Subgroup.div_mem _ hOneLoc hxLocUnit
    obtain ⟨b, hb, hcloseU⟩ := rf_localChi_has_approximant D v hv6 u huLoc
    have h1not : (1 : 𝓞 F) ∉ v.asIdeal := by
      intro hmem
      exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem v.asIdeal hmem isUnit_one)
    have hcloseOne : Valued.v
        ((1 : v.adicCompletion F) - algebraMap F _ (algebraMap (𝓞 F) F 1)) < 1 := by
      simp
    have hresProduct := rf_local_residue_t_mul_digit R v hv x hx xF rfl
      xLoc hxLocMap hxLocVal 1 u rfl 1 h1not hcloseOne b hb hcloseU
    have hresOne : residue v (algebraMap (𝓞 F) F (1 : 𝓞 F)) = 1 := by
      simpa using SB.residue_algebraMap v (1 : 𝓞 F)
    have hresB : Ideal.Quotient.mk v.asIdeal b * x = 1 := by
      rw [hresOne] at hresProduct
      exact hresProduct
    have hBInv : Ideal.Quotient.mk v.asIdeal b = x⁻¹ := by
      exact (mul_eq_one_iff_eq_inv₀ hx).1 hresB
    calc
      A.ψ v ((((toLoc v (primeGen R v))⁻¹ * (1 : (v.adicCompletion F)ˣ) :
          (v.adicCompletion F)ˣ) : _) /
            algebraMap F _ (algebraMap (𝓞 F) F x.out)) =
          ψ (Ideal.Quotient.mk v.asIdeal b) := by
            simpa [xF, u] using
              (rf_local_inverse_phase_residue R v hv xF xLoc hxLocMap 1 u rfl
                b hb hcloseU ψ hψval)
      _ = ψ (x⁻¹) := by rw [hBInv]
  have hphiScale (y : 𝓞 F ⧸ v.asIdeal) (hy : y ≠ 0) :
      phi (τ * y) = y⁻¹ := by
    have hxy : τ * y ≠ 0 := mul_ne_zero hτne hy
    have hprod := hphiProduct (τ * y) hxy
    have hprod' : (phi (τ * y) * y) * τ = 1 * τ := by
      calc
        (phi (τ * y) * y) * τ = phi (τ * y) * (y * τ) := by ac_rfl
        _ = phi (τ * y) * (τ * y) := by rw [mul_comm y τ]
        _ = τ := hprod
        _ = 1 * τ := by simp
    have hmul : phi (τ * y) * y = 1 := mul_right_cancel₀ hτne hprod'
    exact (mul_eq_one_iff_eq_inv₀ hy).1 hmul
  have hpSpec : S.IsGen (primeGen R v : F) v.asIdeal ∧ Bd.Allowed (primeGen R v) := by
    have h := bc.gen_spec (R.exterior.prime v hv)
    simpa [primeGen, hv, R.exterior.prime_val] using h
  have hmaskFourierOne (k : Fin 6) :
      (∑ᶠ x : 𝓞 F ⧸ v.asIdeal,
        maskAlpha D A v (primeGen R v) k x * maskPhase A v (primeGen R v) 1 x) = 1 := by
    have h := ArtinPrimitiveRoots.A2.rf_mask_identity D S H Bd A v hv
      (primeGen R v) hpSpec k (1 : 𝓞 F ⧸ v.asIdeal)
    have hresOne : residue v (algebraMap (𝓞 F) F
        (1 : 𝓞 F ⧸ v.asIdeal).out) = 1 := hresτ 1
    have hresOneNe : residue v (algebraMap (𝓞 F) F
        (1 : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by rw [hresOne]; norm_num
    have hχone : χ (1 : 𝓞 F ⧸ v.asIdeal) = 1 := MulChar.map_one χ
    have hχpowone : chiPow D v
        (algebraMap (𝓞 F) F (1 : 𝓞 F ⧸ v.asIdeal).out) 1 = 1 :=
      (hχval 1).symm.trans hχone
    have hchiRepOne : chi D v
        (algebraMap (𝓞 F) F (1 : 𝓞 F ⧸ v.asIdeal).out) = 1 := by
      calc
        _ = chiPow D v
            (algebraMap (𝓞 F) F (1 : 𝓞 F ⧸ v.asIdeal).out) 1 := by
              rw [SB.chiPow_nonzero v _ 1 hresOneNe]
              simp
        _ = 1 := hχpowone
    have hχpow : chiPow D v
        (algebraMap (𝓞 F) F (1 : 𝓞 F ⧸ v.asIdeal).out) (k.1 : ℤ) = 1 := by
      calc
        _ = chi D v (algebraMap (𝓞 F) F (1 : 𝓞 F ⧸ v.asIdeal).out) ^ (k.1 : ℤ) :=
          SB.chiPow_nonzero v _ _ hresOneNe
        _ = 1 := by rw [hchiRepOne]; simp
    rw [hχpow] at h
    simpa using h
  have hOmegaRatio : localOmega R v =
      maskTau D A v (primeGen R v) 3 / maskTau D A v (primeGen R v) 1 := by
    unfold localOmega
    rw [rf_localOmega_numerator_maskTau R v hv ψ hψval]
  have hchiZpowEval (n : ℤ) (y : 𝓞 F ⧸ v.asIdeal) (hy : y ≠ 0) :
      (χ ^ n) y = (χ y) ^ n := by
    have hyresne : residue v (algebraMap (𝓞 F) F y.out) ≠ 0 := by
      rw [hresτ y]
      exact hy
    calc
      (χ ^ n) y = chiPow D v (algebraMap (𝓞 F) F y.out) n :=
        rf_local_mulchar_zpow_eval D S v χ hχval n y
      _ = chi D v (algebraMap (𝓞 F) F y.out) ^ n :=
        SB.chiPow_nonzero v _ n hyresne
      _ = (χ y) ^ n := by rw [hchiEval y hy]
  have hchiQuot (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0)
      (hy : phi x ≠ 0) : χ x = localChi D v t / χ (phi x) := by
    have hprodχ : χ (phi x) * χ x = χ τ := by
      calc
        χ (phi x) * χ x = χ (phi x * x) := (map_mul χ (phi x) x).symm
        _ = χ τ := by rw [hphiProduct x hx]
    have hyχne : χ (phi x) ≠ 0 :=
      (MulChar.apply_ne_zero_iff).2 (isUnit_iff_ne_zero.mpr hy)
    rw [eq_div_iff hyχne]
    calc
      χ x * χ (phi x) = χ (phi x) * χ x := by ring
      _ = χ τ := hprodχ
      _ = localChi D v t := hchiTau
  have hchiOrbitPow (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0)
      (hy : phi x ≠ 0) (n : ℤ) :
      (χ x) ^ n = localChi D v t ^ n * (χ (phi x)) ^ (-n) := by
    rw [hchiQuot x hx hy, div_zpow, div_eq_mul_inv, zpow_neg]
  have hchiOrbitPowNorm (n : ℤ) : ‖localChi D v t ^ n‖ = 1 := by
    rw [norm_zpow, hlocalChiNorm]
    simp
  have hmaskedGauss (n : ℤ) :
      (∑ y : 𝓞 F ⧸ v.asIdeal, if y = 0 then 0 else (χ ^ n) y * ψ y) =
        gaussSum (χ ^ n) ψ := by
    classical
    rw [gaussSum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y = 0
    · subst y
      simp only [if_pos rfl]
      have hzero : (χ ^ n) (0 : 𝓞 F ⧸ v.asIdeal) = 0 :=
        MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : 𝓞 F ⧸ v.asIdeal))
      rw [hzero]
      simp
    · simp [hy]
  have hψne : ψ ≠ 1 := by
    intro h
    apply hψprim (a := (1 : 𝓞 F ⧸ v.asIdeal)) one_ne_zero
    simpa [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    rw [rf_localR_formula R v hv j e t htLoc]
    rw [rf_localW_zero_of_negative R v hv e he]
    simp
  · intro he
    exact rf_localR_formula R v hv j e t htLoc
  · intro hj1 he
    subst j
    rw [rf_localR_formula R v hv 1 e t htLoc, hphaseSum he t htLoc]
    rw [rf_local_positive_alpha_chi_sum D S A v (primeGen R v) χ hχval hχorder 1]
    norm_num
  · intro hj1 he0
    subst j
    subst e
    have hW0 : localW R v 0 = 1 := by
      rw [rf_localW_table R v hv 0]
      simp [sphericalTable]
    let c : ℂ := (maskTau D A v (primeGen R v) 1)⁻¹ *
      localChi D v t ^ (3 : ℕ)
    let f : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x => if x = 0 then 0 else
      maskAlpha D A v (primeGen R v) 1 x *
        chi D v (algebraMap (𝓞 F) F x.out) ^ 4 * ψ (phi x)
    let fψ : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x => if x = 0 then 0 else
      maskAlpha D A v (primeGen R v) 1 x *
        chi D v (algebraMap (𝓞 F) F x.out) ^ 4 *
          A.ψ v (((toLoc v (primeGen R v) ^ ((0 : ℤ) - 1) * t :
            (v.adicCompletion F)ˣ) : _) /
              algebraMap F _ (algebraMap (𝓞 F) F x.out))
    have hfψ := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v fψ
    have hf := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v f
    have hphaseFinsum : (∑ᶠ x, fψ x) = ∑ᶠ x, f x := by
      calc
        (∑ᶠ x, fψ x) = ∑ x, fψ x := hfψ
        _ = ∑ x, f x := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = 0
          · simp [fψ, f, hx]
          · simp only [fψ, f, if_neg hx]
            have hphase := hphaseZero x hx
            have hphase' : A.ψ v (((toLoc v (primeGen R v) ^
                ((0 : ℤ) - 1) * t : (v.adicCompletion F)ˣ) : _) /
                  algebraMap F _ (algebraMap (𝓞 F) F x.out)) = ψ (phi x) := by
              simpa using hphase
            rw [hphase']
        _ = ∑ᶠ x, f x := hf.symm
    have hcoef (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) :
        maskAlpha D A v (primeGen R v) 1 x *
          chi D v (algebraMap (𝓞 F) F x.out) ^ 4 =
        c * ((χ ^ (-(3 : ℤ))) (phi x)) := by
      have hy : phi x ≠ 0 := by
        intro hzero
        have hEq : phi x = phi 0 := by rw [hzero, hphi0]
        exact hx (hphiBij.1 hEq)
      have hxchi := hchiEval x hx
      have hychi := hchiEval (phi x) hy
      have hprodχ : χ (phi x) * χ x = χ τ := by
        calc
          χ (phi x) * χ x = χ (phi x * x) := (map_mul χ (phi x) x).symm
          _ = χ τ := by rw [hphiProduct x hx]
      have hyχne : χ (phi x) ≠ 0 :=
        (MulChar.apply_ne_zero_iff).2 (isUnit_iff_ne_zero.mpr hy)
      have hxχne : χ x ≠ 0 :=
        (MulChar.apply_ne_zero_iff).2 (isUnit_iff_ne_zero.mpr hx)
      have hquotχ : χ x = localChi D v t / χ (phi x) := by
        rw [eq_div_iff hyχne]
        calc
          χ x * χ (phi x) = χ (phi x) * χ x := by ring
          _ = χ τ := hprodχ
          _ = localChi D v t := hchiTau
      have hpowχ : (χ x) ^ (3 : ℤ) =
          localChi D v t ^ (3 : ℤ) * χ (phi x) ^ (-(3 : ℤ)) := by
        rw [hquotχ]
        field_simp [hyχne]
      have hchiYpow : (χ ^ (-(3 : ℤ))) (phi x) =
          (χ (phi x)) ^ (-(3 : ℤ)) := by
        have hyresne : residue v
            (algebraMap (𝓞 F) F (phi x).out) ≠ 0 := by
          rw [hresτ (phi x)]
          exact hy
        calc
          (χ ^ (-(3 : ℤ))) (phi x) = chiPow D v
              (algebraMap (𝓞 F) F (phi x).out) (-(3 : ℤ)) :=
            rf_local_mulchar_zpow_eval D S v χ hχval (-(3 : ℤ)) (phi x)
          _ = chi D v (algebraMap (𝓞 F) F (phi x).out) ^ (-(3 : ℤ)) :=
            SB.chiPow_nonzero v _ (-(3 : ℤ)) hyresne
          _ = (χ (phi x)) ^ (-(3 : ℤ)) := by rw [hychi]
      have hα : maskAlpha D A v (primeGen R v) 1 x =
          (maskTau D A v (primeGen R v) 1)⁻¹ *
            chi D v (algebraMap (𝓞 F) F x.out) ^ (-1 : ℤ) := by
        simp [maskAlpha, hx]
      have hcombine : (χ x) ^ (-1 : ℤ) * (χ x) ^ (4 : ℤ) =
          (χ x) ^ (3 : ℤ) := by
        calc
          _ = (χ x) ^ ((-1 : ℤ) + 4) := (zpow_add₀ hxχne _ _).symm
          _ = _ := by congr 1 <;> norm_num
      calc
        maskAlpha D A v (primeGen R v) 1 x *
            chi D v (algebraMap (𝓞 F) F x.out) ^ 4 =
          (maskTau D A v (primeGen R v) 1)⁻¹ *
            ((χ x) ^ (-1 : ℤ) * (χ x) ^ (4 : ℤ)) := by
              rw [hα, hxchi]
              ac_rfl
        _ = (maskTau D A v (primeGen R v) 1)⁻¹ * (χ x) ^ (3 : ℤ) := by
          rw [hcombine]
        _ = (maskTau D A v (primeGen R v) 1)⁻¹ *
            (localChi D v t ^ (3 : ℤ) * χ (phi x) ^ (-(3 : ℤ))) := by
          rw [hpowχ]
        _ = c * ((χ ^ (-(3 : ℤ))) (phi x)) := by
          dsimp [c]
          rw [← hchiYpow]
          ac_rfl
    let g : (𝓞 F ⧸ v.asIdeal) → ℂ := fun y => if y = 0 then 0 else
      c * (χ y) ^ (-(3 : ℤ)) * ψ y
    have hpoint (x : 𝓞 F ⧸ v.asIdeal) : f x = g (phi x) := by
      by_cases hx : x = 0
      · subst x
        simp [f, g, hphi0]
      · have hy : phi x ≠ 0 := by
          intro hzero
          have hEq : phi x = phi 0 := by rw [hzero, hphi0]
          exact hx (hphiBij.1 hEq)
        simp only [f, g, if_neg hx, if_neg hy]
        rw [hcoef x hx]
        rw [hchiMinus3 (phi x) hy]
    have hsumChange : (∑ x : 𝓞 F ⧸ v.asIdeal, f x) =
        ∑ y : 𝓞 F ⧸ v.asIdeal, g y :=
      Fintype.sum_bijective phi hphiBij f g hpoint
    have hcharSum :
        (∑ y : 𝓞 F ⧸ v.asIdeal, if y = 0 then 0 else
          (χ ^ (-(3 : ℤ))) y * ψ y) = maskTau D A v (primeGen R v) 3 := by
      have hgauss : (∑ y : 𝓞 F ⧸ v.asIdeal,
          if y = 0 then 0 else (χ ^ (-(3 : ℤ))) y * ψ y) =
          gaussSum (χ ^ (-(3 : ℤ))) ψ := by
        change (∑ y : 𝓞 F ⧸ v.asIdeal,
          if y = 0 then 0 else (χ ^ (-(3 : ℤ))) y * ψ y) =
          ∑ y : 𝓞 F ⧸ v.asIdeal, (χ ^ (-(3 : ℤ))) y * ψ y
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y = 0
        · subst y
          have hzeroChar : (χ ^ (-(3 : ℤ)))
              (0 : 𝓞 F ⧸ v.asIdeal) = 0 :=
            MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : 𝓞 F ⧸ v.asIdeal))
          simp only [if_pos rfl]
          rw [hzeroChar]
          simp
        · simp [hy]
      calc
        _ = gaussSum (χ ^ (-(3 : ℤ))) ψ := hgauss
        _ = maskTau D A v (primeGen R v) 3 := (htau 3).symm
    have hsumG : (∑ y : 𝓞 F ⧸ v.asIdeal, g y) = c *
      maskTau D A v (primeGen R v) 3 := by
      calc
        (∑ y, g y) = ∑ y, c * (if y = 0 then 0 else
            (χ ^ (-(3 : ℤ))) y * ψ y) := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : y = 0
          · simp [g, hy]
          · simp only [g, if_neg hy]
            rw [hchiMinus3 y hy]
            ac_rfl
        _ = c * ∑ y, if y = 0 then 0 else
            (χ ^ (-(3 : ℤ))) y * ψ y := by rw [Finset.mul_sum]
        _ = _ := by rw [hcharSum]
    have hzeroFinsum : (∑ᶠ x, f x) = c *
        maskTau D A v (primeGen R v) 3 := by
      calc
        (∑ᶠ x, f x) = ∑ x, f x := hf
        _ = c * maskTau D A v (primeGen R v) 3 := hsumChange.trans hsumG
    have hformula := rf_localR_formula R v hv 1 0 t htLoc
    rw [hformula, hW0, hphaseFinsum, hzeroFinsum]
    have hchiPow7 : localChi D v t ^ (7 : ℕ) = localChi D v t := by
      rw [show (7 : ℕ) = 6 + 1 by norm_num, pow_add, hlocalChiSix]
      simp
    rw [hOmegaRatio]
    simp only [mul_zero, add_zero, one_mul]
    change localChi D v t ^ (4 : ℕ) * (c * maskTau D A v (primeGen R v) 3) =
      (maskTau D A v (primeGen R v) 3 / maskTau D A v (primeGen R v) 1) *
        localChi D v t
    dsimp [c]
    rw [div_eq_mul_inv]
    calc
      _ = localChi D v t ^ (7 : ℕ) *
          (maskTau D A v (primeGen R v) 1)⁻¹ *
            maskTau D A v (primeGen R v) 3 := by ring
      _ = localChi D v t *
          (maskTau D A v (primeGen R v) 1)⁻¹ *
            maskTau D A v (primeGen R v) 3 := by rw [hchiPow7]
      _ = maskTau D A v (primeGen R v) 3 /
          maskTau D A v (primeGen R v) 1 * localChi D v t := by
            rw [div_eq_mul_inv]
            ring
  · have hΩ : localOmega R v =
        maskTau D A v (primeGen R v) 3 / maskTau D A v (primeGen R v) 1 := by
      unfold localOmega
      rw [rf_localOmega_numerator_maskTau R v hv ψ hψval]
    have hχneg3ne : χ ^ (-(3 : ℤ)) ≠ 1 := by
      apply rf_local_mulchar_zpow_ne_one hχorder (-3)
      norm_num
    have hχneg1ne : χ ^ (-(1 : ℤ)) ≠ 1 := by
      apply rf_local_mulchar_zpow_ne_one hχorder (-1)
      norm_num
    have hnorm3 : ‖maskTau D A v (primeGen R v) 3‖ =
        Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
      rw [htau 3]
      exact rf_gauss_sum_norm (χ ^ (-(3 : ℤ))) ψ hχneg3ne hψprim
    have hnorm1 : ‖maskTau D A v (primeGen R v) 1‖ =
        Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
      rw [htau 1]
      exact rf_gauss_sum_norm (χ ^ (-(1 : ℤ))) ψ hχneg1ne hψprim
    have hcardpos : 0 < (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    rw [hΩ, norm_div, hnorm3, hnorm1]
    exact div_self (ne_of_gt (Real.sqrt_pos.2 hcardpos))
  ·
    let qC : ℂ := (Ideal.absNorm v.asIdeal : ℂ)
    have hqC : qC = (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℂ) := by
      dsimp [qC]
      exact_mod_cast hnormCard.symm
    have hqRgt : 1 < (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
      rw [hnormCard]
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hqRpos : 0 < (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by positivity
    let fψ : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x => if x = 0 then 0 else
      maskAlpha D A v (primeGen R v) j x *
        chi D v (algebraMap (𝓞 F) F x.out) ^ 4 *
          A.ψ v (((toLoc v (primeGen R v) ^ ((0 : ℤ) - 1) * t :
            (v.adicCompletion F)ˣ) : _) /
              algebraMap F _ (algebraMap (𝓞 F) F x.out))
    let f : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x => if x = 0 then 0 else
      maskAlpha D A v (primeGen R v) j x *
        chi D v (algebraMap (𝓞 F) F x.out) ^ 4 * ψ (phi x)
    have hfψ := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v fψ
    have hf := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v f
    have hphaseFinsum : (∑ᶠ x, fψ x) = ∑ᶠ x, f x := by
      calc
        (∑ᶠ x, fψ x) = ∑ x, fψ x := hfψ
        _ = ∑ x, f x := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = 0
          · simp [fψ, f, hx]
          · simp only [fψ, f, if_neg hx]
            have hphase := hphaseZero x hx
            have hphase' : A.ψ v (((toLoc v (primeGen R v) ^
                ((0 : ℤ) - 1) * t : (v.adicCompletion F)ˣ) : _) /
                  algebraMap F _ (algebraMap (𝓞 F) F x.out)) = ψ (phi x) := by
              simpa using hphase
            rw [hphase']
        _ = ∑ᶠ x, f x := hf.symm
    have hW0 : localW R v 0 = 1 := by
      rw [rf_localW_table R v hv 0]
      simp [sphericalTable]
    have hyne (x : 𝓞 F ⧸ v.asIdeal) (hx : x ≠ 0) : phi x ≠ 0 := by
      intro hzero
      have hEq : phi x = phi 0 := by rw [hzero, hphi0]
      exact hx (hphiBij.1 hEq)
    have hOrbitZero (j0 : Fin 6) (hj0 : j0 = 0) :
        (∑ᶠ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
          maskAlpha D A v (primeGen R v) j0 x *
            chi D v (algebraMap (𝓞 F) F x.out) ^ 4 * ψ (phi x)) =
        (-qC⁻¹ * localChi D v t ^ (4 : ℤ)) *
          gaussSum (χ ^ (-(4 : ℤ))) ψ := by
      subst j0
      let f0 : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x => if x = 0 then 0 else
        maskAlpha D A v (primeGen R v) 0 x *
          chi D v (algebraMap (𝓞 F) F x.out) ^ 4 * ψ (phi x)
      let g : (𝓞 F ⧸ v.asIdeal) → ℂ := fun y => if y = 0 then 0 else
        (-qC⁻¹ * localChi D v t ^ (4 : ℤ)) *
          ((χ ^ (-(4 : ℤ))) y * ψ y)
      have hf0 := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v f0
      have hpoint (x : 𝓞 F ⧸ v.asIdeal) : f0 x = g (phi x) := by
        by_cases hx : x = 0
        · subst x
          simp [f0, g, hphi0]
        · have hy := hyne x hx
          have hα : maskAlpha D A v (primeGen R v) 0 x = -qC⁻¹ := by
            simp [maskAlpha, hx, qC]
          have hpow := hchiOrbitPow x hx hy (4 : ℤ)
          simp only [f0, g, if_neg hx, if_neg hy]
          rw [hα, hchiEval x hx]
          have hnat : (χ x) ^ (4 : ℕ) = (χ x) ^ (4 : ℤ) :=
            (zpow_natCast (χ x) 4).symm
          rw [hnat, hpow, ← hchiZpowEval (-(4 : ℤ)) (phi x) hy]
          ring
      have hsumChange : (∑ x, f0 x) = ∑ y, g y :=
        Fintype.sum_bijective phi hphiBij f0 g hpoint
      have hsumG : (∑ y, g y) =
          (-qC⁻¹ * localChi D v t ^ (4 : ℤ)) *
            gaussSum (χ ^ (-(4 : ℤ))) ψ := by
        calc
          (∑ y, g y) = ∑ y, (-qC⁻¹ * localChi D v t ^ (4 : ℤ)) *
              (if y = 0 then 0 else (χ ^ (-(4 : ℤ))) y * ψ y) := by
                apply Finset.sum_congr rfl
                intro y _
                by_cases hy : y = 0 <;> simp [g, hy]
          _ = (-qC⁻¹ * localChi D v t ^ (4 : ℤ)) *
              ∑ y, if y = 0 then 0 else (χ ^ (-(4 : ℤ))) y * ψ y := by
                rw [Finset.mul_sum]
          _ = _ := by rw [hmaskedGauss]
      calc
        (∑ᶠ x, f0 x) = ∑ x, f0 x := hf0
        _ = _ := hsumChange.trans hsumG
    have hOrbitNonzero (j : Fin 6) (hj0 : j ≠ 0) :
        (∑ᶠ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
          maskAlpha D A v (primeGen R v) j x *
            chi D v (algebraMap (𝓞 F) F x.out) ^ 4 * ψ (phi x)) =
          (maskTau D A v (primeGen R v) j)⁻¹ *
            localChi D v t ^ ((4 : ℤ) - j.1) *
              gaussSum (χ ^ ((j.1 : ℤ) - 4)) ψ := by
      let n : ℤ := (j.1 : ℤ) - 4
      let k : ℤ := (4 : ℤ) - j.1
      let fj : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x => if x = 0 then 0 else
        maskAlpha D A v (primeGen R v) j x *
          chi D v (algebraMap (𝓞 F) F x.out) ^ 4 * ψ (phi x)
      let gj : (𝓞 F ⧸ v.asIdeal) → ℂ := fun y => if y = 0 then 0 else
        (maskTau D A v (primeGen R v) j)⁻¹ * localChi D v t ^ k *
          ((χ ^ n) y * ψ y)
      have hfinsum := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v fj
      have hpoint (x : 𝓞 F ⧸ v.asIdeal) : fj x = gj (phi x) := by
        by_cases hx : x = 0
        · subst x
          simp [fj, gj, hphi0]
        · have hy := hyne x hx
          have hα : maskAlpha D A v (primeGen R v) j x =
              (maskTau D A v (primeGen R v) j)⁻¹ *
                chi D v (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) := by
            simp [maskAlpha, hj0, hx]
          have hpow := hchiOrbitPow x hx hy k
          have hnat : (χ x) ^ (4 : ℕ) = (χ x) ^ (4 : ℤ) :=
            (zpow_natCast _ 4).symm
          have hcombine : (χ x) ^ (-(j.1 : ℤ)) * (χ x) ^ (4 : ℤ) =
              (χ x) ^ k := by
            calc
              _ = (χ x) ^ ((-(j.1 : ℤ)) + 4) := (zpow_add₀
                ((MulChar.apply_ne_zero_iff).2 (isUnit_iff_ne_zero.mpr hx)) _ _).symm
              _ = _ := by congr 1 <;> dsimp [k] <;> ring
          simp only [fj, gj, if_neg hx, if_neg hy]
          rw [hα, hchiEval x hx, hnat]
          calc
            _ = ((maskTau D A v (primeGen R v) j)⁻¹ *
                (χ x ^ (-(j.1 : ℤ)) * χ x ^ (4 : ℤ))) * ψ (phi x) := by ac_rfl
            _ = ((maskTau D A v (primeGen R v) j)⁻¹ * (χ x ^ k)) * ψ (phi x) := by
              rw [hcombine]
            _ = (maskTau D A v (primeGen R v) j)⁻¹ * localChi D v t ^ k *
                ((χ ^ n) (phi x) * ψ (phi x)) := by
              rw [hpow]
              have hnEq : n = -k := by dsimp [n, k]; ring
              have hchar : (χ (phi x)) ^ (-k) = (χ ^ n) (phi x) := by
                rw [← hnEq]
                exact (hchiZpowEval n (phi x) hy).symm
              rw [hchar]
              ring
      have hsumChange : (∑ x, fj x) = ∑ y, gj y :=
        Fintype.sum_bijective phi hphiBij fj gj hpoint
      have hsumG : (∑ y, gj y) =
          (maskTau D A v (primeGen R v) j)⁻¹ * localChi D v t ^ k *
            gaussSum (χ ^ n) ψ := by
        calc
          (∑ y, gj y) = ∑ y, (maskTau D A v (primeGen R v) j)⁻¹ *
              localChi D v t ^ k *
                (if y = 0 then 0 else (χ ^ n) y * ψ y) := by
                  apply Finset.sum_congr rfl
                  intro y _
                  by_cases hy : y = 0 <;> simp [gj, hy]
          _ = (maskTau D A v (primeGen R v) j)⁻¹ * localChi D v t ^ k *
              ∑ y, if y = 0 then 0 else (χ ^ n) y * ψ y := by
                rw [Finset.mul_sum]
          _ = _ := by rw [hmaskedGauss]
      calc
        _ = ∑ x, fj x := hfinsum
        _ = ∑ y, gj y := hsumChange
        _ = _ := hsumG
    rw [rf_localR_formula R v hv j 0 t htLoc, hphaseFinsum, hW0]
    simp only [mul_zero, add_zero, one_mul]
    by_cases hj0 : j = 0
    · have hsum0 : (∑ᶠ x, f x) =
          (-qC⁻¹ * localChi D v t ^ (4 : ℤ)) *
            gaussSum (χ ^ (-(4 : ℤ))) ψ := by
        simpa [f, hj0] using hOrbitZero j hj0
      rw [hsum0]
      have hχm4ne : χ ^ (-(4 : ℤ)) ≠ 1 := by
        apply rf_local_mulchar_zpow_ne_one hχorder
        norm_num
      have hgaussNorm : ‖gaussSum (χ ^ (-(4 : ℤ))) ψ‖ =
          Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) :=
        rf_gauss_sum_norm _ _ hχm4ne hψprim
      have hqcnorm : ‖qC‖ = (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
        rw [hqC]
        simp
      have hbound : (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ)⁻¹ *
          Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) ≤ 1 := by
        have hsqrt : 1 ≤ Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
          calc
            1 = Real.sqrt 1 := by norm_num
            _ ≤ Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) :=
              Real.sqrt_le_sqrt hqRgt.le
        have hrootpos := Real.sqrt_pos.2 hqRpos
        have hprod : (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ)⁻¹ *
            Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) =
              1 / Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
          field_simp [ne_of_gt hqRpos, ne_of_gt hrootpos]
          nlinarith [Real.sq_sqrt hqRpos.le]
        rw [hprod]
        exact (div_le_one₀ hrootpos).2 hsqrt
      calc
        ‖localChi D v t ^ (4 : ℤ) *
            ((-qC⁻¹ * localChi D v t ^ (4 : ℤ)) *
              gaussSum (χ ^ (-(4 : ℤ))) ψ)‖ =
              (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ)⁻¹ *
                Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
          have hcharpow : χ ^ (-(4 : ℤ)) = (χ ^ (4 : ℤ))⁻¹ := by
            rw [zpow_neg]
          rw [hcharpow] at hgaussNorm
          simp [norm_mul, norm_zpow, hlocalChiNorm, hqcnorm]
          exact hgaussNorm
        _ ≤ 1 := hbound
    · rw [hOrbitNonzero j hj0]
      have hτne : χ ^ (-(j.1 : ℤ)) ≠ 1 := by
        apply rf_local_mulchar_zpow_ne_one hχorder
        have hjpos : 0 < j.1 := Nat.pos_of_ne_zero (by
          intro h
          exact hj0 (Fin.ext h))
        have hjlt : j.1 < 6 := j.isLt
        omega
      have hτnorm : ‖maskTau D A v (primeGen R v) j‖ =
          Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
        rw [htau j]
        exact rf_gauss_sum_norm _ _ hτne hψprim
      have hkEval : (4 : ℤ) - j.1 + ((j.1 : ℤ) - 4) = 0 := by ring
      have hnumCase : j = 4 ∨ j ≠ 4 := eq_or_ne j 4
      rcases hnumCase with hj4 | hj4
      · subst j
        have hgaussOne : gaussSum (χ ^ ((4 : ℤ) - 4)) ψ = -1 := by
          convert gaussSum_one_left hψne using 1 <;> rfl
        have hrootpos : 0 < Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) :=
          Real.sqrt_pos.2 hqRpos
        have hdenpos : 0 < ‖maskTau D A v (primeGen R v) (4 : Fin 6)‖ := by
          rw [hτnorm]
          exact hrootpos
        calc
          ‖localChi D v t ^ (4 : ℤ) *
              ((maskTau D A v (primeGen R v) (4 : Fin 6))⁻¹ *
                localChi D v t ^ (4 - 4 : ℤ) *
                  gaussSum (χ ^ ((4 : ℤ) - 4)) ψ)‖ =
              ‖maskTau D A v (primeGen R v) (4 : Fin 6)‖⁻¹ := by
            rw [hgaussOne]
            simp only [norm_mul, norm_zpow, hlocalChiNorm, inv_one, mul_one,
              norm_inv, norm_neg, norm_one]
            ring
          _ ≤ 1 := by
            rw [hτnorm]
            have hsqrt : 1 ≤ Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
              calc
                1 = Real.sqrt 1 := by norm_num
                _ ≤ Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) :=
                  Real.sqrt_le_sqrt hqRgt.le
            simpa [one_div] using (div_le_one₀ hrootpos).2 hsqrt
      · have hnne : (j.1 : ℤ) - 4 ≠ 0 := by
          intro h
          apply hj4
          apply Fin.ext
          omega
        have hnumNe : χ ^ ((j.1 : ℤ) - 4) ≠ 1 := by
          apply rf_local_mulchar_zpow_ne_one hχorder
          have hjpos : 0 < j.1 := Nat.pos_of_ne_zero (by
            intro h
            exact hj0 (Fin.ext h))
          have hjlt : j.1 < 6 := j.isLt
          omega
        have hnumNorm : ‖gaussSum (χ ^ ((j.1 : ℤ) - 4)) ψ‖ =
            Real.sqrt (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) :=
          rf_gauss_sum_norm _ _ hnumNe hψprim
        calc
          ‖localChi D v t ^ (4 : ℤ) *
              ((maskTau D A v (primeGen R v) j)⁻¹ *
                localChi D v t ^ ((4 : ℤ) - j.1) *
                  gaussSum (χ ^ ((j.1 : ℤ) - 4)) ψ)‖ = 1 := by
            simp [norm_mul, hchiOrbitPowNorm, hτnorm, hnumNorm,
              Real.sqrt_ne_zero'.mpr hqRpos]
            rw [hlocalChiNorm]
            norm_num
          _ ≤ 1 := le_rfl
  · intro he
    by_cases hj4 : j = 4
    · subst j
      have hR : localR R v 4 e t =
          localW R v e * localChi D v t ^ (4 + 2 * e) *
            (((Ideal.absNorm v.asIdeal : ℂ) - 1) / maskTau D A v (primeGen R v) 4) := by
        rw [rf_localR_formula R v hv 4 e t htLoc, hphaseSum he t htLoc]
        rw [rf_local_positive_alpha_chi_sum D S A v (primeGen R v) χ hχval hχorder 4]
        simp
      let q : ℝ := qI v.asIdeal
      have hqpos : 1 < q := by
        dsimp [q, qI]
        exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hqcard : (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) = q := by
        dsimp [q, qI]
        exact_mod_cast hnormCard
      have hχ4ne : χ ^ (-(4 : ℤ)) ≠ 1 := by
        apply rf_local_mulchar_zpow_ne_one hχorder
        norm_num
      have hτ4norm : ‖maskTau D A v (primeGen R v) 4‖ = Real.sqrt q := by
        rw [htau 4]
        have h := rf_gauss_sum_norm (χ ^ (-(4 : ℤ))) ψ hχ4ne hψprim
        rw [hqcard] at h
        exact h
      have hchiPowNorm (n : ℤ) : ‖localChi D v t ^ n‖ = 1 := by
        rw [norm_zpow, hlocalChiNorm]
        simp
      have hqminuspos : 0 < q - 1 := by linarith
      have hnumNorm : ‖((Ideal.absNorm v.asIdeal : ℂ) - 1)‖ = q - 1 := by
        have hcast : (Ideal.absNorm v.asIdeal : ℂ) - 1 = ((q - 1 : ℝ) : ℂ) := by
          simp [q, qI]
        rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqminuspos]
      have hcoeffNorm :
          ‖((Ideal.absNorm v.asIdeal : ℂ) - 1) / maskTau D A v (primeGen R v) 4‖ =
            (q - 1) / Real.sqrt q := by
        rw [norm_div, hnumNorm, hτ4norm]
      have hrootPos : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
      have hrootSq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt (by linarith : 0 ≤ q)
      have hcoeffBound : (q - 1) / Real.sqrt q ≤ Real.sqrt q := by
        apply (div_le_iff₀ hrootPos).2
        nlinarith [hrootSq]
      have hRzero : localR R v 4 e t =
          localW R v e * localChi D v t ^ (4 + 2 * e) *
            (((Ideal.absNorm v.asIdeal : ℂ) - 1) / maskTau D A v (primeGen R v) 4) := hR
      calc
        ‖localR R v 4 e t‖ = ‖localW R v e‖ * ((q - 1) / Real.sqrt q) := by
          rw [hRzero]
          simp only [norm_mul, hchiPowNorm, hcoeffNorm, mul_one]
        _ ≤ ‖localW R v e‖ * Real.sqrt q :=
          mul_le_mul_of_nonneg_left hcoeffBound (norm_nonneg _)
        _ = Real.sqrt q * ‖localW R v e‖ := by ring
        _ = qI v.asIdeal ^ (1 / 2 : ℝ) * ‖localW R v e‖ := by
          rw [Real.sqrt_eq_rpow]
    · have hRzero : localR R v j e t = 0 := by
        rw [rf_localR_formula R v hv j e t htLoc, hphaseSum he t htLoc]
        rw [rf_local_positive_alpha_chi_sum D S A v (primeGen R v) χ hχval hχorder j]
        simp [hj4]
      rw [hRzero]
      simp only [norm_zero]
      have hqnonneg : 0 ≤ qI v.asIdeal := by
        dsimp [qI]
        positivity
      exact mul_nonneg (Real.rpow_nonneg hqnonneg _) (norm_nonneg _)
  · intro he
    by_cases he0 : e = 0
    · subst e
      let qC : ℂ := (Ideal.absNorm v.asIdeal : ℂ)
      have hWzero : localW R v 0 = 1 := by
        rw [rf_localW_table R v hv 0]
        simp [sphericalTable]
      let ftψ : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x => if x = 0 then 0 else
        maskAlpha D A v (primeGen R v) j x *
          chi D v (algebraMap (𝓞 F) F x.out) ^ 4 *
            A.ψ v (((toLoc v (primeGen R v) ^ ((0 : ℤ) - 1) * t :
              (v.adicCompletion F)ˣ) : _) /
                algebraMap F _ (algebraMap (𝓞 F) F x.out))
      let ft : (𝓞 F ⧸ v.asIdeal) → ℂ := fun x => if x = 0 then 0 else
        maskAlpha D A v (primeGen R v) j x *
          chi D v (algebraMap (𝓞 F) F x.out) ^ 4 * ψ (phi x)
      have hftψ := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v ftψ
      have hft := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v ft
      have hphaseFinsumT : (∑ᶠ x, ftψ x) = ∑ᶠ x, ft x := by
        calc
          (∑ᶠ x, ftψ x) = ∑ x, ftψ x := hftψ
          _ = ∑ x, ft x := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x = 0
            · simp [ftψ, ft, hx]
            · simp only [ftψ, ft, if_neg hx]
              have hphase := hphaseZero x hx
              have hphase' : A.ψ v (((toLoc v (primeGen R v) ^
                  ((0 : ℤ) - 1) * t : (v.adicCompletion F)ˣ) : _) /
                    algebraMap F _ (algebraMap (𝓞 F) F x.out)) = ψ (phi x) := by
                simpa using hphase
              rw [hphase']
          _ = ∑ᶠ x, ft x := hft.symm
      let f1ψ : (𝓞 F ⧸ v.asIdeal) → ℂ := fun y => if y = 0 then 0 else
        maskAlpha D A v (primeGen R v) j y *
          chi D v (algebraMap (𝓞 F) F y.out) ^ 4 *
            A.ψ v (((toLoc v (primeGen R v) ^ ((0 : ℤ) - 1) *
              (1 : (v.adicCompletion F)ˣ) : (v.adicCompletion F)ˣ) : _) /
                algebraMap F _ (algebraMap (𝓞 F) F y.out))
      let f1 : (𝓞 F ⧸ v.asIdeal) → ℂ := fun y => if y = 0 then 0 else
        maskAlpha D A v (primeGen R v) j y *
          chi D v (algebraMap (𝓞 F) F y.out) ^ 4 * ψ (y⁻¹)
      have hf1ψ := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v f1ψ
      have hf1 := ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum v f1
      have hphaseFinsumOne : (∑ᶠ y, f1ψ y) = ∑ᶠ y, f1 y := by
        calc
          (∑ᶠ y, f1ψ y) = ∑ y, f1ψ y := hf1ψ
          _ = ∑ y, f1 y := by
            apply Finset.sum_congr rfl
            intro y _
            by_cases hy : y = 0
            · simp [f1ψ, f1, hy]
            · simp only [f1ψ, f1, if_neg hy]
              have hphase := hphaseOne y hy
              have hphase' : A.ψ v (((toLoc v (primeGen R v) ^
                  ((0 : ℤ) - 1) * (1 : (v.adicCompletion F)ˣ) :
                    (v.adicCompletion F)ˣ) : _) /
                    algebraMap F _ (algebraMap (𝓞 F) F y.out)) = ψ (y⁻¹) := by
                simpa using hphase
              rw [hphase']
          _ = ∑ᶠ y, f1 y := hf1.symm
      have hlocalChiOne : localChi D v (1 : (v.adicCompletion F)ˣ) = 1 :=
        (ArtinPrimitiveRoots.A1.Theta.localChi_basic (D := D) (v := v) hv6).1
      have hlocalChiNe : localChi D v t ≠ 0 := by
        intro hzero
        rw [hzero] at hlocalChiNorm
        norm_num at hlocalChiNorm
      have hchiInv (y : 𝓞 F ⧸ v.asIdeal) (hy : y ≠ 0) :
          χ (y⁻¹) = (χ y)⁻¹ := by
        have hχyne : χ y ≠ 0 :=
          (MulChar.apply_ne_zero_iff).2 (isUnit_iff_ne_zero.mpr hy)
        have hprod : χ (y⁻¹) * χ y = 1 := by
          calc
            χ (y⁻¹) * χ y = χ (y⁻¹ * y) := (map_mul χ (y⁻¹) y).symm
            _ = χ 1 := congrArg χ (inv_mul_cancel₀ hy)
            _ = 1 := MulChar.map_one χ
        have hdiv : χ (y⁻¹) = 1 / χ y := (eq_div_iff hχyne).2 hprod
        simpa [one_div] using hdiv
      have hcoeffScale (y : 𝓞 F ⧸ v.asIdeal) (hy : y ≠ 0) :
          maskAlpha D A v (primeGen R v) j (τ * y) *
              chi D v (algebraMap (𝓞 F) F (τ * y).out) ^ 4 =
            localChi D v t ^ ((4 : ℤ) - j.1) *
              (maskAlpha D A v (primeGen R v) j y *
                chi D v (algebraMap (𝓞 F) F y.out) ^ 4) := by
        let x : 𝓞 F ⧸ v.asIdeal := τ * y
        have hx : x ≠ 0 := mul_ne_zero hτne hy
        have hphix : phi x ≠ 0 := by
          rw [show x = τ * y by rfl, hphiScale y hy]
          exact inv_ne_zero hy
        have hχx : chi D v (algebraMap (𝓞 F) F x.out) = χ x := hchiEval x hx
        have hχy : chi D v (algebraMap (𝓞 F) F y.out) = χ y := hchiEval y hy
        have hnatX : (χ x) ^ (4 : ℕ) = (χ x) ^ (4 : ℤ) :=
          (zpow_natCast (χ x) 4).symm
        have hnatY : (χ y) ^ (4 : ℕ) = (χ y) ^ (4 : ℤ) :=
          (zpow_natCast (χ y) 4).symm
        by_cases hj0 : j = 0
        · subst j
          have hαx : maskAlpha D A v (primeGen R v) 0 x = -qC⁻¹ := by
            simp [maskAlpha, hx, qC]
          have hαy : maskAlpha D A v (primeGen R v) 0 y = -qC⁻¹ := by
            simp [maskAlpha, hy, qC]
          have horbit := hchiOrbitPow x hx hphix (4 : ℤ)
          have hinvpow : χ (y⁻¹) ^ (-(4 : ℤ)) = (χ y) ^ (4 : ℤ) := by
            rw [hchiInv y hy, inv_zpow]
            simp
          calc
            _ = (-qC⁻¹) * (χ x) ^ (4 : ℤ) := by
              rw [hαx, hχx, hnatX]
            _ = (-qC⁻¹) *
                (localChi D v t ^ (4 : ℤ) * χ (phi x) ^ (-(4 : ℤ))) := by
              rw [horbit]
            _ = localChi D v t ^ (4 : ℤ) *
                (maskAlpha D A v (primeGen R v) 0 y *
                  chi D v (algebraMap (𝓞 F) F y.out) ^ 4) := by
              rw [show phi x = y⁻¹ by
                rw [show x = τ * y by rfl, hphiScale y hy], hinvpow,
                hαy, hχy, hnatY]
              ring
        · have hαxG : maskAlpha D A v (primeGen R v) j x =
              (maskTau D A v (primeGen R v) j)⁻¹ *
                chi D v (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) := by
            simp [maskAlpha, hj0, hx]
          have hαyG : maskAlpha D A v (primeGen R v) j y =
              (maskTau D A v (primeGen R v) j)⁻¹ *
                chi D v (algebraMap (𝓞 F) F y.out) ^ (-(j.1 : ℤ)) := by
            simp [maskAlpha, hj0, hy]
          have hαx : maskAlpha D A v (primeGen R v) j x =
              (maskTau D A v (primeGen R v) j)⁻¹ * (χ x) ^ (-(j.1 : ℤ)) := by
            rw [hαxG, hχx]
          have hαy : maskAlpha D A v (primeGen R v) j y =
              (maskTau D A v (primeGen R v) j)⁻¹ * (χ y) ^ (-(j.1 : ℤ)) := by
            rw [hαyG, hχy]
          have hχxne : χ x ≠ 0 :=
            (MulChar.apply_ne_zero_iff).2 (isUnit_iff_ne_zero.mpr hx)
          have hχyne : χ y ≠ 0 :=
            (MulChar.apply_ne_zero_iff).2 (isUnit_iff_ne_zero.mpr hy)
          let k : ℤ := (4 : ℤ) - j.1
          have hcombineX : (χ x) ^ (-(j.1 : ℤ)) * (χ x) ^ (4 : ℤ) = (χ x) ^ k := by
            calc
              _ = (χ x) ^ ((-(j.1 : ℤ)) + 4) :=
                (zpow_add₀ hχxne _ _).symm
              _ = _ := by congr 1 <;> dsimp [k] <;> ring
          have hcombineY : (χ y) ^ (-(j.1 : ℤ)) * (χ y) ^ (4 : ℤ) = (χ y) ^ k := by
            calc
              _ = (χ y) ^ ((-(j.1 : ℤ)) + 4) :=
                (zpow_add₀ hχyne _ _).symm
              _ = _ := by congr 1 <;> dsimp [k] <;> ring
          have horbit := hchiOrbitPow x hx hphix k
          have hinvpow : χ (y⁻¹) ^ (-k) = (χ y) ^ k := by
            rw [hchiInv y hy, inv_zpow]
            simp
          calc
            _ = (maskTau D A v (primeGen R v) j)⁻¹ *
                ((χ x) ^ (-(j.1 : ℤ)) * (χ x) ^ (4 : ℤ)) := by
              rw [hαx, hχx, hnatX]
              ac_rfl
            _ = (maskTau D A v (primeGen R v) j)⁻¹ * (χ x) ^ k := by
              rw [hcombineX]
            _ = (maskTau D A v (primeGen R v) j)⁻¹ *
                (localChi D v t ^ k * χ (phi x) ^ (-k)) := by
              rw [horbit]
            _ = localChi D v t ^ k *
                ((maskTau D A v (primeGen R v) j)⁻¹ * (χ y) ^ k) := by
              rw [show phi x = y⁻¹ by
                rw [show x = τ * y by rfl, hphiScale y hy], hinvpow]
              ac_rfl
            _ = localChi D v t ^ k *
                (maskAlpha D A v (primeGen R v) j y *
                  chi D v (algebraMap (𝓞 F) F y.out) ^ 4) := by
              rw [hαy, hχy, hnatY, ← hcombineY]
              ac_rfl
      let g : (𝓞 F ⧸ v.asIdeal) → ℂ := fun y => ft (τ * y)
      have hbijInv : Function.Bijective (fun x : 𝓞 F ⧸ v.asIdeal => τ⁻¹ * x) :=
        mulLeft_bijective₀ τ⁻¹ (inv_ne_zero hτne)
      have hsumReindex : (∑ x : 𝓞 F ⧸ v.asIdeal, ft x) =
          ∑ y : 𝓞 F ⧸ v.asIdeal, ft (τ * y) := by
        have hτcancel : τ * τ⁻¹ = 1 := mul_inv_cancel₀ hτne
        have hmul (x : 𝓞 F ⧸ v.asIdeal) : τ * (τ⁻¹ * x) = x := by
          calc
            τ * (τ⁻¹ * x) = (τ * τ⁻¹) * x := by ac_rfl
            _ = 1 * x := congrArg (fun z : 𝓞 F ⧸ v.asIdeal => z * x) hτcancel
            _ = x := by simp
        have hpoint (x : 𝓞 F ⧸ v.asIdeal) : ft x = g (τ⁻¹ * x) := by
          dsimp [g]
          exact (congrArg ft (hmul x)).symm
        simpa [g] using Fintype.sum_bijective
          (fun x : 𝓞 F ⧸ v.asIdeal => τ⁻¹ * x) hbijInv ft g hpoint
      have hsumScale : (∑ᶠ x, ft x) =
          localChi D v t ^ ((4 : ℤ) - j.1) * ∑ᶠ y, f1 y := by
        calc
          (∑ᶠ x, ft x) = ∑ x, ft x := hft
          _ = ∑ y, ft (τ * y) := hsumReindex
          _ = ∑ y, localChi D v t ^ ((4 : ℤ) - j.1) * f1 y := by
            apply Finset.sum_congr rfl
            intro y _
            by_cases hy : y = 0
            · subst y
              simp [ft, f1]
            · have hxy := hcoeffScale y hy
              have hph := hphiScale y hy
              simp only [ft, f1, if_neg (mul_ne_zero hτne hy), if_neg hy]
              rw [hxy, hph]
              ring
          _ = localChi D v t ^ ((4 : ℤ) - j.1) * ∑ y, f1 y := by
            rw [Finset.mul_sum]
          _ = localChi D v t ^ ((4 : ℤ) - j.1) * ∑ᶠ y, f1 y := by rw [← hf1]
      have hlocalChiOne : localChi D v (1 : (v.adicCompletion F)ˣ) = 1 :=
        (ArtinPrimitiveRoots.A1.Theta.localChi_basic (D := D) (v := v) hv6).1
      have hRt : localR R v j 0 t =
          localChi D v t ^ (4 : ℤ) * ∑ᶠ x, ft x := by
        rw [rf_localR_formula R v hv j 0 t htLoc, hphaseFinsumT, hWzero]
        simp only [mul_zero, add_zero, one_mul]
      have hRone : localR R v j 0 1 = ∑ᶠ y, f1 y := by
        rw [rf_localR_formula R v hv j 0 1 hOneLoc, hphaseFinsumOne, hWzero]
        simp [hlocalChiOne]
      have hlocalChiNonzero : localChi D v t ≠ 0 := by
        intro hz
        rw [hz] at hlocalChiNorm
        norm_num at hlocalChiNorm
      have hB : localB j (Int.toNat (0 : ℤ)) =
          (4 : ℤ) + ((4 : ℤ) - j.1) := by
        simp [localB]
        ring
      rw [hRt, hRone, hsumScale]
      calc
        localChi D v t ^ (4 : ℤ) *
            (localChi D v t ^ ((4 : ℤ) - j.1) * ∑ᶠ y, f1 y) =
          localChi D v t ^ ((4 : ℤ) + ((4 : ℤ) - j.1)) * ∑ᶠ y, f1 y := by
            calc
              _ = (localChi D v t ^ (4 : ℤ) *
                    localChi D v t ^ ((4 : ℤ) - j.1)) * ∑ᶠ y, f1 y := by ac_rfl
              _ = localChi D v t ^ ((4 : ℤ) + ((4 : ℤ) - j.1)) * ∑ᶠ y, f1 y := by
                exact congrArg (fun z : ℂ => z * ∑ᶠ y, f1 y)
                  ((zpow_add₀ hlocalChiNonzero (4 : ℤ) ((4 : ℤ) - j.1)).symm)
        _ = (∑ᶠ y, f1 y) *
            localChi D v t ^ localB j (Int.toNat (0 : ℤ)) := by
              rw [hB]
              ac_rfl
    · have hepos : 0 < e := by omega
      have hlocalChiOne : localChi D v (1 : (v.adicCompletion F)ˣ) = 1 :=
        (ArtinPrimitiveRoots.A1.Theta.localChi_basic (D := D) (v := v) hv6).1
      have hnatPos : e.toNat ≠ 0 := by omega
      have hnat : (e.toNat : ℤ) = e := Int.toNat_of_nonneg he
      have hB : localB j e.toNat = (4 : ℤ) + 2 * e := by
        simp [localB, hnatPos, hnat]
      let sum0 : ℂ := ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, if x = 0 then 0 else
        maskAlpha D A v (primeGen R v) j x *
          chi D v (algebraMap (𝓞 F) F x.out) ^ 4
      have hRt : localR R v j e t =
          localW R v e * localChi D v t ^ (4 + 2 * e) * sum0 := by
        rw [rf_localR_formula R v hv j e t htLoc, hphaseSum hepos t htLoc]
      have hRone : localR R v j e 1 =
          localW R v e * localChi D v (1 : (v.adicCompletion F)ˣ) ^ (4 + 2 * e) * sum0 := by
        rw [rf_localR_formula R v hv j e 1 hOneLoc, hphaseSum hepos 1 hOneLoc]
      rw [hRt, hRone, hlocalChiOne, hB]
      rw [one_zpow]
      ring
  · intro he hj4
    rw [rf_localR_formula R v hv j e 1 hOneLoc, hphaseSum he 1 hOneLoc]
    rw [rf_local_positive_alpha_chi_sum D S A v (primeGen R v) χ hχval hχorder j]
    simp [hj4]
  · intro he hmod
    have hWzero : localW R v e = 0 := by
      rw [rf_localW_table R v hv e]
      simp [sphericalTable, not_lt.mpr he, hmod]
    rw [rf_localR_formula R v hv j e 1 hOneLoc, hWzero]
    simp
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

end ArtinPrimitiveRoots.A2
