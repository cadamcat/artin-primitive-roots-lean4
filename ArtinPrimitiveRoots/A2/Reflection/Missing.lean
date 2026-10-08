import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».All
import ArtinPrimitiveRoots.Proofs.th_factor_b.Analytic
import ArtinPrimitiveRoots.A1.ThetaInterfaceMain
import Mathlib.Analysis.Asymptotics.Basic

/-! A2 statement interfaces derived from the design lane. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory Filter Topology Asymptotics
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

private theorem heckeChar_unitary_of_finOrder (χ : HeckeChar F) (hχ : IsOfFinOrder χ) :
    ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hχ)
  intro x
  have hxpow : (χ x : ℂˣ) ^ n = 1 := by
    have hx := congrArg (fun f : HeckeChar F => f x) hpow
    simpa using hx
  have hxpowC : (((χ x : ℂˣ) : ℂ) ^ n) = 1 := by
    simpa using congrArg (fun z : ℂˣ => (z : ℂ)) hxpow
  exact ((isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hxpowC⟩).norm_eq_one)

private theorem reflection_kernel_moments (K : ℝ → ℂ)
    (hK : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K (Set.Ioi 0))
    (hbounds : ∀ N : ℝ, ∀ j : ℕ, ∃ C : ℝ, ∀ t, 0 < t →
      ‖Theta.normDerivR j K t‖ ≤ C * min (t ^ N) (t ^ (-N))) :
    ∀ β : ℝ, IntegrableOn (fun t => ‖K t‖ * t ^ β / t) (Set.Ioi 0) := by
  classical
  intro β
  let N : ℝ := |β| + 2
  have hβlo : -N < β := by dsimp [N]; have := neg_le_abs β; linarith
  have hβhi : β < N := by dsimp [N]; have := le_abs_self β; linarith
  obtain ⟨C, hC⟩ := hbounds N 0
  have hC_nonneg : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have h' : ‖K 1‖ ≤ C := by simpa [Theta.normDerivR, N] using h
    exact (norm_nonneg (K 1)).trans h'
  have hnorm (t : ℝ) (ht : 0 < t) : ‖Theta.normDerivR 0 K t‖ = ‖K t‖ := by
    simp [Theta.normDerivR, Real.exp_log ht]
  have htop : K =O[atTop] (fun t : ℝ => t ^ (-N)) := by
    refine (IsBigOWith.of_bound (c := C) ?_).isBigO
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have h := hC t ht0
    rw [hnorm t ht0] at h
    have hp : t ^ (-N) ≤ t ^ N :=
      Real.rpow_le_rpow_of_exponent_le ht (by linarith)
    rw [min_eq_right hp] at h
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)] using h
  have hbot : K =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ N) := by
    refine (IsBigOWith.of_bound (c := C) ?_).isBigO
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h := hC t ht
    rw [hnorm t ht] at h
    have h' : ‖K t‖ ≤ C * t ^ N := by
      calc
        ‖K t‖ ≤ C * min (t ^ N) (t ^ (-N)) := h
        _ ≤ C * t ^ N := mul_le_mul_of_nonneg_left (min_le_left _ _) hC_nonneg
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)] using h'
  have hconv : MellinConvergent K (β : ℂ) :=
    mellinConvergent_of_isBigO_rpow (a := N) (b := -N)
      (hK.continuousOn.locallyIntegrableOn measurableSet_Ioi) htop
      (by simpa using hβhi) (by simpa only [neg_neg] using hbot) (by simpa using hβlo)
  have hconv' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((β : ℂ) - 1) * K t) (Set.Ioi 0) := by
    simpa [MellinConvergent, smul_eq_mul] using hconv
  have hEq : (fun t : ℝ => ‖(t : ℂ) ^ ((β : ℂ) - 1) * K t‖) =ᵐ[
      volume.restrict (Set.Ioi 0)] (fun t => ‖K t‖ * t ^ β / t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    rw [Real.rpow_sub_one ht.ne']
    ring
  exact hconv'.norm.congr hEq

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
  classical
  intro η Λ G hη hηram hΛunit hΛangular hG hGauss
  let ϑ : HeckeChar F := vartheta Λ G η
  have hΛram : ∀ v, v ∉ S.Sf → Λ.UnramifiedAt v := fun v hv => (hGauss v hv).1
  have hGram : ∀ v, v ∉ S.Sf → G.UnramifiedAt v := fun v hv => (hGauss v hv).2.1
  have hηunit : ∀ x, ‖((η x : ℂˣ) : ℂ)‖ = 1 :=
    heckeChar_unitary_of_finOrder η hη
  have hGunit : ∀ x, ‖((G x : ℂˣ) : ℂ)‖ = 1 :=
    heckeChar_unitary_of_finOrder G hG
  have hϑunit : ∀ x, ‖((ϑ x : ℂˣ) : ℂ)‖ = 1 := by
    intro x
    change ‖((((Λ x : ℂˣ)⁻¹ * (G x : ℂˣ)⁻¹) * (η x : ℂˣ) : ℂˣ) : ℂ)‖ = 1
    simp [Units.val_mul, Units.val_inv, norm_mul, norm_inv,
      hΛunit x, hGunit x, hηunit x]
  have hϑram : ∀ v, v ∉ S.Sf → ϑ.UnramifiedAt v := by
    intro v hv u hu huinv
    change (Λ.loc v u)⁻¹ * (G.loc v u)⁻¹ * η.loc v u = 1
    rw [hΛram v hv u hu huinv, hGram v hv u hu huinv, hηram v hv u hu huinv]
    simp
  have hΛG : ∀ v, v ∉ S.Sf → ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
      gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p =
        -(Λ.primeValue v * G.primeValue v) := fun v hv => (hGauss v hv).2.2
  have hVS := vartheta_S D S A H Bd η Λ G hηram hΛram hGram hη hG hΛunit hΛangular hΛG
  have hϑangular : HeckeChar.HasAngularType D ϑ := by
    intro w
    obtain ⟨m, hm, hangle⟩ := hVS.2.2.1 w
    have hwc : w.IsComplex := D.isTotallyComplex.isComplex w
    refine ⟨-m, ?_, ?_⟩
    · rcases hm with hm | hm <;> simp [hm]
    · intro z
      let zInf : w.Completionˣ := Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).symm.toMonoidHom z
      let zInf' (w' : InfinitePlace F) : w'.Completionˣ := Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w')).symm.toMonoidHom
          (S.compC w' (S.atComplex w z))
      let g (w' : InfinitePlace F) : ℂ :=
        (((ϑ.locInf w' (zInf' w'))⁻¹ : ℂˣ) : ℂ)
      have hmap : zInf' w = zInf := by
        apply Units.ext
        simp [zInf', zInf, SData.atComplex, SData.compC]
      have hfinite :
          ∏ v : S.Sf,
            (((ϑ.loc v (S.compU v (S.atComplex w z)))⁻¹ : ℂˣ) : ℂ) = 1 := by
        apply Fintype.prod_eq_one
        intro v
        have hU : S.compU v (S.atComplex w z) = 1 := by
          apply Units.ext
          simp [SData.atComplex, SData.compU]
        rw [hU]
        simp [HeckeChar.loc]
      have hcomplex : ∏ w' : InfinitePlace F, g w' =
          (((ϑ.locInf w zInf)⁻¹ : ℂˣ) : ℂ) := by
        rw [Fintype.prod_eq_single w]
        · simp [g, hmap]
        · intro w' hne
          have hC : S.compC w' (S.atComplex w z) = 1 := by
            apply Units.ext
            simp [SData.atComplex, SData.compC, hne]
          simp [g, zInf', hC]
      have hLS : S.LS ϑ (S.atComplex w z) =
          (((ϑ.locInf w zInf)⁻¹ : ℂˣ) : ℂ) := by
        unfold SData.LS
        rw [hfinite]
        simp_rw [dif_pos (D.isTotallyComplex.isComplex _)]
        rw [hcomplex]
        simp
      have hval := hangle z
      rw [hLS] at hval
      have hval' : ((ϑ.locInf w zInf : ℂˣ) : ℂ)⁻¹ =
          ((z : ℂ) / ‖(z : ℂ)‖) ^ m := by simpa using hval
      have hlocal : ((ϑ.locInf w zInf : ℂˣ) : ℂ) =
          ((z : ℂ) / ‖(z : ℂ)‖) ^ (-m) := by
        calc
          ((ϑ.locInf w zInf : ℂˣ) : ℂ) =
              ((((ϑ.locInf w zInf : ℂˣ) : ℂ)⁻¹)⁻¹) := by simp
          _ = (((z : ℂ) / ‖(z : ℂ)‖) ^ m)⁻¹ := congrArg Inv.inv hval'
          _ = ((z : ℂ) / ‖(z : ℂ)‖) ^ (-m) := by rw [← zpow_neg]
      exact hlocal
  obtain ⟨E⟩ := exteriorArithmetic_exists D S H Bd bc
  obtain ⟨Sh⟩ := sheetGeometry_exists D S μ v0
  obtain ⟨Chars⟩ := reflectionCharacters_exists D S H Bd bc ϑ hϑunit hϑram hϑangular
  obtain ⟨Pair⟩ := classPairing_exists D S H
  letI : Fintype (UnitSix S) := Sh.unitSixFinite
  let family : Finset (SChar S) := Finset.univ.image Chars.L
  have hmem : ∀ u, Chars.L u ∈ family := by
    intro u
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
  obtain ⟨P, hRP, hfamily⟩ := A1.theta_interface D S H A
  let T : ThetaFamily P.tc family := Classical.choice (hfamily family)
  rcases T.U_spec with ⟨hUo, hUc, hU1, _, hUunit, _, _⟩
  letI : IsTotallyComplex F := D.isTotallyComplex
  obtain ⟨C₀, A₀, hC₀, hA₀, hMellin, K, hKsmooth, hKbounds, hKgaussian, hKmellin⟩ :=
    Theta.gaussian_smoothing S μ v0 T.U hUo hUc hU1 hUunit T.cS T.cS_pos
  let h6 (u : UnitSix S) := T.T6 (Chars.L u) (hmem u)
  let rotJ (u : UnitSix S) : ℕ := Classical.choose (h6 u)
  let hffExists (u : UnitSix S) := Classical.choose_spec (h6 u)
  let rotFF (u : UnitSix S) : Fin (rotJ u) → (v : S.Sf) → v.1.adicCompletion F → ℂ :=
    Classical.choose (hffExists u)
  let hfcExists (u : UnitSix S) := Classical.choose_spec (hffExists u)
  let rotFC (u : UnitSix S) : Fin (rotJ u) → InfinitePlace F → ℂ → ℂ :=
    Classical.choose (hfcExists u)
  let rotData (u : UnitSix S) := Classical.choose_spec (hfcExists u)
  let rotated : UnitSix S → RotatedPresentation S T.δ := fun u =>
    ⟨rotJ u, rotFF u, rotFC u, (rotData u).1, (rotData u).2.1⟩
  have hrotated_eq : ∀ u y,
      T.WS (Chars.L u) (P.tc.aS y * P.tc.wS) =
        Theta.sumProd S (rotated u).J (rotated u).ff (rotated u).fc (y : S.FS) := by
    intro u y
    have hWS := (rotData u).2.2 y
    simpa only [Theta.sumProd] using hWS
  refine ⟨{
    vartheta_unitary := hϑunit
    vartheta_unramified := hϑram
    vartheta_angular := hϑangular
    vartheta_generator := ?_
    exterior := E
    sheets := Sh
    chars := Chars
    pairing := Pair
    C := P.tc
    family := family
    T := T
    mem_family := hmem
    rotated := rotated
    rotated_eq := hrotated_eq
    K := K
    K_smooth := hKsmooth
    K_moments := reflection_kernel_moments K hKsmooth hKbounds
    K_bounds := hKbounds
    K_gaussian := hKgaussian
  }⟩
  · intro I
    exact hVS.1 I.1 (bc.gen I) I.2 (bc.gen_spec I).1

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

private theorem a2Setup_same_generator_ideal
    (S : SData F CE condη) (x : F) (I J : Ideal (𝓞 F))
    (hI : S.IsGen x I) (hJ : S.IsGen x J) : I = J := by
  classical
  have hI0 : I ≠ 0 := by simpa [Ideal.zero_eq_bot] using hI.1.1
  have hJ0 : J ≠ 0 := by simpa [Ideal.zero_eq_bot] using hJ.1.1
  have hcounts : ∀ v : FinPlace F,
      FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    intro v
    by_cases hv : v ∈ S.Sf
    · have hnotI : ¬ v.asIdeal ∣ I := by
        intro hdiv
        exact hI.1.2 v hv (Ideal.dvd_iff_le.mp hdiv)
      have hnotJ : ¬ v.asIdeal ∣ J := by
        intro hdiv
        exact hJ.1.2 v hv (Ideal.dvd_iff_le.mp hdiv)
      have hcountI : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
        by_contra hn
        exact hnotI ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hn)
      have hcountJ : (Associates.mk v.asIdeal).count (Associates.mk J).factors = 0 := by
        by_contra hn
        exact hnotJ ((Associates.count_ne_zero_iff_dvd hJ0 v.irreducible).mp hn)
      rw [FractionalIdeal.count_coe F v hI0, FractionalIdeal.count_coe F v hJ0,
        hcountI, hcountJ]
    · exact (hI.2.2 v hv).symm.trans (hJ.2.2 v hv)
  let gI : ClassFieldTheory.NumberFieldFractionalIdealGroup F :=
    Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hI0)
  let gJ : ClassFieldTheory.NumberFieldFractionalIdealGroup F :=
    Units.mk0 (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hJ0)
  have hg : gI = gJ := by
    apply ClassFieldTheory.NumberFieldFractionalIdealGroup.ext_count
    intro v
    change FractionalIdeal.count F v
        (gI : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      FractionalIdeal.count F v (gJ : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    simpa [gI, gJ] using hcounts v
  have hfrac : (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    have hval := congrArg
      (fun g : ClassFieldTheory.NumberFieldFractionalIdealGroup F =>
        (g : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) hg
    simpa [gI, gJ] using hval
  exact FractionalIdeal.coeIdeal_injective hfrac

private theorem a2Setup_emultiplicity_eq_factorization (p I : Ideal (𝓞 F))
    (hp : Prime p) (hI : I ≠ 0) :
    emultiplicity p I = (factorization I p : ℕ∞) := by
  rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hp.irreducible hI]
  simp [factorization, normalize_eq]

private theorem a2Setup_powerful_split_unique
    (I h d h' d' : Ideal (𝓞 F))
    (hI : I = h * d) (hI' : I = h' * d')
    (hh : h ≠ ⊥) (hd : d ≠ ⊥) (hh' : h' ≠ ⊥) (hd' : d' ≠ ⊥)
    (hpower : IsPowerful h) (hpower' : IsPowerful h')
    (hsq : Squarefree d) (hsq' : Squarefree d')
    (hcop : IsCoprime h d) (hcop' : IsCoprime h' d') : h = h' ∧ d = d' := by
  have hh0 : h ≠ 0 := by simpa [Ideal.zero_eq_bot] using hh
  have hd0 : d ≠ 0 := by simpa [Ideal.zero_eq_bot] using hd
  have hh'0 : h' ≠ 0 := by simpa [Ideal.zero_eq_bot] using hh'
  have hd'0 : d' ≠ 0 := by simpa [Ideal.zero_eq_bot] using hd'
  have hfac : factorization I = factorization h + factorization d := by
    rw [hI]
    exact factorization_mul hh0 hd0
  have hfac' : factorization I = factorization h' + factorization d' := by
    rw [hI']
    exact factorization_mul hh'0 hd'0
  have hcountEq : ∀ p : Ideal (𝓞 F), factorization h p = factorization h' p := by
    intro p
    by_cases hp : Prime p
    · let eI := factorization I p
      let eh := factorization h p
      let ed := factorization d p
      let eh' := factorization h' p
      let ed' := factorization d' p
      have hsum : eI = eh + ed := congrArg (fun f : Ideal (𝓞 F) →₀ ℕ => f p) hfac
      have hsum' : eI = eh' + ed' := congrArg (fun f : Ideal (𝓞 F) →₀ ℕ => f p) hfac'
      have hdBound : ed ≤ 1 := by
        have hsqE := (squarefree_iff_emultiplicity_le_one d).mp hsq p
        have hle : emultiplicity p d ≤ 1 := hsqE.resolve_right hp.not_isUnit
        rw [a2Setup_emultiplicity_eq_factorization p d hp hd0] at hle
        exact_mod_cast hle
      have hd'Bound : ed' ≤ 1 := by
        have hsqE := (squarefree_iff_emultiplicity_le_one d').mp hsq' p
        have hle : emultiplicity p d' ≤ 1 := hsqE.resolve_right hp.not_isUnit
        rw [a2Setup_emultiplicity_eq_factorization p d' hp hd'0] at hle
        exact_mod_cast hle
      have hpowBound : 0 < eh → 2 ≤ eh := by
        intro heh
        have hem : 0 < emultiplicity p h := by
          rw [a2Setup_emultiplicity_eq_factorization p h hp hh0]
          exact_mod_cast heh
        have hdiv : p ∣ h := (dvd_iff_emultiplicity_pos).mp hem
        let v : FinPlace F := HeightOneSpectrum.ofPrime hp
        have hp2 : p ^ 2 ∣ h := by simpa [v] using hpower v hdiv
        have hle : (2 : ℕ∞) ≤ emultiplicity p h :=
          (pow_dvd_iff_le_emultiplicity).mp hp2
        rw [a2Setup_emultiplicity_eq_factorization p h hp hh0] at hle
        exact_mod_cast hle
      have hpowBound' : 0 < eh' → 2 ≤ eh' := by
        intro heh
        have hem : 0 < emultiplicity p h' := by
          rw [a2Setup_emultiplicity_eq_factorization p h' hp hh'0]
          exact_mod_cast heh
        have hdiv : p ∣ h' := (dvd_iff_emultiplicity_pos).mp hem
        let v : FinPlace F := HeightOneSpectrum.ofPrime hp
        have hp2 : p ^ 2 ∣ h' := by simpa [v] using hpower' v hdiv
        have hle : (2 : ℕ∞) ≤ emultiplicity p h' :=
          (pow_dvd_iff_le_emultiplicity).mp hp2
        rw [a2Setup_emultiplicity_eq_factorization p h' hp hh'0] at hle
        exact_mod_cast hle
      have hcopCounts : ¬ (0 < eh ∧ 0 < ed) := by
        rintro ⟨heh, hed⟩
        have hemH : 0 < emultiplicity p h := by
          rw [a2Setup_emultiplicity_eq_factorization p h hp hh0]
          exact_mod_cast heh
        have hemD : 0 < emultiplicity p d := by
          rw [a2Setup_emultiplicity_eq_factorization p d hp hd0]
          exact_mod_cast hed
        have hdivH : p ∣ h := (dvd_iff_emultiplicity_pos).mp hemH
        have hdivD : p ∣ d := (dvd_iff_emultiplicity_pos).mp hemD
        have hpne : p ≠ ⊤ := by
          intro htop
          apply hp.not_isUnit
          rw [htop]
          simpa [Ideal.one_eq_top] using (isUnit_one : IsUnit (1 : Ideal (𝓞 F)))
        have htop : (⊤ : Ideal (𝓞 F)) ≤ p := by
          rw [← hcop.sup_eq]
          exact sup_le (Ideal.dvd_iff_le.mp hdivH) (Ideal.dvd_iff_le.mp hdivD)
        exact hpne (top_unique htop)
      have hcopCounts' : ¬ (0 < eh' ∧ 0 < ed') := by
        rintro ⟨heh, hed⟩
        have hemH : 0 < emultiplicity p h' := by
          rw [a2Setup_emultiplicity_eq_factorization p h' hp hh'0]
          exact_mod_cast heh
        have hemD : 0 < emultiplicity p d' := by
          rw [a2Setup_emultiplicity_eq_factorization p d' hp hd'0]
          exact_mod_cast hed
        have hdivH : p ∣ h' := (dvd_iff_emultiplicity_pos).mp hemH
        have hdivD : p ∣ d' := (dvd_iff_emultiplicity_pos).mp hemD
        have hpne : p ≠ ⊤ := by
          intro htop
          apply hp.not_isUnit
          rw [htop]
          simpa [Ideal.one_eq_top] using (isUnit_one : IsUnit (1 : Ideal (𝓞 F)))
        have htop : (⊤ : Ideal (𝓞 F)) ≤ p := by
          rw [← hcop'.sup_eq]
          exact sup_le (Ideal.dvd_iff_le.mp hdivH) (Ideal.dvd_iff_le.mp hdivD)
        exact hpne (top_unique htop)
      have hcanonical : eh = if 2 ≤ eI then eI else 0 := by
        by_cases heI : 2 ≤ eI
        · have heh : 0 < eh := by
            by_contra hnot
            have heh0 : eh = 0 := Nat.eq_zero_of_not_pos hnot
            have heq : eI = ed := by rw [hsum, heh0]; omega
            have : eI ≤ 1 := by rw [heq]; exact hdBound
            omega
          have hed0 : ed = 0 := by
            by_contra hne
            exact hcopCounts ⟨heh, Nat.pos_of_ne_zero hne⟩
          have heq : eI = eh := by rw [hsum, hed0]; omega
          rw [if_pos heI]
          exact heq.symm
        · have heh0 : eh = 0 := by
            by_contra hne
            have hehpos := Nat.pos_of_ne_zero hne
            have : 2 ≤ eI := by rw [hsum]; omega
            exact heI this
          rw [if_neg heI]
          exact heh0
      have hcanonical' : eh' = if 2 ≤ eI then eI else 0 := by
        by_cases heI : 2 ≤ eI
        · have heh : 0 < eh' := by
            by_contra hnot
            have heh0 : eh' = 0 := Nat.eq_zero_of_not_pos hnot
            have heq : eI = ed' := by rw [hsum', heh0]; omega
            have : eI ≤ 1 := by rw [heq]; exact hd'Bound
            omega
          have hed0 : ed' = 0 := by
            by_contra hne
            exact hcopCounts' ⟨heh, Nat.pos_of_ne_zero hne⟩
          have heq : eI = eh' := by rw [hsum', hed0]; omega
          rw [if_pos heI]
          exact heq.symm
        · have heh0 : eh' = 0 := by
            by_contra hne
            have hehpos := Nat.pos_of_ne_zero hne
            have : 2 ≤ eI := by rw [hsum']; omega
            exact heI this
          rw [if_neg heI]
          exact heh0
      change eh = eh'
      exact hcanonical.trans hcanonical'.symm
    · have hnotNorm (J : Ideal (𝓞 F)) :
          p ∉ UniqueFactorizationMonoid.normalizedFactors J := by
        intro hpJ
        exact hp (UniqueFactorizationMonoid.prime_of_normalized_factor p hpJ)
      have hzero (J : Ideal (𝓞 F)) : factorization J p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hsupp
        have hpfin : p ∈ (UniqueFactorizationMonoid.normalizedFactors J).toFinset := by
          simpa [support_factorization] using hsupp
        exact hnotNorm J (Multiset.mem_toFinset.mp hpfin)
      rw [hzero h, hzero h']
  have hfacEq : factorization h = factorization h' := by
    ext p
    exact hcountEq p
  have hassoc : Associated h h' :=
    associated_of_factorization_eq h h' hh0 hh'0 hfacEq
  have hhEq : h = h' := associated_iff_eq.mp hassoc
  constructor
  · exact hhEq
  · have hmul : h * d = h * d' := by
      calc
        h * d = I := hI.symm
        _ = h' * d' := hI'
        _ = h * d' := by rw [hhEq]
    exact (mul_left_cancel₀ hh0) hmul

/-- Row-factorization obligation for the finite/`tsum` bridge to `prop:reflection`
(04:1198–1228). -/
theorem reflection_row_element_injective : rowElementInjectiveStatement (S := S) := by
  intro r s hrs
  cases r with
  | mk rm rI rh rd rgen rfac rhp rds rc =>
    cases s with
    | mk sm sI sh sd sgen sfac shp sds sc =>
      have hm : rm = sm := Subtype.ext hrs
      have hideal : rI.1 = sI.1 :=
        a2Setup_same_generator_ideal S (rm : F) rI.1 sI.1 rgen
          (by simpa [hm] using sgen)
      have hsplit := a2Setup_powerful_split_unique rI.1 rh.1 rd.1 sh.1 sd.1
        rfac (hideal.trans sfac)
        rh.2.1 rd.2.1 sh.2.1 sd.2.1
        rhp shp rds sds rc sc
      have hI : rI = sI := Subtype.ext hideal
      have hh : rh = sh := Subtype.ext hsplit.1
      have hd : rd = sd := Subtype.ext hsplit.2
      subst sm
      subst sI
      subst sh
      subst sd
      rfl

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
