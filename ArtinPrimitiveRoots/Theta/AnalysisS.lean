import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.MeasureSubstrate
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.ComplexPolar
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.RadialScaling
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.ProductPolar
import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».PowerClasses
import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».FiniteWeighted
import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».ComplexRadial
import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».ComplexWeighted
import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».Differentiation
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory
open scoped FourierTransform Topology

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## P-ANALYSIS-S -/

section AnalysisS

variable {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη)

/-- Multiplicative Haar measure `d^×y = dy/‖y‖_v` at a finite place. -/
def mulHaarFin {v : FinPlace F} (μ : LocHaar v) : Measure (v.adicCompletion F) :=
  μ.μ.withDensity fun y => ENNReal.ofReal (absFin v y)⁻¹

/-- Multiplicative measure `d^×z = dz/|z|²` on `ℂ^×` (`= π (dt/t) dθ`, `t = |z|²`, `θ ∈ [0,1)`). -/
def mulHaarC : Measure ℂ := volume.withDensity fun z => ENNReal.ofReal (Complex.normSq z)⁻¹

/-- `d^×y` on `F_S = Π_{v∈S_f} F_v × ℂ^r`. -/
def mulHaarS (μ : ∀ v : FinPlace F, LocHaar v) : Measure S.FS :=
  (Measure.pi fun v : S.Sf => mulHaarFin (μ v.1)).prod (Measure.pi fun _ : InfinitePlace F => mulHaarC)

/-- The point of the sheet `X_u` with free coordinates `(y_f, y')` (`y'` off `v0`) and angle `θ` at
the dependent complex place `v0`: `y_{v0} = (u / (‖y_f‖ Π_{w≠v0}|y'_w|²))^{1/2} e^{2πiθ}`. -/
def sheetPoint (v0 : InfinitePlace F) (u : ℝ)
    (p : (∀ v : S.Sf, v.1.adicCompletion F) × ({w : InfinitePlace F // w ≠ v0} → ℂ)) (θ : ℝ) :
    S.FS :=
  (p.1, fun w => if h : w = v0 then
      ((Real.sqrt (u / ((∏ v : S.Sf, absFin v.1 (p.1 v)) *
        ∏ w' : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w'))) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * θ)
    else p.2 ⟨w, h⟩)

/-- **def:sheet-integral**: `H(u) = ∫_{X_u} f d^×_u y` in the `v0`-parametrization. -/
def sheetInt (μ : ∀ v : FinPlace F, LocHaar v) (v0 : InfinitePlace F) (f : S.FS → ℂ) (u : ℝ) : ℂ :=
  ∫ p, ∫ θ in Set.Ioc (0 : ℝ) 1, f (sheetPoint S v0 u p θ) ∂volume
    ∂((Measure.pi fun v : S.Sf => mulHaarFin (μ v.1)).prod
      (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => mulHaarC))

private theorem thsol_sheet_geometry (μ : ∀ v : FinPlace F, LocHaar v) (v0 : InfinitePlace F) :
    let P := (∀ v : S.Sf, v.1.adicCompletion F) × ({w : InfinitePlace F // w ≠ v0} → ℂ)
    let ν : Measure P := (Measure.pi fun v : S.Sf => mulHaarFin (μ v.1)).prod
      (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => mulHaarC)
    let B : P → ℝ := fun p => (∏ v : S.Sf, absFin v.1 (p.1 v)) *
      ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)
    ∃ e : (P × ℂ) ≃ᵐ S.FS, MeasurePreserving e (ν.prod mulHaarC) (mulHaarS S μ) ∧
      (∀ u p θ, e (p, ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint (u / B p, θ)) =
        sheetPoint S v0 u p θ) ∧ Measurable B ∧ ∀ᵐ p ∂ν, 0 < B p := by
  let Xf := ∀ v : S.Sf, v.1.adicCompletion F
  let Xc := {w : InfinitePlace F // w ≠ v0} → ℂ
  let E := {w : InfinitePlace F // w = v0}
  let νf : Measure Xf := Measure.pi fun v : S.Sf => mulHaarFin (μ v.1)
  let νc : Measure Xc := Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => mulHaarC
  have h := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  have : ∀ v : S.Sf, SigmaFinite (mulHaarFin (μ v.1)) := fun v => (h.1 v.1).2.2.2.2
  have : SigmaFinite mulHaarC := h.2.2
  have : ∀ v : S.Sf, NullSingletonClass (mulHaarFin (μ v.1)) := fun v => by
    have : NullSingletonClass (μ v.1).μ := (h.1 v.1).2.2.1
    dsimp [mulHaarFin]
    infer_instance
  have : NullSingletonClass mulHaarC := h.2.1
  let : Unique E := {
    default := ⟨v0, rfl⟩
    uniq := fun w => Subtype.ext w.property }
  let : Fintype E := Subtype.fintype (fun w : InfinitePlace F => w = v0)
  let split : (InfinitePlace F → ℂ) ≃ᵐ ((E → ℂ) × Xc) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ => ℂ) (fun w => w = v0)
  let collapse : ((E → ℂ) × Xc) ≃ᵐ (ℂ × Xc) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.piUnique fun _ : E => ℂ)
      (MeasurableEquiv.refl Xc)
  let ec : (InfinitePlace F → ℂ) ≃ᵐ (Xc × ℂ) :=
    (split.trans collapse).trans (MeasurableEquiv.prodComm : ℂ × Xc ≃ᵐ Xc × ℂ)
  have hsplit : MeasurePreserving split (Measure.pi fun _ : InfinitePlace F => mulHaarC)
      ((Measure.pi fun _ : E => mulHaarC).prod νc) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : InfinitePlace F => mulHaarC) (fun w => w = v0)
  have hcollapse : MeasurePreserving collapse ((Measure.pi fun _ : E => mulHaarC).prod νc)
      (mulHaarC.prod νc) :=
    (measurePreserving_piUnique (fun _ : E => mulHaarC)).prod (MeasurePreserving.id νc)
  have hec : MeasurePreserving ec (Measure.pi fun _ : InfinitePlace F => mulHaarC)
      (νc.prod mulHaarC) :=
    (Measure.measurePreserving_swap (μ := mulHaarC) (ν := νc)).comp (hcollapse.comp hsplit)
  let ef : S.FS ≃ᵐ ((Xf × Xc) × ℂ) :=
    ((MeasurableEquiv.refl Xf).prodCongr ec).trans MeasurableEquiv.prodAssoc.symm
  have hef : MeasurePreserving ef (mulHaarS S μ) ((νf.prod νc).prod mulHaarC) :=
    (measurePreserving_prodAssoc νf νc mulHaarC).symm.comp ((MeasurePreserving.id νf).prod hec)
  have hef_apply (y : S.FS) : ef y = ((y.1, fun w => y.2 w.1), y.2 v0) := by
    rcases y with ⟨yf, yc⟩
    rfl
  refine ⟨ef.symm, hef.symm, ?_, ?_, ?_⟩
  · intro u p θ
    apply ef.injective
    rw [ef.apply_symm_apply, hef_apply]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext w
        simp [sheetPoint, w.property]
    · simp [sheetPoint, ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint]
  · apply Measurable.mul
    · apply Finset.measurable_fun_prod
      intro v hv
      exact (h.1 v.1).1.comp ((measurable_pi_apply v).comp measurable_fst)
    · apply Finset.measurable_fun_prod
      intro w hw
      exact Complex.continuous_normSq.measurable.comp
        ((measurable_pi_apply w).comp measurable_snd)
  · have hfn : ∀ᵐ yf ∂νf, ∀ v : S.Sf, yf v ≠ 0 :=
      ae_all_iff.mpr fun v => Measure.ae_eval_ne (fun v : S.Sf => mulHaarFin (μ v.1)) v 0
    have hcn : ∀ᵐ yc ∂νc, ∀ w : {w : InfinitePlace F // w ≠ v0}, yc w ≠ 0 :=
      ae_all_iff.mpr fun w => Measure.ae_eval_ne (fun _ : {w : InfinitePlace F // w ≠ v0} => mulHaarC) w 0
    have hfn' := (Measure.quasiMeasurePreserving_fst (μ := νf) (ν := νc)).ae hfn
    have hcn' := (Measure.quasiMeasurePreserving_snd (μ := νf) (ν := νc)).ae hcn
    filter_upwards [hfn', hcn'] with p hp hc
    apply mul_pos
    · exact Finset.prod_pos fun v hv => (h.1 v.1).2.1 (p.1 v) (hp v)
    · apply Finset.prod_pos
      intro w hw
      rw [Complex.normSq_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr (hc w))

/-- **eq:sheet-disintegration** (03:487–498): `∫_{F_S^×} f d^×y = π ∫_0^∞ H_f(u) du/u`. -/
theorem sheet_disintegration [IsTotallyComplex F] (μ : ∀ v : FinPlace F, LocHaar v)
    (v0 : InfinitePlace F) (f : S.FS → ℂ) (hf : Integrable f (mulHaarS S μ)) :
    ∫ y, f y ∂(mulHaarS S μ) = Real.pi * ∫ u in Set.Ioi (0 : ℝ), sheetInt S μ v0 f u / u := by
  have h := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  have : ∀ v : S.Sf, SigmaFinite (mulHaarFin (μ v.1)) := fun v => (h.1 v.1).2.2.2.2
  have : SigmaFinite mulHaarC := h.2.2
  let P := (∀ v : S.Sf, v.1.adicCompletion F) × ({w : InfinitePlace F // w ≠ v0} → ℂ)
  let ν : Measure P := (Measure.pi fun v : S.Sf => mulHaarFin (μ v.1)).prod
    (Measure.pi fun _ : {w : InfinitePlace F // w ≠ v0} => mulHaarC)
  let B : P → ℝ := fun p => (∏ v : S.Sf, absFin v.1 (p.1 v)) *
    ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)
  obtain ⟨e, he, hpoint, hB, hpos⟩ := thsol_sheet_geometry S μ v0
  have hg := he.integrable_comp_of_integrable hf
  have hi := (ArtinPrimitiveRoots.Proofs.thsol_sheets.polar_product_disintegration
    ν B hB hpos (fun q => f (e q)) hg).2
  calc
    _ = ∫ q, f (e q) ∂ν.prod mulHaarC := (he.integral_comp' f).symm
    _ = _ := by simpa only [B, ν, hpoint, sheetInt, mulHaarC] using hi

/-- `D^j H(u) = (u d/du)^j H(u)`. -/
def normDerivR (j : ℕ) (Hf : ℝ → ℂ) (u : ℝ) : ℂ :=
  iteratedDeriv j (fun t : ℝ => Hf (Real.exp t)) (Real.log u)

/-- A finite sum of products of local factors (the shape of T6). -/
def sumProd (J : ℕ) (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ) (y : S.FS) : ℂ :=
  ∑ ℓ : Fin J, (∏ v : S.Sf, ff ℓ v (y.1 v)) * ∏ w : InfinitePlace F, fc ℓ w (y.2 w)

/-- The absolute derivative profile `H^abs_j` (derivatives at `v0` only). -/
def absProfile (μ : ∀ v : FinPlace F, LocHaar v) (v0 : InfinitePlace F) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ) (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (j : ℕ) (u : ℝ) : ℝ :=
  ∑ ℓ : Fin J, (sheetInt S μ v0 (fun y => ((‖normDeriv j (fc ℓ v0) (y.2 v0)‖ *
    (∏ w ∈ Finset.univ.erase v0, ‖fc ℓ w (y.2 w)‖) * ∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖ : ℝ) : ℂ)) u).re

/-- Admissible multipliers: `L(y)^k · b([y])`, `L` an admissible S-character, `b` bounded on `𝒱`. -/
def SheetMultiplier (m : S.FS → ℂ) : Prop :=
  ∃ (L : SChar S) (k : ℤ) (b : S.V → ℂ), (∃ C, ∀ x, ‖b x‖ ≤ C) ∧
    ∀ y : S.FSˣ, m (y : S.FS) = ((L.L y : ℂˣ) : ℂ) ^ k * b (QuotientGroup.mk y)

private theorem thsol_multiplier_radial (m : S.FS → ℂ) (hm : SheetMultiplier S m) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ y : S.FSˣ, ‖m (y : S.FS)‖ ≤ C) ∧
      ∀ (w : InfinitePlace F) (y : S.FSˣ) (t : ℝ),
        m ((y * S.atComplex w (Units.mk0 (Real.exp t : ℂ)
          (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)))) : S.FS) = m (y : S.FS) := by
  obtain ⟨L, k, b, ⟨C, hC⟩, hmval⟩ := hm
  refine ⟨max 0 C, le_max_left _ _, ?_, ?_⟩
  · intro y
    rw [hmval, norm_mul, Complex.norm_zpow, L.unitary, one_zpow, one_mul]
    exact (hC _).trans (le_max_right _ _)
  · intro w y t
    let z (s : ℝ) : ℂˣ := Units.mk0 (Real.exp s : ℂ)
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero s))
    have hz6 : z (t / 6) ^ 6 = z t := by
      apply Units.ext
      change (Real.exp (t / 6) : ℂ) ^ 6 = (Real.exp t : ℂ)
      rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    have hrange : S.atComplex w (z t) ∈ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range := by
      refine ⟨S.atComplex w (z (t / 6)), ?_⟩
      change S.atComplex w (z (t / 6)) ^ 6 = S.atComplex w (z t)
      apply Units.ext
      ext v
      · simp [SData.atComplex]
      · by_cases hv : v = w
        · subst v
          simpa [SData.atComplex] using congrArg (fun u : ℂˣ => (u : ℂ)) hz6
        · simp [SData.atComplex, Function.update_of_ne hv]
    have hq : (QuotientGroup.mk (S.atComplex w (z t)) : S.V) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hrange
    have hL : ((L.L (S.atComplex w (z t)) : ℂˣ) : ℂ) = 1 := by
      rw [L.angular]
      simp [omegaAng, z]
    change m ((y * S.atComplex w (z t)) : S.FS) = m (y : S.FS)
    calc
      _ = ((L.L (y * S.atComplex w (z t)) : ℂˣ) : ℂ) ^ k *
          b (QuotientGroup.mk (y * S.atComplex w (z t))) := hmval _
      _ = ((L.L y : ℂˣ) : ℂ) ^ k * b (QuotientGroup.mk y) := by
        simp only [map_mul, Units.val_mul, hL, QuotientGroup.mk_mul, hq, mul_one]
        exact congrArg (fun q : S.V => ((L.L y : ℂˣ) : ℂ) ^ k * b q)
          (mul_one (QuotientGroup.mk y : S.V))
      _ = _ := (hmval y).symm

private theorem thsol_multiplier_continuous (m : S.FS → ℂ) (hm : SheetMultiplier S m) :
    Continuous (fun y : S.FSˣ => m (y : S.FS)) := by
  obtain ⟨L, k, b, hb, hmval⟩ := hm
  let : ∀ v : S.Sf, NontriviallyNormedField (v.1.adicCompletion F) := fun v =>
    Valued.toNontriviallyNormedField (v.1.adicCompletion F) (WithZero (Multiplicative ℤ))
  have hbCont : Continuous (fun y : S.FSˣ => b (QuotientGroup.mk y)) :=
    ArtinPrimitiveRoots.Proofs.thsol_sheets.power_quotient_factor_continuous
      (fun v : S.Sf => v.1.adicCompletion F) (fun _ : InfinitePlace F => ℂ) b
  have hChar := L.cont.zpow₀ k (fun y => Or.inl (L.L y).ne_zero)
  simpa only [hmval, Pi.mul_def] using hChar.mul hbCont

private theorem thsol_multiplier_measurable (m : S.FS → ℂ) (hm : SheetMultiplier S m) :
    ContinuousOn m {y : S.FS | (∀ v : S.Sf, y.1 v ≠ 0) ∧
      ∀ w : InfinitePlace F, y.2 w ≠ 0} ∧
    Measurable (fun y : S.FS => if (∀ v : S.Sf, y.1 v ≠ 0) ∧
      (∀ w : InfinitePlace F, y.2 w ≠ 0) then m y else 0) := by
  let U : Set S.FS := {y | (∀ v : S.Sf, y.1 v ≠ 0) ∧ ∀ w : InfinitePlace F, y.2 w ≠ 0}
  let lift : U → S.FSˣ := fun y =>
    ⟨y.1, ((fun v => (y.1.1 v)⁻¹), (fun w => (y.1.2 w)⁻¹)), by
      apply Prod.ext
      · funext v
        exact mul_inv_cancel₀ (y.property.1 v)
      · funext w
        exact mul_inv_cancel₀ (y.property.2 w), by
      apply Prod.ext
      · funext v
        exact inv_mul_cancel₀ (y.property.1 v)
      · funext w
        exact inv_mul_cancel₀ (y.property.2 w)⟩
  have hlift : Continuous lift := by
    apply Units.continuous_iff.mpr
    refine ⟨continuous_subtype_val, ?_⟩
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact ((continuous_apply v).comp (continuous_fst.comp continuous_subtype_val)).inv₀
        (fun y => y.property.1 v)
    · apply continuous_pi
      intro w
      exact ((continuous_apply w).comp (continuous_snd.comp continuous_subtype_val)).inv₀
        (fun y => y.property.2 w)
  have hcont : ContinuousOn m U :=
    continuousOn_iff_continuous_domRestrict.mpr
      ((thsol_multiplier_continuous S m hm).comp hlift)
  let _ : ∀ v : S.Sf, ProperSpace (v.1.adicCompletion F) := fun v => by
    let K := v.1.adicCompletion F
    let O := v.1.adicCompletionIntegers F
    let _ : Finite (IsLocalRing.ResidueField O) :=
      Finite.of_equiv _ (v.1.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
    exact (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing O),
        inferInstanceAs (Finite (IsLocalRing.ResidueField O))⟩
  have hUopen : IsOpen U := by
    have hf : IsOpen {y : S.FS | ∀ v : S.Sf, y.1 v ≠ 0} := by
      convert isOpen_iInter_of_finite (fun v : S.Sf =>
        (isClosed_singleton : IsClosed ({(0 : v.1.adicCompletion F)} : Set _)).isOpen_compl.preimage
          ((continuous_apply v).comp continuous_fst)) using 1
      ext y
      simp
    have hc : IsOpen {y : S.FS | ∀ w : InfinitePlace F, y.2 w ≠ 0} := by
      convert isOpen_iInter_of_finite (fun w : InfinitePlace F =>
        (isClosed_singleton : IsClosed ({(0 : ℂ)} : Set ℂ)).isOpen_compl.preimage
          ((continuous_apply w).comp continuous_snd)) using 1
      ext y
      simp
    exact hf.inter hc
  refine ⟨hcont, ?_⟩
  exact hcont.measurable_piecewise continuousOn_const hUopen.measurableSet

set_option maxHeartbeats 800000 in
private theorem thsol_profile_weighted [IsTotallyComplex F]
    (μ : ∀ v : FinPlace F, LocHaar v) (v0 : InfinitePlace F)
    (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v))
    (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w)) :
    ∀ (j : ℕ) (σ : ℝ), -δ < σ → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u →
      0 ≤ absProfile S μ v0 J ff fc j u ∧
      absProfile S μ v0 J ff fc j u ≤ C * u ^ (-σ) := by
  intro j σ hσ
  have hsub := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  have : ∀ v : S.Sf, SigmaFinite (mulHaarFin (μ v.1)) := fun v => (hsub.1 v.1).2.2.2.2
  have : SigmaFinite mulHaarC := hsub.2.2
  let W := {w : InfinitePlace F // w ≠ v0}
  let Xf := ∀ v : S.Sf, v.1.adicCompletion F
  let Xc := W → ℂ
  let P := Xf × Xc
  let νf : Measure Xf := Measure.pi fun v : S.Sf => mulHaarFin (μ v.1)
  let νc : Measure Xc := Measure.pi fun _ : W => mulHaarC
  let ν : Measure P := νf.prod νc
  let η : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let B : P → ℝ := fun p => (∏ v : S.Sf, absFin v.1 (p.1 v)) *
    ∏ w : W, Complex.normSq (p.2 w)
  obtain ⟨e, he, hpoint, hB, hpos⟩ := thsol_sheet_geometry S μ v0
  choose M hM hbound using fun ℓ : Fin J =>
    (ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_factor_weighted δ σ hσ
      (fc ℓ v0) (hfc ℓ v0) j).2
  let Ff (ℓ : Fin J) (s : ℝ) (v : S.Sf) (x : v.1.adicCompletion F) : ℝ :=
    ‖ff ℓ v x‖ * absFin v.1 x ^ s
  let Fc (ℓ : Fin J) (s : ℝ) (w : W) (z : ℂ) : ℝ :=
    ‖fc ℓ w.1 z‖ * Complex.normSq z ^ s
  let G (ℓ : Fin J) (p : P) : ℝ :=
    (∏ v : S.Sf, Ff ℓ σ v (p.1 v)) * ∏ w : W, Fc ℓ σ w (p.2 w)
  let N (ℓ : Fin J) (p : P) : ℝ :=
    (∏ w : W, ‖fc ℓ w.1 (p.2 w)‖) * ∏ v : S.Sf, ‖ff ℓ v (p.1 v)‖
  have hFi (ℓ : Fin J) (s : ℝ) (hs : -δ < s) (v : S.Sf) :
      Integrable (Ff ℓ s v) (mulHaarFin (μ v.1)) :=
    ArtinPrimitiveRoots.Proofs.thsol_sheets.finite_factor_weighted_integrable
      (μ v.1) δ s hs (ff ℓ v) (hff ℓ v)
  have hCi (ℓ : Fin J) (s : ℝ) (hs : -δ < s) (w : W) :
      Integrable (Fc ℓ s w) mulHaarC := by
    simpa only [Fc, normDeriv, iteratedDeriv_zero, zero_div, Real.exp_zero,
      Complex.ofReal_one, one_mul, mulHaarC] using!
      (ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_factor_weighted
        δ s hs (fc ℓ w.1) (hfc ℓ w.1) 0).1
  have hGi (ℓ : Fin J) : Integrable (G ℓ) ν :=
    (Integrable.fintype_prod_dep (hFi ℓ σ hσ)).mul_prod
      (Integrable.fintype_prod (hCi ℓ σ hσ))
  have hNi (ℓ : Fin J) : Integrable (N ℓ) ν := by
    have hf0 := Integrable.fintype_prod_dep (hFi ℓ 0 (by linarith only [hδ]))
    have hc0 := Integrable.fintype_prod (hCi ℓ 0 (by linarith only [hδ]))
    have hi : Integrable (fun p : P =>
        (∏ v : S.Sf, ‖ff ℓ v (p.1 v)‖) * ∏ w : W, ‖fc ℓ w.1 (p.2 w)‖) ν := by
      simpa only [Ff, Fc, Real.rpow_zero, mul_one] using hf0.mul_prod hc0
    apply hi.congr
    exact Filter.Eventually.of_forall fun p => mul_comm _ _
  have hNnonneg (ℓ : Fin J) (p : P) : 0 ≤ N ℓ p :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hGnonneg (ℓ : Fin J) (p : P) : 0 ≤ G ℓ p := by
    apply mul_nonneg <;> apply Finset.prod_nonneg
    · intro v hv
      exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by rw [absFin_eq_norm]; positivity) _)
    · intro w hw
      exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Complex.normSq_nonneg _) _)
  have hGfactor (ℓ : Fin J) (p : P) : G ℓ p = N ℓ p * B p ^ σ := by
    have hfnonneg (v : S.Sf) : 0 ≤ absFin v.1 (p.1 v) := by rw [absFin_eq_norm]; positivity
    have hfprod : (∏ v : S.Sf, absFin v.1 (p.1 v) ^ σ) =
        (∏ v : S.Sf, absFin v.1 (p.1 v)) ^ σ :=
      Real.finsetProd_rpow _ _ (fun v _ => hfnonneg v) σ
    have hcprod : (∏ w : W, Complex.normSq (p.2 w) ^ σ) =
        (∏ w : W, Complex.normSq (p.2 w)) ^ σ :=
      Real.finsetProd_rpow _ _ (fun w _ => Complex.normSq_nonneg _) σ
    dsimp only [G, Ff, Fc, N, B]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hfprod, hcprod,
      Real.mul_rpow (Finset.prod_nonneg fun v _ => hfnonneg v)
        (Finset.prod_nonneg fun w _ => Complex.normSq_nonneg _)]
    ring
  let C (ℓ : Fin J) : ℝ := M ℓ *
    (∏ v : S.Sf, ∫ x, Ff ℓ σ v x ∂mulHaarFin (μ v.1)) *
    ∏ w : W, ∫ z, Fc ℓ σ w z ∂mulHaarC
  have hGval (ℓ : Fin J) : M ℓ * ∫ p, G ℓ p ∂ν = C ℓ := by
    dsimp only [G, ν, νf, νc, C]
    rw [integral_prod_mul (fun yf : Xf => ∏ v : S.Sf, Ff ℓ σ v (yf v))
      (fun yc : Xc => ∏ w : W, Fc ℓ σ w (yc w)),
      integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod]
    ring
  have hCnonneg (ℓ : Fin J) : 0 ≤ C ℓ := by
    rw [← hGval ℓ]
    exact mul_nonneg (hM ℓ) (integral_nonneg (hGnonneg ℓ))
  have hsummand (ℓ : Fin J) (u : ℝ) (hu : 0 < u) :
      let a := (sheetInt S μ v0 (fun y => ((‖normDeriv j (fc ℓ v0) (y.2 v0)‖ *
        (∏ w ∈ Finset.univ.erase v0, ‖fc ℓ w (y.2 w)‖) *
          ∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖ : ℝ) : ℂ)) u).re
      0 ≤ a ∧ a ≤ C ℓ * u ^ (-σ) := by
    let z : P × ℝ → ℂ := fun q =>
      ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint (u / B q.1, q.2)
    let R : P × ℝ → ℝ := fun q => ‖normDeriv j (fc ℓ v0) (z q)‖ * N ℓ q.1
    have hzmeas : Measurable z :=
      ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_polar_measurePreserving.measurable.comp
        ((measurable_const.div (hB.comp measurable_fst)).prodMk measurable_snd)
    have hdmeas : Measurable (fun z => ‖normDeriv j (fc ℓ v0) z‖) :=
      (measurable_of_continuousOn_compl_singleton (0 : ℂ)
        (ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_normDeriv_contDiff
          (fc ℓ v0) (hfc ℓ v0).1 j).continuousOn).norm
    have hRmeas : AEStronglyMeasurable R (ν.prod η) :=
      (hdmeas.comp hzmeas).aestronglyMeasurable.mul (hNi ℓ).aestronglyMeasurable.comp_fst
    have hRnonneg (q : P × ℝ) : 0 ≤ R q := mul_nonneg (norm_nonneg _) (hNnonneg ℓ _)
    have hp : ∀ᵐ q ∂ν.prod η, 0 < B q.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := η)).ae hpos
    have hRbound : ∀ᵐ q ∂ν.prod η, R q ≤ (M ℓ * u ^ (-σ)) * G ℓ q.1 := by
      filter_upwards [hp] with q hq
      have hrad : 0 < u / B q.1 := div_pos hu hq
      have hznorm : Complex.normSq (z q) = u / B q.1 := by
        dsimp only [z, ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint]
        rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp]
        have hre : (2 * Real.pi * Complex.I * (q.2 : ℂ)).re = 0 := by simp
        rw [hre, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hrad.le]
      have hz0 : z q ≠ 0 := by
        intro hz
        have : Complex.normSq (z q) = 0 := by simp only [hz, map_zero]
        rw [hznorm] at this
        exact hrad.ne' this
      have hlocal := hbound ℓ (z q) hz0
      rw [hznorm] at hlocal
      have hweight : ((u / B q.1) ^ σ)⁻¹ = u ^ (-σ) * B q.1 ^ σ := by
        rw [Real.div_rpow hu.le hq.le, inv_div, Real.rpow_neg hu.le]
        ring
      have hd : ‖normDeriv j (fc ℓ v0) (z q)‖ ≤
          M ℓ * (u ^ (-σ) * B q.1 ^ σ) := by
        rw [← hweight, ← div_eq_mul_inv]
        exact (le_div_iff₀ (Real.rpow_pos_of_pos hrad σ)).mpr hlocal
      calc
        R q ≤ (M ℓ * (u ^ (-σ) * B q.1 ^ σ)) * N ℓ q.1 :=
          mul_le_mul_of_nonneg_right hd (hNnonneg ℓ _)
        _ = (M ℓ * u ^ (-σ)) * G ℓ q.1 := by rw [hGfactor]; ring
    have hmajor : Integrable (fun q : P × ℝ => (M ℓ * u ^ (-σ)) * G ℓ q.1) (ν.prod η) :=
      ((hGi ℓ).comp_fst η).const_mul _
    have hRi : Integrable R (ν.prod η) := by
      apply hmajor.mono' hRmeas
      filter_upwards [hRbound] with q hq
      rwa [Real.norm_eq_abs, abs_of_nonneg (hRnonneg q)]
    have hRci : Integrable (fun q => (R q : ℂ)) (ν.prod η) := hRi.ofReal
    have hfree (p : P) (θ : ℝ) :
        (∏ w ∈ Finset.univ.erase v0, ‖fc ℓ w ((sheetPoint S v0 u p θ).2 w)‖) =
          ∏ w : W, ‖fc ℓ w.1 (p.2 w)‖ := by
      rw [Finset.prod_subtype (p := fun w : InfinitePlace F => w ≠ v0)
        (Finset.univ.erase v0) (by simp [ne_comm])]
      apply Finset.prod_congr rfl
      intro w hw
      simp only [sheetPoint, dite_eq_right w.property]
    have hRpoint (p : P) (θ : ℝ) :
        ((‖normDeriv j (fc ℓ v0) ((sheetPoint S v0 u p θ).2 v0)‖ *
          (∏ w ∈ Finset.univ.erase v0, ‖fc ℓ w ((sheetPoint S v0 u p θ).2 w)‖) *
            ∏ v : S.Sf, ‖ff ℓ v ((sheetPoint S v0 u p θ).1 v)‖ : ℝ) : ℂ) =
            (R (p, θ) : ℂ) := by
      rw [hfree]
      simp only [sheetPoint, R, z, N,
        ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint, B]
      push_cast
      ring
    have hid : (sheetInt S μ v0 (fun y => ((‖normDeriv j (fc ℓ v0) (y.2 v0)‖ *
        (∏ w ∈ Finset.univ.erase v0, ‖fc ℓ w (y.2 w)‖) *
          ∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖ : ℝ) : ℂ)) u).re = ∫ q, R q ∂ν.prod η := by
      simp only [sheetInt, hRpoint]
      change (∫ p, ∫ θ, (R (p, θ) : ℂ) ∂η ∂ν).re = _
      rw [← integral_prod _ hRci, integral_complex_ofReal, Complex.ofReal_re]
    dsimp only
    rw [hid]
    refine ⟨integral_nonneg hRnonneg, ?_⟩
    calc
      _ ≤ ∫ q : P × ℝ, (M ℓ * u ^ (-σ)) * G ℓ q.1 ∂ν.prod η :=
        integral_mono_ae hRi hmajor hRbound
      _ = C ℓ * u ^ (-σ) := by
        rw [integral_const_mul, integral_fun_fst]
        have hη : η.real Set.univ = 1 := by
          simp [η, Measure.real, Real.volume_Ioc]
        rw [hη, one_smul]
        rw [← hGval ℓ]
        ring
  refine ⟨∑ ℓ : Fin J, C ℓ, Finset.sum_nonneg fun ℓ _ => hCnonneg ℓ, ?_⟩
  intro u hu
  constructor
  · exact Finset.sum_nonneg fun ℓ _ => (hsummand ℓ u hu).1
  · change (∑ ℓ : Fin J, _) ≤ _
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun ℓ _ => (hsummand ℓ u hu).2

set_option maxHeartbeats 2000000 in
private theorem thsol_profile_differentiation [IsTotallyComplex F]
    (μ : ∀ v : FinPlace F, LocHaar v) (v0 : InfinitePlace F)
    (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v))
    (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w)) (m : S.FS → ℂ) (hm : SheetMultiplier S m) :
    let Hf : ℝ → ℂ := sheetInt S μ v0 (fun y => m y * sumProd S J ff fc y)
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hf (Set.Ioi 0) ∧
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ (j : ℕ) (u : ℝ), 0 < u →
      ‖normDerivR j Hf u‖ ≤ Cm * absProfile S μ v0 J ff fc j u := by
  let Hf : ℝ → ℂ := sheetInt S μ v0 (fun y => m y * sumProd S J ff fc y)
  have hsub := ArtinPrimitiveRoots.Proofs.thsol_sheets.local_measure_substrate μ
  have : ∀ v : S.Sf, SigmaFinite (mulHaarFin (μ v.1)) := fun v => (hsub.1 v.1).2.2.2.2
  have : SigmaFinite mulHaarC := hsub.2.2
  let W := {w : InfinitePlace F // w ≠ v0}
  let P := (∀ v : S.Sf, v.1.adicCompletion F) × (W → ℂ)
  let ν : Measure P := (Measure.pi fun v : S.Sf => mulHaarFin (μ v.1)).prod
    (Measure.pi fun _ : W => mulHaarC)
  let η : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let Q := P × ℝ
  let ρ : Measure Q := ν.prod η
  let B : P → ℝ := fun p => (∏ v : S.Sf, absFin v.1 (p.1 v)) *
    ∏ w : W, Complex.normSq (p.2 w)
  obtain ⟨e, he, hpoint, hB, hpos⟩ := thsol_sheet_geometry S μ v0
  obtain ⟨Cm, hCm, hmBound, hmRad⟩ := thsol_multiplier_radial S m hm
  let m0 : S.FS → ℂ := fun y => if (∀ v : S.Sf, y.1 v ≠ 0) ∧
    (∀ w : InfinitePlace F, y.2 w ≠ 0) then m y else 0
  have hm0 : Measurable m0 := (thsol_multiplier_measurable S m hm).2
  let z0 : Q → ℂ := fun q =>
    ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint (1 / B q.1, q.2)
  let z : ℝ → Q → ℂ := fun t q => (Real.exp (t / 2) : ℂ) * z0 q
  let Y : ℝ → Q → S.FS := fun t q => sheetPoint S v0 (Real.exp t) q.1 q.2
  let Y0 : Q → S.FS := fun q => sheetPoint S v0 1 q.1 q.2
  have hz0meas : Measurable z0 :=
    ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_polar_measurePreserving.measurable.comp
      ((measurable_const.div (hB.comp measurable_fst)).prodMk measurable_snd)
  have hY0meas : Measurable Y0 := by
    have hme := e.measurable.comp (measurable_fst.prodMk hz0meas)
    have hEq : (fun q : Q => e (q.1, z0 q)) = Y0 := by
      funext q
      exact hpoint 1 q.1 q.2
    change Measurable (fun q : Q => e (q.1, z0 q)) at hme
    rwa [hEq] at hme
  have hzmeas (t : ℝ) : Measurable (z t) := measurable_const.mul hz0meas
  have hamp (t b : ℝ) : Real.sqrt (Real.exp t / b) =
      Real.exp (t / 2) * Real.sqrt (1 / b) := by
    have hexp : Real.exp t = Real.exp (t / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hs : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
      rw [hexp, Real.sqrt_sq (Real.exp_pos _).le]
    rw [div_eq_mul_inv, Real.sqrt_mul (Real.exp_pos t).le, hs, one_div]
  have hYdep (t : ℝ) (q : Q) : (Y t q).2 v0 = z t q := by
    simp only [Y, sheetPoint, z, z0,
      ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint]
    change (Real.sqrt (Real.exp t / B q.1) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * q.2) =
      (Real.exp (t / 2) : ℂ) * ((Real.sqrt (1 / B q.1) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * q.2))
    rw [hamp]
    push_cast
    ring
  have hY0dep (q : Q) : (Y0 q).2 v0 = z0 q := by
    simpa only [Y, Real.exp_zero, z, zero_div, Complex.ofReal_one, one_mul] using hYdep 0 q
  have hz0ne (q : Q) (hp : 0 < B q.1) : z0 q ≠ 0 := by
    unfold z0 ArtinPrimitiveRoots.Proofs.thsol_sheets.complexPolarPoint
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (one_div_pos.mpr hp)).ne')
      (Complex.exp_ne_zero _)
  have hregular (q : Q) (hp : 0 < B q.1) :
      (∀ v : S.Sf, (Y0 q).1 v ≠ 0) ∧ ∀ w : InfinitePlace F, (Y0 q).2 w ≠ 0 := by
    have hfn : (∏ v : S.Sf, absFin v.1 (q.1.1 v)) ≠ 0 :=
      (mul_ne_zero_iff.mp hp.ne').1
    have hcn : (∏ w : W, Complex.normSq (q.1.2 w)) ≠ 0 :=
      (mul_ne_zero_iff.mp hp.ne').2
    constructor
    · intro v
      have hv := Finset.prod_ne_zero_iff.mp hfn v (Finset.mem_univ v)
      rw [absFin_eq_norm] at hv
      exact norm_ne_zero_iff.mp hv
    · intro w
      by_cases hw : w = v0
      · subst w
        rw [hY0dep]
        exact hz0ne q hp
      · have hn := Finset.prod_ne_zero_iff.mp hcn ⟨w, hw⟩ (Finset.mem_univ _)
        have hc : q.1.2 ⟨w, hw⟩ ≠ 0 := by
          intro hz
          exact hn (by simp only [hz, map_zero])
        simpa only [Y0, sheetPoint, dite_eq_right hw] using hc
  have hunit (q : Q) (hp : 0 < B q.1) : IsUnit (Y0 q) := by
    have hr := hregular q hp
    refine ⟨⟨Y0 q, ((fun v => ((Y0 q).1 v)⁻¹), (fun w => ((Y0 q).2 w)⁻¹)), ?_, ?_⟩, rfl⟩
    · apply Prod.ext
      · funext v
        exact mul_inv_cancel₀ (hr.1 v)
      · funext w
        exact mul_inv_cancel₀ (hr.2 w)
    · apply Prod.ext
      · funext v
        exact inv_mul_cancel₀ (hr.1 v)
      · funext w
        exact inv_mul_cancel₀ (hr.2 w)
  have hm0eq (q : Q) (hp : 0 < B q.1) : m0 (Y0 q) = m (Y0 q) :=
    ite_eq_left (hregular q hp)
  have hm0Bound (q : Q) (hp : 0 < B q.1) : ‖m0 (Y0 q)‖ ≤ Cm := by
    obtain ⟨y, hy⟩ := hunit q hp
    rw [hm0eq q hp, ← hy]
    exact hmBound y
  have hmRay (q : Q) (hp : 0 < B q.1) (t : ℝ) : m (Y t q) = m0 (Y0 q) := by
    obtain ⟨y, hy⟩ := hunit q hp
    let a : ℂˣ := Units.mk0 (Real.exp (t / 2) : ℂ)
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
    have hmul : ((y * S.atComplex v0 a) : S.FS) = Y t q := by
      apply Prod.ext
      · funext v
        simp only [SData.atComplex, Prod.fst_mul, Pi.mul_apply,
          Units.val_mk, mul_one, hy, Y0, Y, sheetPoint]
      · funext w
        by_cases hw : w = v0
        · subst w
          simp only [SData.atComplex, Prod.snd_mul, Pi.mul_apply, Units.val_mk,
            Function.update_self, a, Units.val_mk0]
          change ((y : S.FS).2 v0) * (Real.exp (t / 2) : ℂ) = (Y t q).2 v0
          rw [hy, hY0dep, hYdep]
          dsimp only [z]
          exact mul_comm _ _
        · simp only [SData.atComplex, Prod.snd_mul, Pi.mul_apply,
            Units.val_mk, Function.update_of_ne hw, mul_one, hy,
            Y0, Y, sheetPoint, dite_eq_right hw]
    have hmR := hmRad v0 y (t / 2)
    change m ((y * S.atComplex v0 a) : S.FS) = m (y : S.FS) at hmR
    rw [hmul, hy] at hmR
    exact hmR.trans (hm0eq q hp).symm
  have hp : ∀ᵐ q ∂ρ, 0 < B q.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := η)).ae hpos
  have hfree (M : Type) [CommMonoid M] (g : InfinitePlace F → ℂ → M)
      (u : ℝ) (p : P) (θ : ℝ) :
      (∏ w ∈ Finset.univ.erase v0, g w ((sheetPoint S v0 u p θ).2 w)) =
        ∏ w : W, g w.1 (p.2 w) := by
    rw [Finset.prod_subtype (p := fun w : InfinitePlace F => w ≠ v0)
      (Finset.univ.erase v0) (by simp [ne_comm])]
    apply Finset.prod_congr rfl
    intro w hw
    simp only [sheetPoint, dite_eq_right w.property]
  have hfmeas (ℓ : Fin J) (v : S.Sf) : Measurable (ff ℓ v) := by
    apply measurable_of_continuousOn_compl_singleton (0 : v.1.adicCompletion F)
    intro x hx
    have hx0 : x ≠ 0 := by simpa using hx
    obtain ⟨U, hU, hxU, heq⟩ := (hff ℓ v).1 x hx0
    have hE : (fun _ => ff ℓ v x) =ᶠ[𝓝 x] ff ℓ v := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact (heq y hy).symm
    exact (continuousAt_const.congr hE).continuousWithinAt
  have hcmeas (ℓ : Fin J) (w : InfinitePlace F) (j : ℕ) :
      Measurable (normDeriv j (fc ℓ w)) :=
    measurable_of_continuousOn_compl_singleton (0 : ℂ)
      (ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_normDeriv_contDiff
        (fc ℓ w) (hfc ℓ w).1 j).continuousOn
  have hfcmeas (ℓ : Fin J) (w : InfinitePlace F) : Measurable (fc ℓ w) := by
    have hzero : normDeriv 0 (fc ℓ w) = fc ℓ w := by
      funext x
      simp only [normDeriv, iteratedDeriv_zero, zero_div, Real.exp_zero,
        Complex.ofReal_one, one_mul]
    simpa only [hzero] using hcmeas ℓ w 0
  let A (ℓ : Fin J) (p : P) : ℂ :=
    (∏ v : S.Sf, ff ℓ v (p.1 v)) * ∏ w : W, fc ℓ w.1 (p.2 w)
  let N (ℓ : Fin J) (p : P) : ℝ :=
    (∏ v : S.Sf, ‖ff ℓ v (p.1 v)‖) * ∏ w : W, ‖fc ℓ w.1 (p.2 w)‖
  have hAmeas (ℓ : Fin J) : Measurable (A ℓ) := by
    apply Measurable.mul
    · exact Finset.measurable_fun_prod Finset.univ fun v hv =>
        (hfmeas ℓ v).comp ((measurable_pi_apply v).comp measurable_fst)
    · exact Finset.measurable_fun_prod Finset.univ fun w hw =>
        (hfcmeas ℓ w.1).comp ((measurable_pi_apply w).comp measurable_snd)
  have hAnorm (ℓ : Fin J) (p : P) : ‖A ℓ p‖ = N ℓ p := by
    simp only [A, N, norm_mul, norm_prod]
  have hNmeas (ℓ : Fin J) : Measurable (N ℓ) := by
    simpa only [hAnorm] using (hAmeas ℓ).norm
  have hNnonneg (ℓ : Fin J) (p : P) : 0 ≤ N ℓ p := by
    rw [← hAnorm]
    exact norm_nonneg _
  have hNi (ℓ : Fin J) : Integrable (N ℓ) ν := by
    have hfI (v : S.Sf) : Integrable (fun x => ‖ff ℓ v x‖) (mulHaarFin (μ v.1)) := by
      simpa only [Real.rpow_zero, mul_one, mulHaarFin] using!
        ArtinPrimitiveRoots.Proofs.thsol_sheets.finite_factor_weighted_integrable
          (μ v.1) δ 0 (by linarith only [hδ]) (ff ℓ v) (hff ℓ v)
    have hcI (w : W) : Integrable (fun x => ‖fc ℓ w.1 x‖) mulHaarC := by
      simpa only [Real.rpow_zero, mul_one, normDeriv, iteratedDeriv_zero,
        zero_div, Real.exp_zero, Complex.ofReal_one, one_mul, mulHaarC] using!
        (ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_factor_weighted
          δ 0 (by linarith only [hδ]) (fc ℓ w.1) (hfc ℓ w.1) 0).1
    exact (Integrable.fintype_prod_dep hfI).mul_prod (Integrable.fintype_prod hcI)
  choose M hM hMb using fun (j : ℕ) (ℓ : Fin J) =>
    (ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_factor_weighted
      δ 0 (by linarith only [hδ]) (fc ℓ v0) (hfc ℓ v0) j).2
  have hDbound (j : ℕ) (ℓ : Fin J) (q : Q) (hq : 0 < B q.1) (t : ℝ) :
      ‖normDeriv j (fc ℓ v0) (z t q)‖ ≤ M j ℓ := by
    have hz : z t q ≠ 0 := mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) (hz0ne q hq)
    simpa only [Real.rpow_zero, mul_one] using hMb j ℓ (z t q) hz
  let R (ℓ : Fin J) (j : ℕ) (t : ℝ) (q : Q) : ℝ :=
    ‖normDeriv j (fc ℓ v0) (z t q)‖ * N ℓ q.1
  let D (j : ℕ) (t : ℝ) (q : Q) : ℂ := m0 (Y0 q) *
    ∑ ℓ : Fin J, A ℓ q.1 * normDeriv j (fc ℓ v0) (z t q)
  have hRmeas (ℓ : Fin J) (j : ℕ) (t : ℝ) : Measurable (R ℓ j t) :=
    ((hcmeas ℓ v0 j).comp (hzmeas t)).norm.mul
      ((hNmeas ℓ).comp measurable_fst)
  have hRnonneg (ℓ : Fin J) (j : ℕ) (t : ℝ) (q : Q) : 0 ≤ R ℓ j t q :=
    mul_nonneg (norm_nonneg _) (hNnonneg ℓ _)
  have hRi (ℓ : Fin J) (j : ℕ) (t : ℝ) : Integrable (R ℓ j t) ρ := by
    apply (((hNi ℓ).comp_fst η).const_mul (M j ℓ)).mono' (hRmeas ℓ j t).aestronglyMeasurable
    filter_upwards [hp] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (hRnonneg ℓ j t q)]
    exact mul_le_mul_of_nonneg_right (hDbound j ℓ q hq t) (hNnonneg ℓ _)
  have hRsumi (j : ℕ) (t : ℝ) : Integrable (fun q => ∑ ℓ : Fin J, R ℓ j t q) ρ :=
    integrable_finsetSum Finset.univ fun ℓ hℓ => hRi ℓ j t
  have hDmeas (j : ℕ) (t : ℝ) : AEStronglyMeasurable (D j t) ρ := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul (hm0.comp hY0meas)
    exact Finset.measurable_fun_sum Finset.univ fun ℓ hℓ =>
      ((hAmeas ℓ).comp measurable_fst).mul ((hcmeas ℓ v0 j).comp (hzmeas t))
  have hDabs (j : ℕ) (t : ℝ) (q : Q) (hq : 0 < B q.1) :
      ‖D j t q‖ ≤ Cm * ∑ ℓ : Fin J, R ℓ j t q := by
    calc
      ‖D j t q‖ = ‖m0 (Y0 q)‖ * ‖∑ ℓ : Fin J, A ℓ q.1 * normDeriv j (fc ℓ v0) (z t q)‖ := norm_mul _ _
      _ ≤ Cm * ‖∑ ℓ : Fin J, A ℓ q.1 * normDeriv j (fc ℓ v0) (z t q)‖ :=
        mul_le_mul_of_nonneg_right (hm0Bound q hq) (norm_nonneg _)
      _ ≤ Cm * ∑ ℓ : Fin J, ‖A ℓ q.1 * normDeriv j (fc ℓ v0) (z t q)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hCm
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        rw [norm_mul, hAnorm]
        exact mul_comm _ _
  have hDcommon (j : ℕ) : ∃ b : Q → ℝ, Integrable b ρ ∧
      ∀ᵐ q ∂ρ, ∀ t, ‖D j t q‖ ≤ b q := by
    refine ⟨fun q => Cm * ∑ ℓ : Fin J, M j ℓ * N ℓ q.1, ?_, ?_⟩
    · exact (integrable_finsetSum Finset.univ fun ℓ hℓ =>
        ((hNi ℓ).comp_fst η).const_mul (M j ℓ)).const_mul Cm
    · filter_upwards [hp] with q hq
      intro t
      apply (hDabs j t q hq).trans
      apply mul_le_mul_of_nonneg_left _ hCm
      apply Finset.sum_le_sum
      intro ℓ hℓ
      exact mul_le_mul_of_nonneg_right (hDbound j ℓ q hq t) (hNnonneg ℓ _)
  have hDder (j : ℕ) : ∀ᵐ q ∂ρ, ∀ t,
      HasDerivAt (fun s : ℝ => D j s q) (D (j + 1) t q) t := by
    filter_upwards [hp] with q hq
    intro t
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro ℓ hℓ
    exact (ArtinPrimitiveRoots.Proofs.thsol_sheets.complex_normDeriv_hasDerivAt
      (fc ℓ v0) (hfc ℓ v0).1 j (z0 q) (hz0ne q hq) t).const_mul (A ℓ q.1)
  obtain ⟨hDi, hSmooth, hDId⟩ := ArtinPrimitiveRoots.Proofs.thsol_sheets.radial_integral_smooth
    ρ D hDmeas hDder hDcommon
  have hSum0 (t : ℝ) (q : Q) : sumProd S J ff fc (Y t q) =
      ∑ ℓ : Fin J, A ℓ q.1 * normDeriv 0 (fc ℓ v0) (z t q) := by
    unfold sumProd
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [← Finset.mul_prod_erase Finset.univ (fun w => fc ℓ w ((Y t q).2 w)) (Finset.mem_univ v0)]
    rw [hYdep]
    have hfcFree := hfree ℂ (fc ℓ) (Real.exp t) q.1 q.2
    change (∏ v : S.Sf, ff ℓ v (q.1.1 v)) *
      (fc ℓ v0 (z t q) * ∏ w ∈ Finset.univ.erase v0, fc ℓ w ((Y t q).2 w)) = _
    rw [hfcFree]
    simp only [A, normDeriv, iteratedDeriv_zero, zero_div, Real.exp_zero,
      Complex.ofReal_one, one_mul]
    ring
  have hD0 (t : ℝ) : ∀ᵐ q ∂ρ,
      D 0 t q = m (Y t q) * sumProd S J ff fc (Y t q) := by
    filter_upwards [hp] with q hq
    rw [hSum0, hmRay q hq t]
  have hH (t : ℝ) : Hf (Real.exp t) = ∫ q, D 0 t q ∂ρ := by
    have hiActual : Integrable (fun q => m (Y t q) * sumProd S J ff fc (Y t q)) ρ :=
      (hDi 0 t).congr (hD0 t)
    change (∫ p, ∫ θ, m (sheetPoint S v0 (Real.exp t) p θ) *
      sumProd S J ff fc (sheetPoint S v0 (Real.exp t) p θ) ∂η ∂ν) = _
    rw [← integral_prod _ hiActual]
    exact integral_congr_ae (Filter.EventuallyEq.symm (hD0 t))
  have hHfun : (fun t : ℝ => Hf (Real.exp t)) = fun t : ℝ => ∫ q, D 0 t q ∂ρ :=
    funext hH
  have hHs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => Hf (Real.exp t)) := by
    rw [hHfun]
    exact hSmooth
  have hOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hf (Set.Ioi 0) := by
    have hlog : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.log (Set.Ioi 0) :=
      Real.contDiffOn_log.mono fun u hu => by simpa using hu.ne'
    have hc := hHs.comp_contDiffOn hlog
    apply hc.congr
    intro u hu
    exact congrArg Hf (Real.exp_log hu).symm
  have hAbs (j : ℕ) (t : ℝ) : absProfile S μ v0 J ff fc j (Real.exp t) =
      ∫ q, ∑ ℓ : Fin J, R ℓ j t q ∂ρ := by
    have hs (ℓ : Fin J) :
        (sheetInt S μ v0 (fun y => ((‖normDeriv j (fc ℓ v0) (y.2 v0)‖ *
          (∏ w ∈ Finset.univ.erase v0, ‖fc ℓ w (y.2 w)‖) *
            ∏ v : S.Sf, ‖ff ℓ v (y.1 v)‖ : ℝ) : ℂ)) (Real.exp t)).re = ∫ q, R ℓ j t q ∂ρ := by
      have hRP (p : P) (θ : ℝ) :
          ((‖normDeriv j (fc ℓ v0) ((sheetPoint S v0 (Real.exp t) p θ).2 v0)‖ *
            (∏ w ∈ Finset.univ.erase v0, ‖fc ℓ w ((sheetPoint S v0 (Real.exp t) p θ).2 w)‖) *
              ∏ v : S.Sf, ‖ff ℓ v ((sheetPoint S v0 (Real.exp t) p θ).1 v)‖ : ℝ) : ℂ) = (R ℓ j t (p, θ) : ℂ) := by
        change ((‖normDeriv j (fc ℓ v0) ((Y t (p, θ)).2 v0)‖ *
          (∏ w ∈ Finset.univ.erase v0, ‖fc ℓ w ((Y t (p, θ)).2 w)‖) *
            ∏ v : S.Sf, ‖ff ℓ v ((Y t (p, θ)).1 v)‖ : ℝ) : ℂ) = _
        rw [hYdep, hfree ℝ (fun w z => ‖fc ℓ w z‖) (Real.exp t) p θ]
        simp only [Y, sheetPoint, R, N]
        push_cast
        ring
      simp only [sheetInt, hRP]
      change (∫ p, ∫ θ, (R ℓ j t (p, θ) : ℂ) ∂η ∂ν).re = _
      have hRci : Integrable (fun q : Q => (R ℓ j t q : ℂ)) ρ := (hRi ℓ j t).ofReal
      rw [← integral_prod (fun q : Q => (R ℓ j t q : ℂ)) hRci,
        integral_complex_ofReal, Complex.ofReal_re]
    unfold absProfile
    simp_rw [hs]
    exact (integral_finsetSum Finset.univ fun ℓ hℓ => hRi ℓ j t).symm
  refine ⟨hOn, Cm, hCm, ?_⟩
  intro j u hu
  change ‖iteratedDeriv j (fun t : ℝ => Hf (Real.exp t)) (Real.log u)‖ ≤ _
  rw [hHfun, hDId j (Real.log u)]
  calc
    _ ≤ ∫ q, ‖D j (Real.log u) q‖ ∂ρ := norm_integral_le_integral_norm _
    _ ≤ ∫ q, Cm * ∑ ℓ : Fin J, R ℓ j (Real.log u) q ∂ρ := by
      apply integral_mono_ae (hDi j (Real.log u)).norm ((hRsumi j (Real.log u)).const_mul Cm)
      exact hp.mono fun q hq => hDabs j (Real.log u) q hq
    _ = Cm * absProfile S μ v0 J ff fc j u := by
      rw [integral_const_mul, ← hAbs j (Real.log u), Real.exp_log hu]

/-- **lem:sheet-profile** (03:500–620), profile part: smoothness, eq:sheet-weighted-bound,
eq:sheet-two-ended-bound, with an admissible multiplier. C4 of `sol-gate-theta` carries its norm
constant into the exact majorant; C9 uses the retained C-infinity hypothesis. -/
theorem sheet_profile [IsTotallyComplex F] (μ : ∀ v : FinPlace F, LocHaar v) (v0 : InfinitePlace F)
    (δ : ℝ) (hδ : 0 < δ) (J : ℕ) (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ) (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v))
    (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w)) (m : S.FS → ℂ) (hm : SheetMultiplier S m) :
    let Hf : ℝ → ℂ := sheetInt S μ v0 (fun y => m y * sumProd S J ff fc y)
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hf (Set.Ioi 0) ∧
    (∃ Cm : ℝ, 0 ≤ Cm ∧
      ∀ (j : ℕ) (σ : ℝ), -δ < σ → ∃ C : ℝ, ∀ u : ℝ, 0 < u →
        ‖normDerivR j Hf u‖ ≤ Cm * absProfile S μ v0 J ff fc j u ∧
          absProfile S μ v0 J ff fc j u ≤ C * u ^ (-σ)) ∧
    (∀ (j : ℕ) (α A : ℝ), 0 < α → α < δ → 0 < A → ∃ C : ℝ, ∀ u : ℝ, 0 < u →
      ‖normDerivR j Hf u‖ + absProfile S μ v0 J ff fc j u ≤ C * min (u ^ α) (u ^ (-A))) := by
  sorry

/-- Absolute Mellin moments `M_β(𝒦) = ∫_0^∞ |𝒦(T)| T^β dT/T`. -/
def absMoment (K : ℝ → ℂ) (β : ℝ) : ℝ := ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * T ^ β / T

/-- **lem:sheet-profile**, convolution part: for a kernel with all moments finite, both
convolutions `∫𝒦(T)H(uT^{±1})dT/T` and their absolute majorants obey the two-ended bound; and
eq:sheet-absolute-sum. C9 of `sol-gate-theta` keeps the already C-infinity `SheetHypC` input.
Kernel measurability is required per `sol-thin-thglobal` for dominated differentiation. -/
theorem sheet_profile_convolution [IsTotallyComplex F] (μ : ∀ v : FinPlace F, LocHaar v)
    (v0 : InfinitePlace F) (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ) (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v)) (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w))
    (m : S.FS → ℂ) (hm : SheetMultiplier S m) (K : ℝ → ℂ)
    (hKmeas : AEStronglyMeasurable K (volume.restrict (Set.Ioi (0 : ℝ))))
    (hK : ∀ β : ℝ, IntegrableOn (fun T => ‖K T‖ * T ^ β / T) (Set.Ioi 0)) :
    let Hf : ℝ → ℂ := sheetInt S μ v0 (fun y => m y * sumProd S J ff fc y)
    (∀ (τ : ℤ), (τ = 1 ∨ τ = -1) → ∀ (j : ℕ) (α A : ℝ), 0 < α → α < δ → 0 < A →
      ∃ C : ℝ, ∀ u : ℝ, 0 < u →
        ‖normDerivR j (fun u' => ∫ T in Set.Ioi (0 : ℝ), K T * Hf (u' * T ^ τ) / T) u‖ +
          ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * absProfile S μ v0 J ff fc j (u * T ^ τ) / T ≤
        C * min (u ^ α) (u ^ (-A))) ∧
    (∀ (σ : ℝ), -δ < σ → ∃ C : ℝ, ∀ (τ : ℤ), (τ = 1 ∨ τ = -1) → ∀ (ι : Type) (x : ι → ℝ)
      (a : ι → ℂ), (∀ i, 0 < x i) → Summable (fun i => ‖a i‖ * x i ^ (-σ)) → ∀ u : ℝ, 0 < u →
        ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ *
            (∑' i, ‖a i‖ * absProfile S μ v0 J ff fc 0 (u * x i * T ^ τ)) / T ≤
          C * u ^ (-σ) * absMoment K (-(τ : ℝ) * σ) * ∑' i, ‖a i‖ * x i ^ (-σ)) := by
  sorry

/-- **eq:sheet-fourier-separation** (03:622–640): for `ρ ∈ C_c^∞(ℝ)` and a convolved profile `Φ`
obeying the two-ended bound with its first two derivatives, the Fourier transform of
`t ↦ ρ(t)Φ(ue^t)` has `L¹` norm `≤ C min(u^α, u^{-A})`. C9 of `sol-gate-theta` requires a
C-infinity cutoff. -/
theorem sheet_fourier_separation (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (Φ : ℝ → ℂ) (α : ℝ) (hα : 0 < α)
    (hΦ : ∀ (j : ℕ), j ≤ 2 → ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ u : ℝ, 0 < u →
      ‖normDerivR j Φ u‖ ≤ C * min (u ^ α) (u ^ (-A)))
    (hΦs : ContDiffOn ℝ 2 Φ (Set.Ioi 0)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ u : ℝ, 0 < u →
      ∫ ξ : ℝ, ‖𝓕 (fun t : ℝ => ρ t * Φ (u * Real.exp t)) ξ‖ ≤
        C * min (u ^ α) (u ^ (-A)) := by
  sorry

/-- **eq:theta-V-profile** (03:661–669): the radial profile of the chosen S-function (T5 without
its angular characters), with the cutoff `U` and constants `cS`. -/
def thetaV (μ : ∀ v : FinPlace F, LocHaar v) (v0 : InfinitePlace F)
    (U : Set (∀ v : S.Sf, v.1.adicCompletion F)) (cS : InfinitePlace F → ℝ) (u : ℝ) : ℂ :=
  sheetInt S μ v0 (fun y => (if y.1 ∈ U then (1 : ℂ) else 0) *
    ∏ w : InfinitePlace F, ((Complex.normSq (y.2 w) : ℝ) : ℂ) *
      (besselK (1 / 3) (cS w * ‖y.2 w‖) : ℂ)) u

/-- **lem:gaussian-smoothing** (03:671–775), for `U` as in `U_spec` (open compact, local units)
and `cS > 0`: (i) `V̂(s) = C₀A₀^s[Γ(s+5/6)Γ(s+7/6)]^r` for `Re s > -5/6`; (ii) a kernel `𝒦` with
`|(T∂_T)^j 𝒦| ≤ C min(T^N, T^{-N})`, `∫𝒦(T)V(uT)dT/T = P_G(u)`, and `𝒦̂(-s) = e^{s²}/V̂(s)`. C9
of `sol-gate-theta` states generic smoothness with C-infinity regularity. -/
theorem gaussian_smoothing [IsTotallyComplex F] (μ : ∀ v : FinPlace F, LocHaar v)
    (v0 : InfinitePlace F) (U : Set (∀ v : S.Sf, v.1.adicCompletion F)) (hUo : IsOpen U)
    (hUc : IsCompact U) (hU1 : (1 : ∀ v : S.Sf, v.1.adicCompletion F) ∈ U)
    (hUunit : ∀ y ∈ U, ∀ v : S.Sf, Valued.v (y v) = 1)
    (cS : InfinitePlace F → ℝ) (hcS : ∀ w, 0 < cS w) :
    ∃ (C₀ A₀ : ℝ), 0 < C₀ ∧ 0 < A₀ ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        mellin (fun u : ℝ => thetaV S μ v0 U cS u) s =
          (C₀ : ℂ) * (A₀ : ℂ) ^ s *
            (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ numComplex F) ∧
      ∃ K : ℝ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K (Set.Ioi 0) ∧
        (∀ (N : ℝ) (j : ℕ), ∃ C : ℝ, ∀ T : ℝ, 0 < T →
          ‖normDerivR j K T‖ ≤ C * min (T ^ N) (T ^ (-N))) ∧
        (∀ u : ℝ, 0 < u →
          ∫ T in Set.Ioi (0 : ℝ), K T * thetaV S μ v0 U cS (u * T) / T = (PG u : ℂ)) ∧
        (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
          mellin K (-s) = Complex.exp (s ^ 2) / mellin (fun u : ℝ => thetaV S μ v0 U cS u) s) := by
  sorry

end AnalysisS

end ArtinPrimitiveRoots.A1.Theta
