import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.ReciprocalGamma
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.Quotient
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.Moments
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.Contour
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.LogKernel
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.Decay
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.PositiveKernel
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.MellinKernel
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.Convolution
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.LocalMellin
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.FiniteHaar
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.WeightedHaar
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.CutoffMass
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.ProductMellin
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.MeasureSubstrate
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.ComplexPolar
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.RadialScaling
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.ProductPolar
import ArtinPrimitiveRoots.Theta.Proofs.TH_S_CONV.FourierL1
import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».PowerClasses
import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».FiniteWeighted
import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».ComplexRadial
import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».ComplexWeighted
import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».Differentiation
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory Filter
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
  dsimp only
  obtain ⟨hs, Cm, hCm, hd⟩ := thsol_profile_differentiation S μ v0 δ hδ J ff fc hff hfc m hm
  refine ⟨hs, ⟨Cm, hCm, ?_⟩, ?_⟩
  · intro j σ hσ
    obtain ⟨C, _, hC⟩ := thsol_profile_weighted S μ v0 δ hδ J ff fc hff hfc j σ hσ
    exact ⟨C, fun u hu => ⟨hd j u hu, (hC u hu).2⟩⟩
  · intro j α A hα hαδ hA
    obtain ⟨C₁, hC₁, h₁⟩ :=
      thsol_profile_weighted S μ v0 δ hδ J ff fc hff hfc j (-α) (by linarith)
    obtain ⟨C₂, hC₂, h₂⟩ :=
      thsol_profile_weighted S μ v0 δ hδ J ff fc hff hfc j A (by linarith)
    refine ⟨(Cm + 1) * max C₁ C₂, ?_⟩
    intro u hu
    have hp₁ := (h₁ u hu).2
    simp only [neg_neg] at hp₁
    have hp₂ := (h₂ u hu).2
    have hc₁ : absProfile S μ v0 J ff fc j u ≤ max C₁ C₂ * u ^ α :=
      hp₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hu.le _))
    have hc₂ : absProfile S μ v0 J ff fc j u ≤ max C₁ C₂ * u ^ (-A) :=
      hp₂.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hu.le _))
    have hd' := hd j u hu
    have hm₁ : 0 ≤ Cm + 1 := by linarith
    rcases le_total (u ^ α) (u ^ (-A)) with h | h
    · rw [min_eq_left h]
      have := mul_le_mul_of_nonneg_left hc₁ hm₁
      nlinarith
    · rw [min_eq_right h]
      have := mul_le_mul_of_nonneg_left hc₂ hm₁
      nlinarith

/-- Absolute Mellin moments `M_β(𝒦) = ∫_0^∞ |𝒦(T)| T^β dT/T`. -/
def absMoment (K : ℝ → ℂ) (β : ℝ) : ℝ := ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * T ^ β / T

private theorem iteratedDeriv_log_scale (Φ : ℝ → ℂ) (u : ℝ) (hu : 0 < u)
    (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun z : ℝ => Φ (u * Real.exp z)) t =
      normDerivR j Φ (u * Real.exp t) := by
  let f : ℝ → ℂ := fun s => Φ (Real.exp s)
  have hfun : (fun z : ℝ => Φ (u * Real.exp z)) = fun z => f (Real.log u + z) := by
    funext z
    dsimp [f]
    congr 1
    rw [Real.exp_add, Real.exp_log hu]
  have hlog : Real.log (u * Real.exp t) = Real.log u + t := by
    rw [Real.log_mul (ne_of_gt hu) (ne_of_gt (Real.exp_pos t)), Real.log_exp]
  rw [hfun, iteratedDeriv_comp_const_add]
  simp [normDerivR, f, hlog]

private theorem sheetInt_nonneg_of_real_nonneg (μ : ∀ v : FinPlace F, LocHaar v)
    (v0 : InfinitePlace F) (f : S.FS → ℝ) (hf : ∀ y, 0 ≤ f y) (u : ℝ) :
    0 ≤ (sheetInt S μ v0 (fun y => (f y : ℂ)) u).re := by
  unfold sheetInt
  simp only [integral_complex_ofReal, RCLike.ofReal_re]
  apply integral_nonneg_of_ae
  filter_upwards with p
  apply integral_nonneg_of_ae
  exact Filter.Eventually.of_forall fun θ => hf (sheetPoint S v0 u p θ)

private theorem absProfile_nonneg (μ : ∀ v : FinPlace F, LocHaar v)
    (v0 : InfinitePlace F) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ) (j : ℕ) (u : ℝ) :
    0 ≤ absProfile S μ v0 J ff fc j u := by
  unfold absProfile
  apply Finset.sum_nonneg
  intro ℓ hℓ
  apply sheetInt_nonneg_of_real_nonneg S μ v0
  intro y
  positivity

private theorem real_rpow_zpow_mul (a T : ℝ) (ha : 0 < a) (hT : 0 < T)
    (τ : ℤ) (hτ : τ = 1 ∨ τ = -1) (β : ℝ) :
    (a * T ^ τ) ^ β = a ^ β * T ^ ((τ : ℝ) * β) := by
  rw [Real.mul_rpow ha.le (by positivity : 0 ≤ T ^ τ)]
  have hpow : (T ^ τ) ^ β = T ^ ((τ : ℝ) * β) := by
    rw [← Real.rpow_zpow_comm hT.le β τ]
    rcases hτ with h | h
    · subst τ
      norm_num
    · subst τ
      norm_num
      exact (Real.rpow_neg hT.le β).symm
  rw [hpow]

/-- **lem:sheet-profile**, convolution part: for a kernel with all moments finite, both
convolutions `∫𝒦(T)H(uT^{±1})dT/T` and their absolute majorants obey the two-ended bound; and
eq:sheet-absolute-sum. C9 of `sol-gate-theta` keeps the already C-infinity `SheetHypC` input.
Kernel measurability is required for dominated differentiation. -/
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
  let Hf : ℝ → ℂ := sheetInt S μ v0 (fun y => m y * sumProd S J ff fc y)
  obtain ⟨hHs, ⟨Cm, hCm, hCmW⟩, hTwo⟩ :=
    sheet_profile S μ v0 δ hδ J ff fc hff hfc m hm
  constructor
  · intro τ hτ j α A hα hαδ hA
    have hSep (n : ℕ) : ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ v : ℝ, 0 < v →
        ‖normDerivR n Hf v‖ ≤ Cn * min (v ^ α) (v ^ (-A)) ∧
          absProfile S μ v0 J ff fc n v ≤ Cn * min (v ^ α) (v ^ (-A)) := by
      obtain ⟨Cn, hCn⟩ := hTwo n α A hα hαδ hA
      have hCnnonneg : 0 ≤ Cn := by
        have h1 := hCn 1 (by norm_num)
        have hn : 0 ≤ ‖normDerivR n Hf 1‖ := norm_nonneg _
        have hp : 0 ≤ absProfile S μ v0 J ff fc n 1 :=
          absProfile_nonneg S μ v0 J ff fc n 1
        have h1' : ‖normDerivR n Hf 1‖ + absProfile S μ v0 J ff fc n 1 ≤ Cn := by
          simpa using h1
        linarith
      refine ⟨Cn, hCnnonneg, ?_⟩
      intro v hv
      have hp : 0 ≤ absProfile S μ v0 J ff fc n v :=
        absProfile_nonneg S μ v0 J ff fc n v
      have hn : 0 ≤ ‖normDerivR n Hf v‖ := norm_nonneg _
      have hh := hCn v hv
      exact ⟨by linarith, by linarith⟩
    let Dconst : ℕ → ℝ := fun n => Classical.choose (hSep n)
    have hDspec (n : ℕ) : 0 ≤ Dconst n ∧ ∀ v : ℝ, 0 < v →
        ‖normDerivR n Hf v‖ ≤ Dconst n * min (v ^ α) (v ^ (-A)) ∧
          absProfile S μ v0 J ff fc n v ≤ Dconst n * min (v ^ α) (v ^ (-A)) :=
      Classical.choose_spec (hSep n)
    let θ : ℝ := (τ : ℝ)
    let ψ : ℝ → ℂ := fun y => Hf (Real.exp y)
    have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
      simpa [ψ, Function.comp_def] using hHs.comp_contDiff
        (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => Real.exp y))
        (fun y => Real.exp_pos y)
    have hExpPowT (T q : ℝ) (hT : 0 < T) : Real.exp (q * Real.log T) = T ^ q := by
      rw [Real.rpow_def_of_pos hT]
      congr 1
      ring
    have hDpoint (n : ℕ) (x0 T : ℝ) (hT : 0 < T) :
        ‖iteratedDeriv n ψ (x0 + θ * Real.log T)‖ ≤
          Dconst n * (Real.exp (α * x0) * T ^ (θ * α) +
            Real.exp (-A * x0) * T ^ (-A * θ)) := by
      let y : ℝ := x0 + θ * Real.log T
      have hArg : normDerivR n Hf (Real.exp y) = iteratedDeriv n ψ y := by
        simp [normDerivR, ψ, Real.log_exp]
      have hbase : ‖iteratedDeriv n ψ y‖ ≤
          Dconst n * min ((Real.exp y) ^ α) ((Real.exp y) ^ (-A)) := by
        rw [← hArg]
        exact (hDspec n).2 (Real.exp y) (Real.exp_pos y) |>.1
      have hmin : min ((Real.exp y) ^ α) ((Real.exp y) ^ (-A)) ≤
          (Real.exp y) ^ α + (Real.exp y) ^ (-A) := by
        calc
          min ((Real.exp y) ^ α) ((Real.exp y) ^ (-A)) ≤ (Real.exp y) ^ α := min_le_left _ _
          _ ≤ (Real.exp y) ^ α + (Real.exp y) ^ (-A) :=
            le_add_of_nonneg_right (Real.rpow_nonneg (Real.exp_pos y).le _)
      have hpowα : (Real.exp y) ^ α = Real.exp (α * x0) * T ^ (θ * α) := by
        calc
          (Real.exp y) ^ α = Real.exp (α * y) := by
            rw [Real.rpow_def_of_pos (Real.exp_pos y)]
            simp [Real.log_exp, mul_comm]
          _ = Real.exp (α * x0) * Real.exp ((θ * α) * Real.log T) := by
            rw [show α * y = α * x0 + (θ * α) * Real.log T by dsimp [y]; ring,
              Real.exp_add]
          _ = Real.exp (α * x0) * T ^ (θ * α) := by rw [hExpPowT T (θ * α) hT]
      have hpowA : (Real.exp y) ^ (-A) = Real.exp (-A * x0) * T ^ (-A * θ) := by
        calc
          (Real.exp y) ^ (-A) = Real.exp ((-A) * y) := by
            rw [Real.rpow_def_of_pos (Real.exp_pos y)]
            simp [Real.log_exp, mul_comm]
          _ = Real.exp ((-A) * x0) * Real.exp ((-A * θ) * Real.log T) := by
            rw [show (-A) * y = (-A) * x0 + (-A * θ) * Real.log T by dsimp [y]; ring,
              Real.exp_add]
          _ = Real.exp (-A * x0) * T ^ (-A * θ) := by rw [hExpPowT T (-A * θ) hT]
      calc
        ‖iteratedDeriv n ψ y‖ ≤ Dconst n * min ((Real.exp y) ^ α) ((Real.exp y) ^ (-A)) := hbase
        _ ≤ Dconst n * ((Real.exp y) ^ α + (Real.exp y) ^ (-A)) :=
          mul_le_mul_of_nonneg_left hmin (hDspec n).1
        _ = Dconst n * (Real.exp (α * x0) * T ^ (θ * α) +
              Real.exp (-A * x0) * T ^ (-A * θ)) := by rw [hpowα, hpowA]
    let momentFun : ℝ → ℝ → ℝ := fun β T => ‖K T‖ * T ^ β / T
    have hMomInt (β : ℝ) : Integrable (momentFun β) (volume.restrict (Set.Ioi 0)) := by
      exact hK β
    let F : ℕ → ℝ → ℝ → ℂ := fun n x T =>
      (K T * (T : ℂ)⁻¹) * iteratedDeriv n ψ (x + θ * Real.log T)
    let G : ℕ → ℝ → ℂ := fun n x => ∫ T, F n x T ∂(volume.restrict (Set.Ioi 0))
    let boundAt : ℕ → ℝ → ℝ → ℝ := fun n x T =>
      Dconst n * (Real.exp (α * x) * momentFun (θ * α) T +
        Real.exp (-A * x) * momentFun (-A * θ) T)
    have hBoundAtInt (n : ℕ) (x0 : ℝ) :
        Integrable (boundAt n x0) (volume.restrict (Set.Ioi 0)) := by
      have h1 := (hMomInt (θ * α)).const_mul (Dconst n * Real.exp (α * x0))
      have h2 := (hMomInt (-A * θ)).const_mul (Dconst n * Real.exp (-A * x0))
      convert h1.add h2 using 1 <;> ext T <;> dsimp [boundAt] <;> ring
    have hFmeas (n : ℕ) (x0 : ℝ) :
        AEStronglyMeasurable (F n x0) (volume.restrict (Set.Ioi 0)) := by
      have hInvCont : ContinuousOn (fun T : ℝ => (T : ℂ)⁻¹) (Set.Ioi 0) := by
        exact Complex.continuous_ofReal.continuousOn.inv₀
          (fun T hT => Complex.ofReal_ne_zero.mpr hT.ne')
      have hInvMeas : AEStronglyMeasurable (fun T : ℝ => (T : ℂ)⁻¹)
          (volume.restrict (Set.Ioi 0)) :=
        hInvCont.aestronglyMeasurable (μ := volume) measurableSet_Ioi
      have hlogCont : ContinuousOn (fun T : ℝ => x0 + θ * Real.log T) (Set.Ioi 0) := by
        exact continuousOn_const.add (continuousOn_const.mul
          (Real.continuousOn_log.mono (fun T hT => ne_of_gt hT)))
      have hfacCont : ContinuousOn (fun T : ℝ => iteratedDeriv n ψ (x0 + θ * Real.log T))
          (Set.Ioi 0) := (hψ.continuous_iteratedDeriv n (by simp)).comp_continuousOn hlogCont
      have hfacMeas : AEStronglyMeasurable
          (fun T : ℝ => iteratedDeriv n ψ (x0 + θ * Real.log T))
          (volume.restrict (Set.Ioi 0)) :=
        hfacCont.aestronglyMeasurable (μ := volume) measurableSet_Ioi
      change AEStronglyMeasurable
        ((K * (fun T : ℝ => (T : ℂ)⁻¹)) *
          (fun T : ℝ => iteratedDeriv n ψ (x0 + θ * Real.log T)))
        (volume.restrict (Set.Ioi 0))
      exact (hKmeas.mul hInvMeas).mul hfacMeas
    have hFnormBound (n : ℕ) (x0 T : ℝ) (hT : 0 < T) :
        ‖F n x0 T‖ ≤ boundAt n x0 T := by
      have hD := hDpoint n x0 T hT
      have hcoeff : ‖K T * (T : ℂ)⁻¹‖ = ‖K T‖ / T := by
        simp [norm_mul, norm_inv, Real.norm_eq_abs, abs_of_pos hT]
        ring
      calc
        ‖F n x0 T‖ = (‖K T‖ / T) *
            ‖iteratedDeriv n ψ (x0 + θ * Real.log T)‖ := by
              calc
                ‖F n x0 T‖ = ‖K T * (T : ℂ)⁻¹‖ *
                    ‖iteratedDeriv n ψ (x0 + θ * Real.log T)‖ := by simp [F, norm_mul]
                _ = _ := by rw [hcoeff]
        _ ≤ (‖K T‖ / T) *
            (Dconst n * (Real.exp (α * x0) * T ^ (θ * α) +
              Real.exp (-A * x0) * T ^ (-A * θ))) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
        _ = boundAt n x0 T := by dsimp [boundAt, momentFun]; ring
    have hGint (n : ℕ) (x0 : ℝ) :
        Integrable (F n x0) (volume.restrict (Set.Ioi 0)) := by
      apply (hBoundAtInt n x0).mono' (hFmeas n x0)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
      exact hFnormBound n x0 T hT
    have hFderiv (n : ℕ) (x0 T : ℝ) :
        HasDerivAt (fun x => F n x T) (F (n + 1) x0 T) x0 := by
      let c : ℝ := θ * Real.log T
      have hDdiff : Differentiable ℝ (iteratedDeriv n ψ) :=
        hψ.differentiable_iteratedDeriv n
          (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
      have hAt : DifferentiableAt ℝ (iteratedDeriv n ψ) (x0 + c) := hDdiff.differentiableAt
      have hShift := hAt.hasDerivAt.comp_add_const x0 c
      have hShift' : HasDerivAt (fun x => iteratedDeriv n ψ (x + c))
          (iteratedDeriv (n + 1) ψ (x0 + c)) x0 := by
        simpa [iteratedDeriv_succ] using hShift
      simpa [F, c] using hShift'.const_mul (K T * (T : ℂ)⁻¹)
    have hGdiff (n : ℕ) (x0 : ℝ) : HasDerivAt (G n) (G (n + 1) x0) x0 := by
      let localBound : ℝ → ℝ := fun T =>
        Dconst (n + 1) *
          (Real.exp (α * x0 + α) * momentFun (θ * α) T +
            Real.exp (-A * x0 + A) * momentFun (-A * θ) T)
      have hLocalBoundInt : Integrable localBound (volume.restrict (Set.Ioi 0)) := by
        have h1 := (hMomInt (θ * α)).const_mul
          (Dconst (n + 1) * Real.exp (α * x0 + α))
        have h2 := (hMomInt (-A * θ)).const_mul
          (Dconst (n + 1) * Real.exp (-A * x0 + A))
        convert h1.add h2 using 1 <;> ext T <;> dsimp [localBound] <;> ring
      have hMeas : ∀ᶠ x in nhds x0,
          AEStronglyMeasurable (F n x) (volume.restrict (Set.Ioi 0)) :=
        Filter.Eventually.of_forall fun x => hFmeas n x
      have hBound : ∀ᵐ T ∂(volume.restrict (Set.Ioi 0)),
          ∀ x ∈ Metric.ball x0 1, ‖F (n + 1) x T‖ ≤ localBound T := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
        intro x hxball
        have hxabs : |x - x0| < 1 := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hxball
        have hxupper : x ≤ x0 + 1 := by
          have := (abs_lt.mp hxabs).2
          linarith
        have hxlower : x0 - 1 ≤ x := by
          have := (abs_lt.mp hxabs).1
          linarith
        have hexpα : Real.exp (α * x) ≤ Real.exp (α * x0 + α) := by
          apply Real.exp_le_exp.mpr
          calc
            α * x ≤ α * (x0 + 1) := mul_le_mul_of_nonneg_left hxupper hα.le
            _ = α * x0 + α := by ring
        have hexpA : Real.exp (-A * x) ≤ Real.exp (-A * x0 + A) := by
          apply Real.exp_le_exp.mpr
          calc
            (-A) * x ≤ (-A) * (x0 - 1) :=
              mul_le_mul_of_nonpos_left hxlower (by linarith)
            _ = -A * x0 + A := by ring
        have hD := hDpoint (n + 1) x T hT
        have hMomNonneg (β : ℝ) : 0 ≤ momentFun β T := by
          dsimp [momentFun]
          exact div_nonneg
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hT.le _)) hT.le
        have hsum : Real.exp (α * x) * momentFun (θ * α) T +
              Real.exp (-A * x) * momentFun (-A * θ) T ≤
            Real.exp (α * x0 + α) * momentFun (θ * α) T +
              Real.exp (-A * x0 + A) * momentFun (-A * θ) T :=
          add_le_add
            (mul_le_mul_of_nonneg_right hexpα (hMomNonneg (θ * α)))
            (mul_le_mul_of_nonneg_right hexpA (hMomNonneg (-A * θ)))
        calc
          ‖F (n + 1) x T‖ ≤ boundAt (n + 1) x T := hFnormBound (n + 1) x T hT
          _ ≤ localBound T := by
            dsimp [boundAt, localBound]
            exact mul_le_mul_of_nonneg_left hsum (hDspec (n + 1)).1
      have hFprimeMeas := hFmeas (n + 1) x0
      have hDiff : ∀ᵐ T ∂(volume.restrict (Set.Ioi 0)),
          ∀ x ∈ Metric.ball x0 1, HasDerivAt (F n · T) (F (n + 1) x T) x := by
        filter_upwards [] with T
        intro x hxball
        exact hFderiv n x T
      have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (Metric.ball_mem_nhds x0 one_pos) hMeas (hGint n x0) hFprimeMeas hBound hLocalBoundInt hDiff
      simpa [G] using hmain.2
    have hGderiv (n : ℕ) (x0 : ℝ) : deriv (G n) x0 = G (n + 1) x0 := by
      have h := (hGdiff n x0).deriv
      simpa [G] using h
    have hGiter (n : ℕ) : iteratedDeriv n (G 0) = G n := by
      induction n with
      | zero => exact iteratedDeriv_zero
      | succ n ih =>
          funext x0
          rw [iteratedDeriv_succ, ih]
          exact hGderiv n x0
    let Conv : ℝ → ℂ := fun v =>
      ∫ T in Set.Ioi (0 : ℝ), K T * Hf (v * T ^ τ) / T
    have hlogT (T : ℝ) : Real.log (T ^ τ) = θ * Real.log T := by
      simp [θ, Real.log_zpow]
    have hlogMul (v T : ℝ) (hv : 0 < v) (hT : 0 < T) :
        Real.log (v * T ^ τ) = Real.log v + θ * Real.log T := by
      calc
        Real.log (v * T ^ τ) = Real.log v + Real.log (T ^ τ) :=
          Real.log_mul (ne_of_gt hv) (zpow_ne_zero τ (ne_of_gt hT))
        _ = Real.log v + θ * Real.log T :=
          congrArg (fun z : ℝ => Real.log v + z) (hlogT T)
    have hexpMul (x0 T : ℝ) (hT : 0 < T) :
        Real.exp (x0 + θ * Real.log T) = Real.exp x0 * T ^ τ := by
      have hv : 0 < Real.exp x0 * T ^ τ := mul_pos (Real.exp_pos x0) (zpow_pos hT τ)
      have hlog := hlogMul (Real.exp x0) T (Real.exp_pos x0) hT
      have hlog' : Real.log (Real.exp x0 * T ^ τ) = x0 + θ * Real.log T := by
        calc
          Real.log (Real.exp x0 * T ^ τ) = Real.log (Real.exp x0) + θ * Real.log T := hlog
          _ = x0 + θ * Real.log T := by rw [Real.log_exp]
      calc
        Real.exp (x0 + θ * Real.log T) = Real.exp (Real.log (Real.exp x0 * T ^ τ)) := by
          rw [← hlog']
        _ = Real.exp x0 * T ^ τ := Real.exp_log hv
    have hG0conv (x0 : ℝ) : G 0 x0 = Conv (Real.exp x0) := by
      change ∫ T, F 0 x0 T ∂(volume.restrict (Set.Ioi (0 : ℝ))) =
        ∫ T in Set.Ioi (0 : ℝ), K T * Hf (Real.exp x0 * T ^ τ) / T
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
      have hF0 : F 0 x0 T = (K T * (T : ℂ)⁻¹) * Hf (Real.exp x0 * T ^ τ) := by
        simp [F, ψ, iteratedDeriv_zero, hexpMul x0 T hT]
      rw [hF0]
      ring
    have hDshift (n : ℕ) (v T : ℝ) (hv : 0 < v) (hT : 0 < T) :
        iteratedDeriv n ψ (Real.log v + θ * Real.log T) =
          normDerivR n Hf (v * T ^ τ) := by
      unfold normDerivR
      rw [hlogMul v T hv hT]
    have hGvalue (n : ℕ) (v : ℝ) (hv : 0 < v) :
        G n (Real.log v) =
          ∫ T in Set.Ioi (0 : ℝ), K T * normDerivR n Hf (v * T ^ τ) / T := by
      change ∫ T, F n (Real.log v) T ∂(volume.restrict (Set.Ioi (0 : ℝ))) = _
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
      have hD := hDshift n v T hv hT
      change (K T * (T : ℂ)⁻¹) * iteratedDeriv n ψ (Real.log v + θ * Real.log T) = _
      rw [hD]
      ring
    have hConvDerivative (n : ℕ) (v : ℝ) (hv : 0 < v) :
        normDerivR n Conv v = G n (Real.log v) := by
      unfold normDerivR
      have hfun : (fun x0 : ℝ => Conv (Real.exp x0)) = G 0 := by
        funext x0
        exact (hG0conv x0).symm
      rw [hfun, hGiter n]
    have hConvDerivativeNorm (n : ℕ) (v : ℝ) (hv : 0 < v) :
        ‖normDerivR n Conv v‖ ≤
          ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * ‖normDerivR n Hf (v * T ^ τ)‖ / T := by
      calc
        ‖normDerivR n Conv v‖ = ‖G n (Real.log v)‖ := by rw [hConvDerivative n v hv]
        _ = ‖∫ T, F n (Real.log v) T ∂(volume.restrict (Set.Ioi (0 : ℝ)) )‖ := rfl
        _ ≤ ∫ T, ‖F n (Real.log v) T‖ ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
          simpa using norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Ioi (0 : ℝ))) (F n (Real.log v))
        _ = ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ *
            ‖normDerivR n Hf (v * T ^ τ)‖ / T := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
          have hTpos : 0 < T := hT
          change ‖(K T * (T : ℂ)⁻¹) *
              iteratedDeriv n ψ (Real.log v + θ * Real.log T)‖ = _
          rw [hDshift n v T hv hTpos]
          simp [norm_mul, norm_inv, Real.norm_eq_abs, abs_of_pos hTpos]
          ring_nf
    have hAbsMomentNonneg (β : ℝ) : 0 ≤ absMoment K β := by
      change 0 ≤ ∫ T, momentFun β T ∂(volume.restrict (Set.Ioi 0))
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
      dsimp [momentFun]
      exact div_nonneg
        (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hT.le _)) hT.le
    have hIntegralMomentBound (β c : ℝ) (f : ℝ → ℝ)
        (hf0 : ∀ T, 0 < T → 0 ≤ f T)
        (hfBound : ∀ T, 0 < T → f T ≤ c * T ^ β) :
        ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * f T / T ∂volume ≤
          c * absMoment K β := by
      have hleftNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
          (fun T => ‖K T‖ * f T / T) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
        exact div_nonneg (mul_nonneg (norm_nonneg _) (hf0 T hT)) hT.le
      have hupperInt : Integrable (fun T : ℝ => c * momentFun β T)
          (volume.restrict (Set.Ioi 0)) := (hMomInt β).const_mul c
      have hpoint : (fun T : ℝ => ‖K T‖ * f T / T) ≤ᵐ[volume.restrict (Set.Ioi 0)]
          (fun T => c * momentFun β T) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
        have hmul := mul_le_mul_of_nonneg_left (hfBound T hT) (norm_nonneg (K T))
        calc
          ‖K T‖ * f T / T ≤ ‖K T‖ * (c * T ^ β) / T :=
            div_le_div_of_nonneg_right hmul hT.le
          _ = c * momentFun β T := by dsimp [momentFun]; ring
      calc
        ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * f T / T ∂volume ≤
            ∫ T, c * momentFun β T ∂(volume.restrict (Set.Ioi 0)) := by
              exact integral_mono_of_nonneg hleftNonneg hupperInt hpoint
        _ = c * absMoment K β := by
          change ∫ T, c * momentFun β T ∂(volume.restrict (Set.Ioi 0)) = _
          rw [integral_const_mul]
          rfl
    let βsmall : ℝ := θ * α
    let βlarge : ℝ := -A * θ
    let Msmall : ℝ := absMoment K βsmall
    let Mlarge : ℝ := absMoment K βlarge
    have hMsmall : 0 ≤ Msmall := hAbsMomentNonneg βsmall
    have hMlarge : 0 ≤ Mlarge := hAbsMomentNonneg βlarge
    refine ⟨2 * Dconst j * (Msmall + Mlarge), ?_⟩
    intro u hu
    have hpowSmall (T : ℝ) (hT : 0 < T) :
        (u * T ^ τ) ^ α = u ^ α * T ^ βsmall := by
      simpa [βsmall, θ] using real_rpow_zpow_mul u T hu hT τ hτ α
    have hpowLarge (T : ℝ) (hT : 0 < T) :
        (u * T ^ τ) ^ (-A) = u ^ (-A) * T ^ βlarge := by
      simpa [βlarge, θ, mul_comm] using real_rpow_zpow_mul u T hu hT τ hτ (-A)
    have hprofileSmall (T : ℝ) (hT : 0 < T) :
        absProfile S μ v0 J ff fc j (u * T ^ τ) ≤
          Dconst j * u ^ α * T ^ βsmall := by
      have hv : 0 < u * T ^ τ := mul_pos hu (zpow_pos hT τ)
      have hp := (hDspec j).2 (u * T ^ τ) hv |>.2
      calc
        absProfile S μ v0 J ff fc j (u * T ^ τ) ≤
            Dconst j * min ((u * T ^ τ) ^ α) ((u * T ^ τ) ^ (-A)) := hp
        _ ≤ Dconst j * (u * T ^ τ) ^ α :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (hDspec j).1
        _ = Dconst j * u ^ α * T ^ βsmall := by rw [hpowSmall T hT]; ring
    have hprofileLarge (T : ℝ) (hT : 0 < T) :
        absProfile S μ v0 J ff fc j (u * T ^ τ) ≤
          Dconst j * u ^ (-A) * T ^ βlarge := by
      have hv : 0 < u * T ^ τ := mul_pos hu (zpow_pos hT τ)
      have hp := (hDspec j).2 (u * T ^ τ) hv |>.2
      calc
        absProfile S μ v0 J ff fc j (u * T ^ τ) ≤
            Dconst j * min ((u * T ^ τ) ^ α) ((u * T ^ τ) ^ (-A)) := hp
        _ ≤ Dconst j * (u * T ^ τ) ^ (-A) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (hDspec j).1
        _ = Dconst j * u ^ (-A) * T ^ βlarge := by rw [hpowLarge T hT]; ring
    have hderivSmall (T : ℝ) (hT : 0 < T) :
        ‖normDerivR j Hf (u * T ^ τ)‖ ≤
          Dconst j * u ^ α * T ^ βsmall := by
      have hv : 0 < u * T ^ τ := mul_pos hu (zpow_pos hT τ)
      have hd := (hDspec j).2 (u * T ^ τ) hv |>.1
      calc
        ‖normDerivR j Hf (u * T ^ τ)‖ ≤
            Dconst j * min ((u * T ^ τ) ^ α) ((u * T ^ τ) ^ (-A)) := hd
        _ ≤ Dconst j * (u * T ^ τ) ^ α :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (hDspec j).1
        _ = Dconst j * u ^ α * T ^ βsmall := by rw [hpowSmall T hT]; ring
    have hderivLarge (T : ℝ) (hT : 0 < T) :
        ‖normDerivR j Hf (u * T ^ τ)‖ ≤
          Dconst j * u ^ (-A) * T ^ βlarge := by
      have hv : 0 < u * T ^ τ := mul_pos hu (zpow_pos hT τ)
      have hd := (hDspec j).2 (u * T ^ τ) hv |>.1
      calc
        ‖normDerivR j Hf (u * T ^ τ)‖ ≤
            Dconst j * min ((u * T ^ τ) ^ α) ((u * T ^ τ) ^ (-A)) := hd
        _ ≤ Dconst j * (u * T ^ τ) ^ (-A) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (hDspec j).1
        _ = Dconst j * u ^ (-A) * T ^ βlarge := by rw [hpowLarge T hT]; ring
    have hprofileIntegralSmall :
        ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * absProfile S μ v0 J ff fc j (u * T ^ τ) / T ∂volume ≤
          Dconst j * u ^ α * Msmall :=
      hIntegralMomentBound βsmall (Dconst j * u ^ α)
        (fun T => absProfile S μ v0 J ff fc j (u * T ^ τ))
        (fun T _ => absProfile_nonneg S μ v0 J ff fc j (u * T ^ τ)) hprofileSmall
    have hprofileIntegralLarge :
        ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * absProfile S μ v0 J ff fc j (u * T ^ τ) / T ∂volume ≤
          Dconst j * u ^ (-A) * Mlarge :=
      hIntegralMomentBound βlarge (Dconst j * u ^ (-A))
        (fun T => absProfile S μ v0 J ff fc j (u * T ^ τ))
        (fun T _ => absProfile_nonneg S μ v0 J ff fc j (u * T ^ τ)) hprofileLarge
    have hderivIntegralSmall :
        ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * ‖normDerivR j Hf (u * T ^ τ)‖ / T ∂volume ≤
          Dconst j * u ^ α * Msmall :=
      hIntegralMomentBound βsmall (Dconst j * u ^ α)
        (fun T => ‖normDerivR j Hf (u * T ^ τ)‖)
        (fun _ _ => norm_nonneg _) hderivSmall
    have hderivIntegralLarge :
        ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * ‖normDerivR j Hf (u * T ^ τ)‖ / T ∂volume ≤
          Dconst j * u ^ (-A) * Mlarge :=
      hIntegralMomentBound βlarge (Dconst j * u ^ (-A))
        (fun T => ‖normDerivR j Hf (u * T ^ τ)‖)
        (fun _ _ => norm_nonneg _) hderivLarge
    have hsmall :
        ‖normDerivR j Conv u‖ +
          ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * absProfile S μ v0 J ff fc j (u * T ^ τ) / T ∂volume ≤
          2 * Dconst j * u ^ α * Msmall := by
      have hN := (hConvDerivativeNorm j u hu).trans hderivIntegralSmall
      linarith
    have hlarge :
        ‖normDerivR j Conv u‖ +
          ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * absProfile S μ v0 J ff fc j (u * T ^ τ) / T ∂volume ≤
          2 * Dconst j * u ^ (-A) * Mlarge := by
      have hN := (hConvDerivativeNorm j u hu).trans hderivIntegralLarge
      linarith
    by_cases hmin : u ^ α ≤ u ^ (-A)
    · rw [min_eq_left hmin]
      calc
        ‖normDerivR j Conv u‖ +
            ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * absProfile S μ v0 J ff fc j (u * T ^ τ) / T ∂volume ≤
            2 * Dconst j * u ^ α * Msmall := hsmall
        _ ≤ 2 * Dconst j * (Msmall + Mlarge) * u ^ α := by
          have hle : Msmall ≤ Msmall + Mlarge := le_add_of_nonneg_right hMlarge
          calc
            2 * Dconst j * u ^ α * Msmall ≤ 2 * Dconst j * u ^ α * (Msmall + Mlarge) :=
              mul_le_mul_of_nonneg_left hle
                (mul_nonneg (mul_nonneg (by norm_num) (hDspec j).1)
                  (Real.rpow_nonneg hu.le _))
            _ = 2 * Dconst j * (Msmall + Mlarge) * u ^ α := by ring
    · have hmin' : u ^ (-A) ≤ u ^ α := le_of_not_ge hmin
      rw [min_eq_right hmin']
      calc
        ‖normDerivR j Conv u‖ +
            ∫ T in Set.Ioi (0 : ℝ), ‖K T‖ * absProfile S μ v0 J ff fc j (u * T ^ τ) / T ∂volume ≤
            2 * Dconst j * u ^ (-A) * Mlarge := hlarge
        _ ≤ 2 * Dconst j * (Msmall + Mlarge) * u ^ (-A) := by
          have hle : Mlarge ≤ Msmall + Mlarge := le_add_of_nonneg_left hMsmall
          calc
            2 * Dconst j * u ^ (-A) * Mlarge ≤ 2 * Dconst j * u ^ (-A) * (Msmall + Mlarge) :=
              mul_le_mul_of_nonneg_left hle
                (mul_nonneg (mul_nonneg (by norm_num) (hDspec j).1)
                  (Real.rpow_nonneg hu.le _))
            _ = 2 * Dconst j * (Msmall + Mlarge) * u ^ (-A) := by ring
  · intro σ hσ
    obtain ⟨Cσ, hCσ⟩ := hCmW 0 σ hσ
    have hCσnonneg : 0 ≤ Cσ := by
      have h := (hCσ 1 (by norm_num)).2
      have hprof : 0 ≤ absProfile S μ v0 J ff fc 0 1 :=
        absProfile_nonneg S μ v0 J ff fc 0 1
      have h' : absProfile S μ v0 J ff fc 0 1 ≤ Cσ := by simpa using h
      linarith
    refine ⟨Cσ, ?_⟩
    intro τ hτ ι x a hx ha u hu
    let θ : ℝ := (τ : ℝ)
    let bseq : ι → ℝ := fun i => ‖a i‖ * x i ^ (-σ)
    let pseq : ℝ → ι → ℝ := fun T i =>
      ‖a i‖ * absProfile S μ v0 J ff fc 0 (u * x i * T ^ τ)
    let β : ℝ := -(τ : ℝ) * σ
    let w : ℝ → ℝ := fun T => ‖K T‖ * T ^ β / T
    let scalar : ℝ := Cσ * u ^ (-σ) * ∑' i, bseq i
    let targetIntegrand : ℝ → ℝ := fun T => ‖K T‖ * (∑' i, pseq T i) / T
    let upperIntegrand : ℝ → ℝ := fun T => scalar * w T
    have hweightsNonneg (i : ι) : 0 ≤ bseq i := by
      dsimp [bseq]
      exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hx i).le _)
    have hweightsTsumNonneg : 0 ≤ ∑' i, bseq i := tsum_nonneg hweightsNonneg
    have hscalarNonneg : 0 ≤ scalar := by
      dsimp [scalar]
      positivity
    have hTsumBound (T : ℝ) (hT : 0 < T) :
        ∑' i, pseq T i ≤
          (Cσ * u ^ (-σ) * T ^ β) * ∑' i, bseq i := by
      let P : ℝ := Cσ * u ^ (-σ) * T ^ β
      have hP : 0 ≤ P := by dsimp [P]; positivity
      have hprofileBound (i : ι) :
          absProfile S μ v0 J ff fc 0 (u * x i * T ^ τ) ≤
            Cσ * u ^ (-σ) * x i ^ (-σ) * T ^ β := by
        have hv : 0 < u * x i * T ^ τ := mul_pos (mul_pos hu (hx i)) (zpow_pos hT τ)
        have hbase := (hCσ (u * x i * T ^ τ) hv).2
        have hp := real_rpow_zpow_mul (u * x i) T (mul_pos hu (hx i)) hT τ hτ (-σ)
        calc
          absProfile S μ v0 J ff fc 0 (u * x i * T ^ τ) ≤
              Cσ * (u * x i * T ^ τ) ^ (-σ) := hbase
          _ = Cσ * u ^ (-σ) * x i ^ (-σ) * T ^ β := by
            rw [hp, Real.mul_rpow hu.le (hx i).le]
            dsimp [β, θ]
            ring_nf
      have htermBound (i : ι) : pseq T i ≤ P * bseq i := by
        have h := mul_le_mul_of_nonneg_left (hprofileBound i) (norm_nonneg (a i))
        dsimp [pseq, P, bseq]
        calc
          ‖a i‖ * absProfile S μ v0 J ff fc 0 (u * x i * T ^ τ) ≤
              ‖a i‖ * (Cσ * u ^ (-σ) * x i ^ (-σ) * T ^ β) := h
          _ = (Cσ * u ^ (-σ) * T ^ β) * (‖a i‖ * x i ^ (-σ)) := by ring
      have hupperSummable : Summable (fun i => P * bseq i) := ha.mul_left P
      have hprofileSummable : Summable (pseq T) :=
        hupperSummable.of_nonneg_of_le (fun i => by
          dsimp [pseq]
          exact mul_nonneg (norm_nonneg _) (absProfile_nonneg S μ v0 J ff fc 0 _)) htermBound
      calc
        ∑' i, pseq T i ≤ ∑' i, P * bseq i := hprofileSummable.tsum_le_tsum htermBound hupperSummable
        _ = P * ∑' i, bseq i := by rw [tsum_mul_left]
    have hpoint (T : ℝ) (hT : 0 < T) : targetIntegrand T ≤ upperIntegrand T := by
      have hsum := hTsumBound T hT
      have hmul := mul_le_mul_of_nonneg_left hsum (norm_nonneg (K T))
      dsimp [targetIntegrand, upperIntegrand, scalar, w, β]
      calc
        ‖K T‖ * (∑' i, pseq T i) / T ≤
            ‖K T‖ * ((Cσ * u ^ (-σ) * T ^ (-(τ : ℝ) * σ)) * ∑' i, bseq i) / T := by
              exact div_le_div_of_nonneg_right hmul hT.le
        _ = Cσ * u ^ (-σ) * (∑' i, bseq i) * (‖K T‖ * T ^ (-(τ : ℝ) * σ) / T) := by ring
    have hleftNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] targetIntegrand := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
      have hprof : ∀ i, 0 ≤ pseq T i := by
        intro i
        dsimp [pseq]
        exact mul_nonneg (norm_nonneg _) (absProfile_nonneg S μ v0 J ff fc 0 _)
      have hsum : 0 ≤ ∑' i, pseq T i := tsum_nonneg hprof
      dsimp [targetIntegrand]
      exact div_nonneg (mul_nonneg (norm_nonneg _) hsum) (le_of_lt hT)
    have hupperIntegrable : Integrable upperIntegrand (volume.restrict (Set.Ioi (0 : ℝ))) := by
      dsimp [upperIntegrand, w, β, scalar]
      exact (hK (-(τ : ℝ) * σ)).const_mul (Cσ * u ^ (-σ) * ∑' i, bseq i)
    have hupperIntegral :
        ∫ T, upperIntegrand T ∂(volume.restrict (Set.Ioi (0 : ℝ))) =
          scalar * absMoment K (-(τ : ℝ) * σ) := by
      change ∫ T, scalar * w T ∂(volume.restrict (Set.Ioi (0 : ℝ))) = _
      rw [integral_const_mul]
      rfl
    have hIntegralBound :
        ∫ T in Set.Ioi (0 : ℝ), targetIntegrand T ∂volume ≤
          Cσ * u ^ (-σ) * absMoment K (-(τ : ℝ) * σ) * ∑' i, bseq i := by
      change ∫ T, targetIntegrand T ∂(volume.restrict (Set.Ioi (0 : ℝ))) ≤ _
      calc
        ∫ T, targetIntegrand T ∂(volume.restrict (Set.Ioi (0 : ℝ))) ≤
            ∫ T, upperIntegrand T ∂(volume.restrict (Set.Ioi (0 : ℝ))) :=
          integral_mono_of_nonneg hleftNonneg hupperIntegrable
            (by
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
              exact hpoint T hT)
        _ = scalar * absMoment K (-(τ : ℝ) * σ) := hupperIntegral
        _ = Cσ * u ^ (-σ) * absMoment K (-(τ : ℝ) * σ) * ∑' i, bseq i := by
          dsimp [scalar]
          ring
    simpa [bseq, targetIntegrand] using hIntegralBound

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
  have hρtwo : ContDiff ℝ 2 ρ := hρ.of_le (by norm_num)
  obtain ⟨b, hb⟩ := bddAbove_def.mp (hρc.bddAbove_image continuous_abs.continuousOn)
  let B : ℝ := max b 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB (t : ℝ) (ht : t ∈ tsupport ρ) : |t| ≤ B := by
    have htb : |t| ≤ b := hb _ ⟨t, ht, rfl⟩
    dsimp [B]
    exact le_trans htb (le_max_left _ _)
  have hρone : ContDiff ℝ 1 (deriv ρ) := hρtwo.deriv'
  have hρtwo' : ContDiff ℝ 0 (deriv (deriv ρ)) := hρone.deriv'
  have hρsupp₁ : HasCompactSupport (deriv ρ) := hρc.deriv
  have hρsupp₂ : HasCompactSupport (deriv (deriv ρ)) := hρsupp₁.deriv
  have hR0int : Integrable (fun t : ℝ => ‖ρ t‖) :=
    (hρtwo.continuous.integrable_of_hasCompactSupport hρc).norm
  have hR1int : Integrable (fun t : ℝ => ‖deriv ρ t‖) :=
    (hρone.continuous.integrable_of_hasCompactSupport hρsupp₁).norm
  have hR2int : Integrable (fun t : ℝ => ‖iteratedDeriv 2 ρ t‖) := by
    simpa [iteratedDeriv_succ] using
      (hρtwo'.continuous.integrable_of_hasCompactSupport hρsupp₂).norm
  let R0 : ℝ := ∫ t : ℝ, ‖ρ t‖
  let R1 : ℝ := ∫ t : ℝ, ‖deriv ρ t‖
  let R2 : ℝ := ∫ t : ℝ, ‖iteratedDeriv 2 ρ t‖
  have hR0 : 0 ≤ R0 := by
    dsimp [R0]
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hR1 : 0 ≤ R1 := by
    dsimp [R1]
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hR2 : 0 ≤ R2 := by
    dsimp [R2]
    exact integral_nonneg (fun _ => norm_nonneg _)
  intro A hA
  obtain ⟨C0, hC0⟩ := hΦ 0 (by norm_num) A hA
  obtain ⟨C1, hC1⟩ := hΦ 1 (by norm_num) A hA
  obtain ⟨C2, hC2⟩ := hΦ 2 (by norm_num) A hA
  have hC0nonneg : 0 ≤ C0 := by
    have h := hC0 1 (by norm_num)
    have h' : ‖normDerivR 0 Φ 1‖ ≤ C0 := by simpa using h
    exact le_trans (norm_nonneg _) h'
  have hC1nonneg : 0 ≤ C1 := by
    have h := hC1 1 (by norm_num)
    have h' : ‖normDerivR 1 Φ 1‖ ≤ C1 := by simpa using h
    exact le_trans (norm_nonneg _) h'
  have hC2nonneg : 0 ≤ C2 := by
    have h := hC2 1 (by norm_num)
    have h' : ‖normDerivR 2 Φ 1‖ ≤ C2 := by simpa using h
    exact le_trans (norm_nonneg _) h'
  let E : ℝ := Real.exp (B * max α A)
  have hEpos : 0 < E := by positivity
  have hpow (u t : ℝ) (hu : 0 < u) (ht : t ∈ tsupport ρ) :
      (u * Real.exp t) ^ α ≤ E * u ^ α ∧
        (u * Real.exp t) ^ (-A) ≤ E * u ^ (-A) := by
    have htupper : t ≤ B := (abs_le.mp (hB t ht)).2
    have htlower : -t ≤ B := by
      have := (abs_le.mp (hB t ht)).1
      linarith
    have heα : α * t ≤ B * max α A := by
      calc
        α * t ≤ α * B := mul_le_mul_of_nonneg_left htupper hα.le
        _ ≤ B * max α A := by
          calc
            α * B ≤ max α A * B := mul_le_mul_of_nonneg_right (le_max_left _ _) hB0
            _ = B * max α A := by ring
    have heA : (-A) * t ≤ B * max α A := by
      calc
        (-A) * t = A * (-t) := by ring
        _ ≤ A * B := mul_le_mul_of_nonneg_left htlower hA.le
        _ ≤ B * max α A := by
          calc
            A * B ≤ max α A * B := mul_le_mul_of_nonneg_right (le_max_right _ _) hB0
            _ = B * max α A := by ring
    have hexpα : (Real.exp t) ^ α = Real.exp (α * t) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos t)]
      simp [Real.log_exp, mul_comm]
    have hexpA : (Real.exp t) ^ (-A) = Real.exp ((-A) * t) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos t)]
      simp [Real.log_exp, mul_comm]
    constructor
    · calc
        (u * Real.exp t) ^ α = u ^ α * Real.exp (α * t) := by
          rw [Real.mul_rpow hu.le (Real.exp_pos t).le, hexpα]
        _ ≤ u ^ α * E := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr heα) (by positivity)
        _ = E * u ^ α := by ring
    · calc
        (u * Real.exp t) ^ (-A) = u ^ (-A) * Real.exp ((-A) * t) := by
          rw [Real.mul_rpow hu.le (Real.exp_pos t).le, hexpA]
        _ ≤ u ^ (-A) * E := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr heA) (by positivity)
        _ = E * u ^ (-A) := by ring
  have hscale (j : ℕ) (Cj : ℝ) (hCj : ∀ z : ℝ, 0 < z →
      ‖normDerivR j Φ z‖ ≤ Cj * min (z ^ α) (z ^ (-A)))
      (hCjnonneg : 0 ≤ Cj) (u t : ℝ) (hu : 0 < u) (ht : t ∈ tsupport ρ) :
      ‖normDerivR j Φ (u * Real.exp t)‖ ≤ Cj * E * min (u ^ α) (u ^ (-A)) := by
    have hz : 0 < u * Real.exp t := mul_pos hu (Real.exp_pos t)
    have hp := hpow u t hu ht
    rcases le_total (u ^ α) (u ^ (-A)) with hmin | hmin
    · have hm : min (u ^ α) (u ^ (-A)) = u ^ α := min_eq_left hmin
      calc
        ‖normDerivR j Φ (u * Real.exp t)‖ ≤ Cj * min ((u * Real.exp t) ^ α) ((u * Real.exp t) ^ (-A)) := hCj _ hz
        _ ≤ Cj * (E * u ^ α) := mul_le_mul_of_nonneg_left (le_trans (min_le_left _ _) hp.1) hCjnonneg
        _ = Cj * E * min (u ^ α) (u ^ (-A)) := by rw [hm]; ring
    · have hm : min (u ^ α) (u ^ (-A)) = u ^ (-A) := min_eq_right hmin
      calc
        ‖normDerivR j Φ (u * Real.exp t)‖ ≤ Cj * min ((u * Real.exp t) ^ α) ((u * Real.exp t) ^ (-A)) := hCj _ hz
        _ ≤ Cj * (E * u ^ (-A)) := mul_le_mul_of_nonneg_left (le_trans (min_le_right _ _) hp.2) hCjnonneg
        _ = Cj * E * min (u ^ α) (u ^ (-A)) := by rw [hm]; ring
  refine ⟨Real.pi * E * (2 * C0 * R0 + C0 * R2 + 2 * C1 * R1 + C2 * R0), ?_⟩
  intro u hu
  let φ : ℝ → ℂ := fun t => Φ (u * Real.exp t)
  let g : ℝ → ℂ := fun t => ρ t * φ t
  have hφ : ContDiff ℝ 2 φ := by
    simpa [φ, Function.comp_def] using hΦs.comp_contDiff (by fun_prop : ContDiff ℝ 2 (fun t : ℝ => u * Real.exp t))
      (fun t => mul_pos hu (Real.exp_pos t))
  have hg : ContDiff ℝ 2 g := by
    dsimp [g]
    exact hρtwo.mul hφ
  have hgc : HasCompactSupport g := by
    dsimp [g, φ]
    exact HasCompactSupport.mul_right hρc
  have hform (t : ℝ) : iteratedDeriv 2 g t =
      iteratedDeriv 2 ρ t * Φ (u * Real.exp t) +
        2 * deriv ρ t * normDerivR 1 Φ (u * Real.exp t) +
        ρ t * normDerivR 2 Φ (u * Real.exp t) := by
    change iteratedDeriv 2 (ρ * φ) t = _
    have hφiter0 : iteratedDeriv 0 φ t = Φ (u * Real.exp t) := by simp [φ]
    have hφiter1 : iteratedDeriv 1 φ t = normDerivR 1 Φ (u * Real.exp t) := by
      simpa [φ] using iteratedDeriv_log_scale Φ u hu 1 t
    have hφiter2 : iteratedDeriv 2 φ t = normDerivR 2 Φ (u * Real.exp t) := by
      simpa [φ] using iteratedDeriv_log_scale Φ u hu 2 t
    rw [iteratedDeriv_mul hρtwo.contDiffAt hφ.contDiffAt]
    simp [Finset.sum_range_succ, iteratedDeriv_succ, hφiter0, hφiter1, hφiter2]
    ring_nf
  have hpoint0 (t : ℝ) : ‖g t‖ ≤ E * min (u ^ α) (u ^ (-A)) * C0 * ‖ρ t‖ := by
    by_cases ht : t ∈ tsupport ρ
    · have hs := hscale 0 C0 hC0 hC0nonneg u t hu ht
      have hz : 0 < u * Real.exp t := mul_pos hu (Real.exp_pos t)
      have hs' : ‖Φ (u * Real.exp t)‖ ≤ C0 * E * min (u ^ α) (u ^ (-A)) := by
        rw [← Real.exp_log hz]
        simpa [normDerivR] using hs
      calc
        ‖g t‖ = ‖ρ t‖ * ‖Φ (u * Real.exp t)‖ := by simp [g, φ, norm_mul]
        _ ≤ ‖ρ t‖ * (C0 * E * min (u ^ α) (u ^ (-A))) :=
          mul_le_mul_of_nonneg_left hs' (norm_nonneg _)
        _ = E * min (u ^ α) (u ^ (-A)) * C0 * ‖ρ t‖ := by ring
    · have hρzero : ρ t = 0 := (notMem_tsupport_iff_eventuallyEq.mp ht).eq_of_nhds
      simp [g, φ, hρzero]
  have hpoint2 (t : ℝ) :
      ‖iteratedDeriv 2 g t‖ ≤
        E * min (u ^ α) (u ^ (-A)) * C0 * ‖iteratedDeriv 2 ρ t‖ +
          E * min (u ^ α) (u ^ (-A)) * (2 * C1) * ‖deriv ρ t‖ +
          E * min (u ^ α) (u ^ (-A)) * C2 * ‖ρ t‖ := by
    by_cases ht : t ∈ tsupport ρ
    · have hs0 := hscale 0 C0 hC0 hC0nonneg u t hu ht
      have hs1 := hscale 1 C1 hC1 hC1nonneg u t hu ht
      have hs2 := hscale 2 C2 hC2 hC2nonneg u t hu ht
      let a : ℂ := iteratedDeriv 2 ρ t * Φ (u * Real.exp t)
      let b : ℂ := 2 * deriv ρ t * normDerivR 1 Φ (u * Real.exp t)
      let c : ℂ := ρ t * normDerivR 2 Φ (u * Real.exp t)
      have htriangle : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
        calc
          ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le (a + b) c
          _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by nlinarith [norm_add_le a b]
      have hz : 0 < u * Real.exp t := mul_pos hu (Real.exp_pos t)
      have hs0' : ‖Φ (u * Real.exp t)‖ ≤ C0 * E * min (u ^ α) (u ^ (-A)) := by
        rw [← Real.exp_log hz]
        simpa [normDerivR] using hs0
      have ha := mul_le_mul_of_nonneg_left hs0' (norm_nonneg (iteratedDeriv 2 ρ t))
      have hb := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ 2 * ‖deriv ρ t‖)
      have hc := mul_le_mul_of_nonneg_left hs2 (norm_nonneg (ρ t))
      have hproducts : ‖a‖ + ‖b‖ + ‖c‖ ≤
          ‖iteratedDeriv 2 ρ t‖ * (C0 * E * min (u ^ α) (u ^ (-A))) +
            2 * ‖deriv ρ t‖ * (C1 * E * min (u ^ α) (u ^ (-A))) +
            ‖ρ t‖ * (C2 * E * min (u ^ α) (u ^ (-A))) := by
        calc
          ‖a‖ + ‖b‖ + ‖c‖ =
              ‖iteratedDeriv 2 ρ t‖ * ‖Φ (u * Real.exp t)‖ +
                (2 * ‖deriv ρ t‖ * ‖normDerivR 1 Φ (u * Real.exp t)‖) +
                (‖ρ t‖ * ‖normDerivR 2 Φ (u * Real.exp t)‖) := by
                  simp [a, b, c, norm_mul, Complex.norm_ofNat, mul_assoc]
          _ ≤ _ := add_le_add (add_le_add ha hb) hc
      rw [hform]
      calc
        ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := htriangle
        _ ≤ ‖iteratedDeriv 2 ρ t‖ * (C0 * E * min (u ^ α) (u ^ (-A))) +
              2 * ‖deriv ρ t‖ * (C1 * E * min (u ^ α) (u ^ (-A))) +
              ‖ρ t‖ * (C2 * E * min (u ^ α) (u ^ (-A))) := hproducts
        _ = E * min (u ^ α) (u ^ (-A)) * C0 * ‖iteratedDeriv 2 ρ t‖ +
              E * min (u ^ α) (u ^ (-A)) * (2 * C1) * ‖deriv ρ t‖ +
              E * min (u ^ α) (u ^ (-A)) * C2 * ‖ρ t‖ := by ring
    · have hρzero : ρ t = 0 := (notMem_tsupport_iff_eventuallyEq.mp ht).eq_of_nhds
      have hρ₁zero : deriv ρ t = 0 := deriv_of_notMem_tsupport ht
      have hnotρ₁ : t ∉ tsupport (deriv ρ) := fun h => ht (tsupport_deriv_subset h)
      have hρ₂zero : iteratedDeriv 2 ρ t = 0 := by
        simpa [iteratedDeriv_succ] using deriv_of_notMem_tsupport hnotρ₁
      rw [hform]
      simp [hρzero, hρ₁zero, hρ₂zero]
  have hIntg : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hIntg2 : Integrable (fun t : ℝ => iteratedDeriv 2 g t) := by
    have hcont : ContDiff ℝ 0 (iteratedDeriv 2 g) := by
      have hderiv₁ : ContDiff ℝ 1 (deriv g) := hg.deriv'
      have hderiv₂ : ContDiff ℝ 0 (deriv (deriv g)) := hderiv₁.deriv'
      simpa [iteratedDeriv_succ] using hderiv₂
    have hsupport : HasCompactSupport (iteratedDeriv 2 g) := by
      have hderiv₁ : HasCompactSupport (deriv g) := hgc.deriv
      have hderiv₂ : HasCompactSupport (deriv (deriv g)) := hderiv₁.deriv
      simpa [iteratedDeriv_succ] using hderiv₂
    exact hcont.continuous.integrable_of_hasCompactSupport hsupport
  have hI0 : ∫ t : ℝ, ‖g t‖ ≤ E * min (u ^ α) (u ^ (-A)) * C0 * R0 := by
    calc
      ∫ t, ‖g t‖ ≤ ∫ t, E * min (u ^ α) (u ^ (-A)) * C0 * ‖ρ t‖ :=
        integral_mono_ae hIntg.norm (hR0int.const_mul _) (Filter.Eventually.of_forall hpoint0)
      _ = E * min (u ^ α) (u ^ (-A)) * C0 * R0 := by
        simp [R0, integral_const_mul, mul_assoc]
  let q0 : ℝ := E * min (u ^ α) (u ^ (-A)) * C0
  let q1 : ℝ := E * min (u ^ α) (u ^ (-A)) * (2 * C1)
  let q2 : ℝ := E * min (u ^ α) (u ^ (-A)) * C2
  let rhs2 : ℝ → ℝ := fun t =>
    q0 * ‖iteratedDeriv 2 ρ t‖ + (q1 * ‖deriv ρ t‖ + q2 * ‖ρ t‖)
  have hterm0 : Integrable (fun t : ℝ => q0 * ‖iteratedDeriv 2 ρ t‖) := hR2int.const_mul q0
  have hterm1 : Integrable (fun t : ℝ => q1 * ‖deriv ρ t‖) := hR1int.const_mul q1
  have hterm2 : Integrable (fun t : ℝ => q2 * ‖ρ t‖) := hR0int.const_mul q2
  have hRhs2 : Integrable rhs2 := by
    exact hterm0.add (hterm1.add hterm2)
  have hRhs2Integral : ∫ t : ℝ, rhs2 t = q0 * R2 + (q1 * R1 + q2 * R0) := by
    let f0 : ℝ → ℝ := fun t => q0 * ‖iteratedDeriv 2 ρ t‖
    let f1 : ℝ → ℝ := fun t => q1 * ‖deriv ρ t‖
    let f2 : ℝ → ℝ := fun t => q2 * ‖ρ t‖
    change ∫ t : ℝ, f0 t + (f1 t + f2 t) = _
    calc
      ∫ t : ℝ, f0 t + (f1 t + f2 t) =
          (∫ t : ℝ, f0 t) + ∫ t : ℝ, f1 t + f2 t :=
        integral_add hterm0 (hterm1.add hterm2)
      _ = q0 * R2 + (q1 * R1 + q2 * R0) := by
        rw [integral_add hterm1 hterm2]
        simp [f0, f1, f2, R0, R1, R2, integral_const_mul, mul_assoc]
  have hI2 : ∫ t : ℝ, ‖iteratedDeriv 2 g t‖ ≤
      E * min (u ^ α) (u ^ (-A)) *
        (C0 * R2 + 2 * C1 * R1 + C2 * R0) := by
    calc
      ∫ t, ‖iteratedDeriv 2 g t‖ ≤ ∫ t, rhs2 t :=
        integral_mono_ae hIntg2.norm hRhs2 (Filter.Eventually.of_forall (fun t => by
          simpa [rhs2, q0, q1, q2, mul_assoc, add_assoc] using hpoint2 t))
      _ = q0 * R2 + (q1 * R1 + q2 * R0) := hRhs2Integral
      _ = E * min (u ^ α) (u ^ (-A)) *
          (C0 * R2 + 2 * C1 * R1 + C2 * R0) := by
        dsimp [q0, q1, q2]
        ring
  have hfourier := ArtinPrimitiveRoots.Proofs.TH_S_CONV.fourier_integral_norm_le_of_compactSupport hg hgc
  calc
    ∫ ξ : ℝ, ‖𝓕 g ξ‖ ≤
        Real.pi * (2 * (∫ t, ‖g t‖) + ∫ t, ‖iteratedDeriv 2 g t‖) := hfourier
    _ ≤ Real.pi * (2 * (E * min (u ^ α) (u ^ (-A)) * C0 * R0) +
          E * min (u ^ α) (u ^ (-A)) * (C0 * R2 + 2 * C1 * R1 + C2 * R0)) := by
      gcongr
    _ = (Real.pi * E * (2 * C0 * R0 + C0 * R2 + 2 * C1 * R1 + C2 * R0)) *
          min (u ^ α) (u ^ (-A)) := by ring

/-- **eq:theta-V-profile** (03:661–669): the radial profile of the chosen S-function (T5 without
its angular characters), with the cutoff `U` and constants `cS`. -/
def thetaV (μ : ∀ v : FinPlace F, LocHaar v) (v0 : InfinitePlace F)
    (U : Set (∀ v : S.Sf, v.1.adicCompletion F)) (cS : InfinitePlace F → ℝ) (u : ℝ) : ℂ :=
  sheetInt S μ v0 (fun y => (if y.1 ∈ U then (1 : ℂ) else 0) *
    ∏ w : InfinitePlace F, ((Complex.normSq (y.2 w) : ℝ) : ℂ) *
      (besselK (1 / 3) (cS w * ‖y.2 w‖) : ℂ)) u

private def smoothBase (U : Set (∀ v : S.Sf, v.1.adicCompletion F))
    (cS : InfinitePlace F → ℝ) (y : S.FS) : ℂ :=
  (if y.1 ∈ U then (1 : ℂ) else 0) *
    ∏ w : InfinitePlace F, (Complex.normSq (y.2 w) : ℂ) *
      (besselK (1 / 3) (cS w * ‖y.2 w‖) : ℂ)

private def smoothWeighted (U : Set (∀ v : S.Sf, v.1.adicCompletion F))
    (cS : InfinitePlace F → ℝ) (s : ℂ) (y : S.FS) : ℂ :=
  (if y.1 ∈ U then (1 : ℂ) else 0) *
    ∏ w : InfinitePlace F, (Complex.normSq (y.2 w) : ℂ) ^ s *
      (Complex.normSq (y.2 w) : ℂ) * (besselK (1 / 3) (cS w * ‖y.2 w‖) : ℂ)

private theorem smoothWeightedFactor (U : Set (∀ v : S.Sf, v.1.adicCompletion F))
    (cS : InfinitePlace F → ℝ) (s : ℂ) (y : S.FS) :
    smoothWeighted S U cS s y =
      ((∏ w : InfinitePlace F, Complex.normSq (y.2 w) : ℝ) : ℂ) ^ s *
        smoothBase S U cS y := by
  have hp : ((∏ w : InfinitePlace F, Complex.normSq (y.2 w) : ℝ) : ℂ) ^ s =
      ∏ w : InfinitePlace F, (Complex.normSq (y.2 w) : ℂ) ^ s := by
    induction (Finset.univ : Finset (InfinitePlace F)) using Finset.induction_on with
    | empty => simp
    | @insert w t hw ih =>
      rw [Finset.prod_insert hw, Finset.prod_insert hw, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (Complex.normSq_nonneg _)
          (Finset.prod_nonneg fun w _ => Complex.normSq_nonneg _) s, ih]
  dsimp only [smoothWeighted, smoothBase]
  rw [hp]
  simp_rw [Finset.prod_mul_distrib]
  ring

private theorem smoothFiniteUnitProduct (U : Set (∀ v : S.Sf, v.1.adicCompletion F))
    (hUunit : ∀ y ∈ U, ∀ v : S.Sf, Valued.v (y v) = 1)
    (y : ∀ v : S.Sf, v.1.adicCompletion F) (hy : y ∈ U) :
    ∏ v : S.Sf, absFin v.1 (y v) = 1 := by
  apply Finset.prod_eq_one
  intro v _
  rw [absFin, dite_eq_left (HeightOneSpectrum.absNorm_ne_zero v.1), hUunit y hy v,
    map_one, NNReal.coe_one]

private theorem smoothSheetNormProduct (v0 : InfinitePlace F) (u : ℝ)
    (p : (∀ v : S.Sf, v.1.adicCompletion F) × ({w : InfinitePlace F // w ≠ v0} → ℂ))
    (θ : ℝ) (hfin : ∏ v : S.Sf, absFin v.1 (p.1 v) = 1) (hu : 0 < u)
    (hp : 0 < ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)) :
    ∏ w : InfinitePlace F, Complex.normSq ((sheetPoint S v0 u p θ).2 w) = u := by
  have he : Complex.normSq (Complex.exp (2 * Real.pi * Complex.I * θ)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp
  have hd : Complex.normSq ((sheetPoint S v0 u p θ).2 v0) =
      u / ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w) := by
    simp only [sheetPoint]
    change Complex.normSq ((Real.sqrt (u / ((∏ v : S.Sf, absFin v.1 (p.1 v)) *
      ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w))) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * θ)) = _
    rw [Complex.normSq_mul, he, mul_one, Complex.normSq_ofReal, hfin, one_mul,
      Real.mul_self_sqrt (div_nonneg hu.le hp.le)]
  have hf : (∏ w : {w : InfinitePlace F // w ≠ v0},
      Complex.normSq ((sheetPoint S v0 u p θ).2 w.1)) =
      ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w) := by
    apply Finset.prod_congr rfl
    intro w _
    simp [sheetPoint, w.2]
  rw [Fintype.prod_eq_mul_prod_compl v0,
    Finset.prod_subtype (p := fun w : InfinitePlace F => w ≠ v0) ({v0}ᶜ) (fun w => by simp)
      (fun w => Complex.normSq ((sheetPoint S v0 u p θ).2 w)), hf, hd]
  exact div_mul_cancel₀ u hp.ne'

private theorem smoothPointWeight (v0 : InfinitePlace F)
    (U : Set (∀ v : S.Sf, v.1.adicCompletion F))
    (hUunit : ∀ y ∈ U, ∀ v : S.Sf, Valued.v (y v) = 1)
    (cS : InfinitePlace F → ℝ) (s : ℂ) (u : ℝ) (hu : 0 < u)
    (p : (∀ v : S.Sf, v.1.adicCompletion F) × ({w : InfinitePlace F // w ≠ v0} → ℂ))
    (θ : ℝ) :
    smoothWeighted S U cS s (sheetPoint S v0 u p θ) =
      (u : ℂ) ^ s * smoothBase S U cS (sheetPoint S v0 u p θ) := by
  rw [smoothWeightedFactor]
  by_cases hy : p.1 ∈ U
  · have hfin := smoothFiniteUnitProduct S U hUunit p.1 hy
    by_cases hp : (∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w)) = 0
    · have hd : (sheetPoint S v0 u p θ).2 v0 = 0 := by simp [sheetPoint, hp]
      have hbase : smoothBase S U cS (sheetPoint S v0 u p θ) = 0 := by
        unfold smoothBase
        have hz : (∏ w : InfinitePlace F,
            (Complex.normSq ((sheetPoint S v0 u p θ).2 w) : ℂ) *
              (besselK (1 / 3) (cS w * ‖(sheetPoint S v0 u p θ).2 w‖) : ℂ)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ v0) (by rw [hd]; simp)
        rw [hz, mul_zero]
      rw [hbase, mul_zero, mul_zero]
    · have hpos : 0 < ∏ w : {w : InfinitePlace F // w ≠ v0}, Complex.normSq (p.2 w) :=
        lt_of_le_of_ne (Finset.prod_nonneg fun w _ => Complex.normSq_nonneg _) (Ne.symm hp)
      rw [smoothSheetNormProduct S v0 u p θ hfin hu hpos]
  · have hbase : smoothBase S U cS (sheetPoint S v0 u p θ) = 0 := by
      change (if p.1 ∈ U then (1 : ℂ) else 0) * _ = 0
      rw [ite_eq_right hy, zero_mul]
    rw [hbase, mul_zero, mul_zero]

private theorem smoothSheetWeight (μ : ∀ v : FinPlace F, LocHaar v)
    (v0 : InfinitePlace F) (U : Set (∀ v : S.Sf, v.1.adicCompletion F))
    (hUunit : ∀ y ∈ U, ∀ v : S.Sf, Valued.v (y v) = 1)
    (cS : InfinitePlace F → ℝ) (s : ℂ) (u : ℝ) (hu : 0 < u) :
    sheetInt S μ v0 (smoothWeighted S U cS s) u =
      (u : ℂ) ^ s * thetaV S μ v0 U cS u := by
  unfold sheetInt thetaV
  simp_rw [smoothPointWeight S v0 U hUunit cS s u hu, integral_const_mul]
  rfl

/-- The sheet Mellin transform equals the product of all local weighted Bessel integrals,
with the disintegration factor pi retained explicitly. -/
theorem _root_.ArtinPrimitiveRoots.Proofs.thsol_smooth.bessel_sheet_mellin
    [IsTotallyComplex F] (μ : ∀ v : FinPlace F, LocHaar v)
    (v0 : InfinitePlace F) (U : Set (∀ v : S.Sf, v.1.adicCompletion F))
    (hUo : IsOpen U) (hUc : IsCompact U)
    (hU1 : (1 : ∀ v : S.Sf, v.1.adicCompletion F) ∈ U)
    (hUunit : ∀ y ∈ U, ∀ v : S.Sf, Valued.v (y v) = 1)
    (cS : InfinitePlace F → ℝ) (hcS : ∀ w, 0 < cS w)
    (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    (Real.pi : ℂ) * mellin (thetaV S μ v0 U cS) s =
      ((Measure.pi (fun v : S.Sf => mulHaarFin (μ v.1)) U).toReal : ℂ) *
        ∏ w : InfinitePlace F, (Real.pi : ℂ) *
          ((2 : ℂ) ^ (2 * s + 1) * (cS w : ℂ) ^ (-2 * s - 2) *
            Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by
  obtain ⟨hi, hv⟩ := ArtinPrimitiveRoots.Proofs.thsol_smooth.bessel_product_mellin
    S μ U hUo hUc hU1 hUunit cS hcS s hs
  have hi' : Integrable (smoothWeighted S U cS s) (mulHaarS S μ) := hi
  have hd := sheet_disintegration S μ v0 (smoothWeighted S U cS s) hi'
  have hr : (∫ u in Set.Ioi (0 : ℝ),
      sheetInt S μ v0 (smoothWeighted S U cS s) u / u) =
      mellin (thetaV S μ v0 U cS) s := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change sheetInt S μ v0 (smoothWeighted S U cS s) u / (u : ℂ) =
      (u : ℂ) ^ (s - 1) * thetaV S μ v0 U cS u
    rw [smoothSheetWeight S μ v0 U hUunit cS s u hu]
    rw [Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr (ne_of_gt hu)), Complex.cpow_one]
    exact mul_div_right_comm _ _ _
  rw [hr] at hd
  exact hd.symm.trans hv

private theorem smoothProdCpow {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (s : ℂ) :
    ((∏ i, a i : ℝ) : ℂ) ^ s = ∏ i, (a i : ℂ) ^ s := by
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha i) (Finset.prod_nonneg fun i _ => ha i) s, ih]

private theorem smoothSquareCpow (a : ℝ) (ha : 0 ≤ a) (s : ℂ) :
    ((a ^ 2 : ℝ) : ℂ) ^ s = (a : ℂ) ^ (2 * s) := by
  rw [Complex.ofReal_pow]
  exact (Complex.cpow_ofNat_mul' (x := (a : ℂ)) (n := 2)
    (by simpa only [Complex.arg_ofReal_of_nonneg ha, mul_zero] using
      (neg_lt_zero.mpr Real.pi_pos))
    (by simpa only [Complex.arg_ofReal_of_nonneg ha, mul_zero] using Real.pi_pos.le) s).symm

private theorem smoothLocalNormalize (c : ℝ) (hc : 0 < c) (s : ℂ) :
    (Real.pi : ℂ) * ((2 : ℂ) ^ (2 * s + 1) * (c : ℂ) ^ (-2 * s - 2)) =
      ((2 * Real.pi / c ^ 2 : ℝ) : ℂ) * ((4 / c ^ 2 : ℝ) : ℂ) ^ s := by
  have hcnz : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have htwo : (2 : ℂ) ^ (2 * s + 1) = 2 * (2 : ℂ) ^ (2 * s) := by
    rw [Complex.cpow_add (2 * s) 1 (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
    ring
  have hcFactor : (c : ℂ) ^ (-2 * s - 2) = ((c : ℂ) ^ (2 * s))⁻¹ / (c : ℂ) ^ 2 := by
    rw [show -2 * s - 2 = -(2 * s) - 2 by ring,
      Complex.cpow_sub _ _ hcnz, Complex.cpow_neg, Complex.cpow_two]
  have hfour : (4 : ℂ) ^ s = (2 : ℂ) ^ (2 * s) := by
    convert smoothSquareCpow 2 (by norm_num) s using 1
    norm_num
  have hA : ((4 / c ^ 2 : ℝ) : ℂ) ^ s =
      (2 : ℂ) ^ (2 * s) / (c : ℂ) ^ (2 * s) := by
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (by norm_num) (sq_nonneg c) s]
    rw [Complex.ofReal_ofNat, hfour, smoothSquareCpow c hc.le s]
  rw [htwo, hcFactor, hA]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- The Mellin transform of the theta radial profile is a positive scale times
an exponential scale and the prescribed product of shifted gamma factors. -/
theorem _root_.ArtinPrimitiveRoots.Proofs.thsol_smooth.gaussian_smoothing_part1
    [IsTotallyComplex F] (μ : ∀ v : FinPlace F, LocHaar v)
    (v0 : InfinitePlace F) (U : Set (∀ v : S.Sf, v.1.adicCompletion F))
    (hUo : IsOpen U) (hUc : IsCompact U)
    (hU1 : (1 : ∀ v : S.Sf, v.1.adicCompletion F) ∈ U)
    (hUunit : ∀ y ∈ U, ∀ v : S.Sf, Valued.v (y v) = 1)
    (cS : InfinitePlace F → ℝ) (hcS : ∀ w, 0 < cS w) :
    ∃ C₀ A₀ : ℝ, 0 < C₀ ∧ 0 < A₀ ∧ ∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
      mellin (thetaV S μ v0 U cS) s = (C₀ : ℂ) * (A₀ : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ numComplex F := by
  let mU : ℝ := (Measure.pi (fun v : S.Sf => mulHaarFin (μ v.1)) U).toReal
  let A (w : InfinitePlace F) : ℝ := 4 / (cS w) ^ 2
  let B (w : InfinitePlace F) : ℝ := 2 * Real.pi / (cS w) ^ 2
  let C₀ : ℝ := mU / Real.pi * ∏ w, B w
  let A₀ : ℝ := ∏ w, A w
  have hmU : 0 < mU :=
    (ArtinPrimitiveRoots.Proofs.thsol_smooth.finite_unit_cutoff_mass
      S μ U hUo hUc hU1 hUunit).2.1
  have hA (w : InfinitePlace F) : 0 < A w :=
    div_pos (by norm_num) (pow_pos (hcS w) 2)
  have hB (w : InfinitePlace F) : 0 < B w :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos (hcS w) 2)
  refine ⟨C₀, A₀, mul_pos (div_pos hmU Real.pi_pos)
    (Finset.prod_pos fun w _ => hB w), Finset.prod_pos (fun w _ => hA w), ?_⟩
  intro s hs
  let g : ℂ := Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)
  have hlocal (w : InfinitePlace F) :
      (Real.pi : ℂ) * ((2 : ℂ) ^ (2 * s + 1) * (cS w : ℂ) ^ (-2 * s - 2) *
        Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) =
        (B w : ℂ) * (A w : ℂ) ^ s * g := by
    dsimp only [A, B, g]
    calc
      _ = ((Real.pi : ℂ) * ((2 : ℂ) ^ (2 * s + 1) *
          (cS w : ℂ) ^ (-2 * s - 2))) *
          (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by ring
      _ = _ := by rw [smoothLocalNormalize (cS w) (hcS w) s]
  have hprod : (∏ w : InfinitePlace F, (Real.pi : ℂ) *
      ((2 : ℂ) ^ (2 * s + 1) * (cS w : ℂ) ^ (-2 * s - 2) *
        Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6))) =
      ((∏ w, B w : ℝ) : ℂ) * ((∏ w, A w : ℝ) : ℂ) ^ s * g ^ numComplex F := by
    calc
      _ = ∏ w : InfinitePlace F, (B w : ℂ) * (A w : ℂ) ^ s * g := by
        apply Finset.prod_congr rfl
        intro w _
        exact hlocal w
      _ = (∏ w : InfinitePlace F, (B w : ℂ)) *
          (∏ w : InfinitePlace F, (A w : ℂ) ^ s) * ∏ _ : InfinitePlace F, g := by
        simp only [Finset.prod_mul_distrib]
      _ = _ := by
        rw [← Complex.ofReal_prod Finset.univ B,
          ← smoothProdCpow A (fun w => (hA w).le) s]
        simp only [Finset.prod_const, Finset.card_univ, numComplex]
  have hm := ArtinPrimitiveRoots.Proofs.thsol_smooth.bessel_sheet_mellin
    S μ v0 U hUo hUc hU1 hUunit cS hcS s hs
  rw [hprod] at hm
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_left_cancel₀ hπ
  rw [hm]
  change (mU : ℂ) * (((∏ w, B w : ℝ) : ℂ) * (A₀ : ℂ) ^ s * g ^ numComplex F) =
    (Real.pi : ℂ) * ((C₀ : ℂ) * (A₀ : ℂ) ^ s * g ^ numComplex F)
  dsimp only [C₀]
  rw [Complex.ofReal_mul, Complex.ofReal_div]
  field_simp [hπ]

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
  obtain ⟨C₀, A₀, hC₀, hA₀, hM⟩ :=
    ArtinPrimitiveRoots.Proofs.thsol_smooth.gaussian_smoothing_part1
      S μ v0 U hUo hUc hU1 hUunit cS hcS
  refine ⟨C₀, A₀, hC₀, hA₀, hM,
    ArtinPrimitiveRoots.Proofs.thsol_smooth.smoothingKernel C₀ A₀ (numComplex F),
    (ArtinPrimitiveRoots.Proofs.thsol_smooth.smoothing_kernel_regular
      C₀ A₀ hC₀ hA₀ _).1, ?_, ?_, ?_⟩
  · intro N j
    obtain ⟨B, _, hb⟩ := (ArtinPrimitiveRoots.Proofs.thsol_smooth.smoothing_kernel_regular
      C₀ A₀ hC₀ hA₀ _).2 N j
    exact ⟨B, hb⟩
  · intro u hu
    exact ArtinPrimitiveRoots.Proofs.thsol_smooth.smoothing_kernel_convolution
      C₀ A₀ hC₀ hA₀ (numComplex F) (thetaV S μ v0 U cS) hM u hu
  · intro s hs
    rw [(ArtinPrimitiveRoots.Proofs.thsol_smooth.smoothing_kernel_hasMellin
      C₀ A₀ hC₀ hA₀ _ s).2,
      (ArtinPrimitiveRoots.Proofs.thsol_smooth.smoothing_quotient_control
        C₀ A₀ hC₀ hA₀ _).2.1 s, hM s hs]

end AnalysisS

end ArtinPrimitiveRoots.A1.Theta
