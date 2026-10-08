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

open MeasureTheory
open scoped FourierTransform

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
