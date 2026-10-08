import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.MeasureSubstrate
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.ComplexPolar
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.RadialScaling
import ArtinPrimitiveRoots.Theta.Proofs.TH_SHEETS.ProductPolar
import ArtinPrimitiveRoots.Theta.Proofs.TH_S_CONV.FourierL1

open MeasureTheory Filter
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
