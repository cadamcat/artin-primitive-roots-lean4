import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Shared
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
