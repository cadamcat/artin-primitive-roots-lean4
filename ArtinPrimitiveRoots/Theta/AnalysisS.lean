import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Proofs.TH_S_CONV.FourierL1

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

/-- **eq:sheet-disintegration** (03:487–498): `∫_{F_S^×} f d^×y = π ∫_0^∞ H_f(u) du/u`. -/
theorem sheet_disintegration [IsTotallyComplex F] (μ : ∀ v : FinPlace F, LocHaar v)
    (v0 : InfinitePlace F) (f : S.FS → ℂ) (hf : Integrable f (mulHaarS S μ)) :
    ∫ y, f y ∂(mulHaarS S μ) = Real.pi * ∫ u in Set.Ioi (0 : ℝ), sheetInt S μ v0 f u / u := by
  sorry

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
