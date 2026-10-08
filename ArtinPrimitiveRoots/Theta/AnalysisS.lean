import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.ReciprocalGamma
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.LocalMellin
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.FiniteHaar
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.WeightedHaar
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.CutoffMass
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.ProductMellin

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
