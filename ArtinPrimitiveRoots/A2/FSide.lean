import Mathlib
import OAI.NumberTheory.DirichletL.Continuation
import OAI.NumberTheory.DirichletL.ContinuationContour
import OAI.NumberTheory.DirichletL.ContinuationInversion
import OAI.NumberTheory.DirichletL.ContinuationInversion

/-!
# Design draft A2-FSide: A2's own F-side objects (not A1's)

Status: design draft, compiled against Mathlib `d13f23b` only.  Definitions are complete;
analytic statements are `sorry`; the exponent arithmetic of 06-zero-free.tex and the algebraic
identity 05-poisson.tex:692-694 are *proved* (machine check of the paper's numbers).

Objects that depend on A1's S-adic layer (`F_S`, `e(x)`, `R = O_S`, allowed generators,
`χ_𝔭`, `B_m(Z)`) are specified in `A2-DESIGN.md` §5 by A1 node IDs and are not restated here.

* §1 Scales and contour exponents (06:371-387) and the margin table (06:653-674), checked.
* §2 Zero detector: ideal Möbius function, `α_U`, the mollifier `D_U` (06:188-215).
* §3 The principal signal `f_η`, its Mellin transform `𝒯`, and the statement of
     `zf:mellin-identification` in Mathlib-only form (06:691-752).
* §4 The closed local Euler factor and `H_{u,𝔭}` (05:644-699), with the paper's
     `E₁ = 0` identity proved.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField Complex
open MeasureTheory
open Filter
open Asymptotics
open scoped FourierTransform Topology

noncomputable section

namespace ArtinPrimitiveRoots.A2

/-! ## §1 Scales, exponents, margins -/

/-- **def:zf-exponents** (06-zero-free.tex:371-387): `a` from `eq:reflection-scales`. -/
def a : ℝ := 9 / 10
/-- **def:zf-exponents** (06-zero-free.tex:371-387): `b = 133/1000`. -/
def b : ℝ := 133 / 1000
/-- **def:zf-exponents** (06-zero-free.tex:371-387): `M₀ = a + b`. -/
def M0 : ℝ := a + b
/-- **def:zf-exponents** (06-zero-free.tex:371-387): `h₀ = 1 - a`. -/
def h0 : ℝ := 1 - a

/-- **def:zf-exponents** (06-zero-free.tex:371-387): `E_*(σξ,σw,σz)`, the real exponent of `Z`. -/
def Estar (σξ σw σz : ℝ) : ℝ := a / 2 + σξ - 1 + h0 * σz + b * (σw - 1)

/-- **def:zf-exponents** (06-zero-free.tex:371-387): `C_*(ξ) = ξ - 8/15`. -/
def Cstar (ξ : ℂ) : ℂ := ξ - 8 / 15

/-- **zf:principal-row** (06-zero-free.tex:413-417): `δ₁ = 10⁻⁷`. -/
def δ1 : ℝ := 1 / 10 ^ 7

/-- 06:381-382: `a/2 - 1 + h₀/6 = -8/15`, so `C_*(1) = 7/15`. -/
theorem Cstar_constant : a / 2 - 1 + h0 / 6 = -(8 / 15 : ℝ) := by
  norm_num [a, h0]

/-- 05:198-199, 06:651-654: the reflection exponent `(2M₀-1-b)/2 = 933/2000 = 7/15 - 1/6000`. -/
theorem probe_exponent : (2 * M0 - 1 - b) / 2 = 933 / 2000 ∧
    (933 / 2000 : ℝ) = 7 / 15 - 1 / 6000 := by
  constructor <;> norm_num [M0, a, b]

/-- 06:442-443: `E_*(σ₁, .95, ζ₁) - C_*(1) = (1+h₀)δ₁ - .05b = -.00664989`. -/
theorem margin_Rw : Estar (1 + δ1) (95 / 100) (1 / 6 + δ1) - 7 / 15 = -(664989 / 10 ^ 8) := by
  norm_num [Estar, a, b, h0, δ1]

/-- 06:444-446: `E_*(σ₁, 1, .16) - C_*(1) = δ₁ + h₀(.16 - 1/6) = 10⁻⁷ - 1/1500`. -/
theorem margin_Rz : Estar (1 + δ1) 1 (16 / 100) - 7 / 15 = 1 / 10 ^ 7 - 1 / 1500 := by
  norm_num [Estar, a, b, h0, δ1]

/-- 06:540-545: `E_*(σ₁, .003, .4) - C_*(1) = 10⁻⁷ + 7/300 - .132601`. -/
theorem margin_contour : Estar (1 + δ1) (3 / 1000) (4 / 10) - 7 / 15 =
    1 / 10 ^ 7 + 7 / 300 - 132601 / 10 ^ 6 := by
  norm_num [Estar, a, b, h0, δ1]

/-- 06:547-550: rows `U ≤ Z^{.09}` (α = 1): relative exponent `< 0`. -/
theorem margin_small_rows :
    Estar (1 + δ1) (3 / 1000) (4 / 10) - 7 / 15 + (9 / 100) * (11 / 10) < 0 := by
  norm_num [Estar, a, b, h0, δ1]

/-- 06:558-560: exceptional rows `U ≤ Z^{.10001}` (α = 1/2): relative exponent `< 0`. -/
theorem margin_exceptional_rows :
    Estar (1 + δ1) (3 / 1000) (4 / 10) - 7 / 15 + (10001 / 100000) * (6 / 10) < 0 := by
  norm_num [Estar, a, b, h0, δ1]

/-- 06:574-581: good central rows: `E_*(.998,.003,.4) - C_*(1) + .10001·1.1 = -377/300000`. -/
theorem margin_good_rows :
    Estar (998 / 1000) (3 / 1000) (4 / 10) - 7 / 15 + (10001 / 100000) * (11 / 10) =
      -(377 / 300000) := by
  norm_num [Estar, a, b, h0]

/-- 06:617-628: far rows, `R₀ = 350000`: `E_*(4,4,R₀) + .10001(1-R₀) = .44901 < 7/15 - .01`. -/
theorem margin_far_rows :
    Estar 4 4 350000 + (10001 / 100000) * (1 - 350000) = 44901 / 100000 ∧
      (44901 / 100000 : ℝ) < 7 / 15 - 1 / 100 := by
  constructor <;> norm_num [Estar, a, b, h0]

/-- 06:682-690, 06:713-718: `1/6000 - 10⁻⁵ > 1/20000` and `1 - 1/20000 < 1 - 10⁻⁶`. -/
theorem final_margins : (1 : ℝ) / 6000 - 1 / 10 ^ 5 > 1 / 20000 ∧
    (1 : ℝ) - 1 / 20000 < 1 - 1 / 10 ^ 6 := by
  constructor <;> norm_num

/-- 06:256-257 and 06:316-323: detector exponents at `β = σ₀ = .996`:
`10(1/2 - β) + 1/2 + 1 = -3.46` and `11(2 - 2σ₀) = .088`. -/
theorem detector_exponents : (10 : ℝ) * (1 / 2 - 996 / 1000) + 1 / 2 + 1 = -(346 / 100) ∧
    (11 : ℝ) * (2 - 2 * (996 / 1000)) = 88 / 1000 := by
  constructor <;> norm_num

/-! ## §2 Zero detector (06:188-215) -/

variable {K : Type*} [Field K] [NumberField K]

open Classical in
/-- **def:zf-detector** (06-zero-free.tex:188-215): the Möbius function of integral ideals of
`𝓞_K`, `(-1)^{#prime factors}` on squarefree
nonzero ideals, `0` otherwise. -/
def idealMoebius (I : Ideal (𝓞 K)) : ℤ :=
  if I ≠ ⊥ ∧ Squarefree I then (-1) ^ (UniqueFactorizationMonoid.normalizedFactors I).card
  else 0

open Classical in
/-- **def:zf-detector** (06-zero-free.tex:188-215): `α_U(𝔫) = Σ_{𝔡 ∣ 𝔫, N𝔡 ≤ U²} μ_K(𝔡)`, as a sum over sets of distinct prime factors
(the squarefree divisors). -/
def detectorCoeff (U : ℝ) (I : Ideal (𝓞 K)) : ℤ :=
  ∑ T ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset.powerset,
    if ((∏ P ∈ T, Ideal.absNorm P : ℕ) : ℝ) ≤ U ^ 2 then (-1) ^ T.card else 0

open Classical in
/-- **def:zf-detector** (06-zero-free.tex:188-215): mollifier `D_U(s,f)`. -/
def mollifier (U : ℝ) (f : Ideal (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊U ^ 2⌋₊).toFinset,
    (idealMoebius I : ℂ) * f I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)

/-- **def:zf-detector** (06-zero-free.tex:188-215): for `f` completely multiplicative with `‖f‖ ≤ 1`
and `Re s > 1`, `(Σ_𝔞 f(𝔞) N𝔞^{-s}) · D_U(s,f) = Σ_𝔫 α_U(𝔫) f(𝔫) N𝔫^{-s}`;
`α_U((1)) = 1`; `α_U(𝔫) = 0` for `1 < N𝔫 ≤ U²`; `|α_U(𝔫)| ≤ τ_K(𝔫)`.
Consumers: A2 `zf:detector-shift`, `zf:detector-count`.  (Ideal sums as `tsum` over the
nonzero ideals.) -/
theorem detector_identity (U : ℝ) (hU : 1 ≤ U) (f : Ideal (𝓞 K) → ℂ)
    (hmul : ∀ I J, f (I * J) = f I * f J) (hb : ∀ I, ‖f I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, f I * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) *
        mollifier U f s =
      ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, (detectorCoeff U (I : Ideal (𝓞 K)) : ℂ) * f I *
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) ∧
    detectorCoeff U (⊤ : Ideal (𝓞 K)) = 1 ∧
    (∀ I : Ideal (𝓞 K), I ≠ ⊥ → 1 < Ideal.absNorm I → ((Ideal.absNorm I : ℕ) : ℝ) ≤ U ^ 2 →
      detectorCoeff U I = 0) := sorry

/-! ## §3 The principal signal and its Mellin transform (06:458-476, 06:691-752) -/

/-- **def:zf-principal-mellin** (06-zero-free.tex:691-712): amplitude `𝒜(s)`. -/
def amplitude (H L : ℂ → ℂ) (s : ℂ) : ℂ := exp ((s - 5 / 6) ^ 2) * H s / L s

/-- **def:zf-principal-mellin** (06-zero-free.tex:458-469): `f_η(Z)` on the line `ξ = 2 + it`
(06:464-466; `dξ = i dt`). -/
def fEta (H L : ℂ → ℂ) (Z : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t : ℝ, (Z : ℂ) ^ Cstar (2 + t * I) * amplitude H L (2 + t * I)

/-- **def:zf-principal-mellin** (06-zero-free.tex:709-712): Mellin transform `𝒯(s)` via Mathlib's
`mellin f w = ∫_0^∞ t^{w-1} f(t) dt`. -/
def mellinT (f : ℝ → ℂ) (s : ℂ) : ℂ := mellin f (-Cstar s)

private def z3MellinSignal (H L : ℂ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (c : ℂ) * mellinInv (-2) (fun s => amplitude H L (-s)) x

private def z3Quotient (H L : ℂ → ℂ) (s : ℂ) : ℂ := H s * (L s)⁻¹

private theorem z3Quotient_differentiableOn (H L : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0) :
  DifferentiableOn ℂ (z3Quotient H L) {s : ℂ | 1 < s.re} := by
  apply DifferentiableOn.mul
  · exact hH.mono (by
      intro s hs
      change 1 < s.re at hs
      exact lt_trans (by norm_num : (998 : ℝ) / 1000 < 1) hs)
  · exact hL.inv hL0

private theorem z3Amplitude_differentiableOn (H L : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0) :
    DifferentiableOn ℂ (amplitude H L) {s : ℂ | 1 < s.re} := by
  have he : Differentiable ℂ (fun s : ℂ => exp ((s - 5 / 6) ^ 2)) := by
    exact (((differentiable_id.sub_const (5 / 6 : ℂ)).pow 2).cexp)
  have hq := z3Quotient_differentiableOn H L hH hL hL0
  convert he.differentiableOn.mul hq using 1
  ext s
  simp [amplitude, z3Quotient, div_eq_mul_inv, mul_assoc]

private theorem z3Quotient_norm_bound (H L : ℂ → ℂ)
    (hHb : ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖H s‖ ≤ B)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B)
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖z3Quotient H L s‖ ≤ (Classical.choose hHb + 1) * (Classical.choose hLb + 1) := by
  have hBH := hHb.choose_spec s (by linarith [hs])
  have hBL := hLb.choose_spec s hs
  have hHpos : 0 ≤ Classical.choose hHb := le_trans (norm_nonneg _) hBH
  have hLpos : 0 ≤ Classical.choose hLb := le_trans (norm_nonneg _) hBL
  rw [z3Quotient, norm_mul]
  calc
    ‖H s‖ * ‖(L s)⁻¹‖ ≤ Classical.choose hHb * Classical.choose hLb :=
      mul_le_mul hBH hBL (norm_nonneg _) hHpos
    _ ≤ (Classical.choose hHb + 1) * (Classical.choose hLb + 1) := by
      nlinarith [hHpos, hLpos]

private theorem z3Amplitude_continuous_line (H L : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0) :
    Continuous (fun t : ℝ => amplitude H L ((2 : ℂ) + t * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hAmp := z3Amplitude_differentiableOn H L hH hL hL0
  have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 ((2 : ℂ) + t * I) :=
    (Complex.isOpen_re_gt 1).mem_nhds (by show 1 < (((2 : ℂ) + t * I).re); simp)
  have hd : DifferentiableAt ℂ (amplitude H L) ((2 : ℂ) + t * I) := by
    exact hAmp.differentiableAt hmem
  have hm : Continuous (fun t : ℝ => (2 : ℂ) + t * I) := by fun_prop
  exact hd.continuousAt.comp (f := fun t : ℝ => (2 : ℂ) + t * I) hm.continuousAt

private theorem z3Amplitude_integrable_line (H L : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hHb : ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖H s‖ ≤ B)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B) :
    Integrable (fun t : ℝ => amplitude H L ((2 : ℂ) + t * I)) := by
  have hcont := z3Amplitude_continuous_line H L hH hL hL0
  have hbound (t : ℝ) :
      ‖amplitude H L ((2 : ℂ) + t * I)‖ ≤
        (Real.exp ((2 - 5 / 6 : ℝ) ^ 2) *
          ((Classical.choose hHb + 1) * (Classical.choose hLb + 1))) *
            Real.exp (-(t ^ 2)) := by
    have hq := z3Quotient_norm_bound H L hHb hLb (s := (2 : ℂ) + t * I) (by simp)
    have hAmpEq : amplitude H L ((2 : ℂ) + t * I) =
        Complex.exp (((2 : ℂ) + t * I - 5 / 6) ^ 2) *
          z3Quotient H L ((2 : ℂ) + t * I) := by
      simp [amplitude, z3Quotient, div_eq_mul_inv, mul_assoc]
    rw [hAmpEq]
    change ‖Complex.exp (((2 : ℂ) + t * I - 5 / 6) ^ 2) *
      z3Quotient H L ((2 : ℂ) + t * I)‖ ≤ _
    rw [norm_mul, Complex.norm_exp]
    have hre : (((2 : ℂ) + t * I - 5 / 6) ^ 2).re = (2 - 5 / 6 : ℝ) ^ 2 - t ^ 2 := by
      simp [pow_two]
    rw [hre, Real.exp_sub]
    rw [Real.exp_neg]
    calc
      _ = Real.exp ((2 - 5 / 6 : ℝ) ^ 2) *
          ‖z3Quotient H L ((2 : ℂ) + t * I)‖ * (Real.exp (t ^ 2))⁻¹ := by ring
      _ ≤ Real.exp ((2 - 5 / 6 : ℝ) ^ 2) *
          ((Classical.choose hHb + 1) * (Classical.choose hLb + 1)) *
          (Real.exp (t ^ 2))⁻¹ := by
        have h1 : 0 ≤ Real.exp ((2 - 5 / 6 : ℝ) ^ 2) := (Real.exp_pos _).le
        have h2 : 0 ≤ (Real.exp (t ^ 2))⁻¹ := inv_nonneg.mpr (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq h1) h2
      _ = _ := by ring
  exact OAI.SevenEighths.Continuation.integrable_of_gaussian_bound _ _
    hcont.aestronglyMeasurable hbound

set_option maxHeartbeats 500000 in
private theorem z3Amplitude_integrable_reflected (H L : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hHb : ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖H s‖ ≤ B)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B) :
    Integrable (fun y : ℝ => amplitude H L ((2 : ℂ) - 2 * Real.pi * y * I)) := by
  have h := (z3Amplitude_integrable_line H L hH hL hL0 hHb hLb).comp_mul_left'
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
  convert h using 1
  ext y
  congr 1
  push_cast
  ring

private theorem z3Amplitude_continuous_reflected (H L : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0) :
    Continuous (fun y : ℝ => amplitude H L ((2 : ℂ) - 2 * Real.pi * y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hAmp := z3Amplitude_differentiableOn H L hH hL hL0
  have hz : 1 < ((2 : ℂ) - 2 * Real.pi * y * I).re := by simp
  have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 ((2 : ℂ) - 2 * Real.pi * y * I) :=
    (Complex.isOpen_re_gt 1).mem_nhds hz
  have hd : DifferentiableAt ℂ (amplitude H L) ((2 : ℂ) - 2 * Real.pi * y * I) :=
    hAmp.differentiableAt hmem
  have hm : Continuous (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) := by fun_prop
  exact hd.continuousAt.comp (f := fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) hm.continuousAt

private theorem z3MellinSignal_continuousOn (H L : ℂ → ℂ) (c : ℝ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hHb : ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖H s‖ ≤ B)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B) :
    ContinuousOn (z3MellinSignal H L c) (Set.Ioi 0) := by
  let F : ℝ → ℂ := fun y => amplitude H L ((2 : ℂ) - 2 * Real.pi * y * I)
  have hF : Integrable F := by
    exact z3Amplitude_integrable_reflected H L hH hL hL0 hHb hLb
  have hFourier : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hF
  have hInv : Continuous (𝓕⁻ F) := by
    have heq : 𝓕⁻ F = fun w : ℝ => 𝓕 F (-w) := funext (Real.fourierInv_eq_fourier_neg F)
    rw [heq]
    exact hFourier.comp continuous_neg
  have hpow (z : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ) ^ z) (Set.Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const
      (fun _ hx => Complex.ofReal_mem_slitPlane.mpr hx)
  have hlog : ContinuousOn (fun x : ℝ => -Real.log x) (Set.Ioi 0) := by
    intro x hx
    exact (Real.continuousAt_log hx.ne').neg.continuousWithinAt
  have hcomp : ContinuousOn (fun x : ℝ => 𝓕⁻ F (-Real.log x)) (Set.Ioi 0) :=
    hInv.comp_continuousOn hlog
  have hG : ContinuousOn
      (fun x : ℝ => (x : ℂ) ^ (c : ℂ) *
        ((x : ℂ) ^ (2 : ℂ) * 𝓕⁻ F (-Real.log x))) (Set.Ioi 0) :=
    (hpow (c : ℂ)).mul ((hpow (2 : ℂ)).mul hcomp)
  apply hG.congr
  intro x hx
  unfold z3MellinSignal
  rw [mellinInv_eq_fourierInv _ _ hx]
  simp only [smul_eq_mul, Complex.ofReal_neg, neg_neg, Complex.ofReal_ofNat,
    F, Pi.mul_apply, Function.comp_apply]
  have hfun : (fun y : ℝ => amplitude H L (-((-2 : ℂ) +
      2 * Real.pi * y * I))) = F := by
    funext y
    dsimp [F]
    congr 1
    push_cast
    ring
  rw [hfun]

private theorem z3MellinSignal_locallyIntegrable (H L : ℂ → ℂ) (c : ℝ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hHb : ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖H s‖ ≤ B)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B) :
    LocallyIntegrableOn (z3MellinSignal H L c) (Set.Ioi 0) :=
  (z3MellinSignal_continuousOn H L c hH hL hL0 hHb hLb).locallyIntegrableOn
    measurableSet_Ioi

private theorem z3MellinSignal_eq_contour (H L : ℂ → ℂ) (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    z3MellinSignal H L c Z =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ y : ℝ, OAI.SevenEighths.Continuation.gaussianContourIntegrand
          (z3Quotient H L) c Z ((2 : ℂ) + y * I) := by
  unfold z3MellinSignal mellinInv
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold OAI.SevenEighths.Continuation.gaussianContourIntegrand amplitude z3Quotient
  have he : -(((-2 : ℝ) : ℂ) + (-t : ℝ) * I) = (2 : ℂ) + t * I := by push_cast; ring
  rw [he, ← mul_assoc, ← Complex.cpow_add]
  · ring_nf
  · exact Complex.ofReal_ne_zero.mpr hZ.ne'

private theorem z3MellinSignal_eq_fEta (H L : ℂ → ℂ) {Z : ℝ} (hZ : 0 < Z) :
    z3MellinSignal H L (-(8 / 15 : ℝ)) Z = fEta H L Z := by
  rw [z3MellinSignal_eq_contour H L (-(8 / 15 : ℝ)) hZ]
  unfold fEta
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [OAI.SevenEighths.Continuation.gaussianContourIntegrand,
    Cstar, amplitude, z3Quotient, div_eq_mul_inv]
  have he : (2 : ℂ) + (t : ℂ) * I +
      (((-(8 * (15 : ℝ)⁻¹)) : ℝ) : ℂ) =
      (2 : ℂ) + (t : ℂ) * I - (8 : ℂ) * (15 : ℂ)⁻¹ := by
    push_cast
    ring
  have hpow := congrArg (fun w : ℂ => (Z : ℂ) ^ w) he
  rw [hpow]
  ring

private theorem z3MellinSignal_small_bound (H L : ℂ → ℂ) (B : ℝ) (hB : 2 ≤ B)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hHb : ∃ b : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖H s‖ ≤ b)
    (hLb : ∃ b : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z : ℝ, 0 < Z → Z ≤ 1 →
      ‖z3MellinSignal H L (-(8 / 15 : ℝ)) Z‖ ≤ C * Z ^ (B - 8 / 15) := by
  let K : ℝ := (Classical.choose hHb + 1) * (Classical.choose hLb + 1)
  let C : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖ * Real.exp ((B - 5 / 6) ^ 2) * K *
    ∫ t : ℝ, Real.exp (-(t ^ 2))
  have hK : 0 ≤ K := by
    dsimp [K]
    have h1 : 0 ≤ Classical.choose hHb :=
      le_trans (norm_nonneg _) (hHb.choose_spec 2 (by norm_num))
    have h2 : 0 ≤ Classical.choose hLb :=
      le_trans (norm_nonneg _) (hLb.choose_spec 2 (by norm_num))
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    have hg : 0 ≤ ∫ t : ℝ, Real.exp (-(t ^ 2)) :=
      integral_nonneg (fun _ => (Real.exp_pos _).le)
    positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ hZ1
  have hQ : DifferentiableOn ℂ (z3Quotient H L) {s : ℂ | 1 < s.re} :=
    z3Quotient_differentiableOn H L hH hL hL0
  let F : ℂ → ℂ := OAI.SevenEighths.Continuation.gaussianContourIntegrand
    (z3Quotient H L) (-(8 / 15 : ℝ)) Z
  have hFdiff : DifferentiableOn ℂ F {s : ℂ | 2 ≤ s.re ∧ s.re ≤ B} := by
    apply OAI.SevenEighths.Continuation.gaussianContourIntegrand_differentiableOn
      (hQ.mono (by intro s hs; exact lt_of_lt_of_le (by norm_num) hs.1)) _ hZ
  have hFbound : ∀ x ∈ Set.Icc (2 : ℝ) B, ∀ t : ℝ,
      ‖F ((x : ℂ) + t * I)‖ ≤
        (Z ^ ((2 : ℝ) - 8 / 15) * Real.exp ((B - 5 / 6) ^ 2) * K) *
          Real.exp (-(t ^ 2)) := by
    intro x hx t
    dsimp [F]
    rw [OAI.SevenEighths.Continuation.norm_gaussianContourIntegrand _ _ _ _ hZ]
    have hq := z3Quotient_norm_bound H L hHb hLb (s := (x : ℂ) + t * I) (by simpa using hx.1)
    have hpow : Z ^ (x - 8 / 15 : ℝ) ≤ Z ^ ((2 : ℝ) - 8 / 15) :=
      Real.rpow_le_rpow_of_exponent_ge (x := Z) (y := x - 8 / 15)
        (z := (2 : ℝ) - 8 / 15) hZ hZ1 (by linarith [hx.1])
    have hexp : Real.exp ((x - 5 / 6) ^ 2) ≤ Real.exp ((B - 5 / 6) ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hx.1, hx.2]
    calc
      _ = (Z ^ (x - 8 / 15) * Real.exp ((x - 5 / 6) ^ 2) *
          ‖z3Quotient H L ((x : ℂ) + t * I)‖) * Real.exp (-(t ^ 2)) := by ring
      _ ≤ (Z ^ ((2 : ℝ) - 8 / 15) * Real.exp ((B - 5 / 6) ^ 2) * K) *
          Real.exp (-(t ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        calc
          _ = (Z ^ (x - 8 / 15) * Real.exp ((x - 5 / 6) ^ 2)) *
              ‖z3Quotient H L ((x : ℂ) + t * I)‖ := by ring
          _ ≤ (Z ^ ((2 : ℝ) - 8 / 15) * Real.exp ((B - 5 / 6) ^ 2)) * K := by
            exact mul_le_mul (mul_le_mul hpow hexp (by positivity) (by positivity))
              hq (norm_nonneg _) (by positivity)
          _ = _ := by ring
  have hshift := OAI.SevenEighths.Continuation.vertical_integral_eq_of_gaussian_bound
    F (a := 2) (b := B) (C := Z ^ ((2 : ℝ) - 8 / 15) * Real.exp ((B - 5 / 6) ^ 2) * K)
      hB hFdiff hFbound
  have hendpoint : ‖(1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F ((B : ℂ) + t * I)‖ ≤ C * Z ^ (B - 8 / 15) := by
    have hgauss : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
      simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
    have hnorm (t : ℝ) : ‖F ((B : ℂ) + t * I)‖ ≤
        (Z ^ (B - 8 / 15) * Real.exp ((B - 5 / 6) ^ 2) * K) * Real.exp (-(t ^ 2)) := by
      dsimp [F]
      rw [OAI.SevenEighths.Continuation.norm_gaussianContourIntegrand _ _ _ _ hZ]
      have hq := z3Quotient_norm_bound H L hHb hLb
        (s := (B : ℂ) + t * I) (by simpa using hB)
      have he : B + (-(8 / 15 : ℝ)) = B - 8 / 15 := by ring
      rw [he]
      calc
        _ = (Z ^ (B - 8 / 15) * Real.exp ((B - 5 / 6) ^ 2) *
            ‖z3Quotient H L ((B : ℂ) + t * I)‖) * Real.exp (-(t ^ 2)) := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left hq (mul_nonneg
            (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le)
    have hint := norm_integral_le_of_norm_le
      (hgauss.const_mul (Z ^ (B - 8 / 15) * Real.exp ((B - 5 / 6) ^ 2) * K))
      (f := fun t : ℝ => F ((B : ℂ) + t * I)) (ae_of_all _ hnorm)
    have hmul := mul_le_mul_of_nonneg_left hint (norm_nonneg (1 / (2 * Real.pi) : ℂ))
    rw [integral_const_mul] at hmul
    dsimp [C]
    simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
  rw [z3MellinSignal_eq_contour H L (-(8 / 15 : ℝ)) hZ]
  change ‖(1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F ((2 : ℂ) + t * I)‖ ≤ _
  calc
    ‖(1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F ((2 : ℂ) + t * I)‖ =
        ‖(1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F ((B : ℂ) + t * I)‖ := by
      congr 1
      have hshift' : (∫ t : ℝ, F ((2 : ℂ) + t * I)) =
          ∫ t : ℝ, F ((B : ℂ) + t * I) := by
        simpa only [Complex.ofReal_ofNat] using hshift
      rw [hshift']
    _ ≤ _ := hendpoint

private theorem z3MellinSignal_normalized (H L : ℂ → ℂ) (c : ℝ) {x : ℝ}
    (hx : 0 < x) :
    OAI.SevenEighths.Continuation.normalizedSignal (z3MellinSignal H L c) c x =
      mellinInv (-2) (fun s => amplitude H L (-s)) x := by
  unfold OAI.SevenEighths.Continuation.normalizedSignal z3MellinSignal
  simp only [smul_eq_mul, ← mul_assoc]
  rw [Complex.cpow_neg, inv_mul_cancel₀]
  · simp
  · exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hx.ne'])

private theorem z3MellinSignal_rapidDecayAtZero (H L : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hHb : ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖H s‖ ≤ B)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B) :
    OAI.SevenEighths.Continuation.RapidDecayAtZero
      (z3MellinSignal H L (-(8 / 15 : ℝ))) := by
  intro R
  let B : ℝ := max 2 (R + 8 / 15)
  obtain ⟨C, hC, hsmall⟩ := z3MellinSignal_small_bound H L B
    (le_max_left _ _) hH hL hL0 hHb hLb
  apply IsBigO.of_bound C
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with x hx hx1
  have hpow : x ^ (B - 8 / 15) ≤ x ^ R :=
    Real.rpow_le_rpow_of_exponent_ge (x := x) (y := B - 8 / 15) (z := R)
      hx (by simpa using hx1) (by dsimp [B]; linarith [le_max_right 2 (R + 8 / 15)])
  have hb := hsmall x hx (by simpa using hx1)
  have h := hb.trans (mul_le_mul_of_nonneg_left hpow hC)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.le R)] using h

private theorem z3MellinSignal_top_isBigO (H L : ℂ → ℂ)
    (hlarge : ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
      ‖fEta H L Z‖ ≤ C * Z ^ ((7 : ℝ) / 15 - 1 / 20000)) :
    z3MellinSignal H L (-(8 / 15 : ℝ)) =O[atTop]
      (fun Z : ℝ => Z ^ ((7 : ℝ) / 15 - 1 / 20000)) := by
  obtain ⟨C, Z₀, hC⟩ := hlarge
  apply IsBigO.of_bound (|C| + 1)
  filter_upwards [eventually_ge_atTop (max Z₀ 1)] with Z hZ
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right Z₀ 1) hZ)
  have hsignal := z3MellinSignal_eq_fEta H L hZ0
  have hlargeZ := hC Z (le_trans (le_max_left Z₀ 1) hZ)
  rw [← hsignal] at hlargeZ
  have hpow : 0 ≤ Z ^ ((7 : ℝ) / 15 - 1 / 20000) :=
    Real.rpow_nonneg hZ0.le _
  calc
    ‖z3MellinSignal H L (-(8 / 15 : ℝ)) Z‖ ≤
        C * Z ^ ((7 : ℝ) / 15 - 1 / 20000) := hlargeZ
    _ ≤ (|C| + 1) * Z ^ ((7 : ℝ) / 15 - 1 / 20000) := by
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hpow
    _ = (|C| + 1) * ‖Z ^ ((7 : ℝ) / 15 - 1 / 20000)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hpow]

private theorem z3MellinSignal_mellinLine (H L : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hHb : ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖H s‖ ≤ B)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B)
    (hlarge : ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
      ‖fEta H L Z‖ ≤ C * Z ^ ((7 : ℝ) / 15 - 1 / 20000)) (t : ℝ) :
    OAI.SevenEighths.Continuation.signalMellin
      (z3MellinSignal H L (-(8 / 15 : ℝ))) (-(8 / 15 : ℝ))
      ((2 : ℂ) - 2 * Real.pi * t * I) = amplitude H L ((2 : ℂ) - 2 * Real.pi * t * I) := by
  let c : ℝ := -(8 / 15)
  let a : ℝ := 1 - 1 / 20000
  have hlocal := z3MellinSignal_locallyIntegrable H L c hH hL hL0 hHb hLb
  have hzero := z3MellinSignal_rapidDecayAtZero H L hH hL hL0 hHb hLb
  have htop0 := z3MellinSignal_top_isBigO H L hlarge
  have hexp : (7 : ℝ) / 15 - 1 / 20000 = a + c := by
    dsimp [a, c]
    ring
  have htop : z3MellinSignal H L c =O[atTop] (fun Z : ℝ => Z ^ (a + c)) := by
    simpa only [hexp] using htop0
  have hconv := OAI.SevenEighths.Continuation.signalMellin_convergent
    (z3MellinSignal H L c) a c hlocal htop hzero (s := (2 : ℂ)) (by norm_num [a])
  have hA := z3Amplitude_integrable_reflected H L hH hL hL0 hHb hLb
  have hAc := z3Amplitude_continuous_reflected H L hH hL hL0
  have hrep : ∀ x : ℝ, 0 < x →
      OAI.SevenEighths.Continuation.normalizedSignal
        (z3MellinSignal H L c) c x = mellinInv (-2) (fun s => amplitude H L (-s)) x := by
    intro x hx
    exact z3MellinSignal_normalized H L c hx
  simpa only [c, Complex.ofReal_ofNat] using
    OAI.SevenEighths.Continuation.signalMellin_eq_on_line
      (z3MellinSignal H L c) (amplitude H L) c 2 hconv hA hAc hrep t

private theorem z3HalfPlane_toFun_mem (a : ℝ) (z : ℂ) :
    a < ((((a + Real.exp z.re : ℝ) : ℂ) + (z.im : ℂ) * I).re) := by
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero]
  exact lt_add_of_pos_right _ (Real.exp_pos _)

private noncomputable def z3HalfPlaneHomeomorph (a : ℝ) :
    ℂ ≃ₜ {z : ℂ // a < z.re} where
  toFun z := ⟨((a + Real.exp z.re : ℝ) : ℂ) + (z.im : ℂ) * I,
    z3HalfPlane_toFun_mem a z⟩
  invFun z := ((Real.log (z.1.re - a) : ℝ) : ℂ) + (z.1.im : ℂ) * I
  left_inv z := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero]
      rw [show a + Real.exp z.re - a = Real.exp z.re by ring, Real.log_exp]
    · simp
  right_inv z := by
    apply Subtype.ext
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, sub_zero, Complex.I_im, mul_one, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      rw [Real.exp_log (sub_pos.mpr z.2)]
      ring
    · simp
  continuous_toFun := Continuous.subtype_mk
    (f := fun z : ℂ => ((a + Real.exp z.re : ℝ) : ℂ) + (z.im : ℂ) * I)
    (by fun_prop) (z3HalfPlane_toFun_mem a)
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    let positiveCoord : {z : ℂ // a < z.re} → {x : ℝ // 0 < x} := fun w =>
      ⟨w.1.re - a, sub_pos.mpr w.2⟩
    have hpos : ContinuousAt positiveCoord z := by
      apply (Continuous.subtype_mk (by fun_prop) (fun w => sub_pos.mpr w.2)).continuousAt
    have hlog : ContinuousAt (fun w : {z : ℂ // a < z.re} => Real.log (w.1.re - a)) z := by
      change ContinuousAt (fun w : {z : ℂ // a < z.re} => Real.log (positiveCoord w).1) z
      exact Real.continuous_log'.continuousAt.comp hpos
    have hreal : ContinuousAt
        (fun w : {z : ℂ // a < z.re} => (Real.log (w.1.re - a) : ℂ)) z :=
      Complex.continuous_ofReal.continuousAt.comp hlog
    have himag : ContinuousAt
        (fun w : {z : ℂ // a < z.re} => (w.1.im : ℂ) * I) z :=
      (Complex.continuous_ofReal.continuousAt.comp
        (Complex.continuous_im.continuousAt.comp continuous_subtype_val.continuousAt)).mul_const _
    change ContinuousAt
      (fun w : {z : ℂ // a < z.re} =>
        (Real.log (w.1.re - a) : ℂ) + (w.1.im : ℂ) * I) z
    exact hreal.add himag

private theorem z3HalfPlane_sdiff_finset_preconnected (a : ℝ) (P : Finset ℂ) :
    IsPreconnected ({z : ℂ | a < z.re} \ (P : Set ℂ)) := by
  let e := z3HalfPlaneHomeomorph a
  let A : Set {z : ℂ // a < z.re} := {z | (z.1 : ℂ) ∈ P}
  let T : Set ℂ := e.symm '' A
  have hA : A.Finite := by
    dsimp [A]
    exact P.finite_toSet.preimage (by
      intro x hx y hy hxy
      exact Subtype.ext hxy)
  have hT : T.Finite := by exact hA.image e.symm
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hpathC : IsPathConnected (Tᶜ : Set ℂ) :=
    hT.countable.isPathConnected_compl_of_one_lt_rank hrank
  have hpathS : IsPathConnected (e '' (Tᶜ : Set ℂ)) := hpathC.image e.continuous
  have hpath : IsPathConnected (Subtype.val '' (e '' (Tᶜ : Set ℂ))) :=
    hpathS.image continuous_subtype_val
  have himage : Subtype.val '' (e '' (Tᶜ : Set ℂ)) =
      {z : ℂ | a < z.re} \ (P : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨s, ⟨x, hxT, hxs⟩, hsz⟩
      have hzEq : (e x).1 = z := by simpa [hxs] using hsz
      refine ⟨by simpa [hzEq] using (e x).2, ?_⟩
      intro hzP
      apply hxT
      have heA : e x ∈ A := by simpa [A, hzEq] using hzP
      exact ⟨e x, heA, e.symm_apply_apply x⟩
    · rintro ⟨hzD, hzP⟩
      let s : {z : ℂ // a < z.re} := ⟨z, hzD⟩
      refine ⟨s, ?_, ?_⟩
      · refine ⟨e.symm s, ?_, e.apply_symm_apply s⟩
        intro hxT
        rcases hxT with ⟨s', hs'P, hs'eq⟩
        have hs' : s' = s := e.symm.injective (by simpa using hs'eq)
        have hsA : s ∈ A := by simpa [hs'] using hs'P
        exact hzP (by simpa [A, s] using hsA)
      · rfl
  rw [← himage]
  exact hpath.isConnected.isPreconnected


/-- **zf:mellin-identification** (06-zero-free.tex:709-752), Mathlib-only form.  Its hypotheses
include the small-`Z` half of `zf:f-bounds`.
Hypotheses abstract what the earlier nodes deliver: `H = H_η` holomorphic, nonvanishing and
bounded on `Re s > .998` (`def:po-H-eta`); `L = L^S(·, η)` nonvanishing with `‖L⁻¹‖ ≤ B` on
`Re s ≥ 2` and holomorphic on `Re s > 1` (§2 of A2-HeckeAPI); the large-`Z` bound of
`zf:f-bounds` (`f_η(Z) ≪ Z^{7/15 - 1/20000}`).  Conclusion: every continuation `Λ` of `L` to
`{Re s > 1 - 1/20000}` minus a finite set `P` (the pole `{1}` or `∅`) has no zero off `P`. -/
theorem mellin_identification (H L : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hH0 : ∀ s : ℂ, 998 / 1000 < s.re → H s ≠ 0)
    (hHb : ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖H s‖ ≤ B)
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B)
    (hlarge : ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
      ‖fEta H L Z‖ ≤ C * Z ^ ((7 : ℝ) / 15 - 1 / 20000))
    (P : Finset ℂ) (Λ : ℂ → ℂ)
    (hΛ : DifferentiableOn ℂ Λ ({s : ℂ | 1 - 1 / 20000 < s.re} \ ↑P))
    (hΛL : ∀ s : ℂ, 1 < s.re → Λ s = L s) :
    ∀ s : ℂ, 1 - 1 / 20000 < s.re → s ∉ P → Λ s ≠ 0 := by
  let a : ℝ := 1 - 1 / 20000
  let c : ℝ := -(8 / 15)
  let f : ℝ → ℂ := z3MellinSignal H L c
  let T : ℂ → ℂ := OAI.SevenEighths.Continuation.signalMellin f c
  let U : Set ℂ := {s : ℂ | a < s.re} \ (P : Set ℂ)
  let N : ℂ → ℂ := fun s => Complex.exp ((s - 5 / 6) ^ 2) * H s
  have hlocal : LocallyIntegrableOn f (Set.Ioi 0) := by
    exact z3MellinSignal_locallyIntegrable H L c hH hL hL0 hHb hLb
  have hzero : OAI.SevenEighths.Continuation.RapidDecayAtZero f := by
    simpa [f, c] using z3MellinSignal_rapidDecayAtZero H L hH hL hL0 hHb hLb
  have htop0 := z3MellinSignal_top_isBigO H L hlarge
  have hexp : (7 : ℝ) / 15 - 1 / 20000 = a + c := by
    dsimp [a, c]
    ring
  have htop : f =O[atTop] (fun Z : ℝ => Z ^ (a + c)) := by
    simpa only [f, c, hexp] using htop0
  have hTanalytic : AnalyticOnNhd ℂ T {s : ℂ | a < s.re} := by
    simpa only [T] using
      OAI.SevenEighths.Continuation.signalMellin_analytic f a c hlocal htop hzero
  have hbase : 998 / 1000 < a := by norm_num [a]
  have hHanalytic : DifferentiableOn ℂ H {s : ℂ | a < s.re} :=
    hH.mono (by
      intro s hs
      change a < s.re at hs
      exact lt_trans hbase hs)
  have hExpDiff : Differentiable ℂ (fun s : ℂ =>
      Complex.exp ((s - 5 / 6) ^ 2)) := by
    exact (((differentiable_id.sub_const (5 / 6 : ℂ)).pow 2).cexp)
  have hNdiff : DifferentiableOn ℂ N {s : ℂ | a < s.re} := by
    dsimp [N]
    exact hExpDiff.differentiableOn.mul hHanalytic
  have hDopen : IsOpen {s : ℂ | a < s.re} := Complex.isOpen_re_gt a
  have hNanalytic : AnalyticOnNhd ℂ N {s : ℂ | a < s.re} :=
    (Complex.analyticOnNhd_iff_differentiableOn hDopen).2 hNdiff
  have hNne : ∀ s : ℂ, a < s.re → N s ≠ 0 := by
    intro s hs
    dsimp [N]
    exact mul_ne_zero (Complex.exp_ne_zero _)
      (hH0 s (lt_trans hbase hs))
  have hPclosed : IsClosed (P : Set ℂ) := P.finite_toSet.isClosed
  have hUopen : IsOpen U := by
    dsimp [U]
    exact hDopen.sdiff hPclosed
  have hUpre : IsPreconnected U := by
    simpa only [U] using z3HalfPlane_sdiff_finset_preconnected a P
  have hΛanalytic : AnalyticOnNhd ℂ Λ U := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hUopen).2
    simpa only [U, a] using hΛ
  have hTanalyticU : AnalyticOnNhd ℂ T U :=
    hTanalytic.mono (by intro s hs; exact hs.1)
  have hNanalyticU : AnalyticOnNhd ℂ N U :=
    hNanalytic.mono (by intro s hs; exact hs.1)
  let G : ℂ → ℂ := fun s => Λ s * T s
  have hGanalytic : AnalyticOnNhd ℂ G U := by
    simpa only [G] using hΛanalytic.mul hTanalyticU
  have hlineEq (t : ℝ) :
      G ((2 : ℂ) - 2 * Real.pi * t * I) =
        N ((2 : ℂ) - 2 * Real.pi * t * I) := by
    let s : ℂ := (2 : ℂ) - 2 * Real.pi * t * I
    have hs1 : 1 < s.re := by simp [s]
    have hΛs := hΛL s hs1
    have hTs : T s = amplitude H L s := by
      simpa only [T, f, c, s] using
        z3MellinSignal_mellinLine H L hH hL hL0 hHb hLb hlarge t
    change Λ s * T s = N s
    rw [hΛs, hTs]
    dsimp [N, amplitude]
    field_simp [hL0 s hs1]
  let γ : ℝ := (∑ z ∈ P, |z.im|) + 1
  have hsum : 0 ≤ ∑ z ∈ P, |z.im| := by positivity
  have hγpos : 0 < γ := by dsimp [γ]; linarith
  have hγbound : ∀ z ∈ P, |z.im| < γ := by
    intro z hz
    have hle : |z.im| ≤ ∑ w ∈ P, |w.im| :=
      Finset.single_le_sum (fun w hw => abs_nonneg w.im) hz
    dsimp [γ]
    linarith
  let z₀ : ℂ := (2 : ℂ) + (γ : ℂ) * I
  have hz₀re : z₀.re = 2 := by simp [z₀]
  have hz₀im : z₀.im = γ := by simp [z₀]
  have hz₀P : z₀ ∉ (P : Set ℂ) := by
    intro hz
    have hlt := hγbound z₀ hz
    rw [hz₀im, abs_of_pos hγpos] at hlt
    exact (lt_irrefl γ) hlt
  have hz₀U : z₀ ∈ U := by
    constructor
    · change a < z₀.re
      rw [hz₀re]
      norm_num [a]
    · exact hz₀P
  have hclosure : z₀ ∈ closure ({z : ℂ | G z = N z} \ {z₀}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hUopen z₀ hz₀U
    let q : ℝ := min (r / 2) (ε / 2)
    have hqpos : 0 < q := by dsimp [q]; exact lt_min (by linarith) (by linarith)
    have hqr : q < r := by
      dsimp [q]
      exact (min_le_left _ _).trans_lt (by linarith)
    have hqε : q < ε := by
      dsimp [q]
      exact (min_le_right _ _).trans_lt (by linarith)
    let w : ℂ := z₀ + (q : ℂ) * I
    have hdist : dist z₀ w = q := by
      simp [w, dist_eq_norm, Complex.norm_mul, abs_of_pos hqpos]
    have hwball : w ∈ Metric.ball z₀ r := by
      rw [Metric.mem_ball]
      simpa [dist_comm, hdist] using hqr
    have hwU : w ∈ U := hrball hwball
    have hwne : w ≠ z₀ := by
      intro hw
      have hzero : dist z₀ w = 0 := by simp [hw]
      rw [hdist] at hzero
      exact hqpos.ne' hzero
    let t : ℝ := -(γ + q) / (2 * Real.pi)
    have ht : -2 * Real.pi * t = γ + q := by
      dsimp [t]
      field_simp [Real.pi_ne_zero]
    have hwline : w = (2 : ℂ) - 2 * Real.pi * t * I := by
      apply Complex.ext
      · simp [w, z₀]
      · simp [w, z₀]
        simpa [mul_assoc] using ht.symm
    have hGline : G w = N w := by
      have h := hlineEq t
      rw [← hwline] at h
      exact h
    refine ⟨w, ⟨hGline, hwne⟩, ?_⟩
    have hdist' : dist w z₀ = q := by simpa [dist_comm] using hdist
    calc
      dist z₀ w = dist w z₀ := dist_comm _ _
      _ = q := hdist'
      _ < ε := hqε
  have hGN : Set.EqOn G N U :=
    hGanalytic.eqOn_of_preconnected_of_mem_closure hNanalyticU hUpre hz₀U hclosure
  intro s hs hsP
  have hsU : s ∈ U := ⟨hs, hsP⟩
  have hEq := hGN hsU
  have hNneq := hNne s hs
  intro hΛzero
  have hGzero : G s = 0 := by simp [G, hΛzero]
  rw [hGzero] at hEq
  exact hNneq hEq.symm

/-! ## §4 The closed local Euler factor (05:597-699) -/

/-- **po:euler-good-closed** (05-poisson.tex:597-658): closed formula for `𝓕_{u,𝔭}` at
`𝔭 ∤ (u)R`, in the
variables `Q = N𝔭`, `V = Q^{-6z}`, `W = χ_𝔭(u)Q^{-w}`, `D₁ = η(𝔭)χ̄_𝔭(u)Q^{-ξ}`,
`E₁ = ϑ(𝔭)⁶Q^{4-6ξ}V`. -/
def eulerGoodClosed (Q V W D1 E1 : ℂ) : ℂ :=
  1 / (1 - V) + W / (1 - W) + E1 / (1 - E1) * ((1 - Q⁻¹) / (1 - V) + W) -
    D1 / (1 - E1) * (1 + (Q - 1) * W * V / (1 - V))

/-- **po:H-local-bounds** (05-poisson.tex:660-729): normalized local factor `H_{u,𝔭}`. -/
def Hlocal (Q V W D1 E1 : ℂ) : ℂ := (1 - V) * ((1 - W) / (1 - D1)) * eulerGoodClosed Q V W D1 E1

/-- 05:691-694, checked: at `E₁ = 0`,
`H - 1 = (D₁(W+V-WV) - WV - (Q-1)D₁(1-W)WV)/(1-D₁)`. -/
theorem Hlocal_E1_zero (Q V W D1 : ℂ) (hV : V ≠ 1) (hW : W ≠ 1) (hD : D1 ≠ 1) :
    Hlocal Q V W D1 0 - 1 =
      (D1 * (W + V - W * V) - W * V - (Q - 1) * D1 * (1 - W) * W * V) / (1 - D1) := by
  have hV' : 1 - V ≠ 0 := sub_ne_zero.mpr (Ne.symm hV)
  have hW' : 1 - W ≠ 0 := sub_ne_zero.mpr (Ne.symm hW)
  have hD' : 1 - D1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hD)
  simp only [Hlocal, eulerGoodClosed, zero_div, zero_mul, sub_zero, add_zero]
  field_simp
  ring

end ArtinPrimitiveRoots.A2
