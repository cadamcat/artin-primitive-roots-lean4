import Mathlib

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

/-- **def:ideal-divisor-count** (06-zero-free.tex:145): the ideal divisor function. Located here
per rev-a2 so FSide can state the corrected detector bound without an import cycle. -/
def idealDivisorCount (I : Ideal (𝓞 K)) : ℕ :=
  Set.ncard {J : Ideal (𝓞 K) | J ∣ I}

open Classical in
/-- **def:zf-detector** (06-zero-free.tex:188-215): mollifier `D_U(s,f)`. -/
def mollifier (U : ℝ) (f : Ideal (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊U ^ 2⌋₊).toFinset,
    (idealMoebius I : ℂ) * f I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)

/-- **def:zf-detector** (06-zero-free.tex:188-215): for `f` completely multiplicative with `‖f‖ ≤ 1`
and `Re s > 1`, `(Σ_𝔞 f(𝔞) N𝔞^{-s}) · D_U(s,f) = Σ_𝔫 α_U(𝔫) f(𝔫) N𝔫^{-s}`;
`α_U((1)) = 1`; `α_U(𝔫) = 0` for `1 < N𝔫 ≤ U²`; `|α_U(𝔫)| ≤ τ_K(𝔫)`.
Consumers: A2 `zf:detector-shift`, `zf:detector-count`.  (Ideal sums as `tsum` over the
nonzero ideals.) Corrected per rev-a2 to include the divisor-count bound in the conclusion. -/
theorem detector_identity (U : ℝ) (hU : 1 ≤ U) (f : Ideal (𝓞 K) → ℂ)
    (hmul : ∀ I J, f (I * J) = f I * f J) (hb : ∀ I, ‖f I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, f I * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) *
        mollifier U f s =
      ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, (detectorCoeff U (I : Ideal (𝓞 K)) : ℂ) * f I *
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) ∧
    detectorCoeff U (⊤ : Ideal (𝓞 K)) = 1 ∧
    (∀ I : Ideal (𝓞 K), I ≠ ⊥ → 1 < Ideal.absNorm I → ((Ideal.absNorm I : ℕ) : ℝ) ≤ U ^ 2 →
      detectorCoeff U I = 0) ∧
    (∀ I : Ideal (𝓞 K), I ≠ ⊥ →
      ‖(detectorCoeff U I : ℂ)‖ ≤ idealDivisorCount I) := sorry

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

/-- **zf:mellin-identification** (06-zero-free.tex:709-752), Mathlib-only form. Its hypotheses
include the small-`Z` half of `zf:f-bounds`. Corrected per rev-a2 to state both endpoint bounds.
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
    (hsmall : ∀ A₀ : ℝ, 0 < A₀ → ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 0 < Z → Z ≤ 1 →
        ‖fEta H L Z‖ ≤ C * Real.rpow Z A₀)
    (hlarge : ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        ‖fEta H L Z‖ ≤ C * Real.rpow Z (7 / 15 - 1 / 20000))
    (P : Finset ℂ) (Λ : ℂ → ℂ)
    (hΛ : DifferentiableOn ℂ Λ ({s : ℂ | 1 - 1 / 20000 < s.re} \ ↑P))
    (hΛL : ∀ s : ℂ, 1 < s.re → Λ s = L s) :
    ∀ s : ℂ, 1 - 1 / 20000 < s.re → s ∉ P → Λ s ≠ 0 := sorry

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
