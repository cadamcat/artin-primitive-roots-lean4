import Mathlib
import ArtinPrimitiveRoots.Hecke.Elementary

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

open Classical in
/-- **def:zf-detector** (06-zero-free.tex:188-215): mollifier `D_U(s,f)`. -/
def mollifier (U : ℝ) (f : Ideal (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊U ^ 2⌋₊).toFinset,
    (idealMoebius I : ℂ) * f I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)

private def detectorCutoffSet (U : ℝ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊U ^ 2⌋₊).toFinset

private theorem mem_detectorCutoffSet (U : ℝ) (hU : 1 ≤ U)
    (I : Ideal (𝓞 K)) :
    I ∈ detectorCutoffSet U ↔ ((Ideal.absNorm I : ℕ) : ℝ) ≤ U ^ 2 := by
  simp [detectorCutoffSet, Nat.le_floor_iff (show 0 ≤ U ^ 2 by positivity)]

private abbrev detectorNormFiber (n : ℕ) :=
  {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

private def detectorIdealCoeff (f : Ideal (𝓞 K) → ℂ) (n : ℕ) : ℂ :=
  ∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset,
    if I = ⊥ then 0 else f I

private abbrev detectorTrivialModulus : ClassFieldTheory.RayClassModulus K := ⟨0, ∅⟩

private abbrev detectorTrivialChar :
    ClassFieldTheory.RayClassGroup (detectorTrivialModulus (K := K)) →* ℂˣ := 1

private theorem detectorCharValue_trivial (I : Ideal (𝓞 K)) :
    ArtinPrimitiveRoots.Hecke.charValue (detectorTrivialChar (K := K)) I =
      if I = ⊥ then 0 else 1 := by
  classical
  by_cases hI : I = ⊥
  · simp [ArtinPrimitiveRoots.Hecke.charValue, ArtinPrimitiveRoots.Hecke.IsCoprimeTo, hI]
  · have hcop : ArtinPrimitiveRoots.Hecke.IsCoprimeTo (detectorTrivialModulus (K := K)) I := by
      change ∃ h' : I ≠ ⊥,
        ArtinPrimitiveRoots.Hecke.idealUnit I h' ∈
          ClassFieldTheory.rayClassPrimeToIdeals (detectorTrivialModulus (K := K))
      refine ⟨hI, ?_⟩
      change ∀ v, v ∈ (0 : IsDedekindDomain.HeightOneSpectrum (𝓞 K) →₀ ℕ).support → _
      intro v hv
      simp at hv
    simp [ArtinPrimitiveRoots.Hecke.charValue, hI, hcop]

private theorem detectorTrivialCoeff_eq_card {n : ℕ} (hn : n ≠ 0) :
    ArtinPrimitiveRoots.Hecke.coeff (detectorTrivialChar (K := K)) n =
      (Nat.card (detectorNormFiber (K := K) n) : ℂ) := by
  classical
  unfold ArtinPrimitiveRoots.Hecke.coeff
  let F := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
  calc
    _ = ∑ I ∈ F.toFinset, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [detectorCharValue_trivial]
      have hIn : Ideal.absNorm I = n := F.mem_toFinset.mp hI
      have hI0 : I ≠ ⊥ := by
        intro h
        subst I
        simp at hIn
        exact hn hIn.symm
      simp [hI0]
    _ = (F.toFinset.card : ℂ) := by simp
    _ = (Nat.card (detectorNormFiber (K := K) n) : ℂ) := by
      exact_mod_cast (Nat.card_eq_card_finite_toFinset F).symm

private theorem detector_series_summable (f : Ideal (𝓞 K) → ℂ)
    (hb : ∀ I, ‖f I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      f I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  classical
  let c : ℕ → ℂ := ArtinPrimitiveRoots.Hecke.coeff (detectorTrivialChar (K := K))
  have hc : LSeriesSummable c (s.re : ℂ) := by
    simpa [c, LSeriesSummable] using
      ArtinPrimitiveRoots.Hecke.LSeriesSummable_coeff (detectorTrivialChar (K := K))
        (by simpa using hs)
  have hcnorm : Summable (fun n => ‖LSeries.term c (s.re : ℂ) n‖) := by
    exact hc.norm
  let F (n : ℕ) := detectorNormFiber (K := K) n
  let g : (Σ n, F n) → ℝ := fun p =>
    ‖if p.2.1 = ⊥ then 0 else f p.2.1 * ((Ideal.absNorm p.2.1 : ℕ) : ℂ) ^ (-s)‖
  have hfib (n : ℕ) : Summable (fun I : F n => g ⟨n, I⟩) := by
    letI : Fintype (F n) := @Fintype.ofFinite _
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n)
    exact Summable.of_finite
  have hbound (n : ℕ) : (∑' I : F n, g ⟨n, I⟩) ≤ ‖LSeries.term c (s.re : ℂ) n‖ := by
    by_cases hn : n = 0
    · subst n
      letI : Fintype (F 0) := @Fintype.ofFinite _
        (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) 0)
      have hbot : ∀ I : F 0, I.1 = ⊥ := by
        intro I
        apply Ideal.absNorm_eq_zero_iff.mp
        simpa using I.2
      simp [g, hbot]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      letI : Fintype (F n) := @Fintype.ofFinite _
        (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n)
      have hterm (I : F n) : g ⟨n, I⟩ ≤ Real.rpow (n : ℝ) (-s.re) := by
        have hIbot : I.1 ≠ ⊥ := by
          intro h
          have hzero : Ideal.absNorm I.1 = 0 := by rw [h]; simp
          have h0n : (0 : ℕ) = n := hzero.symm.trans I.2
          exact hn h0n.symm
        have hInorm : Ideal.absNorm I.1 = n := I.2
        have hnormIpos : (0 : ℝ) < (Ideal.absNorm I.1 : ℝ) := by
          rw [hInorm]
          exact hnpos
        have hpow : ‖((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)‖ =
          Real.rpow (n : ℝ) (-s.re) := by
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnormIpos, hInorm]
          congr 1
        change ‖if I.1 = ⊥ then 0 else
          f I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)‖ ≤ _
        rw [if_neg hIbot, norm_mul, hpow]
        calc
          ‖f I.1‖ * Real.rpow (n : ℝ) (-s.re) ≤
              1 * Real.rpow (n : ℝ) (-s.re) :=
            mul_le_mul_of_nonneg_right (hb I.1) (Real.rpow_nonneg hnpos.le _)
          _ = Real.rpow (n : ℝ) (-s.re) := one_mul _
      calc
        (∑' I : F n, g ⟨n, I⟩) = ∑ I : F n, g ⟨n, I⟩ := by rw [tsum_fintype]
        _ ≤ ∑ _I : F n, Real.rpow (n : ℝ) (-s.re) := Finset.sum_le_sum fun I _ => hterm I
        _ = (Nat.card (F n) : ℝ) * Real.rpow (n : ℝ) (-s.re) := by simp
        _ = ‖LSeries.term c (s.re : ℂ) n‖ := by
          rw [LSeries.norm_term_eq, if_neg hn]
          dsimp [c]
          rw [detectorTrivialCoeff_eq_card hn]
          simp only [Complex.norm_natCast]
          rw [Real.rpow_neg hnpos.le]
          ring
  have houter : Summable (fun n => ∑' I : F n, g ⟨n, I⟩) :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg fun I => norm_nonneg _)
      hbound hcnorm
  have hsigma : Summable g :=
    (summable_sigma_of_nonneg (fun p => norm_nonneg _)).mpr ⟨hfib, houter⟩
  let e : (Σ n, F n) ≃ Ideal (𝓞 K) := Equiv.sigmaFiberEquiv Ideal.absNorm
  let φ : Ideal (𝓞 K) → ℝ := fun I =>
    ‖if I = ⊥ then 0 else f I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖
  have hcomp : g = φ ∘ e := by
    funext p
    rfl
  have hfullNorm : Summable (fun I : Ideal (𝓞 K) =>
      ‖if I = ⊥ then 0 else f I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖) := by
    exact e.summable_iff.mp (hcomp ▸ hsigma)
  have hfull : Summable (fun I : Ideal (𝓞 K) =>
      if I = ⊥ then 0 else f I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) :=
    Summable.of_norm hfullNorm
  have hsub := hfull.comp_injective (Subtype.val_injective : Function.Injective
    (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => I.1))
  exact hsub.congr fun I => by simp [I.property]

private abbrev detectorNZIdeal := {I : Ideal (𝓞 K) // I ≠ ⊥}

private abbrev detectorDivisor (D : detectorNZIdeal (K := K)) :=
  {J : detectorNZIdeal (K := K) // D.1 ∣ J.1}

private abbrev detectorDivisorRaw (D : Ideal (𝓞 K)) :=
  {J : detectorNZIdeal (K := K) // D ∣ J.1}

private def detectorMulDivEquiv (D : detectorNZIdeal (K := K)) :
    detectorNZIdeal (K := K) ≃ detectorDivisor D where
  toFun I :=
    ⟨⟨D.1 * I.1, mul_ne_zero D.2 I.2⟩, ⟨I.1, rfl⟩⟩
  invFun J :=
    ⟨Classical.choose J.2, by
      intro h
      have hspec := Classical.choose_spec J.2
      have hbot : J.1.1 = ⊥ := by simpa [h] using hspec
      exact J.1.2 hbot⟩
  left_inv I := by
    apply Subtype.ext
    change Classical.choose (show D.1 ∣ D.1 * I.1 from ⟨I.1, rfl⟩) = I.1
    apply mul_left_cancel₀ D.2
    exact (Classical.choose_spec (show D.1 ∣ D.1 * I.1 from ⟨I.1, rfl⟩)).symm
  right_inv J := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec J.2).symm

private theorem detector_mul_factor (f : Ideal (𝓞 K) → ℂ)
    (hmul : ∀ I J, f (I * J) = f I * f J) (hb : ∀ I, ‖f I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) (D : detectorNZIdeal (K := K)) :
    (∑' I : detectorNZIdeal (K := K),
        f I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) *
        ((idealMoebius D.1 : ℂ) * f D.1 *
          ((Ideal.absNorm D.1 : ℕ) : ℂ) ^ (-s)) =
      ∑' J : detectorDivisor D,
        (idealMoebius D.1 : ℂ) * f J.1.1 *
          ((Ideal.absNorm J.1.1 : ℕ) : ℂ) ^ (-s) := by
  classical
  let a (I : detectorNZIdeal (K := K)) :=
    f I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
  let b := (idealMoebius D.1 : ℂ) * f D.1 *
    ((Ideal.absNorm D.1 : ℕ) : ℂ) ^ (-s)
  have ha : Summable a := detector_series_summable f hb hs
  have hnormmul (I : detectorNZIdeal (K := K)) :
      Ideal.absNorm (D.1 * I.1) = Ideal.absNorm D.1 * Ideal.absNorm I.1 :=
    map_mul Ideal.absNorm D.1 I.1
  have hpow (I : detectorNZIdeal (K := K)) :
      ((Ideal.absNorm (D.1 * I.1) : ℕ) : ℂ) ^ (-s) =
        ((Ideal.absNorm D.1 : ℕ) : ℂ) ^ (-s) *
          ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
    rw [hnormmul]
    simpa only [Nat.cast_mul, Complex.ofReal_natCast] using
      Complex.mul_cpow_ofReal_nonneg
        (show 0 ≤ (Ideal.absNorm D.1 : ℝ) by positivity)
        (show 0 ≤ (Ideal.absNorm I.1 : ℝ) by positivity) (-s)
  have hterm (I : detectorNZIdeal (K := K)) :
      a I * b = (idealMoebius D.1 : ℂ) * f (D.1 * I.1) *
        ((Ideal.absNorm (D.1 * I.1) : ℕ) : ℂ) ^ (-s) := by
    dsimp [a, b]
    rw [hmul D.1 I.1, hpow I]
    ring
  let e := detectorMulDivEquiv D
  let g (J : detectorDivisor D) := (idealMoebius D.1 : ℂ) * f J.1.1 *
    ((Ideal.absNorm J.1.1 : ℕ) : ℂ) ^ (-s)
  calc
    _ = (∑' I : detectorNZIdeal (K := K), a I) * b := by rfl
    _ = ∑' I : detectorNZIdeal (K := K), a I * b :=
      (Summable.tsum_mul_right b ha).symm
    _ = ∑' I : detectorNZIdeal (K := K),
        (idealMoebius D.1 : ℂ) * f (D.1 * I.1) *
          ((Ideal.absNorm (D.1 * I.1) : ℕ) : ℂ) ^ (-s) :=
      tsum_congr fun I => hterm I
    _ = ∑' I : detectorNZIdeal (K := K), g (e I) := by
      apply tsum_congr
      intro I
      simp [e, g, detectorMulDivEquiv, mul_comm]
    _ = ∑' J : detectorDivisor D, g J := e.tsum_eq g

private theorem detector_mul_factor_raw (f : Ideal (𝓞 K) → ℂ)
    (hmul : ∀ I J, f (I * J) = f I * f J) (hb : ∀ I, ‖f I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) (D : Ideal (𝓞 K)) (hD : D ≠ ⊥) :
    (∑' I : detectorNZIdeal (K := K),
        f I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) *
        ((idealMoebius D : ℂ) * f D * ((Ideal.absNorm D : ℕ) : ℂ) ^ (-s)) =
      ∑' J : detectorDivisorRaw D,
        (idealMoebius D : ℂ) * f J.1.1 *
          ((Ideal.absNorm J.1.1 : ℕ) : ℂ) ^ (-s) := by
  let d : detectorNZIdeal (K := K) := ⟨D, hD⟩
  simpa [detectorDivisorRaw, d] using detector_mul_factor f hmul hb hs d

open Classical in
private theorem detectorDivisor_tsum_indicator (D : Ideal (𝓞 K))
    (w : detectorNZIdeal (K := K) → ℂ) :
    (∑' J : detectorDivisorRaw D, w J.1) =
      ∑' J : detectorNZIdeal (K := K),
        if D ∣ J.1 then w J else 0 := by
  classical
  let S : Set (detectorNZIdeal (K := K)) := {J | D ∣ J.1}
  change (∑' J : {J : detectorNZIdeal (K := K) // J ∈ S}, w J.1) =
    ∑' J : detectorNZIdeal (K := K), if D ∣ J.1 then w J else 0
  rw [tsum_subtype S w]
  simp [S, Set.indicator_apply]

private theorem detectorIdealMoebius_norm_le_one (I : Ideal (𝓞 K)) :
    ‖(idealMoebius I : ℂ)‖ ≤ 1 := by
  classical
  unfold idealMoebius
  split_ifs <;> simp

private theorem detector_mul_factor_all (f : Ideal (𝓞 K) → ℂ)
    (hmul : ∀ I J, f (I * J) = f I * f J) (hb : ∀ I, ‖f I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) (D : Ideal (𝓞 K)) :
    (∑' I : detectorNZIdeal (K := K),
        f I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) *
        ((idealMoebius D : ℂ) * f D * ((Ideal.absNorm D : ℕ) : ℂ) ^ (-s)) =
      ∑' J : detectorDivisorRaw D,
        (idealMoebius D : ℂ) * f J.1.1 *
          ((Ideal.absNorm J.1.1 : ℕ) : ℂ) ^ (-s) := by
  classical
  by_cases hD : D = ⊥
  · subst D
    letI : IsEmpty (detectorDivisorRaw (⊥ : Ideal (𝓞 K))) := ⟨fun J => by
      rcases J.2 with ⟨I, hI⟩
      simp at hI
      exact J.1.2 hI⟩
    simp [idealMoebius]
  · exact detector_mul_factor_raw f hmul hb hs D hD

open Classical in
private theorem detectorCoeff_divisor_sum (U : ℝ) (hU : 1 ≤ U)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    detectorCoeff U I =
      ∑ D ∈ detectorCutoffSet U, if D ∣ I then idealMoebius D else 0 := by
  classical
  let P := (UniqueFactorizationMonoid.normalizedFactors I).toFinset
  let A := P.powerset.filter fun T =>
    ((∏ Q ∈ T, Ideal.absNorm Q : ℕ) : ℝ) ≤ U ^ 2
  let B := (detectorCutoffSet U).filter fun D => D ∣ I ∧ Squarefree D
  have hPprime : ∀ Q ∈ P, Prime Q := by
    intro Q hQ
    exact UniqueFactorizationMonoid.prime_of_normalized_factor Q
      (Multiset.mem_toFinset.mp (by simpa [P] using hQ))
  have hTprodne (T : Finset (Ideal (𝓞 K))) (hT : T ∈ P.powerset) :
      (∏ Q ∈ T, Q) ≠ (⊥ : Ideal (𝓞 K)) := by
    have hTP : T ⊆ P := Finset.mem_powerset.mp hT
    apply Finset.prod_ne_zero_iff.mpr
    intro Q hQ
    exact (hPprime Q (hTP hQ)).ne_zero
  have hTfac (T : Finset (Ideal (𝓞 K))) (hT : T ∈ P.powerset) :
      UniqueFactorizationMonoid.normalizedFactors (∏ Q ∈ T, Q) = T.val := by
    have hTP : T ⊆ P := Finset.mem_powerset.mp hT
    simpa using UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
      (fun Q hQ => hPprime Q (hTP hQ))
  have hTdvd (T : Finset (Ideal (𝓞 K))) (hT : T ∈ P.powerset) :
      (∏ Q ∈ T, Q) ∣ I := by
    have hTP : T ⊆ P := Finset.mem_powerset.mp hT
    apply (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
      (hTprodne T hT) hI).mpr
    rw [hTfac T hT]
    apply (Multiset.le_iff_subset T.nodup).mpr
    intro Q hQ
    exact Multiset.mem_toFinset.mp (hTP hQ)
  have hTsquarefree (T : Finset (Ideal (𝓞 K))) (hT : T ∈ P.powerset) :
      Squarefree (∏ Q ∈ T, Q) := by
    apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (hTprodne T hT)).mpr
    rw [hTfac T hT]
    exact T.nodup
  have hTnorm (T : Finset (Ideal (𝓞 K))) (hT : T ∈ P.powerset) :
      Ideal.absNorm (∏ Q ∈ T, Q) = ∏ Q ∈ T, Ideal.absNorm Q := by
    simp only [map_prod]
  have himage : A.image (fun T => ∏ Q ∈ T, Q) = B := by
    ext D
    constructor
    · intro hD
      rcases Finset.mem_image.mp hD with ⟨T, hTA, rfl⟩
      rcases Finset.mem_filter.mp hTA with ⟨hTPow, hTcut⟩
      refine Finset.mem_filter.mpr ⟨?_, hTdvd T hTPow, hTsquarefree T hTPow⟩
      apply (mem_detectorCutoffSet U hU _).2
      have hnorm : ((Ideal.absNorm (∏ Q ∈ T, Q) : ℕ) : ℝ) =
          ((∏ Q ∈ T, Ideal.absNorm Q : ℕ) : ℝ) := by rw [hTnorm T hTPow]
      rw [hnorm]
      exact hTcut
    · intro hD
      rcases Finset.mem_filter.mp hD with ⟨hDcut, hDprop⟩
      rcases hDprop with ⟨hdiv, hsq⟩
      have hDne : D ≠ ⊥ := by
        intro hbot
        subst D
        rcases hdiv with ⟨J, hJ⟩
        simp at hJ
        exact hI hJ
      let T := (UniqueFactorizationMonoid.normalizedFactors D).toFinset
      have hfacle : UniqueFactorizationMonoid.normalizedFactors D ≤
          UniqueFactorizationMonoid.normalizedFactors I :=
        (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hDne hI).mp hdiv
      have hTsub : T ⊆ P := by
        intro Q hQ
        have hQfin : Q ∈ (UniqueFactorizationMonoid.normalizedFactors D).toFinset := by
          simpa only [T] using hQ
        have hQfac : Q ∈ UniqueFactorizationMonoid.normalizedFactors D :=
          Multiset.mem_toFinset.mp hQfin
        exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hfacle hQfac)
      have hTval : T.val = UniqueFactorizationMonoid.normalizedFactors D := by
        have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hDne).mp hsq
        simpa only [T, Multiset.toFinset_val] using hnodup.dedup
      have hDprod : (∏ Q ∈ T, Q) = D := by
        calc
          _ = T.val.prod := (Finset.prod_val _).symm
          _ = (UniqueFactorizationMonoid.normalizedFactors D).prod := by rw [hTval]
          _ = D := Ideal.prod_normalizedFactors_eq_self hDne
      have hTPow : T ∈ P.powerset := Finset.mem_powerset.mpr hTsub
      have hTcut : ((∏ Q ∈ T, Ideal.absNorm Q : ℕ) : ℝ) ≤ U ^ 2 := by
        have hnorm : ((∏ Q ∈ T, Ideal.absNorm Q : ℕ) : ℝ) =
            ((Ideal.absNorm D : ℕ) : ℝ) := by
          rw [← map_prod, hDprod]
        rw [hnorm]
        exact (mem_detectorCutoffSet U hU D).mp hDcut
      refine Finset.mem_image.mpr ⟨T, Finset.mem_filter.mpr ⟨hTPow, hTcut⟩, ?_⟩
      exact hDprod
  have hinj (T : Finset (Ideal (𝓞 K))) (hT : T ∈ A)
      (T' : Finset (Ideal (𝓞 K))) (hT' : T' ∈ A)
      (hEq : (∏ Q ∈ T, Q) = ∏ Q ∈ T', Q) : T = T' := by
    have hfac := congrArg UniqueFactorizationMonoid.normalizedFactors hEq
    rw [hTfac T (Finset.mem_filter.mp hT).1,
      hTfac T' (Finset.mem_filter.mp hT').1] at hfac
    exact Finset.val_inj.mp hfac
  have hsumImage :
      (∑ T ∈ A, (-1 : ℤ) ^ T.card) =
        ∑ D ∈ A.image (fun T => ∏ Q ∈ T, Q), idealMoebius D := by
    apply Finset.sum_bij (fun T _ => ∏ Q ∈ T, Q)
    · intro T hT
      exact Finset.mem_image.mpr ⟨T, hT, rfl⟩
    · intro T hT T' hT' hEq
      exact hinj T hT T' hT' hEq
    · intro D hD
      rw [himage] at hD
      rcases Finset.mem_filter.mp hD with ⟨hDcut, hDprops⟩
      rcases hDprops with ⟨hdiv, hsq⟩
      have hDne : D ≠ ⊥ := by
        intro hbot
        subst D
        rcases hdiv with ⟨J, hJ⟩
        simp at hJ
        exact hI hJ
      let T := (UniqueFactorizationMonoid.normalizedFactors D).toFinset
      have hfacle : UniqueFactorizationMonoid.normalizedFactors D ≤
          UniqueFactorizationMonoid.normalizedFactors I :=
        (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hDne hI).mp hdiv
      have hTsub : T ⊆ P := by
        intro Q hQ
        have hQfin : Q ∈ (UniqueFactorizationMonoid.normalizedFactors D).toFinset := by
          simpa only [T] using hQ
        have hQfac : Q ∈ UniqueFactorizationMonoid.normalizedFactors D :=
          Multiset.mem_toFinset.mp hQfin
        exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hfacle hQfac)
      have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hDne).mp hsq
      have hTval : T.val = UniqueFactorizationMonoid.normalizedFactors D := by
        simpa only [T, Multiset.toFinset_val] using hnodup.dedup
      have hDprod : (∏ Q ∈ T, Q) = D := by
        calc
          _ = T.val.prod := (Finset.prod_val _).symm
          _ = (UniqueFactorizationMonoid.normalizedFactors D).prod := by rw [hTval]
          _ = D := Ideal.prod_normalizedFactors_eq_self hDne
      have hTcut : ((∏ Q ∈ T, Ideal.absNorm Q : ℕ) : ℝ) ≤ U ^ 2 := by
        have hnorm : ((∏ Q ∈ T, Ideal.absNorm Q : ℕ) : ℝ) =
            ((Ideal.absNorm D : ℕ) : ℝ) := by
          rw [← map_prod, hDprod]
        rw [hnorm]
        exact (mem_detectorCutoffSet U hU D).mp hDcut
      refine ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTsub, hTcut⟩, ?_⟩
      rw [hDprod]
    · intro T hT
      have hTpow := (Finset.mem_filter.mp hT).1
      have hsq := hTsquarefree T hTpow
      have hne := hTprodne T hTpow
      simp [idealMoebius, hne, hsq, hTfac T hTpow]
  have hdivSum :
      (∑ D ∈ detectorCutoffSet U, if D ∣ I then idealMoebius D else 0) =
        ∑ D ∈ B, idealMoebius D := by
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro D hD
    by_cases hdiv : D ∣ I
    · by_cases hsq : Squarefree D
      · simp [hdiv, hsq]
      · simp [hdiv, hsq, idealMoebius]
    · simp [hdiv]
  unfold detectorCoeff
  change (∑ T ∈ P.powerset,
    if ((∏ Q ∈ T, Ideal.absNorm Q : ℕ) : ℝ) ≤ U ^ 2 then (-1) ^ T.card else 0) = _
  rw [← Finset.sum_filter]
  calc
    _ = ∑ T ∈ A, (-1 : ℤ) ^ T.card := rfl
    _ = ∑ D ∈ B, idealMoebius D := by rw [hsumImage, himage]
    _ = _ := hdivSum.symm

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
      detectorCoeff U I = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · classical
    let S := detectorCutoffSet (K := K) U
    let aI (I : detectorNZIdeal (K := K)) :=
      f I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
    let bD (D : Ideal (𝓞 K)) :=
      (idealMoebius D : ℂ) * f D * ((Ideal.absNorm D : ℕ) : ℂ) ^ (-s)
    let wD (D : Ideal (𝓞 K)) (J : detectorNZIdeal (K := K)) :=
      if D ∣ J.1 then (idealMoebius D : ℂ) * f J.1 *
        ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) else 0
    have hweightSummable (D : Ideal (𝓞 K)) : Summable (wD D) := by
      have hmu : ‖(idealMoebius D : ℂ)‖ ≤ 1 := detectorIdealMoebius_norm_le_one D
      have hb' : ∀ I, ‖(idealMoebius D : ℂ) * f I‖ ≤ 1 := by
        intro I
        rw [norm_mul]
        calc
          ‖(idealMoebius D : ℂ)‖ * ‖f I‖ ≤ 1 * ‖f I‖ :=
            mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
          _ ≤ 1 := by simpa using hb I
      have hbase := detector_series_summable (fun I => (idealMoebius D : ℂ) * f I) hb' hs
      apply Summable.of_norm_bounded hbase.norm
      intro J
      by_cases hdiv : D ∣ J.1
      · simp [wD, hdiv, norm_mul]
      · change ‖if D ∣ J.1 then
            (idealMoebius D : ℂ) * f J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)
          else 0‖ ≤ ‖(idealMoebius D : ℂ) * f J.1 *
            ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)‖
        rw [if_neg hdiv, norm_zero]
        exact norm_nonneg _
    change (∑' I : detectorNZIdeal (K := K), aI I) *
        (∑ D ∈ S, bD D) =
      ∑' I : detectorNZIdeal (K := K), (detectorCoeff U I.1 : ℂ) * f I.1 *
        ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
    calc
      _ = ∑ D ∈ S, (∑' I : detectorNZIdeal (K := K), aI I) * bD D := by
        rw [Finset.mul_sum]
      _ = ∑ D ∈ S, ∑' J : detectorDivisorRaw D,
            (idealMoebius D : ℂ) * f J.1.1 *
              ((Ideal.absNorm J.1.1 : ℕ) : ℂ) ^ (-s) := by
        apply Finset.sum_congr rfl
        intro D hD
        exact detector_mul_factor_all f hmul hb hs D
      _ = ∑ D ∈ S, ∑' J : detectorNZIdeal (K := K), wD D J := by
        apply Finset.sum_congr rfl
        intro D hD
        exact detectorDivisor_tsum_indicator D (fun J =>
          (idealMoebius D : ℂ) * f J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s))
      _ = ∑' J : detectorNZIdeal (K := K), ∑ D ∈ S, wD D J :=
        (Summable.tsum_finsetSum (s := S) fun D hD => hweightSummable D).symm
      _ = ∑' J : detectorNZIdeal (K := K),
          (detectorCoeff U J.1 : ℂ) * f J.1 *
            ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
        apply tsum_congr
        intro J
        have hcoefC : (detectorCoeff U J.1 : ℂ) =
            ∑ D ∈ S, if D ∣ J.1 then (idealMoebius D : ℂ) else 0 := by
          rw [detectorCoeff_divisor_sum U hU J.1 J.2]
          norm_cast
        have hfactor :
            (∑ D ∈ S, wD D J) =
              (∑ D ∈ S, if D ∣ J.1 then (idealMoebius D : ℂ) else 0) *
                f J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
          calc
            _ = ∑ D ∈ S,
                  (if D ∣ J.1 then (idealMoebius D : ℂ) else 0) * f J.1 *
                    ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
              apply Finset.sum_congr rfl
              intro D hD
              by_cases hdiv : D ∣ J.1 <;> simp [wD, hdiv] <;> ring
            _ = _ := by
              calc
                _ = ∑ D ∈ S,
                      ((if D ∣ J.1 then (idealMoebius D : ℂ) else 0) * f J.1) *
                        ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by rfl
                _ = (∑ D ∈ S,
                      (if D ∣ J.1 then (idealMoebius D : ℂ) else 0) * f J.1) *
                        ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
                  exact (Finset.sum_mul S
                    (fun D => (if D ∣ J.1 then (idealMoebius D : ℂ) else 0) * f J.1)
                    (((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s))).symm
                _ = ((∑ D ∈ S, if D ∣ J.1 then (idealMoebius D : ℂ) else 0) * f J.1) *
                      ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
                  congr 1
                  exact (Finset.sum_mul S
                    (fun D => if D ∣ J.1 then (idealMoebius D : ℂ) else 0)
                    (f J.1)).symm
                _ = _ := by rfl
        rw [hfactor, hcoefC]
  · have hU2 : (1 : ℝ) ≤ U ^ 2 := by nlinarith [sq_nonneg (U - 1)]
    simpa [detectorCoeff, ← Ideal.one_eq_top, hU2]
  · intro I hI hInorm hIU
    let P := (UniqueFactorizationMonoid.normalizedFactors I).toFinset
    have hPne : P.Nonempty := by
      by_contra hne
      have hPempty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hfac : UniqueFactorizationMonoid.normalizedFactors I = 0 :=
        Multiset.toFinset_eq_empty.mp (by simpa [P] using hPempty)
      have hprod := Ideal.prod_normalizedFactors_eq_self hI
      have hItop : I = ⊤ := by
        rw [← Ideal.one_eq_top]
        simpa [hfac] using hprod.symm
      rw [hItop] at hInorm
      norm_num at hInorm
    have hPprime : ∀ Q ∈ P, Prime Q := by
      intro Q hQ
      exact UniqueFactorizationMonoid.prime_of_normalized_factor Q
        (Multiset.mem_toFinset.mp (by simpa [P] using hQ))
    have hTnorm (T : Finset (Ideal (𝓞 K))) (hT : T ∈ P.powerset) :
        ((∏ Q ∈ T, Ideal.absNorm Q : ℕ) : ℝ) ≤ U ^ 2 := by
      have hTP : T ⊆ P := Finset.mem_powerset.mp hT
      have hTprodne : (∏ Q ∈ T, Q) ≠ (⊥ : Ideal (𝓞 K)) := by
        apply Finset.prod_ne_zero_iff.mpr
        intro Q hQ
        exact (hPprime Q (hTP hQ)).ne_zero
      have hTfac : UniqueFactorizationMonoid.normalizedFactors (∏ Q ∈ T, Q) = T.val := by
        simpa using UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
          (fun Q hQ => hPprime Q (hTP hQ))
      have hTdvd : (∏ Q ∈ T, Q) ∣ I := by
        apply (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
          hTprodne hI).mpr
        rw [hTfac]
        apply (Multiset.le_iff_subset T.nodup).mpr
        intro Q hQ
        exact Multiset.mem_toFinset.mp (hTP hQ)
      have hnormdvd : Ideal.absNorm (∏ Q ∈ T, Q) ∣ Ideal.absNorm I :=
        map_dvd Ideal.absNorm hTdvd
      have hnormIpos : 0 < Ideal.absNorm I := by
        apply Nat.pos_of_ne_zero
        intro hzero
        exact hI (Ideal.absNorm_eq_zero_iff.mp hzero)
      have hnormle : Ideal.absNorm (∏ Q ∈ T, Q) ≤ Ideal.absNorm I :=
        Nat.le_of_dvd hnormIpos hnormdvd
      have hnormprod : Ideal.absNorm (∏ Q ∈ T, Q) = ∏ Q ∈ T, Ideal.absNorm Q := by
        simp only [map_prod]
      calc
        ((∏ Q ∈ T, Ideal.absNorm Q : ℕ) : ℝ) =
            (Ideal.absNorm (∏ Q ∈ T, Q) : ℕ) := by rw [hnormprod]
        _ ≤ (Ideal.absNorm I : ℕ) := Nat.cast_le.mpr hnormle
        _ ≤ U ^ 2 := hIU
    unfold detectorCoeff
    change (∑ T ∈ P.powerset,
      if ((∏ Q ∈ T, Ideal.absNorm Q : ℕ) : ℝ) ≤ U ^ 2 then (-1) ^ T.card else 0) = 0
    calc
      _ = ∑ T ∈ P.powerset, (-1 : ℤ) ^ T.card := by
        apply Finset.sum_congr rfl
        intro T hT
        change (if ((∏ Q ∈ T, Ideal.absNorm Q : ℕ) : ℝ) ≤ U ^ 2 then
          (-1 : ℤ) ^ T.card else 0) = (-1 : ℤ) ^ T.card
        exact if_pos (hTnorm T hT)
      _ = 0 := Finset.sum_powerset_neg_one_pow_card_of_nonempty hPne

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
