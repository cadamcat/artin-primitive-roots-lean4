import Mathlib
import ArtinPrimitiveRoots.TypeII.Defs
import OAI.NumberTheory.PrimeGaps.Main

/-! External analytic inputs used by the Type II and construction arguments. -/

namespace ArtinPrimitiveRoots.Ext.TypeIIInputs

open Classical MeasureTheory
open scoped FourierTransform
open ArtinPrimitiveRoots.TypeII

/-- The Meissel–Mertens constant, defined as the limit of the reciprocal-prime sum error. -/
noncomputable def meisselMertensConstant : ℝ :=
  Filter.limUnder Filter.atTop (fun y : ℝ =>
    (∑ p ∈ primesUpTo y, 1 / (p : ℝ)) - Real.log (Real.log y))

/-- Prime-counting function on a real interval, with primes counted by an explicit finite set. -/
noncomputable def primeIntervalCount (y₁ y₂ : ℝ) : ℝ :=
  ((primesUpTo y₂).filter fun p => y₁ < (p : ℝ)).card

/-- `Li(y)` with lower endpoint `2`. -/
noncomputable def logarithmicIntegral (y : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..y, 1 / Real.log t

/-- Maximum prime progression error, in the `π` form used by §12. Binders typed `ℕ` on 2026-10-07: untyped,
Lean coerced the prime set into `ZMod q` before filtering (lane `c2b`). -/
noncomputable def primeProgressionError (y : ℝ) (q : ℕ) : ℝ :=
  ((Finset.range q).filter (fun v : ℕ => Nat.Coprime v q)).fold max 0 fun v : ℕ =>
    |(((primesUpTo y).filter (fun p : ℕ => ((p : ℕ) : ZMod q) = ((v : ℕ) : ZMod q))).card : ℝ) -
      logarithmicIntegral y / (Nat.totient q : ℝ)|

/-- `ext:bombieri-vinogradov`, 12-construction.tex:286-292 (`con:bv-input`); matching OAI
`bombieriVinogradov` (`PrimeGaps/Main.lean:158`), converted to the prime-counting form. -/
theorem bombieri_vinogradov :
    ∀ A η : ℝ, 0 < A → 0 < η →
      ∃ C y₀ : ℝ, 0 < C ∧ 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          (∑ q ∈ Finset.range (⌊Real.rpow y (1 / 2 - η)⌋₊ + 1),
            primeProgressionError y q) ≤ C * y * Real.rpow (Real.log y) (-A) := by
  sorry

lemma primeCharacterPrefix_eq_range {d : ℕ} (χ : DirichletCharacter ℂ d) (x : ℝ) :
    OAI.LargePrimeGaps.primeCharacterPrefix x χ =
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (χ (n : ZMod d) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
  classical
  let f : ℕ → ℂ := fun n =>
    (χ (n : ZMod d) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)
  have hzero : f 0 = 0 := by
    simp [f, ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
  have hrange : Finset.range (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ := by
    ext n
    simp
  have hioc : Finset.Ioc 0 ⌊x⌋₊ = (Finset.Icc 0 ⌊x⌋₊).erase 0 := by
    ext n
    simp
  have hremove :
      (∑ n ∈ (Finset.Icc 0 ⌊x⌋₊).erase 0, f n) =
        ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n := by
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro n hn hn'
    have hn0 : n = 0 := by
      by_contra hne
      exact hn' (Finset.mem_erase.mpr ⟨hne, hn⟩)
    subst n
    exact hzero
  change (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n) = _
  calc
    _ = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n := by rw [hioc, hremove]
    _ = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), f n := by rw [← hrange]

/-- `ext:siegel-walfisz`, PP `01-preliminaries.tex:24-40`, Proposition 2.1; matching OAI
`siegelWalfisz` (`PrimeGaps/Main.lean:142`). -/
theorem siegel_walfisz :
    ∀ A B : ℝ, 0 < A → 0 < B →
      ∃ C x₀ : ℝ, 0 < C ∧ 1 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.rpow (Real.log x) B →
            ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
              ‖(∑ n ∈ Finset.range (⌊x⌋₊ + 1),
                  (χ (n : ZMod d) : ℂ) *
                    (ArithmeticFunction.vonMangoldt n : ℂ)) -
                    (if χ = 1 then (x : ℂ) else 0)‖ ≤
                  C * x * Real.rpow (Real.log x) (-A) := by
  intro A B hA hB
  obtain ⟨M, hM, x₀, hx₀, hSW⟩ := OAI.LargePrimeGaps.siegelWalfisz A B hA hB
  refine ⟨M, x₀, hM, hx₀, ?_⟩
  intro x hx d hd hdlog χ hχ
  have h := hSW x hx d hd hdlog χ hχ
  rw [OAI.LargePrimeGaps.primeCharacterError, primeCharacterPrefix_eq_range] at h
  exact h

/-- `ext:mertens`, PD Lemma 2.1; 11-sieve.tex:159-164; 12-construction.tex:398-402. The
first assertion is the second Mertens theorem; the second is its product form. Matching PNT+
`mertens_second_theorem` (`RosserSchoenfeldPrime.lean:824-825`) and `E₃.bound''`
(`Mertens.lean:2419). -/
theorem mertens :
    (∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 < y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        |(∑ p ∈ primesUpTo y, 1 / (p : ℝ)) - Real.log (Real.log y) -
          meisselMertensConstant| ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 < y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        |roughSieveProduct y * Real.log y - Real.exp (-Real.eulerMascheroniConstant)| ≤ ε) := by
  sorry

/-- `ext:dirichlet-orthogonality`, 12-construction.tex:116-120; matching Mathlib
`DirichletCharacter.sum_char_inv_mul_char_eq` (`Orthogonality.lean:79`). -/
theorem dirichlet_orthogonality (M : ℕ) (hM : 0 < M)
    (u v : ZMod M) (hu : IsUnit u) :
    (if v = u then (1 : ℂ) else 0) =
      (1 / (Nat.totient M : ℂ)) *
        ∑ χ : DirichletCharacter ℂ M,
          star (χ u) * χ v := by
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  have hstar (χ : DirichletCharacter ℂ M) : star (χ u) = χ (u⁻¹) := by
    calc
      star (χ u) = (χ u)⁻¹ := by
        simpa using (Complex.inv_eq_conj (χ.unit_norm_eq_one hu.unit)).symm
      _ = χ (u⁻¹) := by
        have hmul : χ u * χ (u⁻¹) = 1 := by
          rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
        exact (eq_inv_of_mul_eq_one_right hmul).symm
  have hsum :
      (∑ χ : DirichletCharacter ℂ M, χ (u⁻¹) * χ v) =
        if u = v then (Nat.totient M : ℂ) else 0 := by
    simpa using DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) hu v
  rw [show (∑ χ : DirichletCharacter ℂ M, star (χ u) * χ v) =
      ∑ χ : DirichletCharacter ℂ M, χ (u⁻¹) * χ v from by
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [hstar]]
  rw [hsum]
  by_cases hv : v = u
  · subst v
    have htotient : (Nat.totient M : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.totient_pos.mpr hM))
    simp [htotient]
  · simp [hv, Ne.symm hv]

/-- The Mellin-Fourier transform of the logarithmic-coordinate test function used in §12. -/
noncomputable def logFourierTransform (Ψ : ℝ → ℝ) (v : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℝ) : ℂ) *
    ∫ s : ℝ, (Ψ (Real.exp s) : ℂ) * Complex.exp (-Complex.I * v * s)

/-- `ext:fourier-inversion`, 12-construction.tex:133-140; matching Mathlib
`Continuous.fourierInv_fourier_eq` (`Analysis/Fourier/Inversion.lean:174`). -/
theorem fourier_inversion (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hsupp : Function.support Ψ ⊆ Set.Ioo 1 2) :
    (∀ y : ℝ, 0 < y →
      (Ψ y : ℂ) = ∫ v : ℝ,
        logFourierTransform Ψ v * Complex.exp (Complex.I * v * Real.log y)) ∧
    (∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ v : ℝ, ‖logFourierTransform Ψ v‖ ≤
        C * Real.rpow (1 + |v|) (-(N : ℝ))) := by
  classical
  let ψlog : ℝ → ℂ := fun s => (Ψ (Real.exp s) : ℂ)
  have hψreal : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => Ψ (Real.exp s)) :=
    hΨ.comp Real.contDiff_exp
  have hψsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψlog := by
    dsimp [ψlog]
    exact Complex.ofRealCLM.contDiff.comp hψreal
  have hψsupport : Function.support ψlog ⊆ Set.Icc 0 (Real.log 2) := by
    intro s hs
    have hs' : ψlog s ≠ 0 := by simpa only [Function.mem_support] using hs
    have hne : Ψ (Real.exp s) ≠ 0 := by
      intro hz
      apply hs'
      simp [ψlog, hz]
    have hmem : Real.exp s ∈ Function.support Ψ := by
      simpa only [Function.mem_support] using hne
    rcases hsupp hmem with ⟨hlo, hhi⟩
    constructor
    · have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 1) hlo
      exact le_of_lt (by simpa using h)
    · have h := Real.log_lt_log (Real.exp_pos s) hhi
      exact le_of_lt (by simpa using h)
  have hψcompact : HasCompactSupport ψlog :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hψsupport
  let F : SchwartzMap ℝ ℂ := hψcompact.toSchwartzMap hψsmooth
  have hFcoe : (F : ℝ → ℂ) = ψlog := rfl
  have hFT (v : ℝ) :
      logFourierTransform Ψ v =
        (1 / (2 * Real.pi : ℝ) : ℂ) * 𝓕 (F : ℝ → ℂ) (v / (2 * Real.pi)) := by
    unfold logFourierTransform
    rw [Real.fourier_eq']
    congr 1
    apply integral_congr_ae
    filter_upwards [] with s
    rw [hFcoe, Real.inner_apply]
    simp only [smul_eq_mul]
    have harg :
        (↑(-2 * Real.pi * (s * (v / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I =
          -Complex.I * (v : ℂ) * s := by
      push_cast
      field_simp [Real.pi_ne_zero]
    rw [harg]
    ring
  constructor
  · intro y hy
    let x := Real.log y
    let H : ℝ → ℂ := fun v => logFourierTransform Ψ v * Complex.exp (Complex.I * v * x)
    have hπ : 0 < 2 * Real.pi := by positivity
    have hchange : (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) • ∫ w : ℝ, H ((2 * Real.pi) * w) := by
      have h := Measure.integral_comp_mul_left H (2 * Real.pi)
      rw [abs_of_pos (inv_pos.mpr hπ)] at h
      calc
        (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) •
            ((2 * Real.pi : ℝ)⁻¹ • ∫ v : ℝ, H v) := by
              rw [smul_smul, mul_inv_cancel₀ hπ.ne', one_smul]
        _ = (2 * Real.pi : ℝ) • ∫ w : ℝ, H ((2 * Real.pi) * w) := by rw [h.symm]
    have hscaled (w : ℝ) :
        (2 * Real.pi : ℝ) • H ((2 * Real.pi) * w) =
          Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) *
            𝓕 (F : ℝ → ℂ) w := by
      dsimp [H]
      rw [hFT]
      have hfreq : (2 * Real.pi * w) / (2 * Real.pi) = w := by
        field_simp [Real.pi_ne_zero]
      rw [hfreq]
      have hexpArg :
          Complex.I * (↑(2 * Real.pi * w : ℝ) : ℂ) * (x : ℂ) =
            (↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      have hexp : Complex.exp (Complex.I * (↑(2 * Real.pi * w : ℝ) : ℂ) * (x : ℂ)) =
          Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) :=
        congrArg Complex.exp hexpArg
      rw [hexp]
      have hcoef :
          ((2 * Real.pi : ℝ) : ℂ) * (1 / (2 * Real.pi : ℝ) : ℂ) = 1 := by
        push_cast
        field_simp [Real.pi_ne_zero]
      calc
        ((2 * Real.pi : ℝ) : ℂ) *
            (((1 / (2 * Real.pi : ℝ) : ℂ) * 𝓕 (F : ℝ → ℂ) w) *
              Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I)) =
          (((2 * Real.pi : ℝ) : ℂ) * (1 / (2 * Real.pi : ℝ) : ℂ)) *
            𝓕 (F : ℝ → ℂ) w *
              Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) := by ring
        _ = _ := by rw [hcoef]; ring
    have hInvSch : 𝓕⁻ (𝓕 F) = F := by
      ext z
      rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe]
      exact congrFun (F.continuous.fourierInv_fourier_eq F.integrable (𝓕 F).integrable) z
    have hInv : 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x = F x := by
      have h := congrArg (fun G : SchwartzMap ℝ ℂ => (G : ℝ → ℂ)) hInvSch
      simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using congrFun h x
    have hInvIntegral :
        𝓕⁻ (𝓕 (F : ℝ → ℂ)) x =
          ∫ w : ℝ, Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) *
            𝓕 (F : ℝ → ℂ) w := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with w
      rw [Real.inner_apply]
      simp only [smul_eq_mul]
    have hInvToIntegral : (∫ v : ℝ, H v) = 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x := by
      calc
        (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) • ∫ w : ℝ, H ((2 * Real.pi) * w) := hchange
        _ = ∫ w : ℝ, (2 * Real.pi : ℝ) • H ((2 * Real.pi) * w) := by rw [← integral_smul]
        _ = ∫ w : ℝ,
              Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) *
                𝓕 (F : ℝ → ℂ) w := by
          apply integral_congr_ae
          filter_upwards [] with w
          exact hscaled w
        _ = 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x := hInvIntegral.symm
    calc
      (Ψ y : ℂ) = ψlog x := by simp [ψlog, x, Real.exp_log hy]
      _ = F x := rfl
      _ = 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x := hInv.symm
      _ = ∫ v : ℝ, H v := hInvToIntegral.symm
      _ = ∫ v : ℝ,
            logFourierTransform Ψ v * Complex.exp (Complex.I * v * Real.log y) := by
          simp [H, x]
  · intro N
    obtain ⟨C0, hC0, hC0bound⟩ := (𝓕 F).decay 0 0
    obtain ⟨CN, hCN, hCNbound⟩ := (𝓕 F).decay N 0
    have hsmallBound (w : ℝ) : ‖(𝓕 F) w‖ ≤ C0 := by
      have h := hC0bound w
      simpa using h
    have hpowerBound (w : ℝ) : |w| ^ N * ‖(𝓕 F) w‖ ≤ CN := by
      have h := hCNbound w
      simpa [Real.norm_eq_abs] using h
    let Cw : ℝ := 2 ^ N * max C0 CN
    have hCw : 0 < Cw := by positivity
    have hrapid (w : ℝ) :
        ‖(𝓕 F) w‖ * (1 + |w|) ^ N ≤ Cw := by
      by_cases hw : |w| ≤ 1
      · have hbase : 1 + |w| ≤ 2 := by linarith
        have hpow : (1 + |w|) ^ N ≤ (2 : ℝ) ^ N :=
          pow_le_pow_left₀ (by positivity) hbase N
        calc
          ‖(𝓕 F) w‖ * (1 + |w|) ^ N ≤ C0 * (1 + |w|) ^ N :=
            mul_le_mul_of_nonneg_right (hsmallBound w) (by positivity)
          _ ≤ C0 * (2 : ℝ) ^ N := mul_le_mul_of_nonneg_left hpow (by positivity)
          _ ≤ Cw := by
            dsimp [Cw]
            calc
              C0 * (2 : ℝ) ^ N = (2 : ℝ) ^ N * C0 := by ring
              _ ≤ (2 : ℝ) ^ N * max C0 CN :=
                mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      · have hw' : 1 ≤ |w| := le_of_not_ge hw
        have hbase : 1 + |w| ≤ 2 * |w| := by linarith
        have hpow : (1 + |w|) ^ N ≤ (2 * |w|) ^ N :=
          pow_le_pow_left₀ (by positivity) hbase N
        calc
          ‖(𝓕 F) w‖ * (1 + |w|) ^ N ≤ ‖(𝓕 F) w‖ * (2 * |w|) ^ N :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
          _ = (2 : ℝ) ^ N * (|w| ^ N * ‖(𝓕 F) w‖) := by rw [mul_pow]; ring
          _ ≤ (2 : ℝ) ^ N * CN :=
            mul_le_mul_of_nonneg_left (hpowerBound w) (by positivity)
          _ ≤ Cw := by
            dsimp [Cw]
            exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    let Cbase : ℝ := Cw
    have hCbasePos : 0 < Cbase := hCw
    have hCbase (w : ℝ) : ‖(𝓕 F) w‖ * (1 + |w|) ^ N ≤ Cbase := hrapid w
    let Cfinal : ℝ := (1 / (2 * Real.pi)) * Cbase * (1 + 2 * Real.pi) ^ N
    have hCfinal : 0 < Cfinal := by positivity
    refine ⟨Cfinal, hCfinal, fun v => ?_⟩
    let ξ := v / (2 * Real.pi)
    have hπ : 0 < 2 * Real.pi := by positivity
    have hv : v = (2 * Real.pi) * ξ := by
      dsimp [ξ]
      field_simp [Real.pi_ne_zero]
    have hbase : 1 + |v| ≤ (1 + 2 * Real.pi) * (1 + |ξ|) := by
      rw [hv, abs_mul, abs_of_pos hπ]
      nlinarith [abs_nonneg ξ, Real.pi_pos]
    have hpow : (1 + |v|) ^ N ≤
        (1 + 2 * Real.pi) ^ N * (1 + |ξ|) ^ N := by
      calc
        (1 + |v|) ^ N ≤ ((1 + 2 * Real.pi) * (1 + |ξ|)) ^ N :=
          pow_le_pow_left₀ (by positivity) hbase N
        _ = _ := by rw [mul_pow]
    have hFdecay := hCbase ξ
    have hFscaled : ‖(𝓕 F) ξ‖ * (1 + |v|) ^ N ≤
        Cbase * (1 + 2 * Real.pi) ^ N := by
      calc
        _ ≤ ‖(𝓕 F) ξ‖ * ((1 + 2 * Real.pi) ^ N * (1 + |ξ|) ^ N) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = (‖(𝓕 F) ξ‖ * (1 + |ξ|) ^ N) * (1 + 2 * Real.pi) ^ N := by ring
        _ ≤ Cbase * (1 + 2 * Real.pi) ^ N :=
          mul_le_mul_of_nonneg_right hFdecay (by positivity)
    have hcoef : ‖(1 / (2 * Real.pi : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
    have hlog : ‖logFourierTransform Ψ v‖ * (1 + |v|) ^ N ≤ Cfinal := by
      rw [hFT, norm_mul, hcoef]
      calc
        (1 / (2 * Real.pi)) * ‖𝓕 (F : ℝ → ℂ) ξ‖ * (1 + |v|) ^ N =
            (1 / (2 * Real.pi)) * (‖𝓕 (F : ℝ → ℂ) ξ‖ * (1 + |v|) ^ N) := by ring
        _ ≤
          (1 / (2 * Real.pi)) * (Cbase * (1 + 2 * Real.pi) ^ N) :=
            mul_le_mul_of_nonneg_left hFscaled (by positivity)
        _ = Cfinal := by dsimp [Cfinal]; ring
    have hdiv : ‖logFourierTransform Ψ v‖ ≤ Cfinal / (1 + |v|) ^ N :=
      (le_div_iff₀ (by positivity)).2 hlog
    have hrpow : Real.rpow (1 + |v|) (-(N : ℝ)) = ((1 + |v|) ^ N)⁻¹ := by
      change (1 + |v|) ^ (-(N : ℝ)) = ((1 + |v|) ^ N)⁻¹
      calc
        (1 + |v|) ^ (-(N : ℝ)) = ((1 + |v|) ^ (N : ℝ))⁻¹ :=
          Real.rpow_neg (show 0 ≤ 1 + |v| by positivity) (N : ℝ)
        _ = _ := by rw [Real.rpow_natCast]
    simpa [hrpow, div_eq_mul_inv] using hdiv

/-! The following discrete derivative estimate is adapted from
OAI/NumberTheory/EgyptianFractions/DiscreteFirstDerivative.lean (Apache-2.0). Its prebuilt module
is unavailable in the shared checkout, so the small collection of required lemmas is proved here. -/
namespace DerivativeTestProof

open scoped BigOperators

noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

noncomputable def phaseWeight (x : ℝ) : ℂ :=
  -(1 : ℂ) / 2 - (Real.cot (Real.pi * x) : ℂ) * Complex.I / 2

lemma phase_eq_additiveCharacter (x : ℝ) :
    phase x = ArtinPrimitiveRoots.TypeII.additiveCharacter x := by
  unfold phase ArtinPrimitiveRoots.TypeII.additiveCharacter
  congr 1
  push_cast
  ring

lemma phase_norm (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cot_antitone_unit {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    Real.cot (Real.pi * y) ≤ Real.cot (Real.pi * x) := by
  have hpi := Real.pi_pos
  have hxpi : 0 < Real.pi * x := mul_pos hpi hx
  have hypi : 0 < Real.pi * y := by nlinarith
  have hxpi' : Real.pi * x < Real.pi := by nlinarith
  have hypi' : Real.pi * y < Real.pi := by nlinarith
  have hsx := Real.sin_pos_of_pos_of_lt_pi hxpi hxpi'
  have hsy := Real.sin_pos_of_pos_of_lt_pi hypi hypi'
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  apply (div_le_div_iff₀ hsy hsx).2
  have hs : 0 ≤ Real.sin (Real.pi * y - Real.pi * x) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> nlinarith
  rw [Real.sin_sub] at hs
  nlinarith

lemma sin_pi_lower {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    2 * β ≤ Real.sin (Real.pi * x) := by
  have hp := Real.pi_pos
  by_cases hx : x ≤ 1 / 2
  · have h := Real.mul_le_sin (x := Real.pi * x) (by nlinarith) (by nlinarith)
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at h
    linarith
  · have h := Real.mul_le_sin (x := Real.pi * (1 - x)) (by nlinarith) (by nlinarith)
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq] at h
    have harg : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
    rw [harg, Real.sin_pi_sub] at h
    linarith

lemma abs_cot_pi_le {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    |Real.cot (Real.pi * x)| ≤ 1 / (2 * β) := by
  have hs := sin_pi_lower hβ hlo hhi
  have hsp : 0 < Real.sin (Real.pi * x) := by linarith
  rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsp]
  exact (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hsp.le).trans
    (one_div_le_one_div_of_le (by positivity) hs)

lemma phaseWeight_identity {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    (phase x - 1) * phaseWeight x = 1 := by
  have hs : Real.sin (Real.pi * x) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos]))
  unfold phase phaseWeight
  rw [Complex.exp_ofReal_mul_I]
  rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
  rw [Real.sin_two_mul, Real.cos_two_mul, Real.cot_eq_cos_div_sin]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_div]
  have hsc : (Real.sin (Real.pi * x) : ℂ) ^ 2 +
      (Real.cos (Real.pi * x) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (Real.pi * x)
  have hsC : (Real.sin (Real.pi * x) : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp
  ring_nf
  norm_num only [Complex.ofReal_one, Complex.I_sq]
  linear_combination -2 * (Real.cos (Real.pi * x) : ℂ) * Complex.I * hsc

lemma phaseWeight_norm_le {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    ‖phaseWeight x‖ ≤ 1 / 2 + 1 / (4 * β) := by
  have hc := abs_cot_pi_le hβ hlo hhi
  have hn2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  calc
    ‖phaseWeight x‖ ≤ ‖-(1 : ℂ) / 2‖ + ‖(Real.cot (Real.pi * x) : ℂ) * Complex.I / 2‖ :=
      norm_sub_le _ _
    _ = 1 / 2 + |Real.cot (Real.pi * x)| / 2 := by
      simp only [norm_div, norm_neg, norm_one, norm_mul, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, hn2, mul_one]
    _ ≤ 1 / 2 + (1 / (2 * β)) / 2 := by gcongr
    _ = 1 / 2 + 1 / (4 * β) := by ring

lemma phaseWeight_difference_norm {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    ‖phaseWeight x - phaseWeight y‖ =
      (Real.cot (Real.pi * x) - Real.cot (Real.pi * y)) / 2 := by
  have hc := cot_antitone_unit hx hxy hy
  have heq : phaseWeight x - phaseWeight y =
      (((Real.cot (Real.pi * x) - Real.cot (Real.pi * y)) / 2 : ℝ) : ℂ) * (-Complex.I) := by
    unfold phaseWeight
    push_cast
    ring
  rw [heq, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]

lemma phase_step_weight (f : ℕ → ℝ) (i : ℕ)
    (hlo : 0 < f (i + 1) - f i) (hhi : f (i + 1) - f i < 1) :
    (phase (f (i + 1)) - phase (f i)) * phaseWeight (f (i + 1) - f i) = phase (f i) := by
  have heq : phase (f (i + 1)) = phase (f i) * phase (f (i + 1) - f i) := by
    rw [← phase_add]
    congr 1
    ring
  rw [heq]
  calc
    (phase (f i) * phase (f (i + 1) - f i) - phase (f i)) *
        phaseWeight (f (i + 1) - f i) =
      phase (f i) * ((phase (f (i + 1) - f i) - 1) *
        phaseWeight (f (i + 1) - f i)) := by ring
    _ = phase (f i) := by rw [phaseWeight_identity hlo hhi, mul_one]

lemma weighted_telescope (z w : ℕ → ℂ) (N : ℕ)
    (hstep : ∀ i < N, (z (i + 1) - z i) * w i = z i) :
    (∑ i ∈ Finset.range N, z i) = z N * w N - z 0 * w 0 +
      ∑ i ∈ Finset.range N, z (i + 1) * (w i - w (i + 1)) := by
  calc
    (∑ i ∈ Finset.range N, z i) =
        ∑ i ∈ Finset.range N,
          ((z (i + 1) * w (i + 1) - z i * w i) + z (i + 1) * (w i - w (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hstep i (Finset.mem_range.mp hi)
      linear_combination -h
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun i => z i * w i)]

theorem first_derivative_sum_bound_core (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hlo : ∀ i ≤ N, β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range N, phase (f i)‖ ≤ 2 / β := by
  let d : ℕ → ℝ := fun i => f (i + 1) - f i
  let w : ℕ → ℂ := fun i => phaseWeight (d i)
  have hdlo : ∀ i ≤ N, 0 < d i := fun i hi => lt_of_lt_of_le hβ (hlo i hi)
  have hdhi : ∀ i ≤ N, d i < 1 := by
    intro i hi
    have := hhi i hi
    dsimp [d]
    linarith
  have htel := weighted_telescope (fun i => phase (f i)) w N (by
    intro i hi
    exact phase_step_weight f i (hdlo i hi.le) (hdhi i hi.le))
  have hvariation : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
      (Real.cot (Real.pi * d 0) - Real.cot (Real.pi * d N)) / 2 := by
    calc
      (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
          ∑ i ∈ Finset.range N,
            (Real.cot (Real.pi * d i) - Real.cot (Real.pi * d (i + 1))) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i < N := Finset.mem_range.mp hi
        exact phaseWeight_difference_norm (hdlo i hiN.le)
          (hmono (show i ≤ N from hiN.le) (show i + 1 ≤ N by omega) (by omega))
          (hdhi (i + 1) (by omega))
      _ = _ := by rw [← Finset.sum_div, Finset.sum_range_sub']
  have hc0 := abs_cot_pi_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hcN := abs_cot_pi_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hvbound : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) ≤ 1 / (2 * β) := by
    rw [hvariation]
    have h0 := (abs_le.mp hc0).2
    have hN := (abs_le.mp hcN).1
    change Real.cot (Real.pi * d 0) ≤ _ at h0
    change _ ≤ Real.cot (Real.pi * d N) at hN
    linarith
  have hw0 := phaseWeight_norm_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hwN := phaseWeight_norm_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hsum : ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ ≤
      ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range N, ‖phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, phase_norm, one_mul]
  have hβle : β ≤ 1 := by
    have := hlo 0 (Nat.zero_le N)
    have := hhi 0 (Nat.zero_le N)
    linarith
  have hinv : 1 ≤ 1 / β := (le_div_iff₀ hβ).2 (by simpa using hβle)
  rw [htel]
  calc
    _ ≤ ‖phase (f N) * w N - phase (f 0) * w 0‖ +
        ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_add_le _ _
    _ ≤ (‖phase (f N) * w N‖ + ‖phase (f 0) * w 0‖) +
        ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := add_le_add (norm_sub_le _ _) hsum
    _ = (‖w N‖ + ‖w 0‖) + ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
      simp only [norm_mul, phase_norm, one_mul]
    _ ≤ (1 / 2 + 1 / (4 * β)) + (1 / 2 + 1 / (4 * β)) + 1 / (2 * β) :=
      add_le_add (add_le_add hwN hw0) hvbound
    _ = 1 + 1 / β := by ring
    _ ≤ 1 / β + 1 / β := by simpa [add_comm] using add_le_add_right hinv (1 / β)
    _ = 2 / β := by ring

end DerivativeTestProof

/-- `ext:derivative-test` — PP `01-preliminaries.tex:88-106`, Proposition 2.3; matching OAI
`first_derivative_sum_bound` (`DiscreteFirstDerivative.lean:147-151`). -/
theorem derivative_test (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hlo : ∀ i < N, β ≤ f (i + 1) - f i)
    (hhi : ∀ i < N, f (i + 1) - f i ≤ 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Icc 0 N)) :
    ‖∑ i ∈ Finset.range N, additiveCharacter (f i)‖ ≤ 2 / β := by
  by_cases hN : N = 0
  · subst N
    simp
    positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let g : ℕ → ℝ := Function.update f (N + 1) (f N + (f N - f (N - 1)))
  have hg_le (i : ℕ) (hi : i ≤ N) : g i = f i := by
    have hne : i ≠ N + 1 := by omega
    simp [g, hne]
  have hg_step (i : ℕ) (hi : i < N) : g (i + 1) - g i = f (i + 1) - f i := by
    rw [hg_le (i + 1) (Nat.succ_le_of_lt hi), hg_le i hi.le]
  have hg_last : g (N + 1) - g N = f N - f (N - 1) := by
    have hnew : g (N + 1) = f N + (f N - f (N - 1)) := by simp [g]
    rw [hnew, hg_le N le_rfl]
    ring
  have hmonoBase : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N) := by
    intro i hi j hj hij
    apply hmono <;> simp_all
  have hlo' : ∀ i ≤ N, β ≤ g (i + 1) - g i := by
    intro i hi
    by_cases hil : i < N
    · rw [hg_step i hil]
      exact hlo i hil
    · have hiN : i = N := by omega
      subst i
      rw [hg_last]
      have hprev : N - 1 < N := by omega
      have h := hlo (N - 1) hprev
      have heq : N - 1 + 1 = N := by omega
      simpa [heq] using h
  have hhi' : ∀ i ≤ N, g (i + 1) - g i ≤ 1 - β := by
    intro i hi
    by_cases hil : i < N
    · rw [hg_step i hil]
      exact hhi i hil
    · have hiN : i = N := by omega
      subst i
      rw [hg_last]
      have hprev : N - 1 < N := by omega
      have h := hhi (N - 1) hprev
      have heq : N - 1 + 1 = N := by omega
      simpa [heq] using h
  have hmono' : MonotoneOn (fun i => g (i + 1) - g i) (Set.Iic N) := by
    intro i hi j hj hij
    have hiN : i ≤ N := by simpa using hi
    have hjN : j ≤ N := by simpa using hj
    by_cases hjlt : j < N
    · have hilt : i < N := lt_of_le_of_lt hij hjlt
      change g (i + 1) - g i ≤ g (j + 1) - g j
      rw [hg_step i hilt, hg_step j hjlt]
      exact hmonoBase hi hj hij
    · have hjEq : j = N := by omega
      subst j
      by_cases hilt : i < N
      · change g (i + 1) - g i ≤ g (N + 1) - g N
        rw [hg_step i hilt, hg_last]
        have hprev : N - 1 < N := by omega
        have hcmp : i ≤ N - 1 := Nat.le_sub_one_of_lt hilt
        have h := hmonoBase (show i ∈ Set.Iic N from hi)
          (show N - 1 ∈ Set.Iic N by exact Nat.sub_le N 1) hcmp
        have heq : N - 1 + 1 = N := by omega
        simpa [heq] using h
      · have hiEq : i = N := by omega
        subst i
        rfl
  have hsum :
      (∑ i ∈ Finset.range N, DerivativeTestProof.phase (g i)) =
        ∑ i ∈ Finset.range N, additiveCharacter (f i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hil : i < N := Finset.mem_range.mp hi
    rw [hg_le i hil.le, DerivativeTestProof.phase_eq_additiveCharacter]
  rw [← hsum]
  exact DerivativeTestProof.first_derivative_sum_bound_core g N β hβ hlo' hhi' hmono'

/-- `ext:pnt` — PD Lemma 2.1 and 11-sieve.tex:223-226; matching PNT+ `pi_asymp`
(`Consequences.lean:786`). -/
theorem pnt :
    ∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 ≤ y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        |primeIntervalCount y (2 * y) - y / Real.log y| ≤ ε * y / Real.log y := by
  sorry

/-- `ext:dirichlet-L` — PP `02-long-prime.tex:312-323`; matching Mathlib
`DirichletCharacter.LFunction` and `differentiable_LFunction` (`DirichletContinuation.lean:98`).
Correction 9 from review lane `rev-b` records meromorphic continuation for all characters. -/
theorem dirichlet_L (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∀ s : ℂ, 1 < s.re →
      DirichletCharacter.LFunction χ s = LSeries (χ ·) s) ∧
    (∀ s : ℂ, MeromorphicAt (DirichletCharacter.LFunction χ) s) ∧
    (χ ≠ 1 → Differentiable ℂ (DirichletCharacter.LFunction χ)) := by
  sorry

private theorem ncard_zero_le_divisor (g : ℂ → ℂ) (c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hR : r < R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R)) (hgc : g c ≠ 0) :
    Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} ≤
      ∑ᶠ z, (MeromorphicOn.divisor g (Metric.closedBall c r) z : ℝ) := by
  classical
  let S : Set ℂ := {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0}
  let D := MeromorphicOn.divisor g (Metric.closedBall c r)
  have hsmall : AnalyticOnNhd ℂ g (Metric.closedBall c r) :=
    hg.mono (Metric.closedBall_subset_closedBall hR.le)
  have hcenter : analyticOrderAt g c = 0 :=
    (hsmall c (by simpa using hr.le)).analyticOrderAt_eq_zero.mpr hgc
  have hcenterNeTop : analyticOrderAt g c ≠ ⊤ := by simp [hcenter]
  have hDpos (z : ℂ) (hz : z ∈ S) : (1 : ℤ) ≤ D z := by
    have hzsmall : z ∈ Metric.closedBall c r := hz.1
    have horderNe0 : analyticOrderAt g z ≠ 0 :=
      (hsmall z hzsmall).analyticOrderAt_ne_zero.mpr hz.2
    have hpre : IsPreconnected (Metric.closedBall c r) := by
      simpa [abs_of_pos hr] using (convex_closedBall c |r|).isPreconnected
    have horderNeTop : analyticOrderAt g z ≠ ⊤ :=
      hsmall.analyticOrderAt_ne_top_of_isPreconnected
        hpre (by simpa using hr.le) hzsmall hcenterNeTop
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp horderNeTop
    have hkpos : 1 ≤ k := by
      have horderPos : (1 : ℕ∞) ≤ analyticOrderAt g z :=
        Order.one_le_iff_ne_zero.mpr horderNe0
      have hkpos' : (1 : ℕ∞) ≤ (k : ℕ∞) := by
        calc
          (1 : ℕ∞) ≤ analyticOrderAt g z := horderPos
          _ = (k : ℕ∞) := hk.symm
      exact_mod_cast hkpos'
    rw [hsmall.meromorphicOn.divisor_apply hzsmall,
      (hsmall z hzsmall).meromorphicOrderAt_eq]
    have hkz : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hkpos
    have hmap : (1 : WithTop ℤ) ≤
        (analyticOrderAt g z).map (fun n : ℕ => (n : ℤ)) := by
      rw [← hk]
      simp only [ENat.map_natCast]
      exact WithTop.coe_le_coe.mpr hkz
    have hmapNeTop : (analyticOrderAt g z).map (fun n : ℕ => (n : ℤ)) ≠ ⊤ := by
      rw [← hk]
      simp only [ENat.map_natCast]
      simp
    exact WithTop.untop₀_le_untop₀ hmapNeTop hmap
  have hSsub : S ⊆ D.support := by
    intro z hz
    rw [Function.mem_support]
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1) (hDpos z hz))
  have hcompact : IsCompact (Metric.closedBall c r) := by
    simpa [abs_of_pos hr] using isCompact_closedBall c |r|
  have hDfinite := D.finiteSupport hcompact
  have hSfinite : S.Finite := hDfinite.subset hSsub
  have hSsum :
      (hSfinite.toFinset.card : ℝ) ≤
        ∑ z ∈ hSfinite.toFinset, (D z : ℝ) := by
    have h := Finset.card_nsmul_le_sum hSfinite.toFinset (fun z => (D z : ℝ))
      (1 : ℝ) (by
        intro z hz
        exact_mod_cast hDpos z ((Set.Finite.mem_toFinset hSfinite).1 hz))
    simpa using h
  have hSub : hSfinite.toFinset ⊆ hDfinite.toFinset := by
    intro z hz
    exact (Set.Finite.mem_toFinset hDfinite).2
      (hSsub ((Set.Finite.mem_toFinset hSfinite).1 hz))
  have hcastSupport : Function.support (fun z : ℂ => (D z : ℝ)) ⊆ hDfinite.toFinset := by
    intro z hz
    have hzcast : (D z : ℝ) ≠ 0 := by
      simpa only [Function.mem_support] using hz
    have hzD : D z ≠ 0 := by
      intro hzero
      apply hzcast
      simp [hzero]
    exact (Set.Finite.mem_toFinset hDfinite).2 hzD
  have hDnonneg (z : ℂ) : (0 : ℝ) ≤ (D z : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hsmall z
  calc
    (Set.ncard S : ℝ) = (hSfinite.toFinset.card : ℝ) := by
      exact_mod_cast Set.ncard_eq_toFinset_card S hSfinite
    _ ≤ ∑ z ∈ hSfinite.toFinset, (D z : ℝ) := hSsum
    _ ≤ ∑ z ∈ hDfinite.toFinset, (D z : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSub (fun z hz _ => hDnonneg z)
    _ = ∑ᶠ z, (D z : ℝ) := (finsum_eq_sum_of_support_subset _ hcastSupport).symm

/-- `ext:jensen` — PP `02-long-prime.tex:392-394`; matching Mathlib
`AnalyticOnNhd.sum_divisor_le` (`JensenFormula.lean:389-392`). -/
theorem jensen (f : ℂ → ℂ) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (hfc : f c ≠ 0) :
    Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ f z = 0} ≤
      (Real.log (⨆ z ∈ Metric.closedBall c R, ‖f z‖) - Real.log ‖f c‖) /
        Real.log (R / r) := by
  classical
  have hRpos : 0 < R := hr.trans hR
  have hboundSet : BddAbove
      (⋃ z : ℂ, Set.range (fun _ : z ∈ Metric.closedBall c R => ‖f z‖)) := by
    have hset : (⋃ z : ℂ, Set.range (fun _ : z ∈ Metric.closedBall c R => ‖f z‖)) =
        (fun z => ‖f z‖) '' Metric.closedBall c R := by
      ext x
      simp [Set.mem_iUnion, Set.mem_range, Set.mem_image, eq_comm]
    rw [hset]
    have hcompactR : IsCompact (Metric.closedBall c R) := by
      simpa [abs_of_pos hRpos] using isCompact_closedBall c |R|
    exact hcompactR.bddAbove_image hf.continuousOn.norm
  let Smax : ℝ := ⨆ z ∈ Metric.closedBall c R, ‖f z‖
  have hSmaxFc : ‖f c‖ ≤ Smax := by
    have hcball : c ∈ Metric.closedBall c R := by simpa using hRpos.le
    exact le_ciSup₂ hboundSet c hcball
  have hnormFc : 0 < ‖f c‖ := norm_pos_iff.mpr hfc
  have hSmaxPos : 0 < Smax := lt_of_lt_of_le hnormFc hSmaxFc
  let M : ℝ := Smax / ‖f c‖
  have hM : 1 ≤ M := (le_div_iff₀ hnormFc).2 (by simpa using hSmaxFc)
  let g : ℂ → ℂ := fun z => f z / f c
  have hg : AnalyticOnNhd ℂ g (Metric.closedBall c R) := by
    exact hf.div_const
  have hgc : g c = 1 := by
    simp [g, hfc]
  have hgc0 : g c ≠ 0 := by rw [hgc]; norm_num
  have hgBound : ∀ z ∈ Metric.sphere c R, ‖g z‖ ≤ M := by
    intro z hz
    have hzle : ‖f z‖ ≤ Smax := le_ciSup₂ hboundSet z (Metric.sphere_subset_closedBall hz)
    dsimp [g, M, Smax]
    rw [norm_div]
    exact div_le_div_of_nonneg_right hzle (norm_nonneg _)
  have hgAbs : AnalyticOnNhd ℂ g (Metric.closedBall c |R|) := by
    simpa [abs_of_pos hRpos] using hg
  have hgBoundAbs : ∀ z ∈ Metric.sphere c |R|, ‖g z‖ ≤ M := by
    simpa [abs_of_pos hRpos] using hgBound
  have hJensen := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (M := M) (f := g)
    (by simpa [abs_of_pos hr] using hr)
    (by simpa [abs_of_pos hr, abs_of_pos hRpos] using hR)
    hM hgAbs hgc0 hgBoundAbs
  have hzeroSet :
      {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} =
        {z : ℂ | z ∈ Metric.closedBall c r ∧ f z = 0} := by
    ext z
    simp [g, hfc]
  rw [← hzeroSet]
  have hcountFinal :
      Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} ≤
        Real.log (M / ‖g c‖) / Real.log (R / r) := by
    have hcount := ncard_zero_le_divisor g c r R hr hR hg hgc0
    have hcount' :
        Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} ≤
          ∑ᶠ z, (MeromorphicOn.divisor g (Metric.closedBall c |r|) z : ℝ) := by
      calc
        Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} ≤
            ∑ᶠ z, (MeromorphicOn.divisor g (Metric.closedBall c r) z : ℝ) := hcount
        _ = ∑ᶠ z, (MeromorphicOn.divisor g (Metric.closedBall c |r|) z : ℝ) := by
          apply finsum_congr
          intro z
          rw [abs_of_pos hr]
    let D' := MeromorphicOn.divisor g (Metric.closedBall c |r|)
    have hDfinite' := D'.finiteSupport (isCompact_closedBall c |r|)
    have hcount'' :
        (Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} : ℝ) ≤
          (∑ᶠ z, D' z : ℤ) := by
      calc
        _ ≤ ∑ᶠ z, (D' z : ℝ) := hcount'
        _ = (∑ᶠ z, D' z : ℤ) := (map_finsum (Int.castRingHom ℝ) hDfinite').symm
    exact hcount''.trans hJensen
  calc
    Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} ≤
        Real.log (M / ‖g c‖) / Real.log (R / r) := hcountFinal
    _ = (Real.log Smax - Real.log ‖f c‖) / Real.log (R / r) := by
      rw [hgc, norm_one, div_one]
      dsimp [M]
      rw [Real.log_div hSmaxPos.ne' hnormFc.ne']

end ArtinPrimitiveRoots.Ext.TypeIIInputs
