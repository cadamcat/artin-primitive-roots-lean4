import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».Defs
import ArtinPrimitiveRoots.Ext.SplittingInputs
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# A2-QS-POISSON, part P0: smooth cutoffs and the transform `T`

Guide: `runs/lanes/sol-thin-found/PROOFS.md:331-347`.  Hints: smooth bump functions
(`ContDiffBump`, `Real.smoothTransition`); Mellin inversion `mellin_inversion`
(`M/Analysis/MellinInversion.lean`), vertical decay of `Mellin(h)` by repeated integration by
parts in `log x`; Stirling-type bounds for `Gammaℂ` on vertical strips (`|Γ_ℂ(u)/Γ_ℂ(1-u)|` grows
like `|Im u|^{2 Re u - 1}`).  The pole of `Mellin(h)(1-u)` at `u = 1` (from `h(0) ≠ 0`) is
cancelled by the zero of `1/Γ_ℂ(1-u)^{r₂}` (`r₂ ≥ 1` for a totally complex field).
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate FourierTransform RealInnerProductSpace Topology
open NumberField IsDedekindDomain
open MeasureTheory
open Filter

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

private def qsLogMellinWeight (h : ℝ → ℂ) (σ : ℝ) : ℝ → ℂ :=
  fun v => Real.exp (-σ * v) • h (Real.exp (-v))

private lemma qsLogMellinWeight_contDiff (h : ℝ → ℂ) (σ : ℝ) (hh : IsQSWeight h) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (qsLogMellinWeight h σ) := by
  have h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => Real.exp (-σ * v)) := by
    fun_prop
  have h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => h (Real.exp (-v))) :=
    hh.1.comp (by fun_prop)
  exact h₁.smul h₂

private lemma qsLogMellinWeight_iteratedDeriv_integrable (h : ℝ → ℂ) (σ : ℝ)
    (hσ : 0 < σ) (hh : IsQSWeight h) (n : ℕ) :
    Integrable (iteratedDeriv n (qsLogMellinWeight h σ)) := by
  rcases hh with ⟨hhCont, ⟨B, hB⟩, ⟨δ, hδ, hconst⟩⟩
  let B₁ : ℝ := max B 1
  let δ₁ : ℝ := min δ (B₁ / 2)
  have hB₁ : 0 < B₁ := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hBle : B ≤ B₁ := le_max_left _ _
  have hδ₁ : 0 < δ₁ := lt_min hδ (by positivity)
  have hδ₁δ : δ₁ ≤ δ := min_le_left _ _
  have hhalfB : B₁ / 2 < B₁ := by linarith [hB₁]
  have hδ₁B : δ₁ < B₁ := (min_le_right _ _).trans_lt hhalfB
  let l : ℝ := -Real.log B₁
  let r : ℝ := -Real.log δ₁
  have hlr : l < r := by
    dsimp [l, r]
    have := Real.log_lt_log hδ₁ hδ₁B
    linarith
  let q : ℝ → ℂ := qsLogMellinWeight h σ
  let tail : ℝ → ℂ := fun v => Real.exp (-σ * v) • h 0
  have hqCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q := by
    dsimp [q]
    exact qsLogMellinWeight_contDiff h σ ⟨hhCont, ⟨B, hB⟩, ⟨δ, hδ, hconst⟩⟩
  have hleft : Set.EqOn q (fun _ : ℝ => 0) (Set.Iio l) := by
    intro v hv
    have hvlog : Real.log B₁ < -v := by
      have hv' : v < -Real.log B₁ := by simpa [l] using hv
      simpa using neg_lt_neg hv'
    have hx : B₁ ≤ Real.exp (-v) := by
      rw [← Real.exp_log hB₁]
      exact Real.exp_le_exp.mpr hvlog.le
    have hxB : B ≤ Real.exp (-v) := hBle.trans hx
    change Real.exp (-σ * v) • h (Real.exp (-v)) = 0
    rw [hB _ hxB]
    simp
  have hright : Set.EqOn q tail (Set.Ioi r) := by
    intro v hv
    have hvlog : -v < Real.log δ₁ := by
      have hv' : -Real.log δ₁ < v := by simpa [r] using hv
      linarith
    have hxpos : 0 < Real.exp (-v) := Real.exp_pos _
    have hxle : Real.exp (-v) ≤ δ₁ := by
      calc
        Real.exp (-v) ≤ Real.exp (Real.log δ₁) := Real.exp_le_exp.mpr hvlog.le
        _ = δ₁ := Real.exp_log hδ₁
    have hxδ : Real.exp (-v) ∈ Set.Icc (0 : ℝ) δ := ⟨hxpos.le, hxle.trans hδ₁δ⟩
    change Real.exp (-σ * v) • h (Real.exp (-v)) = Real.exp (-σ * v) • h 0
    rw [hconst _ hxδ]
  have hleftDeriv : Set.EqOn (iteratedDeriv n q) (fun _ : ℝ => 0) (Set.Iio l) := by
    intro v hv
    calc
      iteratedDeriv n q v = iteratedDerivWithin n q (Set.Iio l) v :=
        (iteratedDerivWithin_of_isOpen (f := q) isOpen_Iio hv).symm
      _ = iteratedDerivWithin n (fun _ : ℝ => 0) (Set.Iio l) v :=
        iteratedDerivWithin_congr hleft hv
      _ = iteratedDeriv n (fun _ : ℝ => 0) v :=
        iteratedDerivWithin_of_isOpen isOpen_Iio hv
      _ = 0 := by simp
  have hrightDeriv : Set.EqOn (iteratedDeriv n q) (iteratedDeriv n tail) (Set.Ioi r) := by
    intro v hv
    calc
      iteratedDeriv n q v = iteratedDerivWithin n q (Set.Ioi r) v :=
        (iteratedDerivWithin_of_isOpen (f := q) isOpen_Ioi hv).symm
      _ = iteratedDerivWithin n tail (Set.Ioi r) v :=
        iteratedDerivWithin_congr hright hv
      _ = iteratedDeriv n tail v := iteratedDerivWithin_of_isOpen isOpen_Ioi hv
  have htailDeriv : iteratedDeriv n tail =
      fun v => ((-σ) ^ n * Real.exp (-σ * v)) • h 0 := by
    funext v
    change iteratedDeriv n (fun y : ℝ => Real.exp (-σ * y) • h 0) v = _
    rw [iteratedDeriv_smul_const (by fun_prop : ContDiffAt ℝ n (fun y : ℝ => Real.exp (-σ * y)) v),
      iteratedDeriv_exp_const_mul]
  have hleftInt : IntegrableOn (iteratedDeriv n q) (Set.Iio l) := by
    apply (integrableOn_congr_fun hleftDeriv measurableSet_Iio).2
    simp
  have hmiddleInt : IntegrableOn (iteratedDeriv n q) (Set.Icc l r) := by
    exact (hqCont.continuous_iteratedDeriv n (by simp)).continuousOn.integrableOn_compact isCompact_Icc
  have hExpInt : IntegrableOn (fun v : ℝ => ((-σ) ^ n * Real.exp (-σ * v) : ℝ)) (Set.Ioi r) := by
    have hbase : IntegrableOn (fun v : ℝ => Real.exp ((-σ) * v)) (Set.Ioi r) :=
      integrableOn_exp_mul_Ioi (by linarith) r
    have hmul := hbase.const_mul ((-σ) ^ n)
    change Integrable (fun v : ℝ => (-σ) ^ n * Real.exp ((-σ) * v))
      (volume.restrict (Set.Ioi r))
    simpa using hmul
  have htailInt : IntegrableOn (iteratedDeriv n tail) (Set.Ioi r) := by
    rw [htailDeriv]
    exact hExpInt.smul_const (h 0)
  have hrightInt : IntegrableOn (iteratedDeriv n q) (Set.Ioi r) :=
    (integrableOn_congr_fun hrightDeriv measurableSet_Ioi).2 htailInt
  have hsets : Set.Iio l ∪ Set.Icc l r ∪ Set.Ioi r = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi, Set.mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      by_cases hvl : v < l
      · exact Or.inl (Or.inl hvl)
      · by_cases hvr : v ≤ r
        · exact Or.inl (Or.inr ⟨le_of_not_gt hvl, hvr⟩)
        · exact Or.inr (lt_of_not_ge hvr)
  rw [← integrableOn_univ, ← hsets, integrableOn_union, integrableOn_union]
  exact ⟨⟨hleftInt, hmiddleInt⟩, hrightInt⟩

private lemma qs_fourier_decay_bound (q : ℝ → ℂ)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q)
    (hqInt : ∀ n : ℕ, Integrable (iteratedDeriv n q)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ |y| →
      ‖𝓕 q y‖ ≤ C / |y| ^ n := by
  let C : ℝ := ∫ x : ℝ, ‖iteratedDeriv n q x‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact integral_nonneg (fun x => norm_nonneg _)
  have hFour (y : ℝ) : ‖𝓕 (iteratedDeriv n q) y‖ ≤ C := by
    rw [Real.fourier_eq]
    calc
      ‖∫ x : ℝ, 𝐞 (-⟪x, y⟫) • iteratedDeriv n q x‖ ≤
          ∫ x : ℝ, ‖𝐞 (-⟪x, y⟫) • iteratedDeriv n q x‖ := norm_integral_le_integral_norm _
      _ = C := by simp [C, Circle.norm_smul]
  have hEq := Real.fourier_iteratedDeriv (f := q) (N := ⊤) (n := n) hq
    (fun m hm => hqInt m) (by simp)
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hypos : 0 < |y| := lt_of_lt_of_le zero_lt_one hy
  have hscalar : ‖(2 * Real.pi * Complex.I * (y : ℂ)) ^ n‖ =
      (2 * Real.pi * |y|) ^ n := by
    rw [norm_pow, norm_mul, norm_mul, norm_mul]
    simp [RCLike.norm_ofReal, Real.pi_pos]
  have hnormEq : ‖𝓕 (iteratedDeriv n q) y‖ =
      ‖(2 * Real.pi * Complex.I * (y : ℂ)) ^ n‖ * ‖𝓕 q y‖ := by
    rw [congrFun hEq y, norm_smul]
  have hbig : |y| ^ n * ‖𝓕 q y‖ ≤ C := by
    have hfour : ‖(2 * Real.pi * Complex.I * (y : ℂ)) ^ n‖ * ‖𝓕 q y‖ ≤ C := by
      rw [← hnormEq]
      exact hFour y
    rw [hscalar] at hfour
    have hbase : |y| ^ n ≤ (2 * Real.pi * |y|) ^ n := by
      apply pow_le_pow_left₀ (abs_nonneg _) ?_ n
      have hπ : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      nlinarith
    calc
      |y| ^ n * ‖𝓕 q y‖ ≤ (2 * Real.pi * |y|) ^ n * ‖𝓕 q y‖ :=
        mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
      _ ≤ C := by simpa [mul_comm] using hfour
  rw [le_div_iff₀ (pow_pos hypos n)]
  simpa [mul_comm] using hbig

private lemma qs_mellin_log_fourier (h : ℝ → ℂ) (σ t : ℝ) :
    mellin h ((σ : ℂ) + (t : ℂ) * Complex.I) =
      𝓕 (qsLogMellinWeight h σ) (t / (2 * Real.pi)) := by
  have hfun : (fun u : ℝ =>
      Real.exp (-((σ : ℂ) + (t : ℂ) * Complex.I).re * u) • h (Real.exp (-u))) =
      qsLogMellinWeight h σ := by
    funext u
    simp [qsLogMellinWeight, Complex.add_re, Complex.mul_re, Complex.I_re]
  have h := mellin_eq_fourier h (s := (σ : ℂ) + (t : ℂ) * Complex.I)
  rw [hfun] at h
  simpa using h

private lemma qs_mellin_vertical_decay (h : ℝ → ℂ) (hh : IsQSWeight h)
    {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖mellin h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (|t| + 1) ^ N := by
  let q : ℝ → ℂ := qsLogMellinWeight h σ
  have hqCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q :=
    qsLogMellinWeight_contDiff h σ hh
  have hqInt : ∀ n : ℕ, Integrable (iteratedDeriv n q) :=
    fun n => qsLogMellinWeight_iteratedDeriv_integrable h σ hσ hh n
  obtain ⟨C₀, hC₀, hqDecay⟩ := qs_fourier_decay_bound q hqCont hqInt N
  let C₁ : ℝ := ∫ x : ℝ, ‖q x‖
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; exact integral_nonneg (fun x => norm_nonneg _)
  have hFourBound (y : ℝ) : ‖𝓕 q y‖ ≤ C₁ := by
    rw [Real.fourier_eq]
    calc
      ‖∫ x : ℝ, 𝐞 (-⟪x, y⟫) • q x‖ ≤
          ∫ x : ℝ, ‖𝐞 (-⟪x, y⟫) • q x‖ := norm_integral_le_integral_norm _
      _ = C₁ := by simp [C₁, Circle.norm_smul]
  let A : ℝ := 2 * Real.pi + 1
  let C : ℝ := (C₁ + C₀ + 1) * A ^ N
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [Real.pi_gt_three]
  have hC : 0 < C := by positivity
  have hMellinFourier (t : ℝ) :
      mellin h ((σ : ℂ) + (t : ℂ) * Complex.I) = 𝓕 q (t / (2 * Real.pi)) := by
    simpa [q] using qs_mellin_log_fourier h σ t
  refine ⟨C, hC, ?_⟩
  intro t
  let y : ℝ := t / (2 * Real.pi)
  have hπ2 : 0 < 2 * Real.pi := by positivity
  by_cases ht : |t| < 2 * Real.pi
  · have hden : 0 < (|t| + 1) ^ N := pow_pos (by positivity) _
    have hbase : |t| + 1 ≤ A := by dsimp [A]; linarith
    have hcoef : C₁ * (|t| + 1) ^ N ≤ C := by
      dsimp [C]
      calc
        C₁ * (|t| + 1) ^ N ≤ C₁ * A ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase N) hC₁
        _ ≤ (C₁ + C₀ + 1) * A ^ N := by
          have hsum : C₁ ≤ C₁ + C₀ + 1 := by linarith [hC₀]
          exact mul_le_mul_of_nonneg_right hsum
            (pow_nonneg (le_trans (by norm_num) hA) N)
    have hM : ‖mellin h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₁ := by
      rw [hMellinFourier]
      exact hFourBound y
    exact (le_div_iff₀ hden).2 (by nlinarith)
  · have htlarge : 2 * Real.pi ≤ |t| := le_of_not_gt ht
    have hyabs : |y| = |t| / (2 * Real.pi) := by
      dsimp [y]
      rw [abs_div, abs_of_pos hπ2]
    have hy1 : 1 ≤ |y| := by
      rw [hyabs]
      apply (le_div_iff₀ hπ2).2
      have htlarge' : (1 : ℝ) * (2 * Real.pi) ≤ |t| := by nlinarith [htlarge]
      exact htlarge'
    have htAbs : |t| = (2 * Real.pi) * |y| := by
      calc
        |t| = (|t| / (2 * Real.pi)) * (2 * Real.pi) := by field_simp
        _ = |y| * (2 * Real.pi) := by rw [← hyabs]
        _ = _ := by ring
    have htPlus : |t| + 1 ≤ A * |y| := by
      rw [htAbs]
      dsimp [A]
      nlinarith [hy1]
    have hFour : ‖𝓕 q y‖ ≤ C₀ / |y| ^ N := hqDecay y hy1
    have hdenY : 0 < |y| ^ N := pow_pos (lt_of_lt_of_le zero_lt_one hy1) _
    have hdenT : 0 < (|t| + 1) ^ N := pow_pos (by positivity) _
    have hpow : (|t| + 1) ^ N ≤ A ^ N * |y| ^ N := by
      calc
        (|t| + 1) ^ N ≤ (A * |y|) ^ N := pow_le_pow_left₀ (by positivity) htPlus N
        _ = A ^ N * |y| ^ N := mul_pow _ _ _
    have hcoef : C₀ * A ^ N ≤ C := by
      dsimp [C]
      apply mul_le_mul_of_nonneg_right
      · linarith
      · positivity
    have hfrac : C₀ / |y| ^ N ≤ C / (|t| + 1) ^ N := by
      apply (div_le_div_iff₀ hdenY hdenT).2
      calc
        C₀ * (|t| + 1) ^ N ≤ C₀ * (A ^ N * |y| ^ N) :=
          mul_le_mul_of_nonneg_left hpow hC₀
        _ = (C₀ * A ^ N) * |y| ^ N := by ring
        _ ≤ C * |y| ^ N := mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg y) N)
    calc
      ‖mellin h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ = ‖𝓕 q y‖ := by rw [hMellinFourier]
      _ ≤ C₀ / |y| ^ N := hFour
      _ ≤ C / (|t| + 1) ^ N := hfrac

private def qsMellinTransformLine (K : Type) [Field K] [NumberField K]
    (h : ℝ → ℂ) (y : ℝ) : ℂ :=
  qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) *
    mellin h ((1 / 2 : ℂ) - (2 * Real.pi * y : ℝ) * Complex.I)

private lemma qs_gammaC_logDeriv (z : ℂ) (hzNoPole : ∀ n : ℕ, z ≠ -(n : ℂ)) :
    logDeriv (fun w : ℂ => Complex.Gammaℂ w) z =
      -Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma z := by
  let A : ℂ := 2 * (Real.pi : ℂ)
  have hA : A ≠ 0 := by
    dsimp [A]
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hΓ : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hzNoPole
  have hΓ0 : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzNoPole
  have hpow : DifferentiableAt ℂ (fun w : ℂ => A ^ (-w)) z :=
    (differentiableAt_id.neg.const_cpow (Or.inl hA))
  have hpow0 : A ^ (-z) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
  have hprod : DifferentiableAt ℂ (fun w : ℂ => A ^ (-w) * Complex.Gamma w) z :=
    hpow.mul hΓ
  have hprod0 : A ^ (-z) * Complex.Gamma z ≠ 0 := mul_ne_zero hpow0 hΓ0
  have hdef : (fun w : ℂ => Complex.Gammaℂ w) =
      fun w => 2 * (A ^ (-w) * Complex.Gamma w) := by
    funext w
    simp [Complex.Gammaℂ_def, A, mul_assoc]
  rw [hdef, logDeriv_const_mul z (2 : ℂ) (by norm_num),
    show (fun w : ℂ => A ^ (-w) * Complex.Gamma w) =
      (fun w : ℂ => A ^ (-w)) * Complex.Gamma from rfl,
    logDeriv_mul z hpow0 hΓ0 hpow hΓ]
  have hpowLog : logDeriv (fun w : ℂ => A ^ (-w)) z = -Complex.log A := by
    rw [logDeriv_apply, Complex.deriv_const_cpow (by fun_prop) A]
    simp only [deriv_neg, mul_neg, mul_one]
    rw [div_eq_iff hpow0]
  rw [hpowLog, Complex.digamma_def]

private lemma qs_gammaC_nezero (z : ℂ) (hz : 0 < z.re) : Complex.Gammaℂ z ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  have hA : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hpow : (2 * (Real.pi : ℂ)) ^ (-z) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
  have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  exact mul_ne_zero (mul_ne_zero (by norm_num) hpow) hΓ

private lemma qs_prefactor_nezero [IsTotallyComplex K] (z : ℂ) (hz : 0 < z.re) :
    Hecke.dedekindPrefactor K z ≠ 0 := by
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  have hDreal : (|(NumberField.discr K : ℝ)| : ℝ) ≠ 0 := by
    exact abs_ne_zero.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact Complex.ofReal_ne_zero.mpr hDreal
  have hcpow : D ^ (z / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hD)
  rw [Hecke.dedekindPrefactor, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero,
    pow_zero, one_mul]
  exact mul_ne_zero hcpow (pow_ne_zero _ (qs_gammaC_nezero z hz))

private lemma qs_prefactor_differentiableAt [IsTotallyComplex K] (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ (Hecke.dedekindPrefactor K) z := by
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  have hDreal : (|(NumberField.discr K : ℝ)| : ℝ) ≠ 0 := by
    exact abs_ne_zero.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact Complex.ofReal_ne_zero.mpr hDreal
  have hDpow : DifferentiableAt ℂ (fun w : ℂ => D ^ (w / 2)) z :=
    (differentiableAt_id.div_const (2 : ℂ)).const_cpow (Or.inl hD)
  have hzNoPole : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have hreal : z.re = -(n : ℝ) := by rw [hn]; simp
    rw [hreal] at hz
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hΓ : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hzNoPole
  have hA : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hCpow : DifferentiableAt ℂ (fun w : ℂ => (2 * (Real.pi : ℂ)) ^ (-w)) z :=
    differentiableAt_id.neg.const_cpow (Or.inl hA)
  have hΓC : DifferentiableAt ℂ (fun w : ℂ => Complex.Gammaℂ w) z := by
    have hdef : (fun w : ℂ => Complex.Gammaℂ w) =
        fun w => 2 * ((2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w) := by
      funext w
      simp [Complex.Gammaℂ_def, mul_assoc]
    rw [hdef]
    exact (hCpow.mul hΓ).const_mul (2 : ℂ)
  change DifferentiableAt ℂ (fun w : ℂ =>
    D ^ (w / 2) *
      (Complex.Gammaℝ w ^ NumberField.InfinitePlace.nrRealPlaces K *
        Complex.Gammaℂ w ^ NumberField.InfinitePlace.nrComplexPlaces K)) z
  rw [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  simp only [pow_zero, one_mul]
  exact hDpow.mul (hΓC.pow _)

private lemma qs_gammaC_inv_differentiable :
    Differentiable ℂ (fun z : ℂ => (Complex.Gammaℂ z)⁻¹) := by
  let A : ℂ := 2 * (Real.pi : ℂ)
  have hA : A ≠ 0 := by
    dsimp [A]
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hEq : (fun z : ℂ => (Complex.Gammaℂ z)⁻¹) =
      fun z => (2 : ℂ)⁻¹ * A ^ z * (Complex.Gamma z)⁻¹ := by
    funext z
    rw [Complex.Gammaℂ_def]
    have hcpow : ((A ^ (-z))⁻¹) = A ^ z := by
      rw [Complex.cpow_neg, inv_inv]
    simp only [show 2 * (Real.pi : ℂ) = A by rfl, mul_inv_rev, hcpow]
    ring
  rw [hEq]
  have hcpow : Differentiable ℂ (fun z : ℂ => A ^ z) := by
    intro z
    exact (differentiableAt_id.const_cpow (Or.inl hA))
  have hGammaInv : Differentiable ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
    Complex.differentiable_one_div_Gamma
  intro z
  exact ((differentiableAt_const _).mul (hcpow z)).mul (hGammaInv z)

private lemma qs_gammaC_inv_formula (s : ℂ) :
    (Complex.Gammaℂ s)⁻¹ =
      ((1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ s) *
        (s * (Complex.Gamma (s + 1))⁻¹) := by
  let A : ℂ := 2 * (Real.pi : ℂ)
  rw [Complex.Gammaℂ_def]
  have hA : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hrec := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s
  have hpowInv : ((A ^ (-s))⁻¹) = A ^ s := by
    rw [Complex.cpow_neg, inv_inv]
  rw [show 2 * (Real.pi : ℂ) = A by rfl, mul_inv_rev, mul_inv_rev, hpowInv]
  rw [hrec]
  ring

private lemma qs_prefactor_inv_differentiableAt [IsTotallyComplex K] (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => (Hecke.dedekindPrefactor K w)⁻¹) z := by
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  have hDreal : (|(NumberField.discr K : ℝ)| : ℝ) ≠ 0 := by
    exact abs_ne_zero.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact Complex.ofReal_ne_zero.mpr hDreal
  have hEq : (fun w : ℂ => (Hecke.dedekindPrefactor K w)⁻¹) =
      fun w => D ^ (-w / 2) * (Complex.Gammaℂ w)⁻¹ ^
        NumberField.InfinitePlace.nrComplexPlaces K := by
    funext w
    rw [Hecke.dedekindPrefactor, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero,
      pow_zero, one_mul]
    have hcpow : (D ^ (w / 2))⁻¹ = D ^ (-w / 2) := by
      rw [← Complex.cpow_neg]
      congr 1 <;> ring
    rw [mul_inv_rev, hcpow, inv_pow]
    ring
  rw [hEq]
  have hDpow : DifferentiableAt ℂ (fun w : ℂ => D ^ (-w / 2)) z := by
    exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hD)
  exact hDpow.mul ((qs_gammaC_inv_differentiable z).pow _)

private lemma qs_prefactor_inv_formula [IsTotallyComplex K] (s : ℂ) :
    (Hecke.dedekindPrefactor K s)⁻¹ =
      (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (-s / 2)) *
        ((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
  have hDreal : (|(NumberField.discr K : ℝ)| : ℝ) ≠ 0 := by
    exact abs_ne_zero.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hD : ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hDreal
  rw [Hecke.dedekindPrefactor, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero,
    pow_zero, one_mul, mul_inv_rev, inv_pow]
  have hcpow : (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2))⁻¹ =
      ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (-s / 2) := by
    rw [← Complex.cpow_neg]
    congr 1 <;> ring
  rw [hcpow]
  ring

private lemma qs_gammaRatio_differentiableAt_right [IsTotallyComplex K]
    (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ (fun w : ℂ => qsGammaRatio K w) z := by
  have hnum : DifferentiableAt ℂ (Hecke.dedekindPrefactor K) z :=
    qs_prefactor_differentiableAt z hz
  have hden : DifferentiableAt ℂ
      (fun w : ℂ => (Hecke.dedekindPrefactor K (1 - w))⁻¹) z := by
    exact (qs_prefactor_inv_differentiableAt (1 - z)).comp z (by fun_prop)
  change DifferentiableAt ℂ
    (fun w : ℂ => Hecke.dedekindPrefactor K w * (Hecke.dedekindPrefactor K (1 - w))⁻¹) z
  exact hnum.mul hden

private lemma qs_prefactor_logDeriv [IsTotallyComplex K] (z : ℂ) (hz : 0 < z.re) :
    logDeriv (fun w : ℂ => Hecke.dedekindPrefactor K w) z =
      Complex.log ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) / 2 +
        (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) *
          (-Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma z) := by
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  have hDreal : (|(NumberField.discr K : ℝ)| : ℝ) ≠ 0 := by
    exact abs_ne_zero.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact Complex.ofReal_ne_zero.mpr hDreal
  have hDpow0 : D ^ (z / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hD)
  have hDpowDiff : DifferentiableAt ℂ (fun w : ℂ => D ^ (w / 2)) z :=
    (differentiableAt_id.div_const (2 : ℂ)).const_cpow (Or.inl hD)
  have hDpowLog : logDeriv (fun w : ℂ => D ^ (w / 2)) z = Complex.log D / 2 := by
    rw [logDeriv_apply, Complex.deriv_const_cpow (by fun_prop) D]
    have hderiv : deriv (fun w : ℂ => w / 2) z = (1 / 2 : ℂ) := by simp
    rw [hderiv]
    field_simp [hDpow0]
  have hzNoPole : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have hreal : z.re = -(n : ℝ) := by rw [hn]; simp
    rw [hreal] at hz
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hΓ : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hzNoPole
  have hΓ0 : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hA : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hCpow : DifferentiableAt ℂ (fun w : ℂ => (2 * (Real.pi : ℂ)) ^ (-w)) z :=
    differentiableAt_id.neg.const_cpow (Or.inl hA)
  have hCpow0 : (2 * (Real.pi : ℂ)) ^ (-z) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
  have hΓC : DifferentiableAt ℂ (fun w : ℂ => Complex.Gammaℂ w) z := by
    have hdef : (fun w : ℂ => Complex.Gammaℂ w) =
        fun w => 2 * ((2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w) := by
      funext w
      simp [Complex.Gammaℂ_def, mul_assoc]
    rw [hdef]
    exact (hCpow.mul hΓ).const_mul (2 : ℂ)
  have hΓC0 : Complex.Gammaℂ z ≠ 0 := qs_gammaC_nezero z hz
  have hGammaPowDiff : DifferentiableAt ℂ
      (fun w : ℂ => Complex.Gammaℂ w ^ NumberField.InfinitePlace.nrComplexPlaces K) z :=
    hΓC.pow _
  have hGammaPow0 : Complex.Gammaℂ z ^ NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 :=
    pow_ne_zero _ hΓC0
  have hdef : (fun w : ℂ => Hecke.dedekindPrefactor K w) =
      fun w => D ^ (w / 2) * Complex.Gammaℂ w ^ NumberField.InfinitePlace.nrComplexPlaces K := by
    funext w
    simp [Hecke.dedekindPrefactor, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero,
      D, pow_zero]
  have hfun : (fun w : ℂ => D ^ (w / 2) *
      Complex.Gammaℂ w ^ NumberField.InfinitePlace.nrComplexPlaces K) =
      (fun w : ℂ => D ^ (w / 2)) *
        (fun w : ℂ => Complex.Gammaℂ w ^ NumberField.InfinitePlace.nrComplexPlaces K) := rfl
  rw [hdef, hfun, logDeriv_mul z hDpow0 hGammaPow0 hDpowDiff hGammaPowDiff,
    logDeriv_fun_pow hΓC (NumberField.InfinitePlace.nrComplexPlaces K), hDpowLog,
    qs_gammaC_logDeriv z hzNoPole]

private lemma qs_prefactor_nezero_of_im [IsTotallyComplex K] (z : ℂ) (him : z.im ≠ 0) :
    Hecke.dedekindPrefactor K z ≠ 0 := by
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  have hDreal : (|(NumberField.discr K : ℝ)| : ℝ) ≠ 0 := by
    exact abs_ne_zero.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact Complex.ofReal_ne_zero.mpr hDreal
  have hDpow : D ^ (z / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hD)
  have hzNoPole : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have : z.im = 0 := by rw [hn]; simp
    exact him this
  have hGamma : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzNoPole
  have hA : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hGammaC : Complex.Gammaℂ z ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hA))) hGamma
  rw [Hecke.dedekindPrefactor, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero,
    pow_zero, one_mul]
  exact mul_ne_zero hDpow (pow_ne_zero _ hGammaC)

private lemma qs_prefactor_differentiableAt_of_im [IsTotallyComplex K]
    (z : ℂ) (him : z.im ≠ 0) :
    DifferentiableAt ℂ (Hecke.dedekindPrefactor K) z := by
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  have hDreal : (|(NumberField.discr K : ℝ)| : ℝ) ≠ 0 := by
    exact abs_ne_zero.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact Complex.ofReal_ne_zero.mpr hDreal
  have hDpow : DifferentiableAt ℂ (fun w : ℂ => D ^ (w / 2)) z :=
    (differentiableAt_id.div_const (2 : ℂ)).const_cpow (Or.inl hD)
  have hzNoPole : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have : z.im = 0 := by rw [hn]; simp
    exact him this
  have hGamma : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hzNoPole
  have hA : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hCpow : DifferentiableAt ℂ (fun w : ℂ => (2 * (Real.pi : ℂ)) ^ (-w)) z :=
    differentiableAt_id.neg.const_cpow (Or.inl hA)
  have hGammaC : DifferentiableAt ℂ (fun w : ℂ => Complex.Gammaℂ w) z := by
    have hdef : (fun w : ℂ => Complex.Gammaℂ w) =
        fun w => 2 * ((2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w) := by
      funext w
      simp [Complex.Gammaℂ_def, mul_assoc]
    rw [hdef]
    exact (hCpow.mul hGamma).const_mul (2 : ℂ)
  change DifferentiableAt ℂ (fun w : ℂ =>
    D ^ (w / 2) * (Complex.Gammaℝ w ^ NumberField.InfinitePlace.nrRealPlaces K *
      Complex.Gammaℂ w ^ NumberField.InfinitePlace.nrComplexPlaces K)) z
  rw [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  simp only [pow_zero, one_mul]
  exact hDpow.mul (hGammaC.pow _)

private lemma qs_prefactor_logDeriv_of_im [IsTotallyComplex K]
    (z : ℂ) (him : z.im ≠ 0) :
    logDeriv (fun w : ℂ => Hecke.dedekindPrefactor K w) z =
      Complex.log ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) / 2 +
        (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) *
          (-Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma z) := by
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  have hDreal : (|(NumberField.discr K : ℝ)| : ℝ) ≠ 0 := by
    exact abs_ne_zero.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact Complex.ofReal_ne_zero.mpr hDreal
  have hDpow0 : D ^ (z / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hD)
  have hDpowDiff : DifferentiableAt ℂ (fun w : ℂ => D ^ (w / 2)) z :=
    (differentiableAt_id.div_const (2 : ℂ)).const_cpow (Or.inl hD)
  have hDpowLog : logDeriv (fun w : ℂ => D ^ (w / 2)) z = Complex.log D / 2 := by
    rw [logDeriv_apply, Complex.deriv_const_cpow (by fun_prop) D]
    have hderiv : deriv (fun w : ℂ => w / 2) z = (1 / 2 : ℂ) := by simp
    rw [hderiv]
    field_simp [hDpow0]
  have hzNoPole : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have : z.im = 0 := by rw [hn]; simp
    exact him this
  have hGamma : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hzNoPole
  have hA : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hCpow : DifferentiableAt ℂ (fun w : ℂ => (2 * (Real.pi : ℂ)) ^ (-w)) z :=
    differentiableAt_id.neg.const_cpow (Or.inl hA)
  have hGammaC : DifferentiableAt ℂ (fun w : ℂ => Complex.Gammaℂ w) z := by
    have hGammaCdef : (fun w : ℂ => Complex.Gammaℂ w) =
        fun w => 2 * ((2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w) := by
      funext w
      simp [Complex.Gammaℂ_def, mul_assoc]
    rw [hGammaCdef]
    exact (hCpow.mul hGamma).const_mul (2 : ℂ)
  have hGammaC0 : Complex.Gammaℂ z ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hA))) (Complex.Gamma_ne_zero hzNoPole)
  have hGammaPowDiff : DifferentiableAt ℂ
      (fun w : ℂ => Complex.Gammaℂ w ^ NumberField.InfinitePlace.nrComplexPlaces K) z :=
    hGammaC.pow _
  have hdef : (fun w : ℂ => Hecke.dedekindPrefactor K w) =
      fun w => D ^ (w / 2) * Complex.Gammaℂ w ^ NumberField.InfinitePlace.nrComplexPlaces K := by
    funext w
    simp [Hecke.dedekindPrefactor, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero,
      D, pow_zero]
  have hGammaPow0 : Complex.Gammaℂ z ^ NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 :=
    pow_ne_zero _ hGammaC0
  rw [hdef, show (fun w : ℂ => D ^ (w / 2) * Complex.Gammaℂ w ^
      NumberField.InfinitePlace.nrComplexPlaces K) =
      (fun w : ℂ => D ^ (w / 2)) *
        (fun w : ℂ => Complex.Gammaℂ w ^ NumberField.InfinitePlace.nrComplexPlaces K) from rfl,
    logDeriv_mul z hDpow0 hGammaPow0 hDpowDiff hGammaPowDiff,
    logDeriv_fun_pow hGammaC (NumberField.InfinitePlace.nrComplexPlaces K), hDpowLog]
  rw [qs_gammaC_logDeriv z hzNoPole]

private lemma qs_gammaRatio_logDeriv [IsTotallyComplex K] (z : ℂ)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    logDeriv (fun w : ℂ => qsGammaRatio K w) z =
      Complex.log ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) +
        (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) *
          (-2 * Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma z +
            Complex.digamma (1 - z)) := by
  let P : ℂ → ℂ := Hecke.dedekindPrefactor K
  have hPz0 : P z ≠ 0 := qs_prefactor_nezero z hz0
  have hP1z0 : P (1 - z) ≠ 0 := by
    apply qs_prefactor_nezero
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hPzDiff : DifferentiableAt ℂ P z := qs_prefactor_differentiableAt z hz0
  have hP1zDiff : DifferentiableAt ℂ P (1 - z) := by
    apply qs_prefactor_differentiableAt
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hOneSubDiff : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  have hdenDiff : DifferentiableAt ℂ (fun w : ℂ => P (1 - w)) z := hP1zDiff.comp z hOneSubDiff
  have hratioDef : (fun w : ℂ => qsGammaRatio K w) =
      fun w => P w / P (1 - w) := by rfl
  have hfun : (fun w : ℂ => P w / P (1 - w)) = P / (fun w : ℂ => P (1 - w)) := rfl
  rw [hratioDef, hfun, logDeriv_div z hPz0 hP1z0 hPzDiff hdenDiff,
    show (fun w : ℂ => P (1 - w)) = P ∘ (fun w : ℂ => 1 - w) from rfl,
    logDeriv_comp hP1zDiff hOneSubDiff]
  have hderiv : deriv (fun w : ℂ => 1 - w) z = -1 := by simp
  rw [hderiv]
  rw [qs_prefactor_logDeriv z hz0, qs_prefactor_logDeriv (1 - z) (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith)]
  ring

private lemma qs_gammaRatio_logDeriv_of_im [IsTotallyComplex K] (z : ℂ)
    (hz0 : 0 < z.re) (him : z.im ≠ 0) :
    logDeriv (fun w : ℂ => qsGammaRatio K w) z =
      Complex.log ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) +
        (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) *
          (-2 * Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma z +
            Complex.digamma (1 - z)) := by
  let P : ℂ → ℂ := Hecke.dedekindPrefactor K
  have h1im : (1 - z).im ≠ 0 := by simpa using neg_ne_zero.mpr him
  have hPz0 : P z ≠ 0 := qs_prefactor_nezero z hz0
  have hP1z0 : P (1 - z) ≠ 0 := qs_prefactor_nezero_of_im (1 - z) h1im
  have hPzDiff : DifferentiableAt ℂ P z := qs_prefactor_differentiableAt z hz0
  have hP1zDiff : DifferentiableAt ℂ P (1 - z) :=
    qs_prefactor_differentiableAt_of_im (1 - z) h1im
  have hOneSubDiff : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  have hdenDiff : DifferentiableAt ℂ (fun w : ℂ => P (1 - w)) z :=
    hP1zDiff.comp z hOneSubDiff
  have hratioDef : (fun w : ℂ => qsGammaRatio K w) = fun w => P w / P (1 - w) := by rfl
  have hfun : (fun w : ℂ => P w / P (1 - w)) = P / (fun w : ℂ => P (1 - w)) := rfl
  rw [hratioDef, hfun, logDeriv_div z hPz0 hP1z0 hPzDiff hdenDiff,
    show (fun w : ℂ => P (1 - w)) = P ∘ (fun w : ℂ => 1 - w) from rfl,
    logDeriv_comp hP1zDiff hOneSubDiff]
  have hderiv : deriv (fun w : ℂ => 1 - w) z = -1 := by simp
  rw [hderiv, qs_prefactor_logDeriv z hz0, qs_prefactor_logDeriv_of_im (1 - z) h1im]
  ring

private lemma qs_digamma_pair_bound_high {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      ‖Complex.digamma z‖ + ‖Complex.digamma (1 - z)‖ ≤
        C * Real.log (|z.im| + 2) := by
  obtain ⟨Cz, hCz, hψz⟩ :=
    ArtinPrimitiveRoots.Ext.SplittingInputs.ext_digamma_strip (a := a) (b := b) ha
  obtain ⟨N, hN⟩ := exists_nat_gt (b - 1)
  have ha' : 0 < 1 - b + (N : ℝ) := by linarith
  obtain ⟨Cw, hCw, hψw⟩ :=
    ArtinPrimitiveRoots.Ext.SplittingInputs.ext_digamma_strip
      (a := 1 - b + (N : ℝ)) (b := 1 - a + (N : ℝ)) ha'
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := Cz + Cw + (N : ℝ) / Real.log 3
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro z hza hzb him
  have him0 : z.im ≠ 0 := by
    intro h
    rw [h] at him
    norm_num at him
  have hlogL : 0 < Real.log (|z.im| + 2) := by
    apply Real.log_pos
    have : 0 ≤ |z.im| := abs_nonneg _
    linarith
  have hlog3le : Real.log (3 : ℝ) ≤ Real.log (|z.im| + 2) := by
    apply Real.log_le_log (by norm_num)
    linarith
  have hψz' : ‖Complex.digamma z‖ ≤ Cz * Real.log (|z.im| + 2) := by
    have h := hψz z hza hzb
    rw [Complex.digamma_def, logDeriv_apply]
    exact h
  let w : ℂ := 1 - z
  have hwNoPole : ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro m hm
    have hzero : z.im = 0 := by
      have ht := congrArg Complex.im hm
      simp [w] at ht
      linarith
    exact him0 hzero
  have hrec := Complex.digamma_apply_add_nat (s := w) hwNoPole N
  have hshiftRe : (w + (N : ℂ)).re = 1 - z.re + (N : ℝ) := by simp [w]
  have hshiftIm : (w + (N : ℂ)).im = -z.im := by simp [w]
  have hshiftBounds :
      1 - b + (N : ℝ) ≤ (w + (N : ℂ)).re ∧
        (w + (N : ℂ)).re ≤ 1 - a + (N : ℝ) := by
    rw [hshiftRe]
    constructor <;> linarith
  have hψshift : ‖Complex.digamma (w + (N : ℂ))‖ ≤
      Cw * Real.log (|z.im| + 2) := by
    have h := hψw (w + (N : ℂ)) hshiftBounds.1 hshiftBounds.2
    simpa [Complex.digamma_def, logDeriv_apply, hshiftIm, abs_neg] using h
  have hsum : ‖∑ k ∈ Finset.range N, (w + (k : ℂ))⁻¹‖ ≤ (N : ℝ) := by
    calc
      ‖∑ k ∈ Finset.range N, (w + (k : ℂ))⁻¹‖ ≤
          ∑ k ∈ Finset.range N, ‖(w + (k : ℂ))⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, (1 : ℝ) := by
        gcongr with k hk
        rw [norm_inv]
        have himTerm : |(w + (k : ℂ)).im| = |z.im| := by simp [w, abs_neg]
        have hnorm : 1 ≤ ‖w + (k : ℂ)‖ := by
          calc
            1 ≤ |(w + (k : ℂ)).im| := by rw [himTerm]; exact him
            _ ≤ ‖w + (k : ℂ)‖ := Complex.abs_im_le_norm _
        exact (inv_le_one₀ (by positivity)).2 hnorm
      _ = N := by simp
  have hψw' : ‖Complex.digamma w‖ ≤ Cw * Real.log (|z.im| + 2) + N := by
    have hident : Complex.digamma w = Complex.digamma (w + (N : ℂ)) -
        ∑ k ∈ Finset.range N, (w + (k : ℂ))⁻¹ := by rw [hrec]; ring
    rw [hident]
    calc
      ‖Complex.digamma (w + (N : ℂ)) - ∑ k ∈ Finset.range N, (w + (k : ℂ))⁻¹‖ ≤
          ‖Complex.digamma (w + (N : ℂ))‖ +
            ‖∑ k ∈ Finset.range N, (w + (k : ℂ))⁻¹‖ := norm_sub_le _ _
      _ ≤ Cw * Real.log (|z.im| + 2) + N := add_le_add hψshift hsum
  have hNbound : (N : ℝ) ≤ ((N : ℝ) / Real.log 3) * Real.log (|z.im| + 2) := by
    calc
      (N : ℝ) = ((N : ℝ) / Real.log 3) * Real.log 3 := by
        field_simp [ne_of_gt hlog3]
      _ ≤ ((N : ℝ) / Real.log 3) * Real.log (|z.im| + 2) :=
        mul_le_mul_of_nonneg_left hlog3le (div_nonneg (Nat.cast_nonneg _) hlog3.le)
  calc
    ‖Complex.digamma z‖ + ‖Complex.digamma (1-z)‖ =
        ‖Complex.digamma z‖ + ‖Complex.digamma w‖ := by rfl
    _ ≤ Cz * Real.log (|z.im| + 2) +
        (Cw * Real.log (|z.im| + 2) + N) := add_le_add hψz' hψw'
    _ = (Cz + Cw) * Real.log (|z.im| + 2) + N := by ring
    _ ≤ (Cz + Cw) * Real.log (|z.im| + 2) +
        ((N : ℝ) / Real.log 3) * Real.log (|z.im| + 2) :=
      add_le_add (le_rfl) hNbound
    _ = C * Real.log (|z.im| + 2) := by dsimp [C]; ring

private lemma qs_gammaRatio_logDeriv_bound_high [IsTotallyComplex K] {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      ‖logDeriv (fun w : ℂ => qsGammaRatio K w) z‖ ≤ C * Real.log (|z.im| + 2) := by
  obtain ⟨Cψ, hCψ, hψ⟩ := qs_digamma_pair_bound_high ha hab
  let LD : ℂ := Complex.log ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  let LA : ℂ := Complex.log (2 * (Real.pi : ℂ))
  let r : ℂ := NumberField.InfinitePlace.nrComplexPlaces K
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  let C₀ : ℝ := ‖LD‖ / Real.log 3 +
    ‖r‖ * (2 * ‖LA‖ / Real.log 3 + Cψ)
  let C : ℝ := C₀ + 1
  have hC : 0 < C := by dsimp [C, C₀]; positivity
  refine ⟨C, hC, ?_⟩
  intro z hza hzb him
  have him0 : z.im ≠ 0 := by
    intro h
    rw [h] at him
    norm_num at him
  have hψpair := hψ z hza hzb him
  have hlogL : 0 < Real.log (|z.im| + 2) := by
    apply Real.log_pos
    have : 0 ≤ |z.im| := abs_nonneg _
    linarith
  have hlog3le : Real.log (3 : ℝ) ≤ Real.log (|z.im| + 2) := by
    apply Real.log_le_log (by norm_num)
    linarith
  have hLD : ‖LD‖ ≤ (‖LD‖ / Real.log 3) * Real.log (|z.im| + 2) := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hlog3).2 (mul_le_mul_of_nonneg_left hlog3le (norm_nonneg _))
  have hLA : 2 * ‖LA‖ ≤ (2 * ‖LA‖ / Real.log 3) * Real.log (|z.im| + 2) := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hlog3).2
      (mul_le_mul_of_nonneg_left hlog3le (by positivity))
  have hlog := qs_gammaRatio_logDeriv_of_im (K := K) z
    (lt_of_lt_of_le ha hza) him0
  have hinner : ‖-2 * LA + Complex.digamma z + Complex.digamma (1-z)‖ ≤
      2 * ‖LA‖ + ‖Complex.digamma z‖ + ‖Complex.digamma (1-z)‖ := by
    have hfirst : ‖-2 * LA + Complex.digamma z‖ ≤
        2 * ‖LA‖ + ‖Complex.digamma z‖ := by
      calc
        _ ≤ ‖-2 * LA‖ + ‖Complex.digamma z‖ := norm_add_le _ _
        _ = _ := by simp
    calc
      ‖-2 * LA + Complex.digamma z + Complex.digamma (1-z)‖ ≤
          ‖-2 * LA + Complex.digamma z‖ + ‖Complex.digamma (1-z)‖ := norm_add_le _ _
      _ ≤ (2 * ‖LA‖ + ‖Complex.digamma z‖) + ‖Complex.digamma (1-z)‖ :=
        add_le_add hfirst (le_rfl)
      _ = _ := by simp
  have hnorm : ‖logDeriv (fun w : ℂ => qsGammaRatio K w) z‖ ≤
      ‖LD‖ + ‖r‖ * (2 * ‖LA‖ + ‖Complex.digamma z‖ + ‖Complex.digamma (1-z)‖) := by
    rw [hlog]
    change ‖LD + r * (-2 * LA + Complex.digamma z + Complex.digamma (1-z))‖ ≤
      ‖LD‖ + ‖r‖ * (2 * ‖LA‖ + ‖Complex.digamma z‖ + ‖Complex.digamma (1-z)‖)
    calc
      _ ≤ ‖LD‖ + ‖r * (-2 * LA + Complex.digamma z + Complex.digamma (1-z))‖ :=
        norm_add_le LD (r * (-2 * LA + Complex.digamma z + Complex.digamma (1-z)))
      _ = ‖LD‖ + ‖r‖ * ‖-2 * LA + Complex.digamma z + Complex.digamma (1-z)‖ := by rw [norm_mul]
      _ ≤ ‖LD‖ + ‖r‖ *
        (2 * ‖LA‖ + ‖Complex.digamma z‖ + ‖Complex.digamma (1-z)‖) :=
        add_le_add (le_rfl) (mul_le_mul_of_nonneg_left hinner (norm_nonneg r))
  have hInner' :
      2 * ‖LA‖ + ‖Complex.digamma z‖ + ‖Complex.digamma (1-z)‖ ≤
        (2 * ‖LA‖ / Real.log 3 + Cψ) * Real.log (|z.im| + 2) := by
    calc
      _ = 2 * ‖LA‖ + (‖Complex.digamma z‖ + ‖Complex.digamma (1-z)‖) := by ring
      _ ≤ 2 * ‖LA‖ + Cψ * Real.log (|z.im| + 2) :=
        add_le_add (le_rfl) hψpair
      _ ≤ (2 * ‖LA‖ / Real.log 3) * Real.log (|z.im| + 2) +
          Cψ * Real.log (|z.im| + 2) := add_le_add hLA (le_rfl)
      _ = (2 * ‖LA‖ / Real.log 3 + Cψ) * Real.log (|z.im| + 2) := by rw [add_mul]
  have hmain :
      ‖LD‖ + ‖r‖ * (2 * ‖LA‖ + ‖Complex.digamma z‖ + ‖Complex.digamma (1-z)‖) ≤
        C₀ * Real.log (|z.im| + 2) := by
    dsimp [C₀]
    calc
      _ ≤ (‖LD‖ / Real.log 3) * Real.log (|z.im| + 2) +
          ‖r‖ * ((2 * ‖LA‖ / Real.log 3 + Cψ) * Real.log (|z.im| + 2)) :=
        add_le_add hLD (mul_le_mul_of_nonneg_left hInner' (norm_nonneg r))
      _ = _ := by ring
  calc
    ‖logDeriv (fun w : ℂ => qsGammaRatio K w) z‖ ≤
        ‖LD‖ + ‖r‖ * (2 * ‖LA‖ + ‖Complex.digamma z‖ + ‖Complex.digamma (1-z)‖) := hnorm
    _ ≤ C₀ * Real.log (|z.im| + 2) := hmain
    _ ≤ C * Real.log (|z.im| + 2) := by
      change C₀ * Real.log (|z.im| + 2) ≤
        (C₀ + 1) * Real.log (|z.im| + 2)
      calc
        _ = C₀ * Real.log (|z.im| + 2) + 0 := by ring
        _ ≤ C₀ * Real.log (|z.im| + 2) + Real.log (|z.im| + 2) :=
          add_le_add (le_rfl) (le_of_lt hlogL)
        _ = (C₀ + 1) * Real.log (|z.im| + 2) := by ring

private lemma qs_gammaRatio_differentiableAt [IsTotallyComplex K] (z : ℂ)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    DifferentiableAt ℂ (fun w : ℂ => qsGammaRatio K w) z := by
  let P : ℂ → ℂ := Hecke.dedekindPrefactor K
  have hPz0 : P z ≠ 0 := qs_prefactor_nezero z hz0
  have hP1z0 : P (1 - z) ≠ 0 := by
    apply qs_prefactor_nezero
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hPzDiff : DifferentiableAt ℂ P z := qs_prefactor_differentiableAt z hz0
  have hP1zDiff : DifferentiableAt ℂ P (1 - z) := by
    apply qs_prefactor_differentiableAt
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hOneSubDiff : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  have hdenDiff : DifferentiableAt ℂ (fun w : ℂ => P (1 - w)) z :=
    hP1zDiff.comp z hOneSubDiff
  change DifferentiableAt ℂ (fun w : ℂ => P w / P (1 - w)) z
  exact hPzDiff.div hdenDiff hP1z0

private lemma qs_ofReal_cpow_conj (r : ℝ) (hr : 0 ≤ r) (w : ℂ) :
    conj ((r : ℂ) ^ w) = (r : ℂ) ^ conj w := by
  have harg : Complex.arg (r : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr]
    exact Real.pi_ne_zero.symm
  simpa [RCLike.conj_ofReal] using
    (Complex.conj_cpow (r : ℂ) (conj w) harg).symm

private lemma qs_gammaC_conj (w : ℂ) :
    Complex.Gammaℂ (conj w) = conj (Complex.Gammaℂ w) := by
  rw [Complex.Gammaℂ_def, Complex.Gammaℂ_def]
  have hpow := qs_ofReal_cpow_conj (2 * Real.pi) (by positivity) (-w)
  have hbase : ((2 * Real.pi : ℝ) : ℂ) = (2 : ℂ) * (Real.pi : ℂ) := by
    push_cast
    ring
  rw [hbase] at hpow
  have hpow' : (2 * (Real.pi : ℂ)) ^ (-conj w) =
      conj ((2 * (Real.pi : ℂ)) ^ (-w)) := by
    rw [show -conj w = conj (-w) by simp]
    exact hpow.symm
  rw [Complex.Gamma_conj]
  simp only [map_mul, map_ofNat]
  rw [hpow']

private lemma qs_prefactor_conj [IsTotallyComplex K] (w : ℂ) :
    Hecke.dedekindPrefactor K (conj w) =
      conj (Hecke.dedekindPrefactor K w) := by
  simp only [Hecke.dedekindPrefactor, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero,
    pow_zero, one_mul]
  change ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (conj w / 2) *
      Complex.Gammaℂ (conj w) ^ NumberField.InfinitePlace.nrComplexPlaces K =
    conj (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (w / 2) *
      Complex.Gammaℂ w ^ NumberField.InfinitePlace.nrComplexPlaces K)
  rw [map_mul, map_pow, qs_gammaC_conj]
  have hpow := qs_ofReal_cpow_conj |(NumberField.discr K : ℝ)| (abs_nonneg _) (w / 2)
  have hdiv : conj (w / 2) = conj w / 2 := by
    rw [map_div₀]
    rw [RCLike.conj_ofNat]
  rw [hdiv] at hpow
  rw [← hpow]

private lemma qs_gammaRatio_logDeriv_bound [IsTotallyComplex K] {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖logDeriv (fun w : ℂ => qsGammaRatio K w) z‖ ≤ C * Real.log (|z.im| + 2) := by
  obtain ⟨C₁, hC₁, hψ₁⟩ :=
    ArtinPrimitiveRoots.Ext.SplittingInputs.ext_digamma_strip (a := a) (b := b) ha
  have ha₂ : 0 < 1 - b := by linarith
  obtain ⟨C₂, hC₂, hψ₂⟩ :=
    ArtinPrimitiveRoots.Ext.SplittingInputs.ext_digamma_strip (a := 1 - b) (b := 1 - a) ha₂
  let n : ℂ := NumberField.InfinitePlace.nrComplexPlaces K
  let LD : ℂ := Complex.log ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  let LA : ℂ := Complex.log (2 * (Real.pi : ℂ))
  let B₀ : ℝ := ‖LD‖ + ‖n‖ * (2 * ‖LA‖)
  let B₁ : ℝ := ‖n‖ * (C₁ + C₂)
  let C : ℝ := B₀ / Real.log 2 + B₁ + 1
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro z hza hzb
    have hz0 : 0 < z.re := lt_of_lt_of_le ha hza
    have hz1 : z.re < 1 := lt_of_le_of_lt hzb hb
    have h1a : 1 - b ≤ (1 - z).re := by simp; linarith
    have h1b : (1 - z).re ≤ 1 - a := by simp; linarith
    have hLpos : 0 < Real.log (|z.im| + 2) := by
      apply Real.log_pos
      have : 0 ≤ |z.im| := abs_nonneg _
      linarith
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog2le : Real.log (2 : ℝ) ≤ Real.log (|z.im| + 2) := by
      apply Real.log_le_log (by norm_num)
      have : 0 ≤ |z.im| := abs_nonneg _
      linarith
    have hψz : ‖Complex.digamma z‖ ≤ C₁ * Real.log (|z.im| + 2) := by
      rw [Complex.digamma_def, logDeriv_apply]
      exact hψ₁ z hza hzb
    have hψ1z : ‖Complex.digamma (1 - z)‖ ≤ C₂ * Real.log (|z.im| + 2) := by
      rw [Complex.digamma_def, logDeriv_apply]
      simpa using hψ₂ (1 - z) h1a h1b
    rw [qs_gammaRatio_logDeriv z hz0 hz1]
    have hInner : ‖-2 * LA + Complex.digamma z + Complex.digamma (1 - z)‖ ≤
        2 * ‖LA‖ + (C₁ + C₂) * Real.log (|z.im| + 2) := by
      calc
        _ ≤ ‖-2 * LA + Complex.digamma z‖ + ‖Complex.digamma (1 - z)‖ := norm_add_le _ _
        _ ≤ (‖-2 * LA‖ + ‖Complex.digamma z‖) + ‖Complex.digamma (1 - z)‖ :=
          by have hnadd := norm_add_le (-2 * LA) (Complex.digamma z); linarith
        _ = 2 * ‖LA‖ + ‖Complex.digamma z‖ + ‖Complex.digamma (1 - z)‖ := by
          simp
        _ ≤ 2 * ‖LA‖ + C₁ * Real.log (|z.im| + 2) +
              C₂ * Real.log (|z.im| + 2) := by gcongr
        _ = 2 * ‖LA‖ + (C₁ + C₂) * Real.log (|z.im| + 2) := by ring
    have hn : 0 ≤ ‖n‖ := norm_nonneg _
    have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
    have hB₁ : 0 ≤ B₁ := by dsimp [B₁]; positivity
    have hconst : B₀ ≤ (B₀ / Real.log 2) * Real.log (|z.im| + 2) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hlog2).2
      nlinarith [mul_le_mul_of_nonneg_left hlog2le hB₀]
    calc
      ‖LD + n * (-2 * LA + Complex.digamma z + Complex.digamma (1 - z))‖
          ≤ ‖LD‖ + ‖n‖ * ‖-2 * LA + Complex.digamma z + Complex.digamma (1 - z)‖ := by
            calc
              _ ≤ ‖LD‖ + ‖n * (-2 * LA + Complex.digamma z + Complex.digamma (1 - z))‖ := norm_add_le _ _
              _ = _ := by simp [norm_mul]
      _ ≤ ‖LD‖ + ‖n‖ * (2 * ‖LA‖ + (C₁ + C₂) * Real.log (|z.im| + 2)) :=
          by have hmul := mul_le_mul_of_nonneg_left hInner hn; linarith
      _ = B₀ + B₁ * Real.log (|z.im| + 2) := by
          dsimp [B₀, B₁]
          ring
      _ ≤ C * Real.log (|z.im| + 2) := by
          dsimp [C]
          nlinarith [hconst, hLpos]

private lemma qs_gammaRatio_line_hasDerivAt [IsTotallyComplex K]
    (t x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y : ℝ => qsGammaRatio K ((y : ℂ) + (t : ℂ) * Complex.I))
      (deriv (fun w : ℂ => qsGammaRatio K w) ((x : ℂ) + (t : ℂ) * Complex.I)) x := by
  let z : ℂ := (x : ℂ) + (t : ℂ) * Complex.I
  have hzre : z.re = x := by simp [z]
  have hz0 : 0 < z.re := by rw [hzre]; exact hx0
  have hz1 : z.re < 1 := by rw [hzre]; exact hx1
  have hPz0 := qs_prefactor_nezero (K := K) z hz0
  have hP1z0 : Hecke.dedekindPrefactor K (1 - z) ≠ 0 := by
    apply qs_prefactor_nezero
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hPzDiff := qs_prefactor_differentiableAt (K := K) z hz0
  have hP1zDiff : DifferentiableAt ℂ (Hecke.dedekindPrefactor K) (1 - z) := by
    apply qs_prefactor_differentiableAt
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hOneSubDiff : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  have hdenDiff : DifferentiableAt ℂ
      (fun w : ℂ => Hecke.dedekindPrefactor K (1 - w)) z :=
    hP1zDiff.comp z hOneSubDiff
  have hRdiff : DifferentiableAt ℂ (fun w : ℂ => qsGammaRatio K w) z := by
    change DifferentiableAt ℂ
      (fun w : ℂ => Hecke.dedekindPrefactor K w /
        Hecke.dedekindPrefactor K (1 - w)) z
    exact hPzDiff.div hdenDiff hP1z0
  have hshift : HasDerivAt (fun w : ℂ => w + (t : ℂ) * Complex.I) 1 (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).add_const ((t : ℂ) * Complex.I)
  have hcomplex := hRdiff.hasDerivAt.comp (x : ℂ) hshift
  have hcomplex' : HasDerivAt (fun w : ℂ => qsGammaRatio K (w + (t : ℂ) * Complex.I))
      (deriv (fun w : ℂ => qsGammaRatio K w) z) (x : ℂ) := by
    simpa [Function.comp_def, z] using hcomplex
  simpa [z] using hcomplex'.comp_ofReal

private lemma qs_gammaRatio_center_norm [IsTotallyComplex K] (t : ℝ) :
    ‖qsGammaRatio K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ = 1 := by
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hzre : z.re = 1 / 2 := by simp [z]
  have hsymm : 1 - z = conj z := by
    apply Complex.ext
    · norm_num [z]
    · simp [z]
  have hPz0 : Hecke.dedekindPrefactor K z ≠ 0 := by
    apply qs_prefactor_nezero
    rw [hzre]
    norm_num
  change ‖Hecke.dedekindPrefactor K z /
      Hecke.dedekindPrefactor K (1 - z)‖ = 1
  rw [hsymm, qs_prefactor_conj, norm_div, RCLike.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hPz0)

private lemma qs_gammaRatio_polynomial_bound [IsTotallyComplex K] {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ p : ℝ, 0 < p ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖qsGammaRatio K z‖ ≤ (|z.im| + 2) ^ p := by
  let a₀ : ℝ := min a (1 / 2)
  let b₀ : ℝ := max b (1 / 2)
  have ha₀ : 0 < a₀ := lt_min ha (by norm_num)
  have hb₀ : b₀ < 1 := max_lt hb (by norm_num)
  have ha₀b₀ : a₀ ≤ b₀ := (min_le_left _ _).trans (hab.trans (le_max_left _ _))
  obtain ⟨C₀, hC₀, hlogR⟩ :=
    qs_gammaRatio_logDeriv_bound (K := K) ha₀ ha₀b₀ hb₀
  refine ⟨C₀, hC₀, ?_⟩
  intro z hza hzb
  let t : ℝ := z.im
  let sgn : ℝ := if (1 / 2 : ℝ) ≤ z.re then 1 else -1
  let d : ℝ := |z.re - 1 / 2|
  let path : ℝ → ℝ := fun u => 1 / 2 + sgn * u
  let f : ℝ → ℂ := fun u => qsGammaRatio K ((path u : ℂ) + (t : ℂ) * Complex.I)
  let f' : ℝ → ℂ := fun u =>
    deriv (fun w : ℂ => qsGammaRatio K w) ((path u : ℂ) + (t : ℂ) * Complex.I) * (sgn : ℂ)
  have hzpos : 0 < z.re := lt_of_lt_of_le ha hza
  have hzlt : z.re < 1 := lt_of_le_of_lt hzb hb
  have hzdecomp : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hLpos : 0 < Real.log (|t| + 2) := by
    apply Real.log_pos
    have : 0 ≤ |t| := abs_nonneg _
    linarith
  have hkpos : 0 < C₀ * Real.log (|t| + 2) := mul_pos hC₀ hLpos
  have hsNorm : ‖(sgn : ℂ)‖ = 1 := by
    dsimp [sgn]
    by_cases hh : (1 / 2 : ℝ) ≤ z.re
    · rw [if_pos hh]
      norm_num
    · rw [if_neg hh]
      norm_num
  have hd_nonneg : 0 ≤ d := abs_nonneg _
  have hd_le_one : d ≤ 1 := by
    dsimp [d]
    rw [abs_le]
    constructor <;> linarith
  have hpathStrip : ∀ u ∈ Set.Icc 0 d, a₀ ≤ path u ∧ path u ≤ b₀ := by
    intro u hu
    by_cases hh : (1 / 2 : ℝ) ≤ z.re
    · have hd : d = z.re - 1 / 2 := by
        dsimp [d]
        rw [abs_of_nonneg (sub_nonneg.mpr hh)]
      have hp : path u = 1 / 2 + u := by
        dsimp [path, sgn]
        rw [if_pos hh]
        ring
      constructor
      · rw [hp]
        exact (min_le_right a (1 / 2)).trans (by linarith [hu.1])
      · have hzb₀ : z.re ≤ b₀ := hzb.trans (le_max_left _ _)
        rw [hp]
        rw [hd] at hu
        linarith [hu.2, hzb₀]
    · have hh' : z.re < 1 / 2 := lt_of_not_ge hh
      have hd : d = 1 / 2 - z.re := by
        dsimp [d]
        rw [abs_of_neg (sub_neg.mpr hh')]
        ring
      have hp : path u = 1 / 2 - u := by
        dsimp [path, sgn]
        rw [if_neg hh]
        ring
      have haz₀ : a₀ ≤ z.re := (min_le_left _ _).trans hza
      constructor
      · rw [hp]
        have huD : u ≤ 1 / 2 - z.re := by
          have huD' := hu.2
          rw [hd] at huD'
          exact huD'
        linarith [huD, haz₀]
      · rw [hp]
        calc
          1 / 2 - u ≤ 1 / 2 := by linarith [hu.1]
          _ ≤ b₀ := le_max_right b (1 / 2)
  have hpathDeriv (u : ℝ) : HasDerivAt path sgn u := by
    have hmul : HasDerivAt (fun y : ℝ => sgn * y) sgn u := by
      simpa using (hasDerivAt_id u).const_mul sgn
    simpa [path, add_comm] using hmul.const_add (1 / 2)
  have hcont : ContinuousOn f (Set.Icc 0 d) := by
    apply continuousOn_of_forall_continuousAt
    intro u hu
    obtain ⟨hpa, hpb⟩ := hpathStrip u hu
    have hu0 : 0 < path u := lt_of_lt_of_le ha₀ hpa
    have hu1 : path u < 1 := lt_of_le_of_lt hpb hb₀
    have hcomp := HasDerivAt.scomp u
      (qs_gammaRatio_line_hasDerivAt (K := K) t (path u) hu0 hu1) (hpathDeriv u)
    have hcomp' : HasDerivAt f (f' u) u := by
      simpa [f, f', Function.comp_def, mul_comm] using hcomp
    exact hcomp'.continuousAt
  have hderiv : ∀ u ∈ Set.Ico 0 d,
      HasDerivWithinAt f (f' u) (Set.Ici u) u := by
    intro u hu
    have huIcc : u ∈ Set.Icc 0 d := ⟨hu.1, hu.2.le⟩
    obtain ⟨hpa, hpb⟩ := hpathStrip u huIcc
    have hu0 : 0 < path u := lt_of_lt_of_le ha₀ hpa
    have hu1 : path u < 1 := lt_of_le_of_lt hpb hb₀
    have hline := qs_gammaRatio_line_hasDerivAt (K := K) t (path u) hu0 hu1
    have hcomp := HasDerivAt.scomp u hline (hpathDeriv u)
    have hcomp' : HasDerivAt f (f' u) u := by
      simpa [f, f', Function.comp_def, mul_comm] using hcomp
    exact hcomp'.hasDerivWithinAt
  have hderivBound : ∀ u ∈ Set.Ico 0 d, ‖f' u‖ ≤ (C₀ * Real.log (|t| + 2)) * ‖f u‖ := by
    intro u hu
    have huIcc : u ∈ Set.Icc 0 d := ⟨hu.1, hu.2.le⟩
    obtain ⟨hpa, hpb⟩ := hpathStrip u huIcc
    let w : ℂ := (path u : ℂ) + (t : ℂ) * Complex.I
    have hwa : a₀ ≤ w.re := by simpa [w] using hpa
    have hwb : w.re ≤ b₀ := by simpa [w] using hpb
    have hw0 : 0 < w.re := lt_of_lt_of_le ha₀ hwa
    have hw1 : w.re < 1 := lt_of_le_of_lt hwb hb₀
    have hR0 : qsGammaRatio K w ≠ 0 := by
      unfold qsGammaRatio
      apply div_ne_zero
      · exact qs_prefactor_nezero w hw0
      · apply qs_prefactor_nezero
        simp only [Complex.sub_re, Complex.one_re]
        linarith
    have hlog := hlogR w hwa hwb
    have hlog' : ‖logDeriv (fun q : ℂ => qsGammaRatio K q) w‖ ≤
        C₀ * Real.log (|t| + 2) := by
      simpa [w] using hlog
    have hderivEq : deriv (fun q : ℂ => qsGammaRatio K q) w =
        logDeriv (fun q : ℂ => qsGammaRatio K q) w * qsGammaRatio K w := by
      rw [logDeriv_apply]
      field_simp [hR0]
    change ‖deriv (fun q : ℂ => qsGammaRatio K q) w * (sgn : ℂ)‖ ≤
      (C₀ * Real.log (|t| + 2)) * ‖qsGammaRatio K w‖
    rw [hderivEq, norm_mul, norm_mul, hsNorm, mul_one]
    exact mul_le_mul_of_nonneg_right hlog' (norm_nonneg _)
  have hinit : ‖f 0‖ ≤ 1 := by
    simpa [f, path] using (qs_gammaRatio_center_norm (K := K) t).le
  have hderivBound' : ∀ u ∈ Set.Ico 0 d,
      ‖f' u‖ ≤ (C₀ * Real.log (|t| + 2)) * ‖f u‖ + 0 := by
    intro u hu
    simpa using hderivBound u hu
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := f) (f' := f') (δ := 1) (K := C₀ * Real.log (|t| + 2)) (ε := 0)
    (a := 0) (b := d) hcont hderiv hinit hderivBound' d ⟨hd_nonneg, le_rfl⟩
  have hGexp : ‖f d‖ ≤ Real.exp ((C₀ * Real.log (|t| + 2)) * d) := by
    simpa [gronwallBound_ε0] using hG
  have hKnonneg : 0 ≤ C₀ * Real.log (|t| + 2) := le_of_lt hkpos
  have hexp : Real.exp ((C₀ * Real.log (|t| + 2)) * d) ≤
      Real.exp (C₀ * Real.log (|t| + 2)) := by
    apply Real.exp_le_exp.mpr
    simpa using mul_le_mul_of_nonneg_left hd_le_one hKnonneg
  have hbasepos : 0 < |z.im| + 2 := by positivity
  have hpowEq : Real.exp (C₀ * Real.log (|z.im| + 2)) = (|z.im| + 2) ^ C₀ := by
    rw [Real.rpow_def_of_pos hbasepos]
    congr 1
    ring
  have hendpoint : path d = z.re := by
    by_cases hh : (1 / 2 : ℝ) ≤ z.re
    · have hd : d = z.re - 1 / 2 := by
        dsimp [d]
        rw [abs_of_nonneg (sub_nonneg.mpr hh)]
      dsimp [path, sgn]
      rw [if_pos hh, hd]
      ring_nf
    · have hh' : z.re < 1 / 2 := lt_of_not_ge hh
      have hd : d = 1 / 2 - z.re := by
        dsimp [d]
        rw [abs_of_neg (sub_neg.mpr hh')]
        ring
      dsimp [path, sgn]
      rw [if_neg hh, hd]
      ring_nf
  have hzdecomp : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have htarget : f d = qsGammaRatio K z := by
    change qsGammaRatio K ((path d : ℂ) + (z.im : ℂ) * Complex.I) = qsGammaRatio K z
    have hpcast : (path d : ℂ) = (z.re : ℂ) := by exact_mod_cast hendpoint
    rw [hpcast, ← hzdecomp]
  have hbound := hGexp.trans (hexp.trans_eq hpowEq)
  calc
    ‖qsGammaRatio K z‖ = ‖f d‖ := by rw [htarget]
    _ ≤ (|z.im| + 2) ^ C₀ := hbound

private lemma qs_gammaRatio_polynomial_bound_right [IsTotallyComplex K] {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C p : ℝ, 0 < C ∧ 0 < p ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖qsGammaRatio K z‖ ≤ C * (|z.im| + 2) ^ p := by
  let a₀ : ℝ := min a (1 / 2)
  let b₀ : ℝ := max b (1 / 2)
  have ha₀ : 0 < a₀ := lt_min ha (by norm_num)
  have ha₀b₀ : a₀ ≤ b₀ :=
    (min_le_left _ _).trans (hab.trans (le_max_left _ _))
  obtain ⟨Cder, hCder, hlogR⟩ := qs_gammaRatio_logDeriv_bound_high (K := K) ha₀ ha₀b₀
  let Box : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1
  let zOfPair : ℝ × ℝ → ℂ := fun v => (v.1 : ℂ) + (v.2 : ℂ) * Complex.I
  have hBoxCompact : IsCompact Box := isCompact_Icc.prod isCompact_Icc
  have hLowCont : ContinuousOn (fun v : ℝ × ℝ => ‖qsGammaRatio K (zOfPair v)‖) Box := by
    apply continuousOn_of_forall_continuousAt
    intro v hv
    have hvre : 0 < (zOfPair v).re := by
      dsimp [zOfPair]
      simp
      exact lt_of_lt_of_le ha hv.1.1
    have hd := qs_gammaRatio_differentiableAt_right (K := K) (zOfPair v) hvre
    have hzcont : ContinuousAt zOfPair v := by fun_prop
    have hcomp := ContinuousAt.comp_of_eq hd.continuousAt hzcont (by rfl)
    simpa [Function.comp_def] using hcomp.norm
  obtain ⟨B, hB⟩ := hBoxCompact.bddAbove_image hLowCont
  have hBnd : ∀ y ∈ (fun v : ℝ × ℝ => ‖qsGammaRatio K (zOfPair v)‖) '' Box,
      y ≤ B := by
    change B ∈ upperBounds ((fun v : ℝ × ℝ => ‖qsGammaRatio K (zOfPair v)‖) '' Box) at hB
    exact hB
  let C₀ : ℝ := max B 1
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  let D₀ : ℝ := |a| + |b| + 1
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  have hHigh (z : ℂ) (hza : a ≤ z.re) (hzb : z.re ≤ b) (him : 1 ≤ |z.im|) :
      ‖qsGammaRatio K z‖ ≤ (|z.im| + 2) ^ (Cder * D₀) := by
    let t : ℝ := z.im
    let slope : ℝ := z.re - 1 / 2
    let path : ℝ → ℝ := fun u => 1 / 2 + slope * u
    let f : ℝ → ℂ := fun u => qsGammaRatio K ((path u : ℂ) + (t : ℂ) * Complex.I)
    let f' : ℝ → ℂ := fun u =>
      deriv (fun w : ℂ => qsGammaRatio K w) ((path u : ℂ) + (t : ℂ) * Complex.I) *
        (slope : ℂ)
    have hpathEq (u : ℝ) : path u = 1 / 2 + (z.re - 1 / 2) * u := by
      dsimp [path, slope]
    have hpathStrip : ∀ u ∈ Set.Icc (0 : ℝ) 1, a₀ ≤ path u ∧ path u ≤ b₀ := by
      intro u hu
      by_cases hmid : (1 / 2 : ℝ) ≤ z.re
      · have hprodlo : 0 ≤ (z.re - 1 / 2) * u :=
          mul_nonneg (sub_nonneg.mpr hmid) hu.1
        have hprodhi : (z.re - 1 / 2) * u ≤ z.re - 1 / 2 :=
          by simpa only [mul_one] using mul_le_mul_of_nonneg_left hu.2 (sub_nonneg.mpr hmid)
        have haMid : a₀ ≤ 1 / 2 := min_le_right _ _
        have hbEnd : z.re ≤ b₀ := le_trans hzb (le_max_left _ _)
        constructor
        · rw [hpathEq]
          linarith
        · rw [hpathEq]
          linarith
      · have hmid' : z.re < 1 / 2 := lt_of_not_ge hmid
        have hstep : 0 ≤ 1 / 2 - z.re := by linarith
        have hprodlo : 0 ≤ (1 / 2 - z.re) * u :=
          mul_nonneg hstep hu.1
        have hprodhi : (1 / 2 - z.re) * u ≤ 1 / 2 - z.re :=
          by simpa only [mul_one] using mul_le_mul_of_nonneg_left hu.2 hstep
        have haEnd : a₀ ≤ z.re := le_trans (min_le_left _ _) hza
        have hbMid : (1 / 2 : ℝ) ≤ b₀ := le_max_right _ _
        constructor
        · rw [hpathEq]
          linarith
        · rw [hpathEq]
          linarith
    have hpathDeriv (u : ℝ) : HasDerivAt path slope u := by
      have hmul : HasDerivAt (fun v : ℝ => slope * v) slope u := by
        simpa using (hasDerivAt_id u).const_mul slope
      simpa [path, slope, add_comm] using hmul.const_add (1 / 2)
    have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
      apply continuousOn_of_forall_continuousAt
      intro u hu
      obtain ⟨hpa, _hpb⟩ := hpathStrip u hu
      have hu0 : 0 < path u := lt_of_lt_of_le ha₀ hpa
      have hw : ((path u : ℂ) + (t : ℂ) * Complex.I).re > 0 := by simpa using hu0
      have hd := qs_gammaRatio_differentiableAt_right (K := K)
        ((path u : ℂ) + (t : ℂ) * Complex.I) hw
      have harg : ContinuousAt (fun v : ℝ =>
          (path v : ℂ) + (t : ℂ) * Complex.I) u := by fun_prop
      have hcomp := ContinuousAt.comp_of_eq hd.continuousAt harg (by rfl)
      simpa [f, Function.comp_def] using hcomp
    have hderiv : ∀ u ∈ Set.Ico (0 : ℝ) 1,
        HasDerivWithinAt f (f' u) (Set.Ici u) u := by
      intro u hu
      obtain ⟨hpa, _hpb⟩ := hpathStrip u ⟨hu.1, hu.2.le⟩
      have hu0 : 0 < path u := lt_of_lt_of_le ha₀ hpa
      let w : ℂ := (path u : ℂ) + (t : ℂ) * Complex.I
      have hargDeriv : HasDerivAt
          (fun v : ℝ => (path v : ℂ) + (t : ℂ) * Complex.I) (slope : ℂ) u := by
        simpa [add_comm] using (hpathDeriv u).ofReal_comp.const_add ((t : ℂ) * Complex.I)
      have houter := (qs_gammaRatio_differentiableAt_right (K := K) w
        (by simpa [w] using hu0)).hasDerivAt
      have hcomp := HasDerivAt.scomp u houter hargDeriv
      have hcomp' : HasDerivAt f (f' u) u := by
        simpa [f, f', w, Function.comp_def, mul_comm] using hcomp
      exact hcomp'.hasDerivWithinAt
    have hSlopeBound : |slope| ≤ D₀ := by
      have hreAbs : |z.re| ≤ |a| + |b| := by
        rw [abs_le]
        constructor
        · have := neg_abs_le a
          linarith [hza, abs_nonneg b]
        · have := le_abs_self b
          linarith [hzb, abs_nonneg a]
      calc
        |slope| = |z.re + (-1 / 2)| := by dsimp [slope]; congr 1 <;> ring
        _ ≤ |z.re| + |-1 / 2| := abs_add_le _ _
        _ ≤ |a| + |b| + 1 / 2 := by
          have hhalf : abs (-1 / 2 : ℝ) = 1 / 2 := by norm_num
          rw [hhalf]
          linarith [hreAbs]
        _ ≤ D₀ := by dsimp [D₀]; linarith
    have hinit : ‖f 0‖ ≤ 1 := by
      simpa [f, path] using (qs_gammaRatio_center_norm (K := K) t).le
    have hderivBound : ∀ u ∈ Set.Ico (0 : ℝ) 1,
        ‖f' u‖ ≤ (Cder * D₀ * Real.log (|t| + 2)) * ‖f u‖ := by
      intro u hu
      obtain ⟨hpa, hpb⟩ := hpathStrip u ⟨hu.1, hu.2.le⟩
      have hu0 : 0 < path u := lt_of_lt_of_le ha₀ hpa
      let w : ℂ := (path u : ℂ) + (t : ℂ) * Complex.I
      have ht0 : z.im ≠ 0 := by
        intro h
        rw [h] at him
        norm_num at him
      have hwa : a₀ ≤ w.re := by simpa [w] using hpa
      have hwb : w.re ≤ b₀ := by simpa [w] using hpb
      have hwim' : w.im = t := by simp [w]
      have hwim : |w.im| = |t| := by rw [hwim']
      have hlog := hlogR w hwa hwb (by rw [hwim]; exact him)
      have hR0 : qsGammaRatio K w ≠ 0 := by
        unfold qsGammaRatio
        apply div_ne_zero
        · exact qs_prefactor_nezero w (by simpa [w] using hu0)
        · have hwi : (1 - w).im ≠ 0 := by
            rw [show (1 - w).im = -w.im by simp, hwim']
            exact neg_ne_zero.mpr (by dsimp [t]; exact ht0)
          exact qs_prefactor_nezero_of_im (1 - w) hwi
      have hderivEq : deriv (fun q : ℂ => qsGammaRatio K q) w =
          logDeriv (fun q : ℂ => qsGammaRatio K q) w * qsGammaRatio K w := by
        rw [logDeriv_apply]
        field_simp [hR0]
      have hlog' : ‖logDeriv (fun q : ℂ => qsGammaRatio K q) w‖ ≤
          Cder * Real.log (|t| + 2) := by simpa [w, hwim] using hlog
      have hslope : ‖(slope : ℂ)‖ ≤ D₀ := by
        simpa using hSlopeBound
      change ‖deriv (fun q : ℂ => qsGammaRatio K q) w * (slope : ℂ)‖ ≤
        (Cder * D₀ * Real.log (|t| + 2)) * ‖qsGammaRatio K w‖
      rw [hderivEq, norm_mul, norm_mul]
      calc
        ‖logDeriv (fun q : ℂ => qsGammaRatio K q) w‖ *
            ‖qsGammaRatio K w‖ * ‖(slope : ℂ)‖ ≤
            (Cder * Real.log (|t| + 2)) * ‖qsGammaRatio K w‖ * D₀ := by
              calc
                _ ≤ (Cder * Real.log (|t| + 2) * ‖qsGammaRatio K w‖) *
                    ‖(slope : ℂ)‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hlog' (norm_nonneg _)) (norm_nonneg _)
                _ ≤ (Cder * Real.log (|t| + 2) * ‖qsGammaRatio K w‖) * D₀ :=
                  mul_le_mul_of_nonneg_left hslope (by
                    exact mul_nonneg (mul_nonneg (le_of_lt hCder)
                      (Real.log_nonneg (by linarith [him]))) (norm_nonneg _))
                _ = (Cder * Real.log (|t| + 2)) * ‖qsGammaRatio K w‖ * D₀ := by ring
        _ = (Cder * D₀ * Real.log (|t| + 2)) * ‖qsGammaRatio K w‖ := by ring
    have hderivBound' : ∀ u ∈ Set.Ico (0 : ℝ) 1,
        ‖f' u‖ ≤ (Cder * D₀ * Real.log (|t| + 2)) * ‖f u‖ + 0 := by
      intro u hu
      simpa using hderivBound u hu
    have hG := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := f) (f' := f') (δ := 1) (K := Cder * D₀ * Real.log (|t| + 2)) (ε := 0)
      (a := 0) (b := 1) hcont hderiv hinit hderivBound' 1 (by norm_num)
    have hGexp : ‖f 1‖ ≤ Real.exp (Cder * D₀ * Real.log (|t| + 2)) := by
      simpa [gronwallBound_ε0] using hG
    have hbasepos : 0 < |t| + 2 := by positivity
    have hpowEq : Real.exp (Cder * D₀ * Real.log (|t| + 2)) =
        (|t| + 2) ^ (Cder * D₀) := by
      rw [Real.rpow_def_of_pos hbasepos]
      congr 1
      ring
    have htarget : f 1 = qsGammaRatio K z := by
      change qsGammaRatio K ((path 1 : ℂ) + (t : ℂ) * Complex.I) = qsGammaRatio K z
      have hpath1 : path 1 = z.re := by dsimp [path, slope]; ring
      rw [hpath1]
      have ht : (t : ℂ) = (z.im : ℝ) := by simp [t]
      have hzdecomp : z = (z.re : ℂ) + (z.im : ℝ) * Complex.I := by
        apply Complex.ext <;> simp
      calc
        qsGammaRatio K ((z.re : ℂ) + (t : ℂ) * Complex.I) =
            qsGammaRatio K ((z.re : ℂ) + (z.im : ℝ) * Complex.I) := by rw [ht]
        _ = qsGammaRatio K z := by rw [← hzdecomp]
    calc
      ‖qsGammaRatio K z‖ = ‖f 1‖ := by rw [htarget]
      _ ≤ Real.exp (Cder * D₀ * Real.log (|t| + 2)) := hGexp
      _ = (|z.im| + 2) ^ (Cder * D₀) := by simpa [t] using hpowEq
  let pHigh : ℝ := Cder * D₀
  let p : ℝ := max pHigh 1
  let C : ℝ := C₀ + 1
  have hpHigh : 0 < pHigh := mul_pos hCder hD₀
  have hp : 0 < p := by dsimp [p]; positivity
  have hC : 0 < C := by dsimp [C]; linarith [hC₀]
  refine ⟨C, p, hC, hp, ?_⟩
  intro z hza hzb
  by_cases him : |z.im| ≤ 1
  · have hpairs : (z.re, z.im) ∈ Box := by
      constructor
      · exact ⟨hza, hzb⟩
      · rw [Set.mem_Icc]
        exact abs_le.mp him
    let pair : ℝ × ℝ := (z.re, z.im)
    have hzpair : zOfPair pair = z := by
      apply Complex.ext <;> simp [zOfPair, pair]
    have hlow' : ‖qsGammaRatio K (zOfPair pair)‖ ≤ B :=
      hBnd _ ⟨pair, by simpa [Box, pair] using hpairs, rfl⟩
    have hlow : ‖qsGammaRatio K z‖ ≤ B := by simpa [hzpair] using hlow'
    have hbase : 1 ≤ |z.im| + 2 := by have := abs_nonneg z.im; linarith
    have hpow : 1 ≤ (|z.im| + 2) ^ p := by
      calc
        1 = (|z.im| + 2) ^ (0 : ℝ) := by simp
        _ ≤ (|z.im| + 2) ^ p := Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    calc
      ‖qsGammaRatio K z‖ ≤ B := by
        simpa [pair, hzpair] using hlow
      _ ≤ C * (|z.im| + 2) ^ p := by
        dsimp [C]
        have hB0 : B ≤ C₀ := le_max_left _ _
        have hbasePow : 0 ≤ (|z.im| + 2) ^ p := Real.rpow_nonneg (by positivity) _
        calc
          B ≤ C₀ := hB0
          _ ≤ C₀ * (|z.im| + 2) ^ p := by
            simpa using mul_le_mul_of_nonneg_left hpow (le_of_lt hC₀)
          _ ≤ (C₀ + 1) * (|z.im| + 2) ^ p := by
            rw [add_mul, one_mul]
            exact le_add_of_nonneg_right hbasePow
  · have him' : 1 ≤ |z.im| := by linarith
    have hh := hHigh z hza hzb him'
    have hpowMono : (|z.im| + 2) ^ pHigh ≤ (|z.im| + 2) ^ p :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (le_max_left _ _)
    calc
      ‖qsGammaRatio K z‖ ≤ (|z.im| + 2) ^ pHigh := hh
      _ ≤ (|z.im| + 2) ^ p := hpowMono
      _ ≤ C * (|z.im| + 2) ^ p := by
        dsimp [C]
        have hpbase : 0 ≤ (|z.im| + 2) ^ p := Real.rpow_nonneg (by positivity) _
        nlinarith [hC₀, hpbase]

private lemma qsMellinTransformLine_tail_bound [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ |y| →
      ‖qsMellinTransformLine K h y‖ ≤ C / |y| ^ m := by
  obtain ⟨p, hp, hQ⟩ :=
    qs_gammaRatio_polynomial_bound (K := K) (a := 1 / 2) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (p + m + 1)
  obtain ⟨Cm, hCm, hM⟩ := qs_mellin_vertical_decay h hh (by norm_num : 0 < (1 / 2 : ℝ)) N
  let A : ℝ := 2 * Real.pi + 2
  let C : ℝ := Cm * A ^ p + 1
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [Real.pi_gt_three]
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro y hy
  let t : ℝ := 2 * Real.pi * y
  let u : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have htAbs : |t| = 2 * Real.pi * |y| := by
    dsimp [t]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hbase : |t| + 2 ≤ A * |y| := by
    rw [htAbs]
    dsimp [A]
    nlinarith [hy]
  have huRe : u.re = 1 / 2 := by simp [u]
  have huIm : u.im = t := by simp [u]
  have hgamma : ‖qsGammaRatio K u‖ ≤ A ^ p * |y| ^ p := by
    have hgamma' := hQ u (by simpa [huRe]) (by simpa [huRe])
    have hbasepos : 0 ≤ |t| + 2 := by positivity
    calc
      ‖qsGammaRatio K u‖ ≤ (|t| + 2) ^ p := by simpa [huIm] using hgamma'
      _ ≤ (A * |y|) ^ p := Real.rpow_le_rpow hbasepos hbase hp.le
      _ = A ^ p * |y| ^ p := Real.mul_rpow (by positivity) (abs_nonneg _)
  have hMellin : ‖mellin h ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)‖ ≤ Cm / |y| ^ N := by
    have hMneg := hM (-t)
    have hden : |y| ≤ |-t| + 1 := by
      rw [abs_neg, htAbs]
      nlinarith [Real.pi_gt_three, hy]
    have hdenpow : |y| ^ N ≤ (|-t| + 1) ^ N := pow_le_pow_left₀ (abs_nonneg _) hden N
    have hypos : 0 < |y| ^ N := pow_pos (lt_of_lt_of_le zero_lt_one hy) _
    have hM' : ‖mellin h ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)‖ ≤
        Cm / (|-t| + 1) ^ N := by
      have harg : ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
          (1 / 2 : ℂ) - (t : ℂ) * Complex.I := by push_cast; ring
      rw [harg] at hMneg
      exact hMneg
    calc
      ‖mellin h ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)‖ ≤ Cm / (|-t| + 1) ^ N := hM'
      _ ≤ Cm / |y| ^ N := (div_le_div_iff₀ (pow_pos (by positivity) _) hypos).2 <| by
          exact mul_le_mul_of_nonneg_left hdenpow hCm.le
  have hprod : ‖qsMellinTransformLine K h y‖ ≤ Cm * A ^ p * |y| ^ (p - N) := by
    rw [qsMellinTransformLine, norm_mul]
    calc
      ‖qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I)‖ *
          ‖mellin h ((1 / 2 : ℂ) - (2 * Real.pi * y : ℝ) * Complex.I)‖
        ≤ (A ^ p * |y| ^ p) * (Cm / |y| ^ N) := by
          exact mul_le_mul hgamma hMellin (norm_nonneg _) (by positivity)
      _ = Cm * A ^ p * |y| ^ (p - N) := by
          rw [Real.rpow_sub (by positivity) p (N : ℝ), Real.rpow_natCast]
          field_simp
  have hpow : |y| ^ (p - N) ≤ |y| ^ (-(m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [hy]) (by linarith [hN])
  have htail : ‖qsMellinTransformLine K h y‖ ≤ Cm * A ^ p * |y| ^ (-(m : ℝ)) :=
    hprod.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hEq : |y| ^ (-(m : ℝ)) = 1 / |y| ^ m := by
    rw [Real.rpow_neg]
    simp
    positivity
  calc
    ‖qsMellinTransformLine K h y‖ ≤ Cm * A ^ p * |y| ^ (-(m : ℝ)) := htail
    _ = Cm * A ^ p / |y| ^ m := by rw [hEq]; ring
    _ ≤ C / |y| ^ m := by
      apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ |y| ^ m)
      dsimp [C]
      exact le_add_of_nonneg_right (by norm_num)

set_option maxHeartbeats 10000000 in
private lemma qs_mellin_transform_line_integrable [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) :
    Integrable (qsMellinTransformLine K h) := by
  let q : ℝ → ℂ := qsLogMellinWeight h (1 / 2)
  have hqCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q :=
    qsLogMellinWeight_contDiff h (1 / 2) hh
  have hqInt : ∀ n : ℕ, Integrable (iteratedDeriv n q) :=
    fun n => qsLogMellinWeight_iteratedDeriv_integrable h (1 / 2) (by norm_num) hh n
  have hq0 : Integrable q := by simpa [q] using hqInt 0
  have hqFourierCont : Continuous (𝓕 q) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) q)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hq0
  have hlineMellin (y : ℝ) :
      mellin h ((1 / 2 : ℂ) - (2 * Real.pi * y : ℝ) * Complex.I) = 𝓕 q (-y) := by
    have hFour := qs_mellin_log_fourier h (1 / 2) (-2 * Real.pi * y)
    have hfreq : (-2 * Real.pi * y) / (2 * Real.pi) = -y := by
      field_simp [Real.pi_ne_zero]
    have hFour' : mellin h ((1 / 2 : ℂ) + (-2 * Real.pi * y : ℝ) * Complex.I) =
        𝓕 q (-y) := by
      calc
        mellin h ((1 / 2 : ℂ) + (-2 * Real.pi * y : ℝ) * Complex.I) =
            𝓕 q ((-2 * Real.pi * y) / (2 * Real.pi)) := by
              simpa [q] using hFour
        _ = 𝓕 q (-y) := by rw [hfreq]
    simpa [sub_eq_add_neg, mul_neg] using hFour'
  have hRatioCont : Continuous
      (fun y : ℝ => qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    let z : ℂ := (1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I
    have hzre : z.re = 1 / 2 := by simp [z]
    have hdiff := qs_gammaRatio_differentiableAt (K := K) z (by rw [hzre]; norm_num)
      (by rw [hzre]; norm_num)
    have hline : ContinuousAt (fun y : ℝ =>
        (1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) y := by fun_prop
    have hcomp := ContinuousAt.comp_of_eq hdiff.continuousAt hline (by rfl)
    simpa [Function.comp_def, z] using hcomp
  have hFdef : (qsMellinTransformLine K h) = fun y : ℝ =>
      qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) * 𝓕 q (-y) := by
    funext y
    rw [qsMellinTransformLine, hlineMellin y]
  have hFcont : Continuous (qsMellinTransformLine K h) := by
    rw [hFdef]
    exact hRatioCont.mul (hqFourierCont.comp continuous_neg)
  obtain ⟨C, hC, htail⟩ := qsMellinTransformLine_tail_bound (K := K) h hh 2
  have hOtop : qsMellinTransformLine K h =O[atTop] (fun y : ℝ => y ^ (-2 : ℝ)) := by
    rw [Asymptotics.isBigO_iff_isBigOWith]
    refine ⟨C, ?_⟩
    rw [Asymptotics.isBigOWith_iff]
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hAbs : |y| = y := abs_of_nonneg (by linarith)
    have hy' : 1 ≤ |y| := by rw [hAbs]; exact hy
    have htail' := htail y hy'
    simpa [hAbs, Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv] using htail'
  have hObot : qsMellinTransformLine K h =O[atBot] (fun y : ℝ => (-y) ^ (-2 : ℝ)) := by
    rw [Asymptotics.isBigO_iff_isBigOWith]
    refine ⟨C, ?_⟩
    rw [Asymptotics.isBigOWith_iff]
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with y hy
    have hAbs : |y| = -y := abs_of_nonpos (by linarith)
    have hy' : 1 ≤ |y| := by rw [hAbs]; linarith
    have htail' := htail y hy'
    simpa [hAbs, Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv] using htail'
  have hpowTop : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (c := 1) zero_lt_one
  have hpowBot : IntegrableOn (fun y : ℝ => (-y) ^ (-2 : ℝ)) (Set.Iio (-1)) := by
    let g : ℝ → ℝ := fun y => (-y) ^ (-2 : ℝ)
    have hImage : Neg.neg '' Set.Ioi (1 : ℝ) = Set.Iio (-1) := by
      ext y
      simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio, neg_neg]
      constructor
      · rintro ⟨x, hx, rfl⟩
        linarith
      · intro hy
        exact ⟨-y, by linarith, by simp⟩
    have hNegDeriv : ∀ x ∈ Set.Ioi (1 : ℝ),
        HasDerivWithinAt (fun x : ℝ => -x) (-1) (Set.Ioi 1) x := by
      intro x hx
      exact (hasDerivAt_neg x).hasDerivWithinAt
    have hNegInj : Set.InjOn (fun x : ℝ => -x) (Set.Ioi 1) := by
      intro x hx y hy hxy
      exact neg_injective hxy
    rw [← hImage]
    apply (integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hNegDeriv hNegInj g).2
    simpa [g] using hpowTop
  have hAtTop : IntegrableAtFilter (fun y : ℝ => y ^ (-2 : ℝ)) atTop volume :=
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, hpowTop⟩
  have hAtBot : IntegrableAtFilter (fun y : ℝ => (-y) ^ (-2 : ℝ)) atBot volume :=
    ⟨Set.Iio (-1), Iio_mem_atBot (-1), hpowBot⟩
  exact hFcont.locallyIntegrable.integrable_of_isBigO_atBot_atTop hObot hAtBot hOtop hAtTop

private lemma qs_mellin_transform_line_moment_integrable [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (n : ℕ) :
    Integrable (fun y : ℝ => |y| ^ n * ‖qsMellinTransformLine K h y‖) := by
  let q : ℝ → ℂ := qsLogMellinWeight h (1 / 2)
  have hq0 : Integrable q := by
    simpa [q] using
      (qsLogMellinWeight_iteratedDeriv_integrable h (1 / 2) (by norm_num) hh 0)
  have hqFourierCont : Continuous (𝓕 q) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) q)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hq0
  have hlineMellin (y : ℝ) :
      mellin h ((1 / 2 : ℂ) - (2 * Real.pi * y : ℝ) * Complex.I) = 𝓕 q (-y) := by
    have hFour := qs_mellin_log_fourier h (1 / 2) (-2 * Real.pi * y)
    have hfreq : (-2 * Real.pi * y) / (2 * Real.pi) = -y := by field_simp [Real.pi_ne_zero]
    have hFour' : mellin h ((1 / 2 : ℂ) + (-2 * Real.pi * y : ℝ) * Complex.I) = 𝓕 q (-y) := by
      calc
        mellin h ((1 / 2 : ℂ) + (-2 * Real.pi * y : ℝ) * Complex.I) =
            𝓕 q ((-2 * Real.pi * y) / (2 * Real.pi)) := by simpa [q] using hFour
        _ = 𝓕 q (-y) := by rw [hfreq]
    simpa [sub_eq_add_neg, mul_neg] using hFour'
  have hratioCont : Continuous
      (fun y : ℝ => qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    let z : ℂ := (1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I
    have hzre : z.re = 1 / 2 := by simp [z]
    have hdiff := qs_gammaRatio_differentiableAt (K := K) z (by rw [hzre]; norm_num)
      (by rw [hzre]; norm_num)
    have hline : ContinuousAt (fun y : ℝ =>
        (1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) y := by fun_prop
    have hcomp := ContinuousAt.comp_of_eq hdiff.continuousAt hline (by rfl)
    simpa [Function.comp_def, z] using hcomp
  have hFdef : qsMellinTransformLine K h = fun y : ℝ =>
      qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) * 𝓕 q (-y) := by
    funext y
    rw [qsMellinTransformLine, hlineMellin y]
  have hFcont : Continuous (qsMellinTransformLine K h) := by
    rw [hFdef]
    exact hratioCont.mul (hqFourierCont.comp continuous_neg)
  obtain ⟨C, hC, htail⟩ := qsMellinTransformLine_tail_bound (K := K) h hh (n + 2)
  let g : ℝ → ℝ := fun y => |y| ^ n * ‖qsMellinTransformLine K h y‖
  have hgcont : Continuous g := by
    dsimp [g]
    exact (continuous_abs.pow n).mul (hFcont.norm)
  have hOtop : g =O[atTop] (fun y : ℝ => y ^ (-2 : ℝ)) := by
    rw [Asymptotics.isBigO_iff_isBigOWith]
    refine ⟨C, ?_⟩
    rw [Asymptotics.isBigOWith_iff]
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
    have hAbs : |y| = y := abs_of_nonneg hypos.le
    have htail' := htail y (by rw [hAbs]; exact hy)
    have hmul : |y| ^ n * ‖qsMellinTransformLine K h y‖ ≤ C / |y| ^ 2 := by
      calc
        |y| ^ n * ‖qsMellinTransformLine K h y‖ ≤
            |y| ^ n * (C / |y| ^ (n + 2)) :=
          mul_le_mul_of_nonneg_left htail' (by positivity)
        _ = C / |y| ^ 2 := by
          rw [div_eq_mul_inv, pow_add]
          field_simp [ne_of_gt (abs_pos.mpr (ne_of_gt hypos))]
    simpa [g, hAbs, Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv] using hmul
  have hObot : g =O[atBot] (fun y : ℝ => (-y) ^ (-2 : ℝ)) := by
    rw [Asymptotics.isBigO_iff_isBigOWith]
    refine ⟨C, ?_⟩
    rw [Asymptotics.isBigOWith_iff]
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with y hy
    have hAbs : |y| = -y := abs_of_nonpos (by linarith)
    have htail' := htail y (by rw [hAbs]; linarith)
    have hmul : |y| ^ n * ‖qsMellinTransformLine K h y‖ ≤ C / |y| ^ 2 := by
      calc
        |y| ^ n * ‖qsMellinTransformLine K h y‖ ≤
            |y| ^ n * (C / |y| ^ (n + 2)) :=
          mul_le_mul_of_nonneg_left htail' (by positivity)
        _ = C / |y| ^ 2 := by
          rw [div_eq_mul_inv, pow_add]
          have hAbsPos : 0 < |y| := by rw [hAbs]; linarith
          field_simp [ne_of_gt hAbsPos]
    simpa [g, hAbs, Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv] using hmul
  have hpowTop : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (c := 1) zero_lt_one
  have hpowBot : IntegrableOn (fun y : ℝ => (-y) ^ (-2 : ℝ)) (Set.Iio (-1)) := by
    let g' : ℝ → ℝ := fun y => (-y) ^ (-2 : ℝ)
    have hImage : Neg.neg '' Set.Ioi (1 : ℝ) = Set.Iio (-1) := by
      ext y
      simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio, neg_neg]
      constructor
      · rintro ⟨x, hx, rfl⟩; linarith
      · intro hy; exact ⟨-y, by linarith, by simp⟩
    have hNegDeriv : ∀ x ∈ Set.Ioi (1 : ℝ),
        HasDerivWithinAt (fun x : ℝ => -x) (-1) (Set.Ioi 1) x := by
      intro x hx; exact (hasDerivAt_neg x).hasDerivWithinAt
    have hNegInj : Set.InjOn (fun x : ℝ => -x) (Set.Ioi 1) := by
      intro x hx y hy hxy; exact neg_injective hxy
    rw [← hImage]
    apply (integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hNegDeriv hNegInj g').2
    simpa [g'] using hpowTop
  have hAtTop : IntegrableAtFilter (fun y : ℝ => y ^ (-2 : ℝ)) atTop volume :=
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, hpowTop⟩
  have hAtBot : IntegrableAtFilter (fun y : ℝ => (-y) ^ (-2 : ℝ)) atBot volume :=
    ⟨Set.Iio (-1), Iio_mem_atBot (-1), hpowBot⟩
  exact hgcont.locallyIntegrable.integrable_of_isBigO_atBot_atTop hObot hAtBot hOtop hAtTop

private lemma qs_iteratedDeriv_isQSWeight (h : ℝ → ℂ) (hh : IsQSWeight h)
    (n : ℕ) (hn : 0 < n) : IsQSWeight (iteratedDeriv n h) ∧ iteratedDeriv n h 0 = 0 := by
  rcases hh with ⟨hhSmooth, ⟨B, hB⟩, ⟨δ, hδ, hconst⟩⟩
  let fN : ℝ → ℂ := iteratedDeriv n h
  have hSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fN := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro m hm
    have hmn : (↑(m + n) : WithTop ℕ∞) < ↑(⊤ : ℕ∞) :=
      WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top (m + n))
    have hdm := hhSmooth.differentiable_iteratedDeriv (m + n) hmn
    convert hdm using 1
    simp [fN, iteratedDeriv_eq_iterate, Function.iterate_add_apply]
  have hZeroOn : Set.EqOn h (fun _ : ℝ => (0 : ℂ)) (Set.Ioi B) := by
    intro x hx
    exact hB x hx.le
  have hTopZero : ∀ x : ℝ, B + 1 ≤ x → fN x = 0 := by
    intro x hx
    have hx' : x ∈ Set.Ioi B := by change B < x; linarith
    have hderiv := hZeroOn.iteratedDeriv_of_isOpen isOpen_Ioi n hx'
    simpa [fN, hn] using hderiv
  have hConstOn : Set.EqOn h (fun _ : ℝ => h 0) (Set.Ioo 0 δ) := by
    intro x hx
    exact hconst x ⟨le_of_lt hx.1, hx.2.le⟩
  have hNearZero : ∀ x ∈ Set.Ioo 0 δ, fN x = 0 := by
    intro x hx
    have hderiv := hConstOn.iteratedDeriv_of_isOpen isOpen_Ioo n hx
    rw [iteratedDeriv_const, if_neg (Nat.ne_of_gt hn)] at hderiv
    simpa [fN] using hderiv
  have hNcont : Continuous fN := by
    simpa [fN] using hhSmooth.continuous_iteratedDeriv n (by simp)
  have hRightZero : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), fN x = 0 := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
    exact hNearZero x hx
  have hNzero : fN 0 = 0 := by
    have hlim₁ : Tendsto fN (𝓝[>] (0 : ℝ)) (𝓝 (fN 0)) :=
      hNcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim₂ : Tendsto fN (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      have hRightEq : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)] fN := by
        filter_upwards [hRightZero] with x hx
        exact hx.symm
      exact tendsto_const_nhds.congr' hRightEq
    exact tendsto_nhds_unique hlim₁ hlim₂
  have hQS : IsQSWeight fN := by
    refine ⟨hSmooth, ⟨B + 1, hTopZero⟩, ⟨δ / 2, by linarith, ?_⟩⟩
    intro x hx
    have hx' : x = 0 ∨ x ∈ Set.Ioo 0 δ := by
      by_cases h0 : x = 0
      · exact Or.inl h0
      · right
        constructor
        · exact lt_of_le_of_ne hx.1 (Ne.symm h0)
        · exact lt_of_le_of_lt hx.2 (by linarith)
    rcases hx' with h0 | hpos
    · simpa [h0] using hNzero.symm
    · calc
        fN x = 0 := hNearZero x hpos
        _ = fN 0 := hNzero.symm
  exact ⟨hQS, hNzero⟩

private lemma qs_x_mul_iteratedDeriv_isQSWeight (h : ℝ → ℂ) (hh : IsQSWeight h)
    (n : ℕ) (hn : 0 < n) :
    IsQSWeight (fun x : ℝ => (x : ℂ) * iteratedDeriv n h x) := by
  obtain ⟨hNQS, hNzero⟩ := qs_iteratedDeriv_isQSWeight h hh n hn
  rcases hNQS with ⟨hNsmooth, ⟨B, hB⟩, ⟨δ, hδ, hconst⟩⟩
  let fN : ℝ → ℂ := iteratedDeriv n h
  let g : ℝ → ℂ := fun x => (x : ℂ) * fN x
  have hNzero' : fN 0 = 0 := by simpa [fN] using hNzero
  have hgSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    have hid : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => (x : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_id
    exact hid.mul hNsmooth
  have hgTop : ∀ x : ℝ, B ≤ x → g x = 0 := by
    intro x hx
    have hfx : fN x = 0 := by simpa [fN] using hB x hx
    simp [g, fN, hfx]
  have hgNear : ∀ x ∈ Set.Icc (0 : ℝ) δ, g x = g 0 := by
    intro x hx
    have hfx : fN x = 0 := by
      have h := hconst x hx
      change fN x = fN 0 at h
      rw [h, hNzero']
    simp [g, fN, hfx, hNzero']
  exact ⟨hgSmooth, ⟨B, hgTop⟩, ⟨δ, hδ, hgNear⟩⟩

private lemma qs_mellin_convergent_of_QS (f : ℝ → ℂ) (hf : IsQSWeight f)
    (s : ℂ) (hs : 0 < s.re) : MellinConvergent f s := by
  rcases hf with ⟨hfSmooth, ⟨B, hB⟩, ⟨δ, hδ, hconst⟩⟩
  let a : ℝ := s.re + 1
  have hTop : f =O[atTop] (fun x : ℝ => x ^ (-a)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (max B 1)] with x hx
    have hxB : B ≤ x := (le_max_left B 1).trans hx
    rw [hB x hxB]
    simpa using norm_nonneg (x ^ (-a))
  have hBot : f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨‖f 0‖, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
    have hxconst : f x = f 0 := hconst x ⟨le_of_lt hx.1, hx.2.le⟩
    simp [hxconst]
  have hloc : LocallyIntegrableOn f (Set.Ioi 0) :=
    hfSmooth.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  exact mellinConvergent_of_isBigO_rpow hloc hTop (by dsimp [a]; linarith)
    hBot hs

private lemma qs_mellin_ibp [IsTotallyComplex K] (h : ℝ → ℂ) (hh : IsQSWeight h)
    (s : ℂ) (hs : 0 < s.re) :
    mellin h s = -(mellin (fun x : ℝ => (x : ℂ) * deriv h x) s) / s := by
  have hsne : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  let g : ℝ → ℂ := fun x => (x : ℂ) * deriv h x
  have hgQS : IsQSWeight g := by
    have h := qs_x_mul_iteratedDeriv_isQSWeight h hh 1 (by norm_num)
    simpa [g, iteratedDeriv_one] using h
  have hMh : MellinConvergent h s := qs_mellin_convergent_of_QS h hh s hs
  have hMg : MellinConvergent g s := qs_mellin_convergent_of_QS g hgQS s hs
  have hUderiv (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x :=
    hasDerivAt_ofReal_cpow_const hx.ne' hsne
  have hDiff : Differentiable ℝ h := hh.1.differentiable (by simp)
  have hVderiv (x : ℝ) (hx : x ∈ Set.Ioi 0) : HasDerivAt h (deriv h x) x :=
    (hDiff x).hasDerivAt
  have hTerm1 : IntegrableOn
      (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * h x) (Set.Ioi 0) := by
    change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) • h x) (Set.Ioi 0) at hMh
    have hsmul := hMh.smul s
    apply (integrableOn_congr_fun ?_ measurableSet_Ioi).2 hsmul
    intro x hx
    simp [smul_eq_mul, mul_assoc]
  have hTerm2 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * deriv h x) (Set.Ioi 0) := by
    change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) • g x) (Set.Ioi 0) at hMg
    apply (integrableOn_congr_fun ?_ measurableSet_Ioi).2 hMg
    intro x hx
    have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    calc
      (x : ℂ) ^ s * deriv h x =
          (x : ℂ) ^ (s - 1) * ((x : ℂ) * deriv h x) := by
            rw [show s = (s - 1) + 1 by ring, Complex.cpow_add _ _ hxne]
            simp [mul_assoc]
      _ = (x : ℂ) ^ (s - 1) • g x := by simp [g, smul_eq_mul]
  have huZero : Tendsto (fun x : ℝ => (x : ℂ) ^ s * h x)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hs0 : s ≠ 0 := hsne
    have hp := Complex.continuousAt_ofReal_cpow_const (0 : ℝ) s (Or.inl hs)
    have hpow : Tendsto (fun x : ℝ => (x : ℂ) ^ s) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := nhdsWithin_le_nhds
      have h := hp.tendsto.mono_left hle
      simpa [Complex.zero_cpow hs0] using h
    have hhcont : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0)) :=
      hh.1.continuous.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    simpa using hpow.mul hhcont
  have huInf : Tendsto (fun x : ℝ => (x : ℂ) ^ s * h x) atTop (𝓝 (0 : ℂ)) := by
    rcases hh.2.1 with ⟨B, hB⟩
    have heq : (fun _ : ℝ => (0 : ℂ)) =ᶠ[atTop]
        fun x => (x : ℂ) ^ s * h x := by
      filter_upwards [eventually_ge_atTop B] with x hx
      simp [hB x hx]
    exact tendsto_const_nhds.congr' heq
  have hIBP := MeasureTheory.integral_Ioi_deriv_mul_eq_sub
    (a := 0) (u := fun x : ℝ => (x : ℂ) ^ s)
    (u' := fun x => s * (x : ℂ) ^ (s - 1)) (v := h) (v' := deriv h)
    (fun x hx => hUderiv x hx) hVderiv (hTerm1.add hTerm2) huZero huInf
  have hTerm1Eq : (∫ x : ℝ in Set.Ioi 0,
      (s * (x : ℂ) ^ (s - 1)) * h x) = s * mellin h s := by
    calc
      (∫ x : ℝ in Set.Ioi 0, (s * (x : ℂ) ^ (s - 1)) * h x) =
          ∫ x : ℝ in Set.Ioi 0, s • ((x : ℂ) ^ (s - 1) • h x) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            simp [smul_eq_mul, mul_assoc]
      _ = s • mellin h s := by rw [mellin, integral_smul]
      _ = s * mellin h s := by simp [smul_eq_mul]
  have hTerm2Eq : (∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ s * deriv h x) = mellin g s := by
    rw [mellin]
    apply (integral_congr_ae ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    dsimp [g]
    rw [show s = (s - 1) + 1 by ring, Complex.cpow_add _ _ hxne]
    simp [mul_assoc]
  rw [integral_add hTerm1 hTerm2, hTerm1Eq, hTerm2Eq] at hIBP
  have hsolve : s * mellin h s = -mellin g s := by linear_combination hIBP
  calc
    mellin h s = s⁻¹ * (s * mellin h s) := by field_simp [hsne]
    _ = s⁻¹ * (-mellin g s) := by rw [hsolve]
    _ = -(mellin g s) / s := by ring

private lemma qsLogMellinWeight_iteratedDeriv_integrable_of_zero
    (g : ℝ → ℂ) (hg : IsQSWeight g) (hgzero : g 0 = 0) (σ : ℝ) (n : ℕ) :
    Integrable (iteratedDeriv n (qsLogMellinWeight g σ)) := by
  rcases hg with ⟨hgSmooth, ⟨B, hgTop⟩, ⟨δ, hδ, hgconst⟩⟩
  let q : ℝ → ℂ := qsLogMellinWeight g σ
  have hconstZero : ∀ x ∈ Set.Icc (0 : ℝ) δ, g x = 0 := by
    intro x hx
    rw [hgconst x hx, hgzero]
  let B₁ : ℝ := max B 1
  let δ₁ : ℝ := min δ (B₁ / 2)
  have hB₁ : 0 < B₁ := by dsimp [B₁]; positivity
  have hδ₁ : 0 < δ₁ := by
    dsimp [δ₁]
    exact lt_min hδ (by positivity)
  have hδB : δ₁ ≤ B₁ := by
    dsimp [δ₁]
    exact (min_le_right _ _).trans (by linarith)
  let lo : ℝ := -Real.log B₁
  let hi : ℝ := -Real.log δ₁
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    rw [neg_le_neg_iff, Real.log_le_log_iff hδ₁ hB₁]
    exact hδB
  have hg' : IsQSWeight g := ⟨hgSmooth, ⟨B, hgTop⟩, ⟨δ, hδ, hgconst⟩⟩
  have hqCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q :=
    qsLogMellinWeight_contDiff g σ hg'
  have hleft : Set.EqOn q (fun _ : ℝ => (0 : ℂ)) (Set.Iio lo) := by
    intro v hv
    have hv' : Real.log B₁ < -v := by
      change v < lo at hv
      have h := neg_lt_neg hv
      simpa [lo] using h
    have hx : B₁ ≤ Real.exp (-v) := by
      calc
        B₁ = Real.exp (Real.log B₁) := (Real.exp_log hB₁).symm
        _ ≤ Real.exp (-v) := Real.exp_le_exp.mpr hv'.le
    have hxg : g (Real.exp (-v)) = 0 := hgTop _ ((le_max_left B 1).trans hx)
    simp [q, qsLogMellinWeight, hxg]
  have hright : Set.EqOn q (fun _ : ℝ => (0 : ℂ)) (Set.Ioi hi) := by
    intro v hv
    have hv' : -v < Real.log δ₁ := by
      change hi < v at hv
      have h := neg_lt_neg hv
      simpa [hi] using h
    have hx : Real.exp (-v) ≤ δ₁ := by
      rw [← Real.exp_log hδ₁]
      exact Real.exp_le_exp.mpr hv'.le
    have hxg : g (Real.exp (-v)) = 0 :=
      hconstZero (Real.exp (-v)) ⟨(Real.exp_pos _).le, hx.trans (min_le_left _ _)⟩
    simp [q, qsLogMellinWeight, hxg]
  have hleftDeriv : Set.EqOn (iteratedDeriv n q) (fun _ : ℝ => (0 : ℂ)) (Set.Iio lo) := by
    intro v hv
    have h := hleft.iteratedDeriv_of_isOpen isOpen_Iio n hv
    simpa using h
  have hrightDeriv : Set.EqOn (iteratedDeriv n q) (fun _ : ℝ => (0 : ℂ)) (Set.Ioi hi) := by
    intro v hv
    have h := hright.iteratedDeriv_of_isOpen isOpen_Ioi n hv
    simpa using h
  have hleftInt : IntegrableOn (iteratedDeriv n q) (Set.Iio lo) := by
    apply (integrableOn_congr_fun hleftDeriv measurableSet_Iio).2
    simp
  have hmiddleInt : IntegrableOn (iteratedDeriv n q) (Set.Icc lo hi) := by
    exact (hqCont.continuous_iteratedDeriv n (by simp)).continuousOn.integrableOn_compact isCompact_Icc
  have hrightInt : IntegrableOn (iteratedDeriv n q) (Set.Ioi hi) := by
    apply (integrableOn_congr_fun hrightDeriv measurableSet_Ioi).2
    simp
  have hsets : Set.Iio lo ∪ Set.Icc lo hi ∪ Set.Ioi hi = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi, Set.mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      by_cases hvl : v < lo
      · exact Or.inl (Or.inl hvl)
      · by_cases hvr : v ≤ hi
        · exact Or.inl (Or.inr ⟨le_of_not_gt hvl, hvr⟩)
        · exact Or.inr (lt_of_not_ge hvr)
  rw [← integrableOn_univ, ← hsets, integrableOn_union, integrableOn_union]
  exact ⟨⟨hleftInt, hmiddleInt⟩, hrightInt⟩

private lemma qs_mellin_vertical_decay_of_zero (g : ℝ → ℂ) (hg : IsQSWeight g)
    (hgzero : g 0 = 0) (σ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 * Real.pi ≤ |t| →
      ‖mellin g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / |t| ^ N := by
  let q : ℝ → ℂ := qsLogMellinWeight g σ
  have hqCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q :=
    qsLogMellinWeight_contDiff g σ hg
  have hqInt : ∀ n : ℕ, Integrable (iteratedDeriv n q) :=
    fun n => qsLogMellinWeight_iteratedDeriv_integrable_of_zero g hg hgzero σ n
  obtain ⟨C₀, hC₀, hFourier⟩ := qs_fourier_decay_bound q hqCont hqInt N
  have hπ : 0 < 2 * Real.pi := by positivity
  let C : ℝ := C₀ * (2 * Real.pi) ^ N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht
  have hy : 1 ≤ |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos hπ]
    exact (one_le_div hπ).2 ht
  have hMellin := qs_mellin_log_fourier g σ t
  calc
    ‖mellin g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
        ‖𝓕 q (t / (2 * Real.pi))‖ := by rw [hMellin]
    _ ≤ C₀ / |t / (2 * Real.pi)| ^ N := hFourier _ hy
    _ = C / |t| ^ N := by
      dsimp [C]
      rw [abs_div, abs_of_pos hπ, div_pow]
      field_simp

private lemma qs_iteratedDeriv_cexp_real (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Complex.exp (c * (x : ℂ))) =
      fun x : ℝ => c ^ n * Complex.exp (c * (x : ℂ)) := by
  induction n with
  | zero =>
      funext x
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [deriv_const_mul_field]
      have hlin : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
        convert Complex.ofRealCLM.hasDerivAt.const_mul c using 1 <;> simp [mul_comm]
      rw [(hlin.cexp).deriv]
      simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

set_option maxHeartbeats 10000000 in
private lemma qs_mellin_vertical_decay_uniform_of_zero (g : ℝ → ℂ)
    (hg : IsQSWeight g) (hgzero : g 0 = 0) (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, 2 * Real.pi ≤ |t| →
      ‖mellin g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / |t| ^ N := by
  rcases hg with ⟨hgSmooth, ⟨B, hgTop⟩, ⟨δ, hδ, hgconst⟩⟩
  let q₀ : ℝ → ℂ := qsLogMellinWeight g 0
  let B₁ : ℝ := max B 1
  let δ₁ : ℝ := min δ (B₁ / 2)
  have hB₁ : 0 < B₁ := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hBle : B ≤ B₁ := le_max_left B 1
  have hδ₁ : 0 < δ₁ := lt_min hδ (by positivity)
  have hδ₁δ : δ₁ ≤ δ := min_le_left _ _
  have hδ₁B : δ₁ < B₁ := by
    have hhalf : B₁ / 2 < B₁ := by linarith [hB₁]
    exact (min_le_right _ _).trans_lt hhalf
  let lo : ℝ := -Real.log B₁
  let hi : ℝ := -Real.log δ₁
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    rw [neg_le_neg_iff, Real.log_le_log_iff hδ₁ hB₁]
    exact (min_le_right _ _).trans (by linarith [hB₁])
  have hg' : IsQSWeight g := ⟨hgSmooth, ⟨B, hgTop⟩, ⟨δ, hδ, hgconst⟩⟩
  have hq₀Int : ∀ n : ℕ, Integrable (iteratedDeriv n q₀) := by
    intro n
    simpa [q₀] using
      qsLogMellinWeight_iteratedDeriv_integrable_of_zero g hg' hgzero 0 n
  have hzeroLeft (σ : ℝ) : Set.EqOn (qsLogMellinWeight g σ)
      (fun _ : ℝ => (0 : ℂ)) (Set.Iio lo) := by
    intro v hv
    have hv' : Real.log B₁ < -v := by
      change v < lo at hv
      have h := neg_lt_neg hv
      simpa [lo] using h
    have hx : B₁ ≤ Real.exp (-v) := by
      calc
        B₁ = Real.exp (Real.log B₁) := (Real.exp_log hB₁).symm
        _ ≤ Real.exp (-v) := Real.exp_le_exp.mpr hv'.le
    have hxg : g (Real.exp (-v)) = 0 := hgTop _ (hBle.trans hx)
    simp [qsLogMellinWeight, hxg]
  have hzeroRight (σ : ℝ) : Set.EqOn (qsLogMellinWeight g σ)
      (fun _ : ℝ => (0 : ℂ)) (Set.Ioi hi) := by
    intro v hv
    have hv' : -v < Real.log δ₁ := by
      change hi < v at hv
      have h := neg_lt_neg hv
      simpa [hi] using h
    have hx : Real.exp (-v) ≤ δ₁ := by
      rw [← Real.exp_log hδ₁]
      exact Real.exp_le_exp.mpr hv'.le
    have hxg : g (Real.exp (-v)) = 0 := by
      rw [hgconst (Real.exp (-v))
        ⟨(Real.exp_pos _).le, hx.trans hδ₁δ⟩, hgzero]
    simp [qsLogMellinWeight, hxg]
  have hzeroLeftDeriv (σ : ℝ) : Set.EqOn
      (iteratedDeriv N (qsLogMellinWeight g σ)) (fun _ : ℝ => (0 : ℂ)) (Set.Iio lo) := by
    intro v hv
    have hz := (hzeroLeft σ).iteratedDeriv_of_isOpen isOpen_Iio N hv
    simpa using hz
  have hzeroRightDeriv (σ : ℝ) : Set.EqOn
      (iteratedDeriv N (qsLogMellinWeight g σ)) (fun _ : ℝ => (0 : ℂ)) (Set.Ioi hi) := by
    intro v hv
    have hz := (hzeroRight σ).iteratedDeriv_of_isOpen isOpen_Ioi N hv
    simpa using hz
  let M : ℝ := max 1 (max |a| |b|)
  let V : ℝ := max |lo| |hi|
  let E : ℝ := Real.exp (M * V)
  have hMone : 1 ≤ M := by dsimp [M]; exact le_max_left _ _
  have hMa : |a| ≤ M := by dsimp [M]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hMb : |b| ≤ M := by dsimp [M]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hMone
  have hVlo : |lo| ≤ V := by dsimp [V]; exact le_max_left _ _
  have hVhi : |hi| ≤ V := by dsimp [V]; exact le_max_right _ _
  have hVnonneg : 0 ≤ V := le_trans (abs_nonneg _) hVlo
  have hEpos : 0 < E := Real.exp_pos _
  have hsigmaAbs (σ : ℝ) (hσ : σ ∈ Set.Icc a b) : |σ| ≤ M := by
    apply abs_le.mpr
    constructor
    · have ha' : -|a| ≤ a := neg_abs_le a
      have hMa' : -M ≤ -|a| := neg_le_neg hMa
      linarith [hσ.1]
    · have hb' : b ≤ |b| := le_abs_self b
      linarith [hσ.2, hb', hMb]
  have hvAbs (v : ℝ) (hv : v ∈ Set.Icc lo hi) : |v| ≤ V := by
    apply abs_le.mpr
    constructor
    · have hlo' : -|lo| ≤ lo := neg_abs_le lo
      linarith [hv.1, hVlo]
    · have hhi' : hi ≤ |hi| := le_abs_self hi
      linarith [hv.2, hhi', hVhi]
  let coeff : ℕ → ℝ := fun i => (N.choose i : ℝ) * M ^ i * E
  let majorant : ℝ → ℝ := fun v =>
    ∑ i ∈ Finset.range (N + 1), coeff i * ‖iteratedDeriv (N - i) q₀ v‖
  have hqEq (σ : ℝ) : qsLogMellinWeight g σ =
      fun v : ℝ => Complex.exp ((-σ : ℂ) * (v : ℂ)) * q₀ v := by
    funext v
    dsimp [qsLogMellinWeight, q₀, smul_eq_mul]
    rw [Complex.ofReal_exp]
    congr 1
    · push_cast
      ring
    · simp
  have hq₀Cont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q₀ := by
    simpa [q₀] using qsLogMellinWeight_contDiff g 0 hg'
  have hderivFormula (σ v : ℝ) :
      iteratedDeriv N (qsLogMellinWeight g σ) v =
        ∑ i ∈ Finset.range (N + 1),
          (N.choose i : ℂ) * (((-σ : ℂ) ^ i) *
            Complex.exp ((-σ : ℂ) * (v : ℂ))) *
            iteratedDeriv (N - i) q₀ v := by
    rw [hqEq σ]
    change iteratedDeriv N
      ((fun v : ℝ => Complex.exp ((-σ : ℂ) * (v : ℂ))) * q₀) v = _
    have hExpReal : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : ℝ => Real.exp (-σ * v)) := by fun_prop
    have hExpRealCo : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : ℝ => (Real.exp (-σ * v) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hExpReal
    have hExpCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : ℝ => Complex.exp ((-σ : ℂ) * (v : ℂ))) := by
      convert hExpRealCo using 1
      funext v
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    have hExpAt : ContDiffAt ℝ N
        (fun v : ℝ => Complex.exp ((-σ : ℂ) * (v : ℂ))) v :=
      (hExpCont.of_le
        (show (N : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by
          exact WithTop.coe_le_coe.mpr (le_top : (N : ℕ∞) ≤ ⊤))).contDiffAt
    have hq₀At : ContDiffAt ℝ N q₀ v :=
      (hq₀Cont.of_le
        (show (N : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by
          exact WithTop.coe_le_coe.mpr (le_top : (N : ℕ∞) ≤ ⊤))).contDiffAt
    rw [iteratedDeriv_mul hExpAt hq₀At]
    simp only [qs_iteratedDeriv_cexp_real]
  have hcoeffNonneg (i : ℕ) : 0 ≤ coeff i := by
    dsimp [coeff]
    positivity
  have hmajorantNonneg (v : ℝ) : 0 ≤ majorant v := by
    apply Finset.sum_nonneg
    intro i hi
    positivity
  have hmajorantIntegrable : Integrable majorant := by
    dsimp [majorant]
    apply integrable_finsetSum (Finset.range (N + 1))
    intro i hi
    apply (hq₀Int (N - i)).norm.const_mul (coeff i)
  have hpointwise (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (v : ℝ) :
      ‖iteratedDeriv N (qsLogMellinWeight g σ) v‖ ≤ majorant v := by
    by_cases hv : v ∈ Set.Icc lo hi
    · rw [hderivFormula]
      calc
        ‖∑ i ∈ Finset.range (N + 1),
            (N.choose i : ℂ) * (((-σ : ℂ) ^ i) *
              Complex.exp ((-σ : ℂ) * (v : ℂ))) *
              iteratedDeriv (N - i) q₀ v‖ ≤
            ∑ i ∈ Finset.range (N + 1),
              ‖(N.choose i : ℂ) * (((-σ : ℂ) ^ i) *
                Complex.exp ((-σ : ℂ) * (v : ℂ))) *
                iteratedDeriv (N - i) q₀ v‖ := norm_sum_le _ _
        _ ≤ majorant v := by
          apply Finset.sum_le_sum
          intro i hi
          have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hchoose : 0 ≤ (N.choose i : ℝ) := by positivity
          have hsig : |σ| ≤ M := hsigmaAbs σ hσ
          have hsigpow : |σ| ^ i ≤ M ^ i := pow_le_pow_left₀ (abs_nonneg _) hsig i
          have hprod : |σ * v| ≤ M * V := by
            rw [abs_mul]
            exact mul_le_mul hsig (hvAbs v hv) (abs_nonneg _) hMpos.le
          have hexp : Real.exp (-σ * v) ≤ E := by
            dsimp [E]
            apply Real.exp_le_exp.mpr
            calc
              -σ * v ≤ |σ * v| := by simpa [neg_mul] using (neg_le_abs (σ * v))
              _ ≤ M * V := hprod
          have hterm :
              ‖(N.choose i : ℂ) * (((-σ : ℂ) ^ i) *
                  Complex.exp ((-σ : ℂ) * (v : ℂ))) *
                  iteratedDeriv (N - i) q₀ v‖ =
                (N.choose i : ℝ) * |σ| ^ i * Real.exp (-σ * v) *
                  ‖iteratedDeriv (N - i) q₀ v‖ := by
            have hchoose : ‖(N.choose i : ℂ)‖ = (N.choose i : ℝ) := by simp
            have hsigpow : ‖(-σ : ℂ) ^ i‖ = |σ| ^ i := by
              simp [norm_pow, RCLike.norm_ofReal, abs_neg]
            have hexpnorm :
                ‖Complex.exp ((-σ : ℂ) * (v : ℂ))‖ = Real.exp (-σ * v) := by
              have harg : (-σ : ℂ) * (v : ℂ) = (-(σ * v) : ℝ) := by
                push_cast
                ring
              rw [harg, Complex.norm_exp_ofReal]
              ring
            rw [norm_mul, norm_mul, hchoose, norm_mul, hsigpow, hexpnorm]
            ring
          rw [hterm]
          dsimp [majorant, coeff]
          gcongr

    · have hnot : v < lo ∨ hi < v := by
        by_cases hleft : v < lo
        · exact Or.inl hleft
        · right
          have hlo : lo ≤ v := le_of_not_gt hleft
          have hhi : ¬ v ≤ hi := by
            intro hle
            exact hv (Set.mem_Icc.mpr ⟨hlo, hle⟩)
          exact lt_of_not_ge hhi
      rcases hnot with hleft | hright
      · rw [hzeroLeftDeriv σ hleft]
        simp
        exact hmajorantNonneg v
      · rw [hzeroRightDeriv σ hright]
        simp
        exact hmajorantNonneg v
  let C₀ : ℝ := ∫ v : ℝ, majorant v
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact integral_nonneg hmajorantNonneg
  have hderivInt (σ : ℝ) (hσ : σ ∈ Set.Icc a b) :
      Integrable (iteratedDeriv N (qsLogMellinWeight g σ)) := by
    exact qsLogMellinWeight_iteratedDeriv_integrable_of_zero g hg' hgzero σ N
  have hCbound (σ : ℝ) (hσ : σ ∈ Set.Icc a b) :
      ∫ v : ℝ, ‖iteratedDeriv N (qsLogMellinWeight g σ) v‖ ≤ C₀ := by
    have hint : Integrable (fun v : ℝ =>
        ‖iteratedDeriv N (qsLogMellinWeight g σ) v‖) := (hderivInt σ hσ).norm
    apply integral_mono_ae hint hmajorantIntegrable
    exact Filter.Eventually.of_forall (hpointwise σ hσ)
  have hFourierBound (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (y : ℝ) :
      ‖𝓕 (iteratedDeriv N (qsLogMellinWeight g σ)) y‖ ≤ C₀ := by
    rw [Real.fourier_eq]
    calc
      ‖∫ v : ℝ, 𝐞 (-⟪v, y⟫) • iteratedDeriv N (qsLogMellinWeight g σ) v‖ ≤
          ∫ v : ℝ, ‖𝐞 (-⟪v, y⟫) • iteratedDeriv N (qsLogMellinWeight g σ) v‖ :=
            norm_integral_le_integral_norm _
      _ = ∫ v : ℝ, ‖iteratedDeriv N (qsLogMellinWeight g σ) v‖ := by
        apply integral_congr_ae
        filter_upwards with v
        simp [Circle.norm_smul]
      _ ≤ C₀ := hCbound σ hσ
  have hFourierIter (σ : ℝ) (hσ : σ ∈ Set.Icc a b) :
      ∀ y : ℝ, 1 ≤ |y| → ‖𝓕 (qsLogMellinWeight g σ) y‖ ≤ C₀ / |y| ^ N := by
    let qσ := qsLogMellinWeight g σ
    have hqCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) qσ :=
      qsLogMellinWeight_contDiff g σ hg'
    have hqInt : ∀ n : ℕ, Integrable (iteratedDeriv n qσ) :=
      fun n => qsLogMellinWeight_iteratedDeriv_integrable_of_zero g hg' hgzero σ n
    have hEq := Real.fourier_iteratedDeriv (f := qσ) (N := ⊤) (n := N) hqCont
      (fun m hm => hqInt m) (by simp)
    intro y hy
    have hyabs : 0 < |y| := lt_of_lt_of_le zero_lt_one hy
    have hscalar : ‖(2 * Real.pi * Complex.I * (y : ℂ)) ^ N‖ =
          (2 * Real.pi * |y|) ^ N := by
        rw [norm_pow, norm_mul, norm_mul, norm_mul]
        simp [RCLike.norm_ofReal, Real.pi_pos]
    have hnormEq : ‖𝓕 (iteratedDeriv N qσ) y‖ =
          ‖(2 * Real.pi * Complex.I * (y : ℂ)) ^ N‖ * ‖𝓕 qσ y‖ := by
        rw [congrFun hEq y, norm_smul]
    have hbig : |y| ^ N * ‖𝓕 qσ y‖ ≤ C₀ := by
      have hfour : ‖(2 * Real.pi * Complex.I * (y : ℂ)) ^ N‖ * ‖𝓕 qσ y‖ ≤ C₀ := by
          rw [← hnormEq]
          exact hFourierBound σ hσ y
      rw [hscalar] at hfour
      have hbase : |y| ^ N ≤ (2 * Real.pi * |y|) ^ N := by
          apply pow_le_pow_left₀ (abs_nonneg _) ?_ N
          have hπ : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
          nlinarith
      calc
        |y| ^ N * ‖𝓕 qσ y‖ ≤ (2 * Real.pi * |y|) ^ N * ‖𝓕 qσ y‖ :=
            mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
        _ ≤ C₀ := by simpa [mul_comm] using hfour
    rw [le_div_iff₀ (pow_pos hyabs N)]
    simpa [mul_comm] using hbig
  have hπ : 0 < 2 * Real.pi := by positivity
  let C : ℝ := C₀ * (2 * Real.pi) ^ N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro σ hσ t ht
  have hy : 1 ≤ |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos hπ]
    exact (one_le_div hπ).2 ht
  have hFour := hFourierIter σ hσ (t / (2 * Real.pi)) hy
  have hMellin := qs_mellin_log_fourier g σ t
  calc
    ‖mellin g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
        ‖𝓕 (qsLogMellinWeight g σ) (t / (2 * Real.pi))‖ := by rw [hMellin]
    _ ≤ C₀ / |t / (2 * Real.pi)| ^ N := hFour
    _ = C / |t| ^ N := by
      dsimp [C]
      rw [abs_div, abs_of_pos hπ, div_pow]
      field_simp

private lemma qs_mellin_deriv_differentiableAt [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (s : ℂ) :
    DifferentiableAt ℂ (mellin (fun x : ℝ => (x : ℂ) * deriv h x)) s := by
  let g : ℝ → ℂ := fun x => (x : ℂ) * deriv h x
  have hgQS : IsQSWeight g := by
    simpa [g, iteratedDeriv_one] using
      qs_x_mul_iteratedDeriv_isQSWeight h hh 1 (by norm_num)
  have hg0 : g 0 = 0 := by simp [g]
  rcases hgQS with ⟨hgSmooth, ⟨B, hgTop⟩, ⟨δ, hδ, hgconst⟩⟩
  let a : ℝ := s.re + 1
  let b : ℝ := s.re - 1
  have hTop : g =O[atTop] (fun x : ℝ => x ^ (-a)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (max B 1)] with x hx
    have hxB : B ≤ x := (le_max_left B 1).trans hx
    rw [hgTop x hxB]
    simpa using norm_nonneg (x ^ (-a))
  have hBot : g =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-b)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨0, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
    have hxzero : g x = 0 := by
      rw [hgconst x ⟨le_of_lt hx.1, hx.2.le⟩, hg0]
    simp [hxzero]
  have hloc : LocallyIntegrableOn g (Set.Ioi 0) :=
    hgSmooth.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  exact mellin_differentiableAt_of_isBigO_rpow hloc hTop (by dsimp [a]; linarith)
    hBot (by dsimp [b]; linarith)

private lemma qs_nrComplexPlaces_pos [IsTotallyComplex K] :
    0 < NumberField.InfinitePlace.nrComplexPlaces K := by
  have hsig := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add] at hsig
  have hRank : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

private def qsRegularizedMellinProduct [IsTotallyComplex K]
    (h : ℝ → ℂ) (u : ℂ) : ℂ :=
  let s : ℂ := 1 - u;
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ);
  let A : ℂ := 2 * (Real.pi : ℂ);
  let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces K;
  -Hecke.dedekindPrefactor K u * D ^ (-s / 2) *
    (((1 / 2 : ℂ) * A ^ s) ^ r) * s ^ (r - 1) *
      ((Complex.Gamma (s + 1))⁻¹) ^ r *
        mellin (fun x : ℝ => (x : ℂ) * deriv h x) s

private lemma qs_prefactor_inv_div_formula [IsTotallyComplex K] (s : ℂ) (hs : s ≠ 0) :
    (Hecke.dedekindPrefactor K s)⁻¹ / s =
      (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (-s / 2)) *
        (((1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ s) ^
          NumberField.InfinitePlace.nrComplexPlaces K) *
        s ^ (NumberField.InfinitePlace.nrComplexPlaces K - 1) *
        ((Complex.Gamma (s + 1))⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
  have hr : 0 < NumberField.InfinitePlace.nrComplexPlaces K := qs_nrComplexPlaces_pos (K := K)
  have hrpow : NumberField.InfinitePlace.nrComplexPlaces K - 1 + 1 =
      NumberField.InfinitePlace.nrComplexPlaces K := by omega
  let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces K
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  let A : ℂ := 2 * (Real.pi : ℂ)
  let c : ℂ := (1 / 2 : ℂ) * A ^ s
  let g : ℂ := (Complex.Gamma (s + 1))⁻¹
  have hfactor : (c * (s * g)) ^ r = c ^ r * g ^ r * s ^ r := by
    rw [mul_pow, mul_pow]
    ring
  have hspow : s ^ r * s⁻¹ = s ^ (r - 1) := by
    rw [show r = (r - 1) + 1 by omega, pow_add, pow_one]
    simp [hs]
  have hDexp : (-s / 2 : ℂ) = s * (-1 / 2 : ℂ) := by ring
  rw [div_eq_mul_inv, qs_prefactor_inv_formula, qs_gammaC_inv_formula]
  rw [hDexp]
  rw [hfactor]
  calc
    _ = D ^ (s * (-1 / 2 : ℂ)) * c ^ r * g ^ r * (s ^ r * s⁻¹) := by ac_rfl
    _ = D ^ (s * (-1 / 2 : ℂ)) * c ^ r * g ^ r * s ^ (r - 1) := by rw [hspow]
    _ = D ^ (s * (-1 / 2 : ℂ)) * c ^ r * s ^ (r - 1) * g ^ r := by ac_rfl
    _ = (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (s * (-1 / 2 : ℂ))) *
        (((1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ s) ^
          NumberField.InfinitePlace.nrComplexPlaces K) *
        s ^ (NumberField.InfinitePlace.nrComplexPlaces K - 1) *
        ((Complex.Gamma (s + 1))⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
          dsimp [D, c, g, r, A]

private lemma qsRegularizedMellinProduct_differentiableAt [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (u : ℂ) (hu : 0 < u.re) :
    DifferentiableAt ℂ (qsRegularizedMellinProduct (K := K) h) u := by
  let s : ℂ := 1 - u
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  let A : ℂ := 2 * (Real.pi : ℂ)
  let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces K
  let g : ℝ → ℂ := fun x => (x : ℂ) * deriv h x
  have hDreal : (|(NumberField.discr K : ℝ)| : ℝ) ≠ 0 := by
    exact abs_ne_zero.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact Complex.ofReal_ne_zero.mpr hDreal
  have hA : A ≠ 0 := by
    dsimp [A]
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hpref : DifferentiableAt ℂ (Hecke.dedekindPrefactor K) u :=
    qs_prefactor_differentiableAt (K := K) u hu
  have hDpow : DifferentiableAt ℂ (fun w : ℂ => D ^ (-(1 - w) / 2)) u := by
    apply ((differentiableAt_const (1 : ℂ) |>.sub differentiableAt_id).neg.div_const (2 : ℂ)).const_cpow
    exact Or.inl hD
  have hApow : DifferentiableAt ℂ (fun w : ℂ => A ^ (1 - w)) u := by
    apply (differentiableAt_const (1 : ℂ) |>.sub differentiableAt_id).const_cpow
    exact Or.inl hA
  have hgamma : DifferentiableAt ℂ
      (fun w : ℂ => ((Complex.Gamma ((1 - w) + 1))⁻¹) ^ r) u := by
    have hInv : Differentiable ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
      Complex.differentiable_one_div_Gamma
    have hComp := hInv.differentiableAt.comp u
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (1 - w) + 1) u)
    exact hComp.pow r
  have hg : DifferentiableAt ℂ (fun w : ℂ => mellin g (1 - w)) u := by
    exact (qs_mellin_deriv_differentiableAt (K := K) h hh (1 - u)).comp u (by fun_prop)
  change DifferentiableAt ℂ (fun w : ℂ =>
    -Hecke.dedekindPrefactor K w * D ^ (-(1 - w) / 2) *
      (((1 / 2 : ℂ) * A ^ (1 - w)) ^ r) * (1 - w) ^ (r - 1) *
        ((Complex.Gamma ((1 - w) + 1))⁻¹) ^ r * mellin g (1 - w)) u
  have hprefNeg : DifferentiableAt ℂ (fun w : ℂ => -Hecke.dedekindPrefactor K w) u := hpref.neg
  have hAterm : DifferentiableAt ℂ
      (fun w : ℂ => ((1 / 2 : ℂ) * A ^ (1 - w)) ^ r) u :=
    ((differentiableAt_const (1 / 2 : ℂ)).mul hApow).pow r
  have hspow : DifferentiableAt ℂ (fun w : ℂ => (1 - w) ^ (r - 1)) u :=
    (differentiableAt_const (1 : ℂ) |>.sub differentiableAt_id).pow (r - 1)
  exact (((((hprefNeg.mul hDpow).mul hAterm).mul hspow).mul hgamma).mul hg)

private lemma qsRegularizedMellinProduct_eq_original [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (u : ℂ) (hu₀ : 0 < u.re) (hu₁ : u.re < 1) :
    qsRegularizedMellinProduct (K := K) h u = qsGammaRatio K u * mellin h (1 - u) := by
  let s : ℂ := 1 - u
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  let A : ℂ := 2 * (Real.pi : ℂ)
  let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces K
  let g : ℝ → ℂ := fun x => (x : ℂ) * deriv h x
  have hs : 0 < s.re := by dsimp [s]; simp; linarith
  have hsne : s ≠ 0 := by
    intro hz
    have : s.re = 0 := by rw [hz]; simp
    linarith
  have hibp := qs_mellin_ibp (K := K) h hh s hs
  have hinvdiv := qs_prefactor_inv_div_formula (K := K) s hsne
  change -Hecke.dedekindPrefactor K u * D ^ (-s / 2) *
      (((1 / 2 : ℂ) * A ^ s) ^ r) * s ^ (r - 1) *
        ((Complex.Gamma (s + 1))⁻¹) ^ r * mellin g s =
    Hecke.dedekindPrefactor K u / Hecke.dedekindPrefactor K s * mellin h s
  rw [hibp]
  have hfactor :
      D ^ (-s / 2) * ((1 / 2 : ℂ) * A ^ s) ^ r * s ^ (r - 1) *
        ((Complex.Gamma (s + 1))⁻¹) ^ r = (Hecke.dedekindPrefactor K s)⁻¹ / s := by
    simpa [D, A, r] using hinvdiv.symm
  calc
    _ = -Hecke.dedekindPrefactor K u *
        (D ^ (-s / 2) * ((1 / 2 : ℂ) * A ^ s) ^ r * s ^ (r - 1) *
          ((Complex.Gamma (s + 1))⁻¹) ^ r) * mellin g s := by ac_rfl
    _ = -Hecke.dedekindPrefactor K u *
        ((Hecke.dedekindPrefactor K s)⁻¹ / s) * mellin g s := by rw [hfactor]
    _ = Hecke.dedekindPrefactor K u / Hecke.dedekindPrefactor K s *
        (-mellin g s / s) := by ring

private lemma qsRegularizedMellinProduct_eq_ratio_deriv [IsTotallyComplex K]
    (h : ℝ → ℂ) (u : ℂ) (hs : 1 - u ≠ 0) :
    qsRegularizedMellinProduct (K := K) h u =
      -(qsGammaRatio K u * mellin (fun x : ℝ => (x : ℂ) * deriv h x) (1 - u)) / (1 - u) := by
  let s : ℂ := 1 - u
  let D : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  let A : ℂ := 2 * (Real.pi : ℂ)
  let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces K
  let g : ℝ → ℂ := fun x => (x : ℂ) * deriv h x
  have hs' : s ≠ 0 := by simpa [s] using hs
  have hfactor :
      D ^ (-s / 2) * ((1 / 2 : ℂ) * A ^ s) ^ r * s ^ (r - 1) *
        ((Complex.Gamma (s + 1))⁻¹) ^ r = (Hecke.dedekindPrefactor K s)⁻¹ / s := by
    simpa [D, A, r] using (qs_prefactor_inv_div_formula (K := K) s hs').symm
  change -Hecke.dedekindPrefactor K u * D ^ (-s / 2) *
      (((1 / 2 : ℂ) * A ^ s) ^ r) * s ^ (r - 1) *
        ((Complex.Gamma (s + 1))⁻¹) ^ r * mellin g s =
    -(Hecke.dedekindPrefactor K u / Hecke.dedekindPrefactor K s * mellin g s) / s
  calc
    _ = -Hecke.dedekindPrefactor K u *
        (D ^ (-s / 2) * ((1 / 2 : ℂ) * A ^ s) ^ r * s ^ (r - 1) *
          ((Complex.Gamma (s + 1))⁻¹) ^ r) * mellin g s := by ac_rfl
    _ = -Hecke.dedekindPrefactor K u *
        ((Hecke.dedekindPrefactor K s)⁻¹ / s) * mellin g s := by rw [hfactor]
    _ = -(Hecke.dedekindPrefactor K u / Hecke.dedekindPrefactor K s * mellin g s) / s := by ring

set_option maxHeartbeats 10000000 in
private lemma qsRegularizedMellinProduct_vertical_decay [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, u.re ∈ Set.Icc a b →
      2 * Real.pi ≤ |u.im| →
      ‖qsRegularizedMellinProduct (K := K) h u‖ ≤ C / |u.im| ^ N := by
  let g : ℝ → ℂ := fun x => (x : ℂ) * deriv h x
  have hgQS : IsQSWeight g := by
    simpa [g, iteratedDeriv_one] using
      qs_x_mul_iteratedDeriv_isQSWeight h hh 1 (by norm_num)
  have hgzero : g 0 = 0 := by simp [g]
  obtain ⟨Cg, p, hCg, hp, hgamma⟩ :=
    qs_gammaRatio_polynomial_bound_right (K := K) ha hab
  obtain ⟨m, hm⟩ := exists_nat_gt p
  obtain ⟨Cm, hCm, hMellin⟩ := qs_mellin_vertical_decay_uniform_of_zero
    g hgQS hgzero (1 - b) (1 - a) (by linarith) (N + m)
  let C : ℝ := Cg * Cm * (2 : ℝ) ^ m
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hπ : 0 < 2 * Real.pi := by positivity
  refine ⟨C, hC, ?_⟩
  intro u hu hT
  let t : ℝ := |u.im|
  have htpos : 0 < t := lt_of_lt_of_le hπ hT
  have htone : 1 ≤ t := by nlinarith [Real.pi_gt_three]
  have hsRe : (1 - u).re = 1 - u.re := by simp
  have hsIm : (1 - u).im = -u.im := by simp
  have hsRange : (1 - u).re ∈ Set.Icc (1 - b) (1 - a) := by
    rw [hsRe]
    constructor <;> linarith [hu.1, hu.2]
  have htCond : 2 * Real.pi ≤ |-u.im| := by simpa [abs_neg] using hT
  have hM := hMellin (1 - u).re hsRange (-u.im) htCond
  have hsDecomp : 1 - u = ((1 - u).re : ℝ) + ((-u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hsRe, hsIm]
  have hMellin' : ‖mellin g (1 - u)‖ ≤ Cm / t ^ (N + m) := by
    have hsEq : 1 - u = ((1 - u).re : ℂ) + ((-u.im : ℝ) : ℂ) * Complex.I := by
      exact hsDecomp
    calc
      ‖mellin g (1 - u)‖ =
          ‖mellin g (((1 - u).re : ℂ) + ((-u.im : ℝ) : ℂ) * Complex.I)‖ :=
            congrArg (fun z : ℂ => ‖mellin g z‖) hsEq
      _ ≤ Cm / |-u.im| ^ (N + m) := hM
      _ = Cm / t ^ (N + m) := by simp [t, abs_neg]
  have hsne : 1 - u ≠ 0 := by
    intro hs0
    have him : u.im = 0 := by
      have h := congrArg Complex.im hs0
      simpa using h
    rw [him, abs_zero] at hT
    exact (not_le_of_gt hπ) hT
  have hRatio := hgamma u hu.1 hu.2
  have hregNorm : ‖qsRegularizedMellinProduct (K := K) h u‖ =
      ‖qsGammaRatio K u‖ * ‖mellin g (1 - u)‖ / ‖1 - u‖ := by
    rw [qsRegularizedMellinProduct_eq_ratio_deriv (K := K) h u hsne]
    rw [norm_div, norm_neg, norm_mul]
  have hden : t ≤ ‖1 - u‖ := by
    calc
      t = |u.im| := rfl
      _ = |-u.im| := by rw [abs_neg]
      _ = |(1 - u).im| := by rw [hsIm]
      _ ≤ ‖1 - u‖ := Complex.abs_im_le_norm (1 - u)
  have hnum : ‖qsGammaRatio K u‖ * ‖mellin g (1 - u)‖ ≤
      (Cg * (t + 2) ^ p) * (Cm / t ^ (N + m)) := by
    apply mul_le_mul hRatio hMellin'
    · positivity
    · positivity
  have hquot : ‖qsRegularizedMellinProduct (K := K) h u‖ ≤
      ((Cg * (t + 2) ^ p) * (Cm / t ^ (N + m))) / t := by
    rw [hregNorm]
    calc
      (‖qsGammaRatio K u‖ * ‖mellin g (1 - u)‖) / ‖1 - u‖ ≤
          ((Cg * (t + 2) ^ p) * (Cm / t ^ (N + m))) / ‖1 - u‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ ((Cg * (t + 2) ^ p) * (Cm / t ^ (N + m))) / t :=
        div_le_div_of_nonneg_left (by positivity) htpos hden
  have htwo : 2 ≤ t := by nlinarith [Real.pi_gt_three, hT]
  have hplus : t + 2 ≤ 2 * t := by linarith
  have hpow : (t + 2) ^ p ≤ (2 : ℝ) ^ m * t ^ m := by
    have hpowReal : (t + 2) ^ p ≤ (2 : ℝ) ^ (m : ℝ) * t ^ (m : ℝ) := by
      calc
        (t + 2) ^ p ≤ (2 * t) ^ p := Real.rpow_le_rpow (by positivity) hplus hp.le
        _ = 2 ^ p * t ^ p := Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ (2 : ℝ) ^ (m : ℝ) * t ^ (m : ℝ) := by
          exact mul_le_mul
            (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hm.le)
            (Real.rpow_le_rpow_of_exponent_le htone hm.le)
            (by positivity) (by positivity)
    simpa [Real.rpow_natCast] using hpowReal
  have htne : t ≠ 0 := ne_of_gt htpos
  have hquot' : ((Cg * (t + 2) ^ p) * (Cm / t ^ (N + m))) / t ≤
      C / t ^ (N + 1) := by
    calc
      ((Cg * (t + 2) ^ p) * (Cm / t ^ (N + m))) / t ≤
          ((Cg * ((2 : ℝ) ^ m * t ^ m)) * (Cm / t ^ (N + m))) / t := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            have hleft : Cg * (t + 2) ^ p ≤ Cg * ((2 : ℝ) ^ m * t ^ m) :=
              mul_le_mul_of_nonneg_left hpow hCg.le
            exact mul_le_mul_of_nonneg_right hleft (by positivity)
      _ = C / t ^ (N + 1) := by
        dsimp [C]
        field_simp [htne]
        rw [pow_add]
        ring
  have hpowmono : t ^ N ≤ t ^ (N + 1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg (le_of_lt htpos) _) htone
  calc
    ‖qsRegularizedMellinProduct (K := K) h u‖ ≤
        ((Cg * (t + 2) ^ p) * (Cm / t ^ (N + m))) / t := hquot
    _ ≤ C / t ^ (N + 1) := hquot'
    _ ≤ C / t ^ N := div_le_div_of_nonneg_left hC (pow_pos htpos N) hpowmono

private lemma qsRegularizedMellinProduct_line_integrable [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b) :
    Integrable (fun y : ℝ => qsRegularizedMellinProduct (K := K) h
      ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
  let F : ℝ → ℂ := fun y => qsRegularizedMellinProduct (K := K) h
    ((σ : ℂ) + (y : ℂ) * Complex.I)
  have hFcont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro y
    let z : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
    have hzre : z.re = σ := by simp [z]
    have hdiff := qsRegularizedMellinProduct_differentiableAt (K := K) h hh z
      (by rw [hzre]; exact lt_of_lt_of_le ha hσ.1)
    have hline : ContinuousAt (fun y : ℝ => (σ : ℂ) + (y : ℂ) * Complex.I) y := by fun_prop
    have hcomp := ContinuousAt.comp_of_eq hdiff.continuousAt hline (by rfl)
    simpa [F, z, Function.comp_def] using hcomp
  obtain ⟨C, hC, htail⟩ :=
    qsRegularizedMellinProduct_vertical_decay (K := K) h hh a b ha hab 3
  have hlineTail (y : ℝ) (hy : 2 * Real.pi ≤ |y|) :
      ‖F y‖ ≤ C / |y| ^ 3 := by
    have h := htail ((σ : ℂ) + (y : ℂ) * Complex.I) (by simpa using hσ) (by simpa)
    simpa [F] using h
  have hOtop : F =O[atTop] (fun y : ℝ => y ^ (-3 : ℝ)) := by
    rw [Asymptotics.isBigO_iff_isBigOWith]
    refine ⟨C, ?_⟩
    rw [Asymptotics.isBigOWith_iff]
    filter_upwards [eventually_ge_atTop (2 * Real.pi)] with y hy
    have hypos : 0 < y := by nlinarith [Real.pi_gt_three]
    have hAbs : |y| = y := abs_of_nonneg hypos.le
    have ht := hlineTail y (by simpa [hAbs] using hy)
    simpa [hAbs, Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv] using ht
  have hObot : F =O[atBot] (fun y : ℝ => (-y) ^ (-3 : ℝ)) := by
    rw [Asymptotics.isBigO_iff_isBigOWith]
    refine ⟨C, ?_⟩
    rw [Asymptotics.isBigOWith_iff]
    filter_upwards [eventually_le_atBot (-2 * Real.pi)] with y hy
    have hAbs : |y| = -y := abs_of_nonpos (by nlinarith [Real.pi_gt_three])
    have ht := hlineTail y (by simpa [hAbs] using (show 2 * Real.pi ≤ -y by linarith))
    simpa [hAbs, Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv] using ht
  have hpowTop : IntegrableOn (fun y : ℝ => y ^ (-3 : ℝ)) (Set.Ioi (2 * Real.pi)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by positivity)
  have hpowBot : IntegrableOn (fun y : ℝ => (-y) ^ (-3 : ℝ)) (Set.Iio (-2 * Real.pi)) := by
    let g : ℝ → ℝ := fun y => (-y) ^ (-3 : ℝ)
    have hImage : Neg.neg '' Set.Ioi (2 * Real.pi) = Set.Iio (-2 * Real.pi) := by
      ext y
      simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
      constructor
      · rintro ⟨x, hx, rfl⟩
        linarith
      · intro hy
        exact ⟨-y, by linarith, by simp⟩
    have hNegDeriv : ∀ x ∈ Set.Ioi (2 * Real.pi),
        HasDerivWithinAt (fun x : ℝ => -x) (-1) (Set.Ioi (2 * Real.pi)) x := by
      intro x hx
      exact (hasDerivAt_neg x).hasDerivWithinAt
    have hNegInj : Set.InjOn (fun x : ℝ => -x) (Set.Ioi (2 * Real.pi)) := by
      intro x hx y hy hxy
      exact neg_injective hxy
    rw [← hImage]
    apply (integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hNegDeriv hNegInj g).2
    simpa [g] using hpowTop
  have hAtTop : IntegrableAtFilter (fun y : ℝ => y ^ (-3 : ℝ)) atTop volume :=
    ⟨Set.Ioi (2 * Real.pi), Ioi_mem_atTop _, hpowTop⟩
  have hAtBot : IntegrableAtFilter (fun y : ℝ => (-y) ^ (-3 : ℝ)) atBot volume :=
    ⟨Set.Iio (-2 * Real.pi), Iio_mem_atBot _, hpowBot⟩
  exact hFcont.locallyIntegrable.integrable_of_isBigO_atBot_atTop hObot hAtBot hOtop hAtTop

private lemma qsRegularizedMellinProduct_line_moment_integrable [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (σ : ℝ) (hσ : 0 < σ) (k : ℕ) :
    Integrable (fun y : ℝ => |y| ^ k *
      ‖qsRegularizedMellinProduct (K := K) h
        ((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I)‖) := by
  let F : ℝ → ℂ := fun y => qsRegularizedMellinProduct (K := K) h
    ((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I)
  have hFcont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro y
    let z : ℂ := (σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I
    have hzre : z.re = σ := by simp [z]
    have hdiff := qsRegularizedMellinProduct_differentiableAt (K := K) h hh z
      (by rw [hzre]; exact hσ)
    have hline : ContinuousAt (fun y : ℝ =>
        (σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I) y := by fun_prop
    have hcomp := ContinuousAt.comp_of_eq hdiff.continuousAt hline (by rfl)
    simpa [F, z, Function.comp_def] using hcomp
  obtain ⟨C, hC, htail⟩ :=
    qsRegularizedMellinProduct_vertical_decay (K := K) h hh σ σ hσ le_rfl (k + 3)
  let G : ℝ → ℝ := fun y => |y| ^ k * ‖F y‖
  have hGcont : Continuous G := by
    dsimp [G]
    exact (continuous_abs.pow k).mul hFcont.norm
  have htailMoment (y : ℝ) (hy : 1 ≤ |y|) : G y ≤ C / |y| ^ 3 := by
    have hyπ : 2 * Real.pi ≤ |(2 * Real.pi * y)| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      have hπone : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * Real.pi - 1) (abs_nonneg y)]
    have hline := htail
      ((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I)
      (by constructor <;> simp) (by
        simpa [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im] using hyπ)
    have him : (((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I).im) =
        2 * Real.pi * y := by simp
    have hline' : ‖F y‖ ≤ C / |y| ^ (k + 3) := by
      have hpiScale : |y| ≤ |2 * Real.pi * y| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
        have hπone : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
        nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * Real.pi - 1) (abs_nonneg y)]
      have htarg : |(2 * Real.pi * y)| =
          |(((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I).im)| := by
        rw [him]
      have hbound : ‖F y‖ ≤ C / |2 * Real.pi * y| ^ (k + 3) := by
        simpa [F, htarg] using hline
      calc
        ‖F y‖ ≤ C / |2 * Real.pi * y| ^ (k + 3) := hbound
        _ ≤ C / |y| ^ (k + 3) := by
          apply div_le_div_of_nonneg_left hC (pow_pos (lt_of_lt_of_le zero_lt_one hy) _)
          exact pow_le_pow_left₀ (abs_nonneg _) hpiScale (k + 3)
    have hypos : 0 < |y| := lt_of_lt_of_le zero_lt_one hy
    have hpow : |y| ^ k * (C / |y| ^ (k + 3)) = C / |y| ^ 3 := by
      rw [pow_add]
      field_simp
    dsimp [G]
    calc
      |y| ^ k * ‖F y‖ ≤ |y| ^ k * (C / |y| ^ (k + 3)) :=
        mul_le_mul_of_nonneg_left hline' (by positivity)
      _ = C / |y| ^ 3 := hpow
  have hOtop : G =O[atTop] (fun y : ℝ => y ^ (-3 : ℝ)) := by
    rw [Asymptotics.isBigO_iff_isBigOWith]
    refine ⟨C, ?_⟩
    rw [Asymptotics.isBigOWith_iff]
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hAbs : |y| = y := abs_of_nonneg (by linarith)
    have ht := htailMoment y (by rw [hAbs]; exact hy)
    have hGnonneg : 0 ≤ G y := by positivity
    simpa [hAbs, Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv,
      Real.norm_eq_abs, abs_of_nonneg hGnonneg] using ht
  have hObot : G =O[atBot] (fun y : ℝ => (-y) ^ (-3 : ℝ)) := by
    rw [Asymptotics.isBigO_iff_isBigOWith]
    refine ⟨C, ?_⟩
    rw [Asymptotics.isBigOWith_iff]
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with y hy
    have hAbs : |y| = -y := abs_of_nonpos (by linarith)
    have ht := htailMoment y (by rw [hAbs]; linarith)
    have hGnonneg : 0 ≤ G y := by positivity
    simpa [hAbs, Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv,
      Real.norm_eq_abs, abs_of_nonneg hGnonneg] using ht
  have hpowTop : IntegrableOn (fun y : ℝ => y ^ (-3 : ℝ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hpowBot : IntegrableOn (fun y : ℝ => (-y) ^ (-3 : ℝ)) (Set.Iio (-1)) := by
    let g : ℝ → ℝ := fun y => (-y) ^ (-3 : ℝ)
    have hImage : Neg.neg '' Set.Ioi (1 : ℝ) = Set.Iio (-1) := by
      ext y
      simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio, neg_neg]
      constructor
      · rintro ⟨x, hx, rfl⟩
        linarith
      · intro hy
        exact ⟨-y, by linarith, by simp⟩
    have hNegDeriv : ∀ x ∈ Set.Ioi (1 : ℝ),
        HasDerivWithinAt (fun x : ℝ => -x) (-1) (Set.Ioi 1) x := by
      intro x hx
      exact (hasDerivAt_neg x).hasDerivWithinAt
    have hNegInj : Set.InjOn (fun x : ℝ => -x) (Set.Ioi 1) := by
      intro x hx y hy hxy
      exact neg_injective hxy
    rw [← hImage]
    apply (integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hNegDeriv hNegInj g).2
    simpa [g] using hpowTop
  have hAtTop : IntegrableAtFilter (fun y : ℝ => y ^ (-3 : ℝ)) atTop volume :=
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, hpowTop⟩
  have hAtBot : IntegrableAtFilter (fun y : ℝ => (-y) ^ (-3 : ℝ)) atBot volume :=
    ⟨Set.Iio (-1), Iio_mem_atBot (-1), hpowBot⟩
  exact hGcont.locallyIntegrable.integrable_of_isBigO_atBot_atTop hObot hAtBot hOtop hAtTop

private lemma qsRegularizedFourierInv_iteratedDeriv_bound [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (σ : ℝ) (hσ : 0 < σ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
      ‖iteratedDeriv n (𝓕⁻ (fun t : ℝ => qsRegularizedMellinProduct (K := K) h
        ((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) * Complex.I))) y‖ ≤ C := by
  let F : ℝ → ℂ := fun t => qsRegularizedMellinProduct (K := K) h
    ((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) * Complex.I)
  have hRawInt : Integrable (fun t : ℝ => qsRegularizedMellinProduct (K := K) h
      ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    qsRegularizedMellinProduct_line_integrable (K := K) h hh σ σ hσ le_rfl σ
      ⟨le_rfl, le_rfl⟩
  have hFInt : Integrable F := by
    have h := hRawInt.comp_mul_left' (by positivity : 2 * Real.pi ≠ 0)
    simpa [F, mul_assoc] using h
  have hMom : ∀ k : ℕ, Integrable (fun t : ℝ => |t| ^ k * ‖F t‖) := by
    intro k
    simpa [F] using qsRegularizedMellinProduct_line_moment_integrable
      (K := K) h hh σ hσ k
  have hVecAEStronglyMeasurable (k : ℕ) :
      AEStronglyMeasurable (fun t : ℝ => (t : ℝ) ^ k • F t) := by
    have hscalar : AEStronglyMeasurable (fun t : ℝ => (t : ℝ) ^ k) :=
      (continuous_id.pow k).aestronglyMeasurable
    exact hscalar.smul hFInt.1
  have hVecInt (k : ℕ) : Integrable (fun t : ℝ => (t : ℝ) ^ k • F t) := by
    apply (integrable_norm_iff (hVecAEStronglyMeasurable k)).mp
    simpa [norm_smul, norm_pow, RCLike.norm_ofReal, abs_pow] using hMom k
  let W : ℝ → ℂ := fun t => (-2 * Real.pi * Complex.I * (t : ℂ)) ^ n • F t
  have hWeq : W = fun t : ℝ =>
      ((-2 * Real.pi * Complex.I) ^ n) • ((t : ℂ) ^ n • F t) := by
    funext t
    dsimp [W]
    rw [mul_pow]
    simp [smul_smul, mul_assoc]
  have hVecIntC : Integrable (fun t : ℝ => (t : ℂ) ^ n • F t) := by
    simpa [Complex.ofReal_pow] using hVecInt n
  have hWInt : Integrable W := by
    rw [hWeq]
    exact hVecIntC.const_mul ((-2 * Real.pi * Complex.I) ^ n)
  let C : ℝ := ∫ t : ℝ, ‖W t‖
  have hC : 0 ≤ C := by dsimp [C]; exact integral_nonneg (fun t => norm_nonneg _)
  have hFourierDeriv := Real.iteratedDeriv_fourier (f := F) (N := ⊤) (n := n)
    (fun k hk => hVecInt k) (by simp)
  have hFourierBound (y : ℝ) : ‖iteratedDeriv n (𝓕 F) y‖ ≤ C := by
    rw [congrFun hFourierDeriv y, Real.fourier_eq]
    calc
      ‖∫ t : ℝ, 𝐞 (-⟪t, y⟫) • W t‖ ≤
          ∫ t : ℝ, ‖𝐞 (-⟪t, y⟫) • W t‖ := norm_integral_le_integral_norm _
      _ = C := by simp [C, W, Circle.norm_smul]
  have hInvEq : (𝓕⁻ F) = fun y : ℝ => 𝓕 F (-y) := by
    funext y
    exact Real.fourierInv_eq_fourier_neg F y
  have hInvDeriv (y : ℝ) :
      iteratedDeriv n (𝓕⁻ F) y = (-1 : ℝ) ^ n • iteratedDeriv n (𝓕 F) (-y) := by
    rw [hInvEq]
    exact iteratedDeriv_comp_neg n (𝓕 F) y
  refine ⟨C, hC, ?_⟩
  intro y
  rw [hInvDeriv, norm_smul]
  have hnorm : ‖(-1 : ℝ) ^ n‖ = 1 := by simp
  rw [hnorm, one_mul]
  exact hFourierBound (-y)

private def qsLogDerivativeRate (σ : ℝ) : ℕ → ℝ
  | 0 => σ
  | n + 1 => qsLogDerivativeRate σ n + 1

private lemma qsLogDerivativeRate_eq (σ : ℝ) (n : ℕ) :
    qsLogDerivativeRate σ n = σ + (n : ℝ) := by
  induction n with
  | zero => simp [qsLogDerivativeRate]
  | succ n ih => simp [qsLogDerivativeRate, ih, Nat.cast_succ]; ring

private noncomputable def qsLogDerivativeProfile (σ : ℝ) (ψ : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun v => ψ v
  | n + 1 => fun v =>
      -((qsLogDerivativeRate σ n : ℝ) : ℂ) * qsLogDerivativeProfile σ ψ n v -
        deriv (qsLogDerivativeProfile σ ψ n) v

private lemma qsContDiff_deriv_of_top {f : ℝ → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro k hk
  have h := hf.differentiable_iteratedDeriv (k + 1) <|
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (k + 1))
  simpa only [← iteratedDeriv_succ'] using h

private lemma qsLogDerivativeProfile_contDiff (σ : ℝ) (ψ : ℝ → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (qsLogDerivativeProfile σ ψ n) := by
  induction n with
  | zero =>
      dsimp [qsLogDerivativeProfile]
      exact hψ.comp (by fun_prop)
  | succ n ih =>
      have hderiv := qsContDiff_deriv_of_top ih
      change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v => -((qsLogDerivativeRate σ n : ℝ) : ℂ) * qsLogDerivativeProfile σ ψ n v -
          deriv (qsLogDerivativeProfile σ ψ n) v)
      fun_prop

private lemma qsLogDerivativeProfile_bounded_derivs (σ : ℝ) (ψ : ℝ → ℂ)
    (hψCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψ : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
      ‖iteratedDeriv k ψ v‖ ≤ C) :
    ∀ j k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
      ‖iteratedDeriv k (qsLogDerivativeProfile σ ψ j) v‖ ≤ C := by
  intro j
  induction j with
  | zero =>
      intro k
      obtain ⟨C, hC, hB⟩ := hψ k
      refine ⟨C, hC, ?_⟩
      intro v
      dsimp [qsLogDerivativeProfile]
      exact hB v
  | succ j ih =>
      intro k
      obtain ⟨C₁, hC₁, hB₁⟩ := ih k
      obtain ⟨C₂, hC₂, hB₂⟩ := ih (k + 1)
      let c : ℂ := -((qsLogDerivativeRate σ j : ℝ) : ℂ)
      let C : ℝ := ‖c‖ * C₁ + C₂
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hQcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (qsLogDerivativeProfile σ ψ j) := qsLogDerivativeProfile_contDiff σ ψ hψCont j
      have hDcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (deriv (qsLogDerivativeProfile σ ψ j)) := qsContDiff_deriv_of_top hQcont
      have hFormula (v : ℝ) :
          iteratedDeriv k (qsLogDerivativeProfile σ ψ (j + 1)) v =
            c * iteratedDeriv k (qsLogDerivativeProfile σ ψ j) v -
              iteratedDeriv (k + 1) (qsLogDerivativeProfile σ ψ j) v := by
        change iteratedDeriv k
          ((fun v : ℝ => c * qsLogDerivativeProfile σ ψ j v) -
            deriv (qsLogDerivativeProfile σ ψ j)) v = _
        have hdeg : (k : WithTop ℕ∞) ≤ (⊤ : ℕ∞) :=
          WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ ⊤)
        have hQAt : ContDiffAt ℝ k (qsLogDerivativeProfile σ ψ j) v :=
          (hQcont.of_le hdeg).contDiffAt
        have hDAt : ContDiffAt ℝ k
            (deriv (qsLogDerivativeProfile σ ψ j)) v :=
          (hDcont.of_le hdeg).contDiffAt
        have hMulAt : ContDiffAt ℝ k
            (fun v : ℝ => c * qsLogDerivativeProfile σ ψ j v) v := by
          fun_prop
        rw [iteratedDeriv_sub hMulAt hDAt, iteratedDeriv_const_mul_field,
          ← iteratedDeriv_succ']
      refine ⟨C, hC, ?_⟩
      intro v
      rw [hFormula]
      calc
        ‖c * iteratedDeriv k (qsLogDerivativeProfile σ ψ j) v -
            iteratedDeriv (k + 1) (qsLogDerivativeProfile σ ψ j) v‖ ≤
            ‖c * iteratedDeriv k (qsLogDerivativeProfile σ ψ j) v‖ +
              ‖iteratedDeriv (k + 1) (qsLogDerivativeProfile σ ψ j) v‖ := norm_sub_le _ _
        _ ≤ C := by
          calc
            _ = ‖c‖ * ‖iteratedDeriv k (qsLogDerivativeProfile σ ψ j) v‖ +
                ‖iteratedDeriv (k + 1) (qsLogDerivativeProfile σ ψ j) v‖ := by rw [norm_mul]
            _ ≤ ‖c‖ * C₁ + C₂ := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left (hB₁ v) (norm_nonneg _)) (hB₂ v)
            _ = C := by rfl

set_option maxHeartbeats 10000000 in
private lemma qsRegularizedMellinInv_shift_ordered [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (x : ℝ) (hx : 0 < x)
    (σ τ : ℝ) (hστ : σ ≤ τ) (hσ : 0 < σ) :
    mellinInv σ (qsRegularizedMellinProduct (K := K) h) x =
      mellinInv τ (qsRegularizedMellinProduct (K := K) h) x := by
  by_cases hst : σ = τ
  · subst τ
    rfl
  have hστ' : σ < τ := lt_of_le_of_ne hστ hst
  have hτ : 0 < τ := lt_of_lt_of_le hσ hστ
  let F : ℂ → ℂ := fun z => (x : ℂ) ^ (-z) * qsRegularizedMellinProduct (K := K) h z
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpow : Differentiable ℂ (fun z : ℂ => (x : ℂ) ^ (-z)) := by
    intro z
    exact differentiableAt_id.neg.const_cpow (Or.inl hxne)
  have hFdiff (z : ℂ) (hz : 0 < z.re) : DifferentiableAt ℂ F z := by
    have hp := hpow z
    have hr := qsRegularizedMellinProduct_differentiableAt (K := K) h hh z hz
    exact hp.mul hr
  let powFn : ℝ → ℝ := fun q => x ^ (-q)
  have hpowCont : Continuous powFn := by
    dsimp [powFn]
    exact (Real.continuous_const_rpow hx.ne').comp continuous_neg
  obtain ⟨Bpow, hBpow⟩ := isCompact_Icc.bddAbove_image hpowCont.continuousOn
  let Mx : ℝ := max Bpow 1
  have hMx : 0 < Mx := by dsimp [Mx]; positivity
  have hpowBound (q : ℝ) (hq : q ∈ Set.Icc σ τ) : powFn q ≤ Mx := by
    have hupper : ∀ y ∈ powFn '' Set.Icc σ τ, y ≤ Bpow := hBpow
    have hm : powFn q ∈ powFn '' Set.Icc σ τ := ⟨q, hq, rfl⟩
    exact (hupper _ hm).trans (le_max_left _ _)
  have hRegTail : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Set.Icc σ τ →
      2 * Real.pi ≤ |z.im| →
      ‖qsRegularizedMellinProduct (K := K) h z‖ ≤ C / |z.im| ^ 3 :=
    qsRegularizedMellinProduct_vertical_decay (K := K) h hh σ τ hσ hστ 3
  rcases hRegTail with ⟨C, hC, hTail⟩
  let L : ℝ := Mx * C * |τ - σ|
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let Hbot : ℝ → ℂ := fun T => ∫ q : ℝ in σ..τ, F ((q : ℂ) + (-T : ℂ) * Complex.I)
  let Htop : ℝ → ℂ := fun T => ∫ q : ℝ in σ..τ, F ((q : ℂ) + (T : ℂ) * Complex.I)
  let Ileft : ℝ → ℂ := fun T => ∫ y : ℝ in (-T)..T,
    F ((σ : ℂ) + (y : ℂ) * Complex.I)
  let Iright : ℝ → ℂ := fun T => ∫ y : ℝ in (-T)..T,
    F ((τ : ℂ) + (y : ℂ) * Complex.I)
  have hTopBound (T : ℝ) (hT : 2 * Real.pi ≤ T) : ‖Htop T‖ ≤ L / T ^ 3 := by
    change ‖∫ q : ℝ in σ..τ, F ((q : ℂ) + (T : ℂ) * Complex.I)‖ ≤ L / T ^ 3
    have hPointCap : ∀ q ∈ Set.uIoc σ τ,
        ‖F ((q : ℂ) + (T : ℂ) * Complex.I)‖ ≤ Mx * (C / T ^ 3) := by
      intro q hq
      have hqIoc : q ∈ Set.Ioc σ τ := by simpa [Set.uIoc_of_le hστ] using hq
      have hqIcc : q ∈ Set.Icc σ τ := ⟨le_of_lt hqIoc.1, hqIoc.2⟩
      have hzre : (((q : ℂ) + (T : ℂ) * Complex.I).re) = q := by simp
      have hzim : (((q : ℂ) + (T : ℂ) * Complex.I).im) = T := by simp
      have hTnonneg : 0 ≤ T := by linarith [Real.pi_gt_three]
      have hR := hTail ((q : ℂ) + (T : ℂ) * Complex.I) (by rw [hzre]; exact hqIcc)
        (by rw [hzim, abs_of_nonneg hTnonneg]; exact hT)
      have hR' :
          ‖qsRegularizedMellinProduct (K := K) h ((q : ℂ) + (T : ℂ) * Complex.I)‖ ≤ C / T ^ 3 := by
        rw [hzim, abs_of_nonneg hTnonneg] at hR
        exact hR
      have hpowNorm : ‖(x : ℂ) ^ (-((q : ℂ) + (T : ℂ) * Complex.I))‖ = powFn q := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
        simp [powFn]
      calc
        ‖F ((q : ℂ) + (T : ℂ) * Complex.I)‖ =
            ‖(x : ℂ) ^ (-((q : ℂ) + (T : ℂ) * Complex.I))‖ *
              ‖qsRegularizedMellinProduct (K := K) h ((q : ℂ) + (T : ℂ) * Complex.I)‖ := by
                simp [F, norm_mul]
        _ ≤ powFn q * ‖qsRegularizedMellinProduct (K := K) h
              ((q : ℂ) + (T : ℂ) * Complex.I)‖ := by rw [hpowNorm]
        _ ≤ powFn q * (C / T ^ 3) :=
          mul_le_mul_of_nonneg_left hR' (by positivity)
        _ ≤ Mx * (C / T ^ 3) :=
          mul_le_mul_of_nonneg_right (hpowBound q hqIcc) (by positivity)
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hPointCap
    calc
      ‖∫ q : ℝ in σ..τ, F ((q : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          Mx * (C / T ^ 3) * |τ - σ| := hI
      _ = L / T ^ 3 := by dsimp [L]; ring
  have hBotBound (T : ℝ) (hT : 2 * Real.pi ≤ T) : ‖Hbot T‖ ≤ L / T ^ 3 := by
    change ‖∫ q : ℝ in σ..τ, F ((q : ℂ) + (-T : ℂ) * Complex.I)‖ ≤ L / T ^ 3
    have hPointCap : ∀ q ∈ Set.uIoc σ τ,
        ‖F ((q : ℂ) + (-T : ℂ) * Complex.I)‖ ≤ Mx * (C / T ^ 3) := by
      intro q hq
      have hqIoc : q ∈ Set.Ioc σ τ := by simpa [Set.uIoc_of_le hστ] using hq
      have hqIcc : q ∈ Set.Icc σ τ := ⟨le_of_lt hqIoc.1, hqIoc.2⟩
      have hzre : (((q : ℂ) + (-T : ℂ) * Complex.I).re) = q := by simp
      have hzim : (((q : ℂ) + (-T : ℂ) * Complex.I).im) = -T := by simp
      have hTnonneg : 0 ≤ T := by linarith [Real.pi_gt_three]
      have hR := hTail ((q : ℂ) + (-T : ℂ) * Complex.I) (by rw [hzre]; exact hqIcc)
        (by rw [hzim, abs_neg, abs_of_nonneg hTnonneg]; exact hT)
      have hR' :
          ‖qsRegularizedMellinProduct (K := K) h ((q : ℂ) + (-T : ℂ) * Complex.I)‖ ≤ C / T ^ 3 := by
        rw [hzim, abs_neg, abs_of_nonneg hTnonneg] at hR
        exact hR
      have hpowNorm : ‖(x : ℂ) ^ (-((q : ℂ) + (-T : ℂ) * Complex.I))‖ = powFn q := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
        simp [powFn]
      calc
        ‖F ((q : ℂ) + (-T : ℂ) * Complex.I)‖ =
            ‖(x : ℂ) ^ (-((q : ℂ) + (-T : ℂ) * Complex.I))‖ *
              ‖qsRegularizedMellinProduct (K := K) h ((q : ℂ) + (-T : ℂ) * Complex.I)‖ := by
                simp [F, norm_mul]
        _ ≤ powFn q * ‖qsRegularizedMellinProduct (K := K) h
              ((q : ℂ) + (-T : ℂ) * Complex.I)‖ := by rw [hpowNorm]
        _ ≤ powFn q * (C / T ^ 3) :=
          mul_le_mul_of_nonneg_left hR' (by positivity)
        _ ≤ Mx * (C / T ^ 3) :=
          mul_le_mul_of_nonneg_right (hpowBound q hqIcc) (by positivity)
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hPointCap
    calc
      ‖∫ q : ℝ in σ..τ, F ((q : ℂ) + (-T : ℂ) * Complex.I)‖ ≤
          Mx * (C / T ^ 3) * |τ - σ| := hI
      _ = L / T ^ 3 := by dsimp [L]; ring
  have hpowAtTop : Tendsto (fun T : ℝ => T ^ 3) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hInvAtTop : Tendsto (fun T : ℝ => (T ^ 3)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpowAtTop
  have hCapAtTop : Tendsto (fun T : ℝ => L / T ^ 3) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hInvAtTop
  have hTopNormTendsto : Tendsto (fun T : ℝ => ‖Htop T‖) atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro c hc
      filter_upwards with T
      exact lt_of_lt_of_le hc (norm_nonneg _)
    · intro c hc
      filter_upwards [eventually_ge_atTop (2 * Real.pi), hCapAtTop.eventually (Iio_mem_nhds hc)]
        with T hT hsmall
      exact (hTopBound T hT).trans_lt hsmall
  have hBotNormTendsto : Tendsto (fun T : ℝ => ‖Hbot T‖) atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro c hc
      filter_upwards with T
      exact lt_of_lt_of_le hc (norm_nonneg _)
    · intro c hc
      filter_upwards [eventually_ge_atTop (2 * Real.pi), hCapAtTop.eventually (Iio_mem_nhds hc)]
        with T hT hsmall
      exact (hBotBound T hT).trans_lt hsmall
  have hTopTendsto : Tendsto Htop atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact hTopNormTendsto
  have hBotTendsto : Tendsto Hbot atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact hBotNormTendsto
  have hFdiffOn (T : ℝ) (hT : 0 ≤ T) :
      DifferentiableOn ℂ F
        (Set.Icc σ τ ×ℂ Set.Icc (-T) T) := by
    intro z hz
    rcases (Complex.mem_reProdIm.mp hz) with ⟨hzre, hzim⟩
    have hzpos : 0 < z.re := lt_of_lt_of_le hσ hzre.1
    exact (hFdiff z hzpos).differentiableWithinAt
  have hRect (T : ℝ) (hT : 0 ≤ T) :
      Hbot T - Htop T + Complex.I • Iright T - Complex.I • Ileft T = 0 := by
    let z : ℂ := (σ : ℂ) + (-T : ℂ) * Complex.I
    let w : ℂ := (τ : ℂ) + (T : ℂ) * Complex.I
    have hdiffRect : DifferentiableOn ℂ F
        (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
      simpa [z, w, Set.uIcc_of_le hστ,
        Set.uIcc_of_le (neg_le_self hT)] using hFdiffOn T hT
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hdiffRect
    simpa [Hbot, Htop, Ileft, Iright, z, w, F, smul_eq_mul] using h
  have hleftInt : Integrable (fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
    have hReg := qsRegularizedMellinProduct_line_integrable (K := K) h hh σ τ hσ hστ σ
      ⟨le_rfl, hστ⟩
    have hPowBound : ∀ y : ℝ,
        ‖(x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))‖ ≤ x ^ (-σ) := by
      intro y
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    have hPowMeas : AEStronglyMeasurable (fun y : ℝ =>
        (x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))) := by
      apply Continuous.aestronglyMeasurable
      apply continuous_iff_continuousAt.mpr
      intro y
      have hline : ContinuousAt (fun y : ℝ => (σ : ℂ) + (y : ℂ) * Complex.I) y := by fun_prop
      have hcomp := ContinuousAt.comp_of_eq (hpow ((σ : ℂ) + (y : ℂ) * Complex.I)).continuousAt
        hline (by rfl)
      simpa [Function.comp_def] using hcomp
    have hMult := hReg.bdd_mul (c := x ^ (-σ)) hPowMeas (Filter.Eventually.of_forall hPowBound)
    simpa [F] using hMult
  have hrightInt : Integrable (fun y : ℝ => F ((τ : ℂ) + (y : ℂ) * Complex.I)) := by
    have hReg := qsRegularizedMellinProduct_line_integrable (K := K) h hh σ τ hσ hστ τ
      ⟨hστ, le_rfl⟩
    have hPowBound : ∀ y : ℝ,
        ‖(x : ℂ) ^ (-((τ : ℂ) + (y : ℂ) * Complex.I))‖ ≤ x ^ (-τ) := by
      intro y
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    have hPowMeas : AEStronglyMeasurable (fun y : ℝ =>
        (x : ℂ) ^ (-((τ : ℂ) + (y : ℂ) * Complex.I))) := by
      apply Continuous.aestronglyMeasurable
      apply continuous_iff_continuousAt.mpr
      intro y
      have hline : ContinuousAt (fun y : ℝ => (τ : ℂ) + (y : ℂ) * Complex.I) y := by fun_prop
      have hcomp := ContinuousAt.comp_of_eq (hpow ((τ : ℂ) + (y : ℂ) * Complex.I)).continuousAt
        hline (by rfl)
      simpa [Function.comp_def] using hcomp
    have hMult := hReg.bdd_mul (c := x ^ (-τ)) hPowMeas (Filter.Eventually.of_forall hPowBound)
    simpa [F] using hMult
  have hIleftTendsto : Tendsto Ileft atTop
      (𝓝 (∫ y : ℝ, F ((σ : ℂ) + (y : ℂ) * Complex.I))) := by
    simpa [Ileft] using intervalIntegral_tendsto_integral hleftInt
      tendsto_neg_atTop_atBot tendsto_id
  have hIrightTendsto : Tendsto Iright atTop
      (𝓝 (∫ y : ℝ, F ((τ : ℂ) + (y : ℂ) * Complex.I))) := by
    simpa [Iright] using intervalIntegral_tendsto_integral hrightInt
      tendsto_neg_atTop_atBot tendsto_id
  have hVerticalDiffZero : Tendsto (fun T : ℝ => Iright T - Ileft T) atTop (𝓝 0) := by
    have hHdiff : Tendsto (fun T : ℝ => Htop T - Hbot T) atTop (𝓝 0) := by
      simpa using hTopTendsto.sub hBotTendsto
    have heq : ∀ᶠ T : ℝ in atTop,
        Iright T - Ileft T = -Complex.I * (Htop T - Hbot T) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      have hEq := hRect T hT
      have hEq' : Complex.I * (Iright T - Ileft T) = Htop T - Hbot T := by
        dsimp [Hbot, Htop, Ileft, Iright] at hEq ⊢
        linear_combination hEq
      calc
        Iright T - Ileft T = Complex.I⁻¹ *
            (Complex.I * (Iright T - Ileft T)) := by field_simp
        _ = Complex.I⁻¹ * (Htop T - Hbot T) := by rw [hEq']
        _ = -Complex.I * (Htop T - Hbot T) := by simp
    have hcomp : Tendsto (fun T : ℝ => -Complex.I * (Htop T - Hbot T)) atTop (𝓝 0) := by
      simpa [mul_comm] using hHdiff.const_mul (-Complex.I)
    exact hcomp.congr' (heq.mono fun _ h => h.symm)
  have hfullEq :
      (∫ y : ℝ, F ((τ : ℂ) + (y : ℂ) * Complex.I)) =
        ∫ y : ℝ, F ((σ : ℂ) + (y : ℂ) * Complex.I) := by
    have hlim := hIrightTendsto.sub hIleftTendsto
    have hzero := tendsto_nhds_unique hlim hVerticalDiffZero
    exact sub_eq_zero.mp hzero
  have hInvLine (ρ : ℝ) :
      mellinInv ρ (qsRegularizedMellinProduct (K := K) h) x =
        (1 / (2 * Real.pi) : ℂ) • ∫ y : ℝ,
          F ((ρ : ℂ) + (y : ℂ) * Complex.I) := by
    simp [mellinInv, F, smul_eq_mul]
  rw [hInvLine σ, hInvLine τ, hfullEq]

private lemma qsRegularizedMellinInv_shift [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (x : ℝ) (hx : 0 < x)
    (σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
    mellinInv σ (qsRegularizedMellinProduct (K := K) h) x =
      mellinInv τ (qsRegularizedMellinProduct (K := K) h) x := by
  by_cases hστ : σ ≤ τ
  · exact qsRegularizedMellinInv_shift_ordered (K := K) h hh x hx σ τ hστ hσ
  · have hτσ : τ ≤ σ := le_of_not_ge hστ
    exact (qsRegularizedMellinInv_shift_ordered (K := K) h hh x hx τ σ hτσ hτ).symm

private lemma qs_transform_eq_regularizedFourierInv [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (x : ℝ) (hx : 0 < x)
    (σ : ℝ) (hσ : 0 < σ) :
    qsTransform K h x = (x : ℂ) ^ (-σ : ℂ) •
      𝓕⁻ (fun y : ℝ => qsRegularizedMellinProduct (K := K) h
        ((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I)) (-Real.log x) := by
  let Fraw : ℂ → ℂ := fun u => qsGammaRatio K u * mellin h (1 - u)
  have hCentral : mellinInv (1 / 2 : ℝ) Fraw x =
      mellinInv (1 / 2 : ℝ) (qsRegularizedMellinProduct (K := K) h) x := by
    unfold mellinInv
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    let u : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
    have huRe : u.re = 1 / 2 := by simp [u]
    have hEq := qsRegularizedMellinProduct_eq_original (K := K) h hh u
      (by rw [huRe]; norm_num) (by rw [huRe]; norm_num)
    have hPoint : Fraw u = qsRegularizedMellinProduct (K := K) h u := by
      simpa [Fraw] using hEq.symm
    have hPoint' :
        Fraw (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
          qsRegularizedMellinProduct (K := K) h (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      simpa [u] using hPoint
    change (x : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) •
        Fraw (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      (x : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) •
        qsRegularizedMellinProduct (K := K) h (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    exact congrArg (fun v : ℂ =>
      (x : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) • v) hPoint'
  have hShift := qsRegularizedMellinInv_shift (K := K) h hh x hx
    (1 / 2) σ (by norm_num) hσ
  have hInv := mellinInv_eq_fourierInv σ (qsRegularizedMellinProduct (K := K) h) hx
  calc
    qsTransform K h x = mellinInv (1 / 2 : ℝ) Fraw x := by rfl
    _ = mellinInv (1 / 2 : ℝ) (qsRegularizedMellinProduct (K := K) h) x := hCentral
    _ = mellinInv σ (qsRegularizedMellinProduct (K := K) h) x := hShift
    _ = (x : ℂ) ^ (-σ : ℂ) •
        𝓕⁻ (fun y : ℝ => qsRegularizedMellinProduct (K := K) h
          ((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I))
          (-Real.log x) := hInv

set_option maxHeartbeats 10000000 in
private lemma qs_transform_iteratedDeriv_log_relation (T : ℝ → ℂ)
    (hT : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T (Set.Ioi 0))
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (σ : ℝ)
    (hFormula : ∀ x : ℝ, 0 < x →
      T x = ((x ^ (-(σ : ℝ)) : ℝ) : ℂ) * ψ (-Real.log x)) :
    ∀ j : ℕ, ∀ v : ℝ,
      iteratedDeriv j T (Real.exp (-v)) =
        ((Real.exp (qsLogDerivativeRate σ j * v) : ℝ) : ℂ) *
          qsLogDerivativeProfile σ ψ j v := by
  intro j
  induction j with
  | zero =>
      intro v
      have hpow : (Real.exp (-v)) ^ (-(σ : ℝ)) = Real.exp (σ * v) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 1
        ring
      calc
        iteratedDeriv 0 T (Real.exp (-v)) = T (Real.exp (-v)) := by simp
        _ = ((Real.exp (-v) ^ (-(σ : ℝ)) : ℝ) : ℂ) *
            ψ (-Real.log (Real.exp (-v))) := hFormula _ (Real.exp_pos _)
        _ = ((Real.exp (σ * v) : ℝ) : ℂ) * ψ v := by simp [hpow, Real.log_exp]
        _ = ((Real.exp (qsLogDerivativeRate σ 0 * v) : ℝ) : ℂ) *
            qsLogDerivativeProfile σ ψ 0 v := by
              simp [qsLogDerivativeRate, qsLogDerivativeProfile]
  | succ j ih =>
      intro v
      let a : ℝ := qsLogDerivativeRate σ j
      let q : ℝ → ℂ := qsLogDerivativeProfile σ ψ j
      have hqCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q := by
        simpa [q] using qsLogDerivativeProfile_contDiff σ ψ hψ j
      have hqDiffCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv q) :=
        qsContDiff_deriv_of_top hqCont
      have hTjDiff : DifferentiableAt ℝ (iteratedDeriv j T) (Real.exp (-v)) := by
        have hlt : (j : WithTop ℕ∞) < (⊤ : ℕ∞) :=
          WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)
        have hx : Real.exp (-v) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (Real.exp_pos _)
        have hTAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T (Real.exp (-v)) :=
          hT.contDiffAt (isOpen_Ioi.mem_nhds hx)
        have hWithin := hTAt.differentiableWithinAt_iteratedDerivWithin hlt
          (by simp [uniqueDiffOn_univ])
        have hAt := hWithin.differentiableAt (by simp)
        simpa only [iteratedDerivWithin_univ] using hAt
      have hOuter : HasDerivAt (iteratedDeriv j T)
          (iteratedDeriv (j + 1) T (Real.exp (-v))) (Real.exp (-v)) := by
        simpa only [iteratedDeriv_succ] using hTjDiff.hasDerivAt
      have hInner : HasDerivAt (fun w : ℝ => Real.exp (-w))
          (-Real.exp (-v)) v := by
        have h := HasDerivAt.comp v (Real.hasDerivAt_exp (-v)) (hasDerivAt_neg v)
        simpa [Function.comp_def, mul_comm] using h
      have hLeftDeriv :
          deriv (fun w : ℝ => iteratedDeriv j T (Real.exp (-w))) v =
            iteratedDeriv (j + 1) T (Real.exp (-v)) * (-Real.exp (-v)) := by
        simpa [Function.comp_def, smul_eq_mul, mul_comm] using
          (HasDerivAt.scomp v hOuter hInner).deriv
      have hEqFun : (fun w : ℝ => iteratedDeriv j T (Real.exp (-w))) =
          fun w => ((Real.exp (a * w) : ℝ) : ℂ) * q w := by
        funext w
        simpa [q, a] using ih w
      have hDerivEq := congrArg (fun f : ℝ → ℂ => deriv f v) hEqFun
      have hExpReal : HasDerivAt (fun w : ℝ => Real.exp (a * w))
          (a * Real.exp (a * v)) v := by
        have hlin : HasDerivAt (fun w : ℝ => a * w) a v := by
          simpa [mul_comm] using (hasDerivAt_id v).const_mul a
        have h := HasDerivAt.comp v (Real.hasDerivAt_exp (a * v)) hlin
        simpa [Function.comp_def, mul_comm] using h
      have hExp : HasDerivAt (fun w : ℝ => (Real.exp (a * w) : ℂ))
          ((a * Real.exp (a * v) : ℝ) : ℂ) v := hExpReal.ofReal_comp
      have hqAt : HasDerivAt q (deriv q v) v :=
        (hqCont.differentiable (by simp)) v |>.hasDerivAt
      have hRightDeriv : HasDerivAt
          (fun w : ℝ => (Real.exp (a * w) : ℂ) * q w)
          (((a * Real.exp (a * v) : ℝ) : ℂ) * q v +
            (Real.exp (a * v) : ℂ) * deriv q v) v := hExp.mul hqAt
      have hMain : iteratedDeriv (j + 1) T (Real.exp (-v)) *
          (-(Real.exp (-v) : ℂ)) =
        ((a * Real.exp (a * v) : ℝ) : ℂ) * q v +
          (Real.exp (a * v) : ℂ) * deriv q v := by
        calc
          _ = deriv (fun w : ℝ => iteratedDeriv j T (Real.exp (-w))) v := hLeftDeriv.symm
          _ = deriv (fun w : ℝ => (Real.exp (a * w) : ℂ) * q w) v := hDerivEq
          _ = _ := hRightDeriv.deriv
      have he : (Real.exp (-v) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
      have hExpQuot : (Real.exp (a * v) : ℂ) / (Real.exp (-v) : ℂ) =
          (Real.exp ((a + 1) * v) : ℂ) := by
        rw [Complex.ofReal_exp, Complex.ofReal_exp, Complex.ofReal_exp]
        apply (div_eq_iff (Complex.exp_ne_zero _)).2
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      have hsolve : iteratedDeriv (j + 1) T (Real.exp (-v)) =
          -((Real.exp ((a + 1) * v) : ℝ) : ℂ) *
            (((a : ℂ) * q v) + deriv q v) := by
        calc
          _ = (iteratedDeriv (j + 1) T (Real.exp (-v)) *
              (-(Real.exp (-v) : ℂ))) / (-(Real.exp (-v) : ℂ)) := by
                field_simp [he]
          _ = -(((a * Real.exp (a * v) : ℝ) : ℂ) * q v +
              (Real.exp (a * v) : ℂ) * deriv q v) / (Real.exp (-v) : ℂ) := by
                rw [hMain]
                ring
          _ = -((Real.exp (a * v) : ℂ) / (Real.exp (-v) : ℂ)) *
              ((a : ℂ) * q v + deriv q v) := by
                rw [Complex.ofReal_mul]
                ring_nf
          _ = _ := by rw [hExpQuot]
      calc
        iteratedDeriv (j + 1) T (Real.exp (-v)) =
            -((Real.exp ((a + 1) * v) : ℝ) : ℂ) *
              (((a : ℂ) * q v) + deriv q v) := hsolve
        _ = ((Real.exp (qsLogDerivativeRate σ (j + 1) * v) : ℝ) : ℂ) *
            qsLogDerivativeProfile σ ψ (j + 1) v := by
              have harg : (a + 1) * v = qsLogDerivativeRate σ (j + 1) * v := by
                simp [a, qsLogDerivativeRate]
              rw [harg]
              dsimp [q, qsLogDerivativeProfile, a]
              ring_nf

private lemma qsRegularizedFourierInv_contDiff [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (σ : ℝ) (hσ : 0 < σ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (𝓕⁻ (fun y : ℝ => qsRegularizedMellinProduct (K := K) h
        ((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I))) := by
  let F : ℝ → ℂ := fun y => qsRegularizedMellinProduct (K := K) h
    ((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I)
  have hMom : ∀ n : ℕ, Integrable (fun y : ℝ => |y| ^ n * ‖F y‖) := by
    intro n
    simpa [F] using qsRegularizedMellinProduct_line_moment_integrable
      (K := K) h hh σ hσ n
  have hFourier : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓕 F) := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) F)
    exact Real.contDiff_fourier (f := F) (fun n _ => hMom n)
  have hInvEq : (𝓕⁻ F) = fun v : ℝ => 𝓕 F (-v) := by
    funext v
    exact Real.fourierInv_eq_fourier_neg F v
  rw [hInvEq]
  exact hFourier.comp (by fun_prop)

private lemma qs_transform_eq_fourierInv_line [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (x : ℝ) (hx : 0 < x) :
    qsTransform K h x = (x : ℂ) ^ (-(1 / 2 : ℂ)) •
      𝓕⁻ (qsMellinTransformLine K h) (-Real.log x) := by
  let Fraw : ℝ → ℂ := fun y : ℝ =>
    qsGammaRatio K (((1 / 2 : ℝ) : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I) *
      mellin h (1 - (((1 / 2 : ℝ) : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I))
  have hFdef : Fraw = qsMellinTransformLine K h := by
    funext y
    dsimp [Fraw, qsMellinTransformLine]
    congr 1 <;> push_cast <;> ring
  have hInvEq : 𝓕⁻ Fraw (-Real.log x) =
      𝓕⁻ (qsMellinTransformLine K h) (-Real.log x) := by
    exact congrArg (fun f : ℝ → ℂ => 𝓕⁻ f (-Real.log x)) hFdef
  have hmi := mellinInv_eq_fourierInv (1 / 2 : ℝ)
    (fun s : ℂ => qsGammaRatio K s * mellin h (1 - s)) hx
  calc
    qsTransform K h x = (x : ℂ) ^ (-(1 / 2 : ℂ)) • 𝓕⁻ Fraw (-Real.log x) := by
      simpa [qsTransform, Fraw] using hmi
    _ = (x : ℂ) ^ (-(1 / 2 : ℂ)) •
        𝓕⁻ (qsMellinTransformLine K h) (-Real.log x) := by rw [hInvEq]

private lemma qs_transform_contDiffOn [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (qsTransform K h) (Set.Ioi 0) := by
  let F : ℝ → ℂ := qsMellinTransformLine K h
  have hMom : ∀ n : ℕ, Integrable (fun y : ℝ => |y| ^ n * ‖F y‖) :=
    fun n => qs_mellin_transform_line_moment_integrable (K := K) h hh n
  have hFourier : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓕 F) := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) F)
    exact Real.contDiff_fourier (f := F) (fun n _ => hMom n)
  have hInv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓕⁻ F) := by
    have hEq : (𝓕⁻ F) = fun v : ℝ => 𝓕 F (-v) := by
      funext v
      exact Real.fourierInv_eq_fourier_neg F v
    rw [hEq]
    exact hFourier.comp (by fun_prop)
  have hScale : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (Set.Ioi 0) := by
    intro x hx
    exact Complex.ofRealCLM.contDiff.comp_contDiffWithinAt
      (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt
  have hLog : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => -Real.log x) (Set.Ioi 0) := by
    have h := Real.contDiffOn_log (n := (⊤ : ℕ∞))
    refine h.neg.mono ?_
    intro x hx
    exact Set.mem_compl_singleton_iff.mpr (ne_of_gt hx)
  have hFormula : Set.EqOn (qsTransform K h)
      (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * 𝓕⁻ F (-Real.log x))
      (Set.Ioi 0) := by
    intro x hx
    have h := qs_transform_eq_fourierInv_line (K := K) h hh x hx
    have hpow : (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      have hc := Complex.ofReal_cpow (le_of_lt hx) (-(1 / 2 : ℝ))
      simpa using hc.symm
    rw [hpow] at h
    simpa [F, RCLike.real_smul_eq_coe_mul] using h
  have hProd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * 𝓕⁻ F (-Real.log x)) (Set.Ioi 0) := by
    exact hScale.mul (hInv.comp_contDiffOn hLog)
  exact hProd.congr (fun x hx => hFormula hx)

private lemma qs_transform_fixed_line_deriv_bound [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (σ : ℝ) (hσ : 0 < σ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖iteratedDeriv j (qsTransform K h) x‖ ≤ C * x ^ (-(σ + (j : ℝ))) := by
  let ψ : ℝ → ℂ := fun y => 𝓕⁻ (fun t : ℝ =>
    qsRegularizedMellinProduct (K := K) h
      ((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) * Complex.I)) y
  have hψCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    qsRegularizedFourierInv_contDiff (K := K) h hh σ hσ
  have hψBound : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
      ‖iteratedDeriv k ψ v‖ ≤ C := by
    intro k
    obtain ⟨C, hC, hBound⟩ :=
      qsRegularizedFourierInv_iteratedDeriv_bound (K := K) h hh σ hσ k
    exact ⟨C, hC, hBound⟩
  have hProfile := qsLogDerivativeProfile_bounded_derivs σ ψ hψCont hψBound
  obtain ⟨C, hC, hProfileBound⟩ := hProfile j 0
  have hTransformCont := qs_transform_contDiffOn (K := K) h hh
  have hFormula : ∀ x : ℝ, 0 < x →
      qsTransform K h x = ((x ^ (-(σ : ℝ)) : ℝ) : ℂ) * ψ (-Real.log x) := by
    intro x hx
    have hInv := qs_transform_eq_regularizedFourierInv (K := K) h hh x hx σ hσ
    have hpow : (x : ℂ) ^ (-(σ : ℂ)) = ((x ^ (-(σ : ℝ)) : ℝ) : ℂ) := by
      have hc := Complex.ofReal_cpow (le_of_lt hx) (-σ)
      simpa using hc.symm
    rw [hpow] at hInv
    simpa [ψ, RCLike.real_smul_eq_coe_mul] using hInv
  refine ⟨C, hC, ?_⟩
  intro x hx
  let v : ℝ := -Real.log x
  have hvx : Real.exp (-v) = x := by
    dsimp [v]
    rw [neg_neg, Real.exp_log hx]
  have hRel := qs_transform_iteratedDeriv_log_relation
    (qsTransform K h) hTransformCont ψ hψCont σ hFormula j v
  rw [hvx] at hRel
  have hExp : Real.exp (qsLogDerivativeRate σ j * v) =
      x ^ (-(σ + (j : ℝ))) := by
    rw [Real.rpow_def_of_pos hx, qsLogDerivativeRate_eq]
    congr 1
    dsimp [v]
    ring
  rw [hRel]
  calc
    ‖((Real.exp (qsLogDerivativeRate σ j * v) : ℝ) : ℂ) *
        qsLogDerivativeProfile σ ψ j v‖ =
        Real.exp (qsLogDerivativeRate σ j * v) *
          ‖qsLogDerivativeProfile σ ψ j v‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    _ ≤ Real.exp (qsLogDerivativeRate σ j * v) * C :=
      mul_le_mul_of_nonneg_left (hProfileBound v) (Real.exp_pos _).le
    _ = C * x ^ (-(σ + (j : ℝ))) := by rw [hExp]; ring

/-- P0 (IMPL): a cap weight exists (found:331). -/
theorem qs_cap_weight_exists_P0 : ∃ W : ℝ → ℝ, IsCapWeight W := by
  let W : ℝ → ℝ := fun x => 1 - Real.smoothTransition ((x - 1) / (3 / 2))
  refine ⟨W, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ⟨5 / 2, ?_⟩, ⟨1, by norm_num, ?_⟩⟩
    · exact Complex.ofRealCLM.contDiff.comp (by
        change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x => 1 - Real.smoothTransition ((x - 1) / (3 / 2)))
        fun_prop)
    · intro x hx
      have harg : 1 ≤ (x - 1) / (3 / 2) := by
        have hden : (0 : ℝ) < 3 / 2 := by norm_num
        rw [le_div_iff₀ hden]
        linarith
      change ((1 - Real.smoothTransition ((x - 1) / (3 / 2)) : ℝ) : ℂ) = 0
      rw [Real.smoothTransition.one_of_one_le harg]
      norm_num
    · intro x hx
      have harg : (x - 1) / (3 / 2) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · linarith [hx.2]
        · norm_num
      change ((1 - Real.smoothTransition ((x - 1) / (3 / 2)) : ℝ) : ℂ) =
        ((1 - Real.smoothTransition ((0 - 1) / (3 / 2)) : ℝ) : ℂ)
      rw [Real.smoothTransition.zero_of_nonpos harg,
        Real.smoothTransition.zero_of_nonpos (by norm_num)]
  · intro x
    dsimp [W]
    linarith [Real.smoothTransition.le_one ((x - 1) / (3 / 2))]
  · intro x hx
    have harg : (x - 1) / (3 / 2) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith [hx.2]
      · norm_num
    simp [W, Real.smoothTransition.zero_of_nonpos harg]
  · intro x hx
    have harg : 1 ≤ (x - 1) / (3 / 2) := by
      have hden : (0 : ℝ) < 3 / 2 := by norm_num
      rw [le_div_iff₀ hden]
      linarith
    simp [W, Real.smoothTransition.one_of_one_le harg]

/-- P0 (IMPL): a dyadic weight exists, and it is a QS weight (found:331-332). -/
theorem qs_dyad_weight_exists_P0 :
    ∃ W : ℝ → ℝ, IsDyadWeight W ∧ IsQSWeight (fun x => (W x : ℂ)) := by
  let W : ℝ → ℝ := fun x =>
    Real.smoothTransition ((x - 1 / 2) / (1 / 2)) *
      (1 - Real.smoothTransition ((x - 2) / (1 / 2)))
  refine ⟨W, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x =>
        Real.smoothTransition ((x - 1 / 2) / (1 / 2)) *
          (1 - Real.smoothTransition ((x - 2) / (1 / 2)))
        )
      fun_prop
    · intro x
      apply mul_nonneg
      · exact Real.smoothTransition.nonneg _
      · linarith [Real.smoothTransition.le_one ((x - 2) / (1 / 2))]
    · intro x hx
      have hleft : 1 ≤ (x - 1 / 2) / (1 / 2) := by
        have hden : (0 : ℝ) < 1 / 2 := by norm_num
        rw [le_div_iff₀ hden]
        linarith [hx.1]
      have hright : (x - 2) / (1 / 2) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · linarith [hx.2]
        · norm_num
      change 1 ≤ Real.smoothTransition ((x - 1 / 2) / (1 / 2)) *
        (1 - Real.smoothTransition ((x - 2) / (1 / 2)))
      rw [Real.smoothTransition.one_of_one_le hleft,
        Real.smoothTransition.zero_of_nonpos hright]
      norm_num
    · intro x hx
      have hout : x ≤ 1 / 2 ∨ 5 / 2 ≤ x := by
        by_contra hn
        push Not at hn
        exact hx ⟨hn.1, hn.2⟩
      rcases hout with hleft | hright
      · have harg : (x - 1 / 2) / (1 / 2) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · linarith
          · norm_num
        change Real.smoothTransition ((x - 1 / 2) / (1 / 2)) *
          (1 - Real.smoothTransition ((x - 2) / (1 / 2))) = 0
        rw [Real.smoothTransition.zero_of_nonpos harg]
        simp
      · have harg : 1 ≤ (x - 2) / (1 / 2) := by
          have hden : (0 : ℝ) < 1 / 2 := by norm_num
          rw [le_div_iff₀ hden]
          linarith
        change Real.smoothTransition ((x - 1 / 2) / (1 / 2)) *
          (1 - Real.smoothTransition ((x - 2) / (1 / 2))) = 0
        rw [Real.smoothTransition.one_of_one_le harg]
        simp
  · refine ⟨?_, ⟨5 / 2, ?_⟩, ⟨1 / 2, by norm_num, ?_⟩⟩
    · exact Complex.ofRealCLM.contDiff.comp (by
        change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x =>
          Real.smoothTransition ((x - 1 / 2) / (1 / 2)) *
            (1 - Real.smoothTransition ((x - 2) / (1 / 2))))
        fun_prop)
    · intro x hx
      have hright : 1 ≤ (x - 2) / (1 / 2) := by
        have hden : (0 : ℝ) < 1 / 2 := by norm_num
        rw [le_div_iff₀ hden]
        linarith
      change ((Real.smoothTransition ((x - 1 / 2) / (1 / 2)) *
        (1 - Real.smoothTransition ((x - 2) / (1 / 2)) : ℝ) : ℝ) : ℂ) = 0
      rw [Real.smoothTransition.one_of_one_le hright]
      norm_num
    · intro x hx
      have hleft : (x - 1 / 2) / (1 / 2) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · linarith [hx.2]
        · norm_num
      have hxW : W x = 0 := by
        dsimp [W]
        rw [Real.smoothTransition.zero_of_nonpos hleft]
        ring
      have h0W : W 0 = 0 := by
        dsimp [W]
        rw [Real.smoothTransition.zero_of_nonpos (by norm_num)]
        ring
      change Complex.ofReal (W x) = Complex.ofReal (W 0)
      rw [hxW, h0W]

/-- P0 (IMPL): derivative bounds for `T h` (found:338-343): `≪ x^{-j-η}` on `(0,1]` and
`≪ x^{-A}` on `[1,∞)`, every `A, j` and `η > 0`.  `T h` is smooth on `(0,∞)`. -/
theorem qs_transform_bounds_P0 [IsTotallyComplex K] (h : ℝ → ℂ) (hh : IsQSWeight h)
    (A j : ℕ) (η : ℝ) (hη : 0 < η) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (qsTransform K h) (Set.Ioi 0) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      (x ≤ 1 → ‖iteratedDeriv j (qsTransform K h) x‖ ≤ C * x ^ (-(j : ℝ) - η)) ∧
      (1 ≤ x → ‖iteratedDeriv j (qsTransform K h) x‖ ≤ C * x ^ (-(A : ℝ))) := by
  refine ⟨qs_transform_contDiffOn (K := K) h hh, ?_⟩
  obtain ⟨Cs, hCs, hSmall⟩ :=
    qs_transform_fixed_line_deriv_bound (K := K) h hh η hη j
  have hLargeSigma : 0 < (A : ℝ) + 1 := by positivity
  obtain ⟨Cl, hCl, hLarge⟩ :=
    qs_transform_fixed_line_deriv_bound (K := K) h hh ((A : ℝ) + 1) hLargeSigma j
  let C : ℝ := max Cs Cl + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith [le_max_left Cs Cl, hCs]
  have hCsC : Cs ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left Cs Cl) (le_add_of_nonneg_right (by norm_num))
  have hClC : Cl ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right Cs Cl) (le_add_of_nonneg_right (by norm_num))
  refine ⟨C, hC, ?_⟩
  intro x hx
  constructor
  · intro hxle
    have hbound := hSmall x hx
    have hpower : -(η + (j : ℝ)) = -(j : ℝ) - η := by ring
    rw [hpower] at hbound
    calc
      ‖iteratedDeriv j (qsTransform K h) x‖ ≤ Cs * x ^ (-(j : ℝ) - η) := hbound
      _ ≤ C * x ^ (-(j : ℝ) - η) := by
        exact mul_le_mul_of_nonneg_right hCsC (Real.rpow_nonneg hx.le _)
  · intro hxge
    have hbound := hLarge x hx
    have hexp : -((A : ℝ) + 1 + (j : ℝ)) ≤ -(A : ℝ) := by
      have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hpow : x ^ (-((A : ℝ) + 1 + (j : ℝ))) ≤ x ^ (-(A : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hxge hexp
    calc
      ‖iteratedDeriv j (qsTransform K h) x‖ ≤
          Cl * x ^ (-((A : ℝ) + 1 + (j : ℝ))) := hbound
      _ ≤ Cl * x ^ (-(A : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hCl
      _ ≤ C * x ^ (-(A : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hClC (Real.rpow_nonneg hx.le _)

private lemma qsTransformLogWeight_integrable [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) :
    Integrable (fun v : ℝ => Real.exp (-v / 2) • qsTransform K h (Real.exp (-v))) := by
  obtain ⟨hSmooth, ⟨C, hC, hDecay⟩⟩ :=
    qs_transform_bounds_P0 (K := K) h hh 2 0 (1 / 4) (by norm_num)
  let g : ℝ → ℂ := fun v => Real.exp (-v / 2) • qsTransform K h (Real.exp (-v))
  have hTcont : ContinuousOn (qsTransform K h) (Set.Ioi 0) := hSmooth.continuousOn
  have hArgCont : Continuous (fun v : ℝ => Real.exp (-v)) := by fun_prop
  have hGcont : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hx : Real.exp (-v) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (Real.exp_pos _)
    have hT : ContinuousAt (qsTransform K h) (Real.exp (-v)) :=
      hTcont.continuousAt (isOpen_Ioi.mem_nhds hx)
    have hTcomp : ContinuousAt (fun x : ℝ => qsTransform K h (Real.exp (-x))) v :=
      ContinuousAt.comp hT hArgCont.continuousAt
    have hScale : ContinuousAt (fun x : ℝ => Real.exp (-x / 2)) v := by fun_prop
    change ContinuousAt
      (fun x : ℝ => Real.exp (-x / 2) • qsTransform K h (Real.exp (-x))) v
    exact hScale.smul hTcomp
  have hNorm (v : ℝ) : ‖g v‖ = Real.exp (-v / 2) *
      ‖qsTransform K h (Real.exp (-v))‖ := by
    change ‖Real.exp (-v / 2) • qsTransform K h (Real.exp (-v))‖ = _
    rw [norm_smul]
    simp [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hTopBound : ∀ v : ℝ, 0 ≤ v → ‖g v‖ ≤ C * Real.exp (-v / 4) := by
    intro v hv
    have hx : 0 < Real.exp (-v) := Real.exp_pos _
    have hxle : Real.exp (-v) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hT := (hDecay (Real.exp (-v)) hx).1 hxle
    have hT' : ‖qsTransform K h (Real.exp (-v))‖ ≤
        C * (Real.exp (-v)) ^ (-(1 / 4 : ℝ)) := by simpa using hT
    have hpow : (Real.exp (-v)) ^ (-(1 / 4 : ℝ)) = Real.exp (v / 4) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    have hT'' : ‖qsTransform K h (Real.exp (-v))‖ ≤ C * Real.exp (v / 4) := by
      rw [hpow] at hT'
      exact hT'
    calc
      ‖g v‖ = Real.exp (-v / 2) * ‖qsTransform K h (Real.exp (-v))‖ := hNorm v
      _ ≤ Real.exp (-v / 2) * (C * Real.exp (v / 4)) := by
        exact mul_le_mul_of_nonneg_left hT'' (Real.exp_pos _).le
      _ = C * Real.exp (-v / 4) := by
        calc
          _ = C * (Real.exp (-v / 2) * Real.exp (v / 4)) := by ring
          _ = C * Real.exp (-v / 2 + v / 4) := by rw [← Real.exp_add]
          _ = C * Real.exp (-v / 4) := by congr 2 <;> ring
  have hBotBound : ∀ v : ℝ, v ≤ 0 → ‖g v‖ ≤ C * Real.exp (3 * v / 2) := by
    intro v hv
    have hx : 0 < Real.exp (-v) := Real.exp_pos _
    have hxge : 1 ≤ Real.exp (-v) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hT := (hDecay (Real.exp (-v)) hx).2 hxge
    have hT' : ‖qsTransform K h (Real.exp (-v))‖ ≤
        C * (Real.exp (-v)) ^ (-(2 : ℝ)) := by simpa using hT
    have hpow : (Real.exp (-v)) ^ (-(2 : ℝ)) = Real.exp (2 * v) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    have hT'' : ‖qsTransform K h (Real.exp (-v))‖ ≤ C * Real.exp (2 * v) := by
      rw [hpow] at hT'
      exact hT'
    calc
      ‖g v‖ = Real.exp (-v / 2) * ‖qsTransform K h (Real.exp (-v))‖ := hNorm v
      _ ≤ Real.exp (-v / 2) * (C * Real.exp (2 * v)) := by
        exact mul_le_mul_of_nonneg_left hT'' (Real.exp_pos _).le
      _ = C * Real.exp (3 * v / 2) := by
        calc
          _ = C * (Real.exp (-v / 2) * Real.exp (2 * v)) := by ring
          _ = C * Real.exp (-v / 2 + 2 * v) := by rw [← Real.exp_add]
          _ = C * Real.exp (3 * v / 2) := by congr 2 <;> ring
  have hOtop : g =O[atTop] (fun v : ℝ => Real.exp (-v / 4)) := by
    rw [Asymptotics.isBigO_iff_isBigOWith]
    refine ⟨C, ?_⟩
    rw [Asymptotics.isBigOWith_iff]
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hTopBound v hv
  have hObot : g =O[atBot] (fun v : ℝ => Real.exp (3 * v / 2)) := by
    rw [Asymptotics.isBigO_iff_isBigOWith]
    refine ⟨C, ?_⟩
    rw [Asymptotics.isBigOWith_iff]
    filter_upwards [eventually_le_atBot (0 : ℝ)] with v hv
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hBotBound v hv
  have hTopInt : IntegrableAtFilter (fun v : ℝ => Real.exp (-v / 4)) atTop volume := by
    refine ⟨Set.Ioi 0, Ioi_mem_atTop 0, ?_⟩
    convert (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 4 : ℝ) < 0) 0) using 1
    ext v
    ring
  have hBotInt : IntegrableAtFilter (fun v : ℝ => Real.exp (3 * v / 2)) atBot volume := by
    refine ⟨Set.Iic 0, Iic_mem_atBot 0, ?_⟩
    convert (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 3 / 2) 0) using 1
    ext v
    ring
  exact hGcont.locallyIntegrable.integrable_of_isBigO_atBot_atTop hObot hBotInt hOtop hTopInt

private lemma qs_transform_mellin_center_line [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (t : ℝ) :
    mellin (qsTransform K h) ((1 / 2 : ℂ) + (2 * Real.pi * t : ℝ) * Complex.I) =
      qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * t : ℝ) * Complex.I) *
        mellin h ((1 / 2 : ℂ) - (2 * Real.pi * t : ℝ) * Complex.I) := by
  let q : ℝ → ℂ := qsLogMellinWeight h (1 / 2)
  let F : ℝ → ℂ := fun y : ℝ =>
    qsGammaRatio K (((1 / 2 : ℝ) : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I) *
      mellin h (1 - (((1 / 2 : ℝ) : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I))
  have hqInt : Integrable q :=
    qsLogMellinWeight_iteratedDeriv_integrable h (1 / 2) (by norm_num) hh 0
  have hqCont : Continuous (𝓕 q) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) q)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hqInt
  have hlineMellin (y : ℝ) :
      mellin h ((1 / 2 : ℂ) - (2 * Real.pi * y : ℝ) * Complex.I) = 𝓕 q (-y) := by
    have hFour := qs_mellin_log_fourier h (1 / 2) (-2 * Real.pi * y)
    have hfreq : (-2 * Real.pi * y) / (2 * Real.pi) = -y := by
      field_simp [Real.pi_ne_zero]
    calc
      mellin h ((1 / 2 : ℂ) - (2 * Real.pi * y : ℝ) * Complex.I) =
          𝓕 q ((-2 * Real.pi * y) / (2 * Real.pi)) := by
            simpa [q, sub_eq_add_neg, mul_neg] using hFour
      _ = 𝓕 q (-y) := by rw [hfreq]
  have hratioCont : Continuous
      (fun y : ℝ => qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    let z : ℂ := (1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I
    have hzre : z.re = 1 / 2 := by simp [z]
    have hdiff := qs_gammaRatio_differentiableAt (K := K) z (by rw [hzre]; norm_num)
      (by rw [hzre]; norm_num)
    have hline : ContinuousAt (fun y : ℝ =>
        (1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) y := by fun_prop
    have hcomp := ContinuousAt.comp_of_eq hdiff.continuousAt hline (by rfl)
    simpa [Function.comp_def, z] using hcomp
  have hFdef : F = qsMellinTransformLine K h := by
    funext y
    dsimp [F, qsMellinTransformLine]
    congr 1 <;> push_cast <;> ring
  have hFcontinuous : Continuous F := by
    rw [hFdef]
    change Continuous (fun y : ℝ =>
      qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) *
        mellin h ((1 / 2 : ℂ) - (2 * Real.pi * y : ℝ) * Complex.I))
    have hGdef : (fun y : ℝ =>
        qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) *
          mellin h ((1 / 2 : ℂ) - (2 * Real.pi * y : ℝ) * Complex.I)) =
        fun y => qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) * 𝓕 q (-y) := by
      funext y
      rw [hlineMellin y]
    rw [hGdef]
    exact hratioCont.mul (hqCont.comp continuous_neg)
  have hFint : Integrable F := by
    rw [hFdef]
    exact qs_mellin_transform_line_integrable (K := K) h hh
  let qT : ℝ → ℂ := qsLogMellinWeight (qsTransform K h) (1 / 2)
  have hgInt : Integrable qT := by
    have hqEq : qT = fun v : ℝ => Real.exp (-v / 2) • qsTransform K h (Real.exp (-v)) := by
      funext v
      dsimp [qT, qsLogMellinWeight]
      congr 1
      ring
    rw [hqEq]
    exact qsTransformLogWeight_integrable (K := K) h hh
  have hEq : qT = 𝓕⁻ F := by
    funext v
    -- The defining inverse Mellin integral is a Fourier inverse on the central line.
    have hx : 0 < Real.exp (-v) := Real.exp_pos _
    have hmi := mellinInv_eq_fourierInv (1 / 2 : ℝ)
      (fun s : ℂ => qsGammaRatio K s * mellin h (1 - s)) hx
    have hTh : qsTransform K h (Real.exp (-v)) =
        (Real.exp (-v) : ℂ) ^ (-(1 / 2 : ℂ)) • 𝓕⁻ F v := by
      simpa [qsTransform, F, Real.log_exp] using hmi
    have hpow : (Real.exp (-v) : ℂ) ^ (-(1 / 2 : ℂ)) =
        ((Real.exp (v / 2) : ℝ) : ℂ) := by
      calc
        (Real.exp (-v) : ℂ) ^ (-(1 / 2 : ℂ)) =
            ((Real.exp (-v) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
              have hcpow := Complex.ofReal_cpow (le_of_lt (Real.exp_pos (-v))) (-(1 / 2 : ℝ))
              simpa using hcpow.symm
        _ = ((Real.exp (v / 2) : ℝ) : ℂ) := by
              congr 1
              rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
              congr 1
              ring
    have hscale : Real.exp (-v / 2) * Real.exp (v / 2) = 1 := by
      rw [← Real.exp_add]
      rw [show -v / 2 + v / 2 = 0 by ring, Real.exp_zero]
    change Real.exp (-(1 / 2 : ℝ) * v) • qsTransform K h (Real.exp (-v)) = 𝓕⁻ F v
    have hcoef : -(1 / 2 : ℝ) * v = -v / 2 := by ring
    rw [hcoef]
    rw [hTh]
    simp only [RCLike.real_smul_eq_coe_mul, smul_eq_mul, hpow]
    have hscaleC : ((Real.exp (-v / 2) : ℝ) : ℂ) *
        ((Real.exp (v / 2) : ℝ) : ℂ) = 1 := by exact_mod_cast hscale
    calc
      ((Real.exp (-v / 2) : ℝ) : ℂ) *
          (((Real.exp (v / 2) : ℝ) : ℂ) * 𝓕⁻ F v) =
          ((((Real.exp (-v / 2) : ℝ) : ℂ) * ((Real.exp (v / 2) : ℝ) : ℂ)) * 𝓕⁻ F v) := by
            rw [mul_assoc]
      _ = (1 : ℂ) * 𝓕⁻ F v := by rw [hscaleC]
      _ = 𝓕⁻ F v := by simp
  have hFourierForward : Integrable (𝓕 F) := by
    have hInv : Integrable (𝓕⁻ F) := by
      rw [← hEq]
      exact hgInt
    have hcongr : (fun y : ℝ => 𝓕 F (-y)) = 𝓕⁻ F := by
      funext y
      exact (Real.fourierInv_eq_fourier_neg F y).symm
    have hcomp : Integrable (fun y : ℝ => 𝓕 F (-y)) := by simpa [hcongr] using hInv
    simpa using hcomp.comp_neg
  have hFourierEq (y : ℝ) : 𝓕 (𝓕⁻ F) y = F y :=
    MeasureTheory.Integrable.fourier_fourierInv_eq hFint hFourierForward hFcontinuous.continuousAt
  have hMellinEq : mellin (qsTransform K h)
      ((1 / 2 : ℂ) + (2 * Real.pi * t : ℝ) * Complex.I) = 𝓕 qT t := by
    have hFour := qs_mellin_log_fourier (qsTransform K h) (1 / 2) (2 * Real.pi * t)
    have hfreq : (2 * Real.pi * t) / (2 * Real.pi) = t := by
      field_simp [Real.pi_ne_zero]
    calc
      mellin (qsTransform K h) ((1 / 2 : ℂ) + (2 * Real.pi * t : ℝ) * Complex.I) =
          𝓕 qT ((2 * Real.pi * t) / (2 * Real.pi)) := by simpa [qT] using hFour
      _ = 𝓕 qT t := by rw [hfreq]
  calc
    mellin (qsTransform K h) ((1 / 2 : ℂ) + (2 * Real.pi * t : ℝ) * Complex.I) =
        𝓕 qT t := hMellinEq
    _ = F t := by rw [hEq]; exact hFourierEq t
    _ = qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * t : ℝ) * Complex.I) *
        mellin h ((1 / 2 : ℂ) - (2 * Real.pi * t : ℝ) * Complex.I) := by
        calc
          F t = qsMellinTransformLine K h t := congrFun hFdef t
          _ = qsGammaRatio K ((1 / 2 : ℂ) + (2 * Real.pi * t : ℝ) * Complex.I) *
              mellin h ((1 / 2 : ℂ) - (2 * Real.pi * t : ℝ) * Complex.I) := by rfl

private lemma qs_transform_mellin_differentiableAt [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    DifferentiableAt ℂ (mellin (qsTransform K h)) s := by
  let η : ℝ := s.re / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨hSmooth, ⟨C, hC, hbound⟩⟩ :=
    qs_transform_bounds_P0 (K := K) h hh 2 0 η hη
  have hTop : qsTransform K h =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hb := (hbound x hxpos).2 hx
    simpa [iteratedDeriv_zero, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hxpos _)] using hb
  have hBot : qsTransform K h =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-η)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hb := (hbound x hx.1).1 hx.2.le
    simpa [iteratedDeriv_zero, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hx.1 _)] using hb
  have hloc : LocallyIntegrableOn (qsTransform K h) (Set.Ioi 0) :=
    hSmooth.continuousOn.locallyIntegrableOn measurableSet_Ioi
  exact mellin_differentiableAt_of_isBigO_rpow hloc hTop (by linarith) hBot (by dsimp [η]; linarith)

private lemma qs_mellin_test_differentiableAt (h : ℝ → ℂ) (hh : IsQSWeight h)
    (s : ℂ) (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    DifferentiableAt ℂ (mellin h) s := by
  rcases hh with ⟨hSmooth, ⟨B, hB⟩, ⟨δ, hδ, hconst⟩⟩
  have hTop : h =O[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (max B 1)] with x hx
    have hxB : B ≤ x := (le_max_left B 1).trans hx
    rw [hB x hxB]
    simpa using (norm_nonneg (x ^ (-(2 : ℝ))))
  have hBot : h =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨‖h 0‖, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
    have hxconst : h x = h 0 := hconst x ⟨le_of_lt hx.1, hx.2.le⟩
    simp [hxconst]
  have hloc : LocallyIntegrableOn h (Set.Ioi 0) :=
    hSmooth.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  exact mellin_differentiableAt_of_isBigO_rpow hloc hTop hs2 hBot hs0

/-- P0 (IMPL): Mellin transform of `T h` on the strip `0 < Re u < 1`:
`Mellin(T h)(u) = G_K(u)/G_K(1-u) · Mellin(h)(1-u)` (found:333-334). -/
theorem qs_transform_mellin_P0 [IsTotallyComplex K] (h : ℝ → ℂ) (hh : IsQSWeight h) (u : ℂ)
    (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    mellin (qsTransform K h) u = qsGammaRatio K u * mellin h (1 - u) := by
  let S : Set ℂ := Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1
  let f : ℂ → ℂ := fun z => mellin (qsTransform K h) z
  let g : ℂ → ℂ := fun z => qsGammaRatio K z * mellin h (1 - z)
  have hSopen : IsOpen S := by
    dsimp [S]
    exact isOpen_Ioo.preimage (by fun_prop)
  have hSconv : Convex ℝ S := by
    intro z hz w hw a b ha hb hab
    simp only [S, Set.mem_preimage, Set.mem_Ioo] at hz hw ⊢
    have hre : (a • z + b • w).re = a * z.re + b * w.re := by simp
    rw [hre]
    constructor
    · by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hw.1
      · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hleft : 0 < a * z.re := mul_pos haPos hz.1
        have hright : 0 ≤ b * w.re := mul_nonneg hb (le_of_lt hw.1)
        linarith
    · by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hw.2
      · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hleft : a * z.re < a := by nlinarith [hz.2, haPos]
        have hright : b * w.re ≤ b := by
          simpa using mul_le_mul_of_nonneg_left hw.2.le hb
        have hsum : a * z.re + b * w.re < a + b := add_lt_add_of_lt_of_le hleft hright
        rw [hab] at hsum
        exact hsum
  have hSpre : IsPreconnected S := hSconv.isPreconnected
  have hcenter : (1 / 2 : ℂ) ∈ S := by norm_num [S]
  have hfdiff : DifferentiableOn ℂ f S := by
    intro z hz
    simp only [S, Set.mem_preimage, Set.mem_Ioo] at hz
    simpa [f] using
      (qs_transform_mellin_differentiableAt (K := K) h hh z hz.1 hz.2).differentiableWithinAt
  have hgdiff : DifferentiableOn ℂ g S := by
    intro z hz
    simp only [S, Set.mem_preimage, Set.mem_Ioo] at hz
    have hratio := qs_gammaRatio_differentiableAt (K := K) z hz.1 hz.2
    have hMellin := qs_mellin_test_differentiableAt h hh (1 - z)
      (by rw [Complex.sub_re, Complex.one_re]; linarith)
      (by rw [Complex.sub_re, Complex.one_re]; linarith)
    have hcomp : DifferentiableAt ℂ (fun z : ℂ => 1 - z) z := by fun_prop
    have hprod : DifferentiableAt ℂ
        (fun w : ℂ => qsGammaRatio K w * mellin h (1 - w)) z := by
      convert hratio.mul (hMellin.comp z hcomp) using 1 <;> rfl
    simpa [g] using hprod.differentiableWithinAt
  have hfanalytic : AnalyticOnNhd ℂ f S :=
    (Complex.analyticOnNhd_iff_differentiableOn hSopen).2 hfdiff
  have hganalytic : AnalyticOnNhd ℂ g S :=
    (Complex.analyticOnNhd_iff_differentiableOn hSopen).2 hgdiff
  let line : ℝ → ℂ := fun y =>
    (1 / 2 : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I
  have hlineCont : ContinuousAt line 0 := by fun_prop
  have hlineNe (y : ℝ) (hy : y ≠ 0) : line y ≠ (1 / 2 : ℂ) := by
    intro heq
    have him := congrArg Complex.im heq
    have hmul : (2 * Real.pi) * y = 0 := by simpa [line] using him
    have hscale : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    exact hy (mul_left_cancel₀ hscale (by simpa using hmul))
  have hlineTendsto : Tendsto line (𝓝[≠] (0 : ℝ)) (𝓝[≠] (1 / 2 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont := hlineCont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
      simpa [line] using hcont
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact hlineNe y (by simpa using hy)
  have hlineEq (y : ℝ) : f (line y) = g (line y) := by
    have harg : 1 - line y = (1 / 2 : ℂ) - (2 * Real.pi * y : ℝ) * Complex.I := by
      dsimp [line]
      ring
    change mellin (qsTransform K h) (line y) =
      qsGammaRatio K (line y) * mellin h (1 - line y)
    rw [harg]
    simpa [line] using qs_transform_mellin_center_line (K := K) h hh y
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 / 2 : ℂ), f z = g z := by
    rw [frequently_iff]
    intro U hU
    have hUline : ∀ᶠ y in 𝓝[≠] (0 : ℝ), line y ∈ U := hlineTendsto hU
    obtain ⟨y, hy⟩ := hUline.exists
    exact ⟨line y, hy, hlineEq y⟩
  have hglobal := hfanalytic.eqOn_of_preconnected_of_frequently_eq
    hganalytic hSpre hcenter hfreq
  have huS : u ∈ S := by simpa [S] using And.intro hu0 hu1
  simpa [f, g] using hglobal huS

/-- P0 (IMPL): half-Mellin preservation (found:344-346): `∫₀^∞ h(t²) dt = ∫₀^∞ (T h)(t²) dt`
(the multiplier is `1` at `u = 1/2`). -/
theorem qs_half_mellin_P0 [IsTotallyComplex K] (h : ℝ → ℂ) (hh : IsQSWeight h) :
    mellin (fun y : ℝ => qsTransform K h (y ^ 2)) 1 = mellin (fun y : ℝ => h (y ^ 2)) 1 := by
  have hcenter := qs_transform_mellin_P0 (K := K) h hh (1 / 2 : ℂ) (by norm_num) (by norm_num)
  have hDreal : (|(NumberField.discr K : ℝ)| : ℝ) ≠ 0 := by
    exact abs_ne_zero.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hD : Complex.ofReal (|(NumberField.discr K : ℝ)|) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hDreal
  have hA : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hGammaC : Complex.Gammaℂ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hA)))
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hGammaR : Complex.Gammaℝ (1 / 2 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hpref : Hecke.dedekindPrefactor K (1 / 2 : ℂ) ≠ 0 := by
    rw [Hecke.dedekindPrefactor]
    apply mul_ne_zero
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl hD)
    · exact mul_ne_zero (pow_ne_zero _ hGammaR) (pow_ne_zero _ hGammaC)
  have hleft : mellin (fun y : ℝ => qsTransform K h (y ^ 2)) 1 =
      (1 / 2 : ℝ) • mellin (qsTransform K h) (1 / 2) := by
    calc
      mellin (fun y : ℝ => qsTransform K h (y ^ 2)) 1 =
          mellin (fun y : ℝ => qsTransform K h (y ^ (2 : ℝ))) 1 := by
        unfold mellin
        refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        change (y : ℂ) ^ ((1 : ℂ) - 1) • qsTransform K h (y ^ 2) =
          (y : ℂ) ^ ((1 : ℂ) - 1) • qsTransform K h (y ^ (2 : ℝ))
        rw [show (1 : ℂ) - 1 = 0 by ring]
        simp only [Complex.cpow_zero, one_smul]
        exact congrArg (qsTransform K h) (Real.rpow_natCast y 2).symm
      _ = (1 / 2 : ℝ) • mellin (qsTransform K h) (1 / 2) := by
        simpa [Real.rpow_natCast] using
          (mellin_comp_rpow (fun x : ℝ => qsTransform K h x) (1 : ℂ) 2)
  have hright : mellin (fun y : ℝ => h (y ^ 2)) 1 =
      (1 / 2 : ℝ) • mellin h (1 / 2) := by
    calc
      mellin (fun y : ℝ => h (y ^ 2)) 1 =
          mellin (fun y : ℝ => h (y ^ (2 : ℝ))) 1 := by
        unfold mellin
        refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        change (y : ℂ) ^ ((1 : ℂ) - 1) • h (y ^ 2) =
          (y : ℂ) ^ ((1 : ℂ) - 1) • h (y ^ (2 : ℝ))
        rw [show (1 : ℂ) - 1 = 0 by ring]
        simp only [Complex.cpow_zero, one_smul]
        exact congrArg h (Real.rpow_natCast y 2).symm
      _ = (1 / 2 : ℝ) • mellin h (1 / 2) := by
        simpa [Real.rpow_natCast] using (mellin_comp_rpow h (1 : ℂ) 2)
  have hratio : qsGammaRatio K (1 / 2 : ℂ) = 1 := by
    rw [qsGammaRatio, show (1 : ℂ) - (1 / 2 : ℂ) = 1 / 2 by ring,
      div_self hpref]
  calc
    mellin (fun y : ℝ => qsTransform K h (y ^ 2)) 1 =
        (1 / 2 : ℝ) • mellin (qsTransform K h) (1 / 2) := hleft
    _ = (1 / 2 : ℝ) • mellin h (1 / 2) := by
      rw [hcenter, hratio]
      congr 1
      norm_num
    _ = mellin (fun y : ℝ => h (y ^ 2)) 1 := hright.symm

end ArtinPrimitiveRoots.A2
