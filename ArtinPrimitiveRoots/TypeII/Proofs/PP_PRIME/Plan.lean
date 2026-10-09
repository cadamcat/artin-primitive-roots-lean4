import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Marked
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.PP_PRIME

open Classical
open Filter
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP
open MeasureTheory
open scoped FourierTransform
open scoped Topology

noncomputable def mangoldtIntervalPolynomial (N : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (I : Set ℕ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter
      (fun n : ℕ => 1 ≤ n ∧ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N ∧ n ∈ I),
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) *
      Complex.exp ((-1 + Complex.I * t) * Real.log (n : ℝ))

noncomputable def smoothedMangoldtPolynomial (N : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (g : ℝ → ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊3 * N⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n),
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) *
      Complex.exp ((-1 + Complex.I * t) * Real.log (n : ℝ)) *
        (g ((n : ℝ) / N) : ℂ)

noncomputable def mellinKernel (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ w : ℝ in Set.Ioi 0,
    (g w : ℂ) * Complex.exp (z * Real.log w) / (w : ℂ)

noncomputable def mellinLogWeight (g : ℝ → ℝ) (α u : ℝ) : ℂ :=
  (Real.exp (-α * u) : ℂ) * (g (Real.exp (-u)) : ℂ)

/-- A smooth cutoff of a real interval, widened by `δ` at both ends. -/
noncomputable def ppPrimeLogCutoff (a b δ : ℝ) (u : ℝ) : ℝ :=
  Real.smoothTransition ((u - (a - δ)) / δ) *
    Real.smoothTransition (((b + δ) - u) / δ)

/-- Transfer a log-coordinate cutoff to positive real inputs and extend it by zero. -/
noncomputable def ppPrimePositiveCutoff (a b δ : ℝ) (w : ℝ) : ℝ :=
  if 0 < w then ppPrimeLogCutoff (Real.log a) (Real.log b) δ (Real.log w) else 0

theorem ppPrimeLogCutoff_contDiff (a b δ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ppPrimeLogCutoff a b δ) := by
  unfold ppPrimeLogCutoff
  fun_prop

theorem ppPrimeLogCutoff_nonneg_le_one (a b δ u : ℝ) :
    0 ≤ ppPrimeLogCutoff a b δ u ∧ ppPrimeLogCutoff a b δ u ≤ 1 := by
  unfold ppPrimeLogCutoff
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · calc
      _ ≤ 1 * Real.smoothTransition (((b + δ) - u) / δ) :=
        mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) (by norm_num)
      _ = 1 := by norm_num

theorem ppPrimeLogCutoff_eq_one (a b δ u : ℝ) (hδ : 0 < δ)
    (hau : a ≤ u) (hub : u ≤ b) : ppPrimeLogCutoff a b δ u = 1 := by
  unfold ppPrimeLogCutoff
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le]
  · norm_num
  · apply (le_div_iff₀ hδ).2
    linarith
  · apply (le_div_iff₀ hδ).2
    linarith

theorem ppPrimeLogCutoff_support (a b δ : ℝ) (hδ : 0 < δ) :
    Function.support (ppPrimeLogCutoff a b δ) ⊆ Set.Icc (a - δ) (b + δ) := by
  intro u hu
  have hne : ppPrimeLogCutoff a b δ u ≠ 0 := by
    simpa only [Function.mem_support] using hu
  by_contra hout
  have hout' : u < a - δ ∨ b + δ < u := by
    by_cases hleft : u < a - δ
    · exact Or.inl hleft
    · have hright : b + δ < u := by
        by_contra h
        exact hout ⟨le_of_not_gt hleft, le_of_not_gt h⟩
      exact Or.inr hright
  rcases hout' with hleft | hright
  · have hzero : Real.smoothTransition ((u - (a - δ)) / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (by linarith) hδ.le)
    apply hne
    simp [ppPrimeLogCutoff, hzero]
  · have hzero : Real.smoothTransition (((b + δ) - u) / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (by linarith) hδ.le)
    apply hne
    simp [ppPrimeLogCutoff, hzero]

theorem ppPrimePositiveCutoff_nonneg_le_one (a b δ w : ℝ) :
    0 ≤ ppPrimePositiveCutoff a b δ w ∧ ppPrimePositiveCutoff a b δ w ≤ 1 := by
  by_cases hw : 0 < w
  · simp only [ppPrimePositiveCutoff, if_pos hw]
    exact ppPrimeLogCutoff_nonneg_le_one _ _ _ _
  · simp [ppPrimePositiveCutoff, hw]

theorem ppPrimePositiveCutoff_eq_one (a b δ w : ℝ) (ha : 0 < a)
    (hδ : 0 < δ) (haw : a ≤ w) (hwb : w ≤ b) :
    ppPrimePositiveCutoff a b δ w = 1 := by
  have hw : 0 < w := lt_of_lt_of_le ha haw
  rw [ppPrimePositiveCutoff, if_pos hw]
  apply ppPrimeLogCutoff_eq_one
  · exact hδ
  · exact Real.log_le_log ha haw
  · exact Real.log_le_log hw hwb

theorem ppPrimePositiveCutoff_support (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 < δ) :
    Function.support (ppPrimePositiveCutoff a b δ) ⊆
      Set.Icc (a * Real.exp (-δ)) (b * Real.exp δ) := by
  intro w hw
  have hne : ppPrimePositiveCutoff a b δ w ≠ 0 := by
    simpa only [Function.mem_support] using hw
  have hwpos : 0 < w := by
    by_contra h
    have hwle : w ≤ 0 := le_of_not_gt h
    apply hne
    simp [ppPrimePositiveCutoff, not_lt.mpr hwle]
  have hlogne : ppPrimeLogCutoff (Real.log a) (Real.log b) δ (Real.log w) ≠ 0 := by
    simpa [ppPrimePositiveCutoff, hwpos] using hne
  have hmem : Real.log w ∈ Function.support
      (ppPrimeLogCutoff (Real.log a) (Real.log b) δ) := by
    simpa only [Function.mem_support] using hlogne
  have hlogBounds := ppPrimeLogCutoff_support (Real.log a) (Real.log b) δ hδ hmem
  have hlow : a * Real.exp (-δ) ≤ w := by
    have := (Real.exp_le_exp).2 hlogBounds.1
    rw [Real.exp_sub, Real.exp_log ha, Real.exp_log hwpos] at this
    have heq : a / Real.exp δ = a * Real.exp (-δ) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
    rw [heq] at this
    exact this
  have hhigh : w ≤ b * Real.exp δ := by
    have := (Real.exp_le_exp).2 hlogBounds.2
    rw [Real.exp_add, Real.exp_log hb, Real.exp_log hwpos] at this
    exact this
  exact ⟨hlow, hhigh⟩

theorem ppPrimePositiveCutoff_logWeight_contDiff (a b δ α : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (mellinLogWeight (ppPrimePositiveCutoff a b δ) α) := by
  have hexpR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => Real.exp (-α * u)) := by fun_prop
  have hexpC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => (Real.exp (-α * u) : ℂ)) := Complex.ofRealCLM.contDiff.comp hexpR
  have hcut : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => ppPrimeLogCutoff (Real.log a) (Real.log b) δ (-u)) :=
    (ppPrimeLogCutoff_contDiff _ _ _).comp (by fun_prop)
  have hcutC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => (ppPrimeLogCutoff (Real.log a) (Real.log b) δ (-u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hcut
  have heq : mellinLogWeight (ppPrimePositiveCutoff a b δ) α =
      (fun u : ℝ => (Real.exp (-α * u) : ℂ) *
        (ppPrimeLogCutoff (Real.log a) (Real.log b) δ (-u) : ℂ)) := by
    funext u
    simp [mellinLogWeight, ppPrimePositiveCutoff, Real.exp_pos]
  rw [heq]
  exact hexpC.mul hcutC

private theorem ppPrimeSmoothTransition_deriv_support :
    Function.support (deriv Real.smoothTransition) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  have hne : deriv Real.smoothTransition x ≠ 0 := by
    simpa only [Function.mem_support] using hx
  constructor
  · by_contra hxlt
    have hstSupport : Function.support Real.smoothTransition ⊆ Set.Ici (0 : ℝ) := by
      intro y hy
      have hyne : Real.smoothTransition y ≠ 0 := by
        simpa only [Function.mem_support] using hy
      by_contra hylt
      have hylt' : y < 0 := lt_of_not_ge (by simpa only [Set.mem_Ici] using hylt)
      exact hyne (Real.smoothTransition.zero_of_nonpos hylt'.le)
    have hstTsupport : tsupport Real.smoothTransition ⊆ Set.Ici (0 : ℝ) :=
      closure_minimal hstSupport isClosed_Ici
    have hxnot : x ∉ tsupport Real.smoothTransition := by
      intro h
      exact hxlt (by simpa only [Set.mem_Ici] using hstTsupport h)
    exact hne (deriv_of_notMem_tsupport hxnot)
  · by_contra hxgt
    let f : ℝ → ℝ := fun y => Real.smoothTransition y - 1
    have hfSupport : Function.support f ⊆ Set.Iic (1 : ℝ) := by
      intro y hy
      have hyne : f y ≠ 0 := by simpa only [Function.mem_support] using hy
      by_contra hygt
      have hygt' : 1 < y := lt_of_not_ge (by simpa only [Set.mem_Iic] using hygt)
      apply hyne
      simp [f, Real.smoothTransition.one_of_one_le hygt'.le]
    have hfTsupport : tsupport f ⊆ Set.Iic (1 : ℝ) :=
      closure_minimal hfSupport isClosed_Iic
    have hxnot : x ∉ tsupport f := by
      intro h
      exact hxgt (by simpa only [Set.mem_Iic] using hfTsupport h)
    have hz : deriv f x = 0 := deriv_of_notMem_tsupport hxnot
    have heq : deriv f x = deriv Real.smoothTransition x := by simp [f]
    apply hne
    rw [← heq]
    exact hz

private theorem ppPrimeSmoothTransition_deriv_bound (j : ℕ) :
    ∃ Cj : ℝ, 0 < Cj ∧ ∀ x : ℝ,
      ‖iteratedDeriv j Real.smoothTransition x‖ ≤ Cj := by
  have hst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.smoothTransition := by fun_prop
  have hderivSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (deriv Real.smoothTransition) := by
    exact (contDiff_infty_iff_deriv.mp hst).2
  have hderivCompact : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ppPrimeSmoothTransition_deriv_support
  cases j with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro x
      have hnonneg := Real.smoothTransition.nonneg x
      have hle := Real.smoothTransition.le_one x
      simpa [iteratedDeriv_zero, Real.norm_eq_abs] using (abs_le.mpr ⟨by linarith, hle⟩)
  | succ n =>
      obtain ⟨C, hC, hbound⟩ :=
        hderivCompact.exists_bound_iteratedFDeriv hderivSmooth n
      refine ⟨C + 1, by linarith, ?_⟩
      intro x
      have hnorm : ‖iteratedDeriv n (deriv Real.smoothTransition) x‖ ≤ C := by
        rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact hbound n le_rfl x
      calc
        ‖iteratedDeriv (n + 1) Real.smoothTransition x‖ =
            ‖iteratedDeriv n (deriv Real.smoothTransition) x‖ := by
              simp [iteratedDeriv_succ']
        _ ≤ C := hnorm
        _ ≤ C + 1 := by linarith

private noncomputable def ppPrimeSmoothTransitionConstant (j : ℕ) : ℝ :=
  Classical.choose (ppPrimeSmoothTransition_deriv_bound j)

private theorem ppPrimeSmoothTransition_affine_deriv_bound (j : ℕ) (c d : ℝ) :
    ∀ x : ℝ,
      ‖iteratedDeriv j (fun y : ℝ => Real.smoothTransition (c * (y - d))) x‖ ≤
        ppPrimeSmoothTransitionConstant j * |c| ^ j := by
  have hC := Classical.choose_spec (ppPrimeSmoothTransition_deriv_bound j)
  have hCpos : 0 < ppPrimeSmoothTransitionConstant j := hC.1
  have hbound : ∀ x : ℝ, ‖iteratedDeriv j Real.smoothTransition x‖ ≤
      ppPrimeSmoothTransitionConstant j := hC.2
  have hst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.smoothTransition := by
    fun_prop
  have hstj : ContDiff ℝ ((j : ℕ∞) : WithTop ℕ∞) Real.smoothTransition :=
    hst.of_le (by simp)
  let f : ℝ → ℝ := fun y => Real.smoothTransition (c * y)
  have hscale := iteratedDeriv_comp_const_mul (n := j)
    (f := Real.smoothTransition) hstj c
  intro x
  have htrans : iteratedDeriv j (fun y : ℝ => f (y - d)) x =
      iteratedDeriv j f (x - d) := by
    have h := congrFun
      (iteratedDerivWithin_comp_sub_const (n := j) (f := f) (s := Set.univ) d) x
    simpa [iteratedDerivWithin_univ] using h
  change ‖iteratedDeriv j (fun y : ℝ => f (y - d)) x‖ ≤
    ppPrimeSmoothTransitionConstant j * |c| ^ j
  calc
    ‖iteratedDeriv j (fun y : ℝ => f (y - d)) x‖ =
        ‖iteratedDeriv j f (x - d)‖ := by rw [htrans]
    _ = ‖c ^ j * iteratedDeriv j Real.smoothTransition (c * (x - d))‖ := by
      rw [show f = fun y : ℝ => Real.smoothTransition (c * y) by rfl]
      rw [congrFun hscale (x - d)]
    _ = |c| ^ j * ‖iteratedDeriv j Real.smoothTransition (c * (x - d))‖ := by
      rw [norm_mul, norm_pow, Real.norm_eq_abs]
    _ ≤ |c| ^ j * ppPrimeSmoothTransitionConstant j :=
      mul_le_mul_of_nonneg_left (hbound (c * (x - d))) (pow_nonneg (abs_nonneg c) _)
    _ = ppPrimeSmoothTransitionConstant j * |c| ^ j := by ring

private noncomputable def ppPrimeLogCutoffDerivativeConstant (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * ppPrimeSmoothTransitionConstant i *
      ppPrimeSmoothTransitionConstant (j - i)

private theorem ppPrimeLogCutoff_deriv_bound (j : ℕ) (a b δ : ℝ)
    (hδ : 0 < δ) :
    ∀ u : ℝ,
      ‖iteratedDeriv j
        (fun v : ℝ =>
          (ppPrimeLogCutoff (Real.log a) (Real.log b) δ (-v) : ℂ)) u‖ ≤
        ppPrimeLogCutoffDerivativeConstant j * (δ⁻¹) ^ j := by
  classical
  let cLeft : ℝ := -(δ⁻¹)
  let dLeft : ℝ := δ - Real.log a
  let cRight : ℝ := δ⁻¹
  let dRight : ℝ := -(Real.log b + δ)
  let f : ℝ → ℝ := fun u => Real.smoothTransition (cLeft * (u - dLeft))
  let g : ℝ → ℝ := fun u => Real.smoothTransition (cRight * (u - dRight))
  let F : ℝ → ℝ := fun u => ppPrimeLogCutoff (Real.log a) (Real.log b) δ (-u)
  let K : ℝ := ppPrimeLogCutoffDerivativeConstant j
  have hargLeft (u : ℝ) :
      cLeft * (u - dLeft) = ((-u) - (Real.log a - δ)) / δ := by
    dsimp [cLeft, dLeft]
    field_simp [ne_of_gt hδ]
    ring
  have hargRight (u : ℝ) :
      cRight * (u - dRight) = ((Real.log b + δ) - (-u)) / δ := by
    dsimp [cRight, dRight]
    field_simp [ne_of_gt hδ]
    ring
  have hF : F = f * g := by
    funext u
    dsimp [F, f, g, ppPrimeLogCutoff]
    rw [← hargLeft u, ← hargRight u]
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    dsimp [f]
    fun_prop
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    dsimp [g]
    fun_prop
  have hFcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    dsimp [F]
    exact (ppPrimeLogCutoff_contDiff _ _ _).comp (by fun_prop)
  have hleftSlope : |cLeft| = δ⁻¹ := by
    dsimp [cLeft]
    rw [abs_neg, abs_of_pos (inv_pos.mpr hδ)]
  have hrightSlope : |cRight| = δ⁻¹ := by
    dsimp [cRight]
    exact abs_of_pos (inv_pos.mpr hδ)
  have hfBound (i : ℕ) (u : ℝ) :
      ‖iteratedDeriv i f u‖ ≤ ppPrimeSmoothTransitionConstant i * (δ⁻¹) ^ i := by
    have h := ppPrimeSmoothTransition_affine_deriv_bound i cLeft dLeft u
    simpa [f, hleftSlope] using h
  have hgBound (i : ℕ) (u : ℝ) :
      ‖iteratedDeriv i g u‖ ≤ ppPrimeSmoothTransitionConstant i * (δ⁻¹) ^ i := by
    have h := ppPrimeSmoothTransition_affine_deriv_bound i cRight dRight u
    simpa [g, hrightSlope] using h
  have hmul (u : ℝ) :
      iteratedDeriv j (f * g) u =
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          iteratedDeriv i f u * iteratedDeriv (j - i) g u := by
    simpa using (iteratedDeriv_mul (n := j) (x := u)
      (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp)))
  have hterm (u : ℝ) (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
      ‖(j.choose i : ℝ) * iteratedDeriv i f u * iteratedDeriv (j - i) g u‖ ≤
        ((j.choose i : ℝ) * ppPrimeSmoothTransitionConstant i *
          ppPrimeSmoothTransitionConstant (j - i)) * (δ⁻¹) ^ j := by
    have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hcoeff : 0 ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hcoeff]
    calc
      (j.choose i : ℝ) * ‖iteratedDeriv i f u‖ *
          ‖iteratedDeriv (j - i) g u‖ ≤
        ((j.choose i : ℝ) * (ppPrimeSmoothTransitionConstant i * (δ⁻¹) ^ i)) *
          (ppPrimeSmoothTransitionConstant (j - i) * (δ⁻¹) ^ (j - i)) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (hfBound i u) hcoeff
            · exact hgBound (j - i) u
            · exact norm_nonneg _
            · exact mul_nonneg hcoeff (mul_nonneg
                ((Classical.choose_spec (ppPrimeSmoothTransition_deriv_bound i)).1.le)
                (pow_nonneg (inv_nonneg.mpr hδ.le) _))
      _ = ((j.choose i : ℝ) * ppPrimeSmoothTransitionConstant i *
          ppPrimeSmoothTransitionConstant (j - i)) *
            ((δ⁻¹) ^ i * (δ⁻¹) ^ (j - i)) := by ring
      _ = ((j.choose i : ℝ) * ppPrimeSmoothTransitionConstant i *
          ppPrimeSmoothTransitionConstant (j - i)) * (δ⁻¹) ^ j := by
            rw [← pow_add, Nat.add_sub_of_le hi']
  have hrealBound (u : ℝ) :
      ‖iteratedDeriv j F u‖ ≤ K * (δ⁻¹) ^ j := by
    rw [hF, hmul]
    calc
      ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          iteratedDeriv i f u * iteratedDeriv (j - i) g u‖ ≤
        ∑ i ∈ Finset.range (j + 1),
          ‖(j.choose i : ℝ) * iteratedDeriv i f u * iteratedDeriv (j - i) g u‖ :=
            norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1),
          ((j.choose i : ℝ) * ppPrimeSmoothTransitionConstant i *
            ppPrimeSmoothTransitionConstant (j - i)) * (δ⁻¹) ^ j := by
            apply Finset.sum_le_sum
            intro i hi
            exact hterm u i hi
      _ = K * (δ⁻¹) ^ j := by
            dsimp [K, ppPrimeLogCutoffDerivativeConstant]
            rw [← Finset.sum_mul]
  have hcast (n : ℕ) :
      iteratedDeriv n (fun u : ℝ => (F u : ℂ)) =
        fun u => ((iteratedDeriv n F u : ℝ) : ℂ) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
        funext u
        have hdiff : DifferentiableAt ℝ (iteratedDeriv n F) u :=
          (hFcont.differentiable_iteratedDeriv n
            (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n))).differentiableAt
        have hcast' := HasDerivAt.ofReal_comp hdiff.hasDerivAt
        change deriv (fun y : ℝ => ((iteratedDeriv n F y : ℝ) : ℂ)) u =
          ((deriv (iteratedDeriv n F) u : ℝ) : ℂ)
        exact hcast'.deriv
  intro u
  change ‖iteratedDeriv j (fun v : ℝ => (F v : ℂ)) u‖ ≤ K * (δ⁻¹) ^ j
  calc
    ‖iteratedDeriv j (fun v : ℝ => (F v : ℂ)) u‖ =
        ‖iteratedDeriv j F u‖ := by
          rw [congrFun (hcast j) u]
          simp
    _ ≤ K * (δ⁻¹) ^ j := hrealBound u

private noncomputable def ppPrimePositiveCutoffLogWeightConstant (j : ℕ) : ℝ :=
  6 * (∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * Real.exp 2 *
      ppPrimeLogCutoffDerivativeConstant (j - i)) + 1

private theorem ppPrimePositiveCutoff_logWeight_lintegral_bound
    (a b δ α : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 4) (hα : |α| ≤ 1) (j : ℕ) :
    Integrable (iteratedDeriv j
      (mellinLogWeight (ppPrimePositiveCutoff a b δ) α)) ∧
    ∫ u : ℝ, ‖iteratedDeriv j
      (mellinLogWeight (ppPrimePositiveCutoff a b δ) α) u‖ ≤
        ppPrimePositiveCutoffLogWeightConstant j * (δ⁻¹) ^ j := by
  classical
  let F : ℝ → ℝ := fun u => ppPrimeLogCutoff (Real.log a) (Real.log b) δ (-u)
  let G : ℝ → ℂ := fun u => (F u : ℂ)
  let R : ℝ → ℝ := fun u => Real.exp (-α * u)
  let E : ℝ → ℂ := fun u => (R u : ℂ)
  let W : ℝ → ℂ := mellinLogWeight (ppPrimePositiveCutoff a b δ) α
  have hW_eq : W = E * G := by
    funext u
    simp [W, E, G, R, F, mellinLogWeight, ppPrimePositiveCutoff, Real.exp_pos]
  have hFcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    dsimp [F]
    exact (ppPrimeLogCutoff_contDiff _ _ _).comp (by fun_prop)
  have hGcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    exact Complex.ofRealCLM.contDiff.comp hFcont
  have hRcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R := by
    dsimp [R]
    fun_prop
  have hEcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E :=
    Complex.ofRealCLM.contDiff.comp hRcont
  have hWcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W := by
    simpa [W] using ppPrimePositiveCutoff_logWeight_contDiff a b δ α
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hbOne : 1 ≤ b := le_trans ha hab
  have hbPos : 0 < b := lt_of_lt_of_le (by norm_num) hbOne
  have haLog : 0 ≤ Real.log a := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1) ha
    simpa using h
  have hbLog : Real.log b ≤ 1 := by
    calc
      Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hbPos
      _ ≤ 1 := by linarith
  have hFsupport : Function.support F ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro u hu
    have hmem : -u ∈ Function.support
        (ppPrimeLogCutoff (Real.log a) (Real.log b) δ) := by
      simpa [F, Function.mem_support] using hu
    have hbds := ppPrimeLogCutoff_support (Real.log a) (Real.log b) δ hδ hmem
    constructor <;> linarith [hbds.1, hbds.2, haLog, hbLog, hδsmall]
  have hGsupport : Function.support G ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro u hu
    have hGne : G u ≠ 0 := by
      simpa only [Function.mem_support] using hu
    have hFne : F u ≠ 0 := by
      intro hzero
      apply hGne
      simp [G, hzero]
    exact hFsupport (by simpa only [Function.mem_support] using hFne)
  have hGtsupport : tsupport G ⊆ Set.Icc (-2 : ℝ) 2 :=
    closure_minimal hGsupport isClosed_Icc
  have hWsupport : Function.support W ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro u hu
    have hWne : W u ≠ 0 := by
      simpa only [Function.mem_support] using hu
    have hGne : G u ≠ 0 := by
      intro hzero
      apply hWne
      rw [hW_eq]
      simp [hzero]
    exact hGsupport (by simpa only [Function.mem_support] using hGne)
  have hWtsupport : tsupport W ⊆ Set.Icc (-2 : ℝ) 2 :=
    closure_minimal hWsupport isClosed_Icc
  have hiterTsupport (f : ℝ → ℂ) (n : ℕ) :
      tsupport (iteratedDeriv n f) ⊆ tsupport f := by
    induction n with
    | zero => simp [iteratedDeriv_zero]
    | succ n ih =>
        simpa only [iteratedDeriv_succ] using tsupport_deriv_subset.trans ih
  have hGderivSupport (k : ℕ) :
      Function.support (iteratedDeriv k G) ⊆ Set.Icc (-2 : ℝ) 2 :=
    (subset_tsupport _).trans ((hiterTsupport G k).trans hGtsupport)
  have hWderivSupport (k : ℕ) :
      Function.support (iteratedDeriv k W) ⊆ Set.Icc (-2 : ℝ) 2 :=
    (subset_tsupport _).trans ((hiterTsupport W k).trans hWtsupport)
  have hGbound (k : ℕ) (u : ℝ) :
      ‖iteratedDeriv k G u‖ ≤ ppPrimeLogCutoffDerivativeConstant k * (δ⁻¹) ^ k := by
    simpa [G, F] using ppPrimeLogCutoff_deriv_bound k a b δ hδ u
  have hcastIter (f : ℝ → ℝ)
      (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (n : ℕ) :
      iteratedDeriv n (fun u : ℝ => (f u : ℂ)) =
        fun u => ((iteratedDeriv n f u : ℝ) : ℂ) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
        funext u
        have hdiff : DifferentiableAt ℝ (iteratedDeriv n f) u :=
          (hf.differentiable_iteratedDeriv n
            (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n))).differentiableAt
        have hcast := HasDerivAt.ofReal_comp hdiff.hasDerivAt
        change deriv (fun y : ℝ => ((iteratedDeriv n f y : ℝ) : ℂ)) u =
          ((deriv (iteratedDeriv n f) u : ℝ) : ℂ)
        exact hcast.deriv
  have hRiter (k : ℕ) :
      iteratedDeriv k R = fun u => (-α) ^ k * Real.exp (-α * u) := by
    simpa [R] using (iteratedDeriv_exp_const_mul k (-α))
  have hEiter (k : ℕ) :
      iteratedDeriv k E =
        fun u => ((((-α) ^ k * Real.exp (-α * u) : ℝ) : ℂ)) := by
    rw [show E = fun u : ℝ => (R u : ℂ) by rfl, hcastIter R hRcont k]
    funext u
    rw [congrFun (hRiter k) u]
  have hExpBound (k : ℕ) (u : ℝ) (hu : u ∈ Set.Icc (-2 : ℝ) 2) :
      ‖iteratedDeriv k E u‖ ≤ Real.exp 2 := by
    have huabs : |u| ≤ 2 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hcoeff : |(-α) ^ k| ≤ 1 := by
      rw [abs_pow, abs_neg]
      exact pow_le_one₀ (abs_nonneg α) hα
    have hexpArg : (-α) * u ≤ 2 := by
      have habs : |(-α) * u| ≤ 2 := by
        rw [abs_mul, abs_neg]
        calc
          |α| * |u| ≤ 1 * 2 := mul_le_mul hα huabs (abs_nonneg u) (by norm_num)
          _ = 2 := by norm_num
      exact (le_abs_self _).trans habs
    have hexp := Real.exp_le_exp.mpr hexpArg
    rw [congrFun (hEiter k) u, Complex.norm_real, Real.norm_eq_abs]
    calc
      |(-α) ^ k * Real.exp (-α * u)| =
          |(-α) ^ k| * Real.exp (-α * u) := by
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ 1 * Real.exp 2 :=
        mul_le_mul hcoeff hexp (Real.exp_nonneg _) (by norm_num)
      _ = Real.exp 2 := by ring
  have hρ : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 (by linarith [hδsmall])
  have hCutNonneg (k : ℕ) : 0 ≤ ppPrimeLogCutoffDerivativeConstant k := by
    dsimp [ppPrimeLogCutoffDerivativeConstant]
    apply Finset.sum_nonneg
    intro i hi
    have hiC := Classical.choose_spec (ppPrimeSmoothTransition_deriv_bound i)
    have hkC := Classical.choose_spec (ppPrimeSmoothTransition_deriv_bound (k - i))
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hiC.1.le) hkC.1.le
  let Ksum : ℝ := ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * Real.exp 2 * ppPrimeLogCutoffDerivativeConstant (j - i)
  have hKsum : 0 ≤ Ksum := by
    dsimp [Ksum]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))
      (hCutNonneg (j - i))
  have hmulW (u : ℝ) :
      iteratedDeriv j (E * G) u =
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) *
          iteratedDeriv i E u * iteratedDeriv (j - i) G u := by
    simpa using (iteratedDeriv_mul (n := j) (x := u)
      (hEcont.contDiffAt.of_le (by simp)) (hGcont.contDiffAt.of_le (by simp)))
  have hterm (u : ℝ) (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
      ‖(j.choose i : ℂ) * iteratedDeriv i E u * iteratedDeriv (j - i) G u‖ ≤
        ((j.choose i : ℝ) * Real.exp 2 *
          ppPrimeLogCutoffDerivativeConstant (j - i)) * (δ⁻¹) ^ j := by
    have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hcoeff : 0 ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    by_cases hzero : iteratedDeriv (j - i) G u = 0
    · have hRhs : 0 ≤ ((j.choose i : ℝ) * Real.exp 2 *
          ppPrimeLogCutoffDerivativeConstant (j - i)) * (δ⁻¹) ^ j :=
        mul_nonneg
          (mul_nonneg (mul_nonneg hcoeff (Real.exp_nonneg _))
            (hCutNonneg (j - i)))
          (pow_nonneg (inv_nonneg.mpr hδ.le) _)
      simpa [hzero] using hRhs
    · have huG : u ∈ Function.support (iteratedDeriv (j - i) G) := by
        simpa only [Function.mem_support] using hzero
      have huIcc : u ∈ Set.Icc (-2 : ℝ) 2 := hGderivSupport (j - i) huG
      have hE := hExpBound i u huIcc
      have hG := hGbound (j - i) u
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        (j.choose i : ℝ) * ‖iteratedDeriv i E u‖ *
            ‖iteratedDeriv (j - i) G u‖ ≤
          ((j.choose i : ℝ) * Real.exp 2) *
            (ppPrimeLogCutoffDerivativeConstant (j - i) * (δ⁻¹) ^ (j - i)) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hE hcoeff
              · exact hG
              · exact norm_nonneg _
              · exact mul_nonneg hcoeff (Real.exp_nonneg _)
        _ ≤ ((j.choose i : ℝ) * Real.exp 2 *
            ppPrimeLogCutoffDerivativeConstant (j - i)) * (δ⁻¹) ^ j := by
              calc
                _ = ((j.choose i : ℝ) * Real.exp 2 *
                    ppPrimeLogCutoffDerivativeConstant (j - i)) *
                      (δ⁻¹) ^ (j - i) := by ring
                _ ≤ ((j.choose i : ℝ) * Real.exp 2 *
                    ppPrimeLogCutoffDerivativeConstant (j - i)) *
                      (δ⁻¹) ^ j :=
                  mul_le_mul_of_nonneg_left
                    (pow_le_pow_right₀ hρ (Nat.sub_le _ _))
                    (mul_nonneg (mul_nonneg hcoeff (Real.exp_nonneg _))
                      (hCutNonneg (j - i)))
  have hWpoint (u : ℝ) :
      ‖iteratedDeriv j W u‖ ≤ Ksum * (δ⁻¹) ^ j := by
    rw [hW_eq, hmulW]
    calc
      ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) *
          iteratedDeriv i E u * iteratedDeriv (j - i) G u‖ ≤
        ∑ i ∈ Finset.range (j + 1),
          ‖(j.choose i : ℂ) * iteratedDeriv i E u * iteratedDeriv (j - i) G u‖ :=
            norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1),
          ((j.choose i : ℝ) * Real.exp 2 *
            ppPrimeLogCutoffDerivativeConstant (j - i)) * (δ⁻¹) ^ j := by
              apply Finset.sum_le_sum
              intro i hi
              exact hterm u i hi
      _ = Ksum * (δ⁻¹) ^ j := by
            dsimp [Ksum]
            rw [← Finset.sum_mul]
  have hWderivCompact : HasCompactSupport (iteratedDeriv j W) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (hWderivSupport j)
  have hWderivInt : Integrable (iteratedDeriv j W) :=
    (hWcont.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport
      hWderivCompact
  let Nfun : ℝ → ℝ := fun u => ‖iteratedDeriv j W u‖
  have hNcont : Continuous Nfun :=
    (hWcont.continuous_iteratedDeriv j (by simp)).norm
  have hNsupport : Function.support Nfun ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro u hu
    have hNne : Nfun u ≠ 0 := by
      simpa only [Function.mem_support] using hu
    have hWne : iteratedDeriv j W u ≠ 0 := by
      intro hz
      apply hNne
      simp [Nfun, hz]
    exact hWderivSupport j (by simpa only [Function.mem_support] using hWne)
  have hNsupportIoc : Function.support Nfun ⊆ Set.Ioc (-3 : ℝ) 3 := by
    intro u hu
    rcases hNsupport hu with ⟨hlo, hhi⟩
    exact ⟨by linarith, by linarith⟩
  have hNint : IntervalIntegrable Nfun volume (-3) 3 := hNcont.intervalIntegrable _ _
  have hCint : IntervalIntegrable (fun _ : ℝ => Ksum * (δ⁻¹) ^ j)
      volume (-3) 3 := intervalIntegrable_const
  have hIntervalBound :
      (∫ u in (-3 : ℝ)..3, Nfun u) ≤
        ∫ u in (-3 : ℝ)..3, Ksum * (δ⁻¹) ^ j := by
    apply intervalIntegral.integral_mono_on (by norm_num) hNint hCint
    intro u hu
    exact hWpoint u
  have hIntegralBound :
      (∫ u : ℝ, Nfun u) ≤ 6 * (Ksum * (δ⁻¹) ^ j) := by
    calc
      (∫ u : ℝ, Nfun u) = ∫ u in (-3 : ℝ)..3, Nfun u :=
        (intervalIntegral.integral_eq_integral_of_support_subset (μ := volume)
          hNsupportIoc).symm
      _ ≤ ∫ u in (-3 : ℝ)..3, Ksum * (δ⁻¹) ^ j := hIntervalBound
      _ = 6 * (Ksum * (δ⁻¹) ^ j) := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  have hConstantBound :
      6 * (Ksum * (δ⁻¹) ^ j) ≤
        ppPrimePositiveCutoffLogWeightConstant j * (δ⁻¹) ^ j := by
    have hpow : 0 ≤ (δ⁻¹) ^ j := pow_nonneg (inv_nonneg.mpr hδ.le) _
    dsimp [ppPrimePositiveCutoffLogWeightConstant, Ksum]
    calc
      6 * ((∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * Real.exp 2 *
            ppPrimeLogCutoffDerivativeConstant (j - i)) * (δ⁻¹) ^ j) =
        (6 * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * Real.exp 2 *
            ppPrimeLogCutoffDerivativeConstant (j - i)) * (δ⁻¹) ^ j := by ring
      _ ≤ (6 * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * Real.exp 2 *
            ppPrimeLogCutoffDerivativeConstant (j - i) + 1) * (δ⁻¹) ^ j := by
          exact mul_le_mul_of_nonneg_right (by linarith) hpow
  refine ⟨?_, ?_⟩
  · change Integrable (iteratedDeriv j W)
    exact hWderivInt
  · change (∫ u : ℝ, ‖iteratedDeriv j W u‖) ≤
      ppPrimePositiveCutoffLogWeightConstant j * (δ⁻¹) ^ j
    calc
      (∫ u : ℝ, ‖iteratedDeriv j W u‖) = ∫ u : ℝ, Nfun u := by rfl
      _ ≤ 6 * (Ksum * (δ⁻¹) ^ j) := hIntegralBound
      _ ≤ ppPrimePositiveCutoffLogWeightConstant j * (δ⁻¹) ^ j := hConstantBound

/-- The kernel is Mathlib's Mellin transform, with the positive-base power
rewritten only on the domain of integration. -/
theorem mellinKernel_eq_mellin (g : ℝ → ℝ) (z : ℂ) :
    mellinKernel g z = mellin (fun w : ℝ => (g w : ℂ)) z := by
  unfold mellinKernel mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [smul_eq_mul]
  have hwpos : 0 < w := hw
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hwpos.ne'
  have hlog : Complex.log (w : ℂ) = (Real.log w : ℂ) :=
    (Complex.ofReal_log hwpos.le).symm
  rw [Complex.cpow_def_of_ne_zero hwC, hlog]
  have hexp : Complex.exp (Real.log w : ℂ) = (w : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hwpos]
  calc
    (g w : ℂ) * Complex.exp (z * (Real.log w : ℂ)) / (w : ℂ) =
        (Complex.exp (z * (Real.log w : ℂ)) / (w : ℂ)) * (g w : ℂ) := by ring
    _ = Complex.exp ((z - 1) * (Real.log w : ℂ)) * (g w : ℂ) := by
      rw [← hexp, ← Complex.exp_sub]
      congr 1
      ring
    _ = Complex.exp ((Real.log w : ℂ) * (z - 1)) * (g w : ℂ) := by
      congr 2
      ring

private theorem ppPrime_fourier_norm_le_integral_norm (f : ℝ → ℂ)
    (_hf : Integrable f) (w : ℝ) : ‖𝓕 f w‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) f w

private theorem ppPrime_fourier_polynomial_decay (f : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hderiv : ∀ n : ℕ, Integrable (iteratedDeriv n f))
    (j : ℕ) (A₀ Aⱼ : ℝ) (hA₀ : 0 ≤ A₀)
    (hbound₀ : ∫ u : ℝ, ‖f u‖ ≤ A₀)
    (hboundⱼ : ∫ u : ℝ, ‖iteratedDeriv j f u‖ ≤ Aⱼ) :
    ∀ w : ℝ, ‖𝓕 f w‖ ≤ max (A₀ * 2 ^ j) Aⱼ / (1 + |w|) ^ j := by
  have hfreqFun : 𝓕 (iteratedDeriv j f) = fun w : ℝ =>
      (2 * Real.pi * Complex.I * (w : ℂ)) ^ j • 𝓕 f w := by
    simpa [smul_eq_mul] using
      (Real.fourier_iteratedDeriv (N := ⊤) hf (fun n _ => hderiv n) (by simp))
  have hfreq (w : ℝ) : 𝓕 (iteratedDeriv j f) w =
      (2 * Real.pi * Complex.I * (w : ℂ)) ^ j * 𝓕 f w := by
    simpa [smul_eq_mul] using congrFun hfreqFun w
  have hqnorm (w : ℝ) :
      ‖(2 * Real.pi * Complex.I * (w : ℂ))‖ = 2 * Real.pi * |w| := by
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hI : ‖Complex.I‖ = 1 := by simp
    have hwR : ‖(w : ℂ)‖ = |w| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      _ = ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖Complex.I‖ * ‖(w : ℂ)‖ := by
        simp only [norm_mul]
      _ = 2 * Real.pi * |w| := by rw [htwo, hpi, hI, hwR]; ring
  intro w
  let Aₙ : ℝ := ∫ u : ℝ, ‖iteratedDeriv j f u‖
  have hFourier₀ := ppPrime_fourier_norm_le_integral_norm f (hderiv 0) w
  have hFourier₀' : ‖𝓕 f w‖ ≤ A₀ := by simpa [iteratedDeriv_zero] using hFourier₀.trans hbound₀
  have hden : 0 < (1 + |w|) ^ j := pow_pos (by positivity) _
  rcases le_total |w| 1 with hw | hw
  · apply (le_div_iff₀ hden).2
    have hdenLe : (1 + |w|) ^ j ≤ (2 : ℝ) ^ j :=
      pow_le_pow_left₀ (by positivity) (by linarith) j
    calc
      ‖𝓕 f w‖ * (1 + |w|) ^ j ≤ A₀ * (1 + |w|) ^ j :=
        mul_le_mul_of_nonneg_right hFourier₀' (by positivity)
      _ ≤ A₀ * 2 ^ j := mul_le_mul_of_nonneg_left hdenLe hA₀
      _ ≤ max (A₀ * 2 ^ j) Aⱼ := le_max_left _ _
  · have hqpos : 0 < 2 * Real.pi * |w| := by positivity
    have hqge : 1 + |w| ≤ 2 * Real.pi * |w| := by
      nlinarith [Real.pi_gt_three, abs_nonneg w, hw]
    have hqpow : (1 + |w|) ^ j ≤ (2 * Real.pi * |w|) ^ j :=
      pow_le_pow_left₀ (by positivity) hqge j
    have hFourierN := ppPrime_fourier_norm_le_integral_norm
      (iteratedDeriv j f) (hderiv j) w
    have hFourierN' : ‖𝓕 (iteratedDeriv j f) w‖ ≤ Aⱼ := by
      exact hFourierN.trans (by simpa [Aₙ] using hboundⱼ)
    have hnormN : ‖𝓕 (iteratedDeriv j f) w‖ =
        (2 * Real.pi * |w|) ^ j * ‖𝓕 f w‖ := by
      rw [hfreq w, norm_mul, norm_pow, hqnorm]
    have hprod : ‖𝓕 f w‖ * (1 + |w|) ^ j ≤ Aⱼ := by
      calc
        _ ≤ ‖𝓕 f w‖ * (2 * Real.pi * |w|) ^ j :=
          mul_le_mul_of_nonneg_left hqpow (norm_nonneg _)
        _ = ‖𝓕 (iteratedDeriv j f) w‖ := by rw [hnormN]; ring
        _ ≤ Aⱼ := hFourierN'
    apply (le_div_iff₀ hden).2
    calc
      ‖𝓕 f w‖ * (1 + |w|) ^ j ≤ Aⱼ := hprod
      _ ≤ max (A₀ * 2 ^ j) Aⱼ := le_max_right _ _

/-- Compact support and derivative control give a uniform vertical Mellin bound. -/
private noncomputable def ppPrimeMellinDecayConstant (K : ℕ → ℝ) (j : ℕ) : ℝ :=
  (2 * Real.pi) ^ j * (K 0 * 2 ^ j + K j) + 1

theorem mellinKernel_uniform_decay (g : ℝ → ℝ) (L A : ℝ)
    (hL : 1 ≤ L) (hA : 0 < A) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hsmooth : ∀ α, |α| ≤ 1 →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mellinLogWeight g α))
    (hint : ∀ α, |α| ≤ 1 → ∀ j,
      Integrable (iteratedDeriv j (mellinLogWeight g α)))
    (hbound : ∀ α, |α| ≤ 1 → ∀ j,
      ∫ u : ℝ, ‖iteratedDeriv j (mellinLogWeight g α) u‖ ≤
        K j * Real.rpow L ((j : ℝ) * (A + 4))) :
    ∀ j : ℕ, ∀ α v : ℝ, |α| ≤ 1 →
      ‖mellinKernel g (⟨α, v⟩ : ℂ)‖ ≤
        ppPrimeMellinDecayConstant K j *
          Real.rpow L (((j + 1 : ℕ) : ℝ) * (A + 5)) *
            Real.rpow (1 + |v|) (-(j : ℝ)) := by
  classical
  intro j
  let E : ℝ := ((j + 1 : ℕ) : ℝ) * (A + 5)
  let Mj : ℝ := (2 * Real.pi) ^ j * (K 0 * 2 ^ j + K j) + 1
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hExponent : (j : ℝ) * (A + 4) ≤ E := by
    dsimp [E]
    push_cast
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    nlinarith [hA]
  have hLp : Real.rpow L ((j : ℝ) * (A + 4)) ≤ Real.rpow L E :=
    Real.rpow_le_rpow_of_exponent_le hL hExponent
  have hLE : 1 ≤ Real.rpow L E := Real.one_le_rpow hL hE
  have hK0 : 0 ≤ K 0 := hK 0
  have hKj : 0 ≤ K j := hK j
  have hL0 : 0 ≤ L := le_trans (by norm_num : (0 : ℝ) ≤ 1) hL
  have hMj : 0 < Mj := by dsimp [Mj]; positivity
  intro α v hα
  let f : ℝ → ℂ := mellinLogWeight g α
  have hline : mellinKernel g (⟨α, v⟩ : ℂ) = 𝓕 f (v / (2 * Real.pi)) := by
    rw [mellinKernel_eq_mellin, mellin_eq_fourier]
    have hfun : (fun u : ℝ =>
        Real.exp (-((⟨α, v⟩ : ℂ).re) * u) • (g (Real.exp (-u)) : ℂ)) = f := by
      funext u
      simp [f, mellinLogWeight, Complex.ofReal_exp]
    rw [hfun]
  have hA0 : ∫ u : ℝ, ‖f u‖ ≤ K 0 := by
    have h := hbound α hα 0
    simpa [f, mellinLogWeight, iteratedDeriv_zero, Real.rpow_zero] using h
  have hAj : ∫ u : ℝ, ‖iteratedDeriv j f u‖ ≤
      K j * Real.rpow L ((j : ℝ) * (A + 4)) := by
    exact hbound α hα j
  have hdec := ppPrime_fourier_polynomial_decay f (hsmooth α hα)
    (hint α hα) j (K 0) (K j * Real.rpow L ((j : ℝ) * (A + 4)))
    hK0 hA0 hAj
  let w : ℝ := v / (2 * Real.pi)
  have hv : v = (2 * Real.pi) * w := by
    dsimp [w]
    field_simp
  have habs : |v| = 2 * Real.pi * |w| := by
    rw [hv, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hscale : 1 + |v| ≤ (2 * Real.pi) * (1 + |w|) := by
    rw [habs]
    have hq : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [abs_nonneg w]
  have hscalePow : (1 + |v|) ^ j ≤ (2 * Real.pi) ^ j * (1 + |w|) ^ j := by
    calc
      (1 + |v|) ^ j ≤ ((2 * Real.pi) * (1 + |w|)) ^ j :=
        pow_le_pow_left₀ (by positivity) hscale j
      _ = (2 * Real.pi) ^ j * (1 + |w|) ^ j := by rw [mul_pow]
  have hdenw : 0 < (1 + |w|) ^ j := pow_pos (by positivity) _
  have hdenv : 0 < (1 + |v|) ^ j := pow_pos (by positivity) _
  have hLepos : 0 ≤ Real.rpow L E := le_trans (by norm_num) hLE
  have hTerm0 : 0 ≤ K 0 * 2 ^ j := mul_nonneg hK0 (by positivity)
  have hMax : max (K 0 * 2 ^ j) (K j * Real.rpow L ((j : ℝ) * (A + 4))) ≤
      (K 0 * 2 ^ j + K j) * Real.rpow L E := by
    apply max_le
    · calc
        K 0 * 2 ^ j = (K 0 * 2 ^ j) * 1 := by ring
        _ ≤ (K 0 * 2 ^ j) * Real.rpow L E :=
          mul_le_mul_of_nonneg_left hLE hTerm0
        _ ≤ (K 0 * 2 ^ j + K j) * Real.rpow L E :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hKj) hLepos
    · calc
        K j * Real.rpow L ((j : ℝ) * (A + 4)) ≤ K j * Real.rpow L E :=
          mul_le_mul_of_nonneg_left hLp hKj
        _ ≤ (K 0 * 2 ^ j + K j) * Real.rpow L E :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hTerm0) hLepos
  have hdecLine : ‖𝓕 f w‖ ≤
      max (K 0 * 2 ^ j) (K j * Real.rpow L ((j : ℝ) * (A + 4))) /
        (1 + |w|) ^ j := by
    exact hdec w
  have hratio : 1 / (1 + |w|) ^ j ≤ (2 * Real.pi) ^ j / (1 + |v|) ^ j := by
    apply (div_le_div_iff₀ hdenw hdenv).2
    simpa only [one_mul] using hscalePow
  have hFourier : ‖𝓕 f w‖ ≤
      (K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j * Real.rpow L E /
        (1 + |v|) ^ j := by
    calc
      ‖𝓕 f w‖ ≤
          max (K 0 * 2 ^ j) (K j * Real.rpow L ((j : ℝ) * (A + 4))) /
            (1 + |w|) ^ j := hdecLine
      _ ≤ ((K 0 * 2 ^ j + K j) * Real.rpow L E) /
            (1 + |w|) ^ j :=
        div_le_div_of_nonneg_right hMax (by positivity)
      _ = (K 0 * 2 ^ j + K j) * Real.rpow L E *
            (1 / (1 + |w|) ^ j) := by rw [div_eq_mul_inv, one_div]
      _ ≤ (K 0 * 2 ^ j + K j) * Real.rpow L E *
            ((2 * Real.pi) ^ j / (1 + |v|) ^ j) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j * Real.rpow L E /
            (1 + |v|) ^ j := by ring
  have hC : (K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j ≤ Mj := by
    dsimp [Mj]
    nlinarith [mul_nonneg (add_nonneg (mul_nonneg hK0 (by positivity)) hKj)
      (by positivity : 0 ≤ (2 * Real.pi) ^ j)]
  have hFinal : ‖mellinKernel g (⟨α, v⟩ : ℂ)‖ ≤
      Mj * Real.rpow L E / (1 + |v|) ^ j := by
    calc
      ‖mellinKernel g (⟨α, v⟩ : ℂ)‖ = ‖𝓕 f w‖ := by
        simpa [w] using congrArg norm hline
      _ ≤ (K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j * Real.rpow L E /
            (1 + |v|) ^ j := hFourier
      _ ≤ Mj * Real.rpow L E / (1 + |v|) ^ j := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc
          (K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j * Real.rpow L E =
              ((K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j) * Real.rpow L E := by ring
          _ ≤ Mj * Real.rpow L E := mul_le_mul_of_nonneg_right hC hLepos
  have hRpow : Real.rpow (1 + |v|) (-(j : ℝ)) = 1 / (1 + |v|) ^ j := by
    calc
      Real.rpow (1 + |v|) (-(j : ℝ)) =
          (Real.rpow (1 + |v|) (j : ℝ))⁻¹ :=
        Real.rpow_neg (by positivity) (j : ℝ)
      _ = ((1 + |v|) ^ j)⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast (1 + |v|) j)
      _ = 1 / (1 + |v|) ^ j := by simp [one_div]
  rw [hRpow]
  simpa [E, Mj, ppPrimeMellinDecayConstant, div_eq_mul_inv, mul_assoc] using hFinal

/-- The endpoint cutoff supplies the log-weight hypotheses for uniform Mellin decay. -/
theorem ppPrimePositiveCutoff_mellinKernel_uniform_decay
    (a b L A : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hL : 1 ≤ L) (hA : 0 < A)
    (hδsmall : Real.rpow L (-A - 4) ≤ 1 / 4) :
    ∀ j : ℕ, ∀ α v : ℝ, |α| ≤ 1 →
      ‖mellinKernel (ppPrimePositiveCutoff a b (Real.rpow L (-A - 4)))
          (⟨α, v⟩ : ℂ)‖ ≤
        ppPrimeMellinDecayConstant ppPrimePositiveCutoffLogWeightConstant j *
          Real.rpow L (((j + 1 : ℕ) : ℝ) * (A + 5)) *
            Real.rpow (1 + |v|) (-(j : ℝ)) := by
  let δ : ℝ := Real.rpow L (-A - 4)
  let K : ℕ → ℝ := ppPrimePositiveCutoffLogWeightConstant
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact Real.rpow_pos_of_pos hLpos _
  have hδinv : δ⁻¹ = Real.rpow L (A + 4) := by
    dsimp [δ]
    rw [show -A - 4 = -(A + 4) by ring, Real.rpow_neg hLpos.le]
    simp
  have hpow (j : ℕ) : (δ⁻¹) ^ j = Real.rpow L ((j : ℝ) * (A + 4)) := by
    rw [hδinv]
    calc
      (Real.rpow L (A + 4)) ^ j = (Real.rpow L (j : ℝ)) ^ (A + 4) :=
        by
          have hcomm := Real.rpow_pow_comm hLpos.le (A + 4) j
          rw [← Real.rpow_natCast L j] at hcomm
          exact hcomm
      _ = Real.rpow L ((j : ℝ) * (A + 4)) :=
        (Real.rpow_mul hLpos.le (j : ℝ) (A + 4)).symm
  have hCutNonneg (j : ℕ) : 0 ≤ ppPrimeLogCutoffDerivativeConstant j := by
    dsimp [ppPrimeLogCutoffDerivativeConstant]
    apply Finset.sum_nonneg
    intro i hi
    have hiC := Classical.choose_spec (ppPrimeSmoothTransition_deriv_bound i)
    have hkC := Classical.choose_spec (ppPrimeSmoothTransition_deriv_bound (j - i))
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hiC.1.le) hkC.1.le
  have hK : ∀ j, 0 ≤ K j := by
    intro j
    dsimp [K, ppPrimePositiveCutoffLogWeightConstant]
    have hsum : 0 ≤ ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * Real.exp 2 * ppPrimeLogCutoffDerivativeConstant (j - i) := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))
        (hCutNonneg (j - i))
    positivity
  apply mellinKernel_uniform_decay
    (g := ppPrimePositiveCutoff a b δ) (L := L) (A := A) hL hA K hK
  · intro α hα
    simpa [δ] using ppPrimePositiveCutoff_logWeight_contDiff a b δ α
  · intro α hα j
    exact (ppPrimePositiveCutoff_logWeight_lintegral_bound
      a b δ α ha hab hb hδpos hδsmall hα j).1
  · intro α hα j
    have hbound := (ppPrimePositiveCutoff_logWeight_lintegral_bound
      a b δ α ha hab hb hδpos hδsmall hα j).2
    simpa only [K, hpow j] using hbound

/-- Mellin inversion on a compactly supported smooth positive-coordinate weight. -/
theorem mellinKernel_inversion (g : ℝ → ℝ)
    (hlogSmooth : ∀ α, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mellinLogWeight g α))
    (hsupport : Function.support g ⊆ Set.Icc (1 / 2 : ℝ) 3)
    (c w : ℝ) (hw : 0 < w) :
    (g w : ℂ) = (1 / (2 * Real.pi) : ℂ) *
      ∫ v : ℝ, mellinKernel g (⟨c, v⟩ : ℂ) *
        Complex.exp (-((⟨c, v⟩ : ℂ) * Real.log w)) := by
  classical
  let f : ℝ → ℂ := mellinLogWeight g c
  have hfsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := hlogSmooth c
  have hfsupport : Function.support f ⊆ Set.Icc (-Real.log 3) (-Real.log (1 / 2)) := by
    intro u hu
    have hfu : f u ≠ 0 := by
      simpa only [Function.mem_support] using hu
    have hgu : g (Real.exp (-u)) ≠ 0 := by
      intro hz
      apply hfu
      simp [f, mellinLogWeight, hz]
    have hmem : Real.exp (-u) ∈ Function.support g := by
      simpa only [Function.mem_support] using hgu
    rcases hsupport hmem with ⟨hlo, hhi⟩
    constructor
    · have hlog := Real.log_le_log (Real.exp_pos (-u)) hhi
      have hlog' : -u ≤ Real.log 3 := by simpa only [Real.log_exp] using hlog
      linarith
    · have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hlo
      have hlog' : Real.log (1 / 2) ≤ -u := by simpa only [Real.log_exp] using hlog
      linarith
  have hfcompact : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hfsupport
  let F : SchwartzMap ℝ ℂ := hfcompact.toSchwartzMap hfsmooth
  have hFcoe : (F : ℝ → ℂ) = f := rfl
  have hline (v : ℝ) :
      mellinKernel g (⟨c, v⟩ : ℂ) = 𝓕 f (v / (2 * Real.pi)) := by
    rw [mellinKernel_eq_mellin, mellin_eq_fourier]
    have hfun : (fun u : ℝ =>
        Real.exp (-((⟨c, v⟩ : ℂ).re) * u) • (g (Real.exp (-u)) : ℂ)) = f := by
      funext u
      simp [f, mellinLogWeight, Complex.ofReal_exp]
    rw [hfun]
  have hFt : 𝓕 f = ((𝓕 F : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    rw [SchwartzMap.fourier_coe]
    rfl
  let x : ℝ := -Real.log w
  have hInv : 𝓕⁻ (𝓕 f) x = f x := by
    exact congrFun (F.continuous.fourierInv_fourier_eq F.integrable
      (𝓕 F).integrable) x
  have hInvIntegral : 𝓕⁻ (𝓕 f) x =
      ∫ y : ℝ, Complex.exp ((↑(2 * Real.pi * (y * x) : ℝ) : ℂ) * Complex.I) * 𝓕 f y := by
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply, smul_eq_mul]
  let H : ℝ → ℂ := fun v => mellinKernel g (⟨c, v⟩ : ℂ) *
    Complex.exp (Complex.I * (v : ℂ) * (x : ℂ))
  have hπ : 0 < 2 * Real.pi := by positivity
  have hchange : (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) •
      ∫ y : ℝ, H ((2 * Real.pi) * y) := by
    have h := Measure.integral_comp_mul_left H (2 * Real.pi)
    rw [abs_of_pos (inv_pos.mpr hπ)] at h
    calc
      (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) •
          ((2 * Real.pi : ℝ)⁻¹ • ∫ v : ℝ, H v) := by
            rw [smul_smul, mul_inv_cancel₀ hπ.ne', one_smul]
      _ = (2 * Real.pi : ℝ) • ∫ y : ℝ, H ((2 * Real.pi) * y) := by rw [h.symm]
  have hscaled (y : ℝ) :
      H ((2 * Real.pi) * y) =
        Complex.exp ((↑(2 * Real.pi * (y * x) : ℝ) : ℂ) * Complex.I) * 𝓕 f y := by
    dsimp [H]
    rw [hline]
    have hfreq : (2 * Real.pi * y) / (2 * Real.pi) = y := by
      field_simp [Real.pi_ne_zero]
    rw [hfreq]
    have hexp : Complex.I * (↑(2 * Real.pi * y : ℝ) : ℂ) * (x : ℂ) =
        (↑(2 * Real.pi * (y * x) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [congrArg Complex.exp hexp]
    ring
  have hscaledIntegral : (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, H v =
      ∫ y : ℝ, Complex.exp ((↑(2 * Real.pi * (y * x) : ℝ) : ℂ) * Complex.I) * 𝓕 f y := by
    rw [hchange]
    have hchange' : (2 * Real.pi : ℝ) • (∫ y : ℝ, H ((2 * Real.pi) * y)) =
        ((2 * Real.pi : ℝ) : ℂ) * ∫ y : ℝ, H ((2 * Real.pi) * y) := by
      rfl
    have hcoef : (1 / (2 * Real.pi) : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = 1 := by
      norm_cast
      field_simp [Real.pi_ne_zero]
    calc
      (1 / (2 * Real.pi) : ℂ) *
          ((2 * Real.pi : ℝ) • ∫ y : ℝ, H ((2 * Real.pi) * y)) =
          (1 / (2 * Real.pi) : ℂ) *
            (((2 * Real.pi : ℝ) : ℂ) * ∫ y : ℝ, H ((2 * Real.pi) * y)) := by rw [hchange']
      _ = ((1 / (2 * Real.pi) : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) *
          ∫ y : ℝ, H ((2 * Real.pi) * y) := by rw [mul_assoc]
      _ = ∫ y : ℝ, H ((2 * Real.pi) * y) := by rw [hcoef, one_mul]
      _ = ∫ y : ℝ, Complex.exp ((↑(2 * Real.pi * (y * x) : ℝ) : ℂ) * Complex.I) *
          𝓕 f y := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hscaled
  have hfAt : f x =
      (Real.exp (-c * x) : ℂ) * (g (Real.exp (-x)) : ℂ) := by
    rfl
  have htarget : (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, H v = f x := by
    rw [hscaledIntegral, ← hInvIntegral, hInv]
  have hlogw : Real.exp (-x) = w := by
    simp [x, Real.exp_log hw]
  have hfinal : f x * (Real.exp (-c * x) : ℂ)⁻¹ = (g w : ℂ) := by
    rw [hfAt, hlogw]
    have he : (Real.exp (-c * x) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
    field_simp
  calc
    (g w : ℂ) = f x * (Real.exp (-c * x) : ℂ)⁻¹ := hfinal.symm
    _ = ((1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, H v) *
        (Real.exp (-c * x) : ℂ)⁻¹ := by rw [htarget]
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ,
        mellinKernel g (⟨c, v⟩ : ℂ) *
          Complex.exp (-((⟨c, v⟩ : ℂ) * Real.log w)) := by
      have hE : (Real.exp (-c * x) : ℂ)⁻¹ =
        Complex.exp ((c : ℂ) * (x : ℂ)) := by
        rw [Complex.ofReal_exp]
        rw [← Complex.exp_neg]
        congr 1
        push_cast
        ring
      have hphase (v : ℝ) :
          Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
              Complex.exp ((c : ℂ) * (x : ℂ)) =
            Complex.exp (-((⟨c, v⟩ : ℂ) * (Real.log w : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        have hx : (x : ℂ) = -(Real.log w : ℂ) := by
          simp [x]
        rw [hx]
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      calc
        _ = (1 / (2 * Real.pi) : ℂ) *
            ((∫ v : ℝ, H v) * (Real.exp (-c * x) : ℂ)⁻¹) := by ring
        _ = (1 / (2 * Real.pi) : ℂ) *
            ∫ v : ℝ, H v * (Real.exp (-c * x) : ℂ)⁻¹ := by rw [integral_mul_const]
        _ = (1 / (2 * Real.pi) : ℂ) *
            ∫ v : ℝ, mellinKernel g (⟨c, v⟩ : ℂ) *
              Complex.exp (-((⟨c, v⟩ : ℂ) * (Real.log w : ℂ))) := by
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun v => by
            dsimp [H]
            rw [hE]
            calc
              mellinKernel g (⟨c, v⟩ : ℂ) *
                  Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
                    Complex.exp ((c : ℂ) * (x : ℂ)) =
                  mellinKernel g (⟨c, v⟩ : ℂ) *
                    (Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
                      Complex.exp ((c : ℂ) * (x : ℂ))) := by ring
              _ = mellinKernel g (⟨c, v⟩ : ℂ) *
                  Complex.exp (-((⟨c, v⟩ : ℂ) * (Real.log w : ℂ))) := by rw [hphase]

private theorem ppPrimeFinset_real_interval_card_le
    (S : Finset ℕ) (a b : ℝ) (hab : a ≤ b)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) :
    (S.card : ℝ) ≤ b - a + 1 := by
  let lo : ℕ := ⌈a⌉₊
  let hi : ℕ := ⌊b⌋₊
  by_cases hne : S.Nonempty
  · obtain ⟨n, hn⟩ := hne
    have hnlo : lo ≤ n := by
      dsimp [lo]
      exact Nat.ceil_le.2 (hS n hn).1
    have hnhi : n ≤ hi := by
      dsimp [hi]
      exact Nat.le_floor (hS n hn).2
    have hlohi : lo ≤ hi := hnlo.trans hnhi
    have hsubset : S ⊆ Finset.Icc lo hi := by
      intro k hk
      simp only [Finset.mem_Icc]
      exact ⟨by
        dsimp [lo]
        exact Nat.ceil_le.2 (hS k hk).1,
        by
        dsimp [hi]
        exact Nat.le_floor (hS k hk).2⟩
    have hcard : S.card ≤ hi + 1 - lo := by
      calc
        S.card ≤ (Finset.Icc lo hi).card := Finset.card_le_card hsubset
        _ = hi + 1 - lo := by simp
    have hsub : lo ≤ hi + 1 := by omega
    have hcastSub : ((hi + 1 - lo : ℕ) : ℝ) = (hi : ℝ) + 1 - (lo : ℝ) := by
      rw [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]
    have hcardR : (S.card : ℝ) ≤ (hi + 1 - lo : ℕ) := by exact_mod_cast hcard
    have hloReal : a ≤ (lo : ℝ) := by
      dsimp [lo]
      exact Nat.le_ceil a
    have hb0 : 0 ≤ b := le_trans (Nat.cast_nonneg n) (hS n hn).2
    have hhiReal : (hi : ℝ) ≤ b := by
      dsimp [hi]
      exact Nat.floor_le hb0
    rw [hcastSub] at hcardR
    nlinarith
  · have hcard : S.card = 0 := by
      by_contra h
      have hpos : 0 < S.card := Nat.pos_of_ne_zero h
      exact hne (Finset.card_pos.mp hpos)
    rw [hcard]
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hR : (0 : ℝ) ≤ b - a + 1 := by
      calc
        0 ≤ b - a := hba
        _ ≤ b - a + 1 := by linarith
    simpa using hR

/-- Smoothing an integer interval changes the Mangoldt polynomial only near its endpoints. -/
theorem ppPrimePositiveCutoff_mangoldt_smoothing_error
    {N : ℝ} (hN : 4 ≤ N) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (m u : ℕ)
    (hm : N ≤ (m : ℝ)) (hmu : (m : ℝ) ≤ u)
    (hu : (u : ℝ) ≤ 2 * N) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 4) :
    ‖mangoldtIntervalPolynomial N q χ t (Set.Icc m u) -
      smoothedMangoldtPolynomial N q χ t
        (ppPrimePositiveCutoff ((m : ℝ) / N) ((u : ℝ) / N) δ)‖ ≤
      20 * (δ + 1 / N) * Real.log (3 * N) := by
  let a : ℝ := (m : ℝ) / N
  let b : ℝ := (u : ℝ) / N
  let g : ℝ → ℝ := ppPrimePositiveCutoff a b δ
  let S : Finset ℕ := (Finset.range (⌊3 * N⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n)
  let Q : ℕ → Prop := fun n => m ≤ n ∧ n ≤ u
  let W : ℕ → ℂ := fun n =>
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) *
      Complex.exp ((-1 + Complex.I * t) * Real.log (n : ℝ))
  let E : ℕ → ℂ := fun n =>
    (if Q n then W n else 0) - W n * (g ((n : ℝ) / N) : ℂ)
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hfinite :
      (Finset.range (⌊2 * N⌋₊ + 1)).filter
        (fun n : ℕ => 1 ≤ n ∧ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N ∧ n ∈ Set.Icc m u) =
        S.filter Q := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, S, Q]
    constructor
    · rintro ⟨_, hnpos, hnN, hn2, hIcc⟩
      rcases Set.mem_Icc.mp hIcc with ⟨hmn, hnu⟩
      have hn3 : (n : ℝ) ≤ 3 * N := by nlinarith [hn2, hN]
      have hnfloor : n ≤ ⌊3 * N⌋₊ := Nat.le_floor hn3
      exact ⟨⟨by omega, hnpos⟩, ⟨hmn, hnu⟩⟩
    · rintro ⟨⟨_, hnpos⟩, ⟨hmn, hnu⟩⟩
      have hnN : N ≤ (n : ℝ) := le_trans hm (by exact_mod_cast hmn)
      have hn2 : (n : ℝ) ≤ 2 * N := le_trans (by exact_mod_cast hnu) hu
      have hnfloor : n ≤ ⌊2 * N⌋₊ := Nat.le_floor hn2
      exact ⟨by omega, hnpos, hnN, hn2, Set.mem_Icc.mpr ⟨hmn, hnu⟩⟩
  have hsharp : mangoldtIntervalPolynomial N q χ t (Set.Icc m u) =
      ∑ n ∈ S.filter Q, W n := by
    unfold mangoldtIntervalPolynomial
    simpa [W] using congrArg (fun F : Finset ℕ => ∑ n ∈ F, W n) hfinite
  have hsmooth : smoothedMangoldtPolynomial N q χ t g =
      ∑ n ∈ S, W n * (g ((n : ℝ) / N) : ℂ) := rfl
  have hsum :
    mangoldtIntervalPolynomial N q χ t (Set.Icc m u) -
        smoothedMangoldtPolynomial N q χ t g = ∑ n ∈ S, E n := by
    rw [hsharp, hsmooth, Finset.sum_filter, Finset.sum_sub_distrib]
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact (one_le_div hNpos).2 hm
  have hab : a ≤ b := by
    dsimp [a, b]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmu) hNpos.le
  have hb2 : b ≤ 2 := by
    dsimp [b]
    exact (div_le_iff₀ hNpos).2 hu
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) ha1
  have hbPos : 0 < b := lt_of_lt_of_le haPos hab
  have hcutBounds (w : ℝ) : 0 ≤ g w ∧ g w ≤ 1 := by
    simpa [g] using ppPrimePositiveCutoff_nonneg_le_one a b δ w
  have hcutSupport : Function.support g ⊆
      Set.Icc (a * Real.exp (-δ)) (b * Real.exp δ) := by
    exact ppPrimePositiveCutoff_support a b δ haPos hbPos hδ
  have hNa : N * a = (m : ℝ) := by
    dsimp [a]
    field_simp
  have hNb : N * b = (u : ℝ) := by
    dsimp [b]
    field_simp
  have hinteriorQ (n : ℕ) (hlo : a ≤ (n : ℝ) / N)
      (hhi : (n : ℝ) / N ≤ b) : Q n := by
    constructor
    · have hmul := (div_le_iff₀ hNpos).1 (by simpa [a] using hlo)
      have hcancel : (n : ℝ) / N * N = (n : ℝ) := by field_simp
      rw [hcancel] at hmul
      exact_mod_cast hmul
    · have hmul := (div_le_iff₀ hNpos).1 (by simpa [b] using hhi)
      have hcancel : (u : ℝ) / N * N = (u : ℝ) := by field_simp
      rw [hcancel] at hmul
      exact_mod_cast hmul
  have hQinterior (n : ℕ) (hq : Q n) :
      a ≤ (n : ℝ) / N ∧ (n : ℝ) / N ≤ b := by
    rcases hq with ⟨hmn, hnu⟩
    constructor
    · dsimp [a]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmn) hNpos.le
    · dsimp [b]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hnu) hNpos.le
  let Bad : ℕ → Prop := fun n =>
    (a * Real.exp (-δ) ≤ (n : ℝ) / N ∧ (n : ℝ) / N ≤ a) ∨
      (b ≤ (n : ℝ) / N ∧ (n : ℝ) / N ≤ b * Real.exp δ)
  have hEzero_or_bad (n : ℕ) : E n = 0 ∨ Bad n := by
    by_cases hq : Q n
    · have hplateau : g ((n : ℝ) / N) = 1 := by
        exact ppPrimePositiveCutoff_eq_one a b δ ((n : ℝ) / N)
          haPos hδ (hQinterior n hq).1 (hQinterior n hq).2
      left
      simp [E, hq, hplateau]
    · by_cases hg : g ((n : ℝ) / N) = 0
      · left
        simp [E, hq, hg]
      · right
        have hwSupport : (n : ℝ) / N ∈ Function.support g := by
          simpa only [Function.mem_support] using hg
        rcases hcutSupport hwSupport with ⟨hlo, hhi⟩
        by_cases hleft : (n : ℝ) / N < a
        · exact Or.inl ⟨hlo, hleft.le⟩
        · by_cases hright : b < (n : ℝ) / N
          · exact Or.inr ⟨hright.le, hhi⟩
          · have hQ' := hinteriorQ n (le_of_not_gt hleft) (le_of_not_gt hright)
            exact False.elim (hq hQ')
  have hδabs : |δ| ≤ 1 := by
    rw [abs_of_pos hδ]
    linarith [hδsmall]
  have hExpNegAbs : |Real.exp (-δ) - 1| ≤ 2 * δ := by
    have h := Real.abs_exp_sub_one_le (x := -δ)
      (by simpa [abs_neg] using hδabs)
    simpa [abs_of_pos hδ] using h
  have hExpPosAbs : |Real.exp δ - 1| ≤ 2 * δ := by
    simpa [abs_of_pos hδ] using Real.abs_exp_sub_one_le hδabs
  have hExpNegOne : Real.exp (-δ) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hExpPosOne : 1 ≤ Real.exp δ := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hδ.le
  have hGapNeg : 0 ≤ 1 - Real.exp (-δ) ∧ 1 - Real.exp (-δ) ≤ 2 * δ := by
    constructor
    · exact sub_nonneg.mpr hExpNegOne
    · have h := (abs_le.mp hExpNegAbs).1
      linarith
  have hGapPos : 0 ≤ Real.exp δ - 1 ∧ Real.exp δ - 1 ≤ 2 * δ := by
    constructor
    · linarith
    · have h := (abs_le.mp hExpPosAbs).2
      linarith
  have hExpHalf : (1 / 2 : ℝ) ≤ Real.exp (-δ) := by
    have h := (abs_le.mp hExpNegAbs).1
    have hsmall : 2 * δ ≤ 1 / 2 := by linarith [hδsmall]
    linarith
  let Lower : Finset ℕ := S.filter (fun n =>
    a * Real.exp (-δ) ≤ (n : ℝ) / N ∧ (n : ℝ) / N ≤ a)
  let Upper : Finset ℕ := S.filter (fun n =>
    b ≤ (n : ℝ) / N ∧ (n : ℝ) / N ≤ b * Real.exp δ)
  let BadFin : Finset ℕ := S.filter Bad
  have hLowerOrder : (m : ℝ) * Real.exp (-δ) ≤ (m : ℝ) := by
    calc
      (m : ℝ) * Real.exp (-δ) ≤ (m : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hExpNegOne (Nat.cast_nonneg m)
      _ = (m : ℝ) := by ring
  have hUpperOrder : (u : ℝ) ≤ (u : ℝ) * Real.exp δ := by
    calc
      (u : ℝ) = (u : ℝ) * 1 := by ring
      _ ≤ (u : ℝ) * Real.exp δ :=
        mul_le_mul_of_nonneg_left hExpPosOne (Nat.cast_nonneg u)
  have hLowerCard : (Lower.card : ℝ) ≤
      (m : ℝ) - (m : ℝ) * Real.exp (-δ) + 1 := by
    apply ppPrimeFinset_real_interval_card_le Lower
      ((m : ℝ) * Real.exp (-δ)) (m : ℝ) hLowerOrder
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnS, hnBounds⟩
    rcases hnBounds with ⟨hnLow, hnHigh⟩
    constructor
    · have hscale := mul_le_mul_of_nonneg_left hnLow hNpos.le
      have hleft : N * (a * Real.exp (-δ)) = (m : ℝ) * Real.exp (-δ) := by
        rw [← mul_assoc, hNa]
      calc
        (m : ℝ) * Real.exp (-δ) = N * (a * Real.exp (-δ)) := hleft.symm
        _ ≤ N * ((n : ℝ) / N) := hscale
        _ = (n : ℝ) := by field_simp
    · calc
        (n : ℝ) = N * ((n : ℝ) / N) := by field_simp
        _ ≤ N * a := mul_le_mul_of_nonneg_left hnHigh hNpos.le
        _ = (m : ℝ) := hNa
  have hUpperCard : (Upper.card : ℝ) ≤
      (u : ℝ) * Real.exp δ - (u : ℝ) + 1 := by
    apply ppPrimeFinset_real_interval_card_le Upper
      (u : ℝ) ((u : ℝ) * Real.exp δ) hUpperOrder
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnS, hnBounds⟩
    rcases hnBounds with ⟨hnLow, hnHigh⟩
    constructor
    · calc
        (u : ℝ) = N * b := hNb.symm
        _ ≤ N * ((n : ℝ) / N) := mul_le_mul_of_nonneg_left hnLow hNpos.le
        _ = (n : ℝ) := by field_simp
    · have hscale := mul_le_mul_of_nonneg_left hnHigh hNpos.le
      have hright : N * (b * Real.exp δ) = (u : ℝ) * Real.exp δ := by
        rw [← mul_assoc, hNb]
      calc
        (n : ℝ) = N * ((n : ℝ) / N) := by field_simp
        _ ≤ N * (b * Real.exp δ) := hscale
        _ = (u : ℝ) * Real.exp δ := hright
  have hmle2 : (m : ℝ) ≤ 2 * N := le_trans (by exact_mod_cast hmu) hu
  have hule2 : (u : ℝ) ≤ 2 * N := by exact_mod_cast hu
  have hLowerLength : (m : ℝ) - (m : ℝ) * Real.exp (-δ) ≤ 4 * N * δ := by
    calc
      (m : ℝ) - (m : ℝ) * Real.exp (-δ) =
          (m : ℝ) * (1 - Real.exp (-δ)) := by ring
      _ ≤ (2 * N) * (1 - Real.exp (-δ)) :=
        mul_le_mul_of_nonneg_right hmle2 hGapNeg.1
      _ ≤ (2 * N) * (2 * δ) :=
        mul_le_mul_of_nonneg_left hGapNeg.2 (by positivity)
      _ = 4 * N * δ := by ring
  have hUpperLength : (u : ℝ) * Real.exp δ - (u : ℝ) ≤ 4 * N * δ := by
    calc
      (u : ℝ) * Real.exp δ - (u : ℝ) =
          (u : ℝ) * (Real.exp δ - 1) := by ring
      _ ≤ (2 * N) * (Real.exp δ - 1) :=
        mul_le_mul_of_nonneg_right hule2 hGapPos.1
      _ ≤ (2 * N) * (2 * δ) :=
        mul_le_mul_of_nonneg_left hGapPos.2 (by positivity)
      _ = 4 * N * δ := by ring
  have hLowerCard' : (Lower.card : ℝ) ≤ 4 * N * δ + 1 := by
    calc
      (Lower.card : ℝ) ≤ (m : ℝ) - (m : ℝ) * Real.exp (-δ) + 1 := hLowerCard
      _ ≤ 4 * N * δ + 1 := by linarith [hLowerLength]
  have hUpperCard' : (Upper.card : ℝ) ≤ 4 * N * δ + 1 := by
    calc
      (Upper.card : ℝ) ≤ (u : ℝ) * Real.exp δ - (u : ℝ) + 1 := hUpperCard
      _ ≤ 4 * N * δ + 1 := by linarith [hUpperLength]
  have hBadSub : BadFin ⊆ Lower ∪ Upper := by
    intro n hn
    simp only [BadFin, Lower, Upper, Finset.mem_filter, Finset.mem_union, Bad] at hn ⊢
    rcases hn with ⟨hnS, hbad⟩
    rcases hbad with hlow | hhigh
    · exact Or.inl ⟨hnS, hlow⟩
    · exact Or.inr ⟨hnS, hhigh⟩
  have hBadCardNat : BadFin.card ≤ Lower.card + Upper.card := by
    calc
      BadFin.card ≤ (Lower ∪ Upper).card := Finset.card_le_card hBadSub
      _ ≤ Lower.card + Upper.card := Finset.card_union_le _ _
  have hBadCard : (BadFin.card : ℝ) ≤ 8 * N * δ + 2 := by
    calc
      (BadFin.card : ℝ) ≤ (Lower.card : ℝ) + (Upper.card : ℝ) := by
        exact_mod_cast hBadCardNat
      _ ≤ (4 * N * δ + 1) + (4 * N * δ + 1) := add_le_add hLowerCard' hUpperCard'
      _ = 8 * N * δ + 2 := by ring
  have hlog3nonneg : 0 ≤ Real.log (3 * N) :=
    Real.log_nonneg (by nlinarith [hN])
  have htermnonneg : 0 ≤ (2 / N) * Real.log (3 * N) :=
    mul_nonneg (by positivity) hlog3nonneg
  have hWbound (n : ℕ) (hnS : n ∈ S) (hbad : Bad n) :
      ‖W n‖ ≤ (2 / N) * Real.log (3 * N) := by
    rcases Finset.mem_filter.mp hnS with ⟨hnrange, hnpos⟩
    have hnFloor : n ≤ ⌊3 * N⌋₊ := by
      have hlt := Finset.mem_range.mp hnrange
      omega
    have hnUpper : (n : ℝ) ≤ 3 * N :=
      le_trans (Nat.cast_le.mpr hnFloor) (Nat.floor_le (by positivity))
    have hnPosReal : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hnpos)
    have hhalf : (1 / 2 : ℝ) ≤ (n : ℝ) / N := by
      rcases hbad with hlow | hhigh
      · have hfirst : (1 / 2 : ℝ) ≤ a * Real.exp (-δ) := by
          calc
            (1 / 2 : ℝ) ≤ Real.exp (-δ) := hExpHalf
            _ = 1 * Real.exp (-δ) := by ring
            _ ≤ a * Real.exp (-δ) :=
              mul_le_mul_of_nonneg_right ha1 (Real.exp_nonneg _)
        exact le_trans hfirst hlow.1
      · have hb1 : 1 ≤ b := le_trans ha1 hab
        exact le_trans (by linarith) hhigh.1
    have hnHalf : N / 2 ≤ (n : ℝ) := by
      have h := (le_div_iff₀ hNpos).1 hhalf
      nlinarith
    have hlogn : Real.log (n : ℝ) ≤ Real.log (3 * N) :=
      Real.log_le_log hnPosReal hnUpper
    have hLambdaNonneg : 0 ≤ ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hLambda : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ Real.log (3 * N) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLambdaNonneg]
      exact (ArithmeticFunction.vonMangoldt_le_log).trans hlogn
    have hχ : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one _
    have hphaseRe :
        (((-1 + Complex.I * t) * Real.log (n : ℝ) : ℂ).re) = -Real.log (n : ℝ) := by
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, one_mul]
      norm_num
    have hphase :
        ‖Complex.exp ((-1 + Complex.I * t) * Real.log (n : ℝ))‖ = (n : ℝ)⁻¹ := by
      rw [Complex.norm_exp, hphaseRe, Real.exp_neg, Real.exp_log hnPosReal]
    have hinv : (n : ℝ)⁻¹ ≤ 2 / N := by
      calc
        (n : ℝ)⁻¹ ≤ (N / 2)⁻¹ :=
          (inv_le_inv₀ hnPosReal (by positivity)).2 hnHalf
        _ = 2 / N := by field_simp
    have hfirst : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ *
        ‖χ (n : ZMod q)‖ ≤ Real.log (3 * N) * 1 :=
      mul_le_mul hLambda hχ (norm_nonneg _) hlog3nonneg
    calc
      ‖W n‖ = ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ *
          ‖χ (n : ZMod q)‖ *
            ‖Complex.exp ((-1 + Complex.I * t) * Real.log (n : ℝ))‖ := by
          simp [W, mul_assoc]
      _ ≤ Real.log (3 * N) * 1 * (2 / N) := by
          calc
            _ ≤ (Real.log (3 * N) * 1) *
                ‖Complex.exp ((-1 + Complex.I * t) * Real.log (n : ℝ))‖ :=
              mul_le_mul_of_nonneg_right hfirst (norm_nonneg _)
            _ ≤ (Real.log (3 * N) * 1) * (2 / N) :=
              mul_le_mul_of_nonneg_left (by rw [hphase]; exact hinv) (by positivity)
      _ = (2 / N) * Real.log (3 * N) := by ring
  have hEbound (n : ℕ) (hnS : n ∈ S) (hbad : Bad n) :
      ‖E n‖ ≤ (2 / N) * Real.log (3 * N) := by
    by_cases hq : Q n
    · have hplateau : g ((n : ℝ) / N) = 1 := by
        exact ppPrimePositiveCutoff_eq_one a b δ ((n : ℝ) / N)
          haPos hδ (hQinterior n hq).1 (hQinterior n hq).2
      have hzero : E n = 0 := by simp [E, hq, hplateau]
      rw [hzero]
      simpa using htermnonneg
    · have hg := hcutBounds ((n : ℝ) / N)
      have hgnorm : ‖(g ((n : ℝ) / N) : ℂ)‖ = g ((n : ℝ) / N) := by
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg.1]
      simp only [E, if_neg hq, zero_sub, norm_neg, norm_mul]
      rw [hgnorm]
      calc
        ‖W n‖ * g ((n : ℝ) / N) ≤
            ((2 / N) * Real.log (3 * N)) * g ((n : ℝ) / N) :=
          mul_le_mul_of_nonneg_right (hWbound n hnS hbad) hg.1
        _ ≤ ((2 / N) * Real.log (3 * N)) * 1 :=
          mul_le_mul_of_nonneg_left hg.2 htermnonneg
        _ = (2 / N) * Real.log (3 * N) := by ring
  have hsumNorm : ‖∑ n ∈ S, E n‖ ≤ (BadFin.card : ℝ) *
      ((2 / N) * Real.log (3 * N)) := by
    calc
      ‖∑ n ∈ S, E n‖ ≤ ∑ n ∈ S, ‖E n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S, if Bad n then (2 / N) * Real.log (3 * N) else 0 := by
        apply Finset.sum_le_sum
        intro n hnS
        by_cases hbad : Bad n
        · simpa [hbad] using hEbound n hnS hbad
        · have hzero := (hEzero_or_bad n).resolve_right hbad
          simp [hbad, hzero]
      _ = (BadFin.card : ℝ) * ((2 / N) * Real.log (3 * N)) := by
        rw [← Finset.sum_filter]
        simp [BadFin, smul_eq_mul]
  rw [hsum]
  calc
    ‖∑ n ∈ S, E n‖ ≤ (BadFin.card : ℝ) * ((2 / N) * Real.log (3 * N)) := hsumNorm
    _ ≤ (8 * N * δ + 2) * ((2 / N) * Real.log (3 * N)) :=
      mul_le_mul_of_nonneg_right hBadCard htermnonneg
    _ = (16 * δ + 4 / N) * Real.log (3 * N) := by
      field_simp [ne_of_gt hNpos]
      ring
    _ ≤ 20 * (δ + 1 / N) * Real.log (3 * N) := by
      apply mul_le_mul_of_nonneg_right _ hlog3nonneg
      have hδ4 : 16 * δ ≤ 20 * δ := by nlinarith [hδ.le]
      have hInvNonneg : 0 ≤ (1 / N : ℝ) := by positivity
      have hInv4 : 4 / N ≤ 20 / N := by
        have h := mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 20) hInvNonneg
        simpa [div_eq_mul_inv] using h
      calc
        16 * δ + 4 / N ≤ 20 * δ + 4 / N := add_le_add hδ4 le_rfl
        _ ≤ 20 * δ + 20 / N := add_le_add le_rfl hInv4
        _ = 20 * (δ + 1 / N) := by ring

private theorem ppPrimeNatInterval_representation
    {N : ℝ} {I : Set ℕ} (hI : IsNatInterval I)
    (hbound : I ⊆ {n : ℕ | N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N})
    (hne : I.Nonempty) :
    ∃ m u : ℕ, m ∈ I ∧ u ∈ I ∧ I = Set.Icc m u ∧
      N ≤ (m : ℝ) ∧ (u : ℝ) ≤ 2 * N := by
  have hfin : I.Finite := (Set.finite_Iic ⌊2 * N⌋₊).subset (by
    intro n hn
    simp only [Set.mem_Iic]
    exact Nat.le_floor (hbound hn).2)
  let F := hfin.toFinset
  have hneF : F.Nonempty := by
    rcases hne with ⟨n, hn⟩
    exact ⟨n, hfin.mem_toFinset.mpr hn⟩
  let m : ℕ := F.min' hneF
  let u : ℕ := F.max' hneF
  have hmF : m ∈ F := by
    dsimp [m]
    exact Finset.min'_mem F hneF
  have huF : u ∈ F := by
    dsimp [u]
    exact Finset.max'_mem F hneF
  have hm : m ∈ I := hfin.mem_toFinset.mp hmF
  have hu : u ∈ I := hfin.mem_toFinset.mp huF
  have hmu : m ≤ u := by
    dsimp [m, u]
    exact Finset.min'_le F (F.max' hneF) (Finset.max'_mem F hneF)
  have hEq : I = Set.Icc m u := by
    ext n
    constructor
    · intro hn
      have hnF : n ∈ F := hfin.mem_toFinset.mpr hn
      constructor
      · exact (Finset.min'_le F n hnF)
      · exact (Finset.le_max' F n hnF)
    · intro hn
      have hn' : m ≤ n ∧ n ≤ u := hn
      exact hI hm hu (by simpa [min_eq_left hmu] using hn'.1)
        (by simpa [max_eq_right hmu] using hn'.2)
  refine ⟨m, u, hm, hu, hEq, (hbound hm).1, (hbound hu).2⟩

private theorem ppPrimeIntegral_tsum_exchange
    {F : ℕ → ℝ → ℂ} {G : ℝ → ℂ}
    (hF : ∀ n, Integrable (F n))
    (hFs : Summable (fun n => ∫ v : ℝ, ‖F n v‖))
    (hHasSum : ∀ v : ℝ, HasSum (fun n => F n v) (G v)) :
    ∫ v : ℝ, G v = ∑' n, ∫ v : ℝ, F n v := by
  have hpoint : (fun v : ℝ => G v) = fun v => ∑' n, F n v := by
    funext v
    exact (hHasSum v).tsum_eq.symm
  rw [hpoint]
  exact (integral_tsum_of_summable_integral_norm hF hFs).symm

private theorem ppPrimeTwistedMangoldt_lseries_eq
    {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ (n : ZMod q) *
      (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv (dirichletLValue q hq χ) s / dirichletLValue q hq χ s := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have htw := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  rw [← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    ← DirichletCharacter.LFunction_eq_LSeries χ hs] at htw
  change LSeries ((fun n : ℕ => χ (n : ZMod q)) *
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s = _ at htw
  change LSeries ((fun n : ℕ => χ (n : ZMod q)) *
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s =
      -deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s
  exact htw

private theorem ppPrimeSmoothed_mellin_identity
    {N : ℝ} (hN : 0 < N) (q : ℕ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (t c : ℝ) (hc : 0 < c)
    (g : ℝ → ℝ)
    (hgsupport : Function.support g ⊆ Set.Icc (1 / 2 : ℝ) 3)
    (hginv : ∀ w : ℝ, 0 < w →
      (g w : ℂ) = (1 / (2 * Real.pi) : ℂ) *
        ∫ v : ℝ, mellinKernel g (⟨c, v⟩ : ℂ) *
          Complex.exp (-((⟨c, v⟩ : ℂ) * Real.log w)))
    (hKernel : Integrable (fun v : ℝ => mellinKernel g (⟨c, v⟩ : ℂ))) :
    smoothedMangoldtPolynomial N q χ t g =
      (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ,
        mellinKernel g (⟨c, v⟩ : ℂ) *
          Complex.exp ((⟨c, v⟩ : ℂ) * Real.log N) *
            (-deriv (dirichletLValue q hq χ)
                (1 - Complex.I * t + (⟨c, v⟩ : ℂ)) /
              dirichletLValue q hq χ
                (1 - Complex.I * t + (⟨c, v⟩ : ℂ))) := by
  classical
  let f : ℕ → ℂ := fun n => χ (n : ZMod q) *
    (ArithmeticFunction.vonMangoldt n : ℂ)
  let z : ℝ → ℂ := fun v => (c : ℂ) + Complex.I * (v : ℂ)
  let s : ℝ → ℂ := fun v => 1 - Complex.I * t + z v
  let D : ℂ → ℂ := dirichletLValue q hq χ
  let a : ℂ := (1 / (2 * Real.pi) : ℂ)
  let E : ℝ → ℂ := fun v => Complex.exp (z v * (Real.log N : ℂ))
  let Cₙ : ℕ → ℝ → ℂ := fun n v => a * E v * LSeries.term f (s v) n
  let F : ℕ → ℝ → ℂ := fun n v => mellinKernel g (z v) * Cₙ n v
  let G : ℝ → ℂ := fun v => mellinKernel g (z v) *
    (a * E v * (-deriv D (s v) / D (s v)))
  let Q : ℕ → ℂ := fun n =>
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) *
      Complex.exp ((-1 + Complex.I * t) * Real.log (n : ℝ))
  let W : ℕ → ℂ := fun n => Q n * (g ((n : ℝ) / N) : ℂ)
  let σ : ℂ := (1 + c : ℝ)
  let K : ℝ := ‖a‖ * Real.rpow N c
  have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
    simp [ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
  have hf0 : f 0 = 0 := by simp [f, hΛ0]
  have hz (v : ℝ) : z v = (⟨c, v⟩ : ℂ) := by
    apply Complex.ext <;> simp [z]
  have hKernelZ : Integrable (fun v : ℝ => mellinKernel g (z v)) := by
    convert hKernel using 1
    funext v
    rw [hz]
  have hσ : 1 < σ.re := by
    dsimp [σ]
    simp
    linarith
  have hLσ : LSeriesSummable f σ := by
    change LSeriesSummable ((fun n : ℕ => χ (n : ZMod q)) *
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) σ
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hσ
  have hSeriesσ : Summable (fun n => LSeries.term f σ n) := hLσ
  have hbn : Summable (fun n => ‖LSeries.term f σ n‖) := hSeriesσ.norm
  have hsRe (v : ℝ) : (s v).re = 1 + c := by
    simp [s, z]
  have htermNorm (n : ℕ) (v : ℝ) :
      ‖LSeries.term f (s v) n‖ = ‖LSeries.term f σ n‖ := by
    simp [LSeries.norm_term_eq, hsRe v, σ]
  have hE_norm (v : ℝ) : ‖E v‖ = Real.rpow N c := by
    calc
      ‖E v‖ = Real.exp (c * Real.log N) := by
        rw [Complex.norm_exp]
        simp [E, z]
      _ = Real.rpow N c := by
        rw [mul_comm c (Real.log N)]
        exact (Real.rpow_def_of_pos hN c).symm
  have ha_ne : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (one_div_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0))
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (norm_pos_iff.mpr ha_ne) (Real.rpow_pos_of_pos hN c)
  have hC_norm (n : ℕ) (v : ℝ) : ‖Cₙ n v‖ = K * ‖LSeries.term f σ n‖ := by
    simp [Cₙ, K, norm_mul, hE_norm v, htermNorm n v, mul_assoc]
  have hC_cont (n : ℕ) : Continuous (Cₙ n) := by
    by_cases hn : n = 0
    · have hzero : Cₙ n = fun _ => 0 := by
        funext v
        simp [Cₙ, hn, LSeries.term]
      rw [hzero]
      exact continuous_const
    · have hterm : (fun v : ℝ => LSeries.term f (s v) n) =
          fun v : ℝ => f n / (n : ℂ) ^ (s v) := by
        funext v
        rw [LSeries.term_of_ne_zero hn]
      have hterm_cont : Continuous (fun v : ℝ => LSeries.term f (s v) n) := by
        rw [hterm]
        have hs_cont : Continuous s := by
          dsimp [s, z]
          fun_prop
        have hpow_cont : Continuous (fun v : ℝ => (n : ℂ) ^ s v) :=
          hs_cont.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))
        have hpow_ne : ∀ v : ℝ, (n : ℂ) ^ s v ≠ 0 := by
          intro v
          exact (Complex.cpow_ne_zero_iff).2 (Or.inl (Nat.cast_ne_zero.mpr hn))
        exact continuous_const.div hpow_cont hpow_ne
      have hE_cont : Continuous E := by
        dsimp [E, z]
        fun_prop
      have hC_eq : Cₙ n = fun v => a * (E v * LSeries.term f (s v) n) := by
        funext v
        simp [Cₙ, mul_assoc]
      rw [hC_eq]
      exact continuous_const.mul (hE_cont.mul hterm_cont)
  have hF_int : ∀ n : ℕ, Integrable (F n) := by
    intro n
    change Integrable (fun v => mellinKernel g (z v) * Cₙ n v)
    exact hKernelZ.mul_bdd (hC_cont n).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun v => (hC_norm n v).le))
  have hFnorm (n : ℕ) (v : ℝ) :
      ‖F n v‖ = ‖mellinKernel g (z v)‖ * (K * ‖LSeries.term f σ n‖) := by
    simp [F, norm_mul, hC_norm n v]
  let k : ℝ := ∫ v : ℝ, ‖mellinKernel g (z v)‖
  have hFsum : Summable (fun n : ℕ => ∫ v : ℝ, ‖F n v‖) := by
    have hintEq (n : ℕ) :
        ∫ v : ℝ, ‖F n v‖ = (K * ‖LSeries.term f σ n‖) * k := by
      calc
        ∫ v : ℝ, ‖F n v‖ = ∫ v : ℝ,
            (K * ‖LSeries.term f σ n‖) * ‖mellinKernel g (z v)‖ := by
          apply integral_congr_ae
          filter_upwards [] with v
          rw [hFnorm]
          ring
        _ = (K * ‖LSeries.term f σ n‖) * k := by
          dsimp [k]
          rw [integral_const_mul]
    have hmajor : Summable (fun n : ℕ =>
        (K * ‖LSeries.term f σ n‖) * k) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbn.mul_left (K * k)
    exact hmajor.of_nonneg_of_le
      (fun n => integral_nonneg (fun _ => norm_nonneg _))
      (fun n => hintEq n ▸ le_rfl)
  have hHasSum : ∀ v : ℝ, HasSum (fun n : ℕ => F n v) (G v) := by
    intro v
    have hsv : 1 < (s v).re := by rw [hsRe v]; linarith
    have hLsv : LSeriesSummable f (s v) := by
      change LSeriesSummable ((fun n : ℕ => χ (n : ZMod q)) *
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (s v)
      exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hsv
    have hsum := hLsv.LSeriesHasSum
    have hlog := ppPrimeTwistedMangoldt_lseries_eq hq χ hsv
    have hsumScaled : HasSum (fun n : ℕ => F n v)
        (mellinKernel g (z v) * (a * E v * LSeries f (s v))) := by
      simpa [F, Cₙ, mul_assoc] using
        (hsum.mul_left (mellinKernel g (z v) * (a * E v)))
    rw [hlog] at hsumScaled
    simpa [G, mul_assoc] using hsumScaled
  have hexchange := ppPrimeIntegral_tsum_exchange hF_int hFsum hHasSum
  have hIntegral (n : ℕ) : (∫ v : ℝ, F n v) = W n := by
    by_cases hn : n = 0
    · subst n
      have hzero : (fun v : ℝ => F 0 v) = 0 := by
        funext v
        simp [F, Cₙ, LSeries.term]
      rw [hzero]
      simp [W, Q, hΛ0]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let w : ℝ := (n : ℝ) / N
      have hw : 0 < w := by dsimp [w]; positivity
      have hlogdiv : Real.log w = Real.log (n : ℝ) - Real.log N := by
        dsimp [w]
        exact Real.log_div (by positivity) hN.ne'
      have hlogdivC : (Real.log w : ℂ) =
          (Real.log (n : ℝ) : ℂ) - (Real.log N : ℂ) := by
        exact_mod_cast hlogdiv
      have hpow (v : ℝ) : (n : ℂ) ^ (-s v) =
          Complex.exp (-(s v) * (Real.log (n : ℝ) : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
        rw [← Complex.natCast_log]
        congr 1
        ring
      have hExp (v : ℝ) :
          Complex.exp (z v * (Real.log N : ℂ)) *
              Complex.exp (-(s v) * (Real.log (n : ℝ) : ℂ)) =
            Complex.exp ((-1 + Complex.I * t) * (Real.log (n : ℝ) : ℂ)) *
              Complex.exp (-z v * (Real.log w : ℂ)) := by
        rw [← Complex.exp_add, ← Complex.exp_add, hlogdivC]
        simp only [s]
        congr 1
        ring
      have hpoint (v : ℝ) : F n v =
          (mellinKernel g (z v) * a * f n) *
            (Complex.exp (z v * (Real.log N : ℂ)) *
              Complex.exp (-(s v) * (Real.log (n : ℝ) : ℂ))) := by
        simp only [F, Cₙ, E]
        rw [LSeries.term_def₀ hf0, hpow v]
        ring
      have hpoint' (v : ℝ) : F n v =
          Q n * (a * (mellinKernel g (z v) *
            Complex.exp (-z v * (Real.log w : ℂ)))) := by
        rw [hpoint v, hExp v]
        dsimp [Q]
        ring
      have hInvZ : (g w : ℂ) = a * ∫ v : ℝ,
          mellinKernel g (z v) * Complex.exp (-z v * (Real.log w : ℂ)) := by
        have hInv := hginv w hw
        have hIntegralEq :
            (∫ v : ℝ, mellinKernel g (z v) *
              Complex.exp (-z v * (Real.log w : ℂ))) =
            ∫ v : ℝ, mellinKernel g (⟨c, v⟩ : ℂ) *
              Complex.exp (-((⟨c, v⟩ : ℂ) * Real.log w)) := by
          apply integral_congr_ae
          filter_upwards [] with v
          rw [hz v]
          ring_nf
        rw [← hIntegralEq] at hInv
        exact hInv
      have hIntegralEq : (∫ v : ℝ, F n v) =
          (Q n * a) * ∫ v : ℝ, mellinKernel g (z v) *
            Complex.exp (-z v * (Real.log w : ℂ)) := by
        calc
          ∫ v : ℝ, F n v = ∫ v : ℝ, (Q n * a) *
              (mellinKernel g (z v) * Complex.exp (-z v * (Real.log w : ℂ))) := by
            apply integral_congr_ae
            filter_upwards [] with v
            rw [hpoint' v]
            ring
          _ = (Q n * a) * ∫ v : ℝ, mellinKernel g (z v) *
              Complex.exp (-z v * (Real.log w : ℂ)) := by
            rw [integral_const_mul]
      rw [hIntegralEq]
      calc
        _ = Q n * (a * ∫ v : ℝ, mellinKernel g (z v) *
              Complex.exp (-z v * (Real.log w : ℂ))) := by ring
        _ = Q n * (g w : ℂ) := by rw [← hInvZ]
        _ = W n := rfl
  have hW_support : ∀ n : ℕ, n ∉ Finset.range (⌊3 * N⌋₊ + 1) → W n = 0 := by
    intro n hn
    have hnlarge : ⌊3 * N⌋₊ + 1 ≤ n := by
      exact Nat.le_of_not_gt (by simpa using hn)
    have h3Nlt : 3 * N < (n : ℝ) := by
      have hfloorlt : 3 * N < ((⌊3 * N⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one (3 * N)
      exact hfloorlt.trans_le (by exact_mod_cast hnlarge)
    have hgzero : g ((n : ℝ) / N) = 0 := by
      by_contra hgn
      have hmem : (n : ℝ) / N ∈ Function.support g := by
        simpa only [Function.mem_support] using hgn
      have hupper := (hgsupport hmem).2
      have hnle : (n : ℝ) ≤ 3 * N := (div_le_iff₀ hN).mp hupper
      linarith
    simp [W, hgzero]
  have hWsum : smoothedMangoldtPolynomial N q χ t g = ∑' n : ℕ, W n := by
    rw [tsum_eq_sum (s := Finset.range (⌊3 * N⌋₊ + 1)) hW_support]
    unfold smoothedMangoldtPolynomial
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hnpos : 1 ≤ n
    · simp [W, Q, hnpos, mul_assoc]
    · have hnzero : n = 0 := by omega
      simp [W, Q, hnzero, hΛ0]
  calc
    smoothedMangoldtPolynomial N q χ t g = ∑' n : ℕ, W n := hWsum
    _ = ∑' n : ℕ, ∫ v : ℝ, F n v := by
      apply tsum_congr
      intro n
      exact (hIntegral n).symm
    _ = ∫ v : ℝ, G v := hexchange.symm
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ,
        mellinKernel g (⟨c, v⟩ : ℂ) *
          Complex.exp ((⟨c, v⟩ : ℂ) * (Real.log N : ℂ)) *
            (-deriv (dirichletLValue q hq χ)
                (1 - Complex.I * t + (⟨c, v⟩ : ℂ)) /
              dirichletLValue q hq χ
                (1 - Complex.I * t + (⟨c, v⟩ : ℂ))) := by
      calc
        ∫ v : ℝ, G v = ∫ v : ℝ, a *
            (mellinKernel g (z v) * E v *
              (-deriv D (s v) / D (s v))) := by
          apply integral_congr_ae
          filter_upwards [] with v
          dsimp [G]
          ring
        _ = a * ∫ v : ℝ, mellinKernel g (z v) * E v *
              (-deriv D (s v) / D (s v)) := by
          rw [integral_const_mul]
        _ = (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ,
              mellinKernel g (⟨c, v⟩ : ℂ) *
                Complex.exp ((⟨c, v⟩ : ℂ) * (Real.log N : ℂ)) *
                  (-deriv (dirichletLValue q hq χ)
                      (1 - Complex.I * t + (⟨c, v⟩ : ℂ)) /
                    dirichletLValue q hq χ
                      (1 - Complex.I * t + (⟨c, v⟩ : ℂ))) := by
          dsimp [a, D, E, s]
          congr 1
          apply integral_congr_ae
          filter_upwards [] with v
          rw [hz v]

private theorem ppPrimeMellinKernel_differentiableAt
    {g : ℝ → ℝ}
    (hfc : LocallyIntegrableOn (fun w : ℝ => (g w : ℂ)) (Set.Ioi 0))
    (hgsupport : Function.support g ⊆ Set.Icc (1 / 2 : ℝ) 3)
    {z : ℂ} (hz : |z.re| < 1) :
    DifferentiableAt ℂ (mellinKernel g) z := by
  let f : ℝ → ℂ := fun w => (g w : ℂ)
  have hzeroTop : f =ᶠ[atTop] (fun _ : ℝ => 0) := by
    filter_upwards [eventually_gt_atTop (3 : ℝ)] with w hw
    have hgw : g w = 0 := by
      by_contra hgw
      have hmem : w ∈ Function.support g := by
        simpa only [Function.mem_support] using hgw
      linarith [(hgsupport hmem).2]
    simp [f, hgw]
  have hzeroBot : f =ᶠ[𝓝[>] (0 : ℝ)] (fun _ : ℝ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    have hgw : g w = 0 := by
      by_contra hgw
      have hmem : w ∈ Function.support g := by
        simpa only [Function.mem_support] using hgw
      linarith [(hgsupport hmem).1, hw.2]
    simp [f, hgw]
  have hf_top : f =O[atTop] (fun w : ℝ => Real.rpow w (-1)) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [hzeroTop, eventually_gt_atTop (3 : ℝ)] with w hwzero hwpos
    rw [hwzero]
    simpa using Real.rpow_nonneg (show 0 ≤ w by linarith) (-1)
  have hf_bot : f =O[𝓝[>] (0 : ℝ)]
      (fun w : ℝ => Real.rpow w (-(-1 : ℝ))) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [hzeroBot,
      Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with w hwzero hwpos
    rw [hwzero]
    simpa using Real.rpow_nonneg hwpos.1.le (-(-1 : ℝ))
  have hf_top' : (fun w : ℝ => (g w : ℂ)) =O[atTop]
      (fun w : ℝ => Real.rpow w (-1)) := by simpa [f] using hf_top
  have hf_bot' : (fun w : ℝ => (g w : ℂ)) =O[𝓝[>] (0 : ℝ)]
      (fun w : ℝ => Real.rpow w (-(-1 : ℝ))) := by simpa [f] using hf_bot
  have hz' := abs_lt.mp hz
  have hEq : mellinKernel g = mellin (fun w : ℝ => (g w : ℂ)) := by
    funext s
    exact mellinKernel_eq_mellin g s
  rw [hEq]
  exact mellin_differentiableAt_of_isBigO_rpow (a := 1) (b := -1)
    hfc hf_top' hz'.2 hf_bot' hz'.1

private theorem ppPrimeMellinKernel_analyticOnNhd
    {g : ℝ → ℝ}
    (hfc : LocallyIntegrableOn (fun w : ℝ => (g w : ℂ)) (Set.Ioi 0))
    (hgsupport : Function.support g ⊆ Set.Icc (1 / 2 : ℝ) 3) :
    AnalyticOnNhd ℂ (mellinKernel g) Set.univ := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
  intro z hz
  let f : ℝ → ℂ := fun w => (g w : ℂ)
  have hzeroTop : f =ᶠ[atTop] (fun _ : ℝ => 0) := by
    filter_upwards [eventually_gt_atTop (3 : ℝ)] with w hw
    have hgw : g w = 0 := by
      by_contra hgw
      have hmem : w ∈ Function.support g := by
        simpa only [Function.mem_support] using hgw
      linarith [(hgsupport hmem).2]
    simp [f, hgw]
  have hzeroBot : f =ᶠ[𝓝[>] (0 : ℝ)] (fun _ : ℝ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    have hgw : g w = 0 := by
      by_contra hgw
      have hmem : w ∈ Function.support g := by
        simpa only [Function.mem_support] using hgw
      linarith [(hgsupport hmem).1, hw.2]
    simp [f, hgw]
  have hf_top : f =O[atTop]
      (fun w : ℝ => Real.rpow w (-(z.re + 1))) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [hzeroTop, eventually_gt_atTop (3 : ℝ)] with w hwzero hwpos
    rw [hwzero]
    simpa using Real.rpow_nonneg (show 0 ≤ w by linarith) (-(z.re + 1))
  have hf_bot : f =O[𝓝[>] (0 : ℝ)]
      (fun w : ℝ => Real.rpow w (-(z.re - 1))) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [hzeroBot,
      Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with w hwzero hwpos
    rw [hwzero]
    simpa using Real.rpow_nonneg hwpos.1.le (-(z.re - 1))
  have hf_top' : (fun w : ℝ => (g w : ℂ)) =O[atTop]
      (fun w : ℝ => Real.rpow w (-(z.re + 1))) := by simpa [f] using hf_top
  have hf_bot' : (fun w : ℝ => (g w : ℂ)) =O[𝓝[>] (0 : ℝ)]
      (fun w : ℝ => Real.rpow w (-(z.re - 1))) := by simpa [f] using hf_bot
  have hEq : mellinKernel g = mellin (fun w : ℝ => (g w : ℂ)) := by
    funext s
    exact mellinKernel_eq_mellin g s
  rw [hEq]
  exact (mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := z.re - 1)
    hfc hf_top' (by linarith) hf_bot' (by linarith)).differentiableWithinAt

private theorem ppPrimeDirichletLogDeriv_analyticOnNhd
    {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    {S : Set ℂ} (hS : S ⊆ ({1} : Set ℂ)ᶜ)
    (hzero : ∀ s ∈ S, dirichletLValue q hq χ s ≠ 0) :
    AnalyticOnNhd ℂ
      (fun s : ℂ => deriv (dirichletLValue q hq χ) s /
        dirichletLValue q hq χ s) S := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hLanalytic : AnalyticOnNhd ℂ
      (fun s : ℂ => dirichletLValue q hq χ s) ({1} : Set ℂ)ᶜ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
    intro s hs
    change DifferentiableWithinAt ℂ (DirichletCharacter.LFunction χ) ({1} : Set ℂ)ᶜ s
    exact (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  have hLanalyticS : AnalyticOnNhd ℂ
      (fun s : ℂ => dirichletLValue q hq χ s) S := by
    intro s hs
    exact hLanalytic s (hS hs)
  exact hLanalyticS.deriv.div hLanalyticS hzero

private noncomputable def ppPrimeMellinContourIntegrand
    (N : ℝ) (q : ℕ) (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (t : ℝ) (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  -(mellinKernel g z * Complex.exp (z * (Real.log N : ℂ)) *
    (deriv (dirichletLValue q hq χ) (1 - Complex.I * (t : ℂ) + z) /
      dirichletLValue q hq χ (1 - Complex.I * (t : ℂ) + z)))

private theorem ppPrimeMellinContourIntegrand_norm_bound
    (N : ℝ) (q : ℕ) (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (t : ℝ) (g : ℝ → ℝ) (z : ℂ) (K E D : ℝ)
    (hK0 : 0 ≤ K) (hE0 : 0 ≤ E)
    (hKernel : ‖mellinKernel g z‖ ≤ K)
    (hExp : ‖Complex.exp (z * (Real.log N : ℂ))‖ ≤ E)
    (hLogDeriv : ‖deriv (dirichletLValue q hq χ)
      (1 - Complex.I * (t : ℂ) + z) /
      dirichletLValue q hq χ (1 - Complex.I * (t : ℂ) + z)‖ ≤ D) :
    ‖ppPrimeMellinContourIntegrand N q hq χ t g z‖ ≤ K * E * D := by
  calc
    ‖ppPrimeMellinContourIntegrand N q hq χ t g z‖ =
        ‖mellinKernel g z‖ * ‖Complex.exp (z * (Real.log N : ℂ))‖ *
          ‖deriv (dirichletLValue q hq χ)
            (1 - Complex.I * (t : ℂ) + z) /
            dirichletLValue q hq χ (1 - Complex.I * (t : ℂ) + z)‖ := by
          simp [ppPrimeMellinContourIntegrand, norm_mul, mul_assoc]
    _ ≤ K * ‖Complex.exp (z * (Real.log N : ℂ))‖ *
          ‖deriv (dirichletLValue q hq χ)
            (1 - Complex.I * (t : ℂ) + z) /
            dirichletLValue q hq χ (1 - Complex.I * (t : ℂ) + z)‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKernel (norm_nonneg _)) (norm_nonneg _)
    _ ≤ (K * E) *
          ‖deriv (dirichletLValue q hq χ)
            (1 - Complex.I * (t : ℂ) + z) /
            dirichletLValue q hq χ (1 - Complex.I * (t : ℂ) + z)‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hExp hK0) (norm_nonneg _)
    _ ≤ (K * E) * D := mul_le_mul_of_nonneg_left hLogDeriv (mul_nonneg hK0 hE0)
    _ = K * E * D := by ring

private theorem ppPrimeMellinContourIntegrand_analyticOnNhd
    (N : ℝ) (q : ℕ) (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (t : ℝ) (g : ℝ → ℝ)
    (hfc : LocallyIntegrableOn (fun w : ℝ => (g w : ℂ)) (Set.Ioi 0))
    (hgsupport : Function.support g ⊆ Set.Icc (1 / 2 : ℝ) 3)
    {S : Set ℂ}
    (hPole : ∀ z ∈ S, 1 - Complex.I * (t : ℂ) + z ≠ 1)
    (hzero : ∀ z ∈ S,
      dirichletLValue q hq χ (1 - Complex.I * (t : ℂ) + z) ≠ 0) :
    AnalyticOnNhd ℂ (ppPrimeMellinContourIntegrand N q hq χ t g) S := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  intro z hz
  let s : ℂ := 1 - Complex.I * (t : ℂ) + z
  have hsPole : s ≠ 1 := by simpa [s] using hPole z hz
  have hsZero : dirichletLValue q hq χ s ≠ 0 := by
    simpa [s] using hzero z hz
  have hLdAt : AnalyticAt ℂ
      (fun w : ℂ => deriv (dirichletLValue q hq χ) w /
        dirichletLValue q hq χ w) s := by
    have hLdRegion := ppPrimeDirichletLogDeriv_analyticOnNhd hq χ
      (S := {s})
      (by
        intro w hw
        have hw' : w = s := by simpa using hw
        rw [hw']
        simpa using hsPole)
      (by
        intro w hw
        have hw' : w = s := by simpa using hw
        rw [hw']
        exact hsZero)
    exact hLdRegion s (by simp)
  let φ : ℂ → ℂ := fun w => 1 - Complex.I * (t : ℂ) + w
  have hφ : AnalyticAt ℂ φ z := by fun_prop
  have hpoint : φ z = s := by simp [φ, s]
  have hLdComp : AnalyticAt ℂ
      (fun w : ℂ => deriv (dirichletLValue q hq χ)
          (1 - Complex.I * (t : ℂ) + w) /
        dirichletLValue q hq χ (1 - Complex.I * (t : ℂ) + w)) z := by
    simpa [φ, Function.comp_def] using hLdAt.comp_of_eq hφ hpoint
  have hKernel : AnalyticAt ℂ (mellinKernel g) z := by
    exact (ppPrimeMellinKernel_analyticOnNhd hfc hgsupport) z (Set.mem_univ z)
  have hExp : AnalyticAt ℂ
      (fun w : ℂ => Complex.exp (w * (Real.log N : ℂ))) z := by
    fun_prop
  have hProduct : AnalyticAt ℂ
      (fun w : ℂ => -(mellinKernel g w * Complex.exp (w * (Real.log N : ℂ)) *
        (deriv (dirichletLValue q hq χ) (1 - Complex.I * (t : ℂ) + w) /
          dirichletLValue q hq χ (1 - Complex.I * (t : ℂ) + w)))) z := by
    exact ((hKernel.mul hExp).mul hLdComp).neg
  change AnalyticAt ℂ
    (fun w : ℂ => -(mellinKernel g w * Complex.exp (w * (Real.log N : ℂ)) *
      (deriv (dirichletLValue q hq χ) (1 - Complex.I * (t : ℂ) + w) /
        dirichletLValue q hq χ (1 - Complex.I * (t : ℂ) + w)))) z
  exact hProduct

private theorem ppPrimeMellinContour_rightLine_integrable
    {N : ℝ} (hN : 0 < N) (q : ℕ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (t c : ℝ) (hc : 0 < c) (g : ℝ → ℝ)
    (hKernel : Integrable (fun v : ℝ => mellinKernel g (⟨c, v⟩ : ℂ)))
    (hfactorBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ v : ℝ,
      ‖Complex.exp ((⟨c, v⟩ : ℂ) * (Real.log N : ℂ)) *
        (deriv (dirichletLValue q hq χ)
            (1 - Complex.I * (t : ℂ) + (⟨c, v⟩ : ℂ)) /
          dirichletLValue q hq χ
            (1 - Complex.I * (t : ℂ) + (⟨c, v⟩ : ℂ)))‖ ≤ M) :
    Integrable (fun v : ℝ =>
      ppPrimeMellinContourIntegrand N q hq χ t g (⟨c, v⟩ : ℂ)) := by
  classical
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  obtain ⟨M, hM, hMbound⟩ := hfactorBound
  let S : Set ℂ := {s : ℂ | 1 < s.re}
  have hS : S ⊆ ({1} : Set ℂ)ᶜ := by
    intro s hs hsone
    have hsone' : s = 1 := by simpa using hsone
    subst s
    change 1 < (1 : ℂ).re at hs
    simp at hs
  have hzero : ∀ s ∈ S, dirichletLValue q hq χ s ≠ 0 := by
    intro s hs
    have hsne : s ≠ 1 := by
      intro heq
      subst s
      change 1 < (1 : ℂ).re at hs
      simp at hs
    have h := χ.LFunction_ne_zero_of_one_le_re (Or.inr hsne) hs.le
    simpa [dirichletLValue] using h
  have hlogAnalytic := ppPrimeDirichletLogDeriv_analyticOnNhd hq χ hS hzero
  let zline : ℝ → ℂ := fun v => (c : ℂ) + (v : ℂ) * Complex.I
  have hzpair (v : ℝ) : (⟨c, v⟩ : ℂ) = zline v := by
    apply Complex.ext <;> simp [zline]
  let line : ℝ → ℂ := fun v =>
    1 - Complex.I * (t : ℂ) + zline v
  have hlineRe (v : ℝ) : (line v).re = 1 + c := by
    simp [line, zline]
  have hlineS (v : ℝ) : line v ∈ S := by
    change 1 < (line v).re
    rw [hlineRe]
    linarith
  have hlineCont : Continuous line := by fun_prop
  let factor : ℝ → ℂ := fun v =>
    Complex.exp (zline v * (Real.log N : ℂ)) *
      (deriv (dirichletLValue q hq χ) (line v) /
        dirichletLValue q hq χ (line v))
  have hfactorBound' : ∀ v : ℝ, ‖factor v‖ ≤ M := by
    intro v
    simpa [factor, line, hzpair v] using hMbound v
  have hfactorContinuous : Continuous factor := by
    have hlogContinuous : Continuous
        (fun v : ℝ => deriv (dirichletLValue q hq χ) (line v) /
          dirichletLValue q hq χ (line v)) := by
      apply continuous_iff_continuousAt.mpr
      intro v
      exact (hlogAnalytic (line v) (hlineS v)).continuousAt.comp
        (hlineCont.continuousAt)
    have hexpContinuous : Continuous (fun v : ℝ =>
        Complex.exp (zline v * (Real.log N : ℂ))) := by fun_prop
    exact hexpContinuous.mul hlogContinuous
  have hmul : Integrable (fun v : ℝ =>
      mellinKernel g (⟨c, v⟩ : ℂ) * factor v) :=
    hKernel.mul_bdd hfactorContinuous.aestronglyMeasurable
      (ae_of_all _ hfactorBound')
  have hEq : (fun v : ℝ =>
      ppPrimeMellinContourIntegrand N q hq χ t g (⟨c, v⟩ : ℂ)) =
      (fun v : ℝ => -(mellinKernel g (⟨c, v⟩ : ℂ) * factor v)) := by
    funext v
    simp [ppPrimeMellinContourIntegrand, factor, line, hzpair v]
    ring
  rw [hEq]
  exact hmul.neg

private theorem ppPrimeMellinContourRectangle_shift
    {F : ℂ → ℂ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hF : AnalyticOnNhd ℂ F (Set.Icc a b ×ℂ Set.Icc c d)) :
    (∫ x : ℝ in a..b, F (x + c * Complex.I)) -
      (∫ x : ℝ in a..b, F (x + d * Complex.I)) +
      Complex.I • (∫ y : ℝ in c..d, F (b + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in c..d, F (a + y * Complex.I)) = 0 := by
  have hF' : AnalyticOnNhd ℂ F (Set.uIcc a b ×ℂ Set.uIcc c d) := by
    simpa [Set.uIcc_of_le hab, Set.uIcc_of_le hcd] using hF
  have hDiff : DifferentiableOn ℂ F (Set.uIcc a b ×ℂ Set.uIcc c d) := by
    intro z hz
    exact (hF' z hz).differentiableAt.differentiableWithinAt
  simpa using Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    F (⟨a, c⟩ : ℂ) (⟨b, d⟩ : ℂ) hDiff

/- Zero-free input passed from `PP.Results`, which imports this plan module. -/
def ppPrimeZeroFree (C : ℝ) : Prop :=
    0 < C →
      ∃ c C₀ x₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          let width := c * T ^ 2 / L
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ hq : 0 < q, ∀ χ : DirichletCharacter ℂ q,
              (∀ s : ℂ, 1 - width ≤ s.re →
                1 ≤ |s.im| → |s.im| ≤ Real.rpow x 3 →
                  dirichletLValue q hq χ s ≠ 0) ∧
              (∀ s : ℂ, 1 - width / 2 ≤ s.re → s.re ≤ 1 + 1 / L →
                2 ≤ |s.im| → |s.im| ≤ Real.rpow x 3 / 2 →
                  ‖deriv (dirichletLValue q hq χ) s /
                    dirichletLValue q hq χ s‖ ≤ C₀ * L)

def ppPrimeZetaLogDerivBound : Prop :=
  ∃ K ε : ℝ, 0 < K ∧ 0 < ε ∧
    ∀ δ : ℝ, 0 < δ → δ < ε →
      (-(deriv riemannZeta (1 + (δ : ℂ)) /
        riemannZeta (1 + (δ : ℂ)))).re ≤ 1 / δ + K

private theorem ppPrimeRightLineLogDeriv_bound
    (hzeta : ppPrimeZetaLogDerivBound) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧
      ∀ L : ℝ, L₀ ≤ L →
        ∀ q : ℕ, ∀ hq : 0 < q,
          ∀ χ : DirichletCharacter ℂ q, ∀ t v : ℝ,
            ‖deriv (dirichletLValue q hq χ)
                (1 - Complex.I * (t : ℂ) + (⟨1 / L, v⟩ : ℂ)) /
              dirichletLValue q hq χ
                (1 - Complex.I * (t : ℂ) + (⟨1 / L, v⟩ : ℂ))‖ ≤ 2 * L := by
  obtain ⟨K, ε, hK, hε, hζ⟩ := hzeta
  let L₀ : ℝ := max K ε⁻¹ + 2
  have hL₀ : 1 ≤ L₀ := by
    dsimp [L₀]
    have hmax : 0 ≤ max K ε⁻¹ := le_of_lt (lt_of_lt_of_le hK (le_max_left _ _))
    linarith
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL q hq χ t v
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) (le_trans hL₀ hL)
  have hKle : K ≤ L := by
    have hK₀ : K ≤ L₀ := by
      dsimp [L₀]
      have hmax : K ≤ max K ε⁻¹ := le_max_left _ _
      linarith
    exact hK₀.trans hL
  have hεinvLt : ε⁻¹ < L := by
    have hεinv₀ : ε⁻¹ + 1 ≤ L₀ := by
      dsimp [L₀]
      have hmax : ε⁻¹ ≤ max K ε⁻¹ := le_max_right _ _
      linarith
    have hεinv : ε⁻¹ + 1 ≤ L := hεinv₀.trans hL
    linarith
  have hδε : 1 / L < ε := by
    apply (div_lt_iff₀ hLpos).2
    calc
      1 = ε * ε⁻¹ := by field_simp
      _ < ε * L := mul_lt_mul_of_pos_left hεinvLt hε
  let δ : ℝ := 1 / L
  let σ : ℂ := Complex.ofReal (1 + δ)
  let s : ℂ := 1 - Complex.I * (t : ℂ) + (⟨δ, v⟩ : ℂ)
  let f : ℕ → ℂ := fun n => χ (n : ZMod q) *
    (ArithmeticFunction.vonMangoldt n : ℂ)
  let g : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδε' : δ < ε := by simpa [δ] using hδε
  have hσ : 1 < σ.re := by
    dsimp [σ]
    simp
    linarith [hδpos]
  have hs : 1 < s.re := by
    dsimp [s]
    simp
    linarith [hδpos]
  have hsRe : s.re = σ.re := by simp [s, σ]
  have htwist : LSeriesSummable f s := by
    change LSeriesSummable
      ((fun n : ℕ => χ (n : ZMod q)) *
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hbase : LSeriesSummable g σ := by
    change LSeriesSummable
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) σ
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt hσ
  have hcoef (n : ℕ) : ‖f n‖ ≤ ‖g n‖ := by
    dsimp [f, g]
    calc
      ‖χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)‖ =
          ‖χ (n : ZMod q)‖ * ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ := norm_mul _ _
      _ ≤ 1 * ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ :=
        mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
      _ = _ := by ring
  have htermBound (n : ℕ) :
      ‖LSeries.term f s n‖ ≤ ‖LSeries.term g σ n‖ := by
    calc
      ‖LSeries.term f s n‖ ≤ ‖LSeries.term g s n‖ :=
        LSeries.norm_term_le s (hcoef n)
      _ = ‖LSeries.term g σ n‖ := by
        rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsRe]
  have hnormSum :
      (∑' n : ℕ, ‖LSeries.term f s n‖) ≤
        ∑' n : ℕ, ‖LSeries.term g σ n‖ :=
    htwist.norm.tsum_le_tsum htermBound hbase.norm
  have htermReal (n : ℕ) :
      ‖LSeries.term g σ n‖ = (LSeries.term g σ n).re := by
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hden : 0 < (n : ℝ) ^ (1 + δ) := by
        apply Real.rpow_pos_of_pos
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hcoefNonneg :
          0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + δ) :=
        div_nonneg hΛ hden.le
      have hpow : (n : ℂ) ^ σ = Complex.ofReal ((n : ℝ) ^ (1 + δ)) := by
        dsimp [σ]
        rw [← Complex.ofReal_natCast,
          Complex.ofReal_cpow (Nat.cast_nonneg n) (1 + δ)]
      have hterm : LSeries.term g σ n =
          ((ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + δ) : ℝ) : ℂ) := by
        rw [LSeries.term_of_ne_zero hn]
        dsimp [g]
        rw [hpow, ← Complex.ofReal_div]
      rw [hterm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoefNonneg]
      simp
  have hsumReal :
      (∑' n : ℕ, ‖LSeries.term g σ n‖) = (LSeries g σ).re := by
    calc
      (∑' n : ℕ, ‖LSeries.term g σ n‖) =
          ∑' n : ℕ, (LSeries.term g σ n).re := by
            apply tsum_congr
            intro n
            exact htermReal n
      _ = (LSeries g σ).re := by
        simpa only [LSeries] using (Complex.re_tsum hbase).symm
  have hbaseZeta : LSeries g σ =
      -(deriv riemannZeta σ / riemannZeta σ) := by
    have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσ
    simpa [g, neg_div] using h
  have hsumZeta : (LSeries g σ).re ≤ 1 / δ + K := by
    rw [hbaseZeta]
    simpa [σ] using hζ δ hδpos hδε'
  have hnormL : ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := by
    simpa only [LSeries] using norm_tsum_le_tsum_norm htwist.norm
  have hlog : LSeries f s =
      -deriv (dirichletLValue q hq χ) s / dirichletLValue q hq χ s := by
    simpa [f] using ppPrimeTwistedMangoldt_lseries_eq hq χ hs
  have hratio :
      ‖deriv (dirichletLValue q hq χ) s / dirichletLValue q hq χ s‖ ≤ 1 / δ + K := by
    calc
      _ = ‖LSeries f s‖ := by rw [hlog]; simp
      _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := hnormL
      _ ≤ ∑' n : ℕ, ‖LSeries.term g σ n‖ := hnormSum
      _ = (LSeries g σ).re := hsumReal
      _ ≤ 1 / δ + K := hsumZeta
  have hδinv : 1 / δ = L := by
    dsimp [δ]
    field_simp
  have hratio' :
      ‖deriv (dirichletLValue q hq χ) s / dirichletLValue q hq χ s‖ ≤ 2 * L := by
    rw [hδinv] at hratio
    nlinarith [hratio, hKle]
  simpa [s, δ] using hratio'

private theorem ppPrime_log_rpow_le_rpow_eventually {r s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ r ≤ Real.rpow x s := by
  have hlim :
      Tendsto (fun x : ℝ => (Real.log x) ^ r / Real.rpow x s) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero
  filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with x hratio hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hden : 0 < Real.rpow x s := Real.rpow_pos_of_pos hxpos s
  have hratio' : (Real.log x) ^ r / Real.rpow x s < 1 := hratio
  have hlt : (Real.log x) ^ r < Real.rpow x s := by
    simpa using (div_lt_iff₀ hden).mp hratio'
  exact hlt.le

private theorem ppPrime_gaussian_exp_le_exp_neg_linear_eventually
    {a b c : ℝ} (ha : 0 < a) :
    ∀ᶠ T : ℝ in atTop,
      Real.exp (-a * T ^ 2 + b * T) ≤ Real.exp (-c * T) := by
  have hLittle :
      (fun T : ℝ => Real.exp (-a * T ^ 2 + (b + c) * T)) =o[atTop]
        (fun _ : ℝ => (1 : ℝ)) := by
    simpa using
      (rexp_neg_quadratic_isLittleO_rpow_atTop
        (neg_lt_zero.mpr ha) (b + c) 0)
  have hlim :
      Tendsto (fun T : ℝ => Real.exp (-a * T ^ 2 + (b + c) * T))
        atTop (𝓝 0) := by
    simpa using hLittle.tendsto_div_nhds_zero
  filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with T hT
  have hratio :
      Real.exp (-a * T ^ 2 + b * T) / Real.exp (-c * T) =
        Real.exp (-a * T ^ 2 + (b + c) * T) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hratio' :
      Real.exp (-a * T ^ 2 + b * T) / Real.exp (-c * T) < 1 := by
    rw [hratio]
    exact hT
  have hlt := (div_lt_iff₀ (Real.exp_pos _)).mp hratio'
  simpa using hlt.le

private theorem ppPrime_mellinKernel_integrable_of_rpow_two
    {g : ℝ → ℝ} {c M : ℝ}
    (hanalytic : AnalyticOnNhd ℂ (mellinKernel g) Set.univ)
    (hbound : ∀ v : ℝ,
      ‖mellinKernel g (⟨c, v⟩ : ℂ)‖ ≤ M * Real.rpow (1 + |v|) (-2)) :
    Integrable (fun v : ℝ => mellinKernel g (⟨c, v⟩ : ℂ)) := by
  have hbase : Integrable (fun v : ℝ => Real.rpow (1 + ‖v‖) (-2)) := by
    exact integrable_one_add_norm (E := ℝ) (by norm_num)
  have hmajor : Integrable (fun v : ℝ => M * Real.rpow (1 + ‖v‖) (-2)) :=
    hbase.const_mul M
  have hcont : Continuous (fun v : ℝ => mellinKernel g (⟨c, v⟩ : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hline : ContinuousAt (fun u : ℝ => (⟨c, u⟩ : ℂ)) v := by
      have hline' : ContinuousAt
          (fun u : ℝ => (c : ℂ) + (u : ℂ) * Complex.I) v := by fun_prop
      have heq : (fun u : ℝ => (⟨c, u⟩ : ℂ)) =
          (fun u : ℝ => (c : ℂ) + (u : ℂ) * Complex.I) := by
        funext u
        apply Complex.ext
        · simp
        · simp
      rw [heq]
      exact hline'
    exact (hanalytic (⟨c, v⟩ : ℂ) (Set.mem_univ _)).continuousAt.comp hline
  refine hmajor.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with v
  simpa [Real.norm_eq_abs] using hbound v

private theorem ppPrimePositiveCutoff_mellinKernel_analyticOnNhd
    (a b δ : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 4) :
    AnalyticOnNhd ℂ (mellinKernel (ppPrimePositiveCutoff a b δ)) Set.univ := by
  have haPos : 0 < a := by linarith
  have hbPos : 0 < b := lt_of_lt_of_le haPos hab
  have hexpLower : (3 / 4 : ℝ) ≤ Real.exp (-δ) := by
    have h := Real.add_one_le_exp (-δ)
    linarith
  have hexpUpper : Real.exp δ ≤ 9 / 7 := by
    have h := Real.exp_le_two_add_div_two_sub hδ.le (by linarith : δ < 2)
    have hden : 0 < 2 - δ := by linarith
    have hfrac : (2 + δ) / (2 - δ) ≤ 9 / 7 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    exact h.trans hfrac
  have hlow : (1 / 2 : ℝ) ≤ a * Real.exp (-δ) := by
    calc
      1 / 2 ≤ 3 / 4 := by norm_num
      _ ≤ Real.exp (-δ) := hexpLower
      _ = 1 * Real.exp (-δ) := by ring
      _ ≤ a * Real.exp (-δ) :=
        mul_le_mul_of_nonneg_right ha (Real.exp_nonneg _)
  have hhigh : b * Real.exp δ ≤ 3 := by
    calc
      b * Real.exp δ ≤ 2 * (9 / 7) :=
        mul_le_mul hb hexpUpper (Real.exp_nonneg _) (by norm_num)
      _ ≤ 3 := by norm_num
  have hsupport : Function.support (ppPrimePositiveCutoff a b δ) ⊆
      Set.Icc (1 / 2 : ℝ) 3 := by
    intro w hw
    have h := ppPrimePositiveCutoff_support a b δ haPos hbPos hδ hw
    exact ⟨hlow.trans h.1, h.2.trans hhigh⟩
  have hlog : ContinuousOn Real.log (Set.Ioi (0 : ℝ)) :=
    Real.continuousOn_log.mono (by intro w hw; exact ne_of_gt hw)
  have hcut : Continuous (ppPrimeLogCutoff (Real.log a) (Real.log b) δ) :=
    (ppPrimeLogCutoff_contDiff _ _ _).continuous
  have hcutU : ContinuousOn
      (ppPrimeLogCutoff (Real.log a) (Real.log b) δ) Set.univ := hcut.continuousOn
  have hcomp : ContinuousOn
      (fun w : ℝ => ppPrimeLogCutoff (Real.log a) (Real.log b) δ (Real.log w))
      (Set.Ioi 0) := by
    exact hcutU.comp hlog (by intro w hw; simp)
  have hrealCLM : Continuous (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.continuous
  have hrealU : ContinuousOn (fun r : ℝ => (r : ℂ)) Set.univ := by
    exact continuousOn_univ.mpr hrealCLM
  have hcompC : ContinuousOn
      (fun w : ℝ => (ppPrimeLogCutoff (Real.log a) (Real.log b) δ
        (Real.log w) : ℂ)) (Set.Ioi 0) := by
    exact hrealU.comp hcomp (by intro w hw; exact Set.mem_univ _)
  have hcutC : ContinuousOn
      (fun w : ℝ => (ppPrimePositiveCutoff a b δ w : ℂ)) (Set.Ioi 0) := by
    apply hcompC.congr
    intro w hw
    have hwpos : 0 < w := hw
    simp [ppPrimePositiveCutoff, hwpos]
  have hfc : LocallyIntegrableOn
      (fun w : ℝ => (ppPrimePositiveCutoff a b δ w : ℂ)) (Set.Ioi 0) :=
    hcutC.locallyIntegrableOn measurableSet_Ioi
  exact ppPrimeMellinKernel_analyticOnNhd hfc hsupport

private theorem ppPrimeSmoothing_error_log_bound
    {x N τ A : ℝ} (hx : 2 < x)
    (hNlo : Real.rpow x τ / 2 ≤ N) (hN4 : 4 ≤ N)
    (hL : 1 ≤ Real.log x)
    (hLpow : Real.rpow (Real.log x) (A + 3) ≤ Real.rpow x τ)
    (hlog : Real.log (3 * N) ≤ 2 * Real.log x)
    (hδsmall : Real.rpow (Real.log x) (-A - 4) ≤ 1 / 4)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (m u : ℕ)
    (hm : N ≤ (m : ℝ)) (hmu : (m : ℝ) ≤ (u : ℝ))
    (hu : (u : ℝ) ≤ 2 * N) :
    ‖mangoldtIntervalPolynomial N q χ t (Set.Icc m u) -
      smoothedMangoldtPolynomial N q χ t
        (ppPrimePositiveCutoff ((m : ℝ) / N) ((u : ℝ) / N)
          (Real.rpow (Real.log x) (-A - 4)))‖ ≤
      120 * Real.rpow (Real.log x) (-A - 2) := by
  let L : ℝ := Real.log x
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hxpos : 0 < x := by linarith
  have hNpos : 0 < N := by linarith
  have hδpos : 0 < Real.rpow L (-A - 4) := Real.rpow_pos_of_pos hLpos _
  have hxp : 0 < Real.rpow x τ := Real.rpow_pos_of_pos hxpos _
  have hLp : 0 < Real.rpow L (A + 3) := Real.rpow_pos_of_pos hLpos _
  have hNinv : 1 / N ≤ 2 * Real.rpow L (-A - 3) := by
    calc
      1 / N ≤ 1 / (Real.rpow x τ / 2) :=
        one_div_le_one_div_of_le (by positivity) hNlo
      _ = 2 * (Real.rpow x τ)⁻¹ := by field_simp
      _ ≤ 2 * (Real.rpow L (A + 3))⁻¹ := by
        simpa only [one_div] using mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le hLp hLpow) (by norm_num)
      _ = 2 * Real.rpow L (-A - 3) := by
        calc
          _ = 2 * Real.rpow L (-(A + 3)) :=
            congrArg (fun y : ℝ => 2 * y) (Real.rpow_neg hLpos.le (A + 3)).symm
          _ = _ := congrArg (fun e : ℝ => 2 * Real.rpow L e) (by ring)
  have hErr := ppPrimePositiveCutoff_mangoldt_smoothing_error
    hN4 q χ t m u hm hmu hu (Real.rpow L (-A - 4)) hδpos hδsmall
  have hδmul : Real.rpow L (-A - 4) * L = Real.rpow L (-A - 3) := by
    calc
      _ = Real.rpow L (-A - 4) * Real.rpow L 1 := by simp
      _ = Real.rpow L ((-A - 4) + 1) :=
        (Real.rpow_add hLpos (-A - 4) 1).symm
      _ = _ := by congr 1 <;> ring
  have hLmul : Real.rpow L (-A - 3) * L = Real.rpow L (-A - 2) := by
    calc
      _ = Real.rpow L (-A - 3) * Real.rpow L 1 := by simp
      _ = Real.rpow L ((-A - 3) + 1) :=
        (Real.rpow_add hLpos (-A - 3) 1).symm
      _ = _ := by congr 1 <;> ring
  have hpowmono : Real.rpow L (-A - 3) ≤ Real.rpow L (-A - 2) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  calc
    _ ≤ 20 * (Real.rpow L (-A - 4) + 1 / N) * Real.log (3 * N) := hErr
    _ ≤ 20 * (Real.rpow L (-A - 4) + 1 / N) * (2 * L) := by
      gcongr
    _ = 40 * (Real.rpow L (-A - 4) * L + (1 / N) * L) := by ring
    _ ≤ 40 * (Real.rpow L (-A - 4) * L +
        2 * Real.rpow L (-A - 3) * L) := by
      gcongr
    _ = 40 * Real.rpow L (-A - 3) + 80 * Real.rpow L (-A - 2) := by
      rw [hδmul]
      calc
        40 * (Real.rpow L (-A - 3) + 2 * Real.rpow L (-A - 3) * L) =
            40 * Real.rpow L (-A - 3) + 80 * (Real.rpow L (-A - 3) * L) := by ring
        _ = 40 * Real.rpow L (-A - 3) + 80 * Real.rpow L (-A - 2) := by rw [hLmul]
    _ ≤ 120 * Real.rpow L (-A - 2) := by nlinarith

private theorem ppPrimeIntegral_largeSet_rpow_bound
    {F : ℝ → ℂ} {S : Set ℝ} {M H j : ℝ}
    (hM : 0 ≤ M) (hH : 0 < H) (hj : 2 ≤ j)
    (hS : MeasurableSet S) (hFint : Integrable F)
    (hdecay : ∀ v : ℝ,
      ‖F v‖ ≤ M * Real.rpow (1 + |v|) (-j))
    (hlarge : ∀ v ∈ S, H ≤ |v|) :
    ‖∫ v in S, F v‖ ≤
      (M * Real.rpow H (2 - j)) *
        ∫ v : ℝ, Real.rpow (1 + ‖v‖) (-2 : ℝ) := by
  have hbase : Integrable (fun v : ℝ => Real.rpow (1 + ‖v‖) (-2 : ℝ)) := by
    exact integrable_one_add_norm (E := ℝ) (by norm_num)
  let K : ℝ := M * Real.rpow H (2 - j)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg hM (Real.rpow_nonneg hH.le _)
  have hmajor : Integrable (fun v : ℝ => K * Real.rpow (1 + ‖v‖) (-2 : ℝ)) :=
    hbase.const_mul K
  have hpoint : ∀ v ∈ S,
      ‖F v‖ ≤ K * Real.rpow (1 + ‖v‖) (-2 : ℝ) := by
    intro v hv
    have hvlarge := hlarge v hv
    have hvnorm : ‖v‖ = |v| := Real.norm_eq_abs v
    have hbaseV : 0 < 1 + |v| := by positivity
    have hHle : H ≤ 1 + |v| := by linarith [abs_nonneg v]
    have hpow : Real.rpow (1 + |v|) (2 - j) ≤ Real.rpow H (2 - j) :=
      Real.rpow_le_rpow_of_nonpos hH hHle (by linarith)
    have hsplit : Real.rpow (1 + |v|) (-j) =
        Real.rpow (1 + |v|) (-2) * Real.rpow (1 + |v|) (2 - j) := by
      calc
        _ = Real.rpow (1 + |v|) ((-2) + (2 - j)) := by congr 1 <;> ring
        _ = _ := Real.rpow_add hbaseV (-2) (2 - j)
    calc
      ‖F v‖ ≤ M * Real.rpow (1 + |v|) (-j) := hdecay v
      _ = M * (Real.rpow (1 + |v|) (-2) *
          Real.rpow (1 + |v|) (2 - j)) := by rw [hsplit]
      _ ≤ M * (Real.rpow (1 + |v|) (-2) * Real.rpow H (2 - j)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow
            (Real.rpow_nonneg hbaseV.le _)) hM
      _ = K * Real.rpow (1 + ‖v‖) (-2 : ℝ) := by
        dsimp [K]
        ring
  have hnorm : ‖∫ v in S, F v‖ ≤ ∫ v in S, ‖F v‖ := by
    simpa only [integral] using
      (norm_integral_le_integral_norm (μ := volume.restrict S) F)
  have hmono := setIntegral_mono_on hFint.norm.integrableOn hmajor.integrableOn hS hpoint
  have htotal :
      (∫ v in S, K * Real.rpow (1 + ‖v‖) (-2 : ℝ)) ≤
        ∫ v : ℝ, K * Real.rpow (1 + ‖v‖) (-2 : ℝ) := by
    exact setIntegral_le_integral hmajor (ae_of_all _ fun v =>
      mul_nonneg hK (Real.rpow_nonneg (by positivity) _))
  calc
    _ ≤ ∫ v in S, ‖F v‖ := hnorm
    _ ≤ ∫ v in S, K * Real.rpow (1 + ‖v‖) (-2 : ℝ) := hmono
    _ ≤ ∫ v : ℝ, K * Real.rpow (1 + ‖v‖) (-2 : ℝ) := htotal
    _ = K * ∫ v : ℝ, Real.rpow (1 + ‖v‖) (-2 : ℝ) := by rw [integral_const_mul]
    _ = _ := by dsimp [K]

private theorem ppPrimeIntegral_truncate_rpow_bound
    {F : ℝ → ℂ} {M H j : ℝ}
    (hM : 0 ≤ M) (hH : 1 ≤ H) (hj : 2 ≤ j) (hFint : Integrable F)
    (hdecay : ∀ v : ℝ,
      ‖F v‖ ≤ M * Real.rpow (1 + |v|) (-j)) :
    ‖(∫ v : ℝ, F v) - ∫ v : ℝ in (-H)..H, F v‖ ≤
      2 * (M * Real.rpow H (2 - j)) *
        ∫ v : ℝ, Real.rpow (1 + ‖v‖) (-2 : ℝ) := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hleft := ppPrimeIntegral_largeSet_rpow_bound hM hHpos hj measurableSet_Iic
    hFint hdecay (by
      intro v hv
      change v ≤ -H at hv
      have hvneg : v ≤ 0 := le_trans hv (neg_nonpos.mpr hHpos.le)
      rw [abs_of_nonpos hvneg]
      linarith)
  have hright := ppPrimeIntegral_largeSet_rpow_bound hM hHpos hj measurableSet_Ioi
    hFint hdecay (by
      intro v hv
      change H < v at hv
      rw [abs_of_pos (lt_trans hHpos hv)]
      linarith)
  have hsplitLeft := intervalIntegral.integral_Iic_add_Ioi (f := F) (b := -H)
    hFint.integrableOn hFint.integrableOn
  have hsplitRight := intervalIntegral.integral_interval_add_Ioi
    (f := F) (a := -H) (b := H) hFint.integrableOn hFint.integrableOn
  have hdecomp : (∫ v : ℝ, F v) - ∫ v : ℝ in (-H)..H, F v =
      (∫ v in Set.Iic (-H), F v) + ∫ v in Set.Ioi H, F v := by
    rw [← hsplitLeft, ← hsplitRight]
    ring
  let E : ℝ := (M * Real.rpow H (2 - j)) *
    ∫ v : ℝ, Real.rpow (1 + ‖v‖) (-2 : ℝ)
  calc
    _ = ‖(∫ v in Set.Iic (-H), F v) + ∫ v in Set.Ioi H, F v‖ := by rw [hdecomp]
    _ ≤ ‖∫ v in Set.Iic (-H), F v‖ + ‖∫ v in Set.Ioi H, F v‖ := norm_add_le _ _
    _ ≤ E + E := add_le_add (by simpa [E, mul_assoc] using hleft)
      (by simpa [E, mul_assoc] using hright)
    _ = 2 * E := by ring
    _ = _ := by dsimp [E]; ring

private theorem ppPrimeIntegral_largeSet_norm_bound
    {F : ℝ → ℂ} {S : Set ℝ} {M H : ℝ}
    (hM : 0 ≤ M) (hH : 0 < H) (hS : MeasurableSet S)
    (hFint : Integrable F)
    (hdecay : ∀ v : ℝ,
      ‖F v‖ ≤ M * Real.rpow (1 + |v|) (-4 : ℝ))
    (hlarge : ∀ v ∈ S, H ≤ |v|) :
    ‖∫ v in S, F v‖ ≤
      (M * Real.rpow H (-2 : ℝ)) *
        ∫ v : ℝ, Real.rpow (1 + ‖v‖) (-2 : ℝ) := by
  have hbase : Integrable (fun v : ℝ => Real.rpow (1 + ‖v‖) (-2 : ℝ)) :=
    integrable_one_add_norm (E := ℝ) (by norm_num)
  let K : ℝ := M * Real.rpow H (-2 : ℝ)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg hM (Real.rpow_nonneg hH.le _)
  have hmajor : Integrable (fun v : ℝ => K * Real.rpow (1 + ‖v‖) (-2 : ℝ)) :=
    hbase.const_mul K
  have hpoint : ∀ v ∈ S,
      ‖F v‖ ≤ K * Real.rpow (1 + ‖v‖) (-2 : ℝ) := by
    intro v hv
    have hvlarge := hlarge v hv
    have hvnorm : ‖v‖ = |v| := Real.norm_eq_abs v
    have hvbase : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    have hsplit : Real.rpow (1 + |v|) (-4 : ℝ) =
        Real.rpow (1 + |v|) (-2 : ℝ) * Real.rpow (1 + |v|) (-2 : ℝ) := by
      calc
        _ = Real.rpow (1 + |v|) ((-2 : ℝ) + (-2 : ℝ)) := by congr 1 <;> ring
        _ = _ := Real.rpow_add (by positivity) _ _
    have hHbase : H ≤ 1 + |v| := by linarith [hvlarge, abs_nonneg v]
    have hpower : Real.rpow (1 + |v|) (-2 : ℝ) ≤ Real.rpow H (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hH hHbase (by norm_num)
    have hbound : M * Real.rpow (1 + |v|) (-4 : ℝ) ≤
        K * Real.rpow (1 + |v|) (-2 : ℝ) := by
      rw [hsplit]
      dsimp [K]
      calc
        M * (Real.rpow (1 + |v|) (-2 : ℝ) * Real.rpow (1 + |v|) (-2 : ℝ)) ≤
            M * (Real.rpow H (-2 : ℝ) * Real.rpow (1 + |v|) (-2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpower
              (Real.rpow_nonneg (by positivity) _)) hM
        _ = M * Real.rpow H (-2 : ℝ) * Real.rpow (1 + |v|) (-2 : ℝ) := by ring
    rw [hvnorm]
    exact (hdecay v).trans hbound
  have hnorm : ‖∫ v in S, F v‖ ≤ ∫ v in S, ‖F v‖ := by
    simpa only [integral] using
      (norm_integral_le_integral_norm (μ := volume.restrict S) F)
  have hmono := setIntegral_mono_on hFint.norm.integrableOn hmajor.integrableOn hS hpoint
  have htotal :
      (∫ v in S, K * Real.rpow (1 + ‖v‖) (-2 : ℝ)) ≤
        ∫ v : ℝ, K * Real.rpow (1 + ‖v‖) (-2 : ℝ) := by
    exact setIntegral_le_integral hmajor (ae_of_all _ fun v =>
      mul_nonneg hK (Real.rpow_nonneg (by positivity) _))
  calc
    _ ≤ ∫ v in S, ‖F v‖ := hnorm
    _ ≤ ∫ v in S, K * Real.rpow (1 + ‖v‖) (-2 : ℝ) := hmono
    _ ≤ ∫ v : ℝ, K * Real.rpow (1 + ‖v‖) (-2 : ℝ) := htotal
    _ = K * ∫ v : ℝ, Real.rpow (1 + ‖v‖) (-2 : ℝ) := by rw [integral_const_mul]

private theorem ppPrimeIntegral_truncate_norm_bound
    {F : ℝ → ℂ} {M H : ℝ}
    (hM : 0 ≤ M) (hH : 1 ≤ H) (hFint : Integrable F)
    (hdecay : ∀ v : ℝ,
      ‖F v‖ ≤ M * Real.rpow (1 + |v|) (-4 : ℝ)) :
    ‖(∫ v : ℝ, F v) - ∫ v : ℝ in (-H)..H, F v‖ ≤
      2 * (M * Real.rpow H (-2 : ℝ)) *
        ∫ v : ℝ, Real.rpow (1 + ‖v‖) (-2 : ℝ) := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hleft := ppPrimeIntegral_largeSet_norm_bound hM hHpos measurableSet_Iic
    hFint hdecay (by
      intro v hv
      change v ≤ -H at hv
      have hvneg : v ≤ 0 := le_trans hv (neg_nonpos.mpr hHpos.le)
      rw [abs_of_nonpos hvneg]
      linarith)
  have hright := ppPrimeIntegral_largeSet_norm_bound hM hHpos measurableSet_Ioi
    hFint hdecay (by
      intro v hv
      change H < v at hv
      rw [abs_of_pos (lt_trans hHpos hv)]
      linarith)
  have hsplitLeft := intervalIntegral.integral_Iic_add_Ioi (f := F) (b := -H)
    hFint.integrableOn hFint.integrableOn
  have hsplitRight := intervalIntegral.integral_interval_add_Ioi
    (f := F) (a := -H) (b := H) hFint.integrableOn hFint.integrableOn
  have hdecomp : (∫ v : ℝ, F v) - ∫ v : ℝ in (-H)..H, F v =
      (∫ v in Set.Iic (-H), F v) + ∫ v in Set.Ioi H, F v := by
    rw [← hsplitLeft, ← hsplitRight]
    ring
  let E : ℝ := (M * Real.rpow H (-2 : ℝ)) *
    ∫ v : ℝ, Real.rpow (1 + ‖v‖) (-2 : ℝ)
  calc
    _ = ‖(∫ v in Set.Iic (-H), F v) + ∫ v in Set.Ioi H, F v‖ := by rw [hdecomp]
    _ ≤ ‖∫ v in Set.Iic (-H), F v‖ + ‖∫ v in Set.Ioi H, F v‖ := norm_add_le _ _
    _ ≤ E + E := add_le_add (by simpa [E, mul_assoc] using hleft)
      (by simpa [E, mul_assoc] using hright)
    _ = 2 * E := by ring
    _ = _ := by dsimp [E]; ring

private theorem ppPrimeMellinContourRectangle_norm_bound
    {F : ℂ → ℂ} {a b c d Mleft Mbottom Mtop : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hF : AnalyticOnNhd ℂ F (Set.Icc a b ×ℂ Set.Icc c d))
    (hleft : ∀ v ∈ Set.Icc c d, ‖F (a + v * Complex.I)‖ ≤ Mleft)
    (hbottom : ∀ u ∈ Set.Icc a b, ‖F (u + c * Complex.I)‖ ≤ Mbottom)
    (htop : ∀ u ∈ Set.Icc a b, ‖F (u + d * Complex.I)‖ ≤ Mtop) :
    ‖∫ v : ℝ in c..d, F (b + v * Complex.I)‖ ≤
      Mleft * (d - c) + (Mbottom + Mtop) * (b - a) := by
  have hrect := ppPrimeMellinContourRectangle_shift hab hcd hF
  have hEq : (∫ v : ℝ in c..d, F (b + v * Complex.I)) =
      (∫ v : ℝ in c..d, F (a + v * Complex.I)) +
        Complex.I • (∫ u : ℝ in a..b, F (u + c * Complex.I)) -
          Complex.I • (∫ u : ℝ in a..b, F (u + d * Complex.I)) := by
    simp only [smul_eq_mul] at hrect
    have hmul := congrArg (fun z : ℂ => Complex.I * z) hrect
    simp only [mul_add, mul_sub, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul] at hmul
    linear_combination -hmul
  have hleftNorm :
      ‖∫ v : ℝ in c..d, F (a + v * Complex.I)‖ ≤ Mleft * (d - c) := by
    calc
      _ ≤ Mleft * |d - c| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (by
          intro v hv
          have hv' : v ∈ Set.Icc c d := by
            have hv'' : c < v ∧ v ≤ d := by simpa [Set.uIoc_of_le hcd] using hv
            exact ⟨le_of_lt hv''.1, hv''.2⟩
          exact hleft v hv')
      _ = Mleft * (d - c) := by rw [abs_of_nonneg (sub_nonneg.mpr hcd)]
  have hbottomNorm :
      ‖∫ u : ℝ in a..b, F (u + c * Complex.I)‖ ≤ Mbottom * (b - a) := by
    calc
      _ ≤ Mbottom * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (by
          intro u hu
          have hu' : u ∈ Set.Icc a b := by
            have hu'' : a < u ∧ u ≤ b := by simpa [Set.uIoc_of_le hab] using hu
            exact ⟨le_of_lt hu''.1, hu''.2⟩
          exact hbottom u hu')
      _ = Mbottom * (b - a) := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  have htopNorm :
      ‖∫ u : ℝ in a..b, F (u + d * Complex.I)‖ ≤ Mtop * (b - a) := by
    calc
      _ ≤ Mtop * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (by
          intro u hu
          have hu' : u ∈ Set.Icc a b := by
            have hu'' : a < u ∧ u ≤ b := by simpa [Set.uIoc_of_le hab] using hu
            exact ⟨le_of_lt hu''.1, hu''.2⟩
          exact htop u hu')
      _ = Mtop * (b - a) := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  calc
    _ = ‖(∫ v : ℝ in c..d, F (a + v * Complex.I)) +
          Complex.I • (∫ u : ℝ in a..b, F (u + c * Complex.I)) -
            Complex.I • (∫ u : ℝ in a..b, F (u + d * Complex.I))‖ := by rw [hEq]
    _ ≤ ‖(∫ v : ℝ in c..d, F (a + v * Complex.I)) +
          Complex.I • (∫ u : ℝ in a..b, F (u + c * Complex.I))‖ +
          ‖Complex.I • (∫ u : ℝ in a..b, F (u + d * Complex.I))‖ := norm_sub_le _ _
    _ ≤ ‖∫ v : ℝ in c..d, F (a + v * Complex.I)‖ +
          ‖Complex.I • (∫ u : ℝ in a..b, F (u + c * Complex.I))‖ +
          ‖Complex.I • (∫ u : ℝ in a..b, F (u + d * Complex.I))‖ := by
        exact add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ Mleft * (d - c) + (Mbottom + Mtop) * (b - a) := by
        simpa [norm_smul, Complex.norm_I, one_mul, add_mul, add_assoc] using
          add_le_add (add_le_add hleftNorm hbottomNorm) htopNorm

private theorem ppPrimeContourGrowth
    (τ η A c L₀ xZ : ℝ)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1) (hA : 0 < A)
    (hc : 0 < c) (hL₀ : 1 ≤ L₀) :
    ∃ x₀ : ℝ, 2 < x₀ ∧ xZ ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        xZ ≤ x ∧ L₀ ≤ Real.log x ∧ 4 ≤ Real.log x ∧
        8 ≤ Real.rpow x τ ∧ Real.log 2 ≤ τ * Real.log x / 2 ∧
        Real.rpow (Real.log x) (A + 3) ≤ Real.rpow x τ ∧
        Real.rpow (Real.log x) (3 * A + 15) ≤ x ∧
        (Real.log (Real.log x)) ^ 2 ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) ∧
        c ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) ∧
        Real.exp (-(c * τ / 4) * (Real.log (Real.log x)) ^ 2 +
            ((3 * A + 15) + (A + 6)) * Real.log (Real.log x)) ≤
          Real.exp (-(A + 3) * Real.log (Real.log x)) := by
  have hlogAtTop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hdoubleLogAtTop :
      Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop := by
    convert hlogAtTop.comp hlogAtTop using 1 <;> rfl
  have hlogPow := ppPrime_log_rpow_le_rpow_eventually
    (r := A + 3) (s := τ) hτ
  have hheightPow := ppPrime_log_rpow_le_rpow_eventually
    (r := 3 * A + 15) (s := 1) (by norm_num)
  have hlogSquare : ∀ᶠ y : ℝ in atTop,
      (Real.log y) ^ 2 ≤ Real.rpow y (1 / 2 : ℝ) := by
    filter_upwards [ppPrime_log_rpow_le_rpow_eventually
      (r := 2) (s := 1 / 2) (by norm_num)] with y hy
    rw [← Real.rpow_natCast (Real.log y) 2]
    exact hy
  have hlogSquareX := hlogAtTop.eventually hlogSquare
  have hrootAtTop := tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))
  have hroot : ∀ᶠ y : ℝ in atTop, c ≤ Real.rpow y (1 / 2 : ℝ) :=
    hrootAtTop.eventually (eventually_ge_atTop c)
  have hrootX := hlogAtTop.eventually hroot
  have hgaussian := ppPrime_gaussian_exp_le_exp_neg_linear_eventually
    (a := c * τ / 4) (b := (3 * A + 15) + (A + 6)) (c := A + 3)
    (by positivity)
  have hgaussianX := hdoubleLogAtTop.eventually hgaussian
  have hlarge : ∀ᶠ x : ℝ in atTop,
      2 < x ∧ xZ ≤ x ∧ L₀ ≤ Real.log x ∧ 4 ≤ Real.log x ∧
        8 ≤ Real.rpow x τ ∧ Real.log 2 ≤ τ * Real.log x / 2 ∧
        Real.rpow (Real.log x) (A + 3) ≤ Real.rpow x τ ∧
        Real.rpow (Real.log x) (3 * A + 15) ≤ x ∧
        (Real.log (Real.log x)) ^ 2 ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) ∧
        c ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) ∧
        Real.exp (-(c * τ / 4) * (Real.log (Real.log x)) ^ 2 +
            ((3 * A + 15) + (A + 6)) * Real.log (Real.log x)) ≤
          Real.exp (-(A + 3) * Real.log (Real.log x)) := by
    filter_upwards [eventually_gt_atTop (2 : ℝ), eventually_ge_atTop xZ,
      hlogAtTop.eventually (eventually_ge_atTop L₀),
      hlogAtTop.eventually (eventually_ge_atTop (4 : ℝ)),
      (tendsto_rpow_atTop hτ).eventually (eventually_ge_atTop (8 : ℝ)),
      hlogAtTop.eventually (eventually_ge_atTop (2 * Real.log 2 / τ)),
      hlogPow, hheightPow, hlogSquareX, hrootX, hgaussianX] with
      x hx2 hxZ hxL₀ hx4 hx8 hxlogLow hxlogPow hxheight hxSquare hxroot hxgauss
    have hlogLow : Real.log 2 ≤ τ * Real.log x / 2 := by
      have hmul := (div_le_iff₀ hτ).1 hxlogLow
      nlinarith
    have hxheight' : Real.rpow (Real.log x) (3 * A + 15) ≤ x := by
      simpa [Real.rpow_one] using hxheight
    exact ⟨hx2, hxZ, hxL₀, hx4, hx8, hlogLow, hxlogPow,
      hxheight', hxSquare, hxroot, hxgauss⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hlarge
  refine ⟨x₀, (hx₀ x₀ le_rfl).1, (hx₀ x₀ le_rfl).2.1, ?_⟩
  intro x hx
  rcases hx₀ x hx with ⟨_, hxZ, hxL₀, hx4, hx8, hxlogLow, hxlogPow,
    hxheight, hxSquare, hxroot, hxgauss⟩
  exact ⟨hxZ, hxL₀, hx4, hx8, hxlogLow, hxlogPow, hxheight,
    hxSquare, hxroot, hxgauss⟩

/-- Uniform contour estimate for the endpoint cutoff, before removing smoothing. -/
private theorem ppPrimeMellinContour_zeroFree_rectangle
    {x L width H t a b : ℝ} (q : ℕ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (C₀ : ℝ)
    (hzeroFree₀ : ∀ s : ℂ, 1 - width ≤ s.re → 1 ≤ |s.im| →
      |s.im| ≤ Real.rpow x 3 → dirichletLValue q hq χ s ≠ 0)
    (hzeroFree₁ : ∀ s : ℂ, 1 - width / 2 ≤ s.re → s.re ≤ 1 + 1 / L →
      2 ≤ |s.im| → |s.im| ≤ Real.rpow x 3 / 2 →
        ‖deriv (dirichletLValue q hq χ) s / dirichletLValue q hq χ s‖ ≤ C₀ * L)
    (ha : a = -width / 2) (hb : b = 1 / L) (hwidth : 0 ≤ width)
    (hx : 2 ≤ x)
    (hheight : ∀ v ∈ Set.Icc (-H) H,
      2 ≤ |v - t| ∧ |v - t| ≤ Real.rpow x 3 / 2) :
    ∀ z ∈ Set.Icc a b ×ℂ Set.Icc (-H) H,
      1 - Complex.I * (t : ℂ) + z ≠ 1 ∧
      dirichletLValue q hq χ (1 - Complex.I * (t : ℂ) + z) ≠ 0 ∧
      ‖deriv (dirichletLValue q hq χ) (1 - Complex.I * (t : ℂ) + z) /
        dirichletLValue q hq χ (1 - Complex.I * (t : ℂ) + z)‖ ≤ C₀ * L := by
  intro z hz
  rcases Complex.mem_reProdIm.mp hz with ⟨hzRe, hzIm⟩
  let s : ℂ := 1 - Complex.I * (t : ℂ) + z
  have hsRe : s.re = 1 + z.re := by simp [s]
  have hsIm : s.im = z.im - t := by simp [s]; ring
  have him := hheight z.im hzIm
  have hAbsLower : 1 ≤ |s.im| := by
    rw [hsIm]
    exact le_trans (by norm_num) him.1
  have hAbsLowerTwo : 2 ≤ |s.im| := by
    rw [hsIm]
    exact him.1
  have hxnonneg : 0 ≤ x := by linarith
  have hrpowNonneg : 0 ≤ Real.rpow x 3 := Real.rpow_nonneg hxnonneg _
  have hrpowHalf : Real.rpow x 3 / 2 ≤ Real.rpow x 3 := by
    nlinarith
  have hAbsUpperHalf : |s.im| ≤ Real.rpow x 3 / 2 := by
    rw [hsIm]
    exact him.2
  have hAbsUpper : |s.im| ≤ Real.rpow x 3 := hAbsUpperHalf.trans hrpowHalf
  have hsReLow : 1 - width / 2 ≤ s.re := by
    calc
      1 - width / 2 = 1 + a := by rw [ha]; ring
      _ ≤ 1 + z.re := by linarith [hzRe.1]
      _ = s.re := hsRe.symm
  have hsReUpper : s.re ≤ 1 + 1 / L := by
    rw [hsRe]
    calc
      1 + z.re ≤ 1 + b := by linarith [hzRe.2]
      _ = 1 + 1 / L := by rw [hb]
  have hsZeroRe : 1 - width ≤ s.re := by
    calc
      1 - width ≤ 1 - width / 2 := by linarith [hwidth]
      _ ≤ s.re := hsReLow
  have hsPole : s ≠ 1 := by
    intro hs
    have hImZero : s.im = 0 := by
      have h := congrArg Complex.im hs
      simpa using h
    have hImAbsZero : |s.im| = 0 := by simp [hImZero]
    linarith
  have hnonzero := hzeroFree₀ s hsZeroRe hAbsLower hAbsUpper
  have hlogderiv := hzeroFree₁ s hsReLow hsReUpper hAbsLowerTwo hAbsUpperHalf
  refine ⟨?_, ?_, ?_⟩
  · simpa [s] using hsPole
  · simpa [s] using hnonzero
  · simpa [s] using hlogderiv

private theorem ppPrimeSmoothedCutoff_uniform_bound
    (hzeroFree : ∀ C : ℝ, ppPrimeZeroFree C)
    (hzeta : ppPrimeZetaLogDerivBound) :
    ∀ τ η C A : ℝ, 0 < τ → τ < η → η < 1 → 0 < C → 0 < A →
      ∃ B₀ K x₀ : ℝ, 0 < B₀ ∧ 0 < K ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ N : ℝ, Real.rpow x τ / 2 ≤ N → N ≤ Real.rpow x η →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
                Real.rpow L B₀ ≤ |t| → |t| ≤ Real.rpow x 2 →
                  ∀ m u : ℕ, N ≤ (m : ℝ) → (m : ℝ) ≤ u →
                    (u : ℝ) ≤ 2 * N →
                      ‖smoothedMangoldtPolynomial N q χ t
                        (ppPrimePositiveCutoff ((m : ℝ) / N) ((u : ℝ) / N)
                          (Real.rpow L (-A - 4)))‖ ≤
                        K * Real.rpow L (-A - 2) := by
  sorry

/-- The sharp von Mangoldt polynomial has uniform cancellation in every natural interval. -/
theorem prime_mangoldt_interval_bound (hzeroFree : ∀ C : ℝ, ppPrimeZeroFree C)
    (hzeta : ppPrimeZetaLogDerivBound) :
    ∀ τ η C A : ℝ, 0 < τ → τ < η → η < 1 → 0 < C → 0 < A →
      ∃ B₀ K x₀ : ℝ, 0 < B₀ ∧ 0 < K ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ N : ℝ, Real.rpow x τ / 2 ≤ N → N ≤ Real.rpow x η →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
                Real.rpow L B₀ ≤ |t| → |t| ≤ Real.rpow x 2 →
                  ∀ I : Set ℕ, IsNatInterval I →
                    I ⊆ {n : ℕ | N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N} →
                      ‖mangoldtIntervalPolynomial N q χ t I‖ ≤
                        K * Real.rpow L (-A - 2) := by
  sorry

/-- The prime-power terms are a uniform lower-order error in a dyadic interval. -/
theorem prime_power_removal {N : ℝ} (hN : 4 ≤ N) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (I : Set ℕ)
    (hI : I ⊆ {n : ℕ | N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N}) :
    ‖mangoldtIntervalPolynomial N q χ t I -
      ∑ p ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N ∧ p ∈ I),
        (Real.log (p : ℝ) : ℂ) * χ (p : ZMod q) *
          Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ))‖ ≤
      100 * Real.rpow N (-1 / 2) * (Real.log (3 * N)) ^ 2 := by
  sorry

/-- Final interval Abel transfer and logarithm removal, to be assembled from the preceding bounds. -/
theorem prime_polynomial_core (hzeroFree : ∀ C : ℝ, ppPrimeZeroFree C)
    (hzeta : ppPrimeZetaLogDerivBound) :
    ∀ τ η C A : ℝ, 0 < τ → τ < η → η < 1 → 0 < C → 0 < A →
      ∃ B₀ C₀ x₀ : ℝ, 0 < B₀ ∧ 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ N : ℝ, Real.rpow x τ / 2 ≤ N → N ≤ Real.rpow x η →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
                Real.rpow L B₀ ≤ |t| → |t| ≤ Real.rpow x 2 →
                  ∀ I : Set ℕ, IsNatInterval I →
                    I ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N} →
                      ‖primeDirichletPolynomial N q χ t I‖ ≤
                        C₀ * Real.rpow L (-A) := by
  sorry

end ArtinPrimitiveRoots.Proofs.PP_PRIME
