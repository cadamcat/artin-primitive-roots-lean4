import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Marked
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.PP_PRIME

open Classical
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP
open MeasureTheory
open scoped FourierTransform

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
theorem mellinKernel_uniform_decay (g : ℝ → ℝ) (L A : ℝ)
    (hL : 1 ≤ L) (hA : 0 < A) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hsmooth : ∀ α, |α| ≤ 1 →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mellinLogWeight g α))
    (hint : ∀ α, |α| ≤ 1 → ∀ j,
      Integrable (iteratedDeriv j (mellinLogWeight g α)))
    (hbound : ∀ α, |α| ≤ 1 → ∀ j,
      ∫ u : ℝ, ‖iteratedDeriv j (mellinLogWeight g α) u‖ ≤
        K j * Real.rpow L ((j : ℝ) * (A + 4))) :
    ∀ j : ℕ, ∃ Mj : ℝ, 0 < Mj ∧
      ∀ α v : ℝ, |α| ≤ 1 →
        ‖mellinKernel g (⟨α, v⟩ : ℂ)‖ ≤
          Mj * Real.rpow L (((j + 1 : ℕ) : ℝ) * (A + 5)) *
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
  refine ⟨Mj, hMj, ?_⟩
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
  simpa [E, div_eq_mul_inv, mul_assoc] using hFinal

/-- The endpoint cutoff supplies the log-weight hypotheses for uniform Mellin decay. -/
theorem ppPrimePositiveCutoff_mellinKernel_uniform_decay
    (a b L A : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hL : 1 ≤ L) (hA : 0 < A)
    (hδsmall : Real.rpow L (-A - 4) ≤ 1 / 4) :
    ∀ j : ℕ, ∃ Mj : ℝ, 0 < Mj ∧
      ∀ α v : ℝ, |α| ≤ 1 →
        ‖mellinKernel (ppPrimePositiveCutoff a b (Real.rpow L (-A - 4)))
            (⟨α, v⟩ : ℂ)‖ ≤
          Mj * Real.rpow L (((j + 1 : ℕ) : ℝ) * (A + 5)) *
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

/-- The sharp von Mangoldt polynomial has uniform cancellation in every natural interval. -/
theorem prime_mangoldt_interval_bound :
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
theorem prime_polynomial_core :
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
