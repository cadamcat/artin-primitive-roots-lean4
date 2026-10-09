import Mathlib

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.w_g

open Complex MeasureTheory Filter Asymptotics
open scoped FourierTransform Topology BigOperators

def gaussianWave (b : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * b * (x : ℂ) ^ 2)

theorem norm_gaussianWave (b : ℂ) (x : ℝ) :
    ‖gaussianWave b x‖ = Real.exp (-Real.pi * b.re * x ^ 2) := by
  unfold gaussianWave
  rw [show -(Real.pi : ℂ) * b * (x : ℂ) ^ 2 = -((Real.pi : ℂ) * b) * (x : ℂ) ^ 2 by ring,
    norm_cexp_neg_mul_sq]
  simp [Complex.mul_re]

theorem gaussianWave_decay {b : ℂ} (hb : 0 < b.re) (s : ℝ) :
    gaussianWave b =o[cocompact ℝ] fun x : ℝ => |x| ^ s := by
  have hp : 0 < ((Real.pi : ℂ) * b).re := by simpa using mul_pos Real.pi_pos hb
  unfold gaussianWave
  simpa only [neg_mul] using isLittleO_exp_neg_mul_sq_cocompact hp s

theorem summable_gaussianWave {b : ℂ} (hb : 0 < b.re) :
    Summable (fun n : ℤ => gaussianWave b (n : ℝ)) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((gaussianWave_decay hb (-2)).isBigO.comp_tendsto Int.tendsto_coe_cofinite)

theorem fourier_gaussianWave {b : ℂ} (hb : 0 < b.re) :
    𝓕 (gaussianWave b) = fun x : ℝ => (b ^ (1 / 2 : ℂ))⁻¹ * gaussianWave b⁻¹ x := by
  have h := fourier_gaussian_pi hb
  unfold gaussianWave
  simpa only [one_div, div_eq_mul_inv, mul_assoc, one_mul] using h

theorem shifted_gaussian_poisson {b : ℂ} (hb : 0 < b.re) (c : ℝ) :
    (∑' n : ℤ, gaussianWave b (c + n)) = (b ^ (1 / 2 : ℂ))⁻¹ *
      ∑' n : ℤ, gaussianWave b⁻¹ n * fourier n (c : UnitAddCircle) := by
  have hn : b ≠ 0 := by intro hzero; simp [hzero] at hb
  have hbi : 0 < (b⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hb (Complex.normSq_pos.mpr hn)
  have hF : 𝓕 (gaussianWave b) =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    rw [fourier_gaussianWave hb]
    exact (gaussianWave_decay hbi (-2)).isBigO.const_mul_left _
  rw [Real.tsum_eq_tsum_fourier_of_rpow_decay
    (by unfold gaussianWave; fun_prop) (by norm_num : (1 : ℝ) < 2)
    (gaussianWave_decay hb (-2)).isBigO hF c]
  simp_rw [fourier_gaussianWave hb, mul_assoc]
  exact tsum_mul_left

theorem dual_gaussian_tsum_tendsto {T : Type*} {l : Filter T} (b : T → ℂ)
    (hRe : Tendsto (fun t => ((b t)⁻¹).re) l atTop) (c : ℝ) :
    Tendsto (fun t => ∑' n : ℤ, gaussianWave (b t)⁻¹ n * fourier n (c : UnitAddCircle))
      l (𝓝 1) := by
  have hfournorm (n : ℤ) : ‖fourier n (c : UnitAddCircle)‖ = 1 := Circle.norm_coe _
  have hbound : Summable (fun n : ℤ => Real.exp (-Real.pi * (n : ℝ) ^ 2)) := by
    simpa only [norm_gaussianWave, Complex.one_re, mul_one] using
      (summable_gaussianWave (b := 1) (by norm_num)).norm
  suffices Tendsto (fun t => ∑' n : ℤ,
      gaussianWave (b t)⁻¹ n * fourier n (c : UnitAddCircle)) l
      (𝓝 (∑' n : ℤ, if n = 0 then (1 : ℂ) else 0)) by simpa using this
  apply tendsto_tsum_of_dominated_convergence (f := fun t (n : ℤ) =>
      gaussianWave (b t)⁻¹ n * fourier n (c : UnitAddCircle))
      (g := fun n : ℤ => if n = 0 then (1 : ℂ) else 0) hbound
  · intro n
    by_cases hn : n = 0
    · subst n
      simpa [gaussianWave] using (tendsto_const_nhds (x := (1 : ℂ)) (f := l))
    · rw [ite_eq_right hn]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have hsq : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast hn)
      have he := Real.tendsto_exp_atBot.comp
        (hRe.const_mul_atTop_of_neg (neg_lt_zero.mpr (mul_pos Real.pi_pos hsq)))
      convert he using 1
      funext t
      rw [norm_mul, norm_gaussianWave, hfournorm, mul_one]
      congr 1
      ring
  · filter_upwards [hRe.eventually (eventually_ge_atTop (1 : ℝ))] with t ht n
    rw [norm_mul, norm_gaussianWave, hfournorm, mul_one]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right ht (sq_nonneg (n : ℝ))
    nlinarith [Real.pi_pos]

theorem normalized_shifted_gaussian_tendsto {T : Type*} {l : Filter T} (b : T → ℂ)
    (hb : ∀ᶠ t in l, 0 < (b t).re)
    (hRe : Tendsto (fun t => ((b t)⁻¹).re) l atTop) (c : ℝ) :
    Tendsto (fun t => (b t) ^ (1 / 2 : ℂ) * ∑' n : ℤ, gaussianWave (b t) (c + n))
      l (𝓝 1) := by
  apply (dual_gaussian_tsum_tendsto b hRe c).congr'
  filter_upwards [hb] with t ht
  have hn : b t ≠ 0 := by intro hzero; simp [hzero] at ht
  have hcp : (b t) ^ (1 / 2 : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
  rw [shifted_gaussian_poisson ht c, ← mul_assoc, mul_inv_cancel₀ hcp, one_mul]

def periodicGaussian (q : ℕ) [NeZero q] (w : Fin q → ℂ) (b : ℂ) : ℂ :=
  ∑' n : ℤ, w ((Int.divModEquiv q n).2) * gaussianWave b n

theorem summable_periodicGaussian (q : ℕ) [NeZero q] (w : Fin q → ℂ)
    {b : ℂ} (hb : 0 < b.re) :
    Summable (fun n : ℤ => w ((Int.divModEquiv q n).2) * gaussianWave b n) := by
  have hw (a : Fin q) : ‖w a‖ ≤ ∑ i : Fin q, ‖w i‖ :=
    Finset.single_le_sum (fun i _ => norm_nonneg (w i)) (Finset.mem_univ a)
  apply ((summable_gaussianWave hb).norm.mul_left (∑ i : Fin q, ‖w i‖)).of_norm_bounded
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hw _) (norm_nonneg _)

theorem periodicGaussian_residue_sum (q : ℕ) [NeZero q] (w : Fin q → ℂ)
    {b : ℂ} (hb : 0 < b.re) :
    periodicGaussian q w b = ∑ a : Fin q, w a *
      ∑' n : ℤ, gaussianWave (b * (q : ℂ) ^ 2) ((a.val : ℝ) / q + n) := by
  let e : ℤ ≃ Fin q × ℤ := (Int.divModEquiv q).trans (Equiv.prodComm _ _)
  let F : Fin q × ℤ → ℂ := fun p => w p.1 *
    gaussianWave (b * (q : ℂ) ^ 2) ((p.1.val : ℝ) / q + p.2)
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hF (n : ℤ) : w ((Int.divModEquiv q n).2) * gaussianWave b n = F (e n) := by
    have hr : ((Int.divModEquiv q n).1 : ℝ) * (q : ℝ) +
        ((Int.divModEquiv q n).2.val : ℝ) = (n : ℝ) := by
      exact_mod_cast (Int.divModEquiv q).symm_apply_apply n
    have hr' : (((Int.divModEquiv q n).2.val : ℝ) / q +
      ((Int.divModEquiv q n).1 : ℝ)) * (q : ℝ) = (n : ℝ) := by field_simp; linarith
    change w ((Int.divModEquiv q n).2) * gaussianWave b n =
      w ((Int.divModEquiv q n).2) * gaussianWave (b * (q : ℂ) ^ 2)
        (((Int.divModEquiv q n).2.val : ℝ) / q + ((Int.divModEquiv q n).1 : ℝ))
    congr 1
    unfold gaussianWave
    congr 1
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr'
    push_cast at hc ⊢
    rw [← hc]
    ring
  have hFsum : Summable F := by
    have hh := (summable_periodicGaussian q w hb).comp_injective e.symm.injective
    apply hh.congr
    intro p
    simpa only [Function.comp_def, e.apply_symm_apply] using hF (e.symm p)
  calc
    _ = ∑' n : ℤ, F (e n) := tsum_congr hF
    _ = ∑' p : Fin q × ℤ, F p := e.tsum_eq F
    _ = ∑' a : Fin q, ∑' n : ℤ, F (a, n) := hFsum.tsum_prod
    _ = _ := by simp only [tsum_fintype, F, tsum_mul_left]

theorem gaussian_scaled_re (b : ℂ) (q : ℕ) :
    (b * (q : ℂ) ^ 2).re = b.re * (q : ℝ) ^ 2 := by
  have h : (q : ℂ) ^ 2 = (((q : ℝ) ^ 2 : ℝ) : ℂ) := by norm_cast
  have hr : ((q : ℂ) ^ 2).re = (q : ℝ) ^ 2 := congrArg Complex.re h
  have hi : ((q : ℂ) ^ 2).im = 0 := congrArg Complex.im h
  rw [Complex.mul_re, hr, hi, mul_zero, sub_zero]

theorem gaussian_scaled_inv_re (b : ℂ) (q : ℕ) :
    ((b * (q : ℂ) ^ 2)⁻¹).re = (b⁻¹).re / (q : ℝ) ^ 2 := by
  rw [mul_inv_rev]
  have h : ((q : ℂ) ^ 2)⁻¹ = (((q : ℝ) ^ 2)⁻¹ : ℝ) := by push_cast; rfl
  rw [h, Complex.re_ofReal_mul]
  ring

theorem periodicGaussian_tendsto {T : Type*} {l : Filter T} (q : ℕ) [NeZero q]
    (w : Fin q → ℂ) (b : T → ℂ) (hb : ∀ᶠ t in l, 0 < (b t).re)
    (hRe : Tendsto (fun t => ((b t)⁻¹).re) l atTop) :
    Tendsto (fun t => (b t * (q : ℂ) ^ 2) ^ (1 / 2 : ℂ) * periodicGaussian q w (b t))
      l (𝓝 (∑ a : Fin q, w a)) := by
  have hq : 0 < (q : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast NeZero.ne q)
  have hsRe : Tendsto (fun t => ((b t * (q : ℂ) ^ 2)⁻¹).re) l atTop := by
    simpa only [gaussian_scaled_inv_re, div_eq_mul_inv] using
      hRe.atTop_mul_const (inv_pos.mpr hq)
  have hsb : ∀ᶠ t in l, 0 < (b t * (q : ℂ) ^ 2).re := by
    filter_upwards [hb] with t ht
    rw [gaussian_scaled_re]
    exact mul_pos ht hq
  have hsum := tendsto_finsetSum Finset.univ (fun a _ =>
    (normalized_shifted_gaussian_tendsto (fun t => b t * (q : ℂ) ^ 2) hsb hsRe
      ((a.val : ℝ) / q)).const_mul (w a))
  simp only [mul_one] at hsum
  apply hsum.congr'
  filter_upwards [hb] with t ht
  rw [periodicGaussian_residue_sum q w ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

def gaussParameter (q : ℕ) (ε : ℝ) : ℂ := (ε : ℂ) - (2 / (q : ℂ)) * I

def gaussResidual (q : ℕ) (ε : ℝ) : ℂ := (gaussParameter q ε)⁻¹ - ((q : ℂ) / 2) * I

def gaussResidualRatio (q : ℕ) (ε : ℝ) : ℂ :=
  ((q : ℂ) ^ 2 / 4) / (1 + ((q : ℂ) * (ε : ℂ) / 2) * I)

@[simp] theorem gaussParameter_re (q : ℕ) (ε : ℝ) : (gaussParameter q ε).re = ε := by
  simp [gaussParameter, Complex.div_re]

theorem gaussParameter_ne_zero (q : ℕ) [NeZero q] (ε : ℝ) : gaussParameter q ε ≠ 0 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  intro h
  have hi := congrArg Complex.im h
  simp [gaussParameter, Complex.div_re] at hi
  exact NeZero.ne q hi

theorem gaussResidualRatio_den_ne_zero (q : ℕ) (ε : ℝ) :
    1 + ((q : ℂ) * (ε : ℂ) / 2) * I ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [Complex.div_re] at hr

theorem gaussResidual_eq_mul_ratio (q : ℕ) [NeZero q] (ε : ℝ) :
    gaussResidual q ε = (ε : ℂ) * gaussResidualRatio q ε := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hz := gaussParameter_ne_zero q ε
  have hr := gaussResidualRatio_den_ne_zero q ε
  unfold gaussResidual gaussResidualRatio
  conv_rhs => rw [← mul_div_assoc]
  apply (eq_div_iff hr).2
  field_simp [hz]
  unfold gaussParameter
  field_simp
  ring_nf
  have hI3 : I ^ (3 : ℕ) = -I := by
    calc
      I ^ 3 = I ^ 2 * I := by ring
      _ = -I := by rw [I_sq]; ring
  simp only [hI3, I_sq]
  ring

theorem gaussResidualRatio_re_pos (q : ℕ) [NeZero q] (ε : ℝ) :
    0 < (gaussResidualRatio q ε).re := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have hr := gaussResidualRatio_den_ne_zero q ε
  have hden := Complex.normSq_pos.mpr hr
  have hre : (gaussResidualRatio q ε).re = ((q : ℝ) ^ 2 / 4) /
      Complex.normSq (1 + ((q : ℂ) * (ε : ℂ) / 2) * I) := by
    unfold gaussResidualRatio
    have hs : (q : ℂ) ^ 2 = (((q : ℝ) ^ 2 : ℝ) : ℂ) := by norm_cast
    have hsre : ((q : ℂ) ^ 2).re = (q : ℝ) ^ 2 := congrArg Complex.re hs
    have hsim : ((q : ℂ) ^ 2).im = 0 := congrArg Complex.im hs
    simp [Complex.div_re, Complex.mul_re, hsre, hsim]
  rw [hre]
  exact div_pos (by positivity) hden

theorem gaussResidual_re_pos (q : ℕ) [NeZero q] {ε : ℝ} (hε : 0 < ε) :
    0 < (gaussResidual q ε).re := by
  rw [gaussResidual_eq_mul_ratio, Complex.re_ofReal_mul]
  exact mul_pos hε (gaussResidualRatio_re_pos q ε)

theorem gaussResidual_inv (q : ℕ) [NeZero q] {ε : ℝ} (hε : 0 < ε) :
    (gaussResidual q ε)⁻¹ = 4 / ((q : ℂ) ^ 2 * (ε : ℂ)) + (2 / (q : ℂ)) * I := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have he : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  rw [gaussResidual_eq_mul_ratio]
  unfold gaussResidualRatio
  field_simp
  ring

theorem gaussResidual_inv_re (q : ℕ) [NeZero q] {ε : ℝ} (hε : 0 < ε) :
    ((gaussResidual q ε)⁻¹).re = 4 / ((q : ℝ) ^ 2 * ε) := by
  rw [gaussResidual_inv q hε]
  have hs : (q : ℂ) ^ 2 = (((q : ℝ) ^ 2 : ℝ) : ℂ) := by norm_cast
  rw [hs]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_ofNat, ← Complex.ofReal_natCast,
    ← Complex.ofReal_div, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]

theorem tendsto_gaussResidual_inv_re (q : ℕ) [NeZero q] :
    Tendsto (fun ε : ℝ => ((gaussResidual q ε)⁻¹).re) (𝓝[>] (0 : ℝ)) atTop := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have h := tendsto_inv_nhdsGT_zero.const_mul_atTop
    (show (0 : ℝ) < 4 / (q : ℝ) ^ 2 by positivity)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [gaussResidual_inv_re q hε]
  ring

theorem gaussResidualRatio_continuousAt_zero (q : ℕ) :
    ContinuousAt (gaussResidualRatio q) 0 := by
  unfold gaussResidualRatio
  exact continuousAt_const.div (by fun_prop) (gaussResidualRatio_den_ne_zero q 0)

theorem principal_sqrt_sq (b : ℂ) : (b ^ (1 / 2 : ℂ)) ^ 2 = b := by
  rw [← Complex.cpow_mul_nat]
  norm_num

theorem principal_sqrt_re_pos {b : ℂ} (hb : 0 < b.re) : 0 < (b ^ (1 / 2 : ℂ)).re := by
  rw [one_div, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos_of_pos
  linarith [norm_nonneg b]

theorem principal_sqrt_mul_real {t : ℝ} (ht : 0 < t) {b : ℂ} (hb : 0 < b.re) :
    ((t : ℂ) * b) ^ (1 / 2 : ℂ) = (Real.sqrt t : ℂ) * b ^ (1 / 2 : ℂ) := by
  have hy : 0 < ((Real.sqrt t : ℂ) * b ^ (1 / 2 : ℂ)).re := by
    rw [Complex.re_ofReal_mul]
    exact mul_pos (Real.sqrt_pos_of_pos ht) (principal_sqrt_re_pos hb)
  have hs : ((Real.sqrt t : ℂ) * b ^ (1 / 2 : ℂ)) ^ 2 = (t : ℂ) * b := by
    rw [mul_pow, principal_sqrt_sq]
    have h : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by exact_mod_cast Real.sq_sqrt ht.le
    rw [h]
  rw [← hs]
  simpa only [one_div] using Complex.sq_cpow_two_inv hy

theorem principal_sqrt_gaussParameter_zero (q : ℕ) [NeZero q] :
    (gaussParameter q 0) ^ (1 / 2 : ℂ) = (1 - I) / (Real.sqrt (q : ℝ) : ℂ) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hs : (Real.sqrt (q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq.le
  have hsn : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hq).ne'
  have hy : 0 < ((1 - I) / (Real.sqrt (q : ℝ) : ℂ)).re := by
    rw [Complex.div_ofReal_re]
    simpa using one_div_pos.mpr (Real.sqrt_pos_of_pos hq)
  have hy2 : ((1 - I : ℂ) / (Real.sqrt (q : ℝ) : ℂ)) ^ 2 = gaussParameter q 0 := by
    rw [div_pow, hs]
    unfold gaussParameter
    simp only [Complex.ofReal_zero, zero_sub]
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [← hy2, one_div, Complex.sq_cpow_two_inv hy]

def gaussNormalizationRatio (q : ℕ) (ε : ℝ) : ℂ :=
  (q : ℂ) * ((gaussParameter q ε) ^ (1 / 2 : ℂ))⁻¹ /
    ((gaussResidualRatio q ε * 16) ^ (1 / 2 : ℂ))

theorem gaussNormalizationRatio_continuousAt_zero (q : ℕ) [NeZero q] :
    ContinuousAt (gaussNormalizationRatio q) 0 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have hz : gaussParameter q 0 ∈ Complex.slitPlane := by
    right
    have hz0 : gaussParameter q 0 ≠ 0 := gaussParameter_ne_zero q 0
    intro hi
    apply hz0
    apply Complex.ext
    · simp
    · simpa using hi
  have hroot : ContinuousAt (fun ε : ℝ => (gaussParameter q ε) ^ (1 / 2 : ℂ)) 0 :=
    ContinuousAt.comp (x := (0 : ℝ)) (f := gaussParameter q)
      (continuousAt_cpow_const hz) (by unfold gaussParameter; fun_prop)
  have hzroot : (gaussParameter q 0) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (gaussParameter_ne_zero q 0))
  have hrpos : 0 < (gaussResidualRatio q 0 * 16).re := by
    simpa using mul_pos (gaussResidualRatio_re_pos q 0) (by norm_num : (0 : ℝ) < 16)
  have hrr : ContinuousAt (fun ε : ℝ => (gaussResidualRatio q ε * 16) ^ (1 / 2 : ℂ)) 0 :=
    ContinuousAt.comp (x := (0 : ℝ)) (f := fun ε => gaussResidualRatio q ε * 16)
      (continuousAt_cpow_const (Or.inl hrpos))
      ((gaussResidualRatio_continuousAt_zero q).mul continuousAt_const)
  have hrne : gaussResidualRatio q 0 * 16 ≠ 0 := by intro h; simp [h] at hrpos
  exact (continuousAt_const.mul (hroot.inv₀ hzroot)).div hrr
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hrne))

theorem gaussNormalizationRatio_zero (q : ℕ) [NeZero q] :
    gaussNormalizationRatio q 0 = (Real.sqrt (q : ℝ) : ℂ) * (1 + I) / 4 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hs : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hq).ne'
  have hi : (1 - I : ℂ) ≠ 0 := by intro h; have := congrArg Complex.re h; norm_num at this
  have hr : gaussResidualRatio q 0 * 16 = (2 * (q : ℂ)) ^ 2 := by
    simp [gaussResidualRatio]
    ring
  have hp : 0 < (2 * (q : ℂ)).re := by simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) hq)
  unfold gaussNormalizationRatio
  rw [principal_sqrt_gaussParameter_zero, hr, one_div, Complex.sq_cpow_two_inv hp]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

def quadraticResidueWeight (q : ℕ) [NeZero q] (a : Fin q) : ℂ :=
  ZMod.stdAddChar ((a.val : ZMod q) ^ 2)

def inverseResidueWeight (q : ℕ) (a : Fin 4) : ℂ :=
  ZMod.stdAddChar (-(q : ZMod 4) * (a.val : ZMod 4) ^ 2)

theorem divMod_residue_zmod (q : ℕ) [NeZero q] (n : ℤ) :
    ((Int.divModEquiv q n).2.val : ZMod q) = (n : ZMod q) := by
  have hr := (Int.divModEquiv q).symm_apply_apply n
  have hz := congrArg (fun m : ℤ => (m : ZMod q)) hr
  simpa using hz

theorem quadraticResidueWeight_int (q : ℕ) [NeZero q] (n : ℤ) :
    quadraticResidueWeight q ((Int.divModEquiv q n).2) =
      Complex.exp (2 * (Real.pi : ℂ) * I * (n : ℂ) ^ 2 / (q : ℂ)) := by
  rw [quadraticResidueWeight, divMod_residue_zmod, ← Int.cast_pow, ZMod.stdAddChar_coe]
  push_cast
  rfl

theorem inverseResidueWeight_int (q : ℕ) (n : ℤ) :
    inverseResidueWeight q ((Int.divModEquiv 4 n).2) =
      Complex.exp (-(Real.pi : ℂ) * I * (q : ℂ) * (n : ℂ) ^ 2 / 2) := by
  rw [inverseResidueWeight, divMod_residue_zmod]
  have h : -(q : ZMod 4) * (n : ZMod 4) ^ 2 = ((-(q : ℤ) * n ^ 2 : ℤ) : ZMod 4) := by
    push_cast
    rfl
  rw [h, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

theorem stdAddChar_four_one : ZMod.stdAddChar (1 : ZMod 4) = I := by
  calc
    _ = Complex.exp (2 * (Real.pi : ℂ) * I * 1 / 4) := by
      simpa using (ZMod.stdAddChar_coe (N := 4) 1)
    _ = Complex.exp ((Real.pi : ℂ) / 2 * I) := by congr 1; ring
    _ = I := Complex.exp_pi_div_two_mul_I

theorem stdAddChar_four_neg_one : ZMod.stdAddChar (-1 : ZMod 4) = -I := by
  calc
    _ = Complex.exp (2 * (Real.pi : ℂ) * I * (-1) / 4) := by
      simpa using (ZMod.stdAddChar_coe (N := 4) (-1))
    _ = Complex.exp (-(Real.pi : ℂ) / 2 * I) := by congr 1; ring
    _ = -I := Complex.exp_neg_pi_div_two_mul_I

theorem inverseResidueWeight_sum_one {q : ℕ} (hq : q % 4 = 1) :
    (∑ a : Fin 4, inverseResidueWeight q a) = 2 * (1 - I) := by
  have hq4 : (q : ZMod 4) = 1 :=
    (ZMod.natCast_eq_natCast_iff' q 1 4).mpr (by simpa using hq)
  norm_num [inverseResidueWeight, hq4, Fin.sum_univ_succ, stdAddChar_four_neg_one,
    show (-4 : ZMod 4) = 0 by decide, show (-9 : ZMod 4) = -1 by decide]
  ring

theorem inverseResidueWeight_sum_three {q : ℕ} (hq : q % 4 = 3) :
    (∑ a : Fin 4, inverseResidueWeight q a) = 2 * (1 + I) := by
  have hq4 : (q : ZMod 4) = 3 :=
    (ZMod.natCast_eq_natCast_iff' q 3 4).mpr (by simpa using hq)
  norm_num [inverseResidueWeight, hq4, Fin.sum_univ_succ, stdAddChar_four_one,
    show (-3 : ZMod 4) = 1 by decide, show (-12 : ZMod 4) = 0 by decide,
    show (-27 : ZMod 4) = 1 by decide, show (4 : ZMod 4) = 0 by decide,
    show (9 : ZMod 4) = 1 by decide]
  simp only [show (4 : ZMod 4) = 0 by decide, show (9 : ZMod 4) = 1 by decide,
    AddChar.map_zero_eq_one, stdAddChar_four_one]
  ring

theorem periodicGaussian_quadratic (q : ℕ) [NeZero q] (ε : ℝ) :
    periodicGaussian q (quadraticResidueWeight q) (ε : ℂ) =
      ∑' n : ℤ, gaussianWave (gaussParameter q ε) n := by
  unfold periodicGaussian
  apply tsum_congr
  intro n
  rw [quadraticResidueWeight_int]
  unfold gaussianWave gaussParameter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem periodicGaussian_inverse (q : ℕ) [NeZero q] (ε : ℝ) :
    (∑' n : ℤ, gaussianWave (gaussParameter q ε)⁻¹ n) =
      periodicGaussian 4 (inverseResidueWeight q) (gaussResidual q ε) := by
  unfold periodicGaussian
  apply tsum_congr
  intro n
  rw [inverseResidueWeight_int]
  unfold gaussianWave gaussResidual
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem normalized_quadratic_gaussian_transfer (q : ℕ) [NeZero q] {ε : ℝ} (hε : 0 < ε) :
    (((ε : ℂ) * (q : ℂ) ^ 2) ^ (1 / 2 : ℂ)) *
      periodicGaussian q (quadraticResidueWeight q) (ε : ℂ) =
    gaussNormalizationRatio q ε *
      (((gaussResidual q ε * 16) ^ (1 / 2 : ℂ)) *
        periodicGaussian 4 (inverseResidueWeight q) (gaussResidual q ε)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have hz : 0 < (gaussParameter q ε).re := by simpa using hε
  have htheta : (∑' n : ℤ, gaussianWave (gaussParameter q ε) n) =
      ((gaussParameter q ε) ^ (1 / 2 : ℂ))⁻¹ *
        ∑' n : ℤ, gaussianWave (gaussParameter q ε)⁻¹ n := by
    simpa using shifted_gaussian_poisson hz 0
  have hqre : 0 < ((q : ℂ) ^ 2).re := by
    have hs : (q : ℂ) ^ 2 = (((q : ℝ) ^ 2 : ℝ) : ℂ) := by norm_cast
    rw [hs, Complex.ofReal_re]
    positivity
  have hrre : 0 < (gaussResidualRatio q ε * 16).re := by
    simpa using mul_pos (gaussResidualRatio_re_pos q ε) (by norm_num : (0 : ℝ) < 16)
  have hleft : (((ε : ℂ) * (q : ℂ) ^ 2) ^ (1 / 2 : ℂ)) =
      (Real.sqrt ε : ℂ) * (q : ℂ) := by
    rw [principal_sqrt_mul_real hε hqre, one_div, Complex.sq_cpow_two_inv (by simpa using hq)]
  have hright : (gaussResidual q ε * 16) ^ (1 / 2 : ℂ) =
      (Real.sqrt ε : ℂ) * (gaussResidualRatio q ε * 16) ^ (1 / 2 : ℂ) := by
    rw [gaussResidual_eq_mul_ratio, mul_assoc, principal_sqrt_mul_real hε hrre]
  have hrr : (gaussResidualRatio q ε * 16) ^ (1 / 2 : ℂ) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    intro h
    simp [h] at hrre
  have hzz : (gaussParameter q ε) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (gaussParameter_ne_zero q ε))
  rw [periodicGaussian_quadratic, htheta, periodicGaussian_inverse, hleft, hright]
  unfold gaussNormalizationRatio
  field_simp

theorem quadratic_phase_sum_identity (q : ℕ) [NeZero q] :
    (∑ a : Fin q, quadraticResidueWeight q a) =
      (((Real.sqrt (q : ℝ) : ℂ) * (1 + I) / 4) *
        (∑ a : Fin 4, inverseResidueWeight q a)) := by
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < (ε : ℂ).re := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hε
  have hRe : Tendsto (fun ε : ℝ => ((ε : ℂ)⁻¹).re) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [← Complex.ofReal_inv, Complex.ofReal_re] using tendsto_inv_nhdsGT_zero
  have hleft := periodicGaussian_tendsto q (quadraticResidueWeight q)
    (fun ε : ℝ => (ε : ℂ)) hb hRe
  have hbr : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < (gaussResidual q ε).re := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact gaussResidual_re_pos q hε
  have hright := ((gaussNormalizationRatio_continuousAt_zero q).tendsto.mono_left
    nhdsWithin_le_nhds).mul (periodicGaussian_tendsto 4 (inverseResidueWeight q)
      (gaussResidual q) hbr (tendsto_gaussResidual_inv_re q))
  norm_num only [show (4 : ℂ) ^ 2 = 16 by norm_num] at hright
  rw [gaussNormalizationRatio_zero] at hright
  have heq : (fun ε : ℝ => (((ε : ℂ) * (q : ℂ) ^ 2) ^ (1 / 2 : ℂ)) *
      periodicGaussian q (quadraticResidueWeight q) (ε : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => gaussNormalizationRatio q ε *
        (((gaussResidual q ε * 16) ^ (1 / 2 : ℂ)) *
          periodicGaussian 4 (inverseResidueWeight q) (gaussResidual q ε))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact normalized_quadratic_gaussian_transfer q hε
  exact tendsto_nhds_unique (hleft.congr' heq) hright

private def finZModEquiv {n : ℕ} [NeZero n] : Fin n ≃ ZMod n :=
  Equiv.ofBijective (fun i : Fin n => (i.val : ZMod n)) (by
    constructor
    · intro i j hij
      apply Fin.ext
      have hval := congrArg ZMod.val hij
      simpa [ZMod.val_natCast_of_lt i.is_lt, ZMod.val_natCast_of_lt j.is_lt] using hval
    · intro z
      exact ⟨⟨z.val, z.val_lt⟩, ZMod.natCast_zmod_val z⟩)

theorem zmod_sum_eq_fin {n : ℕ} [NeZero n] (f : ZMod n → ℂ) :
    (∑ x : ZMod n, f x) = ∑ x : Fin n, f (x.val : ZMod n) := by
  exact (Equiv.sum_comp finZModEquiv f).symm

theorem quadratic_square_sum_gauss_eval (q : ℕ) [NeZero q] (hq : Odd q) :
    (∑ x : ZMod q, ZMod.stdAddChar (x ^ 2)) =
      (if q % 4 = 1 then (1 : ℂ) else I) * (Real.sqrt (q : ℝ) : ℂ) := by
  rw [zmod_sum_eq_fin]
  change (∑ a : Fin q, quadraticResidueWeight q a) = _
  rw [quadratic_phase_sum_identity]
  have hmod : q % 4 = 1 ∨ q % 4 = 3 := by
    have h := Nat.odd_iff.mp hq
    omega
  rcases hmod with h | h
  · rw [inverseResidueWeight_sum_one h, if_pos h]
    ring_nf
    simp only [I_sq]
    ring
  · rw [inverseResidueWeight_sum_three h, if_neg (by omega)]
    ring_nf
    simp only [I_sq]
    ring

noncomputable def quadraticCharComplex (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

theorem square_sum_eq_quadratic_gaussSum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    (∑ x : F, ψ (x ^ 2)) = gaussSum (quadraticCharComplex F) ψ := by
  classical
  calc
    _ = ∑ a : F, ∑ x ∈ Finset.univ.filter (fun x : F => x ^ 2 = a), ψ a :=
      (Finset.sum_fiberwise' Finset.univ (fun x : F => x ^ 2) ψ).symm
    _ = ∑ a : F, ((quadraticCharComplex F a : ℂ) + 1) * ψ a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hc := quadraticChar_card_sqrts hF a
      have hf : Finset.univ.filter (fun x : F => x ^ 2 = a) = {x : F | x ^ 2 = a}.toFinset := by
        ext x
        simp
      rw [hf]
      change (({x : F | x ^ 2 = a}.toFinset.card : ℂ)) =
        (quadraticChar F a : ℂ) + 1
      exact_mod_cast hc
    _ = gaussSum (quadraticCharComplex F) ψ := by
      calc
        _ = (∑ a : F, quadraticCharComplex F a * ψ a) + ∑ a : F, ψ a := by
          simp only [add_mul, one_mul, Finset.sum_add_distrib]
        _ = _ := by
          rw [AddChar.sum_eq_zero_of_ne_one hψ, add_zero]
          rfl

end ArtinPrimitiveRoots.Proofs.w_g

end
