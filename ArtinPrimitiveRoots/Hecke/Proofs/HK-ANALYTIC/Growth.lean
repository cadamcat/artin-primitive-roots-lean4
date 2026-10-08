import ArtinPrimitiveRoots.Hecke.Continuation
import ArtinPrimitiveRoots.Hecke.Dedekind
import ArtinPrimitiveRoots.Hecke.Dedekind.SimplePole
import ArtinPrimitiveRoots.Hecke.Proofs.«HK-ANALYTIC».GammaRatio
import Mathlib.Analysis.Complex.PhragmenLindelof

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Complex Filter Topology MeasureTheory intervalIntegral Asymptotics
open Asymptotics
open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.HK_MISC_P

open ArtinPrimitiveRoots.Hecke

private def invDedekindPrefactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s / 2) *
    ((Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
      (Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K)

private theorem differentiable_nat_pow_complex {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (n : ℕ) : Differentiable ℂ (fun s => f s ^ n) := by
  induction n with
  | zero => fun_prop
  | succ n ih =>
      change Differentiable ℂ ((fun s : ℂ => f s ^ n) * f)
      exact ih.mul hf

private theorem invDedekindPrefactor_differentiable (K : Type*)
    [Field K] [NumberField K] :
    Differentiable ℂ (invDedekindPrefactor K) := by
  have hD : ((|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact_mod_cast (abs_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hDdiff : Differentiable ℂ
      (fun s : ℂ => ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s / 2)) := by
    intro s
    exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hD)
  have hR : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) :=
    Complex.differentiable_Gammaℝ_inv
  have hC : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℂ s)⁻¹) :=
    Complex.differentiable_Gammaℂ_inv
  exact hDdiff.mul ((differentiable_nat_pow_complex hR _).mul
    (differentiable_nat_pow_complex hC _))

private theorem pow_mul_inv_pow_eq_one {g : ℂ} (hg : g ≠ 0) (n : ℕ) :
    g ^ n * g⁻¹ ^ n = 1 := by
  rw [← mul_pow, mul_inv_cancel₀ hg, one_pow]

private theorem dedekindPrefactor_mul_inv_eq_one (K : Type*) [Field K]
    [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    ArtinPrimitiveRoots.Hecke.dedekindPrefactor K s * invDedekindPrefactor K s = 1 := by
  let D : ℂ := ((|(discr K : ℝ)| : ℝ) : ℂ)
  have hD : D ≠ 0 := by
    dsimp [D]
    apply Complex.ofReal_ne_zero.mpr
    exact_mod_cast (abs_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hDpow : D ^ (s / 2) * D ^ (-s / 2) = 1 := by
    rw [← Complex.cpow_add _ _ hD]
    have he : s / 2 + -s / 2 = (0 : ℂ) := by ring
    rw [he, Complex.cpow_zero]
  have hDpow' :
      ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) *
        ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s / 2) = 1 := by
    simpa [D] using hDpow
  have hR : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hC : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    have hbase : (2 * Real.pi : ℂ) ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)))
      (Complex.Gamma_ne_zero_of_re_pos (by linarith))
  have hRpow := pow_mul_inv_pow_eq_one hR (NumberField.InfinitePlace.nrRealPlaces K)
  have hCpow := pow_mul_inv_pow_eq_one hC (NumberField.InfinitePlace.nrComplexPlaces K)
  rw [ArtinPrimitiveRoots.Hecke.dedekindPrefactor, invDedekindPrefactor]
  exact calc
    ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) *
        (Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K) *
        (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s / 2) *
          ((Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
            (Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K)) =
      (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) *
          ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s / 2)) *
        ((Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K *
            (Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K) *
          (Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K *
            (Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K)) := by ring
    _ = 1 := by rw [hDpow', hRpow, hCpow]; ring

private theorem simplePole_mul_s_eq_completed (K : Type*) [Field K] [NumberField K]
    (G : ℂ → ℂ) (hGdiff : Differentiable ℂ G)
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * dedekindZeta K s)
    (s : ℂ) (hs0 : s ≠ 0) :
    G s = DedekindResidue.completedDedekindZetaEntire K s *
      invDedekindPrefactor K s / s := by
  obtain ⟨ξ, hξdiff, hξeq, hξfe, hξ1⟩ := ArtinPrimitiveRoots.Hecke.dedekind_completed K
  let f : ℂ → ℂ := fun z => z * G z
  let g : ℂ → ℂ := fun z => ξ z * invDedekindPrefactor K z
  have hfdiff : Differentiable ℂ f := by
    dsimp [f]
    fun_prop
  have hgdifferentiable : Differentiable ℂ g := by
    dsimp [g]
    exact hξdiff.mul (invDedekindPrefactor_differentiable K)
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hξEntireEq : ∀ z : ℂ, ξ z = DedekindResidue.completedDedekindZetaEntire K z := by
    let ξ₀ : ℂ → ℂ := DedekindResidue.completedDedekindZetaEntire K
    have hξ₀diff : Differentiable ℂ ξ₀ := by
      simpa [ξ₀] using DedekindResidue.differentiable_completedDedekindZetaEntire K
    have hopen' : IsOpen {z : ℂ | 1 < z.re} := hopen
    have hpre' : Set.EqOn ξ ξ₀ {z : ℂ | 1 < z.re} := by
      intro z hz
      have hz0 : z ≠ 0 := by
        intro he
        rw [he] at hz
        norm_num [Complex.zero_re] at hz
      have hz1 : z ≠ 1 := by
        intro he
        rw [he] at hz
        norm_num [Complex.one_re] at hz
      rw [hξeq z hz,
        show ξ₀ z = z * (z - 1) * dedekindPrefactor K z * dedekindZeta K z by
          dsimp [ξ₀]
          rw [DedekindResidue.completedDedekindZetaEntire_eq K hz0 hz1,
            DedekindResidue.completedDedekindZeta_eq_of_one_lt_re K hz,
            ← ArtinPrimitiveRoots.Hecke.dedekindPrefactor_eq_completedZetaPrefactor K z]
          ring]
    have h2mem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    have hagree := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (𝕜 := ℂ) (f := ξ) (g := ξ₀)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hξdiff)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hξ₀diff)
      isPreconnected_univ (Set.mem_univ (2 : ℂ))
      (hpre'.eventuallyEq_of_mem (hopen'.mem_nhds h2mem))
    intro z
    exact hagree (Set.mem_univ z)
  have hpre : Set.EqOn f g {z : ℂ | 1 < z.re} := by
    intro z hz
    have hzspec := hξeq z hz
    have hzpole := hGeq z hz
    have hpref := dedekindPrefactor_mul_inv_eq_one K hz
    dsimp [f, g]
    rw [hzspec, hzpole]
    calc
      z * ((z - 1) * dedekindZeta K z) =
          z * (z - 1) * dedekindZeta K z := by ring
      _ = z * (z - 1) * dedekindZeta K z *
          (dedekindPrefactor K z * invDedekindPrefactor K z) := by rw [hpref]; ring
      _ = z * (z - 1) * dedekindPrefactor K z * dedekindZeta K z *
          invDedekindPrefactor K z := by ring
  have h2mem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have hagree := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (𝕜 := ℂ) (f := f) (g := g)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hfdiff)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hgdifferentiable)
    isPreconnected_univ (Set.mem_univ (2 : ℂ))
    (hpre.eventuallyEq_of_mem (hopen.mem_nhds h2mem))
  have hident : ∀ z : ℂ, z * G z = ξ z * invDedekindPrefactor K z := by
    intro z
    exact hagree (Set.mem_univ z)
  have hmul : s * G s =
      DedekindResidue.completedDedekindZetaEntire K s * invDedekindPrefactor K s := by
    rw [← hξEntireEq s]
    exact hident s
  exact calc
    G s = (s * G s) / s := by field_simp [hs0]
    _ = (DedekindResidue.completedDedekindZetaEntire K s *
        invDedekindPrefactor K s) / s := by rw [hmul]
    _ = _ := by ring

private theorem norm_sin_le_exp_norm (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.sin]
  have hneg : ‖-z * Complex.I‖ = ‖z‖ := by
    rw [norm_mul, norm_neg, norm_I, mul_one]
  have hpos : ‖z * Complex.I‖ = ‖z‖ := by
    rw [norm_mul, norm_I, mul_one]
  calc
    ‖(Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2‖
        = ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ / 2 := by
          rw [norm_div, norm_mul, norm_I]
          norm_num
    _ ≤ (‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖) / 2 := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ (Real.exp ‖z‖ + Real.exp ‖z‖) / 2 := by
          gcongr
          · simpa [hneg] using Complex.norm_exp_le_exp_norm (-z * Complex.I)
          · simpa [hpos] using Complex.norm_exp_le_exp_norm (z * Complex.I)
    _ = Real.exp ‖z‖ := by ring

private theorem norm_complexGamma_le_realGamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  calc
    ‖Complex.Gamma z‖ =
        ‖∫ x in Set.Ioi (0 : ℝ), (↑(-x).exp : ℂ) * (↑x : ℂ) ^ (z - 1)‖ := by
          rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral]
    _ ≤ ∫ x in Set.Ioi (0 : ℝ),
          ‖(↑(-x).exp : ℂ) * (↑x : ℂ) ^ (z - 1)‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          change ‖(↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ (z - 1)‖ = _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos hx]
          simp [Complex.sub_re]
    _ = Real.Gamma z.re := (Real.Gamma_eq_integral hz).symm

private theorem real_Gamma_le_nine {x : ℝ} (hx1 : 1 ≤ x) (hx8 : x ≤ 8) :
    Real.Gamma x ≤ Real.Gamma 9 := by
  have hxpos : 0 < x := by linarith
  have hrec := Real.Gamma_add_one (ne_of_gt hxpos)
  have hstep : Real.Gamma x ≤ Real.Gamma (x + 1) := by
    rw [hrec]
    have hΓ : 0 ≤ Real.Gamma x := (Real.Gamma_pos_of_pos hxpos).le
    nlinarith
  have hmono : Real.Gamma (x + 1) ≤ Real.Gamma 9 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn
      (by simp; linarith) (by norm_num) (by linarith)
  exact hstep.trans hmono

private theorem gamma_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  have him := congrArg Complex.im hn
  have hzero : z.im = 0 := by simpa using him
  exact hz hzero

private theorem gamma_inv_reflection {z : ℂ} (hz : z.im ≠ 0) :
    (Complex.Gamma z)⁻¹ =
      Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi := by
  have hΓz : Complex.Gamma z ≠ 0 := gamma_ne_zero_of_im_ne_zero hz
  have hΓone : Complex.Gamma (1 - z) ≠ 0 := by
    apply gamma_ne_zero_of_im_ne_zero
    simp [hz]
  have hsin : Complex.sin (Real.pi * z) ≠ 0 := by
    intro h
    have href := Complex.Gamma_mul_Gamma_one_sub z
    rw [h] at href
    simp at href
    rcases href with hz0 | hone0
    · exact hΓz hz0
    · exact hΓone hone0
  have hmul : Complex.Gamma z * Complex.Gamma (1 - z) *
      Complex.sin (Real.pi * z) = (Real.pi : ℂ) := by
    calc
      Complex.Gamma z * Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) =
          ((Real.pi : ℂ) / Complex.sin (Real.pi * z)) * Complex.sin (Real.pi * z) := by
            rw [Complex.Gamma_mul_Gamma_one_sub]
      _ = (Real.pi : ℂ) := div_mul_cancel₀ _ hsin
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hval : Complex.Gamma z *
      (Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi) = 1 := by
    calc
      Complex.Gamma z *
          (Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi) =
        (Complex.Gamma z * Complex.Gamma (1 - z) * Complex.sin (Real.pi * z)) /
          Real.pi := by ring
      _ = (Real.pi : ℂ) / Real.pi := by rw [hmul]
      _ = 1 := div_self hπ
  apply (mul_left_cancel₀ hΓz)
  calc
    Complex.Gamma z * (Complex.Gamma z)⁻¹ = 1 := mul_inv_cancel₀ hΓz
    _ = Complex.Gamma z *
        (Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi) := hval.symm

private theorem norm_Gamma_le_nine {z : ℂ} (hz1 : 1 ≤ z.re) (hz8 : z.re ≤ 8) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma 9 := by
  exact (norm_complexGamma_le_realGamma (by linarith)).trans
    (real_Gamma_le_nine hz1 hz8)

private theorem gamma_shift_up_four {w : ℂ} (hw : w.im ≠ 0) :
    Complex.Gamma w = Complex.Gamma (w + 4) /
      (w * (w + 1) * (w + 2) * (w + 3)) := by
  have hn (k : ℕ) : w + (k : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    have hzero : w.im = 0 := by simpa using him
    exact hw hzero
  have hstep (k : ℕ) : Complex.Gamma (w + (k + 1 : ℕ)) =
      (w + k) * Complex.Gamma (w + k) := by
    have hk := Complex.Gamma_add_one (w + k) (hn k)
    simpa [Nat.cast_succ, add_assoc] using hk
  have hrec0 : Complex.Gamma (w + 1) = w * Complex.Gamma w := by simpa using hstep 0
  have hrec1 : Complex.Gamma (w + 2) = (w + 1) * Complex.Gamma (w + 1) := by
    simpa using hstep 1
  have hrec2 : Complex.Gamma (w + 3) = (w + 2) * Complex.Gamma (w + 2) := by
    simpa using hstep 2
  have hrec3 : Complex.Gamma (w + 4) = (w + 3) * Complex.Gamma (w + 3) := by
    simpa using hstep 3
  have hprod : Complex.Gamma (w + 4) = Complex.Gamma w *
      (w * (w + 1) * (w + 2) * (w + 3)) := by
    calc
      Complex.Gamma (w + 4) = (w + 3) * Complex.Gamma (w + 3) := hrec3
      _ = (w + 3) * ((w + 2) * Complex.Gamma (w + 2)) := by rw [hrec2]
      _ = (w + 3) * ((w + 2) * ((w + 1) * Complex.Gamma (w + 1))) := by rw [hrec1]
      _ = (w + 3) * ((w + 2) * ((w + 1) * (w * Complex.Gamma w))) := by rw [hrec0]
      _ = _ := by ring
  have hprodne : w * (w + 1) * (w + 2) * (w + 3) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · simpa using hn 0
        · simpa using hn 1
      · simpa using hn 2
    · simpa using hn 3
  rw [hprod]
  simp [hprodne]

private theorem norm_inv_Gamma_on_strip {z : ℂ} (hzlo : -3 ≤ z.re)
    (hzhi : z.re ≤ 4) (hzim : 1 / 2 ≤ |z.im|) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ 16 * Real.Gamma 9 *
      Real.exp (Real.pi * (4 + |z.im|)) := by
  have him : z.im ≠ 0 := by
    intro h
    rw [h] at hzim
    norm_num at hzim
  have hreflect := gamma_inv_reflection him
  let w : ℂ := 1 - z
  have hwIm : w.im ≠ 0 := by simp [w, him]
  have hwlo : 1 ≤ (w + 4).re := by simp [w]; linarith
  have hwhi : (w + 4).re ≤ 8 := by simp [w]; linarith
  have hwGamma := norm_Gamma_le_nine hwlo hwhi
  have hshift := gamma_shift_up_four hwIm
  have hprodNorm :
      1 / 16 ≤ ‖w * (w + 1) * (w + 2) * (w + 3)‖ := by
    have himw : |w.im| = |z.im| := by simp [w]
    have hfactor (k : ℕ) : 1 / 2 ≤ ‖w + k‖ := by
      have h := Complex.abs_im_le_norm (w + k)
      have himk : (w + k).im = w.im := by simp
      rw [himk] at h
      have h' : 1 / 2 ≤ |w.im| := by rw [himw]; exact hzim
      exact h'.trans h
    rw [norm_mul, norm_mul, norm_mul]
    have h0 : 1 / 2 ≤ ‖w‖ := by simpa using hfactor 0
    have h1 : 1 / 2 ≤ ‖w + 1‖ := by simpa using hfactor 1
    have h2 : 1 / 2 ≤ ‖w + 2‖ := by simpa using hfactor 2
    have h3 : 1 / 2 ≤ ‖w + 3‖ := by simpa using hfactor 3
    calc
      1 / 16 = (1 / 2) * (1 / 2) * (1 / 2) * (1 / 2) := by norm_num
      _ ≤ ‖w‖ * ‖w + 1‖ * ‖w + 2‖ * ‖w + 3‖ := by
        gcongr
  have hGammaW : ‖Complex.Gamma w‖ ≤ 16 * Real.Gamma 9 := by
    calc
      ‖Complex.Gamma w‖ =
          ‖Complex.Gamma (w + 4)‖ / ‖w * (w + 1) * (w + 2) * (w + 3)‖ := by
            rw [hshift, norm_div]
      _ ≤ ‖Complex.Gamma (w + 4)‖ / (1 / 16) := by
            exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hprodNorm
      _ = 16 * ‖Complex.Gamma (w + 4)‖ := by
            rw [div_eq_mul_inv]
            norm_num
            ring
      _ ≤ 16 * Real.Gamma 9 := by gcongr
  have hsin := norm_sin_le_exp_norm (Real.pi * z)
  have hzNorm : ‖z‖ ≤ 4 + |z.im| := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 4 + |z.im| := by
        have : |z.re| ≤ 4 := by rw [abs_le]; constructor <;> linarith
        linarith
  have hpiNorm : ‖(Real.pi : ℂ) * z‖ ≤ Real.pi * (4 + |z.im|) := by
    have hπnorm : ‖(Real.pi : ℂ)‖ = Real.pi := by
      calc
        ‖(Real.pi : ℂ)‖ = |Real.pi| := by simp
        _ = Real.pi := abs_of_pos Real.pi_pos
    rw [norm_mul, hπnorm]
    exact mul_le_mul_of_nonneg_left hzNorm (le_of_lt Real.pi_pos)
  calc
    ‖(Complex.Gamma z)⁻¹‖ =
        ‖Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi‖ :=
          congrArg norm hreflect
    _ = ‖Complex.Gamma w * Complex.sin (Real.pi * z)‖ / Real.pi := by
          rw [norm_div]
          simp [w]
    _ ≤ (16 * Real.Gamma 9 * ‖Complex.sin (Real.pi * z)‖) / Real.pi := by
          rw [norm_mul]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hGammaW (norm_nonneg _)) Real.pi_pos.le
    _ ≤ (16 * Real.Gamma 9 * Real.exp ‖(Real.pi : ℂ) * z‖) / Real.pi := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsin
              (mul_nonneg (by norm_num) (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 9)).le))
            Real.pi_pos.le
    _ ≤ 16 * Real.Gamma 9 * Real.exp (Real.pi * (4 + |z.im|)) := by
          have hπ1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
          calc
            (16 * Real.Gamma 9 * Real.exp ‖(Real.pi : ℂ) * z‖) / Real.pi ≤
                16 * Real.Gamma 9 * Real.exp ‖(Real.pi : ℂ) * z‖ := by
                  exact div_le_self (by positivity) hπ1
            _ ≤ 16 * Real.Gamma 9 * Real.exp (Real.pi * (4 + |z.im|)) := by
                  exact mul_le_mul_of_nonneg_left
                    (Real.exp_le_exp.mpr hpiNorm)
                    (mul_nonneg (by norm_num)
                      (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 9)).le)

private theorem gammaR_inv_formula (s : ℂ) :
    (Complex.Gammaℝ s)⁻¹ = (Real.pi : ℂ) ^ (s / 2) *
      (Complex.Gamma (s / 2))⁻¹ := by
  rw [Complex.Gammaℝ_def, mul_inv_rev]
  have hcpow : (Real.pi : ℂ) ^ (-s / 2) =
      ((Real.pi : ℂ) ^ (s / 2))⁻¹ := by
    rw [show -s / 2 = -(s / 2) by ring, Complex.cpow_neg]
  rw [hcpow, inv_inv]
  ring

private theorem gammaC_inv_formula (s : ℂ) :
    (Complex.Gammaℂ s)⁻¹ = (1 / 2 : ℂ) * (2 * Real.pi : ℂ) ^ s *
      (Complex.Gamma s)⁻¹ := by
  simp [Complex.Gammaℂ_def, Complex.cpow_neg, mul_comm, mul_left_comm, mul_assoc]

private def invPrefactorHeightConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  1 + |(discr K : ℝ)| +
    (16 * Real.pi ^ (2 : ℝ) * Real.Gamma 9) *
      (NumberField.InfinitePlace.nrRealPlaces K : ℝ) +
    (16 * (2 * Real.pi) ^ (4 : ℝ) * Real.Gamma 9) *
      (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) +
    5 * Real.pi * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ) +
      (NumberField.InfinitePlace.nrComplexPlaces K : ℝ))

private theorem invDedekindPrefactor_norm_bound
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hlo : -1 / 4 ≤ s.re) (hhi : s.re ≤ 4) (ht : 1 ≤ |s.im|) :
    ‖invDedekindPrefactor K s‖ ≤ Real.exp (invPrefactorHeightConstant K * (1 + |s.im|)) := by
  let Q : ℝ := |(discr K : ℝ)|
  let r₁ : ℝ := (NumberField.InfinitePlace.nrRealPlaces K : ℝ)
  let r₂ : ℝ := (NumberField.InfinitePlace.nrComplexPlaces K : ℝ)
  let C₁ : ℝ := 16 * Real.pi ^ (2 : ℝ) * Real.Gamma 9
  let C₂ : ℝ := 16 * (2 * Real.pi) ^ (4 : ℝ) * Real.Gamma 9
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero K)
  have hQ1 : 1 ≤ Q := by
    dsimp [Q]
    have hne : discr K ≠ 0 := NumberField.discr_ne_zero K
    by_cases hpos : 0 ≤ discr K
    · rw [abs_of_nonneg (show 0 ≤ ((discr K : ℤ) : ℝ) by exact_mod_cast hpos)]
      have h : (1 : ℤ) ≤ discr K := by omega
      exact_mod_cast h
    · rw [abs_of_neg (show ((discr K : ℤ) : ℝ) < 0 by exact_mod_cast (lt_of_not_ge hpos))]
      have h : (1 : ℤ) ≤ -discr K := by omega
      exact_mod_cast h
  have hr₁ : 0 ≤ r₁ := by positivity
  have hr₂ : 0 ≤ r₂ := by positivity
  have hRconst : 0 < C₁ := by positivity
  have hCconst : 0 < C₂ := by positivity
  let t : ℝ := |s.im|
  have ht0 : 0 ≤ t := abs_nonneg _
  have hs2lo : -3 ≤ (s / 2).re := by simp; linarith
  have hs2hi : (s / 2).re ≤ 4 := by simp; linarith
  have hslo : -3 ≤ s.re := by linarith
  have hGammaR :
      ‖(Complex.Gammaℝ s)⁻¹‖ ≤ C₁ * Real.exp (Real.pi * (4 + t)) := by
    rw [gammaR_inv_formula, norm_mul]
    have hbase : ‖(Real.pi : ℂ) ^ (s / 2)‖ = Real.pi ^ (s / 2).re :=
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos (s / 2)
    rw [hbase]
    have hre : (s / 2).re ≤ 2 := by simp; linarith
    have hpi1 : 1 ≤ Real.pi := by nlinarith [Real.pi_gt_three]
    have hpow : Real.pi ^ (s / 2).re ≤ Real.pi ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpi1 hre
    have himDiv : (s / 2).im = s.im / 2 := by simp
    have himHalf : |(s / 2).im| = |s.im| / 2 := by
      rw [himDiv, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have htHalf : 1 / 2 ≤ |(s / 2).im| := by
      rw [himHalf]
      nlinarith [ht]
    have hgamma := norm_inv_Gamma_on_strip hs2lo hs2hi htHalf
    calc
      Real.pi ^ (s / 2).re * ‖(Complex.Gamma (s / 2))⁻¹‖ ≤
          Real.pi ^ (2 : ℝ) * (16 * Real.Gamma 9 * Real.exp (Real.pi * (4 + |(s / 2).im|))) := by
        exact mul_le_mul hpow hgamma (norm_nonneg _) (by positivity)
      _ ≤ C₁ * Real.exp (Real.pi * (4 + t)) := by
        dsimp [C₁, t]
        have him : |(s / 2).im| ≤ t := by
          rw [himHalf]
          dsimp [t]
          nlinarith [abs_nonneg s.im]
        have he : Real.exp (Real.pi * (4 + |(s / 2).im|)) ≤
            Real.exp (Real.pi * (4 + t)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr him)]
        have hgamma9 : 0 < Real.Gamma 9 :=
          Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 9)
        have hpi2 : 0 ≤ Real.pi ^ (2 : ℝ) :=
          Real.rpow_nonneg Real.pi_pos.le _
        have hgammaFactor : 0 ≤ 16 * Real.Gamma 9 :=
          mul_nonneg (by norm_num) hgamma9.le
        calc
          Real.pi ^ (2 : ℝ) * (16 * Real.Gamma 9 *
              Real.exp (Real.pi * (4 + |(s / 2).im|))) ≤
            Real.pi ^ (2 : ℝ) * (16 * Real.Gamma 9 *
              Real.exp (Real.pi * (4 + t))) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left he hgammaFactor) hpi2
          _ = C₁ * Real.exp (Real.pi * (4 + t)) := by
            dsimp [C₁]
            ring
  have hGammaC :
      ‖(Complex.Gammaℂ s)⁻¹‖ ≤ C₂ * Real.exp (Real.pi * (4 + t)) := by
    rw [gammaC_inv_formula, norm_mul, norm_mul]
    have hpbase0 : 0 < 2 * Real.pi := by positivity
    have hcastBase : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
      push_cast
      ring
    have hbase : ‖(2 * Real.pi : ℂ) ^ s‖ = (2 * Real.pi) ^ s.re := by
      rw [hcastBase]
      exact Complex.norm_cpow_eq_rpow_re_of_pos hpbase0 s
    norm_num
    rw [hbase]
    have hpbase : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hpow : (2 * Real.pi) ^ s.re ≤ (2 * Real.pi) ^ (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpbase hhi
    have htHalf : 1 / 2 ≤ |s.im| := by linarith
    have hgamma := norm_inv_Gamma_on_strip hslo hhi htHalf
    have hgamma' : ‖Complex.Gamma s‖⁻¹ ≤
      16 * Real.Gamma 9 * Real.exp (Real.pi * (4 + t)) := by
      simpa only [norm_inv] using hgamma
    have hinner : (2 * Real.pi) ^ s.re * ‖Complex.Gamma s‖⁻¹ ≤
      (2 * Real.pi) ^ (4 : ℝ) * (16 * Real.Gamma 9 * Real.exp (Real.pi * (4 + t))) := by
      exact mul_le_mul hpow hgamma' (by positivity) (by positivity)
    have hhalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
    calc
      (1 / 2 : ℝ) * (2 * Real.pi) ^ s.re * ‖Complex.Gamma s‖⁻¹ =
          (1 / 2 : ℝ) * ((2 * Real.pi) ^ s.re * ‖Complex.Gamma s‖⁻¹) := by ring
      _ ≤ 1 * ((2 * Real.pi) ^ s.re * ‖Complex.Gamma s‖⁻¹) := by
        exact mul_le_mul_of_nonneg_right hhalf (by positivity)
      _ ≤ 1 * ((2 * Real.pi) ^ (4 : ℝ) *
          (16 * Real.Gamma 9 * Real.exp (Real.pi * (4 + t)))) := by
        exact mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = C₂ * Real.exp (Real.pi * (4 + t)) := by simp [C₂]; ring
  have hQnorm :
      ‖((Q : ℝ) : ℂ) ^ (-s / 2)‖ ≤ Q := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQpos]
    have hexp : (-s / 2).re ≤ 1 := by simp; linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hQ1 hexp
  have hRpow : ‖(Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K‖ ≤
      (C₁ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrRealPlaces K := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hGammaR _
  have hCpow : ‖(Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K‖ ≤
      (C₂ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hGammaC _
  have hconstants : Q * C₁ ^ NumberField.InfinitePlace.nrRealPlaces K *
      C₂ ^ NumberField.InfinitePlace.nrComplexPlaces K ≤
      Real.exp (Q + C₁ * r₁ + C₂ * r₂) := by
        have hQ : Q ≤ Real.exp Q := by nlinarith [Real.add_one_le_exp Q]
        have hR : C₁ ^ NumberField.InfinitePlace.nrRealPlaces K ≤
            Real.exp (C₁ * r₁) := by
          calc C₁ ^ NumberField.InfinitePlace.nrRealPlaces K ≤
              (Real.exp C₁) ^ NumberField.InfinitePlace.nrRealPlaces K := by
                gcongr
                nlinarith [Real.add_one_le_exp C₁]
            _ = Real.exp (C₁ * r₁) := by
              rw [← Real.exp_nat_mul]
              simp [r₁]
              ring
        have hC : C₂ ^ NumberField.InfinitePlace.nrComplexPlaces K ≤
            Real.exp (C₂ * r₂) := by
          calc C₂ ^ NumberField.InfinitePlace.nrComplexPlaces K ≤
              (Real.exp C₂) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
                gcongr
                nlinarith [Real.add_one_le_exp C₂]
            _ = Real.exp (C₂ * r₂) := by
              rw [← Real.exp_nat_mul]
              simp [r₂]
              ring
        calc
          Q * C₁ ^ NumberField.InfinitePlace.nrRealPlaces K *
              C₂ ^ NumberField.InfinitePlace.nrComplexPlaces K ≤
            Real.exp Q * Real.exp (C₁ * r₁) * Real.exp (C₂ * r₂) := by
              gcongr
          _ = Real.exp (Q + C₁ * r₁ + C₂ * r₂) := by rw [← Real.exp_add, ← Real.exp_add]
  have hnorm : ‖invDedekindPrefactor K s‖ ≤
      Q * (C₁ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrRealPlaces K *
        (C₂ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
    dsimp [invDedekindPrefactor]
    rw [norm_mul, norm_mul]
    have hgammaProduct :
        ‖(Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K‖ *
          ‖(Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K‖ ≤
        (C₁ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrRealPlaces K *
          (C₂ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrComplexPlaces K :=
      mul_le_mul hRpow hCpow (norm_nonneg _) (by positivity)
    simpa [mul_assoc] using
      mul_le_mul hQnorm hgammaProduct (by positivity) (by positivity)
  have hRexp : (Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrRealPlaces K =
        Real.exp (Real.pi * (4 + t) * r₁) := by
          rw [← Real.exp_nat_mul]
          simp [r₁]
          ring
  have hCexp : (Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrComplexPlaces K =
      Real.exp (Real.pi * (4 + t) * r₂) := by
        rw [← Real.exp_nat_mul]
        simp [r₂]
        ring
  have hcombine :
      (C₁ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrRealPlaces K *
        (C₂ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrComplexPlaces K =
        C₁ ^ NumberField.InfinitePlace.nrRealPlaces K *
          C₂ ^ NumberField.InfinitePlace.nrComplexPlaces K *
            Real.exp (Real.pi * (4 + t) * (r₁ + r₂)) := by
      simp only [mul_pow, hRexp, hCexp]
      calc
        C₁ ^ NumberField.InfinitePlace.nrRealPlaces K *
            Real.exp (Real.pi * (4 + t) * r₁) *
            (C₂ ^ NumberField.InfinitePlace.nrComplexPlaces K *
              Real.exp (Real.pi * (4 + t) * r₂)) =
          (C₁ ^ NumberField.InfinitePlace.nrRealPlaces K *
            C₂ ^ NumberField.InfinitePlace.nrComplexPlaces K) *
              (Real.exp (Real.pi * (4 + t) * r₁) *
                Real.exp (Real.pi * (4 + t) * r₂)) := by ring_nf
        _ = C₁ ^ NumberField.InfinitePlace.nrRealPlaces K *
              C₂ ^ NumberField.InfinitePlace.nrComplexPlaces K *
              Real.exp (Real.pi * (4 + t) * (r₁ + r₂)) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
  have hR : 0 ≤ r₁ + r₂ := add_nonneg hr₁ hr₂
  have hπR : 0 ≤ Real.pi * (r₁ + r₂) := mul_nonneg Real.pi_pos.le hR
  have hMge : Real.pi * (r₁ + r₂) ≤ invPrefactorHeightConstant K := by
      unfold invPrefactorHeightConstant
      dsimp [Q, r₁, r₂, C₁, C₂]
      have hQnonneg : 0 ≤ Q := abs_nonneg _
      have hC₁r₁ : 0 ≤ C₁ * r₁ := mul_nonneg hRconst.le hr₁
      have hC₂r₂ : 0 ≤ C₂ * r₂ := mul_nonneg hCconst.le hr₂
      nlinarith [mul_nonneg Real.pi_pos.le hR]
  have hprod : 0 ≤
      (invPrefactorHeightConstant K - Real.pi * (r₁ + r₂)) * |s.im| :=
        mul_nonneg (sub_nonneg.mpr hMge) (abs_nonneg _)
  have hgap : invPrefactorHeightConstant K * (1 + |s.im|) -
      (Q + C₁ * r₁ + C₂ * r₂ +
        Real.pi * (4 + |s.im|) * (r₁ + r₂)) =
      1 + Real.pi * (r₁ + r₂) +
        (invPrefactorHeightConstant K - Real.pi * (r₁ + r₂)) * |s.im| := by
          unfold invPrefactorHeightConstant
          dsimp [Q, r₁, r₂, C₁, C₂]
          ring
  have hExp : Q + C₁ * r₁ + C₂ * r₂ +
      Real.pi * (4 + |s.im|) * (r₁ + r₂) ≤
      invPrefactorHeightConstant K * (1 + |s.im|) := by
        rw [← sub_nonneg, hgap]
        positivity
  have hmiddle :
      Q * (C₁ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrRealPlaces K *
        (C₂ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrComplexPlaces K ≤
      Real.exp (Q + C₁ * r₁ + C₂ * r₂ + Real.pi * (4 + t) * (r₁ + r₂)) := by
    calc
      Q * (C₁ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrRealPlaces K *
          (C₂ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrComplexPlaces K =
        Q * ((C₁ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrRealPlaces K *
          (C₂ * Real.exp (Real.pi * (4 + t))) ^ NumberField.InfinitePlace.nrComplexPlaces K) := by ring
      _ = Q * (C₁ ^ NumberField.InfinitePlace.nrRealPlaces K *
          C₂ ^ NumberField.InfinitePlace.nrComplexPlaces K *
            Real.exp (Real.pi * (4 + t) * (r₁ + r₂))) := by rw [hcombine]
      _ = (Q * C₁ ^ NumberField.InfinitePlace.nrRealPlaces K *
          C₂ ^ NumberField.InfinitePlace.nrComplexPlaces K) *
            Real.exp (Real.pi * (4 + t) * (r₁ + r₂)) := by ring
      _ ≤ Real.exp (Q + C₁ * r₁ + C₂ * r₂) *
          Real.exp (Real.pi * (4 + t) * (r₁ + r₂)) :=
        mul_le_mul_of_nonneg_right hconstants (Real.exp_pos _).le
      _ = Real.exp (Q + C₁ * r₁ + C₂ * r₂ + Real.pi * (4 + t) * (r₁ + r₂)) := by
        rw [← Real.exp_add]
  exact le_trans hnorm (le_trans hmiddle (Real.exp_le_exp.mpr hExp))

private theorem invPrefactorHeightConstant_pos (K : Type*) [Field K] [NumberField K] :
    0 < invPrefactorHeightConstant K := by
  unfold invPrefactorHeightConstant
  have hG : 0 < Real.Gamma 9 := Real.Gamma_pos_of_pos (by norm_num)
  positivity

private theorem exists_invDedekindPrefactor_norm_bound (K : Type*) [Field K]
    [NumberField K] :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 4 →
      1 ≤ |s.im| →
        ‖invDedekindPrefactor K s‖ ≤ Real.exp (M * (1 + |s.im|)) :=
  ⟨invPrefactorHeightConstant K, invPrefactorHeightConstant_pos K,
    fun s hlo hhi ht => invDedekindPrefactor_norm_bound K hlo hhi ht⟩

private theorem completed_prefactor_left_ratio_bound (K : Type*) [Field K]
    [NumberField K] {s : ℂ} (hsre : s.re = -1 / 4) :
    ‖ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) * invDedekindPrefactor K s‖ ≤
      |(discr K : ℝ)| ^ ((3 : ℝ) / 4) *
        (ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant (1 / 4)) ^
          NumberField.InfinitePlace.nrRealPlaces K *
        (ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant (1 / 4)) ^
          NumberField.InfinitePlace.nrComplexPlaces K *
        (2 + |s.im|) ^ Module.finrank ℚ K := by
  let Q : ℝ := |(discr K : ℝ)|
  let D : ℂ := (Q : ℂ)
  let δ : ℝ := 1 / 4
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero K)
  have hD : D ≠ 0 := Complex.ofReal_ne_zero.mpr hQpos.ne'
  have hsform : s = (-δ : ℂ) + s.im * Complex.I := by
    apply Complex.ext
    · norm_num [δ, hsre]
    · simp
  have hDpow : D ^ ((1 - s) / 2) * D ^ (-s / 2) = D ^ (1 / 2 - s) := by
    rw [← Complex.cpow_add _ _ hD]
    congr 1
    ring
  have hDnorm : ‖D ^ (1 / 2 - s)‖ = Q ^ ((3 : ℝ) / 4) := by
    rw [show D = (Q : ℂ) by rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hQpos]
    have hre : (1 / 2 - s).re = (3 : ℝ) / 4 := by
      simp [hsre]
      norm_num
    rw [hre]
  have hRratio :
      ‖Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s‖ ≤
        ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant δ *
          (2 + |s.im|) := by
    have hratioEq : Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s =
        Complex.Gammaℝ (1 - ((-δ : ℂ) + s.im * Complex.I)) /
          Complex.Gammaℝ ((-δ : ℂ) + s.im * Complex.I) := by
      exact congrArg₂ (fun a b : ℂ => a / b)
        (congrArg (fun z : ℂ => Complex.Gammaℝ (1 - z)) hsform)
        (congrArg Complex.Gammaℝ hsform)
    calc
      ‖Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s‖ =
          ‖Complex.Gammaℝ (1 - ((-δ : ℂ) + s.im * Complex.I)) /
            Complex.Gammaℝ ((-δ : ℂ) + s.im * Complex.I)‖ := congrArg norm hratioEq
      _ ≤ ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant δ *
          (2 + |s.im|) := by
        simpa [δ] using ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaR_left_ratio_bound
          δ s.im (by norm_num [δ]) (by norm_num [δ])
  have hCratio :
      ‖Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s‖ ≤
        ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant δ *
          (2 + |s.im|) ^ 2 := by
    have hratioEq : Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s =
        Complex.Gammaℂ (1 - ((-δ : ℂ) + s.im * Complex.I)) /
          Complex.Gammaℂ ((-δ : ℂ) + s.im * Complex.I) := by
      exact congrArg₂ (fun a b : ℂ => a / b)
        (congrArg (fun z : ℂ => Complex.Gammaℂ (1 - z)) hsform)
        (congrArg Complex.Gammaℂ hsform)
    calc
      ‖Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s‖ =
          ‖Complex.Gammaℂ (1 - ((-δ : ℂ) + s.im * Complex.I)) /
            Complex.Gammaℂ ((-δ : ℂ) + s.im * Complex.I)‖ := congrArg norm hratioEq
      _ ≤ ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant δ *
          (2 + |s.im|) ^ 2 := by
        simpa [δ] using ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaC_left_ratio_bound
          δ s.im (by norm_num [δ]) (by norm_num [δ])
  have hRfactor :
      Complex.Gammaℝ (1 - s) ^ NumberField.InfinitePlace.nrRealPlaces K *
        (Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K =
      (Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s) ^
        NumberField.InfinitePlace.nrRealPlaces K := by
    calc
      Complex.Gammaℝ (1 - s) ^ NumberField.InfinitePlace.nrRealPlaces K *
          (Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K =
        (Complex.Gammaℝ (1 - s) * (Complex.Gammaℝ s)⁻¹) ^
          NumberField.InfinitePlace.nrRealPlaces K := by rw [mul_pow]
      _ = _ := by rw [div_eq_mul_inv]
  have hCfactor :
      Complex.Gammaℂ (1 - s) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        (Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K =
      (Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s) ^
        NumberField.InfinitePlace.nrComplexPlaces K := by
    calc
      Complex.Gammaℂ (1 - s) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          (Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K =
        (Complex.Gammaℂ (1 - s) * (Complex.Gammaℂ s)⁻¹) ^
          NumberField.InfinitePlace.nrComplexPlaces K := by rw [mul_pow]
      _ = _ := by rw [div_eq_mul_inv]
  have hfactor :
      ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) * invDedekindPrefactor K s =
        D ^ (1 / 2 - s) *
          ((Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s) ^
              NumberField.InfinitePlace.nrRealPlaces K *
            (Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s) ^
              NumberField.InfinitePlace.nrComplexPlaces K) := by
    rw [ArtinPrimitiveRoots.Hecke.dedekindPrefactor, invDedekindPrefactor]
    change (D ^ ((1 - s) / 2) *
        (Complex.Gammaℝ (1 - s) ^ NumberField.InfinitePlace.nrRealPlaces K *
          Complex.Gammaℂ (1 - s) ^ NumberField.InfinitePlace.nrComplexPlaces K)) *
      (D ^ (-s / 2) *
        ((Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
          (Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K)) = _
    calc
      (D ^ ((1 - s) / 2) *
          (Complex.Gammaℝ (1 - s) ^ NumberField.InfinitePlace.nrRealPlaces K *
            Complex.Gammaℂ (1 - s) ^ NumberField.InfinitePlace.nrComplexPlaces K)) *
        (D ^ (-s / 2) *
          ((Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
            (Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K)) =
        (D ^ ((1 - s) / 2) * D ^ (-s / 2)) *
          ((Complex.Gammaℝ (1 - s) ^ NumberField.InfinitePlace.nrRealPlaces K *
              (Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K) *
            (Complex.Gammaℂ (1 - s) ^ NumberField.InfinitePlace.nrComplexPlaces K *
              (Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K)) := by ring
      _ = _ := by rw [hDpow, hRfactor, hCfactor]
  have hplaces : NumberField.InfinitePlace.nrRealPlaces K +
      2 * NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ K :=
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hRpow :
      ‖(Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s) ^ NumberField.InfinitePlace.nrRealPlaces K‖ ≤
        (ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant δ *
          (2 + |s.im|)) ^ NumberField.InfinitePlace.nrRealPlaces K := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hRratio _
  have hCpow :
      ‖(Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s) ^ NumberField.InfinitePlace.nrComplexPlaces K‖ ≤
        (ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant δ *
          (2 + |s.im|) ^ 2) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hCratio _
  have hnorm :
      ‖ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) * invDedekindPrefactor K s‖ =
        Q ^ ((3 : ℝ) / 4) *
          (‖(Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s) ^
              NumberField.InfinitePlace.nrRealPlaces K‖ *
            ‖(Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s) ^
              NumberField.InfinitePlace.nrComplexPlaces K‖) := by
    rw [hfactor, norm_mul, hDnorm, norm_mul, norm_pow, norm_pow]
  have hbound :
      Q ^ ((3 : ℝ) / 4) *
        (‖(Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s) ^
            NumberField.InfinitePlace.nrRealPlaces K‖ *
          ‖(Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s) ^
            NumberField.InfinitePlace.nrComplexPlaces K‖) ≤
      Q ^ ((3 : ℝ) / 4) *
        ((ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant δ) ^
            NumberField.InfinitePlace.nrRealPlaces K *
          (ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant δ) ^
            NumberField.InfinitePlace.nrComplexPlaces K) *
          (2 + |s.im|) ^ Module.finrank ℚ K := by
    have hkr : 0 < ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant δ :=
      ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant_pos δ (by norm_num [δ])
        (by norm_num [δ])
    have hkc : 0 < ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant δ :=
      ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant_pos δ (by norm_num [δ])
        (by norm_num [δ])
    have hRupper : 0 ≤
        (ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant δ *
          (2 + |s.im|)) ^ NumberField.InfinitePlace.nrRealPlaces K :=
      pow_nonneg (mul_nonneg hkr.le (by positivity)) _
    have hRatioProduct := mul_le_mul hRpow hCpow (norm_nonneg _) hRupper
    calc
      _ ≤ Q ^ ((3 : ℝ) / 4) *
          ((ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant δ *
              (2 + |s.im|)) ^ NumberField.InfinitePlace.nrRealPlaces K *
            (ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant δ *
              (2 + |s.im|) ^ 2) ^ NumberField.InfinitePlace.nrComplexPlaces K) :=
        mul_le_mul_of_nonneg_left hRatioProduct (Real.rpow_nonneg hQpos.le _)
      _ = Q ^ ((3 : ℝ) / 4) *
          ((ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant δ) ^
              NumberField.InfinitePlace.nrRealPlaces K *
            (ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant δ) ^
              NumberField.InfinitePlace.nrComplexPlaces K) *
            ((2 + |s.im|) ^ NumberField.InfinitePlace.nrRealPlaces K *
              (2 + |s.im|) ^ (2 * NumberField.InfinitePlace.nrComplexPlaces K)) := by
                rw [mul_pow, mul_pow, ← pow_mul]
                ring
      _ = Q ^ ((3 : ℝ) / 4) *
          ((ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant δ) ^
              NumberField.InfinitePlace.nrRealPlaces K *
            (ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant δ) ^
              NumberField.InfinitePlace.nrComplexPlaces K) *
            (2 + |s.im|) ^ Module.finrank ℚ K := by
              rw [← pow_add, hplaces]
  rw [hnorm]
  simpa [Q, δ, mul_assoc] using hbound

private theorem norm_dedekindZeta_le_of_two_le_re (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖NumberField.dedekindZeta K s‖ ≤
      ∑' n : ℕ, ‖LSeries.term
        (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖ := by
  classical
  let f : ℕ → ℂ := fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)
  have hsum2 : LSeriesSummable f 2 := by
    have h := DedekindResidue.count_LSeriesSummable K (by norm_num : (1 : ℝ) < 2)
    have hfe : (fun n : ℕ =>
        ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) = f := by
      funext n
      rfl
    rw [hfe] at h
    exact_mod_cast h
  have hsummS : LSeriesSummable f s := hsum2.of_re_le_re (by simpa using hs)
  have hterm : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ ‖LSeries.term f 2 n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn0, ite_eq_right hn0,
      show ((2 : ℂ)).re = (2 : ℝ) by norm_num]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    gcongr
  calc
    ‖NumberField.dedekindZeta K s‖ = ‖∑' n : ℕ, LSeries.term f s n‖ := by
      rw [NumberField.dedekindZeta]
      rfl
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsummS.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term f 2 n‖ := hsummS.norm.tsum_le_tsum hterm hsum2.norm

private theorem completed_witness_eq_canonical (K : Type*) [Field K] [NumberField K]
    (ξ : ℂ → ℂ) (hξdiff : Differentiable ℂ ξ)
    (hξeq : ∀ s : ℂ, 1 < s.re →
      ξ s = s * (s - 1) * ArtinPrimitiveRoots.Hecke.dedekindPrefactor K s *
        dedekindZeta K s) :
    ∀ s : ℂ, ξ s = DedekindResidue.completedDedekindZetaEntire K s := by
  let ξ₀ : ℂ → ℂ := DedekindResidue.completedDedekindZetaEntire K
  have hξ₀diff : Differentiable ℂ ξ₀ := by
    simpa [ξ₀] using DedekindResidue.differentiable_completedDedekindZetaEntire K
  have hOpen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hEqOn : Set.EqOn ξ ξ₀ {z : ℂ | 1 < z.re} := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro he
      rw [he] at hz
      norm_num [Complex.zero_re] at hz
    have hz1 : z ≠ 1 := by
      intro he
      rw [he] at hz
      norm_num [Complex.one_re] at hz
    rw [hξeq z hz,
      show ξ₀ z = z * (z - 1) * ArtinPrimitiveRoots.Hecke.dedekindPrefactor K z *
          dedekindZeta K z by
        dsimp [ξ₀]
        rw [DedekindResidue.completedDedekindZetaEntire_eq K hz0 hz1,
          DedekindResidue.completedDedekindZeta_eq_of_one_lt_re K hz,
          ← ArtinPrimitiveRoots.Hecke.dedekindPrefactor_eq_completedZetaPrefactor K z]
        ring]
  have h2mem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have hAgree := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (𝕜 := ℂ) (f := ξ) (g := ξ₀)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hξdiff)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hξ₀diff)
    isPreconnected_univ (Set.mem_univ (2 : ℂ))
    (hEqOn.eventuallyEq_of_mem (hOpen.mem_nhds h2mem))
  intro s
  exact hAgree (Set.mem_univ s)

theorem exists_dedekind_simple_pole_poly_bound (K : Type*) [Field K]
    [NumberField K] :
    ∃ G0 : ℂ → ℂ, Differentiable ℂ G0 ∧
      (∀ s : ℂ, 1 < s.re → G0 s = (s - 1) * dedekindZeta K s) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 4 →
        ‖G0 s‖ ≤ C * (2 + |s.im|) ^ (Module.finrank ℚ K + 2 : ℕ) := by
  classical
  obtain ⟨G0, hG0diff, hG0eq, _⟩ :=
    ArtinPrimitiveRoots.Hecke.dedekindZeta_simple_pole_continuation K
  obtain ⟨ξ, hξdiff, hξeq, hξFE, _⟩ := ArtinPrimitiveRoots.Hecke.dedekind_completed K
  have hξCanonical := completed_witness_eq_canonical K ξ hξdiff hξeq
  have hFEcanonical : ∀ s : ℂ,
      DedekindResidue.completedDedekindZetaEntire K (1 - s) =
        DedekindResidue.completedDedekindZetaEntire K s := by
    intro s
    calc
      DedekindResidue.completedDedekindZetaEntire K (1 - s) = ξ (1 - s) :=
        (hξCanonical (1 - s)).symm
      _ = ξ s := hξFE s
      _ = DedekindResidue.completedDedekindZetaEntire K s := hξCanonical s
  let a : ℝ := -1 / 4
  let b : ℝ := 4
  let d : ℕ := Module.finrank ℚ K
  let N : ℕ := d + 2
  let H : ℂ → ℂ := fun z => G0 z / (z + 2) ^ N
  let Zleft : ℝ := (riemannZeta (5 / 4 : ℝ)).re ^ d
  let Zright : ℝ := (riemannZeta (4 : ℝ)).re ^ d
  let Q : ℝ := |(discr K : ℝ)|
  let kR : ℝ := ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant (1 / 4)
  let kC : ℝ := ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant (1 / 4)
  let D : ℝ := Q ^ ((3 : ℝ) / 4) *
    kR ^ NumberField.InfinitePlace.nrRealPlaces K *
    kC ^ NumberField.InfinitePlace.nrComplexPlaces K
  obtain ⟨Bstrip, hBstrip, hXiStrip⟩ :=
    DedekindBounds.exists_completedDedekindZetaEntire_strip_bound K a b (by norm_num [a, b])
  obtain ⟨M, hMpos, hInv⟩ := exists_invDedekindPrefactor_norm_bound K
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero K)
  have hZleft : 0 < Zleft := by
    dsimp [Zleft]
    exact pow_pos (riemannZeta_re_pos_of_one_lt (by norm_num : (1 : ℝ) < 5 / 4)) _
  have hZright : 0 < Zright := by
    dsimp [Zright]
    exact pow_pos (riemannZeta_re_pos_of_one_lt (by norm_num : (1 : ℝ) < 4)) _
  have hkR : 0 < kR := by
    dsimp [kR]
    exact ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaRLeftConstant_pos
      (1 / 4) (by norm_num) (by norm_num)
  have hkC : 0 < kC := by
    dsimp [kC]
    exact ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant_pos
      (1 / 4) (by norm_num) (by norm_num)
  have hDnonneg : 0 ≤ D := by positivity
  have hBstripNonneg : 0 ≤ Bstrip := hBstrip
  let Bdouble : ℝ := Bstrip + 3 * M + 12
  have hBdoublePos : 0 < Bdouble := by
    dsimp [Bdouble]
    positivity
  let Cleft : ℝ := 6 ^ N * D * Zleft
  let Cright : ℝ := 6 ^ N * Zright
  let Cboundary : ℝ := 1 + Cleft + Cright
  have hCboundary : 0 < Cboundary := by
    dsimp [Cboundary, Cleft, Cright]
    positivity
  have hG0id {s : ℂ} (hs0 : s ≠ 0) :
      G0 s = DedekindResidue.completedDedekindZetaEntire K s *
        invDedekindPrefactor K s / s :=
    simplePole_mul_s_eq_completed K G0 hG0diff hG0eq s hs0
  have hG0leftFormula {s : ℂ} (hsre : s.re = a) (hs0 : s ≠ 0) :
      G0 s = (s - 1) *
        (ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) * invDedekindPrefactor K s) *
          dedekindZeta K (1 - s) := by
    have h1s : 1 < (1 - s).re := by
      rw [show (1 - s).re = 1 - s.re by simp, hsre]
      norm_num [a]
    calc
      G0 s = DedekindResidue.completedDedekindZetaEntire K s *
          invDedekindPrefactor K s / s := hG0id hs0
      _ = DedekindResidue.completedDedekindZetaEntire K (1 - s) *
          invDedekindPrefactor K s / s := by rw [← hFEcanonical s]
      _ = (s - 1) *
          (ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) * invDedekindPrefactor K s) *
            dedekindZeta K (1 - s) := by
          have hu0 : 1 - s ≠ 0 := by
            intro h
            have hre : 1 - s.re = 0 := by simpa using congrArg Complex.re h
            rw [hsre] at hre
            norm_num [a] at hre
          have hu1 : 1 - s ≠ 1 := by
            intro h
            have hre : 1 - s.re = 1 := by simpa using congrArg Complex.re h
            rw [hsre] at hre
            norm_num [a] at hre
          rw [DedekindResidue.completedDedekindZetaEntire_eq K hu0 hu1,
            DedekindResidue.completedDedekindZeta_eq_of_one_lt_re K h1s,
            ← ArtinPrimitiveRoots.Hecke.dedekindPrefactor_eq_completedZetaPrefactor K (1 - s)]
          field_simp [hs0]
          ring
  have hLeftFormula (s : ℂ) (hsre : s.re = a) (ht : 1 ≤ |s.im|) :
      ‖G0 s‖ ≤ D * Zleft * (5 + |s.im|) ^ (d + 1) := by
    have hs0 : s ≠ 0 := by
      intro hs0
      have him := congrArg Complex.im hs0
      have hz : s.im = 0 := by simpa using him
      rw [hz] at ht
      norm_num at ht
    have hxiHi : s.re ≤ b := by rw [hsre]; norm_num [a, b]
    have hξbound := hXiStrip s (le_of_eq hsre.symm) hxiHi
    have hPbound := hInv s (le_of_eq hsre.symm) hxiHi ht
    have hnormSminus : ‖s - 1‖ ≤ 5 + |s.im| := by
      calc
        ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |s.re - 1| + |s.im| := by simp
        _ ≤ 5 + |s.im| := by dsimp [a] at hsre; rw [hsre]; norm_num
    have hPref := completed_prefactor_left_ratio_bound K hsre
    have hPref' :
        ‖ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) * invDedekindPrefactor K s‖ ≤
          D * (5 + |s.im|) ^ d := by
      have hbase : 2 + |s.im| ≤ 5 + |s.im| := by linarith
      calc
        _ ≤ D * (2 + |s.im|) ^ d := by simpa [D, Q, kR, kC, d] using hPref
        _ ≤ D * (5 + |s.im|) ^ d := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hbase d) hDnonneg
    have hζ : ‖dedekindZeta K (1 - s)‖ ≤ Zleft := by
      have hz := (ArtinPrimitiveRoots.Hecke.dedekindZeta_norm_bounds K
        (by norm_num : (1 : ℝ) < 5 / 4) (-s.im)).2
      have harg : 1 - s = (5 / 4 : ℂ) + (-s.im) * Complex.I := by
        apply Complex.ext
        · simp [Complex.sub_re, hsre]
          norm_num [a]
        · simp
      rw [harg]
      simpa [Zleft, d] using hz
    have hprod :
        ‖(s - 1) *
          (ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) * invDedekindPrefactor K s) *
            dedekindZeta K (1 - s)‖ ≤
          (5 + |s.im|) * (D * (5 + |s.im|) ^ d) * Zleft := by
      rw [norm_mul, norm_mul]
      have hinner :
          ‖ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) * invDedekindPrefactor K s‖ *
            ‖dedekindZeta K (1 - s)‖ ≤ (D * (5 + |s.im|) ^ d) * Zleft :=
        mul_le_mul hPref' hζ (norm_nonneg _) (by positivity)
      have hscaled :
          ‖s - 1‖ *
              (‖ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) * invDedekindPrefactor K s‖ *
                ‖dedekindZeta K (1 - s)‖) ≤
            (5 + |s.im|) * ((D * (5 + |s.im|) ^ d) * Zleft) :=
        mul_le_mul hnormSminus hinner (by positivity) (by positivity)
      calc
        ‖s - 1‖ * ‖ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) *
            invDedekindPrefactor K s‖ * ‖dedekindZeta K (1 - s)‖ =
          ‖s - 1‖ * (‖ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) *
            invDedekindPrefactor K s‖ * ‖dedekindZeta K (1 - s)‖) := by ring_nf
        _ ≤ (5 + |s.im|) * ((D * (5 + |s.im|) ^ d) * Zleft) :=
          hscaled
        _ = (5 + |s.im|) * (D * (5 + |s.im|) ^ d) * Zleft := by ring
    calc
      ‖G0 s‖ =
          ‖(s - 1) *
            (ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - s) * invDedekindPrefactor K s) *
              dedekindZeta K (1 - s)‖ := by
        rw [hG0leftFormula hsre hs0]
      _ ≤ (5 + |s.im|) * (D * (5 + |s.im|) ^ d) * Zleft := hprod
      _ = D * Zleft * (5 + |s.im|) ^ (d + 1) := by
        rw [pow_succ]
        ring

  let S : Set ℂ := Complex.re ⁻¹' Set.Ioo a b
  have hClosed : IsClosed (Complex.re ⁻¹' Set.Icc a b) :=
    isClosed_Icc.preimage Complex.continuous_re
  have hClosure : closure S ⊆ Complex.re ⁻¹' Set.Icc a b := by
    apply closure_minimal
    · intro z hz
      exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
    · exact hClosed
  have hDenOne {z : ℂ} (hz : a ≤ z.re) : 1 ≤ ‖z + 2‖ := by
    have hre : 1 ≤ (z + 2).re := by simp; dsimp [a] at hz; linarith
    have habs : 1 ≤ |(z + 2).re| := hre.trans (le_abs_self _)
    exact habs.trans (Complex.abs_re_le_norm _)
  have hDenNe {z : ℂ} (hz : z ∈ closure S) : (z + 2) ^ N ≠ 0 := by
    have hzIcc := hClosure hz
    have hnorm : 1 ≤ ‖z + 2‖ := hDenOne hzIcc.1
    have hbase : z + 2 ≠ 0 := by
      intro hzero
      rw [hzero] at hnorm
      norm_num at hnorm
    exact pow_ne_zero _ hbase
  have hDenDiff : DifferentiableOn ℂ (fun z : ℂ => (z + 2) ^ N) (closure S) := by
    fun_prop
  have hHdiff : DifferentiableOn ℂ H (closure S) := by
    dsimp [H]
    exact hG0diff.differentiableOn.div hDenDiff (fun z hz => hDenNe hz)
  have hfd : DiffContOnCl ℂ H S :=
    ⟨hHdiff.mono subset_closure, hHdiff.continuousOn⟩
  have hTevent : ∀ᶠ z : ℂ in
      Filter.comap (fun z : ℂ => |z.im|) atTop ⊓ Filter.principal S,
        1 ≤ |z.im| := by
    have htend : Tendsto (fun z : ℂ => |z.im|)
        (Filter.comap (fun z : ℂ => |z.im|) atTop) atTop := tendsto_comap
    exact (htend.eventually_ge_atTop 1).filter_mono inf_le_left
  have hSevent : ∀ᶠ z : ℂ in
      Filter.comap (fun z : ℂ => |z.im|) atTop ⊓ Filter.principal S, z ∈ S := by
    have hself : ∀ᶠ z : ℂ in Filter.principal S, z ∈ S := by simp
    exact hself.filter_mono inf_le_right
  let Bdouble : ℝ := Bstrip + 3 * M + 12
  have hBdoublePos : 0 < Bdouble := by dsimp [Bdouble]; positivity
  have hBigO : ∃ c < Real.pi / (b - a), ∃ B : ℝ,
      H =O[Filter.comap (fun z : ℂ => |z.im|) atTop ⊓ Filter.principal S]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1 / 2, ?_, Bdouble, ?_⟩
    · have hwidth : 0 < b - a := by dsimp [a, b]; norm_num
      have hpi : (1 / 2 : ℝ) * (b - a) < Real.pi := by
        dsimp [a, b]
        nlinarith [Real.pi_gt_three]
      exact (lt_div_iff₀ hwidth).2 hpi
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hTevent, hSevent] with z ht hzS
    have hzlo : a ≤ z.re := le_of_lt hzS.1
    have hzhi : z.re ≤ b := le_of_lt hzS.2
    have hs0 : z ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      have hz : z.im = 0 := by simpa using him
      rw [hz] at ht
      norm_num at ht
    have hxi := hXiStrip z hzlo hzhi
    have hInv' := hInv z hzlo hzhi ht
    have hReAbs : |z.re| ≤ 4 := by
      rw [abs_le]
      constructor <;> dsimp [a, b] at hzlo hzhi <;> linarith
    have hNorm : ‖z‖ ≤ 4 + |z.im| :=
      (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hReAbs le_rfl)
    have hG0 : ‖G0 z‖ ≤
        Bstrip * (1 + ‖z‖) ^ 2 * Real.exp (M * (1 + |z.im|)) := by
      rw [hG0id hs0, norm_div, norm_mul]
      calc
        ‖DedekindResidue.completedDedekindZetaEntire K z‖ *
            ‖invDedekindPrefactor K z‖ / ‖z‖ ≤
          ‖DedekindResidue.completedDedekindZetaEntire K z‖ *
            ‖invDedekindPrefactor K z‖ :=
          div_le_self (by positivity) (by linarith [Complex.abs_im_le_norm z])
        _ ≤ Bstrip * (1 + ‖z‖) ^ 2 * Real.exp (M * (1 + |z.im|)) := by
          exact mul_le_mul hxi hInv' (by positivity) (by positivity)
    have hDenOne : 1 ≤ ‖(z + 2) ^ N‖ := by
      rw [norm_pow]
      exact one_le_pow₀ (hDenOne hzlo)
    have hHleG : ‖H z‖ ≤ ‖G0 z‖ := by
      dsimp [H]
      rw [norm_div]
      exact div_le_self (norm_nonneg _) hDenOne
    have htPlus : |z.im| + 5 ≤ Real.exp (|z.im| + 4) := by
      have h := Real.add_one_le_exp (|z.im| + 4)
      linarith
    have hPoly : (1 + ‖z‖) ^ 2 ≤ Real.exp (2 * (|z.im| + 4)) := by
      calc
        (1 + ‖z‖) ^ 2 ≤ (|z.im| + 5) ^ 2 := by
          have hbase : 1 + ‖z‖ ≤ |z.im| + 5 := by linarith [hNorm]
          exact pow_le_pow_left₀ (by positivity) hbase 2
        _ ≤ (Real.exp (|z.im| + 4)) ^ 2 := by gcongr
        _ = Real.exp (2 * (|z.im| + 4)) := by
          rw [← Real.exp_nat_mul]
          norm_num
    have hBstripExp : Bstrip ≤ Real.exp Bstrip := by
      have h := Real.add_one_le_exp Bstrip
      linarith
    have hExpBound :
        Bstrip * (1 + ‖z‖) ^ 2 * Real.exp (M * (1 + |z.im|)) ≤
          Real.exp (Bdouble * Real.exp ((1 / 2 : ℝ) * |z.im|)) := by
      have ht0 : 0 ≤ |z.im| := abs_nonneg _
      have hExpHalf : 1 + |z.im| / 2 ≤ Real.exp (|z.im| / 2) := by
        simpa [add_comm] using Real.add_one_le_exp (|z.im| / 2)
      have hlinear : Bstrip + 2 * (|z.im| + 4) + M * (1 + |z.im|) ≤
          Bdouble * Real.exp (|z.im| / 2) := by
        calc
          Bstrip + 2 * (|z.im| + 4) + M * (1 + |z.im|) ≤
              Bdouble * (1 + |z.im| / 2) := by
                dsimp [Bdouble]
                nlinarith [hBstrip, hMpos.le, ht0]
          _ ≤ Bdouble * Real.exp (|z.im| / 2) :=
            mul_le_mul_of_nonneg_left hExpHalf hBdoublePos.le
      calc
        Bstrip * (1 + ‖z‖) ^ 2 * Real.exp (M * (1 + |z.im|)) ≤
            Real.exp Bstrip * Real.exp (2 * (|z.im| + 4)) *
              Real.exp (M * (1 + |z.im|)) := by
                gcongr
        _ = Real.exp (Bstrip + 2 * (|z.im| + 4) + M * (1 + |z.im|)) := by
          rw [← Real.exp_add, ← Real.exp_add]
        _ ≤ Real.exp (Bdouble * Real.exp (|z.im| / 2)) :=
          Real.exp_le_exp.mpr hlinear
        _ = Real.exp (Bdouble * Real.exp ((1 / 2 : ℝ) * |z.im|)) := by
          congr 2 <;> ring
    calc
      ‖H z‖ ≤ ‖G0 z‖ := hHleG
      _ ≤ Bstrip * (1 + ‖z‖) ^ 2 * Real.exp (M * (1 + |z.im|)) := hG0
      _ ≤ Real.exp (Bdouble * Real.exp ((1 / 2 : ℝ) * |z.im|)) := by
        simpa [div_eq_mul_inv] using hExpBound
      _ = 1 * ‖Real.exp (Bdouble * Real.exp ((1 / 2 : ℝ) * |z.im|))‖ := by
        simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  let Zright : ℝ := (riemannZeta (4 : ℝ)).re ^ d
  let Zleft : ℝ := (riemannZeta (5 / 4 : ℝ)).re ^ d
  have hZright : 0 < Zright := by
    dsimp [Zright]
    exact pow_pos (riemannZeta_re_pos_of_one_lt (by norm_num : (1 : ℝ) < 4)) _
  have hZleft : 0 < Zleft := by
    dsimp [Zleft]
    exact pow_pos (riemannZeta_re_pos_of_one_lt (by norm_num : (1 : ℝ) < 5 / 4)) _
  have hDpos : 0 < D := by positivity
  let Cboundary : ℝ := 1 + 6 ^ N * (D * Zleft + Zright)
  have hCboundary : 0 < Cboundary := by dsimp [Cboundary]; positivity
  have hDenOneStrip {z : ℂ} (hz : a ≤ z.re) : 1 ≤ ‖z + 2‖ := by
    have hre : 1 ≤ (z + 2).re := by simp; dsimp [a] at hz; linarith
    exact (hre.trans (le_abs_self _)).trans (Complex.abs_re_le_norm _)
  have hHden {z : ℂ} (hz : a ≤ z.re) : 5 + |z.im| ≤ 6 * ‖z + 2‖ := by
    have him := Complex.abs_im_le_norm (z + 2)
    have him' : |z.im| ≤ ‖z + 2‖ := by simpa using him
    have hre := hDenOneStrip hz
    nlinarith
  have hHpowDen {z : ℂ} (hz : a ≤ z.re) :
      (5 + |z.im|) ^ N ≤ 6 ^ N * ‖(z + 2) ^ N‖ := by
    calc
      (5 + |z.im|) ^ N ≤ (6 * ‖z + 2‖) ^ N :=
        pow_le_pow_left₀ (by positivity) (hHden hz) _
      _ = 6 ^ N * ‖(z + 2) ^ N‖ := by rw [mul_pow, norm_pow]
  have hNormNormalized {z : ℂ} (hz : a ≤ z.re)
      (C : ℝ) (hC : 0 ≤ C) (hG : ‖G0 z‖ ≤ C * (5 + |z.im|) ^ N) :
      ‖H z‖ ≤ C * 6 ^ N := by
    have hden : 0 < ‖(z + 2) ^ N‖ := by
      rw [norm_pow]
      exact pow_pos (lt_of_lt_of_le zero_lt_one (hDenOneStrip hz)) _
    have hnum : ‖G0 z‖ ≤ C * 6 ^ N * ‖(z + 2) ^ N‖ := by
      calc
        ‖G0 z‖ ≤ C * (5 + |z.im|) ^ N := hG
        _ ≤ C * (6 ^ N * ‖(z + 2) ^ N‖) :=
          mul_le_mul_of_nonneg_left (hHpowDen hz) hC
        _ = C * 6 ^ N * ‖(z + 2) ^ N‖ := by ring
    dsimp [H]
    rw [norm_div]
    exact (div_le_iff₀ hden).2 hnum
  have hBoundaryLeft : ∀ z : ℂ, z.re = a → ‖H z‖ ≤ Cboundary := by
    intro z hzre
    let T : ℝ := 5 + |z.im|
    have hz0 : z ≠ 0 := by
      intro hz
      have hre : z.re = 0 := by simpa using congrArg Complex.re hz
      rw [hzre] at hre
      norm_num [a] at hre
    have hFormula := hG0leftFormula (by simpa [a] using hzre) hz0
    have hPref := completed_prefactor_left_ratio_bound K (by simpa [a] using hzre)
    have hPref' :
        ‖ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - z) * invDedekindPrefactor K z‖ ≤
          D * T ^ d := by
      calc
        _ ≤ D * (2 + |z.im|) ^ d := by simpa [D, Q, kR, kC, d] using hPref
        _ ≤ D * T ^ d := by
          dsimp [T]
          gcongr
          linarith
    have hZ : ‖dedekindZeta K (1 - z)‖ ≤ Zleft := by
      have hZ := (ArtinPrimitiveRoots.Hecke.dedekindZeta_norm_bounds K
        (by norm_num : (1 : ℝ) < 5 / 4) (-z.im)).2
      have hArg : 1 - z = (5 / 4 : ℂ) + (-z.im) * Complex.I := by
        apply Complex.ext
        · simp [Complex.sub_re, hzre]
          norm_num [a]
        · simp
      rw [hArg]
      simpa [Zleft, d] using hZ
    have hminus : ‖z - 1‖ ≤ T := by
      calc
        ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |z.re - 1| + |z.im| := by simp
        _ ≤ T := by dsimp [T]; rw [hzre]; norm_num
    have hG : ‖G0 z‖ ≤ (D * Zleft) * T ^ (d + 1) := by
      have hinner :
          ‖ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - z) * invDedekindPrefactor K z‖ *
            ‖dedekindZeta K (1 - z)‖ ≤ (D * T ^ d) * Zleft :=
        mul_le_mul hPref' hZ (norm_nonneg _) (by positivity)
      calc
        ‖G0 z‖ =
            ‖(z - 1) *
              (ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - z) * invDedekindPrefactor K z) *
                dedekindZeta K (1 - z)‖ := by rw [hFormula]
        _ = ‖z - 1‖ *
            (‖ArtinPrimitiveRoots.Hecke.dedekindPrefactor K (1 - z) * invDedekindPrefactor K z‖ *
              ‖dedekindZeta K (1 - z)‖) := by rw [norm_mul, norm_mul]; ring
        _ ≤ T * ((D * T ^ d) * Zleft) :=
          mul_le_mul hminus hinner (by positivity) (by positivity)
        _ = (D * Zleft) * T ^ (d + 1) := by rw [pow_succ]; ring
    have hHone : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg z.im]
    have hpow : T ^ (d + 1) ≤ T ^ N := by
      apply pow_le_pow_right₀ hHone
      dsimp [N, d]
      omega
    have hG' : ‖G0 z‖ ≤ (D * Zleft) * T ^ N := by
      calc ‖G0 z‖ ≤ (D * Zleft) * T ^ (d + 1) := hG
        _ ≤ (D * Zleft) * T ^ N :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
    have hzlo : a ≤ z.re := by rw [hzre]
    have hnormH := hNormNormalized hzlo (D * Zleft) (by positivity) hG'
    calc
      ‖H z‖ ≤ D * Zleft * 6 ^ N := hnormH
      _ ≤ Cboundary := by
        dsimp [Cboundary]
        have hpos : 0 ≤ 6 ^ N * Zright := by positivity
        nlinarith [hpos]
  have hBoundaryRight : ∀ z : ℂ, z.re = b → ‖H z‖ ≤ Cboundary := by
    intro z hzre
    let T : ℝ := 5 + |z.im|
    have hZ : ‖dedekindZeta K z‖ ≤ Zright := by
      have hZ := (ArtinPrimitiveRoots.Hecke.dedekindZeta_norm_bounds K
        (by norm_num : (1 : ℝ) < 4) z.im).2
      have hArg : z = (4 : ℂ) + z.im * Complex.I := by
        apply Complex.ext
        · rw [hzre]
          norm_num [b]
        · simp
      rw [hArg]
      simpa [Zright, d] using hZ
    have hzright : 1 < z.re := by rw [hzre]; norm_num [b]
    have hG0eq' := hG0eq z hzright
    have hminus : ‖z - 1‖ ≤ T := by
      calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |z.re - 1| + |z.im| := by simp
        _ ≤ T := by dsimp [T]; rw [hzre]; norm_num
    have hG : ‖G0 z‖ ≤ Zright * T ^ N := by
      rw [hG0eq', norm_mul]
      have hmain : ‖z - 1‖ * ‖dedekindZeta K z‖ ≤ T * Zright :=
        mul_le_mul hminus hZ (norm_nonneg _) (by positivity)
      calc
        ‖z - 1‖ * ‖dedekindZeta K z‖ ≤ T * Zright := hmain
        _ ≤ Zright * T ^ N := by
          have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg z.im]
          have hN : 1 ≤ N := by dsimp [N]; omega
          have hTpow : T ≤ T ^ N := by
            simpa using (pow_le_pow_right₀ hT hN)
          calc
            T * Zright ≤ T ^ N * Zright :=
              mul_le_mul_of_nonneg_right hTpow hZright.le
            _ = Zright * T ^ N := by ring
    have hzlo : a ≤ z.re := by rw [hzre]; dsimp [a, b]; norm_num
    have hnormH := hNormNormalized hzlo Zright (le_of_lt hZright) hG
    calc
      ‖H z‖ ≤ Zright * 6 ^ N := hnormH
      _ ≤ Cboundary := by
        dsimp [Cboundary]
        have hpos : 0 ≤ 6 ^ N * D * Zleft := by positivity
        nlinarith [hpos]

  have hPL (z : ℂ) (hzlo : a ≤ z.re) (hzhi : z.re ≤ b) : ‖H z‖ ≤ Cboundary :=
    PhragmenLindelof.vertical_strip hfd hBigO hBoundaryLeft hBoundaryRight hzlo hzhi
  refine ⟨G0, hG0diff, hG0eq, Cboundary * 3 ^ N, ?_, ?_⟩
  · positivity
  · intro s hs0 hs4
    have hPLs := hPL s (by dsimp [a]; linarith [hs0]) (by dsimp [b]; exact hs4)
    have hsbound : ‖s + 2‖ ≤ 3 * (2 + |s.im|) := by
      calc
        ‖s + 2‖ ≤ |(s + 2).re| + |(s + 2).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 6 + |s.im| := by
          have hRe : |(s + 2).re| ≤ 6 := by
            rw [abs_le]
            constructor <;> simp <;> linarith [hs0, hs4]
          have hIm : |(s + 2).im| = |s.im| := by simp
          rw [hIm]
          linarith
        _ ≤ 3 * (2 + |s.im|) := by nlinarith [abs_nonneg s.im]
    have hEq : G0 s = H s * (s + 2) ^ N := by
      dsimp [H]
      have hden : s + 2 ≠ 0 := by
        intro hz
        have hre : (s + 2).re = 0 := by simpa using congrArg Complex.re hz
        have hre' : s.re + 2 = 0 := by simpa using hre
        linarith [hs0]
      field_simp [hden]
    calc
      ‖G0 s‖ = ‖H s * (s + 2) ^ N‖ := by rw [hEq]
      _ = ‖H s‖ * ‖(s + 2) ^ N‖ := norm_mul _ _
      _ ≤ Cboundary * (3 * (2 + |s.im|)) ^ N := by
        have hdenpow : ‖(s + 2) ^ N‖ ≤ (3 * (2 + |s.im|)) ^ N := by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) hsbound _
        exact mul_le_mul hPLs hdenpow (norm_nonneg _) (by positivity)
      _ = Cboundary * 3 ^ N * (2 + |s.im|) ^ N := by rw [mul_pow]; ring

end ArtinPrimitiveRoots.Proofs.HK_MISC_P
