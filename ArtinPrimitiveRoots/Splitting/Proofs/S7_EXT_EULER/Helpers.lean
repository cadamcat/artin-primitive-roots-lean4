import ArtinPrimitiveRoots.Splitting.Defs
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false

open scoped NumberField BigOperators Topology
open NumberField IsDedekindDomain Complex Filter

noncomputable section

namespace ArtinPrimitiveRoots.Splitting.S7ExtEuler

variable {K : Type*} [Field K] [NumberField K]

/-- The local prime-power series is geometric on the Euler half-plane. -/
lemma prime_power_hasSum (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun j : ℕ =>
      (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-((j + 1 : ℕ) : ℂ) * s))
      ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) /
        ((Ideal.absNorm v.asIdeal : ℂ) ^ s - 1)) := by
  have hv := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hr : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hv) (by linarith)
  have hp : (Ideal.absNorm v.asIdeal : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl v.natCast_absNorm_ne_zero)
  have hd := v.absNorm_cpow_sub_one_ne_zero (s := s) (by linarith)
  have hsum := (hasSum_geometric_of_norm_lt_one hr).mul_left
    ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
  have heq : ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ =
      (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) /
        ((Ideal.absNorm v.asIdeal : ℂ) ^ s - 1) := by
    rw [Complex.cpow_neg]
    field_simp [hp, hd]
  rw [← heq]
  refine hsum.congr_fun fun j => ?_
  rw [show -((j + 1 : ℕ) : ℂ) * s = ((j + 1 : ℕ) : ℂ) * (-s) by ring,
    Complex.cpow_nat_mul, pow_succ]
  ring

/-- Differentiate the locally uniformly convergent Dedekind Euler product. -/
lemma euler_logderiv_hasSum (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun v : HeightOneSpectrum (𝓞 K) =>
      (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) /
        ((Ideal.absNorm v.asIdeal : ℂ) ^ s - 1))
      (-logDeriv (dedekindZeta K) s) := by
  classical
  let σ : ℝ := (1 + s.re) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσs : σ < s.re := by dsimp [σ]; linarith
  let U : Set ℂ := {z | σ < z.re}
  let F : HeightOneSpectrum (𝓞 K) → ℂ → ℂ :=
    fun v z => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-z))⁻¹
  let q : ℝ := (2 : ℝ) ^ (-σ)
  have hq : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hqpos : 0 < 1 - q := sub_pos.mpr hq
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hnorm_le (v : HeightOneSpectrum (𝓞 K)) {z : ℂ} (hz : z ∈ U) :
      ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-z)‖ ≤
        ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-(σ : ℂ))‖ :=
    (v.norm_absNorm_cpow_neg_lt (by simpa [U] using hz)).le
  have hnorm_q (v : HeightOneSpectrum (𝓞 K)) :
      ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-(σ : ℂ))‖ ≤ q := by
    have hv := NumberField.HeightOneSpectrum.one_lt_absNorm v
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num)
      (by exact_mod_cast (show 2 ≤ Ideal.absNorm v.asIdeal by omega)) (by linarith)
  have hden (v : HeightOneSpectrum (𝓞 K)) {z : ℂ} (hz : z ∈ U) :
      1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-z) ≠ 0 := by
    intro he
    have hlt := (hnorm_le v hz).trans_lt ((hnorm_q v).trans_lt hq)
    rw [sub_eq_zero] at he
    rw [← he] at hlt
    norm_num at hlt
  have hdiff (v : HeightOneSpectrum (𝓞 K)) {z : ℂ} (hz : z ∈ U) :
      DifferentiableAt ℂ (F v) z :=
    ((((hasDerivAt_neg z).const_cpow (Or.inl v.natCast_absNorm_ne_zero)).const_sub 1).inv
      (hden v hz)).differentiableAt
  have hideals : Summable (TauCeti.idealTerm K
      (1 : TauCeti.MultiplicativeIdealWeight K).toIdealArithmeticFunction (σ : ℂ)) := by
    rw [TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one]
    exact TauCeti.summable_idealTerm_one_iff.mpr (by simpa using hσ)
  have hprimes : Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-(σ : ℂ))) := by
    refine (TauCeti.MultiplicativeIdealWeight.summable_div_of_summable_idealTerm
      (1 : TauCeti.MultiplicativeIdealWeight K) hideals).congr fun v => ?_
    rw [TauCeti.MultiplicativeIdealWeight.one_apply, ite_eq_right v.ne_bot,
      Complex.cpow_neg, one_div]
  have hmajorant : Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-(σ : ℂ))‖ / (1 - q)) :=
    hprimes.norm.div_const (1 - q)
  have hbound (v : HeightOneSpectrum (𝓞 K)) {z : ℂ} (hz : z ∈ U) :
      ‖F v z - 1‖ ≤ ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-(σ : ℂ))‖ / (1 - q) := by
    have hsub : 1 - q ≤ ‖1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-z)‖ := by
      calc
        1 - q ≤ 1 - ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-z)‖ :=
          sub_le_sub_left ((hnorm_le v hz).trans (hnorm_q v)) 1
        _ ≤ ‖1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-z)‖ := by
          simpa using norm_sub_norm_le (1 : ℂ)
            ((Ideal.absNorm v.asIdeal : ℂ) ^ (-z))
    have heq : F v z - 1 = (Ideal.absNorm v.asIdeal : ℂ) ^ (-z) /
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-z)) := by
      dsimp [F]
      field_simp [hden v hz]
      ring
    rw [heq, norm_div]
    calc
      _ ≤ ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-z)‖ / (1 - q) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hqpos hsub
      _ ≤ _ := (div_le_div_iff_of_pos_right hqpos).mpr (hnorm_le v hz)
  have hone : TendstoLocallyUniformlyOn
      (fun t : Finset (HeightOneSpectrum (𝓞 K)) => fun z =>
        ∏ v ∈ t, (1 + (F v z - 1)))
      (fun z => ∏' v : HeightOneSpectrum (𝓞 K), (1 + (F v z - 1))) atTop U :=
    Summable.hasProdLocallyUniformlyOn_one_add (f := fun v z => F v z - 1)
      hU hmajorant (.of_forall fun v z hz => hbound v hz)
      (fun v z hz => ((hdiff v hz).sub_const 1).continuousAt.continuousWithinAt)
  have hlu : TendstoLocallyUniformlyOn
      (fun t : Finset (HeightOneSpectrum (𝓞 K)) => fun z => ∏ v ∈ t, F v z)
      (dedekindZeta K) atTop U :=
    (hone.congr fun t z _ => Finset.prod_congr rfl fun v _ => by ring).congr_right
      (fun z hz => (tprod_congr fun v => (by ring : 1 + (F v z - 1) = F v z)).trans
        (TauCeti.dedekindZeta_eulerProduct_hasProd (hσ.trans hz)).tprod_eq)
  have hsU : s ∈ U := hσs
  have hsum : HasSum (fun v : HeightOneSpectrum (𝓞 K) => logDeriv (F v) s)
      (logDeriv (dedekindZeta K) s) := by
    have key := Complex.logDeriv_tendsto hU hsU hlu
      (.of_forall fun t => DifferentiableOn.fun_finsetProd
        fun v _ z hz => (hdiff v hz).differentiableWithinAt)
      (TauCeti.dedekindZeta_ne_zero_of_one_lt_re hs)
    rw [HasSum]
    exact key.congr fun t => logDeriv_fun_prod
      (fun v _ => inv_ne_zero (hden v hsU)) (fun v _ => hdiff v hsU)
  have hlocal (v : HeightOneSpectrum (𝓞 K)) :
      logDeriv (F v) s = -((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) /
        ((Ideal.absNorm v.asIdeal : ℂ) ^ s - 1)) := by
    have hd := (((hasDerivAt_neg s).const_cpow
      (Or.inl v.natCast_absNorm_ne_zero)).const_sub 1).differentiableAt
    have hi := logDeriv_fun_zpow hd (-1 : ℤ)
    simp only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hi
    rw [show logDeriv (F v) s =
      logDeriv (fun z : ℂ => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-z))⁻¹) s from rfl,
      hi, v.logDeriv_one_sub_absNorm_cpow_neg (by linarith), ← Complex.natCast_log]
  exact hsum.neg.congr_fun fun v => by rw [hlocal v, neg_neg]

/-- D1 identifies the chosen continuation and its derivative on the Euler half-plane. -/
lemma sharp_logderiv_eq (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaLogDerivative K s = -logDeriv (dedekindZeta K) s := by
  have heq (z : ℂ) (hz : 1 < z.re) : dedekindZetaSharp K z = dedekindZeta K z := by
    have hz0 : z ≠ 0 := by
      intro he
      rw [he] at hz
      norm_num at hz
    have hz1 : z ≠ 1 := by
      intro he
      rw [he] at hz
      norm_num at hz
    have hzpos : 0 < z.re := by linarith
    have hD : ((|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast abs_ne_zero.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
    have hR := Complex.Gammaℝ_ne_zero_of_re_pos hzpos
    have hC : Complex.Gammaℂ z ≠ 0 := by
      have hbase : (2 * Real.pi : ℂ) ≠ 0 :=
        mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      rw [Complex.Gammaℂ_def]
      exact mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)))
        (Complex.Gamma_ne_zero_of_re_pos hzpos)
    have hP : ArtinPrimitiveRoots.Hecke.dedekindPrefactor K z ≠ 0 := by
      unfold ArtinPrimitiveRoots.Hecke.dedekindPrefactor
      exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hD))
        (mul_ne_zero (pow_ne_zero _ hR) (pow_ne_zero _ hC))
    have hden : z * (z - 1) * ArtinPrimitiveRoots.Hecke.dedekindPrefactor K z ≠ 0 :=
      mul_ne_zero (mul_ne_zero hz0 (sub_ne_zero.mpr hz1)) hP
    have hξ := (Classical.choose_spec (ArtinPrimitiveRoots.Hecke.dedekind_completed K)).2.1 z hz
    change dedekindXi K z = _ at hξ
    rw [dedekindZetaSharp, hξ, mul_div_cancel_left₀ _ hden]
  have hU : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hnhds : dedekindZetaSharp K =ᶠ[𝓝 s] dedekindZeta K := by
    filter_upwards [hU.mem_nhds hs] with z hz using heq z hz
  have hlog := (logDeriv_congr_nhds hnhds).eq_of_nhds
  simpa only [dedekindZetaLogDerivative, logDeriv_apply, neg_div] using congrArg Neg.neg hlog

end ArtinPrimitiveRoots.Splitting.S7ExtEuler
