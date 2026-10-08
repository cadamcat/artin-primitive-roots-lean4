import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNClassField
import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNAgree

/-!
# QS-ANALYTIC, RN-R: root number `+1` for a quadratic ray character

Let `E/K` be the quadratic class field of `ψ` (RN-C).  Grouping the Euler product of `ζ_E` over
the places of `K` (RN-E) gives, for `Re s > 1`,
`ζ_E(s) P(s) = ζ_K(s) L(s, ψ) Q(s)` with finite products `P, Q` over the places of the modulus.
With the completed Dedekind functions `ξ_E`, `ξ_K` (`Hecke.dedekind_completed`) and
`Λ = hkCompleted ψ` (RN-A) this reads `ξ_E P = ξ_K Λ D^{s/2} Q` for a positive constant `D`,
an identity of entire functions.  The functional equations of `ξ_E`, `ξ_K` and
`Λ(s) = W Λ(1-s)` (HK-FE export, `ψ⁻¹ = ψ`) give
`ξ_K(s) Λ(1-s) (W D^{s/2} Q(s) P(1-s) - D^{(1-s)/2} Q(1-s) P(s)) = 0`; the first factors do not
vanish near a large real `s`, so the bracket vanishes identically, and at `s = 1/2` it is
`(W - 1) D^{1/4} Q(1/2) P(1/2)` with `P(1/2) Q(1/2) ≠ 0`.  Hence `W = 1`.
No conductor-discriminant formula and no information at the places of the modulus is needed.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.A2

/-- RN-R1: `1 - ε n^{-s} ≠ 0` for `n > 1`, `Re s > 0` and `‖ε‖ ≤ 1`. -/
theorem qsa_one_sub_mul_cpow_ne_zero {n : ℕ} (hn : 1 < n) {s : ℂ} (hs : 0 < s.re) {ε : ℂ}
    (hε : ‖ε‖ ≤ 1) : 1 - ε * ((n : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : ε * ((n : ℕ) : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hlt : (n : ℝ) ^ (-s).re < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn)
    simp only [Complex.neg_re]
    linarith
  have hnorm : ‖ε * ((n : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    calc ‖ε‖ * (n : ℝ) ^ (-s).re ≤ 1 * (n : ℝ) ^ (-s).re := by
          gcongr
      _ < 1 := by rw [one_mul]; exact hlt
  rw [h1, norm_one] at hnorm
  exact lt_irrefl _ hnorm

/-- RN-R2: the Dedekind prefactor does not vanish on `Re s > 0`. -/
theorem qsa_dedekindPrefactor_ne_zero (F : Type*) [Field F] [NumberField F] {s : ℂ}
    (hs : 0 < s.re) : Hecke.dedekindPrefactor F s ≠ 0 := by
  unfold Hecke.dedekindPrefactor
  have hd : ((|(discr F : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero F
    exact_mod_cast abs_ne_zero.mpr this
  have hG : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs)
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => by
      have : (2 : ℂ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      exact this h.1
  refine mul_ne_zero ?_ (mul_ne_zero (pow_ne_zero _ (Complex.Gammaℝ_ne_zero_of_re_pos hs))
    (pow_ne_zero _ hG))
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => hd h.1

/-- RN-R3: a finite product of factors `1 - n^{-s}`, `n` a norm of a finite place, is entire. -/
theorem qsa_differentiable_one_sub_cpow (n : ℕ) (hn : n ≠ 0) :
    Differentiable ℂ (fun z : ℂ => 1 - ((n : ℕ) : ℂ) ^ (-z)) := by
  have hN : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
  intro z
  exact (differentiableAt_const _).sub ((differentiableAt_id.neg).const_cpow (Or.inl hN))

variable {K : Type} [Field K] [NumberField K]

/-- RN-R: a primitive nontrivial quadratic ray character has root number `+1`. -/
theorem qsa_hkCompleted_one_sub [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) (hsq : ψ⁻¹ = ψ) (hp : Hecke.HKPrimitive ψ)
    (s : ℂ) : Hecke.hkCompleted ψ (1 - s) = Hecke.hkCompleted ψ s := by
  classical
  obtain ⟨E, _, _, _, hr1, hr2, hloc⟩ := qsa_quadratic_class_field ψ hψ hsq
  obtain ⟨-, -, -, -, hΛd, -, -, -, W, hW1, hFE⟩ :=
    Hecke.hk_fe_export_to_ext_hecke_continuation ψ hψ hp
  rw [hsq] at hFE
  suffices hW : W = 1 by
    rw [hFE s, hW, one_mul]
  set Λ := Hecke.hkCompleted ψ with hΛdef
  obtain ⟨ξK, hξKd, hξKeq, hξKfe, -⟩ := Hecke.dedekind_completed K
  obtain ⟨ξE, hξEd, hξEeq, hξEfe, -⟩ := Hecke.dedekind_completed E
  set S := m.finitePart.support with hSdef
  let P : ℂ → ℂ := fun z => ∏ v ∈ S, ∏ w ∈ (qsa_below_fiber_finite K E v).toFinset,
    (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z))
  let Q : ℂ → ℂ := fun z => ∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z))
  set dK : ℝ := |(discr K : ℝ)| with hdKdef
  set dE : ℝ := |(discr E : ℝ)| with hdEdef
  set Nm : ℝ := (Hecke.modulusNorm m : ℝ) with hNmdef
  set D : ℝ := dE / (dK * dK * Nm) with hDdef
  let c : ℂ → ℂ := fun z => ((D : ℝ) : ℂ) ^ (z / 2)
  have hdK : 0 < dK := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hdE : 0 < dE := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero E)
  have hNm : 0 < Nm := by
    rw [hNmdef]
    exact_mod_cast Dictionary.HKDICTRay.modulusNorm_pos m
  have hD : 0 < D := by positivity
  have hD0 : ((D : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
  -- differentiability
  have hQd : Differentiable ℂ Q := by
    refine Differentiable.fun_finsetProd fun v _ => ?_
    exact qsa_differentiable_one_sub_cpow _
      (NumberField.HeightOneSpectrum.one_lt_absNorm v).ne_bot
  have hPd : Differentiable ℂ P := by
    refine Differentiable.fun_finsetProd fun v _ => ?_
    refine Differentiable.fun_finsetProd fun w _ => ?_
    exact qsa_differentiable_one_sub_cpow _
      (NumberField.HeightOneSpectrum.one_lt_absNorm w).ne_bot
  have hcd : Differentiable ℂ c := fun z =>
    (differentiableAt_id.div_const 2).const_cpow (Or.inl hD0)
  -- Step A: the Euler identity on `Re z > 1`
  have hEuler : ∀ z : ℂ, 1 < z.re →
      dedekindZeta E z * P z = dedekindZeta K z * Hecke.LSeriesRay ψ z * Q z := by
    intro z hz
    have hz0 : 0 < z.re := by linarith
    have hA := qsa_dedekindZeta_hasProd_fiber K E hz
    have hB := qsa_dedekindZeta_hasProd K hz
    have hC := Hecke.LSeriesRay_eulerProduct ψ hz
    let P' : HeightOneSpectrum (𝓞 K) → ℂ := fun v => if v ∈ S then
      ∏ w ∈ (qsa_below_fiber_finite K E v).toFinset,
        (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) else 1
    let Q' : HeightOneSpectrum (𝓞 K) → ℂ := fun v => if v ∈ S then
      (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) else 1
    have hP' : HasProd P' (P z) := by
      have heq : ∏ v ∈ S, P' v = P z :=
        Finset.prod_congr rfl (fun v hv => by simp only [P', if_pos hv])
      rw [← heq]
      exact hasProd_prod_of_ne_finset_one (fun v hv => by simp only [P', if_neg hv])
    have hQ' : HasProd Q' (Q z) := by
      have heq : ∏ v ∈ S, Q' v = Q z :=
        Finset.prod_congr rfl (fun v hv => by simp only [Q', if_pos hv])
      rw [← heq]
      exact hasProd_prod_of_ne_finset_one (fun v hv => by simp only [Q', if_neg hv])
    have h1 := hA.mul hP'
    have h2 := (hB.mul hC).mul hQ'
    have hfun : (fun v : HeightOneSpectrum (𝓞 K) =>
        (∏ w ∈ (qsa_below_fiber_finite K E v).toFinset,
          (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z))⁻¹) * P' v) =
        (fun v => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z))⁻¹ *
          (1 - Hecke.charValue ψ v.asIdeal * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z))⁻¹ *
            Q' v) := by
      funext v
      by_cases hv : v ∈ S
      · simp only [P', Q', if_pos hv]
        rw [Dictionary.charValue_eq_zero_of_mem_support ψ hv, zero_mul, sub_zero, inv_one,
          mul_one, ← Finset.prod_mul_distrib]
        have hv1 : (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) ≠ 0 := by
          simpa using qsa_one_sub_mul_cpow_ne_zero
            (NumberField.HeightOneSpectrum.one_lt_absNorm v) hz0 (ε := 1) (by simp)
        rw [inv_mul_cancel₀ hv1]
        refine Finset.prod_eq_one fun w _ => ?_
        have hw1 : (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) ≠ 0 := by
          simpa using qsa_one_sub_mul_cpow_ne_zero
            (NumberField.HeightOneSpectrum.one_lt_absNorm w) hz0 (ε := 1) (by simp)
        exact inv_mul_cancel₀ hw1
      · simp only [P', Q', if_neg hv, mul_one]
        exact hloc v hv z
    rw [hfun] at h1
    exact h1.unique h2
  -- Step B: the identity of entire functions
  have hcpow : ∀ z : ℂ, ((dE : ℝ) : ℂ) ^ (z / 2) =
      ((dK : ℝ) : ℂ) ^ (z / 2) * ((dK : ℝ) : ℂ) ^ (z / 2) * ((Nm : ℝ) : ℂ) ^ (z / 2) * c z := by
    intro z
    have hdE' : dE = dK * dK * Nm * D := by
      rw [hDdef]
      field_simp
    rw [hdE', Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) hD.le,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) hNm.le,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hdK.le hdK.le]
  have hF1d : Differentiable ℂ (fun z => ξE z * P z) := hξEd.mul hPd
  have hF2d : Differentiable ℂ (fun z => ξK z * Λ z * c z * Q z) :=
    ((hξKd.mul hΛd).mul hcd).mul hQd
  have hFre : ∀ z : ℂ, 1 < z.re → ξE z * P z = ξK z * Λ z * c z * Q z := by
    intro z hz
    have he := hEuler z hz
    rw [hξEeq z hz, hξKeq z hz, hΛdef, qsa_hkCompleted_eq_series ψ hψ hz,
      Hecke.dedekindPrefactor, Hecke.dedekindPrefactor, hr1, hr2,
      IsTotallyComplex.nrRealPlaces_eq_zero K, hcpow z]
    simp only [pow_zero, one_mul, two_mul, pow_add]
    linear_combination (z * (z - 1) * (((dK : ℝ) : ℂ) ^ (z / 2) * ((dK : ℝ) : ℂ) ^ (z / 2) *
      ((Nm : ℝ) : ℂ) ^ (z / 2) * c z) * (Complex.Gammaℂ z ^ InfinitePlace.nrComplexPlaces K *
        Complex.Gammaℂ z ^ InfinitePlace.nrComplexPlaces K)) * he
  have hF : ∀ z : ℂ, ξE z * P z = ξK z * Λ z * c z * Q z := by
    have hev : (fun z => ξE z * P z) =ᶠ[nhds (2 : ℂ)] (fun z => ξK z * Λ z * c z * Q z) := by
      have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
      exact hFre z hz
    have := AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hF1d.analyticAt z)
      (fun z _ => hF2d.analyticAt z) hev
    exact fun z => congrFun this z
  -- Step C: the functional equations
  let B : ℂ → ℂ := fun z => W * c z * Q z * P (1 - z) - c (1 - z) * Q (1 - z) * P z
  have hB : ∀ z : ℂ, (ξK z * Λ (1 - z)) * B z = 0 := by
    intro z
    have e1 := hF z
    have e2 := hF (1 - z)
    rw [hξEfe z, hξKfe z] at e2
    have e3 := hFE z
    simp only [B]
    linear_combination (-(ξK z * c z * Q z * P (1 - z))) * e3 - P (1 - z) * e1 + P z * e2
  -- Step D: the bracket vanishes identically
  have hΛ2 : Λ 2 ≠ 0 := by
    have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
    rw [hΛdef, qsa_hkCompleted_eq_series ψ hψ h2]
    refine mul_ne_zero (mul_ne_zero ?_ (qsa_dedekindPrefactor_ne_zero K (by norm_num)))
      (Hecke.norm_LSeriesRay_le ψ h2).2.1
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => (Complex.ofReal_ne_zero.mpr hNm.ne') h.1
  have hξK2 : ξK 2 ≠ 0 := by
    have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
    rw [hξKeq 2 h2]
    have hζ : dedekindZeta K 2 ≠ 0 := by
      rw [← Hecke.LSeriesRay_trivial_eq_dedekindZeta]
      exact (Hecke.norm_LSeriesRay_le _ h2).2.1
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by norm_num))
      (qsa_dedekindPrefactor_ne_zero K (by norm_num))) hζ
  have hH2 : ξK 2 * Λ (1 - 2) ≠ 0 := by
    refine mul_ne_zero hξK2 fun h => hΛ2 ?_
    rw [hFE 2, h, mul_zero]
  have hHc : Continuous (fun z => ξK z * Λ (1 - z)) :=
    hξKd.continuous.mul (hΛd.continuous.comp (continuous_const.sub continuous_id))
  have hBd : Differentiable ℂ B := by
    have h1 : Differentiable ℂ (fun z : ℂ => P (1 - z)) :=
      hPd.comp ((differentiable_const _).sub differentiable_id)
    have h2 : Differentiable ℂ (fun z : ℂ => c (1 - z)) :=
      hcd.comp ((differentiable_const _).sub differentiable_id)
    have h3 : Differentiable ℂ (fun z : ℂ => Q (1 - z)) :=
      hQd.comp ((differentiable_const _).sub differentiable_id)
    exact ((((differentiable_const W).mul hcd).mul hQd).mul h1).sub ((h2.mul h3).mul hPd)
  have hB0 : B = fun _ => 0 := by
    have hev : B =ᶠ[nhds (2 : ℂ)] (fun _ => 0) := by
      filter_upwards [hHc.continuousAt.eventually_ne hH2] with z hz
      exact (mul_eq_zero.mp (hB z)).resolve_left hz
    exact AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hBd.analyticAt z)
      (fun z _ => analyticAt_const) hev
  -- Step E: evaluate at `1/2`
  have hhalf := congrFun hB0 (1 / 2)
  have h12 : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
  simp only [B, h12] at hhalf
  have hre : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hc12 : c (1 / 2) ≠ 0 := by
    simp only [c]
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => hD0 h.1
  have hQ12 : Q (1 / 2) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun v _ => ?_
    simpa using qsa_one_sub_mul_cpow_ne_zero
      (NumberField.HeightOneSpectrum.one_lt_absNorm v) hre (ε := 1) (by simp)
  have hP12 : P (1 / 2) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun v _ => Finset.prod_ne_zero_iff.mpr fun w _ => ?_
    simpa using qsa_one_sub_mul_cpow_ne_zero
      (NumberField.HeightOneSpectrum.one_lt_absNorm w) hre (ε := 1) (by simp)
  have hprod : c (1 / 2) * Q (1 / 2) * P (1 / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc12 hQ12) hP12
  have : (W - 1) * (c (1 / 2) * Q (1 / 2) * P (1 / 2)) = 0 := by
    linear_combination hhalf
  have := (mul_eq_zero.mp this).resolve_right hprod
  linear_combination this

end ArtinPrimitiveRoots.A2
