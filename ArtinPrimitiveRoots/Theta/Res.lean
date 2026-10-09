import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Reduction
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.square_pairing_nontrivial
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.root_square_lift
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.root_square_commutator
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.root_invariant_genuine_zero
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_genuine
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.unitTorus_constant_of_nonzero_fourier_zero
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.totallyComplexMixedEquiv_embedding
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.mem_span_idealArchBasis
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.archimedean_trace_sum
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_pairing
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_ne_zero
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_coordinate_sum
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_fourier_character
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_period
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.unitTorus_lift_of_int_periodic
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTorus_normalized_integral
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTorus_fourierCoeff_eq
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTorus_constant_of_nonzero_fourier_zero
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_right_of_scalar_invariant
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_automorphic
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_ideal_period
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_arch_invariant_of_nonzero_coeff_zero
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_exterior_upper_invariant_of_arch_invariant
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_exterior_lower_invariant_of_upper_invariant
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.exists_exterior_finPlace
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.lagrangian_vector_selector
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.bigCell_normalized_intertwine
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.tame_lagrangian_vector_selector
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.theta_lambda_descent
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.theta_lambda_whittaker
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.thetaWhit_section_multilinear
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.thetaWhit_jacquet_factorization
import ArtinPrimitiveRoots.Hecke.Continuation
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_uniform_level_components
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_reconstruction
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_series_analytic
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_torus_charts
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_laurent_torus
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_theta_cont
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.theta_constantTerm
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.thetaWhit_equiv

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## P-RES -/

section Res

open MeasureTheory Filter Topology

variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- `ζ_F^{T0}(u) = ζ_F(u) Π_{v∈T0} (1 - q_v^{-u})` (Mathlib `NumberField.dedekindZeta`). -/
def zetaT0 (T0 : Finset (FinPlace F)) (u : ℂ) : ℂ :=
  NumberField.dedekindZeta F u * ∏ v ∈ T0, (1 - (qv v : ℂ) ^ (-u))

private theorem hasProd_div_of_ne_zero {ι : Type} (f g : ι → ℂ) (a b : ℂ)
    (hf : HasProd f a) (hg : HasProd g b) (hb : b ≠ 0) :
    HasProd (fun i => f i / g i) (a / b) := by
  change Tendsto (fun s : Finset ι => ∏ i ∈ s, f i) _ (𝓝 a) at hf
  change Tendsto (fun s : Finset ι => ∏ i ∈ s, g i) _ (𝓝 b) at hg
  change Tendsto (fun s : Finset ι => ∏ i ∈ s, f i / g i) _ (𝓝 (a / b))
  have h := hf.div hg hb
  exact h.congr' (Eventually.of_forall fun s => by simp [Finset.prod_div_distrib])

private theorem zetaT0_ne_zero_of_re_gt_one (T0 : Finset (FinPlace F)) {z : ℂ}
    (hz : 1 < z.re) : zetaT0 T0 z ≠ 0 := by
  let η : ClassFieldTheory.RayClassGroup (⟨0, ∅⟩ : ClassFieldTheory.RayClassModulus F) →* ℂˣ := 1
  have hL := (ArtinPrimitiveRoots.Hecke.norm_LSeriesRay_le (η := η) hz).2.1
  have hζ : NumberField.dedekindZeta F z ≠ 0 := by
    simpa [η, ArtinPrimitiveRoots.Hecke.LSeriesRay_trivial_eq_dedekindZeta] using hL
  apply mul_ne_zero hζ
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  have hq : 1 < qv v := by
    dsimp [qv]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hpowNorm : ‖(qv v : ℂ) ^ (-z)‖ < 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < qv v)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by simpa using (show -z.re < 0 by linarith))
  have hpow : (qv v : ℂ) ^ (-z) ≠ 1 := by
    intro heq
    rw [heq] at hpowNorm
    norm_num at hpowNorm
  exact sub_ne_zero.mpr hpow.symm

set_option maxHeartbeats 500000 in
/-- **res:zeta**: `Π_{v∉T0} c_v(s) = ζ_F^{T0}(6s)/ζ_F^{T0}(6s+1)` for `Re s > 1/6`. -/
theorem cprod_eq_zeta_ratio (T0 : Finset (FinPlace F)) (s : ℂ) (hs : 1 / 6 < s.re) :
    cprod T0 s = zetaT0 T0 (6 * s) / zetaT0 T0 (6 * s + 1) := by
  classical
  let m0 : ClassFieldTheory.RayClassModulus F := ⟨0, ∅⟩
  let η : ClassFieldTheory.RayClassGroup m0 →* ℂˣ := 1
  let u : ℂ := 6 * s
  let factor (z : ℂ) (v : FinPlace F) : ℂ := (1 - (qv v : ℂ) ^ (-z))⁻¹
  have hcop (v : FinPlace F) : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m0 v.asIdeal := by
    refine ⟨v.ne_bot, ?_⟩
    change ∀ w, w ∈ m0.finitePart.support →
      FractionalIdeal.count F w
        ((ArtinPrimitiveRoots.Hecke.idealUnit v.asIdeal v.ne_bot :
          ClassFieldTheory.NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
    intro w hw
    simp [m0] at hw
  have hchar : ∀ v : FinPlace F, ArtinPrimitiveRoots.Hecke.charValue η v.asIdeal = 1 := by
    intro v
    have hv := hcop v
    simp [ArtinPrimitiveRoots.Hecke.charValue, η, hv]
  have hfull (z : ℂ) (hz : 1 < z.re) :
      HasProd (fun v : FinPlace F => factor z v) (NumberField.dedekindZeta F z) := by
    have heuler := ArtinPrimitiveRoots.Hecke.LSeriesRay_eulerProduct (η := η) hz
    have hterms (v : FinPlace F) : factor z v =
        (1 - ArtinPrimitiveRoots.Hecke.charValue η v.asIdeal *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z))⁻¹ := by
      have hnorm : (qv v : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := by
        simp [qv]
      simp [factor, hchar v, hnorm]
    simpa [η, m0, ArtinPrimitiveRoots.Hecke.LSeriesRay_trivial_eq_dedekindZeta] using
      heuler.congr_fun hterms
  have hu : 1 < u.re := by
    have : u.re = 6 * s.re := by simp [u]
    rw [this]
    nlinarith
  have hu1 : 1 < (u + 1).re := by
    have : (u + 1).re = u.re + 1 := by simp
    rw [this]
    linarith
  have hpartial (z : ℂ) (hz : 1 < z.re) :
      HasProd (fun v : {v : FinPlace F // v ∉ T0} => factor z v.1) (zetaT0 T0 z) := by
    have hbase (v : FinPlace F) : (1 - (qv v : ℂ) ^ (-z)) ≠ 0 := by
      have hq : 1 < qv v := by
        dsimp [qv]
        exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hnorm : ‖(qv v : ℂ) ^ (-z)‖ < 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < qv v)]
        exact Real.rpow_lt_one_of_one_lt_of_neg hq (by simpa using
          (show -z.re < 0 by linarith))
      apply sub_ne_zero.mpr
      intro heq
      rw [← heq] at hnorm
      norm_num at hnorm
    let correction : FinPlace F → ℂ := fun v =>
      if v ∈ T0 then 1 - (qv v : ℂ) ^ (-z) else 1
    have hcorrection : HasProd correction (∏ v ∈ T0, (1 - (qv v : ℂ) ^ (-z))) := by
      have h := hasProd_prod_of_ne_finset_one (s := T0) (f := correction)
        (L := SummationFilter.unconditional (FinPlace F))
        (fun v hv => by simp [correction, hv])
      convert h using 1
      apply Finset.prod_congr rfl
      intro v hv
      simp [correction, hv]
    have h := (hfull z hz).mul hcorrection
    apply (hasProd_subtype_iff_mulIndicator
      (s := {v : FinPlace F | v ∉ T0}) (f := factor z)
      (a := zetaT0 T0 z)).mpr
    have heq : ∀ v : FinPlace F,
        ({v : FinPlace F | v ∉ T0}.mulIndicator (factor z)) v = factor z v * correction v := by
      intro v
      by_cases hv : v ∈ T0
      · simp [Set.mulIndicator, factor, correction, hv, hbase v]
      · simp [Set.mulIndicator, correction, hv]
    simpa [zetaT0] using h.congr_fun heq
  have hratio := hasProd_div_of_ne_zero _ _ _ _ (hpartial u hu) (hpartial (u + 1) hu1)
    (zetaT0_ne_zero_of_re_gt_one T0 hu1)
  have hlocal (v : FinPlace F) : factor u v / factor (u + 1) v = cv v s := by
    have hpow0 : (qv v : ℂ) ^ (-u) = (qv v : ℂ) ^ (-6 * s) := by
      congr 1
      dsimp [u]
      ring
    have hpow1 : (qv v : ℂ) ^ (-(u + 1)) = (qv v : ℂ) ^ (-1 - 6 * s) := by
      congr 1
      dsimp [u]
      ring
    simp only [factor, cv]
    rw [hpow0, hpow1]
    simp [div_eq_mul_inv, mul_comm]
  have hratio' := hratio.congr_fun (fun v => (hlocal v.1).symm)
  simpa [cprod] using hratio'.tprod_eq

/-- **res:pole**: `cprod` has a simple pole at `s0 = 1/6` with nonzero residue. -/
private def resModulus (T0 : Finset (FinPlace F)) : ClassFieldTheory.RayClassModulus F where
  finitePart := Finsupp.onFinset T0 (fun v => if v ∈ T0 then 1 else 0) (by
    intro v hv
    by_contra hvT
    simp [hvT] at hv)
  infinitePart := ∅

private theorem resModulus_support (T0 : Finset (FinPlace F)) :
    (resModulus T0).finitePart.support = T0 := by
  classical
  simp [resModulus, Finsupp.support_onFinset]

private theorem res_isCoprimeTo_prime_of_not_mem (m : ClassFieldTheory.RayClassModulus F)
    (v : FinPlace F) (hv : v ∉ m.finitePart.support) :
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m v.asIdeal := by
  refine ⟨v.ne_bot, ?_⟩
  change ∀ w, w ∈ m.finitePart.support →
    FractionalIdeal.count F w
      ((ArtinPrimitiveRoots.Hecke.idealUnit v.asIdeal v.ne_bot :
        ClassFieldTheory.NumberFieldFractionalIdealGroup F) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
  intro w hw
  have hwv : w ≠ v := by
    intro h
    exact hv (h ▸ hw)
  simpa [ArtinPrimitiveRoots.Hecke.idealUnit] using
    (FractionalIdeal.count_maximal_coprime F w (Ne.symm hwv))

private theorem res_charValue_trivial_prime_of_not_mem (m : ClassFieldTheory.RayClassModulus F)
    (v : FinPlace F) (hv : v ∉ m.finitePart.support) :
    ArtinPrimitiveRoots.Hecke.charValue
      (1 : ClassFieldTheory.RayClassGroup m →* ℂˣ) v.asIdeal = 1 := by
  have hcop := res_isCoprimeTo_prime_of_not_mem m v hv
  simp [ArtinPrimitiveRoots.Hecke.charValue, hcop]

private theorem resLSeries_eq_zetaT0 (T0 : Finset (FinPlace F)) (s : ℂ)
    (hs : 1 < s.re) :
    ArtinPrimitiveRoots.Hecke.LSeriesRay
      (1 : ClassFieldTheory.RayClassGroup (resModulus T0) →* ℂˣ) s = zetaT0 T0 s := by
  classical
  let m := resModulus T0
  let m0 : ClassFieldTheory.RayClassModulus F := ⟨0, ∅⟩
  let η : ClassFieldTheory.RayClassGroup m →* ℂˣ := 1
  let η0 : ClassFieldTheory.RayClassGroup m0 →* ℂˣ := 1
  have hsupp : m.finitePart.support = T0 := by
    simpa [m] using resModulus_support T0
  have hagree : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      ArtinPrimitiveRoots.Hecke.charValue η v.asIdeal =
        ArtinPrimitiveRoots.Hecke.charValue η0 v.asIdeal := by
    intro v hv
    have hη : ArtinPrimitiveRoots.Hecke.charValue η v.asIdeal = 1 := by
      simpa [η] using res_charValue_trivial_prime_of_not_mem m v hv
    have hη0 : ArtinPrimitiveRoots.Hecke.charValue η0 v.asIdeal = 1 := by
      simpa [η0] using res_charValue_trivial_prime_of_not_mem m0 v (by simp [m0])
    rw [hη, hη0]
  have hchange := ArtinPrimitiveRoots.Hecke.LSeriesRay_change_modulus
    (η := η) (η' := η0) hagree hs
  have hzero : ArtinPrimitiveRoots.Hecke.LSeriesRay η0 s = NumberField.dedekindZeta F s := by
    simpa [η0] using ArtinPrimitiveRoots.Hecke.LSeriesRay_trivial_eq_dedekindZeta
      (K := F) s
  rw [hzero, hsupp] at hchange
  have hprod :
      (∏ v ∈ T0, (1 - ArtinPrimitiveRoots.Hecke.charValue η0 v.asIdeal *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) =
        ∏ v ∈ T0, (1 - (qv v : ℂ) ^ (-s)) := by
    apply Finset.prod_congr rfl
    intro v hv
    have hη0 : ArtinPrimitiveRoots.Hecke.charValue η0 v.asIdeal = 1 := by
      simpa [η0] using res_charValue_trivial_prime_of_not_mem m0 v (by simp [m0])
    have hnorm : (qv v : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := by
      simp [qv]
    simp [hη0, hnorm]
  calc
    ArtinPrimitiveRoots.Hecke.LSeriesRay η s =
        NumberField.dedekindZeta F s *
          ∏ v ∈ T0, (1 - ArtinPrimitiveRoots.Hecke.charValue η0 v.asIdeal *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := hchange
    _ = NumberField.dedekindZeta F s * ∏ v ∈ T0, (1 - (qv v : ℂ) ^ (-s)) := by
      rw [hprod]
    _ = zetaT0 T0 s := rfl

set_option maxHeartbeats 500000 in
theorem cprod_pole (T0 : Finset (FinPlace F)) :
    ∃ ε > 0, ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) ε) ∧ Ψ (1 / 6) ≠ 0 ∧
      ∀ s ∈ Metric.ball (1 / 6 : ℂ) ε, 1 / 6 < s.re → Ψ s = (s - 1 / 6) * cprod T0 s := by
  classical
  let m := resModulus T0
  let η : ClassFieldTheory.RayClassGroup m →* ℂˣ := 1
  let L : ℂ → ℂ := ArtinPrimitiveRoots.Hecke.LSeriesRay η
  obtain ⟨G, hGdiff, hGeq, hG1⟩ :=
    ArtinPrimitiveRoots.Hecke.LSeriesRay_trivial_continuation (K := F) m
  have habsc : LSeries.abscissaOfAbsConv (ArtinPrimitiveRoots.Hecke.coeff η) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact ArtinPrimitiveRoots.Hecke.LSeriesSummable_coeff η (s := (y : ℂ)) (by
      simpa using hy)
  have hLanalytic : AnalyticOnNhd ℂ L {z | 1 < z.re} := by
    have hsub : {z : ℂ | 1 < z.re} ⊆
        {z | LSeries.abscissaOfAbsConv (ArtinPrimitiveRoots.Hecke.coeff η) < z.re} := by
      intro z hz
      exact lt_of_le_of_lt habsc (by exact_mod_cast hz)
    simpa [L, ArtinPrimitiveRoots.Hecke.LSeriesRay] using!
      (LSeries_analyticOnNhd (ArtinPrimitiveRoots.Hecke.coeff η)).mono hsub
  have hLnonzero (z : ℂ) (hz : 1 < z.re) : L z ≠ 0 := by
    simpa [L] using
      (ArtinPrimitiveRoots.Hecke.norm_LSeriesRay_le (η := η) hz).2.1
  have hprodPos : 0 < ∏ v ∈ m.finitePart.support,
      (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) := by
    apply Finset.prod_pos
    intro v hv
    have hN : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hi : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ hN
    linarith
  have hG1ne : G 1 ≠ 0 := by
    rw [hG1]
    exact_mod_cast (mul_ne_zero (NumberField.dedekindZeta_residue_ne_zero F)
      (ne_of_gt hprodPos))
  have hL2ne : L 2 ≠ 0 := hLnonzero 2 (by norm_num)
  let ε : ℝ := 1 / 12
  have hε : 0 < ε := by norm_num [ε]
  let Ψ : ℂ → ℂ := fun s => ((1 / 6 : ℂ) * G (6 * s)) / L (6 * s + 1)
  have hmap (s : ℂ) (hs : s ∈ Metric.ball (1 / 6 : ℂ) ε) : 1 < (6 * s + 1).re := by
    have hdist : dist s (1 / 6 : ℂ) < ε := Metric.mem_ball.mp hs
    have hreal : |s.re - (1 / 6 : ℝ)| < 1 / 12 := by
      have hle : |s.re - (1 / 6 : ℝ)| ≤ ‖s - (1 / 6 : ℂ)‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (s - (1 / 6 : ℂ))
      have hnorm : ‖s - (1 / 6 : ℂ)‖ < (1 / 12 : ℝ) := by
        simpa [Complex.dist_eq, ε] using hdist
      exact lt_of_le_of_lt hle hnorm
    have hsre : 1 / 12 < s.re := by
      have := (abs_lt.mp hreal).1
      linarith
    have hre : (6 * s + 1).re = 6 * s.re + 1 := by simp
    rw [hre]
    nlinarith
  have hGanalytic : AnalyticOnNhd ℂ G Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hGdiff
  have hGcomp : AnalyticOnNhd ℂ (fun s : ℂ => G (6 * s))
      (Metric.ball (1 / 6 : ℂ) ε) := by
    have haff : AnalyticOnNhd ℂ (fun s : ℂ => 6 * s) (Metric.ball (1 / 6 : ℂ) ε) := by
      fun_prop
    exact hGanalytic.comp haff (by intro s hs; simp)
  have hLcomp : AnalyticOnNhd ℂ (fun s : ℂ => L (6 * s + 1))
      (Metric.ball (1 / 6 : ℂ) ε) := by
    have haff : AnalyticOnNhd ℂ (fun s : ℂ => 6 * s + 1)
        (Metric.ball (1 / 6 : ℂ) ε) := by fun_prop
    exact hLanalytic.comp haff hmap
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => (1 / 6 : ℂ))
      (Metric.ball (1 / 6 : ℂ) ε) := by fun_prop
  have hnum : AnalyticOnNhd ℂ (fun s : ℂ => (1 / 6 : ℂ) * G (6 * s))
      (Metric.ball (1 / 6 : ℂ) ε) := hconst.mul hGcomp
  have hΨ : AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) ε) := by
    have hden : ∀ s ∈ Metric.ball (1 / 6 : ℂ) ε, L (6 * s + 1) ≠ 0 := by
      intro s hs
      exact hLnonzero (6 * s + 1) (hmap s hs)
    simpa [Ψ] using hnum.div hLcomp hden
  have hΨ0 : Ψ (1 / 6) ≠ 0 := by
    dsimp [Ψ]
    convert div_ne_zero
      (mul_ne_zero (show (1 / 6 : ℂ) ≠ 0 by norm_num) hG1ne) hL2ne using 1 <;> norm_num
  refine ⟨ε, hε, Ψ, hΨ, hΨ0, ?_⟩
  intro s hsball hs
  have hu : 1 < (6 * s).re := by
    have hre : (6 * s).re = 6 * s.re := by simp
    rw [hre]
    nlinarith
  have hu1 : 1 < (6 * s + 1).re := by
    have hre : (6 * s + 1).re = (6 * s).re + 1 := by simp
    rw [hre]
    linarith
  have hG := hGeq (6 * s) hu
  have hpart0 : L (6 * s) = zetaT0 T0 (6 * s) := by
    simpa [L, η, m] using resLSeries_eq_zetaT0 T0 (6 * s) hu
  have hpart1 : L (6 * s + 1) = zetaT0 T0 (6 * s + 1) := by
    simpa [L, η, m] using resLSeries_eq_zetaT0 T0 (6 * s + 1) hu1
  calc
    Ψ s = ((1 / 6 : ℂ) * G (6 * s)) / L (6 * s + 1) := rfl
    _ = ((1 / 6 : ℂ) * ((6 * s - 1) * L (6 * s))) / L (6 * s + 1) := by rw [hG]
    _ = (s - 1 / 6) * (L (6 * s) / L (6 * s + 1)) := by ring
    _ = (s - 1 / 6) * (zetaT0 T0 (6 * s) / zetaT0 T0 (6 * s + 1)) := by
      rw [hpart0, hpart1]
    _ = (s - 1 / 6) * cprod T0 s := by
      rw [cprod_eq_zeta_ratio T0 s hs]

/-- The residue of `cprod` at `1/6`. -/
def resCprod (T0 : Finset (FinPlace F)) : ℂ :=
  limUnder (𝓝[>] (1 / 6 : ℝ)) fun t : ℝ => ((t : ℂ) - 1 / 6) * cprod T0 (t : ℂ)

theorem resCprod_ne_zero (T0 : Finset (FinPlace F)) : resCprod T0 ≠ 0 := by
  obtain ⟨ε, hε, Ψ, hΨ, hΨ0, hΨeq⟩ := cprod_pole T0
  have hcenter : (1 / 6 : ℂ) ∈ Metric.ball (1 / 6 : ℂ) ε :=
    Metric.mem_ball_self hε
  have hcast : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (1 / 6 : ℝ))
      (𝓝 ((1 / 6 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (1 / 6 : ℝ)).mono_left
      (show 𝓝[>] (1 / 6 : ℝ) ≤ 𝓝 (1 / 6 : ℝ) from nhdsWithin_le_nhds)
  have hcastEq : ((1 / 6 : ℝ) : ℂ) = (1 / 6 : ℂ) := by norm_num
  have hcenterCast : ((1 / 6 : ℝ) : ℂ) ∈ Metric.ball (1 / 6 : ℂ) ε := by
    rw [hcastEq]
    exact hcenter
  have hlimΨ : Tendsto (fun t : ℝ => Ψ (t : ℂ)) (𝓝[>] (1 / 6 : ℝ))
      (𝓝 (Ψ (1 / 6))) := by
    have hcast' : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (1 / 6 : ℝ))
        (𝓝 (1 / 6 : ℂ)) := by simpa only [hcastEq] using hcast
    exact (hΨ (1 / 6) hcenter).continuousAt.tendsto.comp hcast'
  have hball : ∀ᶠ t : ℝ in 𝓝[>] (1 / 6 : ℝ), (t : ℂ) ∈ Metric.ball (1 / 6 : ℂ) ε :=
    hcast.eventually (Metric.isOpen_ball.mem_nhds hcenterCast)
  have hmatch : (fun t : ℝ => Ψ (t : ℂ)) =ᶠ[𝓝[>] (1 / 6 : ℝ)]
      (fun t : ℝ => ((t : ℂ) - 1 / 6) * cprod T0 (t : ℂ)) := by
    filter_upwards [hball, self_mem_nhdsWithin] with t htball ht
    exact hΨeq (t : ℂ) htball (by simpa using ht)
  have hlimCprod : Tendsto (fun t : ℝ => ((t : ℂ) - 1 / 6) * cprod T0 (t : ℂ))
      (𝓝[>] (1 / 6 : ℝ)) (𝓝 (Ψ (1 / 6))) := by
    exact hlimΨ.congr' hmatch
  have hres : resCprod T0 = Ψ (1 / 6) := by
    unfold resCprod
    exact hlimCprod.limUnder_eq
  rw [hres]
  exact hΨ0

/-- **res:continuation** (existence, from P-REDUCTION `red:decompose` and P-SPEC
`exists_continuedEisenstein`). -/
theorem exists_continuedEis {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) : Nonempty (ContinuedEis Fam) := by
  letI : IsTotallyComplex F := D.isTotallyComplex
  let I : ContinuedEisInput P G := {
    sec := Fam.sec
    T0 := Fam.T0
    T0_eq := Fam.T0_eq
    fC_sph := Fam.fC_sph
    f_analytic := Fam.f_analytic
    level := Fam.level }
  obtain ⟨C⟩ := continuedEis_uniform_level_components I
  obtain ⟨R⟩ := continuedEis_component_reconstruction C
  obtain ⟨hseries, hanalytic, hlaurent⟩ := continuedEis_series_analytic R
  obtain ⟨hcont, harch, hjoint⟩ := continuedEis_theta_cont R
  exact ⟨{
    ε := C.ε
    ε_pos := C.ε_pos
    E := R.E
    E_series := hseries
    E_analytic := hanalytic
    theta := R.theta
    laurent := hlaurent
    laurent_torus := continuedEis_laurent_torus R (continuedEis_torus_charts R)
    theta_cont := hcont
    archSmooth := harch
    jointRoots := hjoint }⟩

/-- The `M(1/6)`-data of a family: `M_v(1/6) f_v` at `v ∈ T0`, `f°'_v` elsewhere. -/
def famM {P : CoverPackage D S H A} {G : GlobalDatum P} {μ : ∀ v : FinPlace F, LocHaar v}
    (Fam : AnalyticFamily P G μ) (v : FinPlace F) : (P.loc v).L → (G.T v).V :=
  if hv : v ∈ Fam.T0 then intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v)
  else sphWeyl P G v (fun h => hv ((Fam.T0_eq (1 / 6)) ▸ (Fam.sec (1 / 6)).sub h)) (1 / 6)

/-- Extract the same section family's hypotheses for the acyclic Fourier helper modules. -/
def AnalyticFamily.fourierHyp {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) :
    FourierFamilyHyp μ Fam.sec Fam.T0 where
  T0_eq := Fam.T0_eq
  fC_sph := Fam.fC_sph
  f_analytic := Fam.f_analytic
  M_analytic := Fam.M_analytic
  J_analytic := Fam.J_analytic
  level := Fam.level

/-- Extract the existing continuation fields; all functions remain definitionally the same. -/
def ContinuedEis.fourierData {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {Fam : AnalyticFamily P G μ}
    (C : ContinuedEis Fam) : FourierResidueData Fam.sec where
  ε := C.ε
  ε_pos := C.ε_pos
  E := C.E
  E_series := C.E_series
  E_analytic := C.E_analytic
  theta := C.theta
  laurent := C.laurent
  laurent_torus := C.laurent_torus

/-- Euler regularization input, reusing the prior lane's partial-zeta identification.
Guide: sol-thin-thglobal/PROOFS.md:843–845. Uses Hecke trivial continuation,
resLSeries_eq_zetaT0, and the frozen cprod_eq_zeta_ratio. -/
theorem fourierEuler_hyp (T0 : Finset (FinPlace F)) : FourierEulerHyp T0 := by
  let m := resModulus T0
  let η : ClassFieldTheory.RayClassGroup m →* ℂˣ := 1
  let L : ℂ → ℂ := ArtinPrimitiveRoots.Hecke.LSeriesRay η
  obtain ⟨N, hNdiff, hNeq, hN1⟩ :=
    ArtinPrimitiveRoots.Hecke.LSeriesRay_trivial_continuation (K := F) m
  have habsc : LSeries.abscissaOfAbsConv (ArtinPrimitiveRoots.Hecke.coeff η) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact ArtinPrimitiveRoots.Hecke.LSeriesSummable_coeff η (s := (y : ℂ)) (by
      simpa using hy)
  have hLanalytic : AnalyticOnNhd ℂ L {z | 1 < z.re} := by
    have hsub : {z : ℂ | 1 < z.re} ⊆
        {z | LSeries.abscissaOfAbsConv (ArtinPrimitiveRoots.Hecke.coeff η) < z.re} := by
      intro z hz
      exact lt_of_le_of_lt habsc (by exact_mod_cast hz)
    convert! (LSeries_analyticOnNhd (ArtinPrimitiveRoots.Hecke.coeff η)).mono hsub using 1
      <;> simp only [L, ArtinPrimitiveRoots.Hecke.LSeriesRay]
  have hLnonzero : ∀ s : ℂ, 1 < s.re → L s ≠ 0 := by
    intro s hs
    exact (ArtinPrimitiveRoots.Hecke.norm_LSeriesRay_le (η := η) hs).2.1
  refine ⟨L, N, hLanalytic, hLnonzero, hNdiff, hNeq, ?_⟩
  intro s hs
  have h0 : 1 < (6 * s).re := by
    have hr : (6 * s).re = 6 * s.re := by simp
    rw [hr]; nlinarith
  have h1 : 1 < (6 * s + 1).re := by
    have hr : (6 * s + 1).re = 6 * s.re + 1 := by simp
    rw [hr]; nlinarith
  rw [cprod_eq_zeta_ratio T0 s hs]
  congr 1
  · exact (resLSeries_eq_zetaT0 T0 (6 * s) h0).symm
  · exact (resLSeries_eq_zetaT0 T0 (6 * s + 1) h1).symm

/-- **res:theta-constant**: the constant term of `θ` is `κ_F⁻¹ · res · Σ_δ Θ^M(a(δ)g)`. -/
theorem theta_constantTerm {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
      Pd volume) (hb : Bornology.IsBounded Pd) :
    torusCoeff P C.theta g Pd 0 = (κF F)⁻¹ * resCprod Fam.T0 *
      ∑' δ : Fˣ ⧸ G.Δ, scalarOf P G (famM Fam) (fun _ => intertwineC (sphC (1 / 6)))
        (P.tc.rat (diagGL (Quotient.out δ)) * g) := by
  have h := theta_constantTerm_assembly Fam.fourierHyp (fourierEuler_hyp Fam.T0)
    C.fourierData g 𝔞 h𝔞 hfix Pd hPd hb
  have hM : fourierRawM μ Fam.sec (1 / 6) =
      scalarOf P G (famM Fam) (fun _ => intertwineC (sphC (1 / 6))) := by
    funext h
    unfold fourierRawM
    congr 1
    · funext v
      unfold famM
      simp only [Fam.T0_eq]
    · funext w
      rw [Fam.fC_sph]
  simpa only [ContinuedEis.fourierData, resCprod, hM] using h

/-- **res:theta-whittaker**: every torus coefficient of `θ` with `ν ≠ 0` over an adapted lattice is
`W_θ(a(ν) g)`; `W_θ` is genuine and `(N, ψ)`-equivariant at every place. -/
theorem theta_fourierCoeff {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
      Pd volume) (hb : Bornology.IsBounded Pd)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1) :
    torusCoeff P C.theta g Pd (ν : F) = thetaWhit C (P.tc.rat (diagGL ν) * g) := by
  change torusCoeff P C.fourierData.theta g Pd (ν : F) =
    fourierFirstCoeff C.fourierData (P.tc.rat (diagGL ν) * g)
  exact theta_fourierCoeff_assembly Fam.fourierHyp C.fourierData g 𝔞 Pd ν
    ⟨h𝔞, hfix, hPd, hb, hν⟩

theorem thetaWhit_equiv {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam) :
    (∀ ζ g, thetaWhit C (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaWhit C g) ∧
    (∀ x g, thetaWhit C (P.tc.nS (Multiplicative.ofAdd x) * g) = S.e A x * thetaWhit C g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g, thetaWhit C (P.tc.n v (Multiplicative.ofAdd x) * g) =
      A.ψ v x * thetaWhit C g) := by
  change (∀ ζ g, fourierFirstCoeff C.fourierData (P.tc.z ζ * g) =
      ((ζ : ℂˣ) : ℂ) * fourierFirstCoeff C.fourierData g) ∧
    (∀ x g, fourierFirstCoeff C.fourierData (P.tc.nS (Multiplicative.ofAdd x) * g) =
      S.e A x * fourierFirstCoeff C.fourierData g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g,
      fourierFirstCoeff C.fourierData (P.tc.n v (Multiplicative.ofAdd x) * g) =
        A.ψ v x * fourierFirstCoeff C.fourierData g)
  exact thetaWhit_equiv_assembly Fam.fourierHyp C.fourierData

/-- **res:depends-on-M** (via P-REDUCTION and P-SPEC `res_lincomb_eq_zero` only): `θ` depends only on
the `M(1/6)`-data. -/
theorem theta_depends_on_M {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam Fam' : AnalyticFamily P G μ) (C : ContinuedEis Fam)
    (C' : ContinuedEis Fam') (hT : Fam.T0 = Fam'.T0)
    (hM : ∀ v ∈ Fam.T0, intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v) =
      intertwine (P.loc v) (μ v) ((Fam'.sec (1 / 6)).f v)) :
    C.theta = C'.theta := by
  sorry

/-- **res:linear-translate**: `θ` is linear in the section at one place and right translation of
that section translates `θ`. -/
theorem theta_linear_translate {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (v0 : FinPlace F) (Fam Fam' Fam'' : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) (C' : ContinuedEis Fam') (C'' : ContinuedEis Fam'') :
    ((∀ s, ∀ v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v ∧ (Fam''.sec s).f v = (Fam.sec s).f v) →
      ∀ c : ℂ, (∀ s, (Fam''.sec s).f v0 = (Fam.sec s).f v0 + c • (Fam'.sec s).f v0) →
        C''.theta = C.theta + c • C'.theta) ∧
    (∀ h : (P.loc v0).L, (∀ s, ∀ v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v) →
      (∀ s, (Fam'.sec s).f v0 = rtr h ((Fam.sec s).f v0)) →
        ∀ g, C'.theta g = C.theta (g * P.emb v0 h)) := by
  sorry

/-- Supply the package proof modules with the frozen residue interfaces. -/
private def thetaResidueLaws {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} : ThetaResidueLaws P G μ where
  continuation := exists_continuedEis
  fourierCoeff := theta_fourierCoeff
  equiv := thetaWhit_equiv
  dependsOnM := theta_depends_on_M
  linearTranslate := theta_linear_translate

/-- **res:exterior-whittaker**: at `v0 ∉ S`, `M(1/6) f ↦ W_θ(g)` (`g` commuting with the `v0`-part)
is a well-defined Whittaker functional on `Θ_{v0}`; P-LOCAL-WHIT then makes it unique. -/
theorem theta_exterior_whittaker {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (hv0 : v0 ∉ S.Sf) (g : P.tc.G) (hg : ∀ h : (P.loc v0).L, g * P.emb v0 h = P.emb v0 h * g) :
    ∃ Λ : ((P.loc v0).L → (G.T v0).V) →ₗ[ℂ] ℂ,
      IsWhittakerOn (P.loc v0) A (thetaSpace (P.loc v0) (G.T v0) (μ v0)) Λ ∧
      ∀ (Fam' : AnalyticFamily P G μ) (C' : ContinuedEis Fam'),
        Fam'.T0 = insert v0 Fam.T0 → (∀ s, ∀ v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v) →
          thetaWhit C' g = Λ (intertwine (P.loc v0) (μ v0) ((Fam'.sec (1 / 6)).f v0)) := by
  obtain ⟨Λ, hΛ⟩ := theta_lambda_descent Fam v0 hv0 g thetaResidueLaws
  refine ⟨Λ, theta_lambda_whittaker Fam v0 hv0 g hg thetaResidueLaws Λ hΛ, ?_⟩
  intro Fam' C' hT hext
  exact hΛ Fam' C' ⟨hT, hext⟩

/-- **res:root-generation**: at a tame place the root subgroups generate a nontrivial central element. -/
theorem center_mem_root_closure {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (L : FinLocalCover D H v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) :
    ∃ ζ : rootsOfUnity 3 ℂ, ζ ≠ 1 ∧ L.z ζ ∈ Subgroup.closure (Set.range L.n ∪ Set.range L.nbar) := by
  obtain ⟨t, u, hne⟩ := square_pairing_nontrivial D H v
  exact ⟨_, hne, root_square_commutator L t u
    (root_square_lift L t) (root_square_lift L u)⟩

/-- **res:nonzero**: a nonzero `θ` has a nonzero Whittaker coefficient. -/
theorem thetaWhit_ne_zero {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam)
    (hθ : ∃ g, C.theta g ≠ 0) : ∃ g, thetaWhit C g ≠ 0 := by
  classical
  by_contra h
  have hW : ∀ g, thetaWhit C g = 0 := by simpa only [not_exists, not_not] using h
  have hcoeff : ∀ (g : P.tc.G)
      (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (Pd : Set (InfinitePlace F → ℂ)) (ν : Fˣ),
      FourierAdaptedDomain Fam.sec g 𝔞 Pd (ν : F) →
        torusCoeff P C.theta g Pd (ν : F) = 0 := by
    intro g 𝔞 Pd ν hdom
    exact (theta_fourierCoeff Fam C g 𝔞 hdom.1 hdom.2.1 Pd hdom.2.2.1
      hdom.2.2.2.1 ν hdom.2.2.2.2).trans (hW _)
  have harch := residue_arch_invariant_of_nonzero_coeff_zero Fam C Fam.fourierHyp hcoeff
  obtain ⟨v, hv⟩ := exists_exterior_finPlace S
  have hn := residue_exterior_upper_invariant_of_arch_invariant Fam C harch v hv
  have hnbar := residue_exterior_lower_invariant_of_upper_invariant Fam C v hv hn
  obtain ⟨g, hg⟩ := hθ
  exact hg (root_invariant_genuine_zero (P := P) v hv C.theta (residue_genuine Fam C)
    (fun t g => hn (Multiplicative.toAdd t) g)
    (fun t g => hnbar (Multiplicative.toAdd t) g) g)

/-- **res:theta-exists**: big-cell sections at `S_f` and spherical sections elsewhere give `θ ≠ 0`.
C6 of `sol-gate-theta` requires the cube-containing Lagrangian global datum. -/
theorem exists_theta_ne_zero (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) :
    ∃ (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam), Fam.T0 = S.Sf ∧
      (∀ v ∈ S.Sf, ∃ φ : v.adicCompletion F → (G.T v).V, IsLocallyConstant φ ∧ HasCompactSupport φ ∧
        ∀ s, (Fam.sec s).f v = bigCell (P.loc v) (G.T v) s φ) ∧ ∃ g, C.theta g ≠ 0 := by
  sorry

/-- **res:theta-multilinear**: with the data outside `S_f` fixed, `W_θ(g)` is a multilinear form in
the local Jacquet vectors at `S_f` at `s0`, times the complex spherical Jacquet values. -/
theorem thetaWhit_multilinear {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (x0 : P.RP) :
    ∃ Λ : MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ,
      ∀ (Fam' : AnalyticFamily P G μ) (C' : ContinuedEis Fam') (x : P.RP), Fam'.T0 = Fam.T0 →
        (∀ s, ∀ v, v ∉ S.Sf → (Fam'.sec s).f v = (Fam.sec s).f v) →
        (∀ v, v ∉ S.Sf → P.compF v x = P.compF v x0) →
          thetaWhit C' (P.q x) =
            Λ (fun v => jacquet (P.loc v.1) A (μ v.1) (rtr (P.compF v.1 x) ((Fam'.sec (1 / 6)).f v.1))) *
              ∏ w, jacquetC (rtr (P.compC w x) (sphC (1 / 6))) := by
  obtain ⟨W, hW, hmatch⟩ := thetaWhit_section_multilinear Fam x0 thetaResidueLaws
  obtain ⟨Λ, hfactor⟩ := thetaWhit_jacquet_factorization (μ := μ) W hW
  refine ⟨Λ, ?_⟩
  intro Fam' C' x hT hext hx
  simpa only [hfactor, familySectionCoords] using hmatch Fam' C' x hT hext hx

end Res

end ArtinPrimitiveRoots.A1.Theta
