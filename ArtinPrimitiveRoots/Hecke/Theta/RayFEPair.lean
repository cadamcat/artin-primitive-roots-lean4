import ArtinPrimitiveRoots.Hecke.Theta.RaySmall
import ArtinPrimitiveRoots.Hecke.Theta.DirichletDecomposition

/-!
Functional-equation pairs of ray-class theta functions. The two constant terms are independent
of the representative ideal, so a nontrivial ray-class character gives an entire completed
Mellin transform. Its agreement with the ray-class Dirichlet series is a separate statement.

The construction follows AINTLIB's `DedekindResidue/CompletedZeta/FEPair.lean`
(Chris Birkbeck, Apache-2.0), using the ray theta estimates instead of the ordinary theta.
-/

set_option autoImplicit false

open NumberField ClassFieldTheory MeasureTheory Filter Asymptotics
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open DedekindResidue ArtinPrimitiveRoots.Hecke.Theta
open scoped NumberField Topology Real NNReal

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

private theorem complex_sub_const_isBigO_of_exp_bound (f : ℝ → ℝ) (d : ℝ)
    {p : ℝ} (hp : 0 < p)
    (h : ∃ C c' t₀ : ℝ, 0 < C ∧ 0 < c' ∧ 1 ≤ t₀ ∧
      ∀ {t : ℝ}, t₀ ≤ t → |f t - d| ≤ C * Real.exp (-c' * t ^ p)) (r : ℝ) :
    (fun t : ℝ => (f t : ℂ) - (d : ℂ)) =O[atTop] (fun t : ℝ => t ^ r) := by
  obtain ⟨C, c', t₀, _, hc', _, hbound⟩ := h
  refine IsBigO.trans ?_ (isBigO_exp_neg_rpow hc' hp r)
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop t₀] with t ht
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hbound ht

/-- A half-weight functional-equation pair for a prime-to integral ray representative. -/
def rayFEPair [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) : WeakFEPair ℂ where
  f := fun t => (rayF m J hcop t : ℂ)
  g := fun t => (rayDualF m J hcop t : ℂ)
  k := 1 / 2
  ε := 1
  f₀ := (rayPrimalConstant m : ℂ)
  g₀ := (rayDualConstant m : ℂ)
  hf_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_rayF m J hcop)).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_rayDualF m J hcop)).locallyIntegrableOn measurableSet_Ioi
  hk := by norm_num
  hε := one_ne_zero
  h_feq t ht := by
    have htpos : 0 < t := ht
    have hpow : t ^ ((1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add htpos]
      norm_num
    change (rayF m J hcop (1 / t) : ℂ) = _
    simp only [smul_eq_mul, one_mul, rayDualF, Complex.ofReal_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, hpow, Complex.ofReal_one, one_mul]
  hf_top r := complex_sub_const_isBigO_of_exp_bound _ _
    (div_pos one_pos (finrank_pos_real K)) (exists_rayF_dev_bound m J hcop) r
  hg_top r := complex_sub_const_isBigO_of_exp_bound _ _
    (div_pos one_pos (finrank_pos_real K)) (exists_rayDualF_dev_bound m J hcop) r

local instance rayFEGroupFintype [IsTotallyComplex K] (m : RayClassModulus K) :
    Fintype (RayClassGroup m) := by
  letI : Finite (RayClassGroup m) := rayClassGroup_finite_viaCFT m
  exact Fintype.ofFinite _

/-- The character-weighted theta pair for a chosen family of integral ray representatives. -/
def rayCharacterFEPair [IsTotallyComplex K] {m : RayClassModulus K}
    (R : IntegralRayRepresentatives m) (η : RayClassGroup m →* ℂˣ) : WeakFEPair ℂ :=
  finiteFEPair (1 / 2) (by norm_num)
    (fun C => rayFEPair m (R.ideal C) (R.coprime C)) (fun _ => rfl)
    (fun C => (η C : ℂ))

/-- Orthogonality removes both polar terms of the completed ray-character theta sum. -/
theorem rayCharacter_completed_entire [IsTotallyComplex K] {m : RayClassModulus K}
    (R : IntegralRayRepresentatives m) (η : RayClassGroup m →* ℂˣ) (hη : η ≠ 1) :
    Differentiable ℂ (rayCharacterFEPair R η).Λ := by
  apply finiteFEPair_character_differentiable η hη
    (fun C => rayFEPair m (R.ideal C) (R.coprime C))
    (1 / 2) (by norm_num) (fun _ => rfl)
    (rayPrimalConstant m : ℂ) (rayDualConstant m : ℂ)
  · intro C
    rfl
  · intro C
    simp [rayFEPair]

/-- Mellin transforms commute with the finite character sum on the convergence half-plane. -/
theorem rayCharacterFEPair_Λ_eq_sum [IsTotallyComplex K] {m : RayClassModulus K}
    (R : IntegralRayRepresentatives m) (η : RayClassGroup m →* ℂˣ)
    {z : ℂ} (hz : (1 : ℝ) / 2 < z.re) :
    (rayCharacterFEPair R η).Λ z =
      ∑ C : RayClassGroup m, (η C : ℂ) * (rayFEPair m (R.ideal C) (R.coprime C)).Λ z := by
  classical
  let P := fun C => rayFEPair m (R.ideal C) (R.coprime C)
  let Q := rayCharacterFEPair R η
  have hQ : Q.k < z.re := hz
  have hP : ∀ C, (P C).k < z.re := fun _ => hz
  rw [← (Q.hasMellin hQ).2, mellin]
  have hsum : (fun t : ℝ => (t : ℂ) ^ (z - 1) • (Q.f t - Q.f₀)) =
      fun t : ℝ => ∑ C : RayClassGroup m,
        (η C : ℂ) • ((t : ℂ) ^ (z - 1) • ((P C).f t - (P C).f₀)) := by
    funext t
    simp only [Q, rayCharacterFEPair, finiteFEPair, P,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  rw [hsum, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro C _
    rw [integral_smul]
    change (η C : ℂ) • mellin (fun t => (P C).f t - (P C).f₀) z = _
    rw [(P C).hasMellin (hP C) |>.2]
    rfl
  · intro C _
    exact Integrable.smul (η C : ℂ) ((P C).hasMellin (hP C)).1

/-- The common completed Mellin factor, using the AINTLIB unit-box Jacobian. -/
def rayMellinFactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((heckeJacobian K : ℝ≥0) : ℝ) : ℂ) * (heckeBeta K : ℂ) ^ (-s / 2) *
    ∏ w : NumberField.InfinitePlace K,
      (Real.pi : ℂ) ^ (-((NumberField.InfinitePlace.mult w : ℂ) * s / 2)) *
        Complex.Gamma ((NumberField.InfinitePlace.mult w : ℂ) * s / 2)

/-- The reciprocal completed Mellin factor, expressed with entire reciprocal Gamma functions. -/
def rayMellinNormalization (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ((((heckeJacobian K : ℝ≥0) : ℝ) : ℂ))⁻¹ * (heckeBeta K : ℂ) ^ (s / 2) *
    ∏ w : NumberField.InfinitePlace K,
      (Real.pi : ℂ) ^ ((NumberField.InfinitePlace.mult w : ℂ) * s / 2) *
        (Complex.Gamma ((NumberField.InfinitePlace.mult w : ℂ) * s / 2))⁻¹

theorem differentiable_rayMellinNormalization (K : Type*) [Field K] [NumberField K] :
    Differentiable ℂ (rayMellinNormalization K) := by
  have hβ : (heckeBeta K : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (heckeBeta_pos K).ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hβpow : Differentiable ℂ (fun s : ℂ => (heckeBeta K : ℂ) ^ (s / 2)) := by
    intro s
    exact (differentiableAt_id.div_const _).const_cpow (Or.inl hβ)
  apply Differentiable.mul (hβpow.const_mul _)
  apply Differentiable.fun_finsetProd
  intro w _
  have harg : Differentiable ℂ
      (fun s : ℂ => (NumberField.InfinitePlace.mult w : ℂ) * s / 2) := by fun_prop
  have hπpow : Differentiable ℂ (fun s : ℂ =>
      (Real.pi : ℂ) ^ ((NumberField.InfinitePlace.mult w : ℂ) * s / 2)) :=
    fun s => (harg s).const_cpow (Or.inl hπ)
  exact hπpow.mul (Complex.differentiable_one_div_Gamma.comp harg)

theorem rayMellinNormalization_mul_factor (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    rayMellinNormalization K s * rayMellinFactor K s = 1 := by
  classical
  have hJ : ((((heckeJacobian K : ℝ≥0) : ℝ) : ℂ)) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    have hpos : 0 < ((heckeJacobian K : ℝ≥0) : ℝ) := by
      exact_mod_cast heckeJacobian_pos K
    exact hpos.ne'
  have hβ : (heckeBeta K : ℂ) ^ (s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl
      (Complex.ofReal_ne_zero.mpr (heckeBeta_pos K).ne'))
  have hprod : (∏ w : NumberField.InfinitePlace K,
      (Real.pi : ℂ) ^ ((NumberField.InfinitePlace.mult w : ℂ) * s / 2) *
        (Complex.Gamma ((NumberField.InfinitePlace.mult w : ℂ) * s / 2))⁻¹) *
      (∏ w : NumberField.InfinitePlace K,
        (Real.pi : ℂ) ^ (-((NumberField.InfinitePlace.mult w : ℂ) * s / 2)) *
          Complex.Gamma ((NumberField.InfinitePlace.mult w : ℂ) * s / 2)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro w _
    have hπ : (Real.pi : ℂ) ^ ((NumberField.InfinitePlace.mult w : ℂ) * s / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hΓ : Complex.Gamma ((NumberField.InfinitePlace.mult w : ℂ) * s / 2) ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro n hn
      have hm : 0 < (NumberField.InfinitePlace.mult w : ℝ) := by
        exact_mod_cast NumberField.InfinitePlace.mult_pos (w := w)
      have hre := congrArg Complex.re hn
      have hpos : 0 < (NumberField.InfinitePlace.mult w : ℝ) * s.re / 2 := by
        have hspos : 0 < s.re := lt_trans one_pos hs
        positivity
      norm_num [Complex.div_re, Complex.mul_re] at hre
      linarith
    rw [Complex.cpow_neg]
    calc
      _ = ((Real.pi : ℂ) ^ ((NumberField.InfinitePlace.mult w : ℂ) * s / 2) *
          ((Real.pi : ℂ) ^ ((NumberField.InfinitePlace.mult w : ℂ) * s / 2))⁻¹) *
          ((Complex.Gamma ((NumberField.InfinitePlace.mult w : ℂ) * s / 2))⁻¹ *
            Complex.Gamma ((NumberField.InfinitePlace.mult w : ℂ) * s / 2)) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hπ, inv_mul_cancel₀ hΓ, one_mul]
  unfold rayMellinNormalization rayMellinFactor
  rw [show -s / 2 = -(s / 2) by ring, Complex.cpow_neg]
  calc
    _ = (((((heckeJacobian K : ℝ≥0) : ℝ) : ℂ))⁻¹ *
          ((((heckeJacobian K : ℝ≥0) : ℝ) : ℂ))) *
        ((heckeBeta K : ℂ) ^ (s / 2) * ((heckeBeta K : ℂ) ^ (s / 2))⁻¹) *
        ((∏ w : NumberField.InfinitePlace K,
          (Real.pi : ℂ) ^ ((NumberField.InfinitePlace.mult w : ℂ) * s / 2) *
            (Complex.Gamma ((NumberField.InfinitePlace.mult w : ℂ) * s / 2))⁻¹) *
          (∏ w : NumberField.InfinitePlace K,
            (Real.pi : ℂ) ^ (-((NumberField.InfinitePlace.mult w : ℂ) * s / 2)) *
              Complex.Gamma ((NumberField.InfinitePlace.mult w : ℂ) * s / 2))) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hJ, mul_inv_cancel₀ hβ, hprod]; norm_num

/-- The final H1 assembly, with the sole remaining per-class Mellin agreement made explicit. -/
theorem LSeriesRay_entire_of_rayMellinAgreement [IsTotallyComplex K] {m : RayClassModulus K}
    (R : IntegralRayRepresentatives m) (η : RayClassGroup m →* ℂˣ) (hη : η ≠ 1)
    (hM : ∀ (C : RayClassGroup m) (s : ℂ), 1 < s.re →
      (rayFEPair m (R.ideal C) (R.coprime C)).Λ (s / 2) =
        rayMellinFactor K s * rayClassPartialZeta C s) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∀ s : ℂ, 1 < s.re → Λ s = LSeriesRay η s := by
  refine ⟨fun s => rayMellinNormalization K s * (rayCharacterFEPair R η).Λ (s / 2),
    (differentiable_rayMellinNormalization K).mul
      ((rayCharacter_completed_entire R η hη).comp (differentiable_id.div_const 2)), ?_⟩
  intro s hs
  dsimp only
  have hs' : (1 : ℝ) / 2 < (s / 2).re := by
    norm_num [Complex.div_re]
    linarith
  rw [rayCharacterFEPair_Λ_eq_sum R η hs']
  simp_rw [hM _ s hs]
  rw [show (∑ C : RayClassGroup m, (η C : ℂ) *
      (rayMellinFactor K s * rayClassPartialZeta C s)) =
      rayMellinFactor K s * ∑ C : RayClassGroup m, (η C : ℂ) * rayClassPartialZeta C s by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro C _; ring]
  rw [← mul_assoc, rayMellinNormalization_mul_factor K hs, one_mul,
    ← LSeriesRay_eq_rayClassPartialZeta_sum η hs]

/-- Real-ray agreement of an entire function with the convergent L-series extends to Re s > 1. -/
theorem LSeriesRay_eq_of_entire_real_agreement {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hreal : ∀ σ : ℝ, 1 < σ → F (σ : ℂ) = LSeriesRay η (σ : ℂ)) :
    ∀ s : ℂ, 1 < s.re → F s = LSeriesRay η s := by
  have hUopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected {z : ℂ | 1 < z.re} :=
    (convex_halfSpace_re_gt 1).isPreconnected
  have hFan : AnalyticOnNhd ℂ F {z : ℂ | 1 < z.re} :=
    hF.differentiableOn.analyticOnNhd hUopen
  have habs : LSeries.abscissaOfAbsConv (coeff η) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => LSeriesSummable_coeff η (by simpa using hy))
  have hLan : AnalyticOnNhd ℂ (LSeriesRay η) {z : ℂ | 1 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    have hz' : LSeries.abscissaOfAbsConv (coeff η) < (z.re : EReal) :=
      lt_of_le_of_lt habs (by exact_mod_cast hz)
    exact (LSeries_hasDerivAt hz').differentiableAt.differentiableWithinAt
  have hfreq : ∃ᶠ z in nhdsWithin (2 : ℂ) {(2 : ℂ)}ᶜ,
      F z = LSeriesRay η z := by
    have htend : Filter.Tendsto (fun n : ℕ => ((2 + (1 : ℝ) / (n + 1) : ℝ) : ℂ))
        Filter.atTop (nhdsWithin (2 : ℂ) {(2 : ℂ)}ᶜ) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hre : Filter.Tendsto (fun n : ℕ => (2 + (1 : ℝ) / (n + 1) : ℝ))
            Filter.atTop (𝓝 (2 : ℝ)) := by
          have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
              Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
          simpa using h0.const_add (2 : ℝ)
        have hcomp := (Complex.continuous_ofReal.tendsto (2 : ℝ)).comp hre
        refine hcomp.congr (fun n => rfl) |>.mono_right ?_
        rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_cast]
      · refine Filter.Eventually.of_forall (fun n => ?_)
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have hr : (2 + (1 : ℝ) / (n + 1) : ℝ) = 2 := by exact_mod_cast h
        have hp : (0 : ℝ) < (1 : ℝ) / (n + 1) := by positivity
        linarith
    apply htend.frequently (Filter.Frequently.of_forall (fun n => ?_))
    apply hreal
    have hp : (0 : ℝ) < (1 : ℝ) / (n + 1) := by positivity
    linarith
  have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  exact hFan.eqOn_of_preconnected_of_frequently_eq hLan hUconn h2 hfreq

/-- For H1, per-class Mellin agreement on the real ray suffices. -/
theorem LSeriesRay_entire_of_real_rayMellinAgreement [IsTotallyComplex K]
    {m : RayClassModulus K} (R : IntegralRayRepresentatives m)
    (η : RayClassGroup m →* ℂˣ) (hη : η ≠ 1)
    (hM : ∀ (C : RayClassGroup m) (σ : ℝ), 1 < σ →
      (rayFEPair m (R.ideal C) (R.coprime C)).Λ ((σ : ℂ) / 2) =
        rayMellinFactor K (σ : ℂ) * rayClassPartialZeta C (σ : ℂ)) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∀ s : ℂ, 1 < s.re → Λ s = LSeriesRay η s := by
  let F : ℂ → ℂ := fun s =>
    rayMellinNormalization K s * (rayCharacterFEPair R η).Λ (s / 2)
  have hF : Differentiable ℂ F :=
    (differentiable_rayMellinNormalization K).mul
      ((rayCharacter_completed_entire R η hη).comp (differentiable_id.div_const 2))
  refine ⟨F, hF, LSeriesRay_eq_of_entire_real_agreement η F hF ?_⟩
  intro σ hσ
  have hσ' : (1 : ℝ) / 2 < ((σ : ℂ) / 2).re := by
    norm_num [Complex.div_re]
    linarith
  dsimp only [F]
  rw [rayCharacterFEPair_Λ_eq_sum R η hσ']
  simp_rw [hM _ σ hσ]
  rw [show (∑ C : RayClassGroup m, (η C : ℂ) *
      (rayMellinFactor K (σ : ℂ) * rayClassPartialZeta C (σ : ℂ))) =
      rayMellinFactor K (σ : ℂ) *
        ∑ C : RayClassGroup m, (η C : ℂ) * rayClassPartialZeta C (σ : ℂ) by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro C _; ring]
  rw [← mul_assoc, rayMellinNormalization_mul_factor K (by simpa using hσ), one_mul,
    ← LSeriesRay_eq_rayClassPartialZeta_sum η (by simpa using hσ)]

end ArtinPrimitiveRoots.Hecke

end
