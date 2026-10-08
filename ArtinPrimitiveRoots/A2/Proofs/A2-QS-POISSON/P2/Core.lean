import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2.Contour
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2.Zeta

/-!
# The abstract unweighted Poisson identity (core of P2)

For a weight `f` with Mellin data `Φ` (continuation of `Mellin f`), `Ψ = s Z₁(s) Φ(s)`
holomorphic and bounded on `-1/2 ≤ Re s ≤ 3/2`, and `D(u) = R(u) Φ(1-u)` holomorphic with
`O(1/t²)` decay on `1/2 ≤ Re u ≤ 3/2`:
`Σ_b f(N b/Y) = ρ_K Y Mellin(f)(1) + R_K(f) + Y Σ_b (T f)(Y N b)`.
Proof: Mellin inversion on `Re s = 3/2`, Dirichlet series, contour shift to `Re s = -1/2`
across the poles at `1` and `0`, functional equation, dual Dirichlet series, and a pole-free
shift of each dual integral to `Re u = 1/2`.
-/

set_option autoImplicit false

open Complex Filter Topology MeasureTheory NumberField
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSP2

variable {K : Type} [Field K] [NumberField K]

/-- Analytic data for P2. -/
structure P2Data (K : Type) [Field K] [NumberField K] (f : ℝ → ℂ) where
  Φ : ℂ → ℂ
  Ψ : ℂ → ℂ
  D : ℂ → ℂ
  inv : ∀ x : ℝ, 0 < x → f x = mellinInv (3/2) Φ x
  Φint : Integrable (fun t : ℝ => Φ (((3/2 : ℝ) : ℂ) + t * I))
  mel : ∀ s : ℂ, 0 < s.re → s.re < 2 → mellin f s = Φ s
  Φc1 : ContinuousAt Φ 1
  Ψd : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 → DifferentiableAt ℂ Ψ s
  Ψeq : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 → s ≠ 0 → s ≠ 1 → Ψ s = s * Z1 K s * Φ s
  Ψbd : ∃ C : ℝ, ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 → ‖Ψ s‖ ≤ C
  Dd : ∀ u : ℂ, 1/2 ≤ u.re → u.re ≤ 3/2 → DifferentiableAt ℂ D u
  Deq : ∀ u : ℂ, 1/2 ≤ u.re → u.re ≤ 3/2 → u ≠ 1 → D u = qsGammaRatio K u * Φ (1 - u)
  Dbd : ∃ C : ℝ, ∀ u : ℂ, 1/2 ≤ u.re → u.re ≤ 3/2 → 1 ≤ |u.im| → ‖D u‖ ≤ C / u.im ^ 2

/-! ### Small helpers -/

theorem integrable_of_cont_decay {g : ℝ → ℂ} (hg : Continuous g) (C : ℝ)
    (hC : ∀ t : ℝ, 1 ≤ |t| → ‖g t‖ ≤ C / t ^ 2) : Integrable g := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-1 : ℝ) 1) hg.continuousOn
  have hbound : ∀ t : ℝ, ‖g t‖ ≤ (2 * |B| + 2 * |C|) * (1 + t ^ 2)⁻¹ := by
    intro t
    have hpos : 0 < 1 + t ^ 2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    by_cases ht : |t| ≤ 1
    · have h1 := hB t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
      have : ‖g t‖ * (1 + t ^ 2) ≤ ‖g t‖ * 2 := by
        gcongr; linarith
      nlinarith [norm_nonneg (g t), abs_nonneg B, abs_nonneg C, le_abs_self B]
    · push Not at ht
      have h1 := hC t ht.le
      have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
      have ht2' : 0 < t ^ 2 := by linarith
      rw [le_div_iff₀ ht2'] at h1
      have : ‖g t‖ * (1 + t ^ 2) ≤ ‖g t‖ * (2 * t ^ 2) := by
        gcongr; linarith
      nlinarith [norm_nonneg (g t), abs_nonneg B, abs_nonneg C, le_abs_self C]
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * |B| + 2 * |C|))
    hg.aestronglyMeasurable (Eventually.of_forall hbound)

theorem rpow_le_add_of_mem {Y a x b : ℝ} (hY : 0 < Y) (hax : a ≤ x) (hxb : x ≤ b) :
    Y ^ x ≤ Y ^ a + Y ^ b := by
  rcases le_or_gt 1 Y with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hxb
    have : 0 ≤ Y ^ a := by positivity
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hY h.le hax
    have : 0 ≤ Y ^ b := by positivity
    linarith

theorem ofReal_div_cpow_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    (((a / b : ℝ)) : ℂ) ^ (-z) = (a : ℂ) ^ (-z) * (b : ℂ) ^ z := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (inv_nonneg.mpr hb.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hb.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg, Complex.cpow_neg b, inv_inv]

theorem norm_mellinInv_le (σ : ℝ) (G : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    ‖mellinInv σ G x‖ ≤ (1 / (2 * Real.pi)) * x ^ (-σ) *
      ∫ t : ℝ, ‖G (σ + t * I)‖ := by
  rw [mellinInv, norm_smul]
  have h1 : ‖(1 / (2 * Real.pi) : ℝ)‖ = 1 / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h1, mul_assoc]
  gcongr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [← integral_const_mul]
  congr 1
  funext t
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- Pole-free shift of an inverse Mellin integral of the dual data. -/
theorem mellinInv_shift_D {f : ℝ → ℂ} (P : P2Data K f) {x : ℝ} (hx : 0 < x) :
    mellinInv (3/2) P.D x = mellinInv (1/2) P.D x := by
  obtain ⟨CD, hCD⟩ := P.Dbd
  have hDc : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 3/2 → Continuous (fun t : ℝ => P.D (σ + t * I)) := by
    intro σ h1 h2
    refine continuous_iff_continuousAt.2 (fun t => ?_)
    exact ((P.Dd _ (by simp; linarith) (by simp; linarith)).continuousAt).comp (by fun_prop)
  set G : ℂ → ℂ := fun u => (x : ℂ) ^ (-u) * P.D u with hG
  have hGc : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 3/2 → Continuous (fun t : ℝ => G (σ + t * I)) := by
    intro σ h1 h2
    refine Continuous.mul ?_ (hDc σ h1 h2)
    exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))
  have hnx : ∀ u : ℂ, ‖(x : ℂ) ^ (-u)‖ = x ^ (-u.re) := by
    intro u; rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  set Cx : ℝ := x ^ (-(3/2 : ℝ)) + x ^ (-(1/2 : ℝ)) with hCx
  have hGb : ∀ u : ℂ, 1/2 ≤ u.re → u.re ≤ 3/2 → 1 ≤ |u.im| → ‖G u‖ ≤ (Cx * CD) / u.im ^ 2 := by
    intro u h1 h2 ht
    rw [hG, norm_mul, hnx]
    have hx' : x ^ (-u.re) ≤ Cx := rpow_le_add_of_mem hx (by linarith) (by linarith)
    have hd := hCD u h1 h2 ht
    have hCD0 : 0 ≤ CD / u.im ^ 2 := (norm_nonneg _).trans hd
    calc x ^ (-u.re) * ‖P.D u‖ ≤ Cx * (CD / u.im ^ 2) :=
          mul_le_mul hx' hd (norm_nonneg _) (by positivity)
      _ = Cx * CD / u.im ^ 2 := by ring
  have hint : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 3/2 → Integrable (fun t : ℝ => G (σ + t * I)) := by
    intro σ h1 h2
    refine integrable_of_cont_decay (hGc σ h1 h2) (Cx * CD) (fun t ht => ?_)
    have := hGb (σ + t * I) (by simp; linarith) (by simp; linarith) (by simpa using ht)
    simpa using this
  have hshift := vline_eq_of_differentiable (G := G) (a := 1/2) (b := 3/2) (by norm_num)
    (fun s h1 h2 => ((differentiableAt_id.neg).const_cpow
      (Or.inl (by exact_mod_cast hx.ne'))).mul (P.Dd s h1 h2))
    (hint (1/2) (by norm_num) (by norm_num)) (hint (3/2) (by norm_num) (by norm_num))
    (Cx * CD) hGb
  simp only [mellinInv, smul_eq_mul]
  congr 1

/-- Integrability of the dual data on a vertical line of the strip. -/
theorem integrable_D_line {f : ℝ → ℂ} (P : P2Data K f) {σ : ℝ} (h1 : 1/2 ≤ σ) (h2 : σ ≤ 3/2) :
    Integrable (fun t : ℝ => P.D (σ + t * I)) := by
  obtain ⟨CD, hCD⟩ := P.Dbd
  refine integrable_of_cont_decay ?_ CD (fun t ht => ?_)
  · refine continuous_iff_continuousAt.2 (fun t => ?_)
    exact ((P.Dd _ (by simp; linarith) (by simp; linarith)).continuousAt).comp (by fun_prop)
  · have := hCD (σ + t * I) (by simp; linarith) (by simp; linarith) (by simpa using ht)
    simpa using this

/-- The transform of `f` is the inverse Mellin transform of the dual data on `Re u = 3/2`. -/
theorem transform_eq {f : ℝ → ℂ} (P : P2Data K f) {x : ℝ} (hx : 0 < x) :
    qsTransform K f x = mellinInv (3/2) P.D x := by
  rw [mellinInv_shift_D P hx, qsTransform]
  simp only [mellinInv]
  congr 2
  funext t
  have hre : (((1/2 : ℝ) : ℂ) + t * I).re = 1/2 := by simp
  have hu1 : ((1/2 : ℝ) : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h1re : (1 - (((1/2 : ℝ) : ℂ) + t * I)).re = 1/2 := by simp; norm_num
  rw [P.Deq _ (by rw [hre]) (by rw [hre]; norm_num) hu1,
    P.mel _ (by rw [h1re]; norm_num) (by rw [h1re]; norm_num)]

/-- `Ψ(1) = ρ_K Φ(1)`. -/
theorem Ψ_one [IsTotallyComplex K] {f : ℝ → ℂ} (P : P2Data K f) :
    P.Ψ 1 = (qsResidueOne K : ℂ) * P.Φ 1 := by
  set g : ℂ → ℂ := fun s => s * Z1 K s * P.Φ s with hg
  have hgc : ContinuousAt g 1 :=
    (continuousAt_id.mul (differentiable_Z1 (K := K) 1).continuousAt).mul P.Φc1
  have hΨc : ContinuousAt P.Ψ 1 := (P.Ψd 1 (by norm_num) (by norm_num)).continuousAt
  have hev : P.Ψ =ᶠ[𝓝[≠] 1] g := by
    have hball : Metric.ball (1 : ℂ) (1/2) ∈ 𝓝[≠] (1 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (by norm_num))
    filter_upwards [hball, self_mem_nhdsWithin] with s hs hs1
    have hd : |s.re - 1| < 1/2 := by
      have := Complex.abs_re_le_norm (s - 1)
      rw [Metric.mem_ball, Complex.dist_eq] at hs
      simp at this
      linarith
    have h1 : 1/2 < s.re := by linarith [abs_lt.mp hd]
    have h2 : s.re < 3/2 := by linarith [abs_lt.mp hd]
    have hs0 : s ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
    exact P.Ψeq s (by linarith) h2.le hs0 hs1
  have hlim1 : Tendsto P.Ψ (𝓝[≠] 1) (𝓝 (g 1)) :=
    (hgc.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  have hlim2 : Tendsto P.Ψ (𝓝[≠] 1) (𝓝 (P.Ψ 1)) := hΨc.tendsto.mono_left nhdsWithin_le_nhds
  rw [tendsto_nhds_unique hlim2 hlim1, hg]
  simp only [one_mul]
  rw [Z1_one]

/-- `R_K(f) = -Ψ(0)`. -/
theorem residueZero_eq [IsTotallyComplex K] {f : ℝ → ℂ} (P : P2Data K f) :
    qsResidueZero K f = -P.Ψ 0 := by
  unfold qsResidueZero
  apply Filter.Tendsto.limUnder_eq
  have hc : ContinuousAt (fun t : ℝ => P.Ψ (t : ℂ) / ((t : ℂ) - 1)) 0 := by
    refine ContinuousAt.div ?_ (by fun_prop) (by simp)
    exact ((P.Ψd ((0:ℝ):ℂ) (by simp; norm_num) (by simp; norm_num)).continuousAt).comp
      Complex.continuous_ofReal.continuousAt
  have hlim : Tendsto (fun t : ℝ => P.Ψ (t : ℂ) / ((t : ℂ) - 1)) (𝓝[>] 0) (𝓝 (-P.Ψ 0)) := by
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simp only [Complex.ofReal_zero, zero_sub, div_neg, div_one] at this
    exact this
  refine hlim.congr' ?_
  have hmem : Set.Ioo (0:ℝ) (1/2) ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hmem] with t ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
  have ht1 : (t : ℂ) ≠ 1 := by
    intro h; have : t = 1 := by exact_mod_cast h
    linarith [ht.2]
  have htm1 : (t : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hre : ((t : ℂ)).re = t := by simp
  rw [P.Ψeq _ (by rw [hre]; linarith [ht.1]) (by rw [hre]; linarith [ht.2]) ht0 ht1,
    Z1_eq ht1 (not_nonpos_int_of_re_pos (by rw [hre]; exact ht.1)),
    P.mel _ (by rw [hre]; exact ht.1) (by rw [hre]; linarith [ht.2])]
  field_simp

instance countable_ideal_ok : Countable (Ideal (𝓞 K)) := by
  have h : (Set.univ : Set (Ideal (𝓞 K))) = ⋃ n : ℕ, {I | Ideal.absNorm I ≤ n} := by
    ext I
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨Ideal.absNorm I, le_rfl⟩
  have hc : (Set.univ : Set (Ideal (𝓞 K))).Countable := by
    rw [h]
    exact Set.countable_iUnion (fun n => (Ideal.finite_setOfPred_absNorm_le n).countable)
  exact Set.countable_univ_iff.mp hc

/-- Real norm of a nonzero ideal. -/
abbrev nb (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) : ℝ := ((Ideal.absNorm b.1 : ℕ) : ℝ)

theorem nb_pos (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) : 0 < nb b := by
  have : Ideal.absNorm b.1 ≠ 0 := fun h => b.2 (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.pos_of_ne_zero this

theorem summable_nb_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} => nb b ^ (-σ)) :=
  summable_norm_rpow hσ

/-- Mellin inversion, Dirichlet series, Fubini: the left-hand side as a line integral. -/
theorem lhs_eq [IsTotallyComplex K] {f : ℝ → ℂ} (P : P2Data K f) {Y : ℝ} (hY : 0 < Y) :
    Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} => ‖f (nb b / Y)‖) ∧
    ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, f (nb b / Y) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, (Y : ℂ) ^ (((3/2 : ℝ) : ℂ) + t * I) *
        qsZetaCont K (((3/2 : ℝ) : ℂ) + t * I) * P.Φ (((3/2 : ℝ) : ℂ) + t * I) := by
  set s : ℝ → ℂ := fun t => ((3/2 : ℝ) : ℂ) + t * I with hsdef
  have hsre : ∀ t, (s t).re = 3/2 := by intro t; simp [hsdef]
  set A : ℝ := ∫ t : ℝ, ‖P.Φ (s t)‖ with hA
  have hxb : ∀ b : {I : Ideal (𝓞 K) // I ≠ ⊥}, 0 < nb b / Y := fun b => div_pos (nb_pos b) hY
  -- the terms
  set F : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ → ℂ :=
    fun b t => ((nb b / Y : ℝ) : ℂ) ^ (-(s t)) * P.Φ (s t) with hF
  have hFn : ∀ b t, ‖F b t‖ = (nb b / Y) ^ (-(3/2 : ℝ)) * ‖P.Φ (s t)‖ := by
    intro b t
    rw [hF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hxb b)]
    simp [hsre]
  have hFi : ∀ b, Integrable (F b) := by
    intro b
    refine Integrable.mono' (P.Φint.norm.const_mul ((nb b / Y) ^ (-(3/2 : ℝ)))) ?_
      (Eventually.of_forall fun t => le_of_eq (hFn b t))
    refine AEStronglyMeasurable.mul ?_ P.Φint.aestronglyMeasurable
    refine Continuous.aestronglyMeasurable ?_
    exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast (hxb b).ne'))
  have hcoef : ∀ b : {I : Ideal (𝓞 K) // I ≠ ⊥},
      (nb b / Y) ^ (-(3/2 : ℝ)) = nb b ^ (-(3/2 : ℝ)) * Y ^ (3/2 : ℝ) := by
    intro b
    rw [Real.div_rpow (nb_pos b).le hY.le, Real.rpow_neg hY.le, div_inv_eq_mul]
  have hsumc : Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} => (nb b / Y) ^ (-(3/2 : ℝ))) := by
    simp_rw [hcoef]
    exact (summable_nb_rpow (σ := 3/2) (by norm_num)).mul_right _
  have hFint : Summable (fun b => ∫ t : ℝ, ‖F b t‖) := by
    simp_rw [hFn, integral_const_mul]
    exact hsumc.mul_right _
  have hrep : ∀ b, f (nb b / Y) = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F b t := by
    intro b
    rw [P.inv _ (hxb b), mellinInv, Complex.real_smul]
    rfl
  constructor
  · refine Summable.of_nonneg_of_le (fun b => norm_nonneg _) (fun b => ?_)
      (hsumc.mul_right ((1 / (2 * Real.pi)) * A))
    rw [P.inv _ (hxb b)]
    refine (norm_mellinInv_le _ _ (hxb b)).trans (le_of_eq ?_)
    rw [hA]
    ring
  · simp_rw [hrep]
    rw [tsum_mul_left, integral_tsum_of_summable_integral_norm hFi hFint]
    congr 1
    congr 1
    funext t
    have hsum : ∑' b, F b t = (Y : ℂ) ^ (s t) * dedekindZeta K (s t) * P.Φ (s t) := by
      have hb : ∀ b : {I : Ideal (𝓞 K) // I ≠ ⊥}, F b t =
          ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (-(s t)) * ((Y : ℂ) ^ (s t) * P.Φ (s t)) := by
        intro b
        rw [hF]
        simp only
        rw [ofReal_div_cpow_neg (nb_pos b) hY, Complex.ofReal_natCast]
        ring
      simp_rw [hb]
      rw [tsum_mul_right, (hasSum_norm_cpow (by rw [hsre]; norm_num)).tsum_eq]
      ring
    rw [hsum, qsZetaCont_eq_dedekindZeta (by rw [hsre]; norm_num)]

/-- The left line `Re s = -1/2`: functional equation, dual Dirichlet series, Fubini. -/
theorem left_line_eq [IsTotallyComplex K] {f : ℝ → ℂ} (P : P2Data K f) {Y : ℝ} (hY : 0 < Y) :
    Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} => ‖qsTransform K f (Y * nb b)‖) ∧
    ∫ t : ℝ, (Y : ℂ) ^ (((-1/2 : ℝ) : ℂ) + t * I) * P.Ψ (((-1/2 : ℝ) : ℂ) + t * I) *
        ((((-1/2 : ℝ) : ℂ) + t * I) * ((((-1/2 : ℝ) : ℂ) + t * I) - 1))⁻¹ =
      ((2 * Real.pi : ℝ) : ℂ) * Y * ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
        qsTransform K f (Y * nb b) := by
  set a : ℝ → ℂ := fun t => ((-1/2 : ℝ) : ℂ) + t * I with hadef
  set u : ℝ → ℂ := fun t => 1 - a t with hudef
  have hare : ∀ t, (a t).re = -1/2 := by intro t; simp [hadef]
  have hure : ∀ t, (u t).re = 3/2 := by intro t; simp [hudef, hadef]; norm_num
  have huim : ∀ t, (u t).im = -t := by intro t; simp [hudef, hadef]
  have ha0 : ∀ t, a t ≠ 0 := by
    intro t h; have := hare t; rw [h] at this; simp at this; norm_num at this
  have ha1 : ∀ t, a t ≠ 1 := by
    intro t h; have := hare t; rw [h] at this; simp at this; norm_num at this
  have hu1 : ∀ t, u t ≠ 1 := by
    intro t h; have := hure t; rw [h] at this; simp at this; norm_num at this
  have hanint : ∀ t, ∀ m : ℕ, a t ≠ -m := by
    intro t
    refine not_nonpos_int_of_re_not_int (fun m hm => ?_)
    rw [hare] at hm
    have : (2 : ℝ) * m = -1 := by linarith
    have h' : (2 * m : ℤ) = -1 := by exact_mod_cast this
    omega
  have hunint : ∀ t, ∀ m : ℕ, 1 - a t ≠ -m := fun t =>
    not_nonpos_int_of_re_pos (by rw [show 1 - a t = u t from rfl, hure]; norm_num)
  obtain ⟨CD, hCD⟩ := P.Dbd
  -- integrability of `t ↦ D(u t)`
  have hDu : Integrable (fun t : ℝ => P.D (u t)) := by
    refine integrable_of_cont_decay ?_ CD (fun t ht => ?_)
    · refine continuous_iff_continuousAt.2 (fun t => ?_)
      exact ((P.Dd _ (by rw [hure]; norm_num) (by rw [hure])).continuousAt).comp
        (by simp only [hudef, hadef]; fun_prop)
    · have := hCD (u t) (by rw [hure]; norm_num) (by rw [hure]) (by rw [huim, abs_neg]; exact ht)
      rwa [huim, neg_sq] at this
  set AD : ℝ := ∫ t : ℝ, ‖P.D (u t)‖ with hAD
  -- the integrand as a series
  set G : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ → ℂ :=
    fun b t => (Y : ℂ) ^ (a t) * P.D (u t) * ((nb b : ℝ) : ℂ) ^ (-(u t)) with hG
  have hpoint : ∀ t, (Y : ℂ) ^ (a t) * P.Ψ (a t) * ((a t) * ((a t) - 1))⁻¹ = ∑' b, G b t := by
    intro t
    have hΨ := P.Ψeq (a t) (by rw [hare]) (by rw [hare]; norm_num) (ha0 t) (ha1 t)
    rw [Z1_eq (ha1 t) (hanint t)] at hΨ
    have hfe := qsZetaCont_fe (K := K) (ha0 t) (ha1 t) (hanint t) (hunint t)
    have hD := P.Deq (u t) (by rw [hure]; norm_num) (by rw [hure]) (hu1 t)
    rw [show 1 - u t = a t by simp [hudef]] at hD
    have hZ : qsZetaCont K (u t) = ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
        ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (-(u t)) := by
      rw [qsZetaCont_eq_dedekindZeta (by rw [hure]; norm_num),
        (hasSum_norm_cpow (by rw [hure]; norm_num)).tsum_eq]
    have hne : (a t) * ((a t) - 1) ≠ 0 := mul_ne_zero (ha0 t) (sub_ne_zero.mpr (ha1 t))
    calc (Y : ℂ) ^ (a t) * P.Ψ (a t) * ((a t) * ((a t) - 1))⁻¹
        = (Y : ℂ) ^ (a t) * (qsGammaRatio K (1 - a t) * P.Φ (a t)) *
            qsZetaCont K (1 - a t) := by
          have ha' := ha0 t
          have hb' : a t - 1 ≠ 0 := sub_ne_zero.mpr (ha1 t)
          rw [hΨ, hfe]
          field_simp
      _ = (Y : ℂ) ^ (a t) * P.D (u t) * qsZetaCont K (u t) := by
          rw [hD]
      _ = ∑' b, G b t := by
          rw [hZ, ← tsum_mul_left]
          congr 1
  have hGn : ∀ b t, ‖G b t‖ = Y ^ (-(1/2 : ℝ)) * ‖P.D (u t)‖ * nb b ^ (-(3/2 : ℝ)) := by
    intro b t
    rw [hG]
    simp only
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY,
      Complex.norm_cpow_eq_rpow_re_of_pos (nb_pos b), hare]
    have h3 : (-u t).re = -(3/2 : ℝ) := by rw [Complex.neg_re, hure]
    rw [h3]
    norm_num
  have hGi : ∀ b, Integrable (G b) := by
    intro b
    refine Integrable.mono' ((hDu.norm.const_mul (Y ^ (-(1/2 : ℝ)))).mul_const
      (nb b ^ (-(3/2 : ℝ)))) ?_ (Eventually.of_forall fun t => le_of_eq (hGn b t))
    refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ hDu.aestronglyMeasurable) ?_
    · exact (Continuous.const_cpow (by simp only [hadef]; fun_prop)
        (Or.inl (by exact_mod_cast hY.ne'))).aestronglyMeasurable
    · exact (Continuous.const_cpow (by simp only [hudef, hadef]; fun_prop)
        (Or.inl (by exact_mod_cast (nb_pos b).ne'))).aestronglyMeasurable
  have hGint : Summable (fun b => ∫ t : ℝ, ‖G b t‖) := by
    simp_rw [hGn]
    have : ∀ b : {I : Ideal (𝓞 K) // I ≠ ⊥}, (∫ t : ℝ, Y ^ (-(1/2 : ℝ)) * ‖P.D (u t)‖ *
        nb b ^ (-(3/2 : ℝ))) = Y ^ (-(1/2 : ℝ)) * AD * nb b ^ (-(3/2 : ℝ)) := by
      intro b
      rw [integral_mul_const, integral_const_mul]
    simp_rw [this]
    exact (summable_nb_rpow (σ := 3/2) (by norm_num)).mul_left _
  -- each term
  have hterm : ∀ b, ∫ t : ℝ, G b t = ((2 * Real.pi : ℝ) : ℂ) * Y * qsTransform K f (Y * nb b) := by
    intro b
    have hYb : 0 < Y * nb b := mul_pos hY (nb_pos b)
    rw [transform_eq P hYb, mellinInv, Complex.real_smul]
    have hrw : ∀ t, G b t = (Y : ℂ) * ((((Y * nb b : ℝ)) : ℂ) ^ (-(u t)) * P.D (u t)) := by
      intro t
      rw [hG]
      simp only
      have h1 : (Y : ℂ) ^ (a t) = (Y : ℂ) * (Y : ℂ) ^ (-(u t)) := by
        rw [show a t = 1 + -(u t) by simp [hudef], Complex.cpow_add _ _ (by exact_mod_cast hY.ne'),
          Complex.cpow_one]
      rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hY.le (nb_pos b).le]
      ring
    simp_rw [hrw]
    rw [integral_const_mul]
    have hneg : ∫ t : ℝ, (((Y * nb b : ℝ)) : ℂ) ^ (-(u t)) * P.D (u t) =
        ∫ t : ℝ, (((Y * nb b : ℝ)) : ℂ) ^ (-(((3/2 : ℝ) : ℂ) + t * I)) *
          P.D (((3/2 : ℝ) : ℂ) + t * I) := by
      rw [← integral_neg_eq_self]
      congr 1
      funext t
      have : u (-t) = ((3/2 : ℝ) : ℂ) + t * I := by
        simp [hudef, hadef]; ring
      rw [this]
    rw [hneg]
    simp only [smul_eq_mul]
    have hpi : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      rw [mul_one_div_cancel (by positivity)]
      simp
    calc (Y : ℂ) * ∫ t : ℝ, (((Y * nb b : ℝ)) : ℂ) ^ (-(((3/2 : ℝ) : ℂ) + t * I)) *
          P.D (((3/2 : ℝ) : ℂ) + t * I)
        = ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) * (Y : ℂ) *
            ∫ t : ℝ, (((Y * nb b : ℝ)) : ℂ) ^ (-(((3/2 : ℝ) : ℂ) + t * I)) *
              P.D (((3/2 : ℝ) : ℂ) + t * I) := by rw [hpi, one_mul]
      _ = _ := by ring
  constructor
  · refine Summable.of_nonneg_of_le (fun b => norm_nonneg _) (fun b => ?_)
      ((summable_nb_rpow (σ := 3/2) (by norm_num)).mul_left
        ((1 / (2 * Real.pi)) * Y ^ (-(3/2 : ℝ)) * ∫ t : ℝ, ‖P.D (((3/2 : ℝ) : ℂ) + t * I)‖))
    have hYb : 0 < Y * nb b := mul_pos hY (nb_pos b)
    rw [transform_eq P hYb]
    refine (norm_mellinInv_le _ _ hYb).trans (le_of_eq ?_)
    rw [Real.mul_rpow hY.le (nb_pos b).le]
    ring
  · rw [funext hpoint, ← integral_tsum_of_summable_integral_norm hGi hGint]
    simp_rw [hterm]
    rw [tsum_mul_left]

/-- **Abstract P2.** -/
theorem p2_core [IsTotallyComplex K] {f : ℝ → ℂ} (P : P2Data K f) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} => ‖f ((Ideal.absNorm b.1 : ℝ) / Y)‖) ∧
      Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        ‖qsTransform K f (Y * (Ideal.absNorm b.1 : ℝ))‖) ∧
      ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, f ((Ideal.absNorm b.1 : ℝ) / Y) =
        (qsResidueOne K : ℂ) * (Y : ℂ) * mellin f 1 + qsResidueZero K f +
          (Y : ℂ) * ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            qsTransform K f (Y * (Ideal.absNorm b.1 : ℝ)) := by
  obtain ⟨hs1, hL⟩ := lhs_eq P hY
  obtain ⟨hs2, hR⟩ := left_line_eq P hY
  refine ⟨hs1, hs2, ?_⟩
  obtain ⟨CΨ, hCΨ⟩ := P.Ψbd
  set Ψ' : ℂ → ℂ := fun s => (Y : ℂ) ^ s * P.Ψ s with hΨ'
  have hΨ'd : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 → DifferentiableAt ℂ Ψ' s := fun s h1 h2 =>
    (differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hY.ne'))).mul (P.Ψd s h1 h2)
  set CY : ℝ := Y ^ (-1/2 : ℝ) + Y ^ (3/2 : ℝ) with hCY
  have hdecay : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
      ‖Ψ' s * (s * (s - 1))⁻¹‖ ≤ (CY * CΨ) / s.im ^ 2 := by
    intro s h1 h2 ht
    have hns : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hns1 : |s.im| ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1); simpa using this
    have him2 : 0 < s.im ^ 2 := by nlinarith [abs_nonneg s.im, sq_abs s.im]
    have hden : s.im ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by
      rw [← sq_abs]; nlinarith [abs_nonneg s.im]
    have hYs : ‖(Y : ℂ) ^ s‖ ≤ CY := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
      exact rpow_le_add_of_mem hY h1 h2
    have hΨb := hCΨ s h1 h2
    have hCΨ0 : 0 ≤ CΨ := (norm_nonneg _).trans hΨb
    rw [hΨ', norm_mul, norm_mul, norm_inv, norm_mul]
    have hpos : 0 < ‖s‖ * ‖s - 1‖ := lt_of_lt_of_le him2 hden
    rw [mul_inv_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ him2]
    calc ‖(Y : ℂ) ^ s‖ * ‖P.Ψ s‖ * s.im ^ 2 ≤ CY * CΨ * s.im ^ 2 := by
          gcongr
      _ ≤ CY * CΨ * (‖s‖ * ‖s - 1‖) := by
          gcongr
  have hcontline : ∀ σ : ℝ, -1/2 ≤ σ → σ ≤ 3/2 → σ ≠ 0 → σ ≠ 1 →
      Continuous (fun t : ℝ => Ψ' (σ + t * I) * ((σ + t * I) * ((σ + t * I) - 1))⁻¹) := by
    intro σ h1 h2 h0 h1'
    refine continuous_iff_continuousAt.2 (fun t => ?_)
    refine ContinuousAt.mul (((hΨ'd _ (by simp; linarith) (by simp; linarith)).continuousAt).comp
      (by fun_prop)) (ContinuousAt.inv₀ (by fun_prop) ?_)
    refine mul_ne_zero ?_ ?_
    · intro h; apply h0; have := congrArg Complex.re h; simpa using this
    · intro h; apply h1'; have := congrArg Complex.re h; simp at this; linarith
  have hintline : ∀ σ : ℝ, -1/2 ≤ σ → σ ≤ 3/2 → σ ≠ 0 → σ ≠ 1 →
      Integrable (fun t : ℝ => Ψ' (σ + t * I) * ((σ + t * I) * ((σ + t * I) - 1))⁻¹) := by
    intro σ h1 h2 h0 h1'
    refine integrable_of_cont_decay (hcontline σ h1 h2 h0 h1') (CY * CΨ) (fun t ht => ?_)
    have := hdecay (σ + t * I) (by simp; linarith) (by simp; linarith) (by simpa using ht)
    simpa using this
  have hshift := vline_sub_two_poles (Ψ := Ψ') (a := -1/2) (b := 3/2) (by norm_num) (by norm_num)
    hΨ'd (hintline (-1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (hintline (3/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (CY * CΨ) hdecay
  -- the right line integrand is `Y^s Z(s) Φ(s)`
  have hright : (∫ t : ℝ, Ψ' (((3/2 : ℝ) : ℂ) + t * I) *
      ((((3/2 : ℝ) : ℂ) + t * I) * ((((3/2 : ℝ) : ℂ) + t * I) - 1))⁻¹) =
      ∫ t : ℝ, (Y : ℂ) ^ (((3/2 : ℝ) : ℂ) + t * I) * qsZetaCont K (((3/2 : ℝ) : ℂ) + t * I) *
        P.Φ (((3/2 : ℝ) : ℂ) + t * I) := by
    congr 1
    funext t
    set z : ℂ := ((3/2 : ℝ) : ℂ) + t * I with hz
    have hzre : z.re = 3/2 := by simp [hz]
    have hz0 : z ≠ 0 := by intro h; rw [h] at hzre; norm_num at hzre
    have hz1 : z ≠ 1 := by intro h; rw [h] at hzre; norm_num at hzre
    simp only [hΨ']
    rw [P.Ψeq z (by rw [hzre]; norm_num) (by rw [hzre]) hz0 hz1,
      Z1_eq hz1 (not_nonpos_int_of_re_pos (by rw [hzre]; norm_num))]
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    field_simp
  -- assemble
  have hleft' : (∫ t : ℝ, Ψ' (((-1/2 : ℝ) : ℂ) + t * I) *
      ((((-1/2 : ℝ) : ℂ) + t * I) * ((((-1/2 : ℝ) : ℂ) + t * I) - 1))⁻¹) =
      ((2 * Real.pi : ℝ) : ℂ) * Y * ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
        qsTransform K f (Y * nb b) := by
    rw [← hR]
  have hΨ1 : Ψ' 1 = (Y : ℂ) * ((qsResidueOne K : ℂ) * mellin f 1) := by
    simp only [hΨ']
    rw [Complex.cpow_one, Ψ_one P, P.mel 1 (by norm_num) (by norm_num)]
  have hΨ0 : Ψ' 0 = -qsResidueZero K f := by
    simp only [hΨ']
    rw [Complex.cpow_zero, one_mul, residueZero_eq P, neg_neg]
  -- `hshift`: right − left = 2π (Ψ' 1 − Ψ' 0)
  have hL' : ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, f ((Ideal.absNorm b.1 : ℝ) / Y) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, Ψ' (((3/2 : ℝ) : ℂ) + t * I) *
        ((((3/2 : ℝ) : ℂ) + t * I) * ((((3/2 : ℝ) : ℂ) + t * I) - 1))⁻¹ := by
    rw [hright]; exact hL
  rw [hL']
  have hsh : (∫ t : ℝ, Ψ' (((3/2 : ℝ) : ℂ) + t * I) *
        ((((3/2 : ℝ) : ℂ) + t * I) * ((((3/2 : ℝ) : ℂ) + t * I) - 1))⁻¹) =
      ((2 * Real.pi : ℝ) : ℂ) * Y * ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
        qsTransform K f (Y * nb b) + 2 * Real.pi * (Ψ' 1 - Ψ' 0) := by
    rw [← hleft']
    have := hshift
    simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_ofNat] at this ⊢
    linear_combination this
  rw [hsh, hΨ1, hΨ0]
  have hpi : ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, one_div_mul_cancel (by positivity)]
    simp
  have hpi' : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) = 1 := by
    rw [← hpi]; push_cast; ring
  linear_combination (Y * ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, qsTransform K f (Y * nb b)) * hpi +
    ((Y : ℂ) * ((qsResidueOne K : ℂ) * mellin f 1) - -qsResidueZero K f) * hpi'

end ArtinPrimitiveRoots.A2.QSP2
