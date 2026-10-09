import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianFiniteScale
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Core
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

local instance uniformBoundMeasurable (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) :=
  borel _
local instance uniformBoundBorel (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem integer_ball_compact (v : FinPlace F) : IsCompact (localBallInt v 0) := by
  have hset : localBallInt v 0 = Metric.closedBall (0 : v.adicCompletion F) 1 := by
    ext x
    simpa only [localBallInt, Set.mem_ofPred_eq, WithZero.exp_zero,
      Metric.mem_closedBall, dist_zero_right] using
      (Valued.toNormedField.norm_le_one_iff (L := v.adicCompletion F)
        (Γ₀ := WithZero (Multiplicative ℤ)) (x := x)).symm
  rw [hset]
  exact isCompact_closedBall 0 1

private theorem integer_radius_ball_compact (v : FinPlace F) (N : ℤ) :
    IsCompact (localBallInt v N) := by
  obtain ⟨b, hb⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp N)
  have hb0 : b ≠ 0 := by
    intro h
    apply WithZero.exp_ne_zero (a := N)
    exact hb.symm.trans (by simp only [h, map_zero])
  have hpre : (fun x : v.adicCompletion F => b * x) ⁻¹' localBallInt v N =
      localBallInt v 0 := by
    ext x
    change Valued.v (b * x) ≤ WithZero.exp N ↔ Valued.v x ≤ 1
    rw [map_mul, hb]
    simpa only [mul_one] using
      (mul_le_mul_iff_right₀ (WithZero.exp_pos (a := N)) :
        WithZero.exp N * Valued.v x ≤ WithZero.exp N * 1 ↔ Valued.v x ≤ 1)
  have himage : (fun x : v.adicCompletion F => b * x) '' localBallInt v 0 =
      localBallInt v N := by
    rw [← hpre]
    exact Set.image_preimage_eq _ (Homeomorph.mulLeft₀ b hb0).surjective
  rw [← himage]
  exact (integer_ball_compact v).image (continuous_const.mul continuous_id)

private theorem representative_integrals_bounded (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (hchar : ∀ x, ‖A.ψ v x‖ ≤ 1) (a : (v.adicCompletion F)ˣ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℤ, ‖quadraticIntegralInt A v (W.measure v) a N‖ ≤ C := by
  have : Measure.IsAddHaarMeasure (W.measure v) := W.isHaar v
  let L := W.cutoff v a
  let B := localBallInt v (L : ℤ)
  have hfinite : W.measure v B < ⊤ := (integer_radius_ball_compact v (L : ℤ)).measure_lt_top
  let C := 1 + ‖W.stableValue v a‖ + (W.measure v B).toReal
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N
  by_cases hN : (L : ℤ) ≤ N
  · have hN0 : 0 ≤ N := (Int.natCast_nonneg L).trans hN
    have hNN : L ≤ N.toNat := by
      exact_mod_cast (show (L : ℤ) ≤ (N.toNat : ℤ) by
        simpa only [Int.toNat_of_nonneg hN0] using hN)
    have hstable : quadraticIntegralInt A v (W.measure v) a N = W.stableValue v a := by
      rw [← Int.toNat_of_nonneg hN0]
      exact W.stable v a N.toNat hNN
    rw [hstable]
    dsimp [C]
    linarith [ENNReal.toReal_nonneg (a := W.measure v B)]
  · have hsub : localBallInt v N ⊆ B := by
      intro x hx
      exact hx.trans (WithZero.exp_le_exp.mpr ((le_total N (L : ℤ)).resolve_right hN))
    have hmeasure : W.measure v (localBallInt v N) ≤ W.measure v B := measure_mono hsub
    have hfiniteN := hmeasure.trans_lt hfinite
    have hbound : ‖quadraticIntegralInt A v (W.measure v) a N‖ ≤
        (W.measure v (localBallInt v N)).toReal := by
      simpa only [one_mul, quadraticIntegralInt, measureReal_def] using
        (norm_setIntegral_le_of_norm_le_const_ae (μ := W.measure v)
          (f := fun x => A.ψ v ((a : v.adicCompletion F) * x ^ 2)) (C := 1) hfiniteN
          (Filter.Eventually.of_forall fun x => hchar ((a : v.adicCompletion F) * x ^ 2)))
    have hreal := ENNReal.toReal_mono hfinite.ne hmeasure
    refine (hbound.trans hreal).trans ?_
    dsimp [C]
    linarith [norm_nonneg (W.stableValue v a)]

private theorem finite_square_representatives (v : FinPlace F) :
    ∃ R : Finset (v.adicCompletion F)ˣ, ∀ t : (v.adicCompletion F)ˣ,
      ∃ r ∈ R, ∃ c : (v.adicCompletion F)ˣ, t = r * c ^ 2 := by
  classical
  let _ : ValuativeRel (v.adicCompletion F) := a1_hilbert_sol.completionValuativeRel v
  have : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    a1_hilbert_sol.completionIsLocalField v
  let H : Subgroup (v.adicCompletion F)ˣ :=
    (powMonoidHom 2 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range
  have : Finite ((v.adicCompletion F)ˣ ⧸ H) :=
    LocalFieldTheory.finite_nthPowerQuotient_of_natCast_ne_zero (v.adicCompletion F) 2
      (by norm_num)
  let : Fintype ((v.adicCompletion F)ˣ ⧸ H) := Fintype.ofFinite _
  let rep : ((v.adicCompletion F)ˣ ⧸ H) → (v.adicCompletion F)ˣ := Quotient.out
  refine ⟨Finset.univ.image rep, ?_⟩
  intro t
  let q : (v.adicCompletion F)ˣ ⧸ H := QuotientGroup.mk t
  refine ⟨rep q, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
  have hq : (QuotientGroup.mk (rep q) : (v.adicCompletion F)ˣ ⧸ H) =
      QuotientGroup.mk t := Quotient.out_eq' q
  have hmem : (rep q)⁻¹ * t ∈ H := QuotientGroup.eq.mp hq
  obtain ⟨c, hc⟩ := hmem
  have hc' : c ^ 2 = (rep q)⁻¹ * t := hc
  refine ⟨c, ?_⟩
  calc
    t = rep q * ((rep q)⁻¹ * t) := by simp
    _ = rep q * c ^ 2 := by rw [hc']

private theorem inverse_square_norm_factor (v : FinPlace F) (r c : (v.adicCompletion F)ˣ) :
    ‖(c : v.adicCompletion F)‖⁻¹ =
      ‖(r : v.adicCompletion F)‖ ^ (1 / 2 : ℝ) *
        ‖((r * c ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ^ (-(1 / 2 : ℝ)) := by
  have hc : 0 < ‖(c : v.adicCompletion F)‖ := norm_pos_iff.mpr c.ne_zero
  have hr : 0 < ‖(r : v.adicCompletion F)‖ := norm_pos_iff.mpr r.ne_zero
  have hhalf : (‖(c : v.adicCompletion F)‖ ^ 2) ^ (1 / 2 : ℝ) =
      ‖(c : v.adicCompletion F)‖ := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.pow_rpow_inv_natCast hc.le (by norm_num : (2 : ℕ) ≠ 0)
  rw [Real.rpow_neg (norm_nonneg _) (1 / 2 : ℝ), Units.val_mul,
    Units.val_pow_eq_pow_val, norm_mul, norm_pow, Real.mul_rpow hr.le (sq_nonneg _), hhalf]
  field_simp [(Real.rpow_pos_of_pos hr (1 / 2 : ℝ)).ne', hc.ne']

/-- A common inverse-square-root bound for every finite Gaussian truncation.
Character modulus and the actual scalar measure Jacobian are explicit hypotheses.
Guide: PROOFS.md:466–475. Finite square classes and the checked finite-ball rescaling
reduce all coefficients to finitely many uniformly bounded representative integrals. -/
theorem uniform_quadratic_integral_norm_bound (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (hchar : ∀ x, ‖A.ψ v x‖ ≤ 1)
    (hscale : ∀ c : (v.adicCompletion F)ˣ,
      Measure.map (fun x : v.adicCompletion F => (c : v.adicCompletion F) * x) (W.measure v) =
        (ENNReal.ofReal ‖(c : v.adicCompletion F)‖)⁻¹ • W.measure v) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : (v.adicCompletion F)ˣ) (N : ℕ),
      ‖quadraticIntegral A v (W.measure v) t N‖ ≤
        C * ‖(t : v.adicCompletion F)‖ ^ (-(1 / 2 : ℝ)) := by
  classical
  obtain ⟨R, hR⟩ := finite_square_representatives v
  choose B hBpos hB using representative_integrals_bounded A W v hchar
  let C := 1 + ∑ r ∈ R, B r * ‖(r : v.adicCompletion F)‖ ^ (1 / 2 : ℝ)
  have hsum : 0 ≤ ∑ r ∈ R, B r * ‖(r : v.adicCompletion F)‖ ^ (1 / 2 : ℝ) := by
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (hBpos r).le (Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro t N
  obtain ⟨r, hr, c, rfl⟩ := hR t
  have hcval : Valued.v (c : v.adicCompletion F) ≠ 0 :=
    (map_ne_zero (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr
      c.ne_zero
  let k := WithZero.log (Valued.v (c : v.adicCompletion F))
  have hck : Valued.v (c : v.adicCompletion F) = WithZero.exp k :=
    (WithZero.exp_log hcval).symm
  have hcp : 0 < ‖(c : v.adicCompletion F)‖ := norm_pos_iff.mpr c.ne_zero
  have hrescale := quadratic_integral_square_scale_int A v (W.measure v) r c
    ‖(c : v.adicCompletion F)‖ hcp (hscale c) (N : ℤ) k hck
  have hcoef : B r * ‖(r : v.adicCompletion F)‖ ^ (1 / 2 : ℝ) ≤ C := by
    have hle : B r * ‖(r : v.adicCompletion F)‖ ^ (1 / 2 : ℝ) ≤
        ∑ s ∈ R, B s * ‖(s : v.adicCompletion F)‖ ^ (1 / 2 : ℝ) :=
      Finset.single_le_sum (fun s _ => mul_nonneg (hBpos s).le
        (Real.rpow_nonneg (norm_nonneg (s : v.adicCompletion F)) (1 / 2 : ℝ))) hr
    dsimp [C]
    linarith
  calc
    ‖quadraticIntegral A v (W.measure v) (r * c ^ 2) N‖ =
        ‖(c : v.adicCompletion F)‖⁻¹ *
          ‖quadraticIntegralInt A v (W.measure v) r ((N : ℤ) + k)‖ := by
      change ‖quadraticIntegralInt A v (W.measure v) (r * c ^ 2) (N : ℤ)‖ = _
      rw [hrescale, norm_mul, norm_inv, Complex.norm_of_nonneg hcp.le]
    _ ≤ ‖(c : v.adicCompletion F)‖⁻¹ * B r :=
      mul_le_mul_of_nonneg_left (hB r ((N : ℤ) + k)) (inv_nonneg.mpr hcp.le)
    _ = (B r * ‖(r : v.adicCompletion F)‖ ^ (1 / 2 : ℝ)) *
        ‖((r * c ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ^ (-(1 / 2 : ℝ)) := by
      rw [inverse_square_norm_factor v r c]
      ring
    _ ≤ C * ‖((r * c ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ^
        (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (norm_nonneg _) _)

private theorem scaled_closed_ball_measure_real (v : FinPlace F)
    (μ : Measure (v.adicCompletion F))
    (hscale : ∀ c : (v.adicCompletion F)ˣ,
      Measure.map (fun x : v.adicCompletion F => (c : v.adicCompletion F) * x) μ =
        (ENNReal.ofReal ‖(c : v.adicCompletion F)‖)⁻¹ • μ)
    (u : (v.adicCompletion F)ˣ) (R : ℝ) :
    (μ (Metric.closedBall 0 (R * ‖(u : v.adicCompletion F)‖))).toReal =
      ‖(u : v.adicCompletion F)‖ * (μ (Metric.closedBall 0 R)).toReal := by
  have hu : 0 < ‖(u : v.adicCompletion F)‖ := norm_pos_iff.mpr u.ne_zero
  have hpre : (fun x : v.adicCompletion F => ((u⁻¹ : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) * x) ⁻¹' Metric.closedBall 0 R =
      Metric.closedBall 0 (R * ‖(u : v.adicCompletion F)‖) := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      Units.val_inv_eq_inv_val, norm_mul, norm_inv]
    rw [inv_mul_eq_div, div_le_iff₀ hu]
  have h := congrArg (fun m : Measure (v.adicCompletion F) =>
    (m (Metric.closedBall 0 R)).toReal) (hscale u⁻¹)
  have hm : Measurable (fun x : v.adicCompletion F =>
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm measurableSet_closedBall, hpre, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv] at h
  simpa only [Units.val_inv_eq_inv_val, norm_inv,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hu.le), inv_inv] using h

private theorem geometric_annulus_factor (R ρ : ℝ) (hR : 0 < R) (hρ : 0 < ρ)
    (n : ℕ) :
    (R * ρ ^ (n + 1)) ^ (-(1 / 2 : ℝ)) * ρ ^ n =
      R ^ (-(1 / 2 : ℝ)) * ρ ^ (-(1 / 2 : ℝ)) * (ρ ^ (1 / 2 : ℝ)) ^ n := by
  rw [Real.mul_rpow hR.le (pow_nonneg hρ.le _)]
  have hp : (ρ ^ (n + 1)) ^ (-(1 / 2 : ℝ)) * ρ ^ n =
      ρ ^ (-(1 / 2 : ℝ)) * (ρ ^ (1 / 2 : ℝ)) ^ n := by
    simp only [← Real.rpow_natCast, ← Real.rpow_mul hρ.le,
      ← Real.rpow_add hρ, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  rw [mul_assoc, hp, ← mul_assoc]

private theorem inverse_sqrt_norm_integrableOn_closedBall (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) [Measure.IsAddHaarMeasure μ]
    (hscale : ∀ c : (v.adicCompletion F)ˣ,
      Measure.map (fun x : v.adicCompletion F => (c : v.adicCompletion F) * x) μ =
        (ENNReal.ofReal ‖(c : v.adicCompletion F)‖)⁻¹ • μ)
    (c : (v.adicCompletion F)ˣ) (hc : ‖(c : v.adicCompletion F)‖ < 1)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x : v.adicCompletion F => ‖x‖ ^ (-(1 / 2 : ℝ)))
      (Metric.closedBall 0 R) μ := by
  let ρ := ‖(c : v.adicCompletion F)‖
  have hρ : 0 < ρ := norm_pos_iff.mpr c.ne_zero
  let f := fun x : v.adicCompletion F => ‖x‖ ^ (-(1 / 2 : ℝ))
  let B := fun n : ℕ => Metric.closedBall (0 : v.adicCompletion F) (R * ρ ^ n)
  let S := fun n : ℕ => B n \ B (n + 1)
  let K := fun n : ℕ => (R * ρ ^ (n + 1)) ^ (-(1 / 2 : ℝ))
  have hmeas : AEStronglyMeasurable f μ := by
    apply Measurable.aestronglyMeasurable
    dsimp [f]
    fun_prop
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_closedBall.diff measurableSet_closedBall
  have hBfinite : ∀ n, μ (B n) < ⊤ := fun n => (isCompact_closedBall _ _).measure_lt_top
  have hSfinite : ∀ n, μ (S n) < ⊤ := fun n =>
    (measure_mono Set.sdiff_subset).trans_lt (hBfinite n)
  have hbound : ∀ n x, x ∈ S n → ‖f x‖ ≤ K n := by
    intro n x hx
    have hxnorm : R * ρ ^ (n + 1) < ‖x‖ := by
      simpa only [B, Metric.mem_closedBall, dist_zero_right, not_le] using hx.2
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hR (pow_pos hρ _)) hxnorm.le (by norm_num)
  have hint : ∀ n, IntegrableOn f (S n) μ := by
    intro n
    apply Measure.integrableOn_of_bounded (hSfinite n).ne hmeas
    filter_upwards [ae_restrict_mem (hSmeas n)] with x hx
    exact hbound n x hx
  have hmass : ∀ n, (μ (B n)).toReal = ρ ^ n * (μ (B 0)).toReal := by
    intro n
    simpa only [B, pow_zero, mul_one, ρ, Units.val_pow_eq_pow_val, norm_pow] using
      scaled_closed_ball_measure_real v μ hscale (c ^ n) R
  have hintegral : ∀ n, (∫ x in S n, ‖f x‖ ∂μ) ≤
      (R ^ (-(1 / 2 : ℝ)) * ρ ^ (-(1 / 2 : ℝ)) * (μ (B 0)).toReal) *
        (ρ ^ (1 / 2 : ℝ)) ^ n := by
    intro n
    have hnorm : (∫ x in S n, ‖f x‖ ∂μ) ≤ K n * (μ (S n)).toReal := by
      simpa only [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (f x)),
        norm_norm, measureReal_def] using
        norm_setIntegral_le_of_norm_le_const (μ := μ) (f := fun x => ‖f x‖)
          (hSfinite n) (fun x hx => by simpa only [norm_norm] using hbound n x hx)
    have hmassle : (μ (S n)).toReal ≤ (μ (B n)).toReal :=
      ENNReal.toReal_mono (hBfinite n).ne (measure_mono Set.sdiff_subset)
    calc
      (∫ x in S n, ‖f x‖ ∂μ) ≤ K n * (μ (S n)).toReal := hnorm
      _ ≤ K n * (μ (B n)).toReal :=
        mul_le_mul_of_nonneg_left hmassle
          (Real.rpow_nonneg (mul_nonneg hR.le (pow_nonneg hρ.le _)) _)
      _ = _ := by
        rw [hmass, ← mul_assoc, geometric_annulus_factor R ρ hR hρ]
        ring
  have hsum : Summable fun n : ℕ => ∫ x in S n, ‖f x‖ ∂μ := by
    exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg (f x))
      hintegral ((summable_geometric_of_lt_one
        (Real.rpow_nonneg hρ.le (1 / 2 : ℝ))
        (Real.rpow_lt_one hρ.le hc (by norm_num : (0 : ℝ) < 1 / 2))).mul_left _)
  have hcover : Metric.closedBall (0 : v.adicCompletion F) R ⊆
      {0} ∪ ⋃ n : ℕ, S n := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hxnorm hR) hc
      have hex : ∃ m : ℕ, R * ρ ^ m < ‖x‖ := by
        refine ⟨m, ?_⟩
        have := (lt_div_iff₀ hR).mp hm
        simpa only [mul_comm] using this
      have hm0 : Nat.find hex ≠ 0 := by
        intro hmzero
        have h := Nat.find_spec hex
        rw [hmzero, pow_zero, mul_one] at h
        exact (Metric.mem_closedBall.mp hx).not_gt (by simpa only [dist_zero_right] using h)
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_, ?_⟩
      · have hnot := Nat.find_min hex (show n < Nat.find hex by omega)
        simpa only [B, Metric.mem_closedBall, dist_zero_right] using le_of_not_gt hnot
      · have hlt := Nat.find_spec hex
        simpa only [B, Metric.mem_closedBall, dist_zero_right, hn, Nat.succ_eq_add_one,
          not_le] using hlt
  have hz : IntegrableOn f {0} μ :=
    integrableOn_singleton (hx := (isCompact_singleton (x := (0 : v.adicCompletion F))).measure_lt_top)
  exact ((integrableOn_union.mpr
    ⟨hz, integrableOn_iUnion_of_summable_integral_norm hint hsum⟩)).mono_set hcover

/-- The inverse-square-root Gaussian bound is integrable on each integer-radius ball.
The scalar Haar Jacobian remains explicit. Geometric metric annuli prove the local
integrability needed for dominated convergence of the actual finite Gaussian integrals.
Guide: PROOFS.md:468–475. -/
theorem inverse_sqrt_norm_integrableOn_localBallInt (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F)
    (hscale : ∀ c : (v.adicCompletion F)ˣ,
      Measure.map (fun x : v.adicCompletion F => (c : v.adicCompletion F) * x) (W.measure v) =
        (ENNReal.ofReal ‖(c : v.adicCompletion F)‖)⁻¹ • W.measure v)
    (M : ℤ) :
    IntegrableOn (fun x : v.adicCompletion F => ‖x‖ ^ (-(1 / 2 : ℝ)))
      (localBallInt v M) (W.measure v) := by
  have : Measure.IsAddHaarMeasure (W.measure v) := W.isHaar v
  obtain ⟨b, hb⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1))
  have hb0 : b ≠ 0 := by
    intro h
    apply WithZero.exp_ne_zero (a := (-1 : ℤ))
    exact hb.symm.trans (by simp only [h, map_zero])
  let c := Units.mk0 b hb0
  have hc : ‖(c : v.adicCompletion F)‖ < 1 := by
    apply (Valued.toNormedField.norm_lt_one_iff (L := v.adicCompletion F)
      (Γ₀ := WithZero (Multiplicative ℤ))).mpr
    change Valued.v b < 1
    rw [hb, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  obtain ⟨R, hR, hsub⟩ := (integer_radius_ball_compact v M).isBounded.subset_closedBall_lt
    0 (0 : v.adicCompletion F)
  exact (inverse_sqrt_norm_integrableOn_closedBall v (W.measure v) hscale c hc R hR).mono_set hsub

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
