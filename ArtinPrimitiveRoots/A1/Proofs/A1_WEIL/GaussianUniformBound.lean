import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianFiniteScale
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.AdditiveOrthogonality
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Core
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

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
Finite square classes and the checked finite-ball rescaling
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
-/
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

/-- An integer-radius valuation ball is an additive subgroup of the completion. -/
def localBallAddSubgroup (v : FinPlace F) (M : ℤ) : AddSubgroup (v.adicCompletion F) where
  carrier := localBallInt v M
  zero_mem' := by
    change Valued.v (0 : v.adicCompletion F) ≤ WithZero.exp M
    rw [map_zero]
    exact bot_le
  add_mem' := by
    intro x y hx hy
    change Valued.v x ≤ WithZero.exp M at hx
    change Valued.v y ≤ WithZero.exp M at hy
    change Valued.v (x + y) ≤ WithZero.exp M
    exact (map_add_le_max
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) x y).trans
      (max_le hx hy)
  neg_mem' := by
    intro x hx
    change Valued.v x ≤ WithZero.exp M at hx
    change Valued.v (-x) ≤ WithZero.exp M
    simpa only [Valuation.map_neg] using hx

/-- Orthogonality of the frozen additive character on each actual local ball.
The value is its Haar mass when t↦ψ(t*z) is trivial on the ball, and zero otherwise.
Compactness and the native valuation supply the measurable
additive subgroup needed by the generic orthogonality theorem. -/
theorem local_ball_character_orthogonality (A : AddCharData F)
    (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (M : ℤ) (z : v.adicCompletion F) :
    (∫ t in localBallInt v M, A.ψ v (t * z) ∂μ) =
      if ∀ t ∈ localBallInt v M, A.ψ v (t * z) = 1
      then ((μ (localBallInt v M)).toReal : ℂ) else 0 := by
  have : Measure.IsAddHaarMeasure μ := hμ
  let χ : AddChar (v.adicCompletion F) ℂ :=
    { toFun := fun t => A.ψ v (t * z)
      map_zero_eq_one' := by simp only [zero_mul, AddChar.map_zero_eq_one]
      map_add_eq_mul' := fun t u => by rw [add_mul, AddChar.map_add_eq_mul] }
  exact integral_addChar_addSubgroup μ (localBallAddSubgroup v M)
    (integer_radius_ball_compact v M).measurableSet χ

/-- A finite Gaussian Fourier test is exactly a quadratic preimage measure.
Both integration domains are compact, and character regularity gives product
integrability before Fubini. The local-ball orthogonality identity then evaluates
the inner character integral. -/
theorem finite_gaussian_fourier_test (A : AddCharData F) (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) (hμ : Measure.IsAddHaarMeasure μ)
    (hregular : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) (M : ℤ) (N : ℕ) :
    (∫ t in localBallInt v M, A.ψ v (-t) *
      (∫ x in localBall v N, A.ψ v ((a : v.adicCompletion F) * t * x ^ 2) ∂μ) ∂μ) =
      ((μ (localBallInt v M)).toReal : ℂ) *
        ((μ {x | x ∈ localBall v N ∧ ∀ t ∈ localBallInt v M,
          A.ψ v (t * ((a : v.adicCompletion F) * x ^ 2 - 1)) = 1}).toReal : ℂ) := by
  have : Measure.IsAddHaarMeasure μ := hμ
  let T := localBallInt v M
  let B := localBall v N
  have hTmeas : MeasurableSet T := (integer_radius_ball_compact v M).measurableSet
  have hBmeas : MeasurableSet B := (integer_radius_ball_compact v (N : ℤ)).measurableSet
  have hTfinite : μ T < ⊤ := (integer_radius_ball_compact v M).measure_lt_top
  have hBfinite : μ B < ⊤ := (integer_radius_ball_compact v (N : ℤ)).measure_lt_top
  have : IsFiniteMeasure (μ.restrict T) := isFiniteMeasure_restrict.mpr hTfinite.ne
  have : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.mpr hBfinite.ne
  let g := fun (t x : v.adicCompletion F) =>
    A.ψ v (t * ((a : v.adicCompletion F) * x ^ 2 - 1))
  have hcont : Continuous (Function.uncurry g) :=
    hregular.1.comp (continuous_fst.mul
      ((continuous_const.mul (continuous_snd.pow 2)).sub continuous_const))
  have hgint : Integrable (Function.uncurry g) ((μ.restrict T).prod (μ.restrict B)) :=
    (integrable_const (1 : ℝ)).mono' hcont.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => (hregular.2.2
        (p.1 * ((a : v.adicCompletion F) * p.2 ^ 2 - 1))).le)
  let S : Set (v.adicCompletion F) :=
    {x | ∀ t ∈ T, A.ψ v (t * ((a : v.adicCompletion F) * x ^ 2 - 1)) = 1}
  have hSclosed : IsClosed S := by
    have hsets : S = ⋂ t ∈ T,
        {x : v.adicCompletion F | A.ψ v (t * ((a : v.adicCompletion F) * x ^ 2 - 1)) = 1} := by
      ext x
      simp only [S, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [hsets]
    apply isClosed_biInter
    intro t _ht
    exact isClosed_eq (hregular.1.comp (continuous_const.mul
      ((continuous_const.mul (continuous_id.pow 2)).sub continuous_const))) continuous_const
  have hproduct : ∀ t x : v.adicCompletion F,
      A.ψ v (-t) * A.ψ v ((a : v.adicCompletion F) * t * x ^ 2) = g t x := by
    intro t x
    dsimp [g]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc
    (∫ t in localBallInt v M, A.ψ v (-t) *
      (∫ x in localBall v N, A.ψ v ((a : v.adicCompletion F) * t * x ^ 2) ∂μ) ∂μ) =
        ∫ t in T, ∫ x in B, g t x ∂μ ∂μ := by
      apply setIntegral_congr_fun hTmeas
      intro t _ht
      change A.ψ v (-t) *
        (∫ x in B, A.ψ v ((a : v.adicCompletion F) * t * x ^ 2) ∂μ) =
          ∫ x in B, g t x ∂μ
      rw [← integral_const_mul]
      exact setIntegral_congr_fun hBmeas fun x _hx => hproduct t x
    _ = ∫ x in B, ∫ t in T, g t x ∂μ ∂μ := integral_integral_swap hgint
    _ = ∫ x in B, ((μ T).toReal : ℂ) * S.indicator (fun _ => (1 : ℂ)) x ∂μ := by
      apply setIntegral_congr_fun hBmeas
      intro x _hx
      change (∫ t in localBallInt v M,
        A.ψ v (t * ((a : v.adicCompletion F) * x ^ 2 - 1)) ∂μ) = _
      rw [local_ball_character_orthogonality A v μ hμ M]
      change (if x ∈ S then ((μ T).toReal : ℂ) else 0) =
        ((μ T).toReal : ℂ) * S.indicator (fun _ => (1 : ℂ)) x
      by_cases hx : x ∈ S
      · rw [ite_eq_left hx, Set.indicator_of_mem hx, mul_one]
      · rw [ite_eq_right hx, Set.indicator_of_notMem hx, mul_zero]
    _ = ((μ T).toReal : ℂ) * ∫ x in B, S.indicator (fun _ => (1 : ℂ)) x ∂μ :=
      integral_const_mul _ _
    _ = ((μ T).toReal : ℂ) * ((μ (B ∩ S)).toReal : ℂ) := by
      rw [setIntegral_indicator hSclosed.measurableSet, setIntegral_const]
      simp only [measureReal_def, Complex.real_smul, mul_one]
    _ = _ := rfl

/-- The annihilator of the actual integer-radius frequency ball. -/
def localBallAnnihilator (A : AddCharData F) (v : FinPlace F) (M : ℤ) :
    Set (v.adicCompletion F) :=
  {z | ∀ t ∈ localBallInt v M, A.ψ v (t * z) = 1}

/-- Enlarging the frequency ball makes its character annihilator arbitrarily small.
Integrality retains the opposite-radius ball inside the annihilator. A witness
to nontriviality excludes every z whose norm is at least r by testing at y/z.
This geometry needs neither continuity nor Haar measure. -/
theorem local_ball_annihilator_small (A : AddCharData F) (v : FinPlace F)
    (hψ : A.ψ v ≠ 1) (r : ℝ) (hr : 0 < r) :
    ∃ M : ℤ, localBallInt v (-M) ⊆ localBallAnnihilator A v M ∧
      localBallAnnihilator A v M ⊆ Metric.ball (0 : v.adicCompletion F) r := by
  have hex : ∃ y : v.adicCompletion F, A.ψ v y ≠ 1 := by
    by_contra h
    push Not at h
    apply hψ
    ext y
    simpa only [AddChar.one_apply] using h y
  obtain ⟨y, hy⟩ := hex
  have hy0 : y ≠ 0 := by
    intro h
    apply hy
    simp only [h, AddChar.map_zero_eq_one]
  have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  obtain ⟨c₀, hc₀⟩ :=
    HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1))
  have hc₀0 : c₀ ≠ 0 := by
    intro h
    apply WithZero.exp_ne_zero (a := (-1 : ℤ))
    exact hc₀.symm.trans (by simp only [h, map_zero])
  let c := Units.mk0 c₀ hc₀0
  have hc : ‖(c : v.adicCompletion F)‖ < 1 := by
    apply (Valued.toNormedField.norm_lt_one_iff (L := v.adicCompletion F)
      (Γ₀ := WithZero (Multiplicative ℤ))).mpr
    change Valued.v c₀ < 1
    rw [hc₀, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hr hynorm) hc
  let b : (v.adicCompletion F)ˣ := (c ^ n)⁻¹
  let M := WithZero.log
    ((Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (b : _))
  have hb : Valued.v (b : v.adicCompletion F) = WithZero.exp M := by
    exact (WithZero.exp_log ((map_ne_zero
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr
      b.ne_zero)).symm
  have hbnorm : 0 < ‖(b : v.adicCompletion F)‖ := norm_pos_iff.mpr b.ne_zero
  have hratio : ‖y‖ / ‖(b : v.adicCompletion F)‖ < r := by
    have hb_norm : ‖(b : v.adicCompletion F)‖ =
        (‖(c : v.adicCompletion F)‖ ^ n)⁻¹ := by simp [b]
    rw [hb_norm, div_inv_eq_mul]
    simpa only [mul_comm] using (lt_div_iff₀ hynorm).mp hn
  refine ⟨M, ?_, ?_⟩
  · intro z hz t ht
    apply A.integral v
    change Valued.v (t * z) ≤ 1
    change Valued.v t ≤ WithZero.exp M at ht
    change Valued.v z ≤ WithZero.exp (-M) at hz
    calc
      Valued.v (t * z) = Valued.v t * Valued.v z := map_mul _ _ _
      _ ≤ WithZero.exp M * WithZero.exp (-M) := mul_le_mul' ht hz
      _ = 1 := by rw [← WithZero.exp_add]; simp only [add_neg_cancel, WithZero.exp_zero]
  · intro z hz
    by_contra h
    have hzr : r ≤ ‖z‖ := by
      simpa only [Metric.mem_ball, dist_zero_right, not_lt] using h
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans_le hzr)
    have htest : ‖y / z‖ ≤ ‖(b : v.adicCompletion F)‖ := by
      rw [norm_div]
      apply le_trans (div_le_div_of_nonneg_left (norm_nonneg y) hr hzr)
      apply le_of_lt
      apply (div_lt_iff₀ hr).mpr
      simpa only [mul_comm] using (div_lt_iff₀ hbnorm).mp hratio
    have ht : y / z ∈ localBallInt v M := by
      change Valued.v (y / z) ≤ WithZero.exp M
      rw [← hb]
      exact (Valued.toNormedField.norm_le_iff (L := v.adicCompletion F)
        (Γ₀ := WithZero (Multiplicative ℤ))).mp htest
    apply hy
    simpa only [div_mul_cancel₀ _ hz0] using hz (y / z) ht

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
