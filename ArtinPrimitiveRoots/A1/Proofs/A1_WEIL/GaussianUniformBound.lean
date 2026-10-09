import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianFiniteScale
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Core
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness

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

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
