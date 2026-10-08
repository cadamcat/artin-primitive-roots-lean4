import OAI.NumberTheory.DirichletL.ContinuationContour

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rows_sol

/-- The Gaussian simple-pole correction vanishes on the horizontal sides of
an expanding rectangle, including when the real pole lies in the strip. -/
theorem gaussian_pole_horizontal_vanish (a b p : ℝ) (hab : a ≤ b) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      Complex.exp ((((x : ℂ) + (-T) * Complex.I) - p) ^ 2) /
        (((x : ℂ) + (-T) * Complex.I) - p)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      Complex.exp ((((x : ℂ) + T * Complex.I) - p) ^ 2) /
        (((x : ℂ) + T * Complex.I) - p)) atTop (𝓝 0) := by
  let B : ℝ := max |a - p| |b - p|
  have hB : 0 ≤ B := (abs_nonneg (a - p)).trans (le_max_left _ _)
  have hsq (x : ℝ) (hx : x ∈ Icc a b) : (x - p) ^ 2 ≤ B ^ 2 := by
    have ha : |a - p| ≤ B := le_max_left _ _
    have hb : |b - p| ≤ B := le_max_right _ _
    have hax := neg_abs_le (a - p)
    have hbx := le_abs_self (b - p)
    have hxabs : |x - p| ≤ B := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    nlinarith [sq_abs (x - p), abs_nonneg (x - p)]
  have hbound (x t : ℝ) (hx : x ∈ Icc a b) (ht : 1 ≤ |t|) :
      ‖Complex.exp ((((x : ℂ) + t * Complex.I) - p) ^ 2) /
        (((x : ℂ) + t * Complex.I) - p)‖ ≤
          Real.exp (B ^ 2) * Real.exp (-(t ^ 2)) := by
    let z : ℂ := ((x : ℂ) + t * Complex.I) - p
    have hzre : z.re = x - p := by simp [z]
    have hzim : z.im = t := by simp [z]
    have hzsq : (z ^ 2).re = (x - p) ^ 2 - t ^ 2 := by
      rw [pow_two, Complex.mul_re, hzre, hzim]
      ring
    have hden : 1 ≤ ‖z‖ := ht.trans (by simpa [hzim] using Complex.abs_im_le_norm z)
    change ‖Complex.exp (z ^ 2) / z‖ ≤ _
    rw [norm_div, Complex.norm_exp, hzsq]
    calc
      _ ≤ Real.exp ((x - p) ^ 2 - t ^ 2) / 1 :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hden
      _ ≤ Real.exp (B ^ 2 - t ^ 2) := by
        simp only [div_one]
        exact Real.exp_le_exp.mpr (sub_le_sub_right (hsq x hx) _)
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add]
  have hexp : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by decide)))
  have hlim : Tendsto
      (fun T : ℝ => Real.exp (B ^ 2) * Real.exp (-(T ^ 2)) * |b - a|)
      atTop (𝓝 0) := by
    simpa using (hexp.const_mul (Real.exp (B ^ 2))).mul_const |b - a|
  have htail (T : ℝ) (hT : 1 ≤ T) (t : ℝ) (ht : |t| = T) :
      ‖∫ x : ℝ in a..b,
        Complex.exp ((((x : ℂ) + t * Complex.I) - p) ^ 2) /
          (((x : ℂ) + t * Complex.I) - p)‖ ≤
            Real.exp (B ^ 2) * Real.exp (-(T ^ 2)) * |b - a| := by
    have ht2 : t ^ 2 = T ^ 2 := by rw [← ht, sq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Icc a b := by
      simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx
    simpa [ht2] using hbound x t hx' (by rwa [ht])
  constructor <;> apply tendsto_zero_iff_norm_tendsto_zero.mpr
  · apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    simpa only [Complex.ofReal_neg] using
      htail T hT (-T) (by rw [abs_neg, abs_of_nonneg (by linarith)])
  · apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact htail T hT T (abs_of_nonneg (by linarith))

/-- Recover the simple-pole residue after subtracting its Gaussian correction.
Endpoint integrability and horizontal decay are required for the original
integrand; the corresponding facts for its holomorphic regularization follow. -/
theorem simple_pole_shift_of_regularization
    (a b p : ℝ) (F G : ℂ → ℂ) (res c : ℂ)
    (hap : a < p) (hpb : p < b)
    (hG : DifferentiableOn ℂ G {z : ℂ | a ≤ z.re ∧ z.re ≤ b})
    (hreg : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ p →
      F z = G z + res * Complex.exp ((z - p) ^ 2) / (z - p))
    (ha : Integrable (fun t : ℝ => F ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => F ((b : ℂ) + t * Complex.I)))
    (hKa : Integrable (fun t : ℝ =>
      Complex.exp ((((a : ℂ) + t * Complex.I) - p) ^ 2) /
        (((a : ℂ) + t * Complex.I) - p)))
    (hKb : Integrable (fun t : ℝ =>
      Complex.exp ((((b : ℂ) + t * Complex.I) - p) ^ 2) /
        (((b : ℂ) + t * Complex.I) - p)))
    (hVa : c * (∫ t : ℝ,
      Complex.exp ((((a : ℂ) + t * Complex.I) - p) ^ 2) /
        (((a : ℂ) + t * Complex.I) - p)) = (-1 / 2 : ℂ))
    (hVb : c * (∫ t : ℝ,
      Complex.exp ((((b : ℂ) + t * Complex.I) - p) ^ 2) /
        (((b : ℂ) + t * Complex.I) - p)) = (1 / 2 : ℂ))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      F ((x : ℂ) + (-T) * Complex.I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      F ((x : ℂ) + T * Complex.I)) atTop (𝓝 0)) :
    c * (∫ t : ℝ, F ((b : ℂ) + t * Complex.I)) =
      c * (∫ t : ℝ, F ((a : ℂ) + t * Complex.I)) + res := by
  let K : ℂ → ℂ := fun z => Complex.exp ((z - p) ^ 2) / (z - p)
  have hab : a ≤ b := hap.le.trans hpb.le
  have hreg' (z : ℂ) (hzlo : a ≤ z.re) (hzhi : z.re ≤ b) (hzne : z ≠ p) :
      F z = G z + res * K z := by
    simpa only [K, mul_div_assoc] using hreg z hzlo hzhi hzne
  have hreal_ne (x t : ℝ) (hx : x ≠ p) :
      (x : ℂ) + t * Complex.I ≠ p := by
    intro h
    apply hx
    simpa using congrArg Complex.re h
  have him_ne (x t : ℝ) (ht : t ≠ 0) :
      (x : ℂ) + t * Complex.I ≠ p := by
    intro h
    apply ht
    simpa using congrArg Complex.im h
  have hpoint (x t : ℝ) (hx : x ∈ Icc a b) (hne : (x : ℂ) + t * Complex.I ≠ p) :
      F ((x : ℂ) + t * Complex.I) =
        G ((x : ℂ) + t * Complex.I) + res * K ((x : ℂ) + t * Complex.I) :=
    hreg' _ (by simpa using hx.1) (by simpa using hx.2) hne
  have hGa : Integrable (fun t : ℝ => G ((a : ℂ) + t * Complex.I)) := by
    apply (ha.sub (hKa.const_mul res)).congr
    filter_upwards [] with t
    change F ((a : ℂ) + t * Complex.I) - res * K ((a : ℂ) + t * Complex.I) = _
    exact sub_eq_iff_eq_add.mpr
      (hpoint a t ⟨le_rfl, hab⟩ (hreal_ne a t (ne_of_lt hap)))
  have hGb : Integrable (fun t : ℝ => G ((b : ℂ) + t * Complex.I)) := by
    apply (hb.sub (hKb.const_mul res)).congr
    filter_upwards [] with t
    change F ((b : ℂ) + t * Complex.I) - res * K ((b : ℂ) + t * Complex.I) = _
    exact sub_eq_iff_eq_add.mpr
      (hpoint b t ⟨hab, le_rfl⟩ (hreal_ne b t (ne_of_gt hpb)))
  have hhorizontal (t : ℝ) (ht : t ≠ 0) :
      (∫ x : ℝ in a..b, F ((x : ℂ) + t * Complex.I)) =
        (∫ x : ℝ in a..b, G ((x : ℂ) + t * Complex.I)) +
          res * ∫ x : ℝ in a..b, K ((x : ℂ) + t * Complex.I) := by
    have hGcont : ContinuousOn (fun x : ℝ => G ((x : ℂ) + t * Complex.I)) (Icc a b) := by
      apply hG.continuousOn.comp
        (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + t * Complex.I) (Icc a b))
      intro x hx
      change a ≤ ((x : ℂ) + t * Complex.I).re ∧ ((x : ℂ) + t * Complex.I).re ≤ b
      simpa using hx
    have hKcont : Continuous (fun x : ℝ => K ((x : ℂ) + t * Complex.I)) := by
      change Continuous (fun x : ℝ =>
        Complex.exp ((((x : ℂ) + t * Complex.I) - p) ^ 2) /
          (((x : ℂ) + t * Complex.I) - p))
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro x
      exact sub_ne_zero.mpr (him_ne x t ht)
    have hGi : IntervalIntegrable (fun x : ℝ => G ((x : ℂ) + t * Complex.I)) volume a b :=
      hGcont.intervalIntegrable_of_Icc hab
    have hKi : IntervalIntegrable (fun x : ℝ => K ((x : ℂ) + t * Complex.I)) volume a b :=
      hKcont.intervalIntegrable a b
    calc
      _ = ∫ x : ℝ in a..b,
          G ((x : ℂ) + t * Complex.I) + res * K ((x : ℂ) + t * Complex.I) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc a b := by simpa [uIcc_of_le hab] using hx
        exact hpoint x t hx' (him_ne x t ht)
      _ = _ := by
        rw [intervalIntegral.integral_add hGi (hKi.const_mul res),
          intervalIntegral.integral_const_mul]
  obtain ⟨hKbot, hKtop⟩ := gaussian_pole_horizontal_vanish a b p hab
  change Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
    K ((x : ℂ) + (-T) * Complex.I)) atTop (𝓝 0) at hKbot
  change Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
    K ((x : ℂ) + T * Complex.I)) atTop (𝓝 0) at hKtop
  have hGbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      G ((x : ℂ) + (-T) * Complex.I)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ =>
        (∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * Complex.I)) -
          res * (∫ x : ℝ in a..b, K ((x : ℂ) + (-T) * Complex.I))) atTop (𝓝 0) := by
      simpa using hbot.sub (hKbot.const_mul res)
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have heq : (∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * Complex.I)) =
        (∫ x : ℝ in a..b, G ((x : ℂ) + (-T) * Complex.I)) +
          res * ∫ x : ℝ in a..b, K ((x : ℂ) + (-T) * Complex.I) := by
      simpa only [Complex.ofReal_neg] using
        hhorizontal (-T) (neg_ne_zero.mpr (ne_of_gt hT))
    exact sub_eq_iff_eq_add.mpr heq
  have hGtop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      G ((x : ℂ) + T * Complex.I)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ =>
        (∫ x : ℝ in a..b, F ((x : ℂ) + T * Complex.I)) -
          res * (∫ x : ℝ in a..b, K ((x : ℂ) + T * Complex.I))) atTop (𝓝 0) := by
      simpa using htop.sub (hKtop.const_mul res)
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact sub_eq_iff_eq_add.mpr (hhorizontal T (ne_of_gt hT))
  have hshift := OAI.SevenEighths.Continuation.vertical_integral_eq_of_horizontal_vanish
    G hab hG hGa hGb hGbot hGtop
  have hInta : (∫ t : ℝ, F ((a : ℂ) + t * Complex.I)) =
      (∫ t : ℝ, G ((a : ℂ) + t * Complex.I)) +
        res * ∫ t : ℝ, K ((a : ℂ) + t * Complex.I) := by
    calc
      _ = ∫ t : ℝ, G ((a : ℂ) + t * Complex.I) +
          res * K ((a : ℂ) + t * Complex.I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hpoint a t ⟨le_rfl, hab⟩ (hreal_ne a t (ne_of_lt hap))
      _ = _ := by rw [integral_add hGa (hKa.const_mul res), integral_const_mul]
  have hIntb : (∫ t : ℝ, F ((b : ℂ) + t * Complex.I)) =
      (∫ t : ℝ, G ((b : ℂ) + t * Complex.I)) +
        res * ∫ t : ℝ, K ((b : ℂ) + t * Complex.I) := by
    calc
      _ = ∫ t : ℝ, G ((b : ℂ) + t * Complex.I) +
          res * K ((b : ℂ) + t * Complex.I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hpoint b t ⟨hab, le_rfl⟩ (hreal_ne b t (ne_of_gt hpb))
      _ = _ := by rw [integral_add hGb (hKb.const_mul res), integral_const_mul]
  change c * (∫ t : ℝ, K ((a : ℂ) + t * Complex.I)) = (-1 / 2 : ℂ) at hVa
  change c * (∫ t : ℝ, K ((b : ℂ) + t * Complex.I)) = (1 / 2 : ℂ) at hVb
  have hValA : c * (∫ t : ℝ, F ((a : ℂ) + t * Complex.I)) =
      c * (∫ t : ℝ, G ((a : ℂ) + t * Complex.I)) + res * (-1 / 2 : ℂ) := by
    rw [hInta]
    calc
      _ = c * (∫ t : ℝ, G ((a : ℂ) + t * Complex.I)) +
          res * (c * ∫ t : ℝ, K ((a : ℂ) + t * Complex.I)) := by ring
      _ = _ := by rw [hVa]
  have hValB : c * (∫ t : ℝ, F ((b : ℂ) + t * Complex.I)) =
      c * (∫ t : ℝ, G ((b : ℂ) + t * Complex.I)) + res * (1 / 2 : ℂ) := by
    rw [hIntb]
    calc
      _ = c * (∫ t : ℝ, G ((b : ℂ) + t * Complex.I)) +
          res * (c * ∫ t : ℝ, K ((b : ℂ) + t * Complex.I)) := by ring
      _ = _ := by rw [hVb]
  rw [hValA, hValB, hshift]
  ring

end ArtinPrimitiveRoots.Proofs.a2_rows_sol
