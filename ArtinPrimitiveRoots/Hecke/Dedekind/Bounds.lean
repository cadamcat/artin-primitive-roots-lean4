import DedekindResidue.CompletedZeta.Existence

/-!
Local estimates used in the Dedekind order bound.  These reproduce the required Mellin
strip estimate from the public prebuilt Hecke-pair interface; the larger AINTLIB
`AnalyticControl` module is not prebuilt in the shared dependency set.
-/

open Complex MeasureTheory NumberField NumberField.InfinitePlace
open scoped Real

noncomputable section

set_option maxHeartbeats 1000000

namespace ArtinPrimitiveRoots.Hecke.DedekindBounds

variable (K : Type*) [Field K] [NumberField K]

noncomputable def completedDedekindOrderConstant : ℝ :=
  2 + (|discr K| : ℝ)
    + 2 * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
      + NumberField.InfinitePlace.nrComplexPlaces K)
    + (1 + ∑' n : ℕ, ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖)

private theorem norm_heckeLambda0_le (s : ℂ) :
    ‖(DedekindResidue.heckeFEPair K).Λ₀ s‖
      ≤ ∫ x in Set.Ioi (0:ℝ), x ^ (s.re - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖ := by
  rw [WeakFEPair.Λ₀, mellin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

private theorem integrable_heckeLambda0_norm (a : ℝ) :
    IntegrableOn
      (fun x : ℝ => x ^ (a - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖)
      (Set.Ioi 0) := by
  have hconv : MellinConvergent
      ((DedekindResidue.heckeFEPair K).f_modif) (a : ℂ) :=
    ((DedekindResidue.heckeFEPair K).isStrongFEPair_toStrongFEPair.hasMellin
      (a : ℂ)).1
  have hnn : IntegrableOn
      (fun x : ℝ => ‖((x:ℂ) ^ ((a:ℂ) - 1) • (DedekindResidue.heckeFEPair K).f_modif x)‖)
      (Set.Ioi 0) := hconv.norm
  refine hnn.congr_fun (fun x hx => ?_) measurableSet_Ioi
  show ‖((x:ℂ) ^ ((a:ℂ) - 1) • (DedekindResidue.heckeFEPair K).f_modif x)‖
    = x ^ (a - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

private theorem exists_heckeLambda0_strip_bound (a b : ℝ) :
    ∃ B : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖(DedekindResidue.heckeFEPair K).Λ₀ s‖ ≤ B := by
  refine ⟨(∫ x in Set.Ioi (0:ℝ), x ^ (a - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖)
    + ∫ x in Set.Ioi (0:ℝ), x ^ (b - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖, ?_⟩
  intro s ha hb
  refine le_trans (norm_heckeLambda0_le K s) ?_
  have hmono : ∀ x ∈ Set.Ioi (0:ℝ),
      x ^ (s.re - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖
        ≤ x ^ (a - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖
          + x ^ (b - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖ := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    rcases le_or_gt x 1 with hx1 | hx1
    · have h1 : x ^ (s.re - 1) ≤ x ^ (a - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
      have h2 : (0:ℝ) ≤ x ^ (b - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖ := by
        positivity
      nlinarith [norm_nonneg ((DedekindResidue.heckeFEPair K).f_modif x),
        Real.rpow_nonneg hx0.le (s.re - 1)]
    · have h1 : x ^ (s.re - 1) ≤ x ^ (b - 1) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) (by linarith)
      have h2 : (0:ℝ) ≤ x ^ (a - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖ := by
        positivity
      nlinarith [norm_nonneg ((DedekindResidue.heckeFEPair K).f_modif x),
        Real.rpow_nonneg hx0.le (s.re - 1)]
  calc (∫ x in Set.Ioi (0:ℝ), x ^ (s.re - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖)
      ≤ ∫ x in Set.Ioi (0:ℝ),
          (x ^ (a - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖
            + x ^ (b - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖) :=
        setIntegral_mono_on (integrable_heckeLambda0_norm K s.re)
          ((integrable_heckeLambda0_norm K a).add (integrable_heckeLambda0_norm K b))
          measurableSet_Ioi hmono
    _ = (∫ x in Set.Ioi (0:ℝ), x ^ (a - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖)
          + ∫ x in Set.Ioi (0:ℝ), x ^ (b - 1) * ‖(DedekindResidue.heckeFEPair K).f_modif x‖ :=
        integral_add (integrable_heckeLambda0_norm K a) (integrable_heckeLambda0_norm K b)

theorem exists_completedDedekindZetaEntire_strip_bound (a b : ℝ) (hab : a ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖DedekindResidue.completedDedekindZetaEntire K s‖ ≤ B * (1 + ‖s‖)^2 := by
  obtain ⟨B₀, hB₀⟩ := exists_heckeLambda0_strip_bound K (a/2) (b/2)
  have hB₀0 : 0 ≤ B₀ := by
    refine le_trans (norm_nonneg ((DedekindResidue.heckeFEPair K).Λ₀ ((a/2 : ℝ) : ℂ)))
      (hB₀ _ ?_ ?_)
    · simp
    · simp
      linarith
  refine ⟨‖(((DedekindResidue.heckeAdjust K : ℝ) : ℂ))⁻¹‖
    * (B₀ + 2 * ‖(DedekindResidue.heckeFEPair K).f₀‖
      + 2 * ‖(DedekindResidue.heckeFEPair K).g₀‖),
    by positivity, fun s ha hb => ?_⟩
  have hs2 : (s / 2).re = s.re / 2 := by
    rw [show s / 2 = ((1/2 : ℝ) : ℂ) * s by push_cast; ring, Complex.re_ofReal_mul]
    ring
  have hΛ : ‖(DedekindResidue.heckeFEPair K).Λ₀ (s / 2)‖ ≤ B₀ :=
    hB₀ (s/2) (by rw [hs2]; linarith) (by rw [hs2]; linarith)
  have h1s : ‖s‖ ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have h1s1 : ‖s - 1‖ ≤ 1 + ‖s‖ := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 1 + ‖s‖ := by rw [norm_one]; ring
  have hone : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hmain : ‖s * (s - 1) * (DedekindResidue.heckeFEPair K).Λ₀ (s / 2)
      - 2 * (s - 1) * (DedekindResidue.heckeFEPair K).f₀
      + 2 * s * (DedekindResidue.heckeFEPair K).g₀‖
      ≤ (1 + ‖s‖)^2 * (B₀ + 2 * ‖(DedekindResidue.heckeFEPair K).f₀‖
        + 2 * ‖(DedekindResidue.heckeFEPair K).g₀‖) := by
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add_left (norm_sub_le _ _) _) ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    have hsq : 1 + ‖s‖ ≤ (1 + ‖s‖)^2 := by nlinarith [norm_nonneg s]
    have hss : ‖s‖ * ‖s - 1‖ ≤ (1 + ‖s‖)^2 := by
      nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
    have e1 : ‖s‖ * ‖s - 1‖ * ‖(DedekindResidue.heckeFEPair K).Λ₀ (s / 2)‖
        ≤ (1 + ‖s‖)^2 * B₀ :=
      mul_le_mul hss hΛ (norm_nonneg _) (by positivity)
    have e2 : 2 * ‖s - 1‖ * ‖(DedekindResidue.heckeFEPair K).f₀‖
        ≤ (1 + ‖s‖)^2 * (2 * ‖(DedekindResidue.heckeFEPair K).f₀‖) := by
      calc 2 * ‖s - 1‖ * ‖(DedekindResidue.heckeFEPair K).f₀‖
          = ‖s - 1‖ * (2 * ‖(DedekindResidue.heckeFEPair K).f₀‖) := by ring
        _ ≤ (1 + ‖s‖)^2 * (2 * ‖(DedekindResidue.heckeFEPair K).f₀‖) :=
          mul_le_mul_of_nonneg_right (h1s1.trans hsq) (by positivity)
    have e3 : 2 * ‖s‖ * ‖(DedekindResidue.heckeFEPair K).g₀‖
        ≤ (1 + ‖s‖)^2 * (2 * ‖(DedekindResidue.heckeFEPair K).g₀‖) := by
      calc 2 * ‖s‖ * ‖(DedekindResidue.heckeFEPair K).g₀‖
          = ‖s‖ * (2 * ‖(DedekindResidue.heckeFEPair K).g₀‖) := by ring
        _ ≤ (1 + ‖s‖)^2 * (2 * ‖(DedekindResidue.heckeFEPair K).g₀‖) :=
          mul_le_mul_of_nonneg_right (h1s.trans hsq) (by positivity)
    have hdist : (1 + ‖s‖)^2 * (B₀ + 2 * ‖(DedekindResidue.heckeFEPair K).f₀‖
        + 2 * ‖(DedekindResidue.heckeFEPair K).g₀‖)
        = (1 + ‖s‖)^2 * B₀
          + (1 + ‖s‖)^2 * (2 * ‖(DedekindResidue.heckeFEPair K).f₀‖)
          + (1 + ‖s‖)^2 * (2 * ‖(DedekindResidue.heckeFEPair K).g₀‖) := by ring
    rw [hdist]
    linarith
  rw [DedekindResidue.completedDedekindZetaEntire, norm_mul]
  calc ‖(((DedekindResidue.heckeAdjust K : ℝ) : ℂ))⁻¹‖
      * ‖s * (s - 1) * (DedekindResidue.heckeFEPair K).Λ₀ (s / 2)
          - 2 * (s - 1) * (DedekindResidue.heckeFEPair K).f₀
          + 2 * s * (DedekindResidue.heckeFEPair K).g₀‖
      ≤ ‖(((DedekindResidue.heckeAdjust K : ℝ) : ℂ))⁻¹‖
        * ((1 + ‖s‖)^2 * (B₀ + 2 * ‖(DedekindResidue.heckeFEPair K).f₀‖
          + 2 * ‖(DedekindResidue.heckeFEPair K).g₀‖)) :=
        mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
    _ = ‖(((DedekindResidue.heckeAdjust K : ℝ) : ℂ))⁻¹‖
        * (B₀ + 2 * ‖(DedekindResidue.heckeFEPair K).f₀‖
          + 2 * ‖(DedekindResidue.heckeFEPair K).g₀‖) * (1 + ‖s‖)^2 := by ring

private theorem norm_complexGamma_le_realGamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  calc ‖Complex.Gamma z‖
      = ‖∫ x in Set.Ioi (0:ℝ), (↑(-x).exp : ℂ) * (↑x : ℂ) ^ (z - 1)‖ := by
        rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral]
    _ ≤ ∫ x in Set.Ioi (0:ℝ),
          ‖(↑(-x).exp : ℂ) * (↑x : ℂ) ^ (z - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0:ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        change ‖(↑(-x).exp : ℂ) * (↑x : ℂ) ^ (z - 1)‖ = _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos hx]
        rw [show (z - 1).re = z.re - 1 by simp]
    _ = Real.Gamma z.re := (Real.Gamma_eq_integral hz).symm

private theorem real_Gamma_le_exp_growth {x R : ℝ} (hx : 1 ≤ x) (hxR : x ≤ R) :
    Real.Gamma x ≤ Real.exp ((R + 1) * Real.log (R + 2)) := by
  let n : ℕ := ⌈x⌉₊
  have hxn : x ≤ (n : ℝ) := by simpa [n] using Nat.le_ceil x
  have hnx : (n : ℝ) < x + 1 := by
    simpa [n] using Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hgpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
  have hrec : Real.Gamma (x + 1) = x * Real.Gamma x :=
    Real.Gamma_add_one (by linarith)
  have hstep : Real.Gamma x ≤ Real.Gamma (x + 1) := by
    rw [hrec]
    nlinarith
  have hmono : Real.Gamma (x + 1) ≤ Real.Gamma ((n : ℝ) + 1) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp; linarith) (by simp; linarith)
      (by linarith)
  have hfact : Real.Gamma ((n : ℝ) + 1) = (n.factorial : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.Gamma_nat_eq_factorial n
  have hfactpow : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hpow : (n : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log (n : ℝ)) := by
    calc (n : ℝ) ^ n = (Real.exp (Real.log (n : ℝ))) ^ n := by
          rw [Real.exp_log hnpos]
      _ = Real.exp ((n : ℝ) * Real.log (n : ℝ)) := by rw [← Real.exp_nat_mul]
  have hnR : (n : ℝ) ≤ R + 1 := by linarith
  have hlogn : Real.log (n : ℝ) ≤ Real.log (R + 2) :=
    Real.log_le_log hnpos (by linarith)
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hR10 : 0 ≤ R + 1 := by linarith
  have hmul : (n : ℝ) * Real.log (n : ℝ)
      ≤ (R + 1) * Real.log (R + 2) := by
    calc (n : ℝ) * Real.log (n : ℝ)
        ≤ (R + 1) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hnR hlogn0
      _ ≤ (R + 1) * Real.log (R + 2) := mul_le_mul_of_nonneg_left hlogn hR10
  calc Real.Gamma x ≤ Real.Gamma (x + 1) := hstep
    _ ≤ Real.Gamma ((n : ℝ) + 1) := hmono
    _ = (n.factorial : ℝ) := hfact
    _ ≤ (n : ℝ) ^ n := hfactpow
    _ = Real.exp ((n : ℝ) * Real.log (n : ℝ)) := hpow
    _ ≤ Real.exp ((R + 1) * Real.log (R + 2)) := Real.exp_le_exp.mpr hmul

private theorem norm_complexGamma_le_exp_growth {z : ℂ} {R : ℝ}
    (hz : 1 ≤ z.re) (hzR : ‖z‖ ≤ R) :
    ‖Complex.Gamma z‖ ≤ Real.exp ((R + 1) * Real.log (R + 2)) := by
  have hz0 : 0 < z.re := by linarith
  have hre : z.re ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    rw [abs_of_nonneg hz0.le] at h
    exact h
  exact (norm_complexGamma_le_realGamma hz0).trans
    (real_Gamma_le_exp_growth hz (hre.trans hzR))

private theorem norm_dedekindZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖NumberField.dedekindZeta K s‖
      ≤ ∑' n : ℕ, ‖LSeries.term
          (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖ := by
  set f : ℕ → ℂ := fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)
    with hf
  have hsum2 : LSeriesSummable f 2 := by
    have h := DedekindResidue.count_LSeriesSummable K (by norm_num : (1:ℝ) < 2)
    have hfe : (fun n : ℕ =>
        ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) = f := by
      funext n
      rw [hf]
      push_cast
      rfl
    rw [hfe] at h
    exact_mod_cast h
  have hsummS : LSeriesSummable f s := hsum2.of_re_le_re (by simpa using hs)
  have hterm : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ ‖LSeries.term f 2 n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn0, ite_eq_right hn0,
      show ((2:ℂ)).re = (2:ℝ) by norm_num]
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    gcongr
  calc ‖NumberField.dedekindZeta K s‖ = ‖∑' n : ℕ, LSeries.term f s n‖ := by
        rw [NumberField.dedekindZeta]
        rfl
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsummS.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term f 2 n‖ :=
        (hsummS.norm).tsum_le_tsum hterm (hsum2.norm)

private theorem exp_mul_assoc (a b c : ℝ) :
    Real.exp (a * (b * c)) = Real.exp (a * b * c) := by
  congr 1
  rw [mul_assoc]

private theorem completedEntire_right_bound {s : ℂ} (hs : 2 ≤ s.re) :
    ‖DedekindResidue.completedDedekindZetaEntire K s‖ ≤
      Real.exp (completedDedekindOrderConstant K * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := by
  let R : ℝ := ‖s‖
  let L : ℝ := (R + 1) * Real.log (R + 2)
  let d : ℝ := (|discr K| : ℝ)
  let T : ℝ := ∑' n : ℕ, ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖
  let Z : ℝ := 1 + T
  have hR0 : 0 ≤ R := by simp [R]
  have hR2 : 2 ≤ R := by
    have hre : s.re ≤ ‖s‖ := by
      have h := Complex.abs_re_le_norm s
      rw [abs_of_nonneg (by linarith : 0 ≤ s.re)] at h
      exact h
    dsimp [R]
    exact hs.trans hre
  have hlog1 : 1 ≤ Real.log (R + 2) := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < R + 2)).2
    have he := Real.exp_one_lt_three
    dsimp [R] at hR2 ⊢
    linarith
  have hL1 : 1 ≤ L := by
    dsimp [L]
    have hlog0 : 0 ≤ Real.log (R + 2) := by linarith
    have hmul := mul_nonneg (by linarith : 0 ≤ R + 1)
      (by linarith : 0 ≤ Real.log (R + 2) - 1)
    nlinarith
  have hRL : R ≤ L := by
    dsimp [L]
    have hmul := mul_nonneg (by linarith : 0 ≤ R + 1)
      (by linarith : 0 ≤ Real.log (R + 2) - 1)
    nlinarith
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast (abs_pos.mpr (NumberField.discr_ne_zero K))
  have hd1 : 1 ≤ d := by
    dsimp [d]
    have hne : discr K ≠ 0 := NumberField.discr_ne_zero K
    by_cases hpos : 0 ≤ discr K
    · rw [abs_of_nonneg (show 0 ≤ ((discr K : ℤ) : ℝ) by exact_mod_cast hpos)]
      have h : (1 : ℤ) ≤ discr K := by omega
      exact_mod_cast h
    · rw [abs_of_neg (show ((discr K : ℤ) : ℝ) < 0 by exact_mod_cast (lt_of_not_ge hpos))]
      have h : (1 : ℤ) ≤ -discr K := by omega
      exact_mod_cast h
  have hlogd0 : 0 ≤ Real.log d := Real.log_nonneg hd1
  have hlogd_le : Real.log d ≤ d := by
    have h := Real.log_le_sub_one_of_pos hdpos
    linarith
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact tsum_nonneg (fun _ => norm_nonneg _)
  have hZ1 : 1 ≤ Z := by dsimp [Z]; linarith
  have hZpos : 0 < Z := by linarith
  have hZle : ‖NumberField.dedekindZeta K s‖ ≤ Z := by
    have h := norm_dedekindZeta_le_of_two_le_re K hs
    dsimp [Z, T]
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hsRe : 1 < s.re := by linarith
  have hformula : DedekindResidue.completedDedekindZetaEntire K s =
      s * (s - 1) * DedekindResidue.completedZetaPrefactor K s
        * NumberField.dedekindZeta K s := by
    rw [DedekindResidue.completedDedekindZetaEntire_eq K hs0 hs1,
      DedekindResidue.completedDedekindZeta_eq_of_one_lt_re K hsRe]
    ring
  have hR1 : ‖s‖ ≤ R + 1 := by dsimp [R]; linarith [norm_nonneg s]
  have hRsub1 : ‖s - 1‖ ≤ R + 1 := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = R + 1 := by simp [R]
  have hpoly : ‖s‖ * ‖s - 1‖ ≤ (R + 1)^2 := by
    calc ‖s‖ * ‖s - 1‖ ≤ (R + 1) * (R + 1) :=
          mul_le_mul hR1 hRsub1 (by positivity) (by positivity)
      _ = (R + 1)^2 := by ring
  have hDelta : ‖((d : ℝ) : ℂ) ^ (s / 2)‖ ≤ Real.exp (d * L) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hdpos, Real.rpow_def_of_pos hdpos]
    apply Real.exp_le_exp.mpr
    have hsarg : (s / 2).re ≤ R := by
      have hre : s.re ≤ R := by
        have h := Complex.abs_re_le_norm s
        rw [abs_of_nonneg (by linarith : 0 ≤ s.re)] at h
        dsimp [R]
        exact h
      have hhalf : (s / 2).re = s.re / 2 := by simp
      rw [hhalf]
      dsimp [R]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsarg hlogd0
    have hmul' : Real.log d * (s / 2).re ≤ d * L := by
      have hmul₂ : Real.log d * R ≤ d * R :=
        mul_le_mul_of_nonneg_right hlogd_le hR0
      have hmul₃ : d * R ≤ d * L :=
        mul_le_mul_of_nonneg_left hRL (by linarith : 0 ≤ d)
      exact hmul.trans (hmul₂.trans hmul₃)
    simpa [mul_comm] using hmul'
  have hGammaHalf : ‖Complex.Gamma (s / 2)‖ ≤ Real.exp L := by
    apply norm_complexGamma_le_exp_growth
    · have hhalf : (s / 2).re = s.re / 2 := by simp
      rw [hhalf]
      linarith
    · have hnorm : ‖s / 2‖ = ‖s‖ / 2 := by
        rw [norm_div]
        norm_num
      rw [hnorm]
      dsimp [R]
      linarith [norm_nonneg s]
  have hGammaWhole : ‖Complex.Gamma s‖ ≤ Real.exp L := by
    apply norm_complexGamma_le_exp_growth
    · linarith
    · rfl
  have hPiBase : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · linarith [Real.pi_gt_three]
    · have harg : (-s / 2).re = -s.re / 2 := by simp
      rw [harg]
      linarith
  have hTwoPiBase : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 2 * Real.pi)]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · nlinarith [Real.pi_gt_three]
    · have harg : (-s).re = -s.re := by simp
      rw [harg]
      linarith
  have hGammaR : ‖Complex.Gammaℝ s‖ ≤ Real.exp (L + 1) := by
    rw [Complex.Gammaℝ_def, norm_mul]
    calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ 1 * Real.exp L := mul_le_mul hPiBase hGammaHalf (norm_nonneg _) (by positivity)
      _ ≤ Real.exp (L + 1) := by
        rw [Real.exp_add]
        have he2 : 2 ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1:ℝ)]
        calc 1 * Real.exp L = Real.exp L * 1 := by ring
          _ ≤ Real.exp L * Real.exp 1 :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos L).le
  have hTwoPiBase' : ‖((2:ℂ) * (Real.pi : ℂ)) ^ (-s)‖ ≤ 1 := by
    simpa [Complex.ofReal_mul] using hTwoPiBase
  have hGammaC : ‖Complex.Gammaℂ s‖ ≤ Real.exp (L + 1) := by
    rw [Complex.Gammaℂ_def, norm_mul, norm_mul]
    calc ‖(2:ℂ)‖ * ‖((2:ℂ) * (Real.pi : ℂ)) ^ (-s)‖ * ‖Complex.Gamma s‖
        = 2 * (‖((2:ℂ) * (Real.pi : ℂ)) ^ (-s)‖ * ‖Complex.Gamma s‖) := by
          simp only [Complex.norm_ofNat]
          ring
      _ ≤ 2 * (1 * Real.exp L) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hTwoPiBase' hGammaWhole (norm_nonneg _) (by positivity))
            (by norm_num)
      _ = 2 * 1 * Real.exp L := by ring
      _ ≤ Real.exp (L + 1) := by
        have he2 : 2 ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1:ℝ)]
        calc 2 * 1 * Real.exp L = Real.exp L * 2 := by ring
          _ ≤ Real.exp L * Real.exp 1 := mul_le_mul_of_nonneg_left he2 (by positivity)
          _ = Real.exp (L + 1) := (Real.exp_add L 1).symm
  have hGammaFactor : ‖DedekindResidue.gammaFactor K s‖
      ≤ Real.exp (2 * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
          + NumberField.InfinitePlace.nrComplexPlaces K) * L) := by
    rw [DedekindResidue.gammaFactor, norm_mul, norm_pow, norm_pow]
    let n₁ := NumberField.InfinitePlace.nrRealPlaces K
    let n₂ := NumberField.InfinitePlace.nrComplexPlaces K
    have hn₁ : (0:ℝ) ≤ (n₁:ℝ) := by positivity
    have hn₂ : (0:ℝ) ≤ (n₂:ℝ) := by positivity
    have hRpow : ‖Complex.Gammaℝ s‖ ^ n₁
        ≤ Real.exp ((n₁:ℝ) * (L + 1)) := by
      calc ‖Complex.Gammaℝ s‖ ^ n₁ ≤ (Real.exp (L + 1)) ^ n₁ :=
            pow_le_pow_left₀ (norm_nonneg _) hGammaR n₁
        _ = Real.exp ((n₁:ℝ) * (L + 1)) := by rw [← Real.exp_nat_mul]
    have hCpow : ‖Complex.Gammaℂ s‖ ^ n₂
        ≤ Real.exp ((n₂:ℝ) * (L + 1)) := by
      calc ‖Complex.Gammaℂ s‖ ^ n₂ ≤ (Real.exp (L + 1)) ^ n₂ :=
            pow_le_pow_left₀ (norm_nonneg _) hGammaC n₂
        _ = Real.exp ((n₂:ℝ) * (L + 1)) := by rw [← Real.exp_nat_mul]
    have hsum : (n₁:ℝ) * (L + 1) + (n₂:ℝ) * (L + 1)
        = ((n₁:ℝ) + n₂) * (L + 1) := by ring
    have hLplus : L + 1 ≤ 2 * L := by linarith
    calc ‖Complex.Gammaℝ s‖ ^ n₁ * ‖Complex.Gammaℂ s‖ ^ n₂
        ≤ Real.exp ((n₁:ℝ) * (L + 1)) * Real.exp ((n₂:ℝ) * (L + 1)) :=
          mul_le_mul hRpow hCpow (by positivity) (by positivity)
      _ = Real.exp (((n₁:ℝ) + n₂) * (L + 1)) := by rw [← Real.exp_add, ← hsum]
      _ ≤ Real.exp (2 * ((n₁:ℝ) + n₂) * L) := by
          apply Real.exp_le_exp.mpr
          calc ((n₁:ℝ) + n₂) * (L + 1)
              ≤ ((n₁:ℝ) + n₂) * (2 * L) :=
                mul_le_mul_of_nonneg_left hLplus (add_nonneg hn₁ hn₂)
            _ = 2 * ((n₁:ℝ) + n₂) * L := by ring
  have hZexp : Z ≤ Real.exp (Z * L) := by
    have hZleExp : Z ≤ Real.exp Z := by
      have h := Real.add_one_le_exp Z
      linarith
    exact hZleExp.trans (Real.exp_le_exp.mpr (by
      have := mul_nonneg (sub_nonneg.mpr hL1) (le_of_lt hZpos)
      nlinarith))
  have hpolyExp : (R + 1)^2 ≤ Real.exp (2 * L) := by
    have hbase : R + 1 ≤ Real.exp (Real.log (R + 2)) := by
      rw [Real.exp_log (by linarith : 0 < R + 2)]
      linarith
    have hsq : (R + 1)^2 ≤ (Real.exp (Real.log (R + 2)))^2 :=
      pow_le_pow_left₀ (by positivity) hbase 2
    calc (R + 1)^2 ≤ (Real.exp (Real.log (R + 2)))^2 := hsq
      _ = Real.exp (2 * Real.log (R + 2)) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp (2 * L) := by
        apply Real.exp_le_exp.mpr
        dsimp [L]
        have hmul := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ R + 1)
          (by linarith : 0 ≤ Real.log (R + 2))
        nlinarith
  have htotal : (R + 1)^2 * Real.exp (d * L)
        * Real.exp (2 * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
          + NumberField.InfinitePlace.nrComplexPlaces K) * L) * Z
      ≤ Real.exp (completedDedekindOrderConstant K * L) := by
    calc (R + 1)^2 * Real.exp (d * L)
          * Real.exp (2 * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
            + NumberField.InfinitePlace.nrComplexPlaces K) * L) * Z
        ≤ Real.exp (2 * L) * Real.exp (d * L)
            * Real.exp (2 * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
              + NumberField.InfinitePlace.nrComplexPlaces K) * L)
            * Real.exp (Z * L) := by
          gcongr
      _ = Real.exp (completedDedekindOrderConstant K * L) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [completedDedekindOrderConstant, d, Z, T]
        ring
  have hformBound : ‖DedekindResidue.completedDedekindZetaEntire K s‖
      ≤ (R + 1)^2 * Real.exp (d * L)
          * Real.exp (2 * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
            + NumberField.InfinitePlace.nrComplexPlaces K) * L) * Z := by
        rw [hformula, norm_mul, norm_mul, norm_mul,
          DedekindResidue.completedZetaPrefactor, norm_mul,
          DedekindResidue.gammaFactor, norm_mul, norm_pow, norm_pow]
        have hGammaP : ‖Complex.Gammaℝ s‖ ^ NumberField.InfinitePlace.nrRealPlaces K
            * ‖Complex.Gammaℂ s‖ ^ NumberField.InfinitePlace.nrComplexPlaces K
            ≤ Real.exp (2 * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
              + NumberField.InfinitePlace.nrComplexPlaces K) * L) := by
          simpa [DedekindResidue.gammaFactor, norm_mul, norm_pow] using hGammaFactor
        have hmid : ‖((d : ℝ) : ℂ) ^ (s / 2)‖ *
            (‖Complex.Gammaℝ s‖ ^ NumberField.InfinitePlace.nrRealPlaces K
              * ‖Complex.Gammaℂ s‖ ^ NumberField.InfinitePlace.nrComplexPlaces K)
            ≤ Real.exp (d * L) * Real.exp (2 * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
              + NumberField.InfinitePlace.nrComplexPlaces K) * L) :=
          mul_le_mul hDelta hGammaP (by positivity) (by positivity)
        have hBC : (‖((d : ℝ) : ℂ) ^ (s / 2)‖ *
            (‖Complex.Gammaℝ s‖ ^ NumberField.InfinitePlace.nrRealPlaces K
              * ‖Complex.Gammaℂ s‖ ^ NumberField.InfinitePlace.nrComplexPlaces K))
            * ‖NumberField.dedekindZeta K s‖
            ≤ (Real.exp (d * L) * Real.exp (2 * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
              + NumberField.InfinitePlace.nrComplexPlaces K) * L) * Z) := by
          exact mul_le_mul hmid hZle (norm_nonneg _) (by positivity)
        calc ‖s‖ * ‖s - 1‖ *
              (‖((d : ℝ) : ℂ) ^ (s / 2)‖ *
                (‖Complex.Gammaℝ s‖ ^ NumberField.InfinitePlace.nrRealPlaces K
                  * ‖Complex.Gammaℂ s‖ ^ NumberField.InfinitePlace.nrComplexPlaces K))
              * ‖NumberField.dedekindZeta K s‖
            = (‖s‖ * ‖s - 1‖) *
                ((‖((d : ℝ) : ℂ) ^ (s / 2)‖ *
                  (‖Complex.Gammaℝ s‖ ^ NumberField.InfinitePlace.nrRealPlaces K
                    * ‖Complex.Gammaℂ s‖ ^ NumberField.InfinitePlace.nrComplexPlaces K))
                  * ‖NumberField.dedekindZeta K s‖) := by ring
          _ ≤ (R + 1)^2 *
              (Real.exp (d * L) * Real.exp (2 * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
                + NumberField.InfinitePlace.nrComplexPlaces K) * L) * Z) := by
            exact mul_le_mul hpoly hBC (by positivity) (by positivity)
          _ = (R + 1)^2 * Real.exp (d * L)
              * Real.exp (2 * ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
                + NumberField.InfinitePlace.nrComplexPlaces K) * L) * Z := by ring
  have hfinal : ‖DedekindResidue.completedDedekindZetaEntire K s‖
      ≤ Real.exp (completedDedekindOrderConstant K * L) := le_trans hformBound htotal
  simpa [L, R, mul_assoc] using hfinal

private theorem completedEntire_one_sub (s : ℂ) :
    DedekindResidue.completedDedekindZetaEntire K (1 - s)
      = DedekindResidue.completedDedekindZetaEntire K s := by
  have hcont1 : Continuous (fun z : ℂ => DedekindResidue.completedDedekindZetaEntire K (1 - z)) :=
    ((DedekindResidue.differentiable_completedDedekindZetaEntire K).comp
      ((differentiable_const (1:ℂ)).sub differentiable_id)).continuous
  have hcont2 : Continuous (DedekindResidue.completedDedekindZetaEntire K) :=
    (DedekindResidue.differentiable_completedDedekindZetaEntire K).continuous
  have hdense : Dense ({(0:ℂ), 1}ᶜ : Set ℂ) :=
    Set.Countable.dense_compl ℝ
      ((Set.toFinite ({(0:ℂ), 1} : Set ℂ)).countable)
  refine congrFun (Continuous.ext_on hdense hcont1 hcont2 ?_) s
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
  obtain ⟨hz0, hz1⟩ := hz
  have h1z0 : (1:ℂ) - z ≠ 0 := by
    intro h0
    apply hz1
    linear_combination -h0
  have h1z1 : (1:ℂ) - z ≠ 1 := by
    intro h0
    apply hz0
    linear_combination -h0
  change DedekindResidue.completedDedekindZetaEntire K (1 - z)
    = DedekindResidue.completedDedekindZetaEntire K z
  rw [DedekindResidue.completedDedekindZetaEntire_eq K h1z0 h1z1,
    DedekindResidue.completedDedekindZetaEntire_eq K hz0 hz1,
    DedekindResidue.completedDedekindZeta_one_sub K z]
  ring

theorem exists_completedDedekindZetaEntire_order_one :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖DedekindResidue.completedDedekindZetaEntire K s‖
        ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := by
  let Cr : ℝ := completedDedekindOrderConstant K
  have hCr : 0 < Cr := by
    have hdisc : 0 ≤ (|discr K| : ℝ) := by positivity
    have hplaces : 0 ≤ (NumberField.InfinitePlace.nrRealPlaces K : ℝ)
        + NumberField.InfinitePlace.nrComplexPlaces K := by positivity
    have hsum : 0 ≤ ∑' n : ℕ, ‖LSeries.term
        (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖ :=
      tsum_nonneg (fun _ => norm_nonneg _)
    dsimp [Cr, completedDedekindOrderConstant]
    linarith
  have hRight : ∀ s : ℂ, 2 ≤ s.re →
      ‖DedekindResidue.completedDedekindZetaEntire K s‖
        ≤ Real.exp (Cr * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := by
    intro s hs
    exact completedEntire_right_bound K hs
  obtain ⟨B, hB0, hStrip⟩ :=
    exists_completedDedekindZetaEntire_strip_bound K (-1) 2 (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let Cc : ℝ := 2 + B / Real.log 2
  have hCc : 0 < Cc := by
    dsimp [Cc]
    positivity
  have hlogbase {R : ℝ} (hR : 0 ≤ R) :
      Real.log 2 ≤ (R + 1) * Real.log (R + 2) := by
    have hlog0 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    have hlogmono : Real.log 2 ≤ Real.log (R + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    calc Real.log 2 ≤ Real.log (R + 2) := hlogmono
      _ ≤ (R + 1) * Real.log (R + 2) := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ R)
          (by linarith : 0 ≤ Real.log (R + 2))]
  have hStripGrowth : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖DedekindResidue.completedDedekindZetaEntire K s‖
        ≤ Real.exp (Cc * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := by
    intro s hslo hshi
    let R : ℝ := ‖s‖
    let L : ℝ := (R + 1) * Real.log (R + 2)
    have hR0 : 0 ≤ R := by positivity
    have hlogR0 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    have hlogRle : Real.log (R + 2) ≤ L := by
      dsimp [L]
      nlinarith [mul_nonneg (by linarith : 0 ≤ R)
        (by linarith : 0 ≤ Real.log (R + 2))]
    have hBexp : B ≤ Real.exp B := by
      have h := Real.add_one_le_exp B
      linarith
    have hpoly : (R + 1)^2 ≤ Real.exp (2 * Real.log (R + 2)) := by
      have hbase : R + 1 ≤ Real.exp (Real.log (R + 2)) := by
        rw [Real.exp_log (by linarith : 0 < R + 2)]
        linarith
      calc (R + 1)^2 ≤ (Real.exp (Real.log (R + 2)))^2 :=
            pow_le_pow_left₀ (by positivity) hbase 2
        _ = Real.exp (2 * Real.log (R + 2)) := by rw [← Real.exp_nat_mul]; norm_num
    have hLmin := hlogbase hR0
    have hfrac0 : 0 ≤ B / Real.log 2 := div_nonneg hB0 hlog2.le
    have hBmul : B ≤ (B / Real.log 2) * L := by
      have heq : (B / Real.log 2) * Real.log 2 = B := by
        field_simp [hlog2.ne']
      calc B = (B / Real.log 2) * Real.log 2 := heq.symm
        _ ≤ (B / Real.log 2) * L := mul_le_mul_of_nonneg_left hLmin hfrac0
    have hExp : ‖DedekindResidue.completedDedekindZetaEntire K s‖
        ≤ Real.exp (Cc * L) := by
      have hbase := hStrip s hslo hshi
      dsimp [L] at hbase ⊢
      calc ‖DedekindResidue.completedDedekindZetaEntire K s‖
          ≤ B * (R + 1)^2 := by simpa [R, add_comm] using hbase
        _ ≤ Real.exp (B + 2 * Real.log (R + 2)) := by
          calc B * (R + 1)^2
              ≤ Real.exp B * Real.exp (2 * Real.log (R + 2)) :=
                mul_le_mul hBexp hpoly (by positivity) (by positivity)
            _ = Real.exp (B + 2 * Real.log (R + 2)) := by rw [← Real.exp_add]
        _ ≤ Real.exp (Cc * ((R + 1) * Real.log (R + 2))) := by
          apply Real.exp_le_exp.mpr
          dsimp [Cc]
          nlinarith [hBmul, hlogRle]
    simpa [R, L, mul_assoc] using hExp
  let C : ℝ := max Cc (4 * Cr)
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le hCc (le_max_left _ _)
  refine ⟨C, hC, fun s => ?_⟩
  by_cases hsleft : s.re < -1
  · have hsRe : 2 ≤ (1 - s).re := by simp; linarith
    have hsNorm : ‖(1:ℂ) - s‖ ≤ ‖s‖ + 1 := by
      calc ‖(1:ℂ) - s‖ ≤ ‖(1:ℂ)‖ + ‖s‖ := norm_sub_le _ _
        _ = ‖s‖ + 1 := by rw [norm_one]; ring
    let R : ℝ := ‖s‖
    let Q : ℝ := ‖(1:ℂ) - s‖
    have hR1 : 1 ≤ R := by
      have h := Complex.abs_re_le_norm s
      rw [abs_of_neg (by linarith : s.re < 0)] at h
      dsimp [R]
      linarith
    have hQ1 : Q + 1 ≤ R + 2 := by dsimp [Q, R]; linarith [hsNorm]
    have hQ2 : Q + 2 ≤ (R + 2)^2 := by
      have hQ : Q ≤ R + 1 := by dsimp [Q, R]; linarith [hsNorm]
      dsimp [Q, R]
      nlinarith [hQ, hR1]
    have hQ0 : 0 ≤ Q := by positivity
    have hR0 : 0 ≤ R := by positivity
    have hlogQ : Real.log (Q + 2) ≤ 2 * Real.log (R + 2) := by
      calc Real.log (Q + 2) ≤ Real.log ((R + 2)^2) :=
            Real.log_le_log (by linarith) (by exact hQ2)
        _ = 2 * Real.log (R + 2) := by rw [Real.log_pow]; norm_num
    have hlogQ0 : 0 ≤ Real.log (Q + 2) := Real.log_nonneg (by linarith)
    have hshift : (Q + 1) * Real.log (Q + 2)
        ≤ 4 * ((R + 1) * Real.log (R + 2)) := by
      calc (Q + 1) * Real.log (Q + 2)
          ≤ (R + 2) * (2 * Real.log (R + 2)) :=
            mul_le_mul hQ1 hlogQ hlogQ0 (by positivity)
        _ ≤ 4 * ((R + 1) * Real.log (R + 2)) := by
          have hcoef : R + 2 ≤ 2 * (R + 1) := by linarith
          have hlogR0 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
          nlinarith [mul_nonneg (by linarith : 0 ≤ R + 1) hlogR0]
    have hright := hRight (1 - s) hsRe
    rw [← completedEntire_one_sub K s]
    have hCright : Cr ≤ C := by
      dsimp [C]
      have hCr0 : 0 ≤ Cr := le_of_lt hCr
      exact le_trans (by nlinarith) (le_max_right _ _)
    calc ‖DedekindResidue.completedDedekindZetaEntire K (1 - s)‖
        ≤ Real.exp (Cr * (Q + 1) * Real.log (Q + 2)) := by
          simpa [Q] using hright
      _ ≤ Real.exp (C * (R + 1) * Real.log (R + 2)) := by
          apply Real.exp_le_exp.mpr
          have hL0 : 0 ≤ (R + 1) * Real.log (R + 2) :=
            mul_nonneg (by linarith : 0 ≤ R + 1)
              (Real.log_nonneg (by linarith : 1 ≤ R + 2))
          have hC4 : 4 * Cr ≤ C := by
            dsimp [C]
            exact le_max_right _ _
          calc Cr * (Q + 1) * Real.log (Q + 2)
              = Cr * ((Q + 1) * Real.log (Q + 2)) := by ring
            _ ≤ Cr * (4 * ((R + 1) * Real.log (R + 2))) :=
                mul_le_mul_of_nonneg_left hshift hCr.le
            _ = (4 * Cr) * ((R + 1) * Real.log (R + 2)) := by ring
            _ ≤ C * ((R + 1) * Real.log (R + 2)) :=
                mul_le_mul_of_nonneg_right hC4 hL0
            _ = C * (R + 1) * Real.log (R + 2) := by ring
  · by_cases hsright : 2 < s.re
    · have hsRe : 2 ≤ s.re := le_of_lt hsright
      have hright := hRight s hsRe
      have hCright : Cr ≤ C := by
        dsimp [C]
        exact le_trans (by nlinarith [hCr.le]) (le_max_right _ _)
      calc ‖DedekindResidue.completedDedekindZetaEntire K s‖
          ≤ Real.exp (Cr * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := hright
        _ ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := by
          apply Real.exp_le_exp.mpr
          have hfac : 0 ≤ (‖s‖ + 1) * Real.log (‖s‖ + 2) :=
            mul_nonneg (by positivity)
              (Real.log_nonneg (by linarith [norm_nonneg s]))
          nlinarith [mul_nonneg (by linarith : 0 ≤ C - Cr) hfac]
    · have hslo : -1 ≤ s.re := le_of_not_gt hsleft
      have hshi : s.re ≤ 2 := le_of_not_gt hsright
      have hcentral := hStripGrowth s hslo hshi
      have hCcenter : Cc ≤ C := by
        dsimp [C]
        exact le_max_left _ _
      calc ‖DedekindResidue.completedDedekindZetaEntire K s‖
          ≤ Real.exp (Cc * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := hcentral
        _ ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := by
          apply Real.exp_le_exp.mpr
          have hfac : 0 ≤ (‖s‖ + 1) * Real.log (‖s‖ + 2) :=
            mul_nonneg (by positivity)
              (Real.log_nonneg (by linarith [norm_nonneg s]))
          nlinarith [mul_nonneg (by linarith : 0 ≤ C - Cc) hfac]

end ArtinPrimitiveRoots.Hecke.DedekindBounds
