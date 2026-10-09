import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.Interfaces
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Exact interfaces for the PP Dirichlet-series continuation estimates. -/

namespace ArtinPrimitiveRoots.Proofs.pp_cont_p

open MeasureTheory
open Filter Asymptotics
open Topology
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP

noncomputable def contPrefix (q : ℕ) (χ : DirichletCharacter ℂ q)
    (u : ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊u⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n),
    χ (n : ZMod q)

noncomputable def contDiscrepancy (q : ℕ) (χ : DirichletCharacter ℂ q)
    (u : ℝ) : ℂ := contPrefix q χ u - characterMean q χ * (u : ℂ)

noncomputable def contTail (q : ℕ) (χ : DirichletCharacter ℂ q)
    (Y : ℝ) (s : ℂ) : ℂ :=
  -contDiscrepancy q χ Y * Complex.exp (-s * (Real.log Y : ℂ)) +
    s * ∫ u : ℝ in Set.Ioi Y,
      contDiscrepancy q χ u *
        Complex.exp (-(s + 1) * (Real.log u : ℂ))

theorem cont_characterMean_norm_le_one {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) : ‖characterMean q χ‖ ≤ 1 := by
  rw [characterMean, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ a ∈ Finset.range q, χ (a : ZMod q)‖ ≤ q := by
    calc
      _ ≤ ∑ a ∈ Finset.range q, ‖χ (a : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ Finset.range q, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact χ.norm_le_one _
      _ = q := by simp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    (q : ℝ)⁻¹ * ‖∑ a ∈ Finset.range q, χ (a : ZMod q)‖
        ≤ (q : ℝ)⁻¹ * q :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by field_simp

private theorem cont_periodic_shift {q : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, f (n + q) = f n) (n m : ℕ) :
    f (n + q * m) = f n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ]
      calc
        f (n + (q * m + q)) = f ((n + q * m) + q) := by congr 1 <;> omega
        _ = f (n + q * m) := hf _
        _ = f n := ih

private theorem cont_periodic_range_sum {q : ℕ} (hq : 0 < q) (f : ℕ → ℂ)
    (hf : ∀ n, f (n + q) = f n) (m : ℕ) :
    ∑ n ∈ Finset.range (q * m), f n = (m : ℂ) * ∑ n ∈ Finset.range q, f n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add]
      have hshift : ∑ n ∈ Finset.range q, f (q * m + n) =
          ∑ n ∈ Finset.range q, f n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Nat.add_comm (q * m) n]
        exact cont_periodic_shift f hf n m
      rw [hshift, ih]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

private theorem cont_centered_prefix_bound {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (m : ℕ) :
    ‖∑ k ∈ Finset.range m,
      (χ ((k + 1 : ℕ) : ZMod q) - characterMean q χ)‖ ≤
        2 * ((q : ℝ) - 1) := by
  classical
  let f : ℕ → ℂ := fun k => χ ((k + 1 : ℕ) : ZMod q) - characterMean q χ
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmean := cont_characterMean_norm_le_one hq χ
  have hper : ∀ k, f (k + q) = f k := by
    intro k
    dsimp [f]
    congr 1
    simp [Nat.cast_add, add_assoc]
  have hshift : (∑ k ∈ Finset.range q, χ ((k + 1 : ℕ) : ZMod q)) =
      ∑ k ∈ Finset.range q, χ (k : ZMod q) := by
    have hzero : χ ((q : ℕ) : ZMod q) = χ (0 : ZMod q) := by simp
    calc
      _ = (∑ k ∈ Finset.range (q + 1), χ (k : ZMod q)) -
            χ (0 : ZMod q) := by
          rw [Finset.sum_range_succ']
          simp
      _ = (∑ k ∈ Finset.range q, χ (k : ZMod q)) +
            χ ((q : ℕ) : ZMod q) - χ (0 : ZMod q) := by
          rw [Finset.sum_range_succ]
      _ = _ := by rw [hzero]; simp
  have hblock : ∑ k ∈ Finset.range q, f k = 0 := by
    dsimp [f]
    rw [Finset.sum_sub_distrib, hshift, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, characterMean]
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
    ring
  let d := m / q
  let r := m % q
  have hdecomp : q * d + r = m := by
    dsimp [d, r]
    calc
      q * (m / q) + m % q = m % q + q * (m / q) := by ac_rfl
      _ = m := Nat.mod_add_div m q
  have hsplit : (∑ k ∈ Finset.range m, f k) =
      (∑ k ∈ Finset.range (q * d), f k) +
        ∑ k ∈ Finset.range r, f (k + q * d) := by
    rw [← hdecomp, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.add_comm]
  have hfull : ∑ k ∈ Finset.range (q * d), f k = 0 := by
    rw [cont_periodic_range_sum hq f hper d, hblock]
    simp
  rw [hsplit, hfull, zero_add]
  calc
    ‖∑ k ∈ Finset.range r, f (k + q * d)‖ ≤
        ∑ k ∈ Finset.range r, ‖f (k + q * d)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range r, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      dsimp [f]
      calc
        ‖χ (((k + q * d) + 1 : ℕ) : ZMod q) - characterMean q χ‖ ≤
            ‖χ (((k + q * d) + 1 : ℕ) : ZMod q)‖ +
              ‖characterMean q χ‖ := norm_sub_le _ _
        _ ≤ 2 := by nlinarith [χ.norm_le_one (((k + q * d) + 1 : ℕ) : ZMod q)]
    _ = (r : ℝ) * 2 := by simp
    _ ≤ ((q : ℝ) - 1) * 2 := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      have hrt : r < q := Nat.mod_lt m hq
      have hrt' : r + 1 ≤ q := Nat.succ_le_of_lt hrt
      have hrtR : (r : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hrt'
      linarith
    _ = 2 * ((q : ℝ) - 1) := by ring

private theorem contPrefix_eq_shifted_sum (q : ℕ) (χ : DirichletCharacter ℂ q)
    (m : ℕ) :
    (∑ n ∈ (Finset.range (m + 1)).filter (fun n : ℕ => 1 ≤ n),
      χ (n : ZMod q)) =
      ∑ k ∈ Finset.range m, χ ((k + 1 : ℕ) : ZMod q) := by
  classical
  have hfilter : (Finset.range (m + 1)).filter (fun n : ℕ => 1 ≤ n) =
      (Finset.range m).image Nat.succ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hnm, hn1⟩
      refine ⟨n - 1, ?_, ?_⟩ <;> omega
    · rintro ⟨k, hkm, rfl⟩
      constructor <;> omega
  rw [hfilter]
  rw [Finset.sum_image (fun a ha b hb hab => Nat.succ.inj hab)]

theorem cont_discrepancy_bound {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : 0 ≤ u) :
    ‖contDiscrepancy q χ u‖ ≤ 2 * (q : ℝ) := by
  classical
  let m := ⌊u⌋₊
  let δ := u - (m : ℝ)
  have hmlo : (m : ℝ) ≤ u := Nat.floor_le hu
  have hmhi : u < (m : ℝ) + 1 := Nat.lt_floor_add_one u
  have hδlo : 0 ≤ δ := by dsimp [δ]; linarith
  have hδhi : δ ≤ 1 := by dsimp [δ]; linarith
  have hprefix := contPrefix_eq_shifted_sum q χ m
  have hcenter :
      ‖(∑ k ∈ Finset.range m, χ ((k + 1 : ℕ) : ZMod q)) -
        characterMean q χ * (m : ℂ)‖ ≤ 2 * ((q : ℝ) - 1) := by
    simpa [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_comm] using cont_centered_prefix_bound hq χ m
  have hmean := cont_characterMean_norm_le_one hq χ
  unfold contDiscrepancy contPrefix
  rw [contPrefix_eq_shifted_sum q χ m]
  have hsplit :
      (∑ k ∈ Finset.range m, χ ((k + 1 : ℕ) : ZMod q)) -
        characterMean q χ * (u : ℂ) =
      ((∑ k ∈ Finset.range m, χ ((k + 1 : ℕ) : ZMod q)) -
        characterMean q χ * (m : ℂ)) - characterMean q χ * (δ : ℂ) := by
    dsimp [δ]
    push_cast
    ring
  rw [hsplit]
  have hδnorm : ‖characterMean q χ * (δ : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real]
    calc
      ‖characterMean q χ‖ * |δ| ≤ 1 * |δ| :=
        mul_le_mul_of_nonneg_right hmean (abs_nonneg δ)
      _ ≤ 1 := by nlinarith [abs_of_nonneg hδlo]
  calc
    _ ≤ ‖(∑ k ∈ Finset.range m, χ ((k + 1 : ℕ) : ZMod q)) -
          characterMean q χ * (m : ℂ)‖ +
        ‖characterMean q χ * (δ : ℂ)‖ := norm_sub_le _ _
    _ ≤ 2 * ((q : ℝ) - 1) + 1 := add_le_add hcenter hδnorm
    _ ≤ 2 * (q : ℝ) := by linarith

theorem cont_tail_integrable {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ)
    (hs : 0 < s.re) :
    IntegrableOn
      (fun u : ℝ => contDiscrepancy q χ u *
        Complex.exp (-(s + 1) * (Real.log u : ℂ))) (Set.Ioi Y) := by
  let f : ℝ → ℂ := fun u => contDiscrepancy q χ u *
    Complex.exp (-(s + 1) * (Real.log u : ℂ))
  let p : ℕ → ℂ := fun m =>
    ∑ n ∈ (Finset.range (m + 1)).filter (fun n : ℕ => 1 ≤ n),
      χ (n : ZMod q)
  have hprefix : Measurable (contPrefix q χ) := by
    change Measurable (fun u : ℝ => p (⌊u⌋₊))
    exact (measurable_of_countable p).comp Nat.measurable_floor
  have hEm : AEStronglyMeasurable (contDiscrepancy q χ) volume := by
    unfold contDiscrepancy
    exact (hprefix.sub (measurable_const.mul Complex.measurable_ofReal)).aestronglyMeasurable
  have hE : AEStronglyMeasurable (contDiscrepancy q χ)
      (volume.restrict (Set.Ioi Y)) :=
    hEm.restrict
  have hlog : Measurable (fun u : ℝ => (Real.log u : ℂ)) :=
    Complex.measurable_ofReal.comp Real.measurable_log
  have hexp : Measurable (fun u : ℝ =>
      Complex.exp (-(s + 1) * (Real.log u : ℂ))) := by
    exact Complex.measurable_exp.comp (measurable_const.mul hlog)
  have hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi Y)) := by
    dsimp [f]
    exact hE.mul (hexp.aestronglyMeasurable.restrict)
  have hmajor : Integrable (fun u : ℝ =>
      (2 * (q : ℝ)) * Real.rpow u (-(s.re + 1)))
      (volume.restrict (Set.Ioi Y)) := by
    have hexpInt := integrableOn_Ioi_rpow_of_lt
      (a := -(s.re + 1)) (c := Y) (by linarith) (by linarith)
    exact hexpInt.const_mul (2 * (q : ℝ))
  have hnormExp (u : ℝ) (hu : 0 < u) :
      ‖Complex.exp (-(s + 1) * (Real.log u : ℂ))‖ =
        Real.rpow u (-(s.re + 1)) := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.neg_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.add_re, Complex.one_re, add_zero]
    calc
      Real.exp (-(s.re + 1) * Real.log u) =
          Real.exp (Real.log u * (-(s.re + 1))) := by congr 1 <;> ring
      _ = Real.rpow u (-(s.re + 1)) := (Real.rpow_def_of_pos hu _).symm
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioi Y)),
      ‖f u‖ ≤ (2 * (q : ℝ)) * Real.rpow u (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := by
      have huY : Y < u := Set.mem_Ioi.mp hu
      linarith
    have hdisc := cont_discrepancy_bound hq χ (le_of_lt hu0)
    dsimp [f]
    rw [norm_mul, hnormExp u hu0]
    exact mul_le_mul_of_nonneg_right hdisc (Real.rpow_nonneg hu0.le _)
  exact hmajor.mono' hf hbound

theorem contDiscrepancy_aestronglyMeasurable (q : ℕ)
    (χ : DirichletCharacter ℂ q) :
    AEStronglyMeasurable (contDiscrepancy q χ) volume := by
  let p : ℕ → ℂ := fun m =>
    ∑ n ∈ (Finset.range (m + 1)).filter (fun n : ℕ => 1 ≤ n),
      χ (n : ZMod q)
  have hprefix : Measurable (contPrefix q χ) := by
    change Measurable (fun u : ℝ => p (⌊u⌋₊))
    exact (measurable_of_countable p).comp Nat.measurable_floor
  unfold contDiscrepancy
  exact (hprefix.sub (measurable_const.mul Complex.measurable_ofReal)).aestronglyMeasurable

theorem contTail_differentiableAt {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (contTail q χ Y) s := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi Y)
  let δ : ℝ := s.re / 4
  let U : Set ℂ := Metric.ball s (s.re / 2)
  let C : ℝ := (2 * (q : ℝ)) / δ
  let F : ℂ → ℝ → ℂ := fun z u =>
    contDiscrepancy q χ u * Complex.exp (-(z + 1) * (Real.log u : ℂ))
  let F' : ℂ → ℝ → ℂ := fun z u =>
    contDiscrepancy q χ u *
      (Complex.exp (-(z + 1) * (Real.log u : ℂ)) * (-(Real.log u : ℂ)))
  have hYpos : 0 < Y := by linarith
  have hδpos : 0 < δ := by dsimp [δ]; linarith
  have hrad : 0 < s.re / 2 := by positivity
  have hE : AEStronglyMeasurable (contDiscrepancy q χ) μ := by
    dsimp [μ]
    exact (contDiscrepancy_aestronglyMeasurable q χ).restrict
  have hlogMeas : Measurable (fun u : ℝ => (Real.log u : ℂ)) :=
    Complex.measurable_ofReal.comp Real.measurable_log
  have hexpMeas (z : ℂ) : Measurable (fun u : ℝ =>
      Complex.exp (-(z + 1) * (Real.log u : ℂ))) :=
    Complex.measurable_exp.comp (measurable_const.mul hlogMeas)
  have hFmeas : ∀ᶠ z : ℂ in nhds s, AEStronglyMeasurable (F z) μ := by
    filter_upwards [] with z
    dsimp [F]
    exact hE.mul (hexpMeas z).aestronglyMeasurable
  have hFint : Integrable (F s) μ := by
    change Integrable (fun u : ℝ => contDiscrepancy q χ u *
      Complex.exp (-(s + 1) * (Real.log u : ℂ)))
      (volume.restrict (Set.Ioi Y))
    exact cont_tail_integrable hq χ hY s hs
  have hF'meas : AEStronglyMeasurable (F' s) μ := by
    dsimp [F']
    exact hE.mul (((hexpMeas s).mul hlogMeas.neg).aestronglyMeasurable)
  have hboundInt : Integrable (fun u : ℝ => C *
      Real.rpow u (-(s.re / 4 + 1))) μ := by
    dsimp [μ, C, δ]
    exact (integrableOn_Ioi_rpow_of_lt
      (a := -(s.re / 4 + 1)) (c := Y) (by linarith) hYpos).const_mul
        (2 * (q : ℝ) / (s.re / 4))
  have hbound : ∀ᵐ u ∂μ, ∀ z ∈ U, ‖F' z u‖ ≤ C *
      Real.rpow u (-(s.re / 4 + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huY : Y < u := Set.mem_Ioi.mp hu
    have hu1 : 1 ≤ u := by linarith [hY]
    have hu0 : 0 < u := by linarith
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
    have hlogPower : Real.log u ≤ Real.rpow u δ / δ := by
      have hlogPow := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu0 δ)
      rw [Real.log_rpow hu0 δ] at hlogPow
      have hlogPow' : δ * Real.log u ≤ Real.rpow u δ - 1 := by
        simpa only [Real.rpow_eq_pow] using hlogPow
      have hpowLog : Real.log u * δ ≤ Real.rpow u δ := by
        nlinarith [hlogPow']
      exact (le_div_iff₀ hδpos).2 hpowLog
    have hlogProduct :
        Real.rpow u (-(s.re / 2 + 1)) * Real.log u ≤
          (1 / δ) * Real.rpow u (-(s.re / 4 + 1)) := by
      calc
        _ ≤ Real.rpow u (-(s.re / 2 + 1)) *
            (Real.rpow u δ / δ) :=
          mul_le_mul_of_nonneg_left hlogPower
            (Real.rpow_nonneg hu0.le _)
        _ = (1 / δ) * (Real.rpow u (-(s.re / 2 + 1)) *
              Real.rpow u δ) := by ring
        _ = (1 / δ) * Real.rpow u (-(s.re / 2 + 1) + δ) := by
          have hadd : Real.rpow u (-(s.re / 2 + 1) + δ) =
              Real.rpow u (-(s.re / 2 + 1)) * Real.rpow u δ := by
            simpa only [Real.rpow_eq_pow] using
              (Real.rpow_add hu0 (-(s.re / 2 + 1)) δ)
          rw [← hadd]
        _ = (1 / δ) * Real.rpow u (-(s.re / 4 + 1)) := by
          congr 1
          dsimp [δ]
          ring
    intro z hz
    have hzDist : dist z s < s.re / 2 := by simpa [U] using hz
    have hzNorm : ‖z - s‖ < s.re / 2 := by
      simpa [dist_eq_norm] using hzDist
    have hzReAbs : |(z - s).re| < s.re / 2 :=
      (Complex.abs_re_le_norm (z - s)).trans_lt hzNorm
    have hzReLow : s.re / 2 < z.re := by
      have hlow := (abs_lt.mp hzReAbs).1
      have hlow' : -(s.re / 2) < z.re - s.re := by
        simpa only [Complex.sub_re] using hlow
      linarith
    have hpow : Real.rpow u (-(z.re + 1)) ≤
        Real.rpow u (-(s.re / 2 + 1)) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
    have hdisc := cont_discrepancy_bound hq χ hu0.le
    have hnormExp : ‖Complex.exp (-(z + 1) * (Real.log u : ℂ))‖ =
        Real.rpow u (-(z.re + 1)) := by
      rw [Complex.norm_exp, Complex.mul_re, Complex.neg_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.add_re, Complex.one_re, add_zero]
      calc
        Real.exp (-(z.re + 1) * Real.log u) =
            Real.exp (Real.log u * (-(z.re + 1))) := by congr 1 <;> ring
        _ = Real.rpow u (-(z.re + 1)) :=
          (Real.rpow_def_of_pos hu0 _).symm
    have hnormF' : ‖F' z u‖ = ‖contDiscrepancy q χ u‖ *
        (Real.rpow u (-(z.re + 1)) * Real.log u) := by
      calc
        ‖F' z u‖ = ‖contDiscrepancy q χ u‖ *
            (‖Complex.exp (-(z + 1) * (Real.log u : ℂ))‖ *
              ‖-(Real.log u : ℂ)‖) := by
                dsimp [F']
                rw [norm_mul, norm_mul]
        _ = ‖contDiscrepancy q χ u‖ *
            (Real.rpow u (-(z.re + 1)) * Real.log u) := by
              rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg hlog0, hnormExp]
    calc
      ‖F' z u‖ = ‖contDiscrepancy q χ u‖ *
          (Real.rpow u (-(z.re + 1)) * Real.log u) := hnormF'
      _ ≤ ‖contDiscrepancy q χ u‖ *
          (Real.rpow u (-(s.re / 2 + 1)) * Real.log u) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right hpow hlog0
        · exact norm_nonneg _
      _ ≤ (2 * (q : ℝ)) *
          (Real.rpow u (-(s.re / 2 + 1)) * Real.log u) :=
        mul_le_mul_of_nonneg_right hdisc
          (mul_nonneg (Real.rpow_nonneg hu0.le _) hlog0)
      _ ≤ (2 * (q : ℝ)) *
          ((1 / δ) * Real.rpow u (-(s.re / 4 + 1))) :=
        mul_le_mul_of_nonneg_left hlogProduct (by positivity)
      _ = C * Real.rpow u (-(s.re / 4 + 1)) := by
        dsimp [C]
        ring
  have hdiff : ∀ᵐ u ∂μ, ∀ z ∈ U,
      HasDerivAt (F · u) (F' z u) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z hz
    let L : ℂ := (Real.log u : ℂ)
    have hlin : HasDerivAt (fun w : ℂ => -(w + 1) * L) (-L) z := by
      simpa [L] using ((hasDerivAt_id z).add_const (1 : ℂ)).neg.mul_const L
    simpa [F, F', L] using
      (hlin.cexp).const_mul (contDiscrepancy q χ u)
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (x₀ := s) (s := U) (bound := fun u =>
      C * Real.rpow u (-(s.re / 4 + 1)))
    (Metric.ball_mem_nhds _ hrad) hFmeas hFint hF'meas hbound hboundInt hdiff
  have hI : DifferentiableAt ℂ (fun z : ℂ =>
      ∫ u : ℝ in Set.Ioi Y, contDiscrepancy q χ u *
        Complex.exp (-(z + 1) * (Real.log u : ℂ))) s := by
    simpa [F, μ] using hparam.2.differentiableAt
  have hfirst : DifferentiableAt ℂ (fun z : ℂ =>
      -contDiscrepancy q χ Y * Complex.exp (-z * (Real.log Y : ℂ))) s := by
    fun_prop
  have hsecond : DifferentiableAt ℂ (fun z : ℂ =>
      z * ∫ u : ℝ in Set.Ioi Y, contDiscrepancy q χ u *
        Complex.exp (-(z + 1) * (Real.log u : ℂ))) s :=
    (differentiableAt_id).mul hI
  unfold contTail
  exact hfirst.add hsecond

theorem cont_tail_bound {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ)
    (hs : 0 < s.re) :
    ‖contTail q χ Y s‖ ≤
      2 * (q : ℝ) * (1 + ‖s‖ / s.re) * Real.rpow Y (-s.re) := by
  have hYpos : 0 < Y := by linarith
  have hnormExp (z : ℂ) (u : ℝ) (hu : 0 < u) :
      ‖Complex.exp (-z * (Real.log u : ℂ))‖ = Real.rpow u (-z.re) := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.neg_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      Real.exp (-z.re * Real.log u) =
          Real.exp (Real.log u * (-z.re)) := by congr 1 <;> ring
      _ = Real.rpow u (-z.re) := (Real.rpow_def_of_pos hu _).symm
  have hnormEnd := hnormExp s Y hYpos
  have hnormTail (u : ℝ) (hu : 0 < u) :
      ‖Complex.exp (-(s + 1) * (Real.log u : ℂ))‖ =
        Real.rpow u (-(s.re + 1)) := by
    simpa only [Complex.add_re, Complex.one_re, add_zero] using
      hnormExp (s + 1) u hu
  have hmajor : Integrable
      (fun u : ℝ => (2 * (q : ℝ)) * Real.rpow u (-(s.re + 1)))
      (volume.restrict (Set.Ioi Y)) := by
    exact (integrableOn_Ioi_rpow_of_lt
      (a := -(s.re + 1)) (c := Y) (by linarith) hYpos).const_mul
        (2 * (q : ℝ))
  have hnormInt : IntegrableOn
      (fun u : ℝ => ‖contDiscrepancy q χ u *
        Complex.exp (-(s + 1) * (Real.log u : ℂ))‖) (Set.Ioi Y) :=
    (cont_tail_integrable hq χ hY s hs).norm
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioi Y)),
      ‖contDiscrepancy q χ u *
        Complex.exp (-(s + 1) * (Real.log u : ℂ))‖ ≤
          (2 * (q : ℝ)) * Real.rpow u (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := by
      have huY : Y < u := Set.mem_Ioi.mp hu
      linarith
    have hdisc := cont_discrepancy_bound hq χ (le_of_lt hu0)
    rw [norm_mul, hnormTail u hu0]
    exact mul_le_mul_of_nonneg_right hdisc (Real.rpow_nonneg hu0.le _)
  have hpowInt : ∫ u : ℝ in Set.Ioi Y, Real.rpow u (-(s.re + 1)) =
      Real.rpow Y (-s.re) / s.re := by
    have h := integral_Ioi_rpow_of_lt
      (a := -(s.re + 1)) (c := Y) (by linarith) hYpos
    rw [show -(s.re + 1) + 1 = -s.re by ring] at h
    calc
      _ = -Real.rpow Y (-s.re) / (-s.re) := by simpa using h
      _ = _ := by ring
  have hIntBound :
      ‖∫ u : ℝ in Set.Ioi Y,
          contDiscrepancy q χ u *
            Complex.exp (-(s + 1) * (Real.log u : ℂ))‖ ≤
        (2 * (q : ℝ)) * (Real.rpow Y (-s.re) / s.re) := by
    calc
      _ ≤ ∫ u : ℝ in Set.Ioi Y,
          ‖contDiscrepancy q χ u *
            Complex.exp (-(s + 1) * (Real.log u : ℂ))‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ u : ℝ in Set.Ioi Y,
          (2 * (q : ℝ)) * Real.rpow u (-(s.re + 1)) :=
          integral_mono_ae hnormInt hmajor hbound
      _ = (2 * (q : ℝ)) * (Real.rpow Y (-s.re) / s.re) := by
          rw [integral_const_mul, hpowInt]
  have hEnd : ‖-contDiscrepancy q χ Y *
        Complex.exp (-s * (Real.log Y : ℂ))‖ ≤
      (2 * (q : ℝ)) * Real.rpow Y (-s.re) := by
    rw [norm_mul, norm_neg, hnormEnd]
    exact mul_le_mul_of_nonneg_right
      (cont_discrepancy_bound hq χ (by linarith))
      (Real.rpow_nonneg (by linarith : 0 ≤ Y) _)
  unfold contTail
  calc
    _ ≤ ‖-contDiscrepancy q χ Y *
          Complex.exp (-s * (Real.log Y : ℂ))‖ +
        ‖s * ∫ u : ℝ in Set.Ioi Y,
          contDiscrepancy q χ u *
            Complex.exp (-(s + 1) * (Real.log u : ℂ))‖ := norm_add_le _ _
    _ = ‖-contDiscrepancy q χ Y *
          Complex.exp (-s * (Real.log Y : ℂ))‖ +
        ‖s‖ * ‖∫ u : ℝ in Set.Ioi Y,
          contDiscrepancy q χ u *
            Complex.exp (-(s + 1) * (Real.log u : ℂ))‖ := by
              simp only [norm_mul]
    _ ≤ (2 * (q : ℝ)) * Real.rpow Y (-s.re) +
        ‖s‖ * ((2 * (q : ℝ)) * (Real.rpow Y (-s.re) / s.re)) :=
          add_le_add hEnd (mul_le_mul_of_nonneg_left hIntBound (norm_nonneg s))
    _ = 2 * (q : ℝ) * (1 + ‖s‖ / s.re) * Real.rpow Y (-s.re) := by ring

private noncomputable def contCoeff (q : ℕ) (χ : DirichletCharacter ℂ q)
    (n : ℕ) : ℂ :=
  if n = 0 then 0 else χ (n : ZMod q)

private noncomputable def contKernel (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-s * (Real.log t : ℂ))

private theorem contPrefix_eq_Icc (q : ℕ) (χ : DirichletCharacter ℂ q)
    (u : ℝ) :
    contPrefix q χ u =
      ∑ n ∈ Finset.Icc 0 ⌊u⌋₊, contCoeff q χ n := by
  classical
  unfold contPrefix contCoeff
  have hset :
      (Finset.range (⌊u⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n) =
        (Finset.Icc 0 ⌊u⌋₊).filter (fun n : ℕ => 1 ≤ n) := by
    ext n
    simp [Nat.lt_succ_iff]
  rw [hset, Finset.sum_filter]
  simp [Nat.one_le_iff_ne_zero]

private theorem contPartialSum_eq_Icc (q : ℕ) (χ : DirichletCharacter ℂ q)
    (Y : ℝ) (s : ℂ) :
  dirichletPartialSum q χ Y s =
      ∑ n ∈ Finset.Icc 0 ⌊Y⌋₊,
        contKernel s (n : ℝ) * contCoeff q χ n := by
  classical
  unfold dirichletPartialSum contCoeff contKernel
  have hset :
      (Finset.range (⌊Y⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n) =
        (Finset.Icc 0 ⌊Y⌋₊).filter (fun n : ℕ => 1 ≤ n) := by
    ext n
    simp [Nat.lt_succ_iff]
  rw [hset, Finset.sum_filter]
  simp [Nat.one_le_iff_ne_zero, mul_comm]

private theorem contKernel_hasDerivAt {s : ℂ} {t : ℝ} (ht : 0 < t) :
    HasDerivAt (contKernel s) (-s * Complex.exp (-(s + 1) * (Real.log t : ℂ))) t := by
  let L : ℂ := (Real.log t : ℂ)
  have hlog : HasDerivAt (fun u : ℝ => (Real.log u : ℂ)) (t⁻¹ : ℂ) t := by
    convert (Complex.ofRealCLM.hasDerivAt (x := Real.log t)).scomp t
      (Real.hasDerivAt_log (ne_of_gt ht)) using 1 <;>
      simp [Function.comp_def, Complex.ofRealCLM_apply, smul_eq_mul,
        Complex.ofReal_inv]
  have harg : HasDerivAt (fun u : ℝ => -s * (Real.log u : ℂ))
      (-s * (t⁻¹ : ℂ)) t := by
    simpa using hlog.const_mul (-s)
  have hderiv := harg.cexp
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have hexpLog : Complex.exp (Real.log t : ℂ) = (t : ℂ) := by
    have hlogC : Complex.log (t : ℂ) = (Real.log t : ℂ) :=
      (Complex.ofReal_log ht.le).symm
    rw [← hlogC]
    exact Complex.exp_log htC
  have hexpNegLog : Complex.exp (-(Real.log t : ℂ)) = (t : ℂ)⁻¹ := by
    rw [Complex.exp_neg, hexpLog]
  convert hderiv using 1
  · funext u
    rfl
  · dsimp [L] at *
    rw [show -(s + 1) * (Real.log t : ℂ) =
      -s * (Real.log t : ℂ) + -(Real.log t : ℂ) by ring,
      Complex.exp_add, hexpNegLog]
    ring

private theorem contPrefix_eq_Icc_one (q : ℕ) (χ : DirichletCharacter ℂ q)
    (u : ℝ) :
    contPrefix q χ u =
      ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, χ (n : ZMod q) := by
  classical
  rw [contPrefix_eq_Icc]
  have hset : Finset.Icc 0 ⌊u⌋₊ =
      insert 0 (Finset.Icc 1 ⌊u⌋₊) := by
    ext n
    by_cases hn : n = 0 <;> simp [hn, Nat.one_le_iff_ne_zero]
  rw [hset, Finset.sum_insert (by simp)]
  simp only [contCoeff, ↓reduceIte, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := by omega
  simp [contCoeff, hn0]

private theorem contKernel_eq_cpow (s : ℂ) {t : ℝ} (ht : 0 < t) :
    contKernel s t = (t : ℂ) ^ (-s) := by
  unfold contKernel
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne')]
  rw [← Complex.ofReal_log ht.le]
  congr 1 <;> ring

private theorem contPartialSum_abel {q : ℕ} (χ : DirichletCharacter ℂ q)
    {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ) :
    dirichletPartialSum q χ Y s =
      contKernel s Y * contPrefix q χ Y +
        s * ∫ t : ℝ in Set.Ioc 1 Y,
          contPrefix q χ t * Complex.exp (-(s + 1) * (Real.log t : ℂ)) := by
  classical
  have hc0 : contCoeff q χ 0 = 0 := by simp [contCoeff]
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Y) :
      deriv (contKernel s) t =
        -s * Complex.exp (-(s + 1) * (Real.log t : ℂ)) := by
    apply (contKernel_hasDerivAt (s := s) (t := t) (by linarith [ht.1])).deriv
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) Y, DifferentiableAt ℝ (contKernel s) t := by
    intro t ht
    exact (contKernel_hasDerivAt (s := s) (t := t) (by linarith [ht.1])).differentiableAt
  have hlogCont : ContinuousOn (fun t : ℝ => (Real.log t : ℂ))
      (Set.Icc (1 : ℝ) Y) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    apply Real.continuousOn_log.mono
    intro t ht
    simp
    linarith [ht.1]
  have hexpCont : ContinuousOn (fun t : ℝ =>
      Complex.exp (-(s + 1) * (Real.log t : ℂ))) (Set.Icc (1 : ℝ) Y) := by
    have harg : ContinuousOn (fun t : ℝ =>
        (-(s + 1)) * (Real.log t : ℂ)) (Set.Icc (1 : ℝ) Y) := by
      exact (continuousOn_const : ContinuousOn (fun _ : ℝ => -(s + 1)) _).mul hlogCont
    exact Complex.continuous_exp.comp_continuousOn harg
  have hderivCont : ContinuousOn (deriv (contKernel s)) (Set.Icc 1 Y) := by
    apply ((continuousOn_const : ContinuousOn (fun _ : ℝ => -s) _).mul hexpCont).congr
    intro t ht
    exact hderiv t ht
  have hint : IntegrableOn (deriv (contKernel s)) (Set.Icc (1 : ℝ) Y) :=
    hderivCont.integrableOn_Icc
  have habel := sum_mul_eq_sub_integral_mul₀ (c := contCoeff q χ)
    (f := contKernel s) hc0 (b := Y) hdiff hint
  have hI :
      (∫ t : ℝ in Set.Ioc 1 Y,
        deriv (contKernel s) t * contPrefix q χ t) =
        -s * ∫ t : ℝ in Set.Ioc 1 Y,
          contPrefix q χ t * Complex.exp (-(s + 1) * (Real.log t : ℂ)) := by
    calc
      _ = ∫ t : ℝ in Set.Ioc 1 Y,
          (-s) * (contPrefix q χ t *
            Complex.exp (-(s + 1) * (Real.log t : ℂ))) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          change deriv (contKernel s) t * contPrefix q χ t =
            (-s) * (contPrefix q χ t *
              Complex.exp (-(s + 1) * (Real.log t : ℂ)))
          have htpos : 0 < t := by
            have := Set.mem_Ioc.mp ht
            linarith
          have htIcc : t ∈ Set.Icc (1 : ℝ) Y := by
            exact ⟨(Set.mem_Ioc.mp ht).1.le, (Set.mem_Ioc.mp ht).2⟩
          rw [hderiv t htIcc]
          ring
      _ = -s * ∫ t : ℝ in Set.Ioc 1 Y,
          contPrefix q χ t * Complex.exp (-(s + 1) * (Real.log t : ℂ)) :=
            integral_const_mul _ _
  rw [← contPartialSum_eq_Icc] at habel
  simp_rw [← contPrefix_eq_Icc q χ] at habel
  rw [hI] at habel
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using habel

private theorem contLSeries_integral_repr {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    dirichletLValue q hq χ s =
      s * ∫ t : ℝ in Set.Ioi 1,
        contPrefix q χ t * Complex.exp (-(s + 1) * (Real.log t : ℂ)) := by
  classical
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hS : LSeriesSummable (χ ·) s :=
    ZMod.LSeriesSummable_of_one_lt_re χ hs
  have hO :
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    apply IsBigO.of_norm_le
    intro n
    rw [Real.rpow_one]
    calc
      ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤
          ∑ k ∈ Finset.Icc 1 n, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact χ.norm_le_one _
      _ = (Finset.Icc 1 n).card := by simp
      _ ≤ n := by
        simp
  have hrepr := LSeries_eq_mul_integral (f := fun n : ℕ => χ (n : ZMod q))
    (r := 1) (by norm_num) hs hS hO
  have hprefix (t : ℝ) :
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) = contPrefix q χ t :=
    (contPrefix_eq_Icc_one q χ t).symm
  have hkernel (t : ℝ) (ht : 0 < t) :
      (t : ℂ) ^ (-(s + 1)) =
        Complex.exp (-(s + 1) * (Real.log t : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne'),
      ← Complex.ofReal_log ht.le]
    congr 1 <;> ring
  have hInt :
      (∫ t : ℝ in Set.Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) *
          (t : ℂ) ^ (-(s + 1))) =
        ∫ t : ℝ in Set.Ioi 1,
          contPrefix q χ t * Complex.exp (-(s + 1) * (Real.log t : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) *
        (t : ℂ) ^ (-(s + 1)) =
      contPrefix q χ t * Complex.exp (-(s + 1) * (Real.log t : ℂ))
    have htpos : 0 < t := by
      have ht' := Set.mem_Ioi.mp ht
      linarith
    rw [hprefix t, hkernel t htpos]
  rw [dirichletLValue, DirichletCharacter.LFunction_eq_LSeries χ hs,
    hrepr, hInt]

private theorem contPrefix_norm_le {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : 1 ≤ u) :
    ‖contPrefix q χ u‖ ≤ u + 2 * (q : ℝ) := by
  have hdecomp : contPrefix q χ u =
      contDiscrepancy q χ u + characterMean q χ * (u : ℂ) := by
    unfold contDiscrepancy
    ring
  have hmean := cont_characterMean_norm_le_one hq χ
  have hmeanTerm : ‖characterMean q χ * (u : ℂ)‖ ≤ u := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ u)]
    calc
      ‖characterMean q χ‖ * u ≤ 1 * u := mul_le_mul_of_nonneg_right hmean (by linarith)
      _ = u := by ring
  calc
    ‖contPrefix q χ u‖ ≤
        ‖contDiscrepancy q χ u‖ + ‖characterMean q χ * (u : ℂ)‖ := by
          rw [hdecomp]
          exact norm_add_le _ _
    _ ≤ 2 * (q : ℝ) + u :=
      add_le_add (cont_discrepancy_bound hq χ (by linarith)) hmeanTerm
    _ = u + 2 * (q : ℝ) := by ring

private theorem contPrefix_kernel_integrable {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ)
    (hs : 1 < s.re) :
    IntegrableOn
      (fun u : ℝ => contPrefix q χ u *
        Complex.exp (-(s + 1) * (Real.log u : ℂ))) (Set.Ioi Y) := by
  let f : ℝ → ℂ := fun u => contPrefix q χ u *
    Complex.exp (-(s + 1) * (Real.log u : ℂ))
  let μ : Measure ℝ := volume.restrict (Set.Ioi Y)
  let p : ℕ → ℂ := fun m =>
    ∑ n ∈ (Finset.range (m + 1)).filter (fun n : ℕ => 1 ≤ n),
      χ (n : ZMod q)
  have hprefix : Measurable (contPrefix q χ) := by
    change Measurable (fun u : ℝ => p (⌊u⌋₊))
    exact (measurable_of_countable p).comp Nat.measurable_floor
  have hlog : Measurable (fun u : ℝ => (Real.log u : ℂ)) :=
    Complex.measurable_ofReal.comp Real.measurable_log
  have hexp : Measurable (fun u : ℝ =>
      Complex.exp (-(s + 1) * (Real.log u : ℂ))) :=
    Complex.measurable_exp.comp (measurable_const.mul hlog)
  have hf : AEStronglyMeasurable f μ := by
    dsimp [f, μ]
    exact (hprefix.aestronglyMeasurable.restrict).mul
      (hexp.aestronglyMeasurable.restrict)
  have hmajor : Integrable
      (fun u : ℝ => (1 + 2 * (q : ℝ)) * Real.rpow u (-s.re)) μ := by
    dsimp [μ]
    exact (integrableOn_Ioi_rpow_of_lt
      (a := -s.re) (c := Y) (by linarith) (by linarith)).const_mul
        (1 + 2 * (q : ℝ))
  have hnormExp (u : ℝ) (hu : 0 < u) :
      ‖Complex.exp (-(s + 1) * (Real.log u : ℂ))‖ =
        Real.rpow u (-(s.re + 1)) := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.neg_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.add_re, Complex.one_re, add_zero]
    calc
      Real.exp (-(s.re + 1) * Real.log u) =
          Real.exp (Real.log u * (-(s.re + 1))) := by congr 1 <;> ring
      _ = Real.rpow u (-(s.re + 1)) := (Real.rpow_def_of_pos hu _).symm
  have hbound : ∀ᵐ u ∂μ, ‖f u‖ ≤
      (1 + 2 * (q : ℝ)) * Real.rpow u (-s.re) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huY : Y < u := Set.mem_Ioi.mp hu
    have hu1 : 1 ≤ u := by linarith [hY]
    have hu0 : 0 < u := by linarith
    have hprefixBound := contPrefix_norm_le hq χ hu1
    have hscale : u + 2 * (q : ℝ) ≤ (1 + 2 * (q : ℝ)) * u := by
      have hqnonneg : 0 ≤ (q : ℝ) := by positivity
      nlinarith
    have hpow : u * Real.rpow u (-(s.re + 1)) = Real.rpow u (-s.re) := by
      have hadd : Real.rpow u (1 + -(s.re + 1)) =
          Real.rpow u 1 * Real.rpow u (-(s.re + 1)) := by
        simpa only [Real.rpow_eq_pow] using
          (Real.rpow_add hu0 1 (-(s.re + 1)))
      calc
        _ = Real.rpow u 1 * Real.rpow u (-(s.re + 1)) := by simp
        _ = Real.rpow u (1 + -(s.re + 1)) := hadd.symm
        _ = Real.rpow u (-s.re) := by congr 1 <;> ring
    dsimp [f]
    rw [norm_mul, hnormExp u hu0]
    calc
      _ ≤ (u + 2 * (q : ℝ)) * Real.rpow u (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_right hprefixBound
          (Real.rpow_nonneg hu0.le _)
      _ ≤ ((1 + 2 * (q : ℝ)) * u) * Real.rpow u (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hu0.le _)
      _ = (1 + 2 * (q : ℝ)) * Real.rpow u (-s.re) := by
        calc
          _ = (1 + 2 * (q : ℝ)) *
              (u * Real.rpow u (-(s.re + 1))) := by ring
          _ = (1 + 2 * (q : ℝ)) * Real.rpow u (-s.re) := by rw [hpow]
  exact hmajor.mono' hf hbound

private theorem contMeanKernel_eq {s : ℂ} {t : ℝ} (ht : 0 < t) :
    (t : ℂ) * Complex.exp (-(s + 1) * (Real.log t : ℂ)) =
      Complex.exp (-s * (Real.log t : ℂ)) := by
  let L : ℂ := (Real.log t : ℂ)
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hexpLog : Complex.exp L = (t : ℂ) := by
    have hlogC : Complex.log (t : ℂ) = L :=
      (Complex.ofReal_log ht.le).symm
    rw [← hlogC]
    exact Complex.exp_log htC
  have hexpNegLog : Complex.exp (-L) = (t : ℂ)⁻¹ := by
    rw [Complex.exp_neg, hexpLog]
  have hsplit : Complex.exp (-(s + 1) * L) =
      Complex.exp (-s * L) * Complex.exp (-L) := by
    rw [show -(s + 1) * L = -s * L + -L by ring, Complex.exp_add]
  calc
    (t : ℂ) * Complex.exp (-(s + 1) * (Real.log t : ℂ)) =
        Complex.exp L * (Complex.exp (-s * L) * Complex.exp (-L)) := by
          rw [← hexpLog, hsplit]
    _ = Complex.exp (-s * L) := by
          rw [hexpNegLog]
          field_simp
          exact hexpLog

private theorem cont_abel_identity_right {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ)
    (hs : 1 < s.re) :
    dirichletLValue q hq χ s = dirichletPartialSum q χ Y s +
      characterMean q χ *
        Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1) +
      contTail q χ Y s := by
  let g : ℝ → ℂ := fun u => contPrefix q χ u *
    Complex.exp (-(s + 1) * (Real.log u : ℂ))
  have hGint := contPrefix_kernel_integrable (Y := 1) hq χ (by norm_num) s hs
  have hIocSub : Set.Ioc (1 : ℝ) Y ⊆ Set.Ioi 1 := by
    intro u hu
    exact (Set.mem_Ioc.mp hu).1
  have hIoiSub : Set.Ioi Y ⊆ Set.Ioi (1 : ℝ) := Set.Ioi_subset_Ioi hY
  have hIocInt : IntegrableOn g (Set.Ioc (1 : ℝ) Y) := by
    exact hGint.mono_set hIocSub
  have hIoiInt : IntegrableOn g (Set.Ioi Y) := hGint.mono_set hIoiSub
  have hdisj : Disjoint (Set.Ioc (1 : ℝ) Y) (Set.Ioi Y) := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    exact not_lt_of_ge (Set.mem_Ioc.mp hu).2 (Set.mem_Ioi.mp hv)
  have hUnion : Set.Ioc (1 : ℝ) Y ∪ Set.Ioi Y = Set.Ioi 1 := by
    ext u
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, hY'⟩ | hY') <;> linarith
    · intro hu
      by_cases huY : u ≤ Y
      · exact Or.inl ⟨by linarith, huY⟩
      · exact Or.inr (lt_of_not_ge huY)
  have hsplitInt :
      (∫ u : ℝ in Set.Ioi 1, g u) =
        (∫ u : ℝ in Set.Ioc 1 Y, g u) +
          ∫ u : ℝ in Set.Ioi Y, g u := by
    rw [← hUnion]
    exact setIntegral_union hdisj measurableSet_Ioi hIocInt hIoiInt
  have hEint := cont_tail_integrable hq χ hY s (by linarith)
  have hMeanInt : IntegrableOn
      (fun u : ℝ => characterMean q χ *
        ((u : ℂ) * Complex.exp (-(s + 1) * (Real.log u : ℂ))))
      (Set.Ioi Y) := by
    have hsub := hIoiInt.sub hEint
    apply hsub.congr
    filter_upwards [] with u
    dsimp [g]
    rw [show contPrefix q χ u =
      characterMean q χ * (u : ℂ) + contDiscrepancy q χ u by
        unfold contDiscrepancy; ring]
    ring
  have hsplitTail :
      (∫ u : ℝ in Set.Ioi Y, g u) =
        characterMean q χ *
          (∫ u : ℝ in Set.Ioi Y,
            (u : ℂ) * Complex.exp (-(s + 1) * (Real.log u : ℂ))) +
          (∫ u : ℝ in Set.Ioi Y,
            contDiscrepancy q χ u *
              Complex.exp (-(s + 1) * (Real.log u : ℂ))) := by
    calc
      _ = ∫ u : ℝ in Set.Ioi Y,
          characterMean q χ *
              ((u : ℂ) * Complex.exp (-(s + 1) * (Real.log u : ℂ))) +
            contDiscrepancy q χ u *
              Complex.exp (-(s + 1) * (Real.log u : ℂ)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          dsimp [g]
          rw [show contPrefix q χ u =
            characterMean q χ * (u : ℂ) + contDiscrepancy q χ u by
              unfold contDiscrepancy; ring]
          ring
      _ = _ := by
          calc
            _ =
                (∫ u : ℝ in Set.Ioi Y,
                    characterMean q χ *
                      ((u : ℂ) * Complex.exp (-(s + 1) * (Real.log u : ℂ)))) +
                  ∫ u : ℝ in Set.Ioi Y,
                    contDiscrepancy q χ u *
                      Complex.exp (-(s + 1) * (Real.log u : ℂ)) :=
                    integral_add hMeanInt hEint
            _ = _ := by rw [integral_const_mul]
  have hmeanKernel (u : ℝ) (hu : 0 < u) :
      (u : ℂ) * Complex.exp (-(s + 1) * (Real.log u : ℂ)) =
        Complex.exp (-s * (Real.log u : ℂ)) := contMeanKernel_eq hu
  have hmeanToCpow :
      (∫ u : ℝ in Set.Ioi Y,
        (u : ℂ) * Complex.exp (-(s + 1) * (Real.log u : ℂ))) =
        ∫ u : ℝ in Set.Ioi Y, (u : ℂ) ^ (-s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu0 : 0 < u := by
      have := Set.mem_Ioi.mp hu
      linarith
    calc
      _ = Complex.exp (-s * (Real.log u : ℂ)) := hmeanKernel u hu0
      _ = contKernel s u := rfl
      _ = (u : ℂ) ^ (-s) := contKernel_eq_cpow s hu0
  have hYpos : 0 < Y := by linarith
  have hmeanCpow := integral_Ioi_cpow_of_lt
    (a := -s) (c := Y) (by simp [Complex.neg_re]; linarith) hYpos
  have hYc : (Y : ℂ) ≠ 0 := by exact_mod_cast hYpos.ne'
  have hexpY : Complex.exp ((1 - s) * (Real.log Y : ℂ)) =
      (Y : ℂ) ^ (1 - s) := by
    rw [Complex.cpow_def_of_ne_zero hYc, ← Complex.ofReal_log (by linarith : 0 ≤ Y)]
    congr 1 <;> ring
  have hmeanCalc :
      characterMean q χ *
        (s * (∫ u : ℝ in Set.Ioi Y, (u : ℂ) *
          Complex.exp (-(s + 1) * (Real.log u : ℂ))) -
          (Y : ℂ) * Complex.exp (-s * (Real.log Y : ℂ))) =
      characterMean q χ *
        Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1) := by
    rw [hmeanToCpow, hmeanCpow]
    have hkernelY : Complex.exp (-s * (Real.log Y : ℂ)) = (Y : ℂ) ^ (-s) :=
      contKernel_eq_cpow s hYpos
    have hpowExp : -s + 1 = 1 - s := by ring
    have hpowMul : (Y : ℂ) * (Y : ℂ) ^ (-s) = (Y : ℂ) ^ (1 - s) := by
      calc
        _ = (Y : ℂ) ^ (1 : ℂ) * (Y : ℂ) ^ (-s) := by rw [Complex.cpow_one]
        _ = (Y : ℂ) ^ (1 + -s) := (Complex.cpow_add 1 (-s) hYc).symm
        _ = (Y : ℂ) ^ (1 - s) := by congr 1 <;> ring
    have hden : s - 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hden' : 1 - s ≠ 0 := by
      intro h
      apply hden
      calc
        s - 1 = -(1 - s) := by ring
        _ = 0 := by rw [h]; simp
    rw [hkernelY, hpowExp, hpowMul, hexpY]
    field_simp [hden, hden']
    ring
  have hL := contLSeries_integral_repr hq χ hs
  rw [hsplitInt] at hL
  have hP := contPartialSum_abel (q := q) χ hY s
  have hdecompY : contPrefix q χ Y =
      characterMean q χ * (Y : ℂ) + contDiscrepancy q χ Y := by
    unfold contDiscrepancy
    ring
  have hidentity :
      dirichletLValue q hq χ s = dirichletPartialSum q χ Y s -
        contKernel s Y * contPrefix q χ Y +
          s * ∫ u : ℝ in Set.Ioi Y, g u := by
    rw [hL, hP]
    ring
  rw [hsplitTail, hdecompY, contKernel] at hidentity
  have hcombined :
      dirichletLValue q hq χ s = dirichletPartialSum q χ Y s +
        characterMean q χ *
          (s *
            (∫ u : ℝ in Set.Ioi Y,
              (u : ℂ) * Complex.exp (-(s + 1) * (Real.log u : ℂ))) -
            (Y : ℂ) * Complex.exp (-s * (Real.log Y : ℂ))) +
        (-contDiscrepancy q χ Y *
            Complex.exp (-s * (Real.log Y : ℂ)) +
          s * ∫ u : ℝ in Set.Ioi Y,
            contDiscrepancy q χ u *
              Complex.exp (-(s + 1) * (Real.log u : ℂ))) := by
    calc
      _ = dirichletPartialSum q χ Y s -
          Complex.exp (-s * (Real.log Y : ℂ)) *
            (characterMean q χ * (Y : ℂ) + contDiscrepancy q χ Y) +
          s * (characterMean q χ *
            (∫ u : ℝ in Set.Ioi Y,
              (u : ℂ) * Complex.exp (-(s + 1) * (Real.log u : ℂ))) +
            (∫ u : ℝ in Set.Ioi Y,
              contDiscrepancy q χ u *
                Complex.exp (-(s + 1) * (Real.log u : ℂ)))) := hidentity
      _ = _ := by ring
  calc
    dirichletLValue q hq χ s = dirichletPartialSum q χ Y s +
        characterMean q χ *
          (s *
            (∫ u : ℝ in Set.Ioi Y,
              (u : ℂ) * Complex.exp (-(s + 1) * (Real.log u : ℂ))) -
            (Y : ℂ) * Complex.exp (-s * (Real.log Y : ℂ))) +
        (-contDiscrepancy q χ Y *
            Complex.exp (-s * (Real.log Y : ℂ)) +
          s * ∫ u : ℝ in Set.Ioi Y,
            contDiscrepancy q χ u *
              Complex.exp (-(s + 1) * (Real.log u : ℂ))) := hcombined
    _ = dirichletPartialSum q χ Y s +
        characterMean q χ *
          Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1) +
        (-contDiscrepancy q χ Y *
            Complex.exp (-s * (Real.log Y : ℂ)) +
          s * ∫ u : ℝ in Set.Ioi Y,
            contDiscrepancy q χ u *
              Complex.exp (-(s + 1) * (Real.log u : ℂ))) := by
          rw [hmeanCalc]
    _ = _ := by simpa [contTail, add_assoc]

private theorem cont_abel_identity_upper {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ)
    (hs : 0 < s.re) (him : 0 < s.im) :
    dirichletLValue q hq χ s = dirichletPartialSum q χ Y s +
      characterMean q χ *
        Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1) +
      contTail q χ Y s := by
  let U : Set ℂ := {z | 0 < z.re ∧ 0 < z.im}
  let F : ℂ → ℂ := fun z => dirichletLValue q hq χ z
  let G : ℂ → ℂ := fun z => dirichletPartialSum q χ Y z +
    characterMean q χ *
      Complex.exp ((1 - z) * (Real.log Y : ℂ)) / (z - 1) +
    contTail q χ Y z
  have hUopen : IsOpen U := by
    change IsOpen ({z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hUconvex : Convex ℝ U := by
    change Convex ℝ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im})
    exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
  have hF : AnalyticOnNhd ℂ F U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
    have hz1 : z ≠ 1 := by
      intro h
      have him0 := congrArg Complex.im h
      simp at him0
      linarith [hz.2]
    simpa [F, dirichletLValue] using
      (DirichletCharacter.differentiableAt_LFunction χ z (.inl hz1)).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    have hpart : DifferentiableAt ℂ (fun w => dirichletPartialSum q χ Y w) z := by
      fun_prop [dirichletPartialSum]
    have hz1 : z - 1 ≠ 0 := by
      intro h
      have him0 := congrArg Complex.im h
      simp at him0
      linarith [hz.2]
    have hpole : DifferentiableAt ℂ
        (fun w => characterMean q χ *
          Complex.exp ((1 - w) * (Real.log Y : ℂ)) / (w - 1)) z := by
      fun_prop
    have htail := contTail_differentiableAt hq χ hY hz.1
    change DifferentiableWithinAt ℂ
      ((fun w => dirichletPartialSum q χ Y w) +
        (fun w => characterMean q χ *
          Complex.exp ((1 - w) * (Real.log Y : ℂ)) / (w - 1)) +
        (fun w => contTail q χ Y w)) U z
    exact ((hpart.add hpole).add htail).differentiableWithinAt
  have hbase : (2 + Complex.I : ℂ) ∈ U := by
    simp [U]
  have hlocal : F =ᶠ[nhds (2 + Complex.I)] G := by
    have hRe : {z : ℂ | 1 < z.re} ∈ nhds (2 + Complex.I) := by
      exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hRe] with z hz
    simpa [F, G] using cont_abel_identity_right hq χ hY z hz
  have hsU : s ∈ U := ⟨hs, him⟩
  have hEq := hF.eqOn_of_preconnected_of_eventuallyEq hG hUconvex.isPreconnected
    hbase hlocal hsU
  simpa [F, G] using hEq

private theorem cont_abel_identity_lower {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ)
    (hs : 0 < s.re) (him : s.im < 0) :
    dirichletLValue q hq χ s = dirichletPartialSum q χ Y s +
      characterMean q χ *
        Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1) +
      contTail q χ Y s := by
  let U : Set ℂ := {z | 0 < z.re ∧ z.im < 0}
  let F : ℂ → ℂ := fun z => dirichletLValue q hq χ z
  let G : ℂ → ℂ := fun z => dirichletPartialSum q χ Y z +
    characterMean q χ *
      Complex.exp ((1 - z) * (Real.log Y : ℂ)) / (z - 1) +
    contTail q χ Y z
  have hUopen : IsOpen U := by
    change IsOpen ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hUconvex : Convex ℝ U := by
    change Convex ℝ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0})
    exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)
  have hF : AnalyticOnNhd ℂ F U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
    have hz1 : z ≠ 1 := by
      intro h
      have him0 := congrArg Complex.im h
      simp at him0
      linarith [hz.2]
    simpa [F, dirichletLValue] using
      (DirichletCharacter.differentiableAt_LFunction χ z (.inl hz1)).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    have hpart : DifferentiableAt ℂ (fun w => dirichletPartialSum q χ Y w) z := by
      fun_prop [dirichletPartialSum]
    have hz1 : z - 1 ≠ 0 := by
      intro h
      have him0 := congrArg Complex.im h
      simp at him0
      linarith [hz.2]
    have hpole : DifferentiableAt ℂ
        (fun w => characterMean q χ *
          Complex.exp ((1 - w) * (Real.log Y : ℂ)) / (w - 1)) z := by
      fun_prop
    have htail := contTail_differentiableAt hq χ hY hz.1
    change DifferentiableWithinAt ℂ
      ((fun w => dirichletPartialSum q χ Y w) +
        (fun w => characterMean q χ *
          Complex.exp ((1 - w) * (Real.log Y : ℂ)) / (w - 1)) +
        (fun w => contTail q χ Y w)) U z
    exact ((hpart.add hpole).add htail).differentiableWithinAt
  have hbase : (2 - Complex.I : ℂ) ∈ U := by
    simp [U]
  have hlocal : F =ᶠ[nhds (2 - Complex.I)] G := by
    have hRe : {z : ℂ | 1 < z.re} ∈ nhds (2 - Complex.I) := by
      exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hRe] with z hz
    simpa [F, G] using cont_abel_identity_right hq χ hY z hz
  have hsU : s ∈ U := ⟨hs, him⟩
  have hEq := hF.eqOn_of_preconnected_of_eventuallyEq hG hUconvex.isPreconnected
    hbase hlocal hsU
  simpa [F, G] using hEq

theorem cont_abel_identity {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ)
    (hs : 0 < s.re) (him : s.im ≠ 0) :
    dirichletLValue q hq χ s = dirichletPartialSum q χ Y s +
      characterMean q χ *
        Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1) +
      contTail q χ Y s := by
  rcases lt_or_gt_of_ne him with him | him
  · exact cont_abel_identity_lower hq χ hY s hs him
  · exact cont_abel_identity_upper hq χ hY s hs him

theorem cont_approximation {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hσlo : 1 / 2 ≤ s.re) (hσhi : s.re ≤ 2)
    (him : 1 / 2 ≤ |s.im|) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖dirichletLValue q hq χ s - dirichletPartialSum q χ Y s -
      characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1)‖ ≤
      4 * (q : ℝ) * (1 + ‖s‖) * Real.rpow Y (-s.re) := by
  have hs : 0 < s.re := by linarith
  have himne : s.im ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at him
    norm_num at him
  have habel := cont_abel_identity hq χ hY s hs himne
  have hsub : dirichletLValue q hq χ s - dirichletPartialSum q χ Y s -
      characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1) =
      contTail q χ Y s := by
    rw [habel]
    ring
  rw [hsub]
  have hdiv : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    apply (div_le_iff₀ hs).2
    nlinarith [mul_nonneg (norm_nonneg s)
      (sub_nonneg.mpr (by linarith : (1 / 2 : ℝ) ≤ s.re))]
  have hfactor : 1 + ‖s‖ / s.re ≤ 2 * (1 + ‖s‖) := by
    calc
      1 + ‖s‖ / s.re ≤ 1 + 2 * ‖s‖ := by linarith [hdiv]
      _ ≤ 2 * (1 + ‖s‖) := by nlinarith
  have hcoeff : 2 * (q : ℝ) * (1 + ‖s‖ / s.re) ≤
      4 * (q : ℝ) * (1 + ‖s‖) := by
    calc
      2 * (q : ℝ) * (1 + ‖s‖ / s.re) ≤
          2 * (q : ℝ) * (2 * (1 + ‖s‖)) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = 4 * (q : ℝ) * (1 + ‖s‖) := by ring
  have hY0 : 0 ≤ Y := by linarith
  calc
    ‖contTail q χ Y s‖ ≤
        2 * (q : ℝ) * (1 + ‖s‖ / s.re) * Real.rpow Y (-s.re) :=
      cont_tail_bound hq χ hY s hs
    _ ≤ 4 * (q : ℝ) * (1 + ‖s‖) * Real.rpow Y (-s.re) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hY0 _)

theorem cont_partial_sum_bound (q : ℕ) (χ : DirichletCharacter ℂ q)
    {Y σ v : ℝ} (hY : 1 ≤ Y) :
    ‖dirichletPartialSum q χ Y (⟨σ, v⟩ : ℂ)‖ ≤
      (1 + Real.log Y) * max 1 (Real.rpow Y (1 - σ)) := by
  classical
  let z : ℂ := ⟨σ, v⟩
  have hzre : z.re = σ := rfl
  have hnormExp {n : ℕ} (hn : 0 < n) :
      ‖Complex.exp (-z * (Real.log (n : ℝ) : ℂ))‖ =
        Real.rpow (n : ℝ) (-z.re) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [Complex.norm_exp, Complex.mul_re, Complex.neg_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    change Real.exp (-z.re * Real.log (n : ℝ)) = (n : ℝ) ^ (-z.re)
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    ring
  have hnormSum :
      ‖dirichletPartialSum q χ Y z‖ ≤
        ∑ n ∈ (Finset.range (⌊Y⌋₊ + 1)).filter (fun n => 1 ≤ n),
          Real.rpow (n : ℝ) (-σ) := by
    unfold dirichletPartialSum
    calc
      _ ≤ ∑ n ∈ (Finset.range (⌊Y⌋₊ + 1)).filter (fun n => 1 ≤ n),
          ‖χ (n : ZMod q) * Complex.exp (-z * (Real.log (n : ℝ) : ℂ))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ (Finset.range (⌊Y⌋₊ + 1)).filter (fun n => 1 ≤ n),
          Real.rpow (n : ℝ) (-σ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_filter.mp hn).2
        have hnpos : 0 < n := by omega
        calc
          ‖χ (n : ZMod q) * Complex.exp (-z * (Real.log (n : ℝ) : ℂ))‖ =
              ‖χ (n : ZMod q)‖ * Real.rpow (n : ℝ) (-σ) := by
                rw [norm_mul, hnormExp hnpos, hzre]
          _ ≤ 1 * Real.rpow (n : ℝ) (-σ) :=
            mul_le_mul_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg (by positivity) _)
          _ = _ := one_mul _
  have hfilter :
      (Finset.range (⌊Y⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n) =
        Finset.Icc 1 ⌊Y⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hsumInv :
      (∑ n ∈ (Finset.range (⌊Y⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n),
        (n : ℝ)⁻¹) = harmonic ⌊Y⌋₊ := by
    rw [hfilter]
    simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hsumBound :
      (∑ n ∈ (Finset.range (⌊Y⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n),
        Real.rpow (n : ℝ) (-σ)) ≤
        (1 + Real.log Y) * max 1 (Real.rpow Y (1 - σ)) := by
    calc
      _ ≤ ∑ n ∈ (Finset.range (⌊Y⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n),
          max 1 (Real.rpow Y (1 - σ)) * (n : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_filter.mp hn).2
        have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have hnpos : 0 < (n : ℝ) := by positivity
        have hnYnat : n ≤ ⌊Y⌋₊ := by
          have hnrange := (Finset.mem_filter.mp hn).1
          have := Finset.mem_range.mp hnrange
          omega
        have hnY : (n : ℝ) ≤ Y := by
          calc
            (n : ℝ) ≤ ⌊Y⌋₊ := by exact_mod_cast hnYnat
            _ ≤ Y := Nat.floor_le (by linarith : 0 ≤ Y)
        have hpowEq : Real.rpow (n : ℝ) (-σ) =
            (n : ℝ)⁻¹ * Real.rpow (n : ℝ) (1 - σ) := by
          change (n : ℝ) ^ (-σ) = (n : ℝ)⁻¹ * (n : ℝ) ^ (1 - σ)
          rw [Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos]
          calc
            Real.exp (Real.log (n : ℝ) * (-σ)) =
                Real.exp (-Real.log (n : ℝ) + Real.log (n : ℝ) * (1 - σ)) := by
                  congr 1 <;> ring
            _ = Real.exp (-Real.log (n : ℝ)) *
                Real.exp (Real.log (n : ℝ) * (1 - σ)) := by rw [Real.exp_add]
            _ = (n : ℝ)⁻¹ * Real.exp (Real.log (n : ℝ) * (1 - σ)) := by
                  rw [Real.exp_neg, Real.exp_log hnpos]
        have hpowBound : Real.rpow (n : ℝ) (1 - σ) ≤
            max 1 (Real.rpow Y (1 - σ)) := by
          by_cases hexp : 0 ≤ 1 - σ
          · exact (Real.rpow_le_rpow (by positivity) hnY hexp).trans
              (le_max_right _ _)
          · exact (Real.rpow_le_one_of_one_le_of_nonpos hnR1
                (not_le.mp hexp).le).trans (le_max_left _ _)
        rw [hpowEq]
        calc
          (n : ℝ)⁻¹ * Real.rpow (n : ℝ) (1 - σ) ≤
              (n : ℝ)⁻¹ * max 1 (Real.rpow Y (1 - σ)) :=
            mul_le_mul_of_nonneg_left hpowBound (inv_nonneg.mpr hnpos.le)
          _ = max 1 (Real.rpow Y (1 - σ)) * (n : ℝ)⁻¹ := by ring
      _ = max 1 (Real.rpow Y (1 - σ)) * harmonic ⌊Y⌋₊ := by
        rw [← Finset.mul_sum, hsumInv]
      _ ≤ max 1 (Real.rpow Y (1 - σ)) * (1 + Real.log Y) :=
        mul_le_mul_of_nonneg_left (harmonic_floor_le_one_add_log Y hY) (by positivity)
      _ = (1 + Real.log Y) * max 1 (Real.rpow Y (1 - σ)) := by ring
  calc
    ‖dirichletPartialSum q χ Y (⟨σ, v⟩ : ℂ)‖ =
        ‖dirichletPartialSum q χ Y z‖ := by rfl
    _ ≤ ∑ n ∈ (Finset.range (⌊Y⌋₊ + 1)).filter (fun n => 1 ≤ n),
          Real.rpow (n : ℝ) (-σ) := hnormSum
    _ ≤ (1 + Real.log Y) * max 1 (Real.rpow Y (1 - σ)) := hsumBound

private theorem cont_character_phase_interval_bound {q : ℕ} [NeZero q]
    (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    {N' v L T Cφ C₃ : ℝ} (hN' : 0 < N')
    (I : Finset ℕ)
    (hPhase : ∀ a : ZMod q,
      ‖residuePhaseSum N' q a (-v) (I : Set ℕ)‖ ≤
        Cφ * (N' / q) * Real.exp (-L / Real.rpow T C₃)) :
    ‖∑ n ∈ (Finset.range (⌊2 * N'⌋₊ + 1)).filter
        (fun n : ℕ => N' ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N' ∧ n ∈ I),
      χ (n : ZMod q) *
      Complex.exp (Complex.I * (-v) * (Real.log (n : ℝ) : ℂ))‖ ≤
      Cφ * N' * Real.exp (-L / Real.rpow T C₃) := by
  classical
  let S : Finset ℕ := (Finset.range (⌊2 * N'⌋₊ + 1)).filter
    (fun n : ℕ => N' ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N' ∧ n ∈ I)
  let f : ℕ → ℂ := fun n => χ (n : ZMod q) *
    Complex.exp (Complex.I * (-v) * (Real.log (n : ℝ) : ℂ))
  have hpartition :
      (∑ a : ZMod q,
        ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = a), f n) =
        ∑ n ∈ S, f n := by
    exact Finset.sum_fiberwise S (fun n : ℕ => (n : ZMod q)) f
  have hinner (a : ZMod q) :
      (∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = a), f n) =
        χ a * residuePhaseSum N' q a (-v) (I : Set ℕ) := by
    calc
      _ = ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = a),
          χ a * Complex.exp (Complex.I * (-v) * (Real.log (n : ℝ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hna : (n : ZMod q) = a := (Finset.mem_filter.mp hn).2
        dsimp [f]
        rw [hna]
      _ = χ a *
          ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = a),
            Complex.exp (Complex.I * (-v) * (Real.log (n : ℝ) : ℂ)) := by
        rw [← Finset.mul_sum]
      _ = χ a * residuePhaseSum N' q a (-v) (I : Set ℕ) := by
        congr 1
        simp [residuePhaseSum, S, Finset.filter_filter, Finset.mem_coe,
          and_assoc, and_left_comm, and_comm]
  have hsum :
      (∑ n ∈ S, f n) =
        ∑ a ∈ (Finset.univ : Finset (ZMod q)),
          χ a * residuePhaseSum N' q a (-v) (I : Set ℕ) := by
    calc
      _ = ∑ a : ZMod q,
          ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = a), f n := hpartition.symm
      _ = _ := Finset.sum_congr rfl (fun a _ => hinner a)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqne : (q : ℝ) ≠ 0 := hqR.ne'
  calc
    ‖∑ n ∈ (Finset.range (⌊2 * N'⌋₊ + 1)).filter
        (fun n : ℕ => N' ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N' ∧ n ∈ I), f n‖ =
      ‖∑ n ∈ S, f n‖ := by rfl
    _ = ‖∑ a ∈ (Finset.univ : Finset (ZMod q)),
          χ a * residuePhaseSum N' q a (-v) (I : Set ℕ)‖ := by rw [hsum]
    _ ≤ ∑ a ∈ (Finset.univ : Finset (ZMod q)),
          ‖χ a * residuePhaseSum N' q a (-v) (I : Set ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : ZMod q, Cφ * (N' / (q : ℝ)) *
          Real.exp (-L / Real.rpow T C₃) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      calc
        ‖χ a‖ * ‖residuePhaseSum N' q a (-v) (I : Set ℕ)‖ ≤
            1 * ‖residuePhaseSum N' q a (-v) (I : Set ℕ)‖ :=
          mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
        _ = ‖residuePhaseSum N' q a (-v) (I : Set ℕ)‖ := one_mul _
        _ ≤ Cφ * (N' / (q : ℝ)) * Real.exp (-L / Real.rpow T C₃) := hPhase a
    _ = (q : ℝ) * (Cφ * (N' / (q : ℝ)) *
          Real.exp (-L / Real.rpow T C₃)) := by simp [ZMod.card]
    _ = Cφ * N' * Real.exp (-L / Real.rpow T C₃) := by
      field_simp [hqne]

private noncomputable def contPrefixSum (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), f k

private theorem contPrefixSum_succ (f : ℕ → ℂ) (n : ℕ) :
    contPrefixSum f (n + 1) = contPrefixSum f n + f (n + 1) := by
  unfold contPrefixSum
  rw [Finset.sum_range_succ]

private theorem cont_abel_sum_range (f g : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), f k * g k) =
      contPrefixSum f n * g n +
        ∑ k ∈ Finset.range n,
          contPrefixSum f k * (g k - g (k + 1)) := by
  induction n with
  | zero => simp [contPrefixSum]
  | succ n ih =>
      calc
        _ = (∑ k ∈ Finset.range (n + 1), f k * g k) +
              f (n + 1) * g (n + 1) := by rw [Finset.sum_range_succ]
        _ = (contPrefixSum f n * g n +
              ∑ k ∈ Finset.range n,
                contPrefixSum f k * (g k - g (k + 1))) +
              f (n + 1) * g (n + 1) := by rw [ih]
        _ = contPrefixSum f (n + 1) * g (n + 1) +
              ∑ k ∈ Finset.range (n + 1),
                contPrefixSum f k * (g k - g (k + 1)) := by
          rw [Finset.sum_range_succ, contPrefixSum_succ]
          ring

private theorem cont_norm_sum_mul_le_of_prefix_bound
    {f g : ℕ → ℂ} {N : ℕ} {B : ℝ}
    (hprefix : ∀ n ≤ N, ‖contPrefixSum f n‖ ≤ B) :
    ‖∑ k ∈ Finset.range (N + 1), f k * g k‖ ≤
      B * (‖g N‖ +
        ∑ k ∈ Finset.range N, ‖g k - g (k + 1)‖) := by
  rw [cont_abel_sum_range]
  calc
    _ ≤ ‖contPrefixSum f N * g N‖ +
        ‖∑ k ∈ Finset.range N,
          contPrefixSum f k * (g k - g (k + 1))‖ := norm_add_le _ _
    _ = ‖contPrefixSum f N‖ * ‖g N‖ +
        ‖∑ k ∈ Finset.range N,
          contPrefixSum f k * (g k - g (k + 1))‖ := by rw [norm_mul]
    _ ≤ ‖contPrefixSum f N‖ * ‖g N‖ +
        ∑ k ∈ Finset.range N,
          ‖contPrefixSum f k‖ * ‖g k - g (k + 1)‖ := by
          have hsum :
              ‖∑ k ∈ Finset.range N,
                contPrefixSum f k * (g k - g (k + 1))‖ ≤
              ∑ k ∈ Finset.range N,
                ‖contPrefixSum f k‖ * ‖g k - g (k + 1)‖ := by
            calc
              _ ≤ ∑ k ∈ Finset.range N,
                  ‖contPrefixSum f k * (g k - g (k + 1))‖ := norm_sum_le _ _
              _ = _ := by simp [norm_mul]
          linarith
    _ ≤ B * ‖g N‖ +
        ∑ k ∈ Finset.range N, B * ‖g k - g (k + 1)‖ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (hprefix N le_rfl) (norm_nonneg _)
          · apply Finset.sum_le_sum
            intro k hk
            exact mul_le_mul_of_nonneg_right
              (hprefix k (Nat.le_of_lt (Finset.mem_range.mp hk)))
              (norm_nonneg _)
    _ = B * (‖g N‖ +
        ∑ k ∈ Finset.range N, ‖g k - g (k + 1)‖) := by
          rw [← Finset.mul_sum]
          ring

private theorem cont_character_dyad_prefix_bound
    {q : ℕ} [NeZero q] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    {N j : ℕ} (hN : 0 < N) (hj : j ≤ N)
    {v L T Cφ C₃ : ℝ}
    (hPhase : ∀ a : ZMod q,
      ‖residuePhaseSum (N : ℝ) q a
        (-v) (Finset.Icc N (N + j) : Set ℕ)‖ ≤
        Cφ * ((N : ℝ) / q) * Real.exp (-L / Real.rpow T C₃)) :
    ‖∑ k ∈ Finset.range (j + 1),
      χ ((N + k : ℕ) : ZMod q) *
        Complex.exp (Complex.I * (-v) * Real.log ((N + k : ℕ) : ℝ))‖ ≤
      Cφ * N * Real.exp (-L / Real.rpow T C₃) := by
  classical
  let I : Finset ℕ := Finset.Icc N (N + j)
  let S : Finset ℕ := (Finset.range (⌊2 * (N : ℝ)⌋₊ + 1)).filter
    (fun n : ℕ => (N : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (N : ℝ) ∧ n ∈ I)
  let f : ℕ → ℂ := fun k =>
    χ ((N + k : ℕ) : ZMod q) *
      Complex.exp (Complex.I * (-v) * Real.log ((N + k : ℕ) : ℝ))
  have hfloor : ⌊2 * (N : ℝ)⌋₊ = 2 * N := by
    have hcast : 2 * (N : ℝ) = ((2 * N : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, Nat.floor_natCast]
  have hS : S = Finset.Icc N (N + j) := by
    ext n
    simp only [S, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, hfloor, I]
    constructor
    · rintro ⟨hnlt, hnlo, hnhi, hnIlo, hnIhi⟩
      exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnIhi⟩
    · rintro ⟨hnlo, hnhi⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · omega
      · exact_mod_cast hnlo
      · exact_mod_cast (hnhi.trans (by omega : N + j ≤ 2 * N))
      · exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩
  have hsum :
      (∑ k ∈ Finset.range (j + 1), f k) =
        ∑ n ∈ Finset.Icc N (N + j),
          χ (n : ZMod q) *
            Complex.exp (Complex.I * (-v) * Real.log (n : ℝ)) := by
    refine Finset.sum_bij (fun k _ => N + k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc]
      constructor
      · omega
      · omega
    · intro k hk k' hk' hEq
      omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      refine ⟨n - N, ?_, Nat.add_sub_of_le hn.1⟩
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      rfl
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hB := cont_character_phase_interval_bound (q := q) (χ := χ)
    (N' := (N : ℝ)) (v := v) (L := L) (T := T) (Cφ := Cφ) (C₃ := C₃)
    (by omega : 1 ≤ q) hNpos I hPhase
  have hB' :
      ‖∑ n ∈ Finset.Icc N (N + j),
        χ (n : ZMod q) *
          Complex.exp (Complex.I * (-v) * Real.log (n : ℝ))‖ ≤
        Cφ * N * Real.exp (-L / Real.rpow T C₃) := by
    have hBS :
        ‖∑ n ∈ S,
          χ (n : ZMod q) * Complex.exp (Complex.I * (-v) * Real.log (n : ℝ))‖ ≤
          Cφ * N * Real.exp (-L / Real.rpow T C₃) := by
      simpa [S] using hB
    simpa [hS] using hBS
  calc
    _ = ‖∑ n ∈ Finset.Icc N (N + j),
          χ (n : ZMod q) * Complex.exp (Complex.I * (-v) * Real.log (n : ℝ))‖ := by
            rw [hsum]
    _ ≤ Cφ * N * Real.exp (-L / Real.rpow T C₃) := hB'

private theorem cont_character_dyad_prefixes_bound
    {q : ℕ} [NeZero q] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    {N j : ℕ} (hN : 0 < N) (hj : j ≤ N)
    {v L T Cφ C₃ : ℝ}
    (hPhase : ∀ m ≤ j, ∀ a : ZMod q,
      ‖residuePhaseSum (N : ℝ) q a (-v)
        (Finset.Icc N (N + m) : Set ℕ)‖ ≤
          Cφ * ((N : ℝ) / q) * Real.exp (-L / Real.rpow T C₃)) :
    ∀ m ≤ j,
      ‖contPrefixSum
        (fun k => χ ((N + k : ℕ) : ZMod q) *
          Complex.exp (Complex.I * (-v) *
            Real.log ((N + k : ℕ) : ℝ))) m‖ ≤
        Cφ * N * Real.exp (-L / Real.rpow T C₃) := by
  intro m hm
  have hbound := cont_character_dyad_prefix_bound
    (q := q) (χ := χ) (N := N) (j := m)
    hq hN (hm.trans hj) (hPhase m hm)
  simpa [contPrefixSum] using hbound

private theorem cont_weighted_dyad_bound
    {q : ℕ} (χ : DirichletCharacter ℂ q) {N j : ℕ} (hN : 0 < N)
    {σ v B : ℝ} (hσ : 0 ≤ σ)
    (hprefix : ∀ m ≤ j,
      ‖contPrefixSum
        (fun k => χ ((N + k : ℕ) : ZMod q) *
          Complex.exp (Complex.I * (-v) *
            Real.log ((N + k : ℕ) : ℝ))) m‖ ≤ B) :
    ‖∑ k ∈ Finset.range (j + 1),
      χ ((N + k : ℕ) : ZMod q) *
        Complex.exp (-⟨σ, v⟩ * Real.log ((N + k : ℕ) : ℝ))‖ ≤
      2 * B * Real.rpow (N : ℝ) (-σ) := by
  classical
  let f : ℕ → ℂ := fun k => χ ((N + k : ℕ) : ZMod q) *
    Complex.exp (Complex.I * (-v) * Real.log ((N + k : ℕ) : ℝ))
  let g : ℕ → ℂ := fun k => Complex.exp
    ((-σ * Real.log ((N + k : ℕ) : ℝ) : ℝ) : ℂ)
  let a : ℕ → ℝ := fun k => Real.rpow ((N + k : ℕ) : ℝ) (-σ)
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hprefix 0 (Nat.zero_le _))
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hg_eq (k : ℕ) : g k = (a k : ℂ) := by
    dsimp [g, a]
    have hn : 0 < ((N + k : ℕ) : ℝ) := by positivity
    rw [← Complex.ofReal_exp, Real.rpow_def_of_pos hn]
    congr 1
    ring
  have ha_mono (k : ℕ) : a (k + 1) ≤ a k := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity :
      0 < ((N + k : ℕ) : ℝ))
      (by exact_mod_cast (show N + k ≤ N + (k + 1) by omega))
      (neg_nonpos.mpr hσ)
  have htel (n : ℕ) :
      (∑ k ∈ Finset.range n, (a k - a (k + 1))) = a 0 - a n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hvariation :
      (∑ k ∈ Finset.range j, ‖g k - g (k + 1)‖) = a 0 - a j := by
    calc
      (∑ k ∈ Finset.range j, ‖g k - g (k + 1)‖) =
          ∑ k ∈ Finset.range j, (a k - a (k + 1)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hg_eq k, hg_eq (k + 1), ← Complex.ofReal_sub,
              Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr (ha_mono k))]
      _ = a 0 - a j := htel j
  have hnormG : ‖g j‖ = a j := by
    have haj : 0 ≤ a j := by
      simpa [a] using Real.rpow_nonneg (show 0 ≤ ((N + j : ℕ) : ℝ) by positivity) (-σ)
    rw [hg_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg haj]
  have hprefix' : ∀ n ≤ j, ‖contPrefixSum f n‖ ≤ B := by
    intro n hn
    simpa [f] using hprefix n hn
  have habel := cont_norm_sum_mul_le_of_prefix_bound (f := f) (g := g)
    (N := j) (B := B) hprefix'
  have hsumEq :
      (∑ k ∈ Finset.range (j + 1),
        χ ((N + k : ℕ) : ZMod q) *
          Complex.exp (-⟨σ, v⟩ * Real.log ((N + k : ℕ) : ℝ))) =
        ∑ k ∈ Finset.range (j + 1), f k * g k := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f, g]
    have hsplit :
        -⟨σ, v⟩ * (Real.log ((N + k : ℕ) : ℝ) : ℂ) =
          Complex.I * (-v) * (Real.log ((N + k : ℕ) : ℝ) : ℂ) +
            ((-σ * Real.log ((N + k : ℕ) : ℝ)) : ℂ) := by
      apply Complex.ext
      · simp [Complex.mul_re] <;> ring
      · simp [Complex.mul_im] <;> ring
    rw [hsplit, Complex.exp_add]
    have hweight : Complex.exp
        ((-σ * Real.log ((N + k : ℕ) : ℝ) : ℝ) : ℂ) =
          Complex.exp ((-σ : ℂ) * (Real.log ((N + k : ℕ) : ℝ) : ℂ) : ℂ) := by
      congr 1
      push_cast
      ring
    rw [hweight]
    simp only [mul_assoc]
  rw [hsumEq]
  calc
    ‖∑ k ∈ Finset.range (j + 1), f k * g k‖ ≤
        B * (‖g j‖ +
          ∑ k ∈ Finset.range j, ‖g k - g (k + 1)‖) := habel
    _ = B * (a j + (a 0 - a j)) := by rw [hnormG, hvariation]
    _ = B * a 0 := by congr 1; ring
    _ ≤ 2 * B * a 0 := by
      have ha0 : 0 ≤ a 0 := Real.rpow_nonneg hNpos.le _
      nlinarith [mul_nonneg hB ha0]
    _ = 2 * B * Real.rpow (N : ℝ) (-σ) := by simp [a]

private theorem cont_weighted_dyad_phase_bound
    {q : ℕ} [NeZero q] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    {N j : ℕ} (hN : 0 < N) (hj : j ≤ N)
    {σ v L T Cφ C₃ : ℝ} (hσ : 0 ≤ σ)
    (hPhase : ∀ m ≤ j, ∀ a : ZMod q,
      ‖residuePhaseSum (N : ℝ) q a (-v)
        (Finset.Icc N (N + m) : Set ℕ)‖ ≤
          Cφ * ((N : ℝ) / q) * Real.exp (-L / Real.rpow T C₃)) :
    ‖∑ k ∈ Finset.range (j + 1),
      χ ((N + k : ℕ) : ZMod q) *
        Complex.exp (-⟨σ, v⟩ * Real.log ((N + k : ℕ) : ℝ))‖ ≤
      2 * Cφ * N * Real.exp (-L / Real.rpow T C₃) *
        Real.rpow (N : ℝ) (-σ) := by
  have hprefix := cont_character_dyad_prefixes_bound hq χ hN hj hPhase
  have hweighted := cont_weighted_dyad_bound χ hN hσ hprefix
  simpa [mul_assoc, mul_left_comm, mul_comm] using hweighted

private theorem cont_sum_Icc_dyadic_prefix {α : Type*}
    [AddCommMonoid α] (f : ℕ → α) (N X m : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.Icc N (min (N * 2 ^ m - 1) X), f n) =
      ∑ k ∈ Finset.range m,
        ∑ n ∈ Finset.Icc (N * 2 ^ k)
          (min (N * 2 ^ (k + 1) - 1) X), f n := by
  classical
  induction m with
  | zero =>
      have hempty : Finset.Icc N (min (N * 2 ^ 0 - 1) X) = ∅ := by
        have hlt : N * 2 ^ 0 - 1 < N := by simp; omega
        ext n
        simp only [Finset.mem_Icc, Finset.notMem_empty]
        constructor
        · rintro ⟨hnN, hnEnd⟩
          have hnC : n ≤ N * 2 ^ 0 - 1 := hnEnd.trans (Nat.min_le_left _ _)
          exact (not_le_of_gt hlt) (hnN.trans hnC)
        · intro hfalse
          cases hfalse
      rw [hempty]
      simp
  | succ m ih =>
      let S : ℕ := N * 2 ^ m
      have hSpos : 0 < S := by dsimp [S]; positivity
      have hpow : N * 2 ^ (m + 1) = 2 * S := by
        dsimp [S]
        rw [pow_succ]
        ring
      by_cases hSX : S ≤ X
      · have hprev : min (S - 1) X = S - 1 := by omega
        have hSupper : S ≤ N * 2 ^ (m + 1) - 1 := by rw [hpow]; omega
        have hR : S ≤ min (N * 2 ^ (m + 1) - 1) X := le_min hSupper hSX
        have hNS : N ≤ S := by
          dsimp [S]
          calc
            N = N * 1 := by simp
            _ ≤ N * 2 ^ m := Nat.mul_le_mul_left N (Nat.one_le_pow _ _ (by decide))
        have hsplit : Finset.Icc N (min (N * 2 ^ (m + 1) - 1) X) =
            Finset.Icc N (S - 1) ∪
              Finset.Icc S (min (N * 2 ^ (m + 1) - 1) X) := by
          ext n
          simp only [Finset.mem_union, Finset.mem_Icc]
          constructor
          · rintro ⟨hnN, hnR⟩
            by_cases hnS : n < S
            · exact Or.inl ⟨hnN, by omega⟩
            · exact Or.inr ⟨le_of_not_gt hnS, hnR⟩
          · rintro (⟨hnN, hnEnd⟩ | ⟨hnS, hnEnd⟩)
            · exact ⟨hnN, hnEnd.trans ((Nat.sub_le S 1).trans hR)⟩
            · exact ⟨hNS.trans hnS, hnEnd⟩
        have hdisj : Disjoint (Finset.Icc N (S - 1))
            (Finset.Icc S (min (N * 2 ^ (m + 1) - 1) X)) := by
          apply Finset.disjoint_left.mpr
          intro n hn₁ hn₂
          simp only [Finset.mem_Icc] at hn₁ hn₂
          omega
        have ih' : (∑ n ∈ Finset.Icc N (S - 1), f n) =
            ∑ k ∈ Finset.range m,
              ∑ n ∈ Finset.Icc (N * 2 ^ k)
                (min (N * 2 ^ (k + 1) - 1) X), f n := by
          simpa [S, hprev] using ih
        calc
          _ = ∑ n ∈ Finset.Icc N (S - 1) ∪
                Finset.Icc S (min (N * 2 ^ (m + 1) - 1) X), f n := by rw [hsplit]
          _ = (∑ n ∈ Finset.Icc N (S - 1), f n) +
                ∑ n ∈ Finset.Icc S (min (N * 2 ^ (m + 1) - 1) X), f n :=
              Finset.sum_union hdisj
          _ = (∑ k ∈ Finset.range m,
                ∑ n ∈ Finset.Icc (N * 2 ^ k)
                  (min (N * 2 ^ (k + 1) - 1) X), f n) +
                ∑ n ∈ Finset.Icc S (min (N * 2 ^ (m + 1) - 1) X), f n := by rw [ih']
          _ = ∑ k ∈ Finset.range (m + 1),
                ∑ n ∈ Finset.Icc (N * 2 ^ k)
                  (min (N * 2 ^ (k + 1) - 1) X), f n := by
              rw [Finset.sum_range_succ]
      · have hXprev : X ≤ S - 1 := by omega
        have hprev : min (S - 1) X = X := min_eq_right hXprev
        have hSnext : S ≤ N * 2 ^ (m + 1) - 1 := by rw [hpow]; omega
        have hnext : min (N * 2 ^ (m + 1) - 1) X = X :=
          min_eq_right (hXprev.trans ((Nat.sub_le S 1).trans hSnext))
        have hblock : Finset.Icc (N * 2 ^ m) X = ∅ := by
          have hlt : X < N * 2 ^ m := lt_of_not_ge (by simpa [S] using hSX)
          ext n
          have hnocontra : ¬ (N * 2 ^ m ≤ n ∧ n ≤ X) := by
            intro h
            exact (not_le_of_gt hlt) (h.1.trans h.2)
          simp only [Finset.mem_Icc, Finset.notMem_empty]
          constructor
          · exact hnocontra
          · intro hfalse
            cases hfalse
        rw [Finset.sum_range_succ, hnext]
        rw [hblock, Finset.sum_empty, add_zero]
        have hprev' : min (N * 2 ^ m - 1) X = X := by simpa [S] using hprev
        simpa [hprev'] using ih

private theorem cont_growth_low_height_bound
    (hLog : ArtinPrimitiveRoots.Proofs.pp_phase_p.phaseLogPhaseStatement) :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          let rstar := T ^ 4 / L
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ hq : 0 < q, ∀ χ : DirichletCharacter ℂ q,
              ∀ σ v : ℝ, |σ - 1| ≤ 10 * rstar →
                1 / 2 ≤ |v| → |v| ≤ 3 * Real.rpow x 3 →
                |v| ≤ Real.exp (L / (2 * T ^ 2)) →
                  ‖dirichletLValue q hq χ (⟨σ, v⟩ : ℂ)‖ ≤
                    Real.exp (C₀ * T ^ 2) := by
  sorry

private theorem cont_weighted_dyad_Icc_bound
    {q : ℕ} [NeZero q] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    {N X : ℕ} {σ v L T Cφ C₃ : ℝ}
    (hN : 0 < N) (hNX : N ≤ X) (hσ : 0 ≤ σ)
    (hPhase : ∀ m ≤ min (N - 1) (X - N), ∀ a : ZMod q,
      ‖residuePhaseSum (N : ℝ) q a (-v)
        (Finset.Icc N (N + m) : Set ℕ)‖ ≤
          Cφ * ((N : ℝ) / q) * Real.exp (-L / Real.rpow T C₃)) :
    ‖∑ n ∈ Finset.Icc N (min (2 * N - 1) X),
      χ (n : ZMod q) *
        Complex.exp (-⟨σ, v⟩ * Real.log (n : ℝ))‖ ≤
      2 * Cφ * N * Real.exp (-L / Real.rpow T C₃) *
        Real.rpow (N : ℝ) (-σ) := by
  classical
  let j := min (N - 1) (X - N)
  have hj : j ≤ N := by dsimp [j]; omega
  have hend : N + j = min (2 * N - 1) X := by
    dsimp [j]
    simp only [Nat.min_def]
    split_ifs <;> omega
  have hPhase' : ∀ m ≤ j, ∀ a : ZMod q,
      ‖residuePhaseSum (N : ℝ) q a (-v)
        (Finset.Icc N (N + m) : Set ℕ)‖ ≤
          Cφ * ((N : ℝ) / q) * Real.exp (-L / Real.rpow T C₃) := by
    intro m hm a
    exact hPhase m (by simpa [j] using hm) a
  have hweighted := cont_weighted_dyad_phase_bound hq χ hN hj hσ hPhase'
  have hsum :
      (∑ k ∈ Finset.range (j + 1),
        χ ((N + k : ℕ) : ZMod q) *
          Complex.exp (-⟨σ, v⟩ * Real.log ((N + k : ℕ) : ℝ))) =
        ∑ n ∈ Finset.Icc N (N + j),
          χ (n : ZMod q) * Complex.exp (-⟨σ, v⟩ * Real.log (n : ℝ)) := by
    refine Finset.sum_bij (fun k _ => N + k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc]
      omega
    · intro k hk k' hk' heq
      omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      refine ⟨n - N, ?_, Nat.add_sub_of_le hn.1⟩
      simp only [Finset.mem_range]
      omega
    · intro k hk
      rfl
  have hinterval : Finset.Icc N (N + j) = Finset.Icc N (min (2 * N - 1) X) := by
    rw [hend]
  calc
    _ = ‖∑ k ∈ Finset.range (j + 1),
          χ ((N + k : ℕ) : ZMod q) *
            Complex.exp (-⟨σ, v⟩ * Real.log ((N + k : ℕ) : ℝ))‖ := by
            rw [← hinterval, ← hsum]
    _ ≤ 2 * Cφ * N * Real.exp (-L / Real.rpow T C₃) *
          Real.rpow (N : ℝ) (-σ) := hweighted

private theorem cont_high_dyadic_tail_bound
    {q : ℕ} [NeZero q] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    {x L T Cφ C₃ σ v : ℝ} {N X : ℕ}
    (hCφ : 0 < Cφ) (hN : 0 < N) (hNX : N ≤ X)
    (hY0 : Real.exp (L / T ^ 2) ≤ (N : ℝ))
    (hX : (X : ℝ) ≤ Real.rpow x 5) (hσ : 0 ≤ σ)
    (hPhaseAtX : ∀ N' : ℝ, Real.exp (L / T ^ 2) ≤ N' →
      N' ≤ 2 * Real.rpow x 5 → ∀ a : ZMod q, ∀ N₁ N₂ : ℝ,
        N' ≤ N₁ → N₂ ≤ 2 * N' →
          ‖residuePhaseSum N' q a (-v)
            {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂}‖ ≤
            Cφ * (N' / q) * Real.exp (-L / Real.rpow T C₃))
    (hweight : ∀ n : ℕ, N ≤ n → n ≤ X →
      (n : ℝ) * Real.rpow (n : ℝ) (-σ) ≤ Real.exp (50 * T ^ 4)) :
    ‖∑ n ∈ Finset.Icc N X,
      χ (n : ZMod q) *
        Complex.exp (-⟨σ, v⟩ * Real.log (n : ℝ))‖ ≤
      2 * Cφ * ((Nat.log 2 X + 1 : ℕ) : ℝ) *
        Real.exp (-L / Real.rpow T C₃ + 50 * T ^ 4) := by
  classical
  let m : ℕ := Nat.log 2 X + 1
  let f : ℕ → ℂ := fun n => χ (n : ZMod q) *
    Complex.exp (-⟨σ, v⟩ * Real.log (n : ℝ))
  have hXne : X ≠ 0 := by omega
  have hmX : Nat.log 2 X < m := by dsimp [m]; omega
  have hpow : X < 2 ^ m :=
    (Nat.log_lt_iff_lt_pow (by decide) hXne).mp hmX
  have hNle : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN)
  have hNpow : 2 ^ m ≤ N * 2 ^ m := by
    calc
      2 ^ m = 1 * 2 ^ m := by simp
      _ ≤ N * 2 ^ m := Nat.mul_le_mul_right _ hNle
  have hlarge : X < N * 2 ^ m := lt_of_lt_of_le hpow hNpow
  have htop : min (N * 2 ^ m - 1) X = X :=
    min_eq_right (by omega)
  have hdecomp :
      (∑ n ∈ Finset.Icc N X, f n) =
        ∑ k ∈ Finset.range m,
          ∑ n ∈ Finset.Icc (N * 2 ^ k)
            (min (N * 2 ^ (k + 1) - 1) X), f n := by
    simpa [htop] using cont_sum_Icc_dyadic_prefix f N X m hN
  let B : ℝ := 2 * Cφ * Real.exp (-L / Real.rpow T C₃) *
    Real.exp (50 * T ^ 4)
  have hblock (k : ℕ) (hk : k ∈ Finset.range m) :
      ‖∑ n ∈ Finset.Icc (N * 2 ^ k)
          (min (N * 2 ^ (k + 1) - 1) X), f n‖ ≤ B := by
    let Nk := N * 2 ^ k
    by_cases hNkX : Nk ≤ X
    · have hNkpos : 0 < Nk := by dsimp [Nk]; positivity
      have hNleNk : N ≤ Nk := by
        dsimp [Nk]
        calc
          N = N * 1 := by simp
          _ ≤ N * 2 ^ k := Nat.mul_le_mul_left N (Nat.one_le_pow k 2 (by decide))
      have hNkY0 : Real.exp (L / T ^ 2) ≤ (Nk : ℝ) := by
        exact le_trans hY0 (by exact_mod_cast hNleNk)
      have hNkUpper : (Nk : ℝ) ≤ 2 * Real.rpow x 5 := by
        have hNkX' : (Nk : ℝ) ≤ (X : ℝ) := by exact_mod_cast hNkX
        have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
        have hXlower : (N : ℝ) ≤ (X : ℝ) := by exact_mod_cast hNX
        have hxpos : 0 < Real.rpow x 5 := lt_of_lt_of_le hNreal (le_trans hXlower hX)
        linarith
      let j := min (Nk - 1) (X - Nk)
      have hphase : ∀ t ≤ j, ∀ a : ZMod q,
          ‖residuePhaseSum (Nk : ℝ) q a (-v)
            (Finset.Icc Nk (Nk + t) : Set ℕ)‖ ≤
              Cφ * ((Nk : ℝ) / q) * Real.exp (-L / Real.rpow T C₃) := by
        intro t ht a
        have htNk : t ≤ Nk := by
          have hj' : j ≤ Nk - 1 := by dsimp [j]; exact Nat.min_le_left _ _
          omega
        have hN₂nat : Nk + t ≤ 2 * Nk := by omega
        have hN₂ : ((Nk + t : ℕ) : ℝ) ≤ 2 * (Nk : ℝ) := by exact_mod_cast hN₂nat
        have hraw := hPhaseAtX (Nk : ℝ) hNkY0 hNkUpper a
          (Nk : ℝ) ((Nk + t : ℕ) : ℝ) le_rfl hN₂
        have hset : (Finset.Icc Nk (Nk + t) : Set ℕ) =
            {n : ℕ | (Nk : ℝ) ≤ (n : ℝ) ∧
              (n : ℝ) ≤ ((Nk + t : ℕ) : ℝ)} := by
          ext n
          simp only [Finset.mem_coe, Finset.mem_Icc, Set.mem_setOf_eq]
          constructor <;> intro hn
          · exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
          · exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
        simpa only [hset] using hraw
      have hinterval := cont_weighted_dyad_Icc_bound hq χ hNkpos hNkX hσ hphase
      have hend : N * 2 ^ (k + 1) = 2 * Nk := by
        dsimp [Nk]
        rw [pow_succ]
        ring
      have hblock' :
          ‖∑ n ∈ Finset.Icc (N * 2 ^ k)
              (min (N * 2 ^ (k + 1) - 1) X), f n‖ ≤
            2 * Cφ * (Nk : ℝ) * Real.exp (-L / Real.rpow T C₃) *
              Real.rpow (Nk : ℝ) (-σ) := by
        rw [hend]
        simpa [f] using hinterval
      have hweight' := hweight Nk hNleNk hNkX
      have hweightB :
          2 * Cφ * (Nk : ℝ) * Real.exp (-L / Real.rpow T C₃) *
              Real.rpow (Nk : ℝ) (-σ) ≤
            2 * Cφ * Real.exp (-L / Real.rpow T C₃) *
              Real.exp (50 * T ^ 4) := by
        calc
          _ = (2 * Cφ * Real.exp (-L / Real.rpow T C₃)) *
                ((Nk : ℝ) * Real.rpow (Nk : ℝ) (-σ)) := by ac_rfl
          _ ≤ _ := mul_le_mul_of_nonneg_left hweight' (by positivity)
      calc
        _ ≤ 2 * Cφ * (Nk : ℝ) * Real.exp (-L / Real.rpow T C₃) *
              Real.rpow (Nk : ℝ) (-σ) := hblock'
        _ ≤ B := by simpa only [B] using hweightB
    · have hupper : min (N * 2 ^ (k + 1) - 1) X < Nk :=
        (Nat.min_le_right _ _).trans_lt (lt_of_not_ge hNkX)
      have hempty : Finset.Icc (N * 2 ^ k)
          (min (N * 2 ^ (k + 1) - 1) X) = ∅ := by
        ext n
        simp only [Finset.mem_Icc, Finset.notMem_empty]
        constructor
        · rintro ⟨hnlo, hnhi⟩
          exact (not_le_of_gt hupper) (hnlo.trans hnhi)
        · intro hn
          cases hn
      rw [hempty]
      simp only [Finset.sum_empty, norm_zero]
      positivity
  rw [hdecomp]
  calc
    _ ≤ ∑ k ∈ Finset.range m,
          ‖∑ n ∈ Finset.Icc (N * 2 ^ k)
              (min (N * 2 ^ (k + 1) - 1) X), f n‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range m, B := by
      apply Finset.sum_le_sum
      intro k hk
      exact hblock k hk
    _ = (m : ℝ) * B := by simp
    _ = 2 * Cφ * ((Nat.log 2 X + 1 : ℕ) : ℝ) *
          Real.exp (-L / Real.rpow T C₃) * Real.exp (50 * T ^ 4) := by
      dsimp [B, m]
      ring
    _ = 2 * Cφ * ((Nat.log 2 X + 1 : ℕ) : ℝ) *
          Real.exp (-L / Real.rpow T C₃ + 50 * T ^ 4) := by
      rw [Real.exp_add]
      simp [B, m, mul_assoc, mul_left_comm, mul_comm]

private theorem cont_partial_sum_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    {Y₀ Y σ v : ℝ} (hfloor : ⌊Y₀⌋₊ ≤ ⌊Y⌋₊) :
    dirichletPartialSum q χ Y (⟨σ, v⟩ : ℂ) =
      dirichletPartialSum q χ Y₀ (⟨σ, v⟩ : ℂ) +
        ∑ n ∈ Finset.Icc (⌊Y₀⌋₊ + 1) ⌊Y⌋₊,
          χ (n : ZMod q) *
            Complex.exp (-⟨σ, v⟩ * Real.log (n : ℝ)) := by
  classical
  let F₀ := ⌊Y₀⌋₊
  let F := ⌊Y⌋₊
  have hfilter₀ :
      (Finset.range (⌊Y₀⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n) =
        Finset.Icc 1 ⌊Y₀⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hfilter :
      (Finset.range (⌊Y⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n) =
        Finset.Icc 1 ⌊Y⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hsplit : Finset.Icc 1 F =
      Finset.Icc 1 F₀ ∪ Finset.Icc (F₀ + 1) F := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc]
    constructor
    · rintro ⟨hn₁, hnF⟩
      by_cases hnF₀ : n ≤ F₀
      · exact Or.inl ⟨hn₁, hnF₀⟩
      · exact Or.inr ⟨by omega, hnF⟩
    · rintro (⟨hn₁, hnF₀⟩ | ⟨hnF₀, hnF⟩)
      · exact ⟨hn₁, hnF₀.trans hfloor⟩
      · exact ⟨by omega, hnF⟩
  have hdisj : Disjoint (Finset.Icc 1 F₀) (Finset.Icc (F₀ + 1) F) := by
    apply Finset.disjoint_left.mpr
    intro n hn₀ hn
    simp only [Finset.mem_Icc] at hn₀ hn
    omega
  have hY0_filter : (Finset.range (F₀ + 1)).filter (fun n : ℕ => 1 ≤ n) =
      Finset.Icc 1 F₀ := by simpa [F₀] using hfilter₀
  have hY_filter : (Finset.range (F + 1)).filter (fun n : ℕ => 1 ≤ n) =
      Finset.Icc 1 F := by simpa [F] using hfilter
  unfold dirichletPartialSum
  rw [show ⌊Y₀⌋₊ = F₀ by rfl, show ⌊Y⌋₊ = F by rfl,
    hY0_filter, hY_filter]
  rw [hsplit, Finset.sum_union hdisj]

private theorem cont_high_growth_threshold (C Cφ C₃ : ℝ)
    (hC : 0 < C) (hCφ : 0 < Cφ) :
    ∃ x₀ : ℝ, 2 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      let L := Real.log x
      let T := Real.log L
      1 ≤ T ∧
      (150 + C) * T ^ 4 ≤ L ∧
      100 * T ^ 6 ≤ L ∧
      (63 + 2 * Cφ) * T ^ (⌈C₃⌉₊ + 15) ≤ L := by
  let A₄ : ℝ := 150 + C
  let A₁₅ : ℝ := 63 + 2 * Cφ
  let d : ℕ := ⌈C₃⌉₊
  let m : ℕ := d + 15
  have hA₄ : 0 < A₄ := by dsimp [A₄]; linarith
  have hA₁₅ : 0 < A₁₅ := by dsimp [A₁₅]; positivity
  have hTlim : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlogpow (m : ℕ) :
      Tendsto (fun x : ℝ => Real.log (Real.log x) ^ m / Real.log x)
        atTop (𝓝 0) := by
    change Tendsto ((fun z : ℝ => Real.log z ^ m / z) ∘ Real.log)
      atTop (𝓝 0)
    simpa [one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 m one_ne_zero).comp
        Real.tendsto_log_atTop
  have hsmall₄ : ∀ᶠ x : ℝ in atTop,
      Real.log (Real.log x) ^ 4 / Real.log x < 1 / A₄ :=
    (hlogpow 4).eventually (gt_mem_nhds (by positivity))
  have hsmall₆ : ∀ᶠ x : ℝ in atTop,
      Real.log (Real.log x) ^ 6 / Real.log x < 1 / 100 :=
    (hlogpow 6).eventually (gt_mem_nhds (by norm_num))
  have hsmallm : ∀ᶠ x : ℝ in atTop,
      Real.log (Real.log x) ^ m / Real.log x < 1 / A₁₅ :=
    (hlogpow m).eventually (gt_mem_nhds (by positivity))
  have hEventually : ∀ᶠ x : ℝ in atTop,
      1 ≤ Real.log x ∧ 1 ≤ Real.log (Real.log x) ∧
        Real.log (Real.log x) ^ 4 / Real.log x < 1 / A₄ ∧
        Real.log (Real.log x) ^ 6 / Real.log x < 1 / 100 ∧
        Real.log (Real.log x) ^ m / Real.log x < 1 / A₁₅ := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
      hTlim.eventually_ge_atTop 1, hsmall₄, hsmall₆, hsmallm]
      with x hL hT h₄ h₆ hm
    exact ⟨hL, hT, h₄, h₆, hm⟩
  obtain ⟨X, hX⟩ := eventually_atTop.1 hEventually
  refine ⟨max 3 X, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x hx
  have hxX : X ≤ x := (le_max_right _ _).trans hx
  rcases hX x hxX with ⟨hLone, hTone, h₄, h₆, hm⟩
  let L : ℝ := Real.log x
  let T : ℝ := Real.log L
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hTpos : 0 < T := by dsimp [T]; linarith
  have h₄' : T ^ 4 / L < 1 / A₄ := by simpa [L, T] using h₄
  have h₆' : T ^ 6 / L < 1 / 100 := by simpa [L, T] using h₆
  have hm' : T ^ m / L < 1 / A₁₅ := by simpa [L, T] using hm
  have hbound₄lt : A₄ * T ^ 4 < L := by
    calc
      A₄ * T ^ 4 = (T ^ 4 / L) * (L * A₄) := by
        field_simp [ne_of_gt hLpos]
      _ < (1 / A₄) * (L * A₄) :=
        mul_lt_mul_of_pos_right h₄' (mul_pos hLpos hA₄)
      _ = L := by field_simp [ne_of_gt hA₄]
  have hbound₄ : A₄ * T ^ 4 ≤ L := hbound₄lt.le
  have hbound₆lt : 100 * T ^ 6 < L := by
    calc
      100 * T ^ 6 = (T ^ 6 / L) * (L * 100) := by
        field_simp [ne_of_gt hLpos]
      _ < (1 / 100) * (L * 100) :=
        mul_lt_mul_of_pos_right h₆' (mul_pos hLpos (by norm_num))
      _ = L := by ring
  have hbound₆ : 100 * T ^ 6 ≤ L := hbound₆lt.le
  have hbound₁₅lt : A₁₅ * T ^ m < L := by
    calc
      A₁₅ * T ^ m = (T ^ m / L) * (L * A₁₅) := by
        field_simp [ne_of_gt hLpos]
      _ < (1 / A₁₅) * (L * A₁₅) :=
        mul_lt_mul_of_pos_right hm' (mul_pos hLpos hA₁₅)
      _ = L := by field_simp [ne_of_gt hA₁₅]
  have hbound₁₅ : A₁₅ * T ^ m ≤ L := hbound₁₅lt.le
  dsimp only
  exact ⟨hTone, by simpa [A₄] using hbound₄, hbound₆,
    by simpa [A₁₅, m, d] using hbound₁₅⟩

set_option maxHeartbeats 1000000 in
private theorem cont_growth_high_height_bound
    (hLog : ArtinPrimitiveRoots.Proofs.pp_phase_p.phaseLogPhaseStatement) :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          let rstar := T ^ 4 / L
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ hq : 0 < q, ∀ χ : DirichletCharacter ℂ q,
              ∀ σ v : ℝ, |σ - 1| ≤ 10 * rstar →
                1 / 2 ≤ |v| → |v| ≤ 3 * Real.rpow x 3 →
                  Real.exp (L / (2 * T ^ 2)) ≤ |v| →
                    ‖dirichletLValue q hq χ (⟨σ, v⟩ : ℂ)‖ ≤
                      Real.exp (C₀ * T ^ 2) := by
  classical
  rcases hLog with ⟨C₃, hC₃, hLogC⟩
  intro C hC
  obtain ⟨Cφ, xφ, hCφ, hxφ, hLogX⟩ := hLogC C hC
  obtain ⟨xGrowth, hxGrowth, hGrowth⟩ :=
    cont_high_growth_threshold C Cφ C₃ hC hCφ
  refine ⟨20, max xφ xGrowth, by norm_num, ?_, ?_⟩
  · exact lt_of_lt_of_le hxφ (le_max_left _ _)
  · intro x hx
    dsimp only
    intro q hq hqC hqpos χ σ v hσ hvlo hvhi hvhigh
    let L : ℝ := Real.log x
    let T : ℝ := Real.log L
    let Y₀ : ℝ := Real.exp (L / T ^ 2)
    let Y : ℝ := Real.rpow x 5
    let X : ℕ := ⌊Y⌋₊
    let N : ℕ := ⌊Y₀⌋₊ + 1
    let s : ℂ := ⟨σ, v⟩
    have hxφ' : xφ ≤ x := (le_max_left _ _).trans hx
    have hxGrowth' : xGrowth ≤ x := (le_max_right _ _).trans hx
    have hxgt2 : 2 < x := lt_of_lt_of_le hxφ hxφ'
    have hxpos : 0 < x := by linarith
    have hLpos : 0 < L := by dsimp [L]; exact Real.log_pos (by linarith)
    have hGrowthAtX := hGrowth x hxGrowth'
    dsimp only at hGrowthAtX
    rcases hGrowthAtX with ⟨hTone, hL4, hL6, hLdyn⟩
    have hToneT : 1 ≤ T := by simpa [L, T] using hTone
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hToneT
    have hT2 : 1 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
    have hLone : 1 ≤ L := by
      calc
        1 ≤ Real.exp T := Real.one_le_exp (by linarith [hToneT])
        _ = L := by dsimp [T]; exact Real.exp_log hLpos
    have hLexp : Real.exp T = L := by
      dsimp [T]
      exact Real.exp_log hLpos
    have hσR : |σ - 1| ≤ 10 * (T ^ 4 / L) := by simpa [L, T] using hσ
    have hσratio : T ^ 4 / L ≤ 1 / 150 := by
      have h150 : (150 : ℝ) * T ^ 4 ≤ L := by
        have hT4nonneg : 0 ≤ T ^ 4 := by positivity
        nlinarith [hL4, hT4nonneg, hC]
      exact (div_le_iff₀ hLpos).2 (by nlinarith)
    have hσsmall : 10 * (T ^ 4 / L) ≤ 1 / 15 := by
      calc
        10 * (T ^ 4 / L) ≤ 10 * (1 / 150) :=
          mul_le_mul_of_nonneg_left hσratio (by norm_num)
        _ = 1 / 15 := by norm_num
    have hσlo : (1 / 2 : ℝ) ≤ σ := by
      have hs := abs_le.mp (hσR.trans hσsmall)
      linarith
    have hσhi : σ ≤ 2 := by
      have hs := abs_le.mp (hσR.trans hσsmall)
      linarith
    have hσnonneg : 0 ≤ σ := by linarith
    have hYpos : 0 < Y := Real.rpow_pos_of_pos hxpos _
    have hYlog : Real.log Y = 5 * L := by
      dsimp [Y, L]
      rw [Real.rpow_def_of_pos hxpos, Real.log_exp]
      ring
    have hYpow : Y = x ^ 5 := by
      dsimp [Y]
      exact Real.rpow_natCast x 5
    have hY0pos : 0 < Y₀ := Real.exp_pos _
    have hY0one : 1 ≤ Y₀ := by
      exact Real.one_le_exp (by positivity)
    have hY0leX : Y₀ ≤ x := by
      have hdiv : L / T ^ 2 ≤ L := by
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [hLpos, hT2]
      calc
        Y₀ = Real.exp (L / T ^ 2) := rfl
        _ ≤ Real.exp L := Real.exp_le_exp.mpr hdiv
        _ = x := by dsimp [L]; exact Real.exp_log hxpos
    have hxpow4 : (2 : ℝ) ^ 4 ≤ x ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hxgt2.le 4
    have hx4 : 2 ≤ x ^ 4 := by nlinarith [hxpow4]
    have hxplus : x + 1 ≤ x ^ 5 := by
      calc
        x + 1 ≤ 2 * x := by linarith
        _ ≤ x * x ^ 4 := by
          nlinarith [mul_nonneg (le_of_lt hxpos) (sub_nonneg.mpr hx4)]
        _ = x ^ 5 := by ring
    have hY0leY : Y₀ ≤ Y := by
      rw [hYpow]
      exact hY0leX.trans (by linarith [hxplus])
    have hNleY : (N : ℝ) ≤ Y := by
      have hfloorY₀ : (⌊Y₀⌋₊ : ℝ) ≤ Y₀ := Nat.floor_le hY0pos.le
      have hY₀plus : Y₀ + 1 ≤ Y := by
        calc
          Y₀ + 1 ≤ x + 1 := by nlinarith [hY0leX]
          _ ≤ Y := by rw [hYpow]; exact hxplus
      dsimp [N]
      push_cast
      linarith [hfloorY₀, hY₀plus]
    have hfloor : ⌊Y₀⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono hY0leY
    have hNX : N ≤ X := by
      dsimp [N, X]
      exact Nat.le_floor hNleY
    have hNpos : 0 < N := by dsimp [N]; omega
    have hXne : X ≠ 0 := by omega
    have hXpos : 0 < (X : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hXne)
    have hXleY : (X : ℝ) ≤ Y := by
      dsimp [X]
      exact Nat.floor_le hYpos.le
    have hY₀N : Y₀ ≤ (N : ℝ) := by
      dsimp [N]
      push_cast
      exact le_of_lt (Nat.lt_floor_add_one Y₀)
    letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
    have hLogAtX := hLogX x hxφ'
    have hvlarge' : Real.exp (L / (2 * T ^ 2)) ≤ |-v| := by simpa using hvhigh
    have hvupper' : |-v| ≤ 4 * Real.rpow x 3 := by
      rw [abs_neg]
      have hrpow : 0 ≤ Real.rpow x 3 := Real.rpow_nonneg hxpos.le _
      calc
        |v| ≤ 3 * Real.rpow x 3 := hvhi
        _ ≤ 4 * Real.rpow x 3 :=
          mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 4) hrpow
    have hPhaseAtX : ∀ N' : ℝ, Real.exp (L / T ^ 2) ≤ N' →
        N' ≤ 2 * Real.rpow x 5 → ∀ a : ZMod q, ∀ N₁ N₂ : ℝ,
          N' ≤ N₁ → N₂ ≤ 2 * N' →
            ‖residuePhaseSum N' q a (-v)
              {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂}‖ ≤
              Cφ * (N' / q) * Real.exp (-L / Real.rpow T C₃) := by
      intro N' hN'lo hN'hi a N₁ N₂ hN₁ hN₂
      exact hLogAtX N' hN'lo hN'hi q hq hqC a (-v)
        hvlarge' hvupper' N₁ N₂ hN₁ hN₂
    have hweight : ∀ n : ℕ, N ≤ n → n ≤ X →
        (n : ℝ) * Real.rpow (n : ℝ) (-σ) ≤ Real.exp (50 * T ^ 4) := by
      intro n hnN hnX
      have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le hNpos hnN)
      have hnRone : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.lt_of_lt_of_le hNpos hnN)))
      have hnleY : (n : ℝ) ≤ Y := by
        exact (show (n : ℝ) ≤ (X : ℝ) by exact_mod_cast hnX).trans hXleY
      have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnRone
      have hlognY : Real.log (n : ℝ) ≤ Real.log Y :=
        Real.log_le_log hnR hnleY
      have hdelta : |1 - σ| ≤ 10 * (T ^ 4 / L) := by
        simpa [abs_sub_comm] using hσR
      have hphase : (1 - σ) * Real.log (n : ℝ) ≤ 50 * T ^ 4 := by
        calc
          (1 - σ) * Real.log (n : ℝ) ≤
              |1 - σ| * Real.log (n : ℝ) := by
                exact mul_le_mul_of_nonneg_right (le_abs_self _) hlogn
          _ ≤ (10 * (T ^ 4 / L)) * Real.log Y :=
                mul_le_mul hdelta hlognY (by positivity) (by positivity)
          _ = 50 * T ^ 4 := by rw [hYlog]; field_simp [ne_of_gt hLpos]; ring
      have hpowIdent : (n : ℝ) * Real.rpow (n : ℝ) (-σ) =
          Real.rpow (n : ℝ) (1 - σ) := by
        have hadd : Real.rpow (n : ℝ) (1 + (-σ)) =
            Real.rpow (n : ℝ) 1 * Real.rpow (n : ℝ) (-σ) := by
          simpa only [Real.rpow_eq_pow] using (Real.rpow_add hnR 1 (-σ))
        calc
          _ = Real.rpow (n : ℝ) 1 * Real.rpow (n : ℝ) (-σ) := by simp
          _ = Real.rpow (n : ℝ) (1 + (-σ)) := hadd.symm
          _ = Real.rpow (n : ℝ) (1 - σ) := by congr 1 <;> ring
      have hpowExp : Real.rpow (n : ℝ) (1 - σ) =
          Real.exp (Real.log (n : ℝ) * (1 - σ)) := by
        exact Real.rpow_def_of_pos hnR (1 - σ)
      rw [hpowIdent]
      rw [hpowExp]
      exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hphase)
    have hTail := cont_high_dyadic_tail_bound hqpos χ
      (by positivity : 0 < Cφ) hNpos hNX hY₀N hXleY hσnonneg
      hPhaseAtX hweight
    have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog₂half : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_two_gt_d9
      norm_num at h ⊢
      linarith
    have hlogX : Real.log (X : ℝ) ≤ Real.log Y :=
      Real.log_le_log hXpos hXleY
    have hnatlog : (Nat.log 2 X : ℝ) ≤ 10 * L := by
      calc
        (Nat.log 2 X : ℝ) ≤ Real.logb 2 X := Real.natLog_le_logb X 2
        _ = Real.log (X : ℝ) / Real.log 2 := by simp [Real.logb]
        _ ≤ Real.log Y / Real.log 2 :=
          div_le_div_of_nonneg_right hlogX hlog₂.le
        _ ≤ 10 * L := by
          rw [hYlog]
          apply (div_le_iff₀ hlog₂).2
          calc
            5 * L = 10 * L * (1 / 2) := by ring
            _ ≤ 10 * L * Real.log 2 :=
              mul_le_mul_of_nonneg_left hlog₂half (by positivity)
    have hdyadCount : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 11 * L := by
      calc
        ((Nat.log 2 X + 1 : ℕ) : ℝ) = (Nat.log 2 X : ℝ) + 1 := by norm_cast
        _ ≤ 10 * L + 1 := by linarith only [hnatlog]
        _ ≤ 11 * L := by linarith only [hLone]
    let d : ℕ := ⌈C₃⌉₊
    have hC₃d : C₃ ≤ (d : ℝ) := by simpa [d] using (Nat.le_ceil C₃)
    have hpowC₃ : Real.rpow T C₃ ≤ T ^ d := by
      rw [← Real.rpow_natCast T d]
      exact Real.rpow_le_rpow_of_exponent_le hToneT hC₃d
    have hden : 0 < Real.rpow T C₃ := Real.rpow_pos_of_pos hTpos _
    have hLover : (63 + 2 * Cφ) * T ^ 15 ≤ L / Real.rpow T C₃ := by
      apply (le_div_iff₀ hden).2
      calc
        (63 + 2 * Cφ) * T ^ 15 * Real.rpow T C₃ ≤
            (63 + 2 * Cφ) * T ^ 15 * T ^ d :=
              mul_le_mul_of_nonneg_left hpowC₃ (by positivity)
        _ = (63 + 2 * Cφ) * T ^ (d + 15) := by rw [pow_add]; ring
        _ ≤ L := by simpa [d] using hLdyn
    have hTpow₄₁₅ : T ^ 4 ≤ T ^ 15 := by
      have h := Real.rpow_le_rpow_of_exponent_le hToneT
        (by norm_num : (4 : ℝ) ≤ 15)
      simpa [Real.rpow_natCast] using h
    have hTpow₁₁₅ : T ≤ T ^ 15 := by
      have h := Real.rpow_le_rpow_of_exponent_le hToneT
        (by norm_num : (1 : ℝ) ≤ 15)
      simpa [Real.rpow_natCast] using h
    have hone₁₅ : 1 ≤ T ^ 15 := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hToneT
        (by norm_num : (0 : ℝ) ≤ 15)
      simpa using h
    have hTailExp : -L / Real.rpow T C₃ + 50 * T ^ 4 +
        (2 * Cφ + 11 + T) ≤ 0 := by
      have hterm50 : 50 * T ^ 4 ≤ 50 * T ^ 15 :=
        mul_le_mul_of_nonneg_left hTpow₄₁₅ (by norm_num)
      have htermT : T ≤ T ^ 15 := hTpow₁₁₅
      have hCφnonneg : 0 ≤ 2 * Cφ := by positivity
      have htermPhi : 2 * Cφ ≤ (2 * Cφ) * T ^ 15 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hone₁₅ hCφnonneg
      have hterm11 : (11 : ℝ) ≤ 11 * T ^ 15 :=
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone₁₅ (by norm_num)
      have hsmall := calc
        50 * T ^ 4 + T + 2 * Cφ + 11 ≤
              50 * T ^ 15 + T ^ 15 + (2 * Cφ) * T ^ 15 + 11 * T ^ 15 := by
              linarith only [hterm50, htermT, htermPhi, hterm11]
        _ = (62 + 2 * Cφ) * T ^ 15 := by ring
        _ ≤ (63 + 2 * Cφ) * T ^ 15 := by
              exact mul_le_mul_of_nonneg_right (by norm_num : (62 + 2 * Cφ : ℝ) ≤ 63 + 2 * Cφ)
                (by positivity)
      have hL : (63 + 2 * Cφ) * T ^ 15 ≤ L / Real.rpow T C₃ := hLover
      rw [neg_div]
      have hneg := neg_le_neg hL
      linarith only [hneg, hsmall]
    have h2Cφ : 2 * Cφ ≤ Real.exp (2 * Cφ) := by
      have h := Real.add_one_le_exp (2 * Cφ)
      have h' : 2 * Cφ ≤ 2 * Cφ + 1 := by linarith
      exact h'.trans h
    have h11 : (11 : ℝ) ≤ Real.exp 11 := by
      have h := Real.add_one_le_exp (11 : ℝ)
      linarith only [h]
    have hcoef : 2 * Cφ * ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤
        Real.exp (2 * Cφ + 11 + T) := by
      calc
        _ ≤ (2 * Cφ) * (11 * L) :=
          mul_le_mul_of_nonneg_left hdyadCount (by positivity)
        _ = (2 * Cφ) * 11 * Real.exp T := by rw [← hLexp]; ring
        _ ≤ Real.exp (2 * Cφ) * Real.exp 11 * Real.exp T := by
          calc
            (2 * Cφ) * 11 * Real.exp T ≤
                (Real.exp (2 * Cφ) * 11) * Real.exp T := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h2Cφ (by norm_num))
                (Real.exp_nonneg _)
            _ ≤ (Real.exp (2 * Cφ) * Real.exp 11) * Real.exp T := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h11 (Real.exp_nonneg _))
                (Real.exp_nonneg _)
        _ = Real.exp (2 * Cφ + 11 + T) := by
          calc
            Real.exp (2 * Cφ) * Real.exp 11 * Real.exp T =
                Real.exp (2 * Cφ + 11) * Real.exp T := by
                  rw [← Real.exp_add]
            _ = Real.exp ((2 * Cφ + 11) + T) := by rw [← Real.exp_add]
            _ = Real.exp (2 * Cφ + 11 + T) := by congr 1 <;> ring
    have hTailSmall : 2 * Cφ * ((Nat.log 2 X + 1 : ℕ) : ℝ) *
        Real.exp (-L / Real.rpow T C₃ + 50 * T ^ 4) ≤ 1 := by
      calc
        _ ≤ Real.exp (2 * Cφ + 11 + T) *
              Real.exp (-L / Real.rpow T C₃ + 50 * T ^ 4) :=
          mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
        _ = Real.exp (-L / Real.rpow T C₃ + 50 * T ^ 4 +
              (2 * Cφ + 11 + T)) := by
          calc
            _ = Real.exp ((2 * Cφ + 11 + T) +
                  (-L / Real.rpow T C₃ + 50 * T ^ 4)) :=
                    (Real.exp_add _ _).symm
            _ = _ := by congr 1 <;> ring
        _ ≤ 1 := (Real.exp_le_one_iff).2 hTailExp
    have hTailSmall' : ‖∑ n ∈ Finset.Icc N X,
        χ (n : ZMod q) * Complex.exp (-⟨σ, v⟩ * Real.log (n : ℝ))‖ ≤ 1 := by
      calc
        _ ≤ 2 * Cφ * ((Nat.log 2 X + 1 : ℕ) : ℝ) *
              Real.exp (-L / Real.rpow T C₃ + 50 * T ^ 4) := by
          exact hTail
        _ ≤ 1 := hTailSmall
    have hheadExp : ‖dirichletPartialSum q χ Y₀ s‖ ≤
        Real.exp (12 * T ^ 2) := by
      have hhead := cont_partial_sum_bound q χ
        (Y := Y₀) (σ := σ) (v := v) hY0one
      have hlogY₀ : Real.log Y₀ = L / T ^ 2 := by
        dsimp [Y₀]
        exact Real.log_exp _
      have hdelta : |1 - σ| ≤ 10 * (T ^ 4 / L) := by
        simpa [abs_sub_comm] using hσR
      have hpowHead : Real.rpow Y₀ (1 - σ) ≤ Real.exp (10 * T ^ 2) := by
        have hpowDef : Real.rpow Y₀ (1 - σ) =
            Real.exp (Real.log Y₀ * (1 - σ)) :=
          Real.rpow_def_of_pos hY0pos (1 - σ)
        rw [hpowDef, hlogY₀]
        apply Real.exp_le_exp.mpr
        have hfac : 0 ≤ L / T ^ 2 := by positivity
        calc
          (L / T ^ 2) * (1 - σ) ≤ (L / T ^ 2) * |1 - σ| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hfac
          _ ≤ (L / T ^ 2) * (10 * (T ^ 4 / L)) :=
            mul_le_mul_of_nonneg_left hdelta hfac
          _ = 10 * T ^ 2 := by field_simp [ne_of_gt hLpos, ne_of_gt hTpos]
      have hmax : max 1 (Real.rpow Y₀ (1 - σ)) ≤ Real.exp (10 * T ^ 2) := by
        apply max_le_iff.mpr
        exact ⟨Real.one_le_exp (by positivity), hpowHead⟩
      have hlogfactor : 1 + Real.log Y₀ ≤ Real.exp (2 * T ^ 2) := by
        rw [hlogY₀]
        have hdiv : L / T ^ 2 ≤ L := by
          apply (div_le_iff₀ (by positivity)).2
          calc
            L = L * 1 := by ring
            _ ≤ L * T ^ 2 := mul_le_mul_of_nonneg_left hT2 hLpos.le
        calc
          1 + L / T ^ 2 ≤ 1 + L := by linarith only [hdiv]
          _ = 1 + Real.exp T := by rw [hLexp]
          _ ≤ 2 * Real.exp T := by
            have h := Real.one_le_exp hTpos.le
            linarith only [h]
          _ ≤ Real.exp (T + 1) := by
            rw [Real.exp_add]
            have hExp1 : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
            calc
              2 * Real.exp T = Real.exp T * 2 := by ring
              _ ≤ Real.exp T * Real.exp 1 :=
                mul_le_mul_of_nonneg_left hExp1 (Real.exp_nonneg _)
          _ ≤ Real.exp (2 * T ^ 2) :=
            Real.exp_le_exp.mpr (by nlinarith only [hToneT, hT2])
      calc
        _ ≤ (1 + Real.log Y₀) * max 1 (Real.rpow Y₀ (1 - σ)) := hhead
        _ ≤ Real.exp (2 * T ^ 2) * max 1 (Real.rpow Y₀ (1 - σ)) :=
          mul_le_mul_of_nonneg_right hlogfactor (by positivity)
        _ ≤ Real.exp (2 * T ^ 2) * Real.exp (10 * T ^ 2) :=
          mul_le_mul_of_nonneg_left hmax (Real.exp_nonneg _)
        _ = Real.exp (12 * T ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hsplit := cont_partial_sum_split (q := q) (χ := χ)
      (Y₀ := Y₀) (Y := Y) (σ := σ) (v := v) hfloor
    have hpartialY : ‖dirichletPartialSum q χ Y s‖ ≤
        Real.exp (12 * T ^ 2) + 1 := by
      rw [hsplit]
      calc
        _ ≤ ‖dirichletPartialSum q χ Y₀ s‖ +
              ‖∑ n ∈ Finset.Icc N X,
                χ (n : ZMod q) * Complex.exp (-s * Real.log (n : ℝ))‖ :=
          norm_add_le _ _
        _ ≤ Real.exp (12 * T ^ 2) + 1 := add_le_add hheadExp hTailSmall'
    have hYone : 1 ≤ Y := by
      have hY0Y : Y₀ ≤ Y := hY0leY
      exact hY0one.trans hY0Y
    have hApproxY := cont_approximation hqpos χ s
      hσlo hσhi hvlo hYone
    have hmean := cont_characterMean_norm_le_one hqpos χ
    have hden : Real.exp (L / (2 * T ^ 2)) ≤ ‖s - 1‖ := by
      calc
        Real.exp (L / (2 * T ^ 2)) ≤ |v| := hvhigh
        _ = |(s - 1).im| := by simp [s]
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have hdenpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (Real.exp_pos _) hden
    have hdivNeg : (-L) / (2 * T ^ 2) = -(L / (2 * T ^ 2)) := by rw [neg_div]
    have hdeninv : (‖s - 1‖)⁻¹ ≤ Real.exp (-L / (2 * T ^ 2)) := by
      have hinvEq : (Real.exp (L / (2 * T ^ 2)))⁻¹ =
          Real.exp ((-L) / (2 * T ^ 2)) := by
        calc
          (Real.exp (L / (2 * T ^ 2)))⁻¹ =
              Real.exp (-(L / (2 * T ^ 2))) := (Real.exp_neg _).symm
          _ = Real.exp ((-L) / (2 * T ^ 2)) := congrArg Real.exp hdivNeg.symm
      have hinv : (Real.exp (L / (2 * T ^ 2)))⁻¹ ≤
          Real.exp (-L / (2 * T ^ 2)) := by simpa only [neg_div] using hinvEq.le
      exact ((inv_le_inv₀ hdenpos (Real.exp_pos _)).mpr hden).trans hinv
    have hExpNormEq : ‖Complex.exp ((1 - s) * (Real.log Y : ℂ))‖ =
        Real.rpow Y (1 - σ) := by
      have hpowDef : Real.rpow Y (1 - σ) =
          Real.exp (Real.log Y * (1 - σ)) := Real.rpow_def_of_pos hYpos (1 - σ)
      have hRe : ((1 - s) * (Real.log Y : ℂ)).re =
          (1 - σ) * Real.log Y := by
        simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, s]
      calc
        ‖Complex.exp ((1 - s) * (Real.log Y : ℂ))‖ =
            Real.exp ((1 - σ) * Real.log Y) := by rw [Complex.norm_exp, hRe]
        _ = Real.exp (Real.log Y * (1 - σ)) :=
          congrArg Real.exp (mul_comm (1 - σ) (Real.log Y))
        _ = Real.rpow Y (1 - σ) := hpowDef.symm
    have hExpNorm : ‖Complex.exp ((1 - s) * (Real.log Y : ℂ))‖ ≤
        Real.exp (50 * T ^ 4) := by
      have hdelta : |1 - σ| ≤ 10 * (T ^ 4 / L) := by
        simpa [abs_sub_comm] using hσR
      have hlogpos : 0 ≤ Real.log Y := by rw [hYlog]; positivity
      have hphase : (1 - σ) * Real.log Y ≤ 50 * T ^ 4 := by
        calc
          (1 - σ) * Real.log Y ≤ |1 - σ| * Real.log Y :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hlogpos
          _ ≤ (10 * (T ^ 4 / L)) * (5 * L) :=
            mul_le_mul hdelta hYlog.le (by positivity) (by positivity)
          _ = 50 * T ^ 4 := by field_simp [ne_of_gt hLpos]; ring
      calc
        _ = Real.rpow Y (1 - σ) := hExpNormEq
        _ = Real.exp (Real.log Y * (1 - σ)) := Real.rpow_def_of_pos hYpos _
        _ ≤ Real.exp (50 * T ^ 4) :=
          Real.exp_le_exp.mpr (by simpa [mul_comm] using hphase)
    have hPole : ‖characterMean q χ *
        Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1)‖ ≤
        Real.exp (-L / (2 * T ^ 2) + 50 * T ^ 4) := by
      have hnum : ‖characterMean q χ‖ *
          ‖Complex.exp ((1 - s) * (Real.log Y : ℂ))‖ ≤
          Real.exp (50 * T ^ 4) := by
        calc
          _ ≤ 1 * ‖Complex.exp ((1 - s) * (Real.log Y : ℂ))‖ :=
            mul_le_mul_of_nonneg_right hmean (norm_nonneg _)
          _ ≤ Real.exp (50 * T ^ 4) := by simpa using hExpNorm
      calc
        _ = (‖characterMean q χ‖ *
              ‖Complex.exp ((1 - s) * (Real.log Y : ℂ))‖) *
                (‖s - 1‖)⁻¹ := by
                  rw [norm_div, norm_mul]
                  simp [div_eq_mul_inv, mul_assoc]
        _ ≤ Real.exp (50 * T ^ 4) * Real.exp (-L / (2 * T ^ 2)) :=
              mul_le_mul hnum hdeninv (by positivity) (by positivity)
        _ = Real.exp (-L / (2 * T ^ 2) + 50 * T ^ 4) := by
              rw [← Real.exp_add]
              congr 1 <;> ring
    have hPoleSmall : Real.exp (-L / (2 * T ^ 2) + 50 * T ^ 4) ≤ 1 := by
      have hdenom : 0 < T ^ 2 := by positivity
      have hineq : 50 * T ^ 4 ≤ L / (2 * T ^ 2) := by
        apply (le_div_iff₀ (by positivity)).2
        nlinarith [hL6]
      have harg : -L / (2 * T ^ 2) + 50 * T ^ 4 ≤ 0 := by
        rw [neg_div]
        have hneg := neg_le_neg hineq
        have hsum := add_le_add_right hneg (50 * T ^ 4)
        simpa [add_comm, add_left_comm, add_assoc] using hsum
      exact (Real.exp_le_one_iff).2 harg
    have hRemainderSmall : 4 * (q : ℝ) * (1 + ‖s‖) *
        Real.rpow Y (-σ) ≤ 1 := by
      have hqexp : (q : ℝ) ≤ Real.exp (C * T) := by
        have h : (q : ℝ) ≤ Real.rpow L C := by simpa [L] using hqC
        have hpowC : Real.rpow L C = Real.exp (Real.log L * C) :=
          Real.rpow_def_of_pos hLpos C
        calc
          (q : ℝ) ≤ Real.rpow L C := h
          _ = Real.exp (Real.log L * C) := hpowC
          _ = Real.exp (C * T) := by congr 1 <;> dsimp [T] <;> ring
      have hsNorm : 1 + ‖s‖ ≤ 4 * x ^ 3 := by
        have hsNorm' : ‖s‖ ≤ |σ| + |v| := by
          have hsrep : s = (σ : ℂ) + Complex.I * (v : ℂ) := by
            apply Complex.ext <;> simp [s]
          calc
            ‖s‖ = ‖(σ : ℂ) + Complex.I * (v : ℂ)‖ := by rw [hsrep]
            _ ≤ ‖(σ : ℂ)‖ + ‖Complex.I * (v : ℂ)‖ := norm_add_le _ _
            _ = |σ| + |v| := by simp
        have hvreal : 0 ≤ Real.rpow x 3 := Real.rpow_nonneg hxpos.le _
        have hpowx : Real.rpow x 3 = x ^ 3 := Real.rpow_natCast x 3
        have hv3 : |v| ≤ 3 * x ^ 3 := by simpa [hpowx] using hvhi
        have hsabs : |σ| ≤ 2 := by rw [abs_le]; constructor <;> linarith
        have hx3 : 3 ≤ x ^ 3 := by
          have hxpow3 : (2 : ℝ) ^ 3 ≤ x ^ 3 :=
            pow_le_pow_left₀ (by norm_num) hxgt2.le 3
          have hxpow3' : 8 ≤ x ^ 3 := by norm_num at hxpow3; exact hxpow3
          exact (by norm_num : (3 : ℝ) ≤ 8).trans hxpow3'
        calc
          1 + ‖s‖ ≤ 1 + (|σ| + |v|) := by linarith only [hsNorm']
          _ ≤ 1 + (2 + 3 * x ^ 3) := by
            linarith only [hsabs, hv3]
          _ = 3 + 3 * x ^ 3 := by ring
          _ ≤ 4 * x ^ 3 := by nlinarith only [hx3]
      have hsigmaLower : 1 - 10 * (T ^ 4 / L) ≤ σ := by
        have hh := (abs_le.mp hσR).1
        have hshift := add_le_add_left hh (1 : ℝ)
        have hshift' : -(10 * (T ^ 4 / L)) + 1 ≤ (σ - 1) + 1 := by
          simpa [add_comm] using hshift
        calc
          1 - 10 * (T ^ 4 / L) = -(10 * (T ^ 4 / L)) + 1 := by ring
          _ ≤ (σ - 1) + 1 := hshift'
          _ = σ := by ring
      have hrpowY : Real.rpow Y (-σ) ≤ Real.exp (-5 * L + 50 * T ^ 4) := by
        have hpowDef : Real.rpow Y (-σ) =
            Real.exp (Real.log Y * (-σ)) := Real.rpow_def_of_pos hYpos (-σ)
        rw [hpowDef, hYlog]
        apply Real.exp_le_exp.mpr
        calc
          (5 * L) * (-σ) = (-5 * L) * σ := by ring
          _ ≤ (-5 * L) * (1 - 10 * (T ^ 4 / L)) :=
            mul_le_mul_of_nonpos_left hsigmaLower (by
              have h5L : 0 ≤ 5 * L := mul_nonneg (by norm_num) hLpos.le
              linarith only [h5L])
          _ = (5 * L) * (-(1 - 10 * (T ^ 4 / L))) := by ring
          _ = -5 * L + 50 * T ^ 4 := by field_simp [ne_of_gt hLpos]; ring
      have hrem := calc
        4 * (q : ℝ) * (1 + ‖s‖) * Real.rpow Y (-σ) ≤
            16 * x ^ 3 * Real.exp (C * T) *
              Real.exp (-5 * L + 50 * T ^ 4) := by
                have hq4 : 4 * (q : ℝ) ≤ 4 * Real.exp (C * T) :=
                  mul_le_mul_of_nonneg_left hqexp (by norm_num)
                calc
                  _ ≤ (4 * Real.exp (C * T)) * (1 + ‖s‖) * Real.rpow Y (-σ) := by
                    apply mul_le_mul_of_nonneg_right
                    · exact mul_le_mul_of_nonneg_right hq4 (by positivity)
                    · exact Real.rpow_nonneg (by positivity) _
                  _ ≤ (4 * Real.exp (C * T)) * (4 * x ^ 3) * Real.rpow Y (-σ) := by
                    apply mul_le_mul_of_nonneg_right
                    · exact mul_le_mul_of_nonneg_left hsNorm (by positivity)
                    · exact Real.rpow_nonneg (by positivity) _
                  _ = 16 * x ^ 3 * Real.exp (C * T) * Real.rpow Y (-σ) := by ring
                  _ ≤ 16 * x ^ 3 * Real.exp (C * T) *
                        Real.exp (-5 * L + 50 * T ^ 4) :=
                      mul_le_mul_of_nonneg_left hrpowY (by positivity)
        _ ≤ 100 * Real.exp (-2 * L + 50 * T ^ 4 + C * T) := by
                have hxExp : x ^ 3 = Real.exp (3 * L) := by
                  rw [← Real.rpow_natCast x 3, Real.rpow_def_of_pos hxpos]
                  simp [L, mul_comm]
                calc
                  _ = 16 * Real.exp (3 * L) * Real.exp (C * T) *
                        Real.exp (-5 * L + 50 * T ^ 4) := by rw [hxExp]
                  _ = 16 * (Real.exp (3 * L) * Real.exp (C * T)) *
                        Real.exp (-5 * L + 50 * T ^ 4) := by ring
                  _ = 16 * Real.exp (3 * L + C * T) *
                        Real.exp (-5 * L + 50 * T ^ 4) := by
                    simpa [mul_assoc] using
                      congrArg (fun z : ℝ => 16 * z *
                        Real.exp (-5 * L + 50 * T ^ 4))
                        (Real.exp_add (3 * L) (C * T)).symm
                  _ = 16 * Real.exp ((3 * L + C * T) + (-5 * L + 50 * T ^ 4)) := by
                    simpa [mul_assoc] using
                      congrArg (fun z : ℝ => 16 * z)
                        (Real.exp_add (3 * L + C * T)
                          (-5 * L + 50 * T ^ 4)).symm
                  _ = 16 * Real.exp (-2 * L + 50 * T ^ 4 + C * T) := by
                        congr 1 <;> ring
                  _ ≤ 100 * Real.exp (-2 * L + 50 * T ^ 4 + C * T) :=
                        mul_le_mul_of_nonneg_right (by norm_num : (16 : ℝ) ≤ 100)
                          (Real.exp_nonneg _)
      have hCT : C * T ≤ C * T ^ 4 := by
        have hTpow : T ≤ T ^ 4 := by
          have h := Real.rpow_le_rpow_of_exponent_le hToneT
            (by norm_num : (1 : ℝ) ≤ 4)
          simpa [Real.rpow_natCast] using h
        exact mul_le_mul_of_nonneg_left hTpow hC.le
      have hT4 : 1 ≤ T ^ 4 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hToneT 4
        simpa using h
      have hsource : 50 * T ^ 4 + C * T ≤ (50 + C) * T ^ 4 := by
        calc
          50 * T ^ 4 + C * T ≤ 50 * T ^ 4 + C * T ^ 4 := by
            linarith only [hCT]
          _ = (50 + C) * T ^ 4 := by ring
      have hmargin : (50 + C) * T ^ 4 + 100 ≤ L := by
        have h100 : 100 ≤ 100 * T ^ 4 := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hT4 (by norm_num : (0 : ℝ) ≤ 100)
        calc
          (50 + C) * T ^ 4 + 100 ≤ (50 + C) * T ^ 4 + 100 * T ^ 4 := by
            linarith only [h100]
          _ = (150 + C) * T ^ 4 := by ring
          _ ≤ L := hL4
      have hExpo : -2 * L + 50 * T ^ 4 + C * T ≤ -100 := by
        have hsum : 50 * T ^ 4 + C * T + 100 ≤ L := by
          calc
            50 * T ^ 4 + C * T + 100 ≤ (50 + C) * T ^ 4 + 100 := by
              linarith only [hsource]
            _ ≤ L := hmargin
        linarith only [hsum, hLpos]
      calc
        _ ≤ 100 * Real.exp (-2 * L + 50 * T ^ 4 + C * T) := hrem
        _ ≤ Real.exp (-2 * L + 50 * T ^ 4 + C * T + 100) := by
          have h100 : (100 : ℝ) ≤ Real.exp 100 := by
            have h101 : (101 : ℝ) ≤ Real.exp 100 := by
              have h := Real.add_one_le_exp (100 : ℝ)
              linarith only [h]
            exact (by norm_num : (100 : ℝ) ≤ 101).trans h101
          let E : ℝ := -2 * L + 50 * T ^ 4 + C * T
          calc
            100 * Real.exp E = Real.exp E * 100 := by ring
            _ ≤ Real.exp E * Real.exp 100 :=
              mul_le_mul_of_nonneg_left h100
                (Real.exp_nonneg E)
            _ = Real.exp (E + 100) := (Real.exp_add E 100).symm
            _ = Real.exp (-2 * L + 50 * T ^ 4 + C * T + 100) := by rfl
        _ ≤ 1 := by
          apply (Real.exp_le_one_iff).2
          linarith
    have hApproxRemainder : ‖dirichletLValue q hqpos χ s -
        dirichletPartialSum q χ Y s -
          characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) /
            (s - 1)‖ ≤ 1 := by
      calc
        _ ≤ 4 * (q : ℝ) * (1 + ‖s‖) * Real.rpow Y (-s.re) := by
          simpa [s] using hApproxY
        _ = 4 * (q : ℝ) * (1 + ‖s‖) * Real.rpow Y (-σ) := by simp [s]
        _ ≤ 1 := hRemainderSmall
    have hLdecomp : dirichletLValue q hqpos χ s =
        (dirichletLValue q hqpos χ s - dirichletPartialSum q χ Y s -
          characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) /
            (s - 1)) + dirichletPartialSum q χ Y s +
              characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) /
                (s - 1) := by ring
    have htotal : ‖dirichletLValue q hqpos χ s‖ ≤
        Real.exp (12 * T ^ 2) + 3 := by
      rw [hLdecomp]
      have hRpart : ‖dirichletLValue q hqpos χ s -
            dirichletPartialSum q χ Y s -
              characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) /
                (s - 1) + dirichletPartialSum q χ Y s‖ ≤
          ‖dirichletLValue q hqpos χ s - dirichletPartialSum q χ Y s -
              characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) /
                (s - 1)‖ + ‖dirichletPartialSum q χ Y s‖ := norm_add_le _ _
      calc
        _ ≤ ‖dirichletLValue q hqpos χ s - dirichletPartialSum q χ Y s -
              characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) /
                (s - 1) + dirichletPartialSum q χ Y s‖ +
              ‖characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) /
                (s - 1)‖ := norm_add_le _ _
        _ ≤ (‖dirichletLValue q hqpos χ s - dirichletPartialSum q χ Y s -
              characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) /
                (s - 1)‖ + ‖dirichletPartialSum q χ Y s‖) +
              ‖characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) /
                (s - 1)‖ := by
            exact add_le_add_left hRpart _
        _ = ‖dirichletLValue q hqpos χ s - dirichletPartialSum q χ Y s -
              characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) /
                (s - 1)‖ +
              (‖dirichletPartialSum q χ Y s‖ +
                ‖characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) /
                  (s - 1)‖) := by ring_nf
        _ ≤ 1 + ((Real.exp (12 * T ^ 2) + 1) + 1) := by
            have hPoleNormle1 := hPole.trans hPoleSmall
            exact add_le_add hApproxRemainder
              (add_le_add hpartialY hPoleNormle1)
        _ = Real.exp (12 * T ^ 2) + 3 := by ring
    have hExpLarge : 4 ≤ Real.exp (8 * T ^ 2) := by
      calc
        4 ≤ 8 * T ^ 2 + 1 := by nlinarith only [hT2]
        _ ≤ Real.exp (8 * T ^ 2) := Real.add_one_le_exp _
    calc
      ‖dirichletLValue q hqpos χ s‖ ≤ Real.exp (12 * T ^ 2) + 3 := htotal
      _ ≤ 4 * Real.exp (12 * T ^ 2) := by
        have hOne : 1 ≤ Real.exp (12 * T ^ 2) := Real.one_le_exp (by positivity)
        have hThree : 3 ≤ 3 * Real.exp (12 * T ^ 2) := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hOne (by norm_num : (0 : ℝ) ≤ 3))
        calc
          Real.exp (12 * T ^ 2) + 3 ≤
              Real.exp (12 * T ^ 2) + 3 * Real.exp (12 * T ^ 2) := by
                exact add_le_add (le_refl _) hThree
          _ = 4 * Real.exp (12 * T ^ 2) := by ring
      _ ≤ Real.exp (20 * T ^ 2) := by
        rw [show 20 * T ^ 2 = 12 * T ^ 2 + 8 * T ^ 2 by ring,
          Real.exp_add]
        calc
          4 * Real.exp (12 * T ^ 2) =
              Real.exp (12 * T ^ 2) * 4 := by ring
          _ ≤ Real.exp (12 * T ^ 2) * Real.exp (8 * T ^ 2) :=
            mul_le_mul_of_nonneg_left hExpLarge (Real.exp_nonneg _)

theorem cont_growth_bound
    (hLog : ArtinPrimitiveRoots.Proofs.pp_phase_p.phaseLogPhaseStatement) :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          let rstar := T ^ 4 / L
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ hq : 0 < q, ∀ χ : DirichletCharacter ℂ q,
              ∀ σ v : ℝ, |σ - 1| ≤ 10 * rstar →
                1 / 2 ≤ |v| → |v| ≤ 3 * Real.rpow x 3 →
                  ‖dirichletLValue q hq χ (⟨σ, v⟩ : ℂ)‖ ≤
                    Real.exp (C₀ * T ^ 2) := by
  intro C hC
  obtain ⟨C₀L, x₀L, hC₀L, hx₀L, hLow⟩ := cont_growth_low_height_bound hLog C hC
  obtain ⟨C₀H, x₀H, hC₀H, hx₀H, hHigh⟩ := cont_growth_high_height_bound hLog C hC
  refine ⟨max C₀L C₀H, max x₀L x₀H,
    lt_of_lt_of_le hC₀L (le_max_left _ _),
    lt_of_lt_of_le hx₀L (le_max_left _ _), ?_⟩
  intro x hx
  dsimp only
  intro q hq hqC hqpos χ σ v hσ hvlo hvhi
  by_cases hlow : |v| ≤ Real.exp (Real.log x / (2 * Real.log (Real.log x) ^ 2))
  · have hbound := hLow x (le_trans (le_max_left _ _) hx) q hq hqC hqpos χ
      σ v hσ hvlo hvhi hlow
    have hT : 0 ≤ Real.log (Real.log x) ^ 2 := sq_nonneg _
    calc
      _ ≤ Real.exp (C₀L * Real.log (Real.log x) ^ 2) := hbound
      _ ≤ Real.exp (max C₀L C₀H * Real.log (Real.log x) ^ 2) :=
        Real.exp_le_exp.mpr <|
          mul_le_mul_of_nonneg_right (le_max_left _ _) hT
  · have hhigh :
        Real.exp (Real.log x / (2 * Real.log (Real.log x) ^ 2)) ≤ |v| :=
      (not_le.mp hlow).le
    have hbound := hHigh x (le_trans (le_max_right _ _) hx) q hq hqC hqpos χ
      σ v hσ hvlo hvhi hhigh
    have hT : 0 ≤ Real.log (Real.log x) ^ 2 := sq_nonneg _
    calc
      _ ≤ Real.exp (C₀H * Real.log (Real.log x) ^ 2) := hbound
      _ ≤ Real.exp (max C₀L C₀H * Real.log (Real.log x) ^ 2) :=
        Real.exp_le_exp.mpr <|
          mul_le_mul_of_nonneg_right (le_max_right _ _) hT

end ArtinPrimitiveRoots.Proofs.pp_cont_p
