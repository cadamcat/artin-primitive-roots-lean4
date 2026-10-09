import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.Interfaces

/-! Exact interfaces for the PP Dirichlet-series continuation estimates. -/

namespace ArtinPrimitiveRoots.Proofs.pp_cont_p

open MeasureTheory
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

theorem cont_abel_identity {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (s : ℂ)
    (hs : 0 < s.re) (him : s.im ≠ 0) :
    dirichletLValue q hq χ s = dirichletPartialSum q χ Y s +
      characterMean q χ *
        Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1) +
      contTail q χ Y s := by
  sorry

theorem cont_approximation {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hσlo : 1 / 2 ≤ s.re) (hσhi : s.re ≤ 2)
    (him : 1 / 2 ≤ |s.im|) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖dirichletLValue q hq χ s - dirichletPartialSum q χ Y s -
      characterMean q χ * Complex.exp ((1 - s) * (Real.log Y : ℂ)) / (s - 1)‖ ≤
      4 * (q : ℝ) * (1 + ‖s‖) * Real.rpow Y (-s.re) := by
  sorry

theorem cont_partial_sum_bound (q : ℕ) (χ : DirichletCharacter ℂ q)
    {Y σ v : ℝ} (hY : 1 ≤ Y) :
    ‖dirichletPartialSum q χ Y (⟨σ, v⟩ : ℂ)‖ ≤
      (1 + Real.log Y) * max 1 (Real.rpow Y (1 - σ)) := by
  sorry

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
  sorry

end ArtinPrimitiveRoots.Proofs.pp_cont_p
