import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2.Core

/-!
# Mellin transforms of compactly supported smooth weights (helpers for P2)

`IsBump g`: smooth, vanishing on `(0, a]` and `[b, ∞)` with `a > 0`.  Its Mellin transform is
entire, satisfies `M g(v) = -(1/v) M g'(v+1)` and decays faster than any power of `|Im v|`
uniformly on vertical strips.  For a QS weight `h`, `Φ_h(w) = -(1/w) M h'(w+1)` continues
`M h` from `Re w > 0` to `w ≠ 0`.
-/

set_option autoImplicit false

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSP2

/-- Smooth, vanishing on `(0, a]` and on `[b, ∞)`, `0 < a ≤ b`. -/
def IsBump (g : ℝ → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ x : ℝ, (0 < x ∧ x ≤ a) ∨ b ≤ x → g x = 0

theorem deriv_eq_zero_of_eqOn_zero {g : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ∀ x ∈ U, g x = 0) {x : ℝ} (hx : x ∈ U) : deriv g x = 0 := by
  have : g =ᶠ[𝓝 x] fun _ => 0 := Filter.eventually_of_mem (hU.mem_nhds hx) hg
  rw [this.deriv_eq]
  simp

theorem IsBump.deriv_bump {g : ℝ → ℂ} (hg : IsBump g) : IsBump (deriv g) := by
  obtain ⟨hs, a, b, ha, hab, hz⟩ := hg
  refine ⟨?_, a / 2, b + 1, by positivity, by linarith, fun x hx => ?_⟩
  · exact (contDiff_infty_iff_deriv.mp hs).2
  · rcases hx with ⟨h1, h2⟩ | h
    · exact deriv_eq_zero_of_eqOn_zero (U := Ioo 0 a) isOpen_Ioo
        (fun y hy => hz y (Or.inl ⟨hy.1, hy.2.le⟩)) ⟨h1, by linarith⟩
    · exact deriv_eq_zero_of_eqOn_zero (U := Ioi b) isOpen_Ioi
        (fun y hy => hz y (Or.inr (le_of_lt hy))) (show b < x by linarith)

theorem IsBump.continuous {g : ℝ → ℂ} (hg : IsBump g) : Continuous g :=
  hg.1.continuous

/-- The Mellin integral of a bump is an integral over `[a, b]`. -/
theorem IsBump.mellin_eq_Icc {g : ℝ → ℂ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hz : ∀ x : ℝ, (0 < x ∧ x ≤ a) ∨ b ≤ x → g x = 0) (v : ℂ) :
    mellin g v = ∫ x in a..b, (x : ℂ) ^ (v - 1) * g x := by
  rw [mellin, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun x hx => show (0:ℝ) < x from lt_of_lt_of_le ha hx.1) (fun x hx => ?_)
  have h0 : (0:ℝ) < x := hx.1
  have hx' : ¬ (a ≤ x ∧ x ≤ b) := hx.2
  rw [smul_eq_mul, hz x ?_, mul_zero]
  by_cases h : x ≤ a
  · exact Or.inl ⟨h0, h⟩
  · exact Or.inr (by push Not at h hx'; exact (hx' h.le).le)

theorem IsBump.mellinConvergent {g : ℝ → ℂ} (hg : IsBump g) (v : ℂ) : MellinConvergent g v := by
  obtain ⟨hs, a, b, ha, hab, hz⟩ := hg
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (v - 1) • g t) (Icc a b) := by
    refine ContinuousOn.integrableOn_Icc ?_
    show ContinuousOn (fun t : ℝ => (t : ℂ) ^ (v - 1) * g t) (Icc a b)
    refine ContinuousOn.mul ?_ hs.continuous.continuousOn
    intro x hx
    exact (continuousAt_ofReal_cpow_const _ _
      (Or.inr (ne_of_gt (lt_of_lt_of_le ha hx.1)))).continuousWithinAt
  unfold MellinConvergent
  refine hint.of_forall_sdiff_eq_zero measurableSet_Ioi (fun x hx => ?_)
  have h0 : (0:ℝ) < x := hx.1
  have hx' : ¬ (a ≤ x ∧ x ≤ b) := hx.2
  rw [smul_eq_mul, hz x ?_, mul_zero]
  by_cases h : x ≤ a
  · exact Or.inl ⟨h0, h⟩
  · exact Or.inr (by push Not at h hx'; exact (hx' h.le).le)

/-- Integration by parts: `M g(v) = -(1/v) M g'(v+1)` for `v ≠ 0`. -/
theorem IsBump.mellin_ibp {g : ℝ → ℂ} (hg : IsBump g) {v : ℂ} (hv : v ≠ 0) :
    mellin g v = -(1 / v) * mellin (deriv g) (v + 1) := by
  have hgb := hg.deriv_bump
  obtain ⟨a', b', ha', hab', hz'⟩ := hgb.2
  obtain ⟨hs, a, b, ha, hab, hz⟩ := hg
  -- a common interval `[c, d]` on which both vanish outside
  set c : ℝ := min a a' with hc
  set d : ℝ := max b b' with hd
  have hc0 : 0 < c := lt_min ha ha'
  have hcd : c ≤ d := le_trans (min_le_left _ _) (le_trans hab (le_max_left _ _))
  have hzc : ∀ x : ℝ, (0 < x ∧ x ≤ c) ∨ d ≤ x → g x = 0 := by
    intro x hx
    rcases hx with ⟨h1, h2⟩ | h
    · exact hz x (Or.inl ⟨h1, h2.trans (min_le_left _ _)⟩)
    · exact hz x (Or.inr ((le_max_left _ _).trans h))
  have hzc' : ∀ x : ℝ, (0 < x ∧ x ≤ c) ∨ d ≤ x → deriv g x = 0 := by
    intro x hx
    rcases hx with ⟨h1, h2⟩ | h
    · exact hz' x (Or.inl ⟨h1, h2.trans (min_le_right _ _)⟩)
    · exact hz' x (Or.inr ((le_max_right _ _).trans h))
  rw [IsBump.mellin_eq_Icc hc0 hcd hzc, IsBump.mellin_eq_Icc hc0 hcd hzc']
  have hgc : g c = 0 := hzc c (Or.inl ⟨hc0, le_rfl⟩)
  have hgd : g d = 0 := hzc d (Or.inr le_rfl)
  have hvm1 : v - 1 ≠ -1 := by intro h; apply hv; linear_combination h
  have hderv : ∀ x ∈ uIcc c d,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (v - 1 + 1) / (v - 1 + 1)) ((x : ℂ) ^ (v - 1)) x := by
    intro x hx
    rw [uIcc_of_le hcd] at hx
    exact hasDerivAt_ofReal_cpow_const' (ne_of_gt (lt_of_lt_of_le hc0 hx.1)) hvm1
  have hderg : ∀ x ∈ uIcc c d, HasDerivAt g (deriv g x) x := fun x _ =>
    (hs.differentiable (by simp)).differentiableAt.hasDerivAt
  have hcp : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (v - 1)) (uIcc c d) := by
    intro x hx
    rw [uIcc_of_le hcd] at hx
    exact (continuousAt_ofReal_cpow_const _ _
      (Or.inr (ne_of_gt (lt_of_lt_of_le hc0 hx.1)))).continuousWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := c) (b := d)
    (u := g) (v := fun y : ℝ => (y : ℂ) ^ (v - 1 + 1) / (v - 1 + 1))
    (u' := deriv g) (v' := fun x : ℝ => (x : ℂ) ^ (v - 1)) hderg hderv
    ((hgb.continuous).intervalIntegrable _ _)
    (hcp.intervalIntegrable)
  rw [hgc, hgd, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  simp only [sub_add_cancel] at hibp
  have e1 : (∫ x in c..d, (x : ℂ) ^ (v - 1) * g x) = ∫ x in c..d, g x * (x : ℂ) ^ (v - 1) := by
    congr 1; funext x; ring
  have e2 : (∫ x in c..d, (x : ℂ) ^ (v + 1 - 1) * deriv g x) =
      v * ∫ x in c..d, deriv g x * ((x : ℂ) ^ v / v) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x
    rw [show v + 1 - 1 = v by ring]
    field_simp
  rw [e1, hibp, e2]
  field_simp

theorem IsBump.differentiableAt_mellin {g : ℝ → ℂ} (hg : IsBump g) (v : ℂ) :
    DifferentiableAt ℂ (mellin g) v := by
  obtain ⟨hs, a, b, ha, hab, hz⟩ := hg
  refine mellin_differentiableAt_of_isBigO_rpow (a := v.re + 1) (b := v.re - 1)
    (hs.continuous.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ (by linarith)
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop b] with x hx
    exact (hz x (Or.inr hx)).symm
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioc_mem_nhdsGT ha] with x hx
    exact (hz x (Or.inl ⟨hx.1, hx.2⟩)).symm

theorem rpow_le_add_of_mem_Icc {a b x c : ℝ} (ha : 0 < a) (hx : x ∈ Icc a b) :
    x ^ c ≤ a ^ c + b ^ c := by
  rcases le_or_gt 0 c with hc | hc
  · have := Real.rpow_le_rpow (by linarith [hx.1]) hx.2 hc
    have : 0 ≤ a ^ c := by positivity
    linarith
  · have := Real.rpow_le_rpow_of_nonpos ha hx.1 hc.le
    have : 0 ≤ b ^ c := Real.rpow_nonneg (by linarith [hx.1, hx.2]) c
    linarith

/-- Rapid decay of the Mellin transform of a bump on vertical strips. -/
theorem IsBump.mellin_decay (k : ℕ) : ∀ {g : ℝ → ℂ}, IsBump g → ∀ α β : ℝ, ∃ C : ℝ,
    ∀ v : ℂ, α ≤ v.re → v.re ≤ β → 1 ≤ |v.im| → ‖mellin g v‖ ≤ C / |v.im| ^ k := by
  induction k with
  | zero =>
    intro g hg α β
    obtain ⟨hs, a, b, ha, hab, hz⟩ := hg
    obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Icc a b) hs.continuous.continuousOn
    refine ⟨(a ^ (α - 1) + b ^ (α - 1) + a ^ (β - 1) + b ^ (β - 1)) * |Mg| * (b - a),
      fun v h1 h2 _ => ?_⟩
    rw [IsBump.mellin_eq_Icc ha hab hz, pow_zero, div_one]
    have hb : ∀ x ∈ Set.uIoc a b, ‖(x : ℂ) ^ (v - 1) * g x‖ ≤
        (a ^ (α - 1) + b ^ (α - 1) + a ^ (β - 1) + b ^ (β - 1)) * |Mg| := by
      intro x hx
      rw [uIoc_of_le hab] at hx
      have hx0 : 0 < x := lt_trans ha hx.1
      have hxI : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have e1 : x ^ (v - 1).re ≤ x ^ (α - 1) + x ^ (β - 1) :=
        rpow_le_add_of_mem hx0 (by simp; linarith) (by simp; linarith)
      have e2 := rpow_le_add_of_mem_Icc (c := α - 1) ha hxI
      have e3 := rpow_le_add_of_mem_Icc (c := β - 1) ha hxI
      have e4 : ‖g x‖ ≤ |Mg| := (hMg x hxI).trans (le_abs_self _)
      have hpos : 0 ≤ x ^ (v - 1).re := by positivity
      have hb0 : 0 ≤ b := by linarith
      have hS : 0 ≤ a ^ (α - 1) + b ^ (α - 1) + a ^ (β - 1) + b ^ (β - 1) := by
        have := Real.rpow_nonneg ha.le (α - 1)
        have := Real.rpow_nonneg hb0 (α - 1)
        have := Real.rpow_nonneg ha.le (β - 1)
        have := Real.rpow_nonneg hb0 (β - 1)
        linarith
      exact mul_le_mul (by linarith) e4 (norm_nonneg _) hS
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [abs_of_nonneg (sub_nonneg.mpr hab : (0:ℝ) ≤ b - a)] at this
    exact this
  | succ k ih =>
    intro g hg α β
    obtain ⟨C, hC⟩ := ih hg.deriv_bump (α + 1) (β + 1)
    refine ⟨|C|, fun v h1 h2 ht => ?_⟩
    have hv : v ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
    rw [hg.mellin_ibp hv, norm_mul, norm_neg, one_div, norm_inv]
    have hb := hC (v + 1) (by simp; linarith) (by simp; linarith) (by simpa using ht)
    rw [(show (v + 1).im = v.im by simp)] at hb
    have hnv : |v.im| ≤ ‖v‖ := Complex.abs_im_le_norm v
    have hpos : 0 < |v.im| := by linarith
    have hb' : ‖mellin (deriv g) (v + 1)‖ ≤ |C| / |v.im| ^ k :=
      hb.trans (div_le_div_of_nonneg_right (le_abs_self C) (by positivity))
    calc ‖v‖⁻¹ * ‖mellin (deriv g) (v + 1)‖ ≤ |v.im|⁻¹ * (|C| / |v.im| ^ k) :=
          mul_le_mul (inv_anti₀ hpos hnv) hb' (norm_nonneg _) (by positivity)
      _ = |C| / |v.im| ^ (k + 1) := by rw [pow_succ]; field_simp

/-! ### QS weights -/

/-- The derivative of a QS weight is a bump. -/
theorem qsWeight_deriv_bump {h : ℝ → ℂ} (hh : IsQSWeight h) : IsBump (deriv h) := by
  obtain ⟨hs, ⟨B, hB⟩, δ, hδ, hconst⟩ := hh
  refine ⟨(contDiff_infty_iff_deriv.mp hs).2, δ / 2, max B δ + 1, by positivity,
    by linarith [le_max_right B δ], fun x hx => ?_⟩
  rcases hx with ⟨h1, h2⟩ | h
  · have : ∀ y ∈ Ioo (0:ℝ) δ, h y - h 0 = 0 := fun y hy => by
      rw [hconst y ⟨hy.1.le, hy.2.le⟩, sub_self]
    have hd := deriv_eq_zero_of_eqOn_zero (g := fun y => h y - h 0) isOpen_Ioo this
      ⟨h1, by linarith⟩
    simpa using hd
  · exact deriv_eq_zero_of_eqOn_zero (U := Ioi B) isOpen_Ioi
      (fun y hy => hB y (le_of_lt hy)) (show B < x by linarith [le_max_left B δ])

/-- `Φ_h(w) = -(1/w) M h'(w+1)`, the continuation of `M h`. -/
def qsPhiH (h : ℝ → ℂ) (w : ℂ) : ℂ := -(1 / w) * mellin (deriv h) (w + 1)

theorem differentiableAt_qsPhiH {h : ℝ → ℂ} (hh : IsQSWeight h) {w : ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℂ (qsPhiH h) w := by
  unfold qsPhiH
  refine ((differentiableAt_const _).div differentiableAt_id hw).neg.mul ?_
  have h1 : DifferentiableAt ℂ (fun w : ℂ => w + 1) w := differentiableAt_id.add_const 1
  have h2 : DifferentiableAt ℂ (mellin (deriv h)) (w + 1) :=
    (qsWeight_deriv_bump hh).differentiableAt_mellin (w + 1)
  exact DifferentiableAt.comp (g := mellin (deriv h)) (f := fun w : ℂ => w + 1) w h2 h1

theorem qsPhiH_decay {h : ℝ → ℂ} (hh : IsQSWeight h) (k : ℕ) (α β : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, α ≤ w.re → w.re ≤ β → 1 ≤ |w.im| → ‖qsPhiH h w‖ ≤ C / |w.im| ^ k := by
  obtain ⟨C, hC⟩ := (qsWeight_deriv_bump hh).mellin_decay k (α + 1) (β + 1)
  refine ⟨|C|, fun w h1 h2 ht => ?_⟩
  have hw : w ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  unfold qsPhiH
  rw [norm_mul, norm_neg, one_div, norm_inv]
  have hb := hC (w + 1) (by simp; linarith) (by simp; linarith) (by simpa using ht)
  rw [(show (w + 1).im = w.im by simp)] at hb
  have hnw : 1 ≤ ‖w‖ := le_trans ht (Complex.abs_im_le_norm w)
  have hinv : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnw
  calc ‖w‖⁻¹ * ‖mellin (deriv h) (w + 1)‖ ≤ 1 * (|C| / |w.im| ^ k) :=
        mul_le_mul hinv (hb.trans (div_le_div_of_nonneg_right (le_abs_self C) (by positivity)))
          (norm_nonneg _) zero_le_one
    _ = |C| / |w.im| ^ k := one_mul _

/-- `M h(w) = Φ_h(w)` for a QS weight on `Re w > 0`. -/
theorem mellin_qsWeight {h : ℝ → ℂ} (hh : IsQSWeight h) {w : ℂ} (hw : 0 < w.re) :
    mellin h w = qsPhiH h w := by
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
  obtain ⟨hs, ⟨B, hB⟩, δ, hδ, hconst⟩ := hh
  set c : ℝ := δ / 2 with hc
  set d : ℝ := max B δ + 1 with hd
  have hc0 : 0 < c := by positivity
  have hcδ : c ≤ δ := by linarith
  have hcd : c ≤ d := by linarith [le_max_right B δ]
  have hBd : B ≤ d := by linarith [le_max_left B δ]
  have hz' : ∀ x : ℝ, (0 < x ∧ x ≤ c) ∨ d ≤ x → deriv h x = 0 := by
    intro x hx
    rcases hx with ⟨h1, h2⟩ | h
    · have : ∀ y ∈ Ioo (0:ℝ) δ, h y - h 0 = 0 := fun y hy => by
        rw [hconst y ⟨hy.1.le, hy.2.le⟩, sub_self]
      have hd' := deriv_eq_zero_of_eqOn_zero (g := fun y => h y - h 0) isOpen_Ioo this
        ⟨h1, by linarith⟩
      simpa using hd'
    · exact deriv_eq_zero_of_eqOn_zero (U := Ioi B) isOpen_Ioi
        (fun y hy => hB y (le_of_lt hy)) (show B < x by linarith [le_max_left B δ])
  unfold qsPhiH
  rw [IsBump.mellin_eq_Icc hc0 hcd hz']
  -- split the Mellin integral of `h`
  have hcont : Continuous h := hs.continuous
  have hI1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (w - 1) * h x) volume 0 c := by
    have hpow : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (w - 1) * h 0) volume 0 c :=
      (intervalIntegral.intervalIntegrable_cpow' (r := w - 1) (by simp; linarith)).mul_const _
    refine hpow.congr (fun x hx => ?_)
    rw [uIoc_of_le hc0.le] at hx
    rw [hconst x ⟨hx.1.le, hx.2.trans hcδ⟩]
  have hI2 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (w - 1) * h x) volume c d := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul ?_ hcont.continuousOn
    intro x hx
    rw [uIcc_of_le hcd] at hx
    exact (continuousAt_ofReal_cpow_const _ _
      (Or.inr (ne_of_gt (lt_of_lt_of_le hc0 hx.1)))).continuousWithinAt
  have hsplit : mellin h w = (∫ x in (0:ℝ)..c, (x : ℂ) ^ (w - 1) * h x) +
      ∫ x in c..d, (x : ℂ) ^ (w - 1) * h x := by
    rw [intervalIntegral.integral_add_adjacent_intervals hI1 hI2, mellin,
      intervalIntegral.integral_of_le (hc0.le.trans hcd)]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => hx.1) (fun x hx => ?_)
    have hx0 : (0:ℝ) < x := hx.1
    have hxd : ¬ (0 < x ∧ x ≤ d) := hx.2
    push Not at hxd
    rw [smul_eq_mul, hB x (by linarith [hxd hx0]), mul_zero]
  -- the piece near zero
  have hP1 : (∫ x in (0:ℝ)..c, (x : ℂ) ^ (w - 1) * h x) = (c : ℂ) ^ w / w * h 0 := by
    have : (∫ x in (0:ℝ)..c, (x : ℂ) ^ (w - 1) * h x) =
        ∫ x in (0:ℝ)..c, (x : ℂ) ^ (w - 1) * h 0 := by
      refine intervalIntegral.integral_congr_ae ?_
      refine Eventually.of_forall fun x hx => ?_
      rw [uIoc_of_le hc0.le] at hx
      rw [hconst x ⟨hx.1.le, hx.2.trans hcδ⟩]
    rw [this, intervalIntegral.integral_mul_const,
      integral_cpow (Or.inl (by simp; linarith))]
    rw [sub_add_cancel, Complex.ofReal_zero, Complex.zero_cpow hw0, sub_zero]
  -- the piece away from zero, by parts
  have hhc : h c = h 0 := hconst c ⟨hc0.le, hcδ⟩
  have hhd : h d = 0 := hB d hBd
  have hvm1 : w - 1 ≠ -1 := by intro h; apply hw0; linear_combination h
  have hderv : ∀ x ∈ uIcc c d,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (w - 1 + 1) / (w - 1 + 1)) ((x : ℂ) ^ (w - 1)) x := by
    intro x hx
    rw [uIcc_of_le hcd] at hx
    exact hasDerivAt_ofReal_cpow_const' (ne_of_gt (lt_of_lt_of_le hc0 hx.1)) hvm1
  have hderh : ∀ x ∈ uIcc c d, HasDerivAt h (deriv h x) x := fun x _ =>
    (hs.differentiable (by simp)).differentiableAt.hasDerivAt
  have hcp : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (w - 1)) (uIcc c d) := by
    intro x hx
    rw [uIcc_of_le hcd] at hx
    exact (continuousAt_ofReal_cpow_const _ _
      (Or.inr (ne_of_gt (lt_of_lt_of_le hc0 hx.1)))).continuousWithinAt
  have hderc : Continuous (deriv h) := (contDiff_infty_iff_deriv.mp hs).2.continuous
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := c) (b := d)
    (u := h) (v := fun y : ℝ => (y : ℂ) ^ (w - 1 + 1) / (w - 1 + 1))
    (u' := deriv h) (v' := fun x : ℝ => (x : ℂ) ^ (w - 1)) hderh hderv
    (hderc.intervalIntegrable _ _) hcp.intervalIntegrable
  simp only [sub_add_cancel] at hibp
  rw [hhc, hhd] at hibp
  have e1 : (∫ x in c..d, (x : ℂ) ^ (w - 1) * h x) = ∫ x in c..d, h x * (x : ℂ) ^ (w - 1) := by
    congr 1; funext x; ring
  have e2 : (∫ x in c..d, (x : ℂ) ^ (w + 1 - 1) * deriv h x) =
      w * ∫ x in c..d, deriv h x * ((x : ℂ) ^ w / w) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x
    rw [show w + 1 - 1 = w by ring]
    field_simp
  rw [hsplit, hP1, e1, hibp, e2]
  field_simp
  ring

end ArtinPrimitiveRoots.A2.QSP2
