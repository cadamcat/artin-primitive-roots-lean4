import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2.Mellin

/-!
# P2 data for the square weight `f(y) = h(y²)` of a QS weight `h`

`Mellin f(s) = ½ Φ_h(s/2) = -(1/s) M h'(s/2 + 1)`; `Ψ(s) = -Z₁(s) M h'(s/2+1)`;
`D(u) = -G_K(u) (1-u)⁻¹G_K(1-u)⁻¹ M h'((1-u)/2 + 1)`.
-/

set_option autoImplicit false

open Complex Filter Topology MeasureTheory Set NumberField
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSP2

variable {K : Type} [Field K] [NumberField K]

/-! ### Generic extension lemmas (compact part of a strip) -/

theorem strip_compact (a b T : ℝ) :
    IsCompact {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ |s.im| ≤ T} := by
  have : {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ |s.im| ≤ T} = Icc a b ×ℂ Icc (-T) T := by
    ext s
    simp only [mem_setOf_eq, Complex.mem_reProdIm, mem_Icc, abs_le]
    tauto
  rw [this]
  exact isCompact_Icc.reProdIm isCompact_Icc

theorem strip_bounded_extend {F : ℂ → ℂ} {a b T C : ℝ}
    (hc : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ContinuousAt F s)
    (hC : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| → ‖F s‖ ≤ C) :
    ∃ C' : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖F s‖ ≤ C' := by
  obtain ⟨B, hB⟩ := (strip_compact a b T).exists_bound_of_continuousOn
    (fun s hs => (hc s hs.1 hs.2.1).continuousWithinAt)
  refine ⟨max B C, fun s h1 h2 => ?_⟩
  rcases le_or_gt T |s.im| with ht | ht
  · exact (hC s h1 h2 ht).trans (le_max_right _ _)
  · exact (hB s ⟨h1, h2, ht.le⟩).trans (le_max_left _ _)

theorem strip_decay_extend {F : ℂ → ℂ} {a b T C : ℝ} (hT : 1 ≤ T)
    (hc : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → |s.im| ≤ T → ContinuousAt F s)
    (hC : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| → ‖F s‖ ≤ C / s.im ^ 2) :
    ∃ C' : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → ‖F s‖ ≤ C' / s.im ^ 2 := by
  obtain ⟨B, hB⟩ := (strip_compact a b T).exists_bound_of_continuousOn
    (fun s hs => (hc s hs.1 hs.2.1 hs.2.2).continuousWithinAt)
  refine ⟨max C (|B| * T ^ 2), fun s h1 h2 ht => ?_⟩
  have hpos : 0 < s.im ^ 2 := by nlinarith [abs_nonneg s.im, sq_abs s.im]
  rcases le_or_gt T |s.im| with hT' | hT'
  · exact (hC s h1 h2 hT').trans (div_le_div_of_nonneg_right (le_max_left _ _) hpos.le)
  · rw [le_div_iff₀ hpos]
    have hb := (hB s ⟨h1, h2, hT'.le⟩).trans (le_abs_self B)
    have hs2 : s.im ^ 2 ≤ T ^ 2 := by nlinarith [abs_nonneg s.im, sq_abs s.im]
    calc ‖F s‖ * s.im ^ 2 ≤ |B| * T ^ 2 := mul_le_mul hb hs2 hpos.le (abs_nonneg _)
      _ ≤ max C (|B| * T ^ 2) := le_max_right _ _
      _ = max C (|B| * T ^ 2) := rfl

theorem integrable_of_cont_decay_T {g : ℝ → ℂ} (hg : Continuous g) {T C : ℝ} (hT : 1 ≤ T)
    (hC : ∀ t : ℝ, T ≤ |t| → ‖g t‖ ≤ C / t ^ 2) : Integrable g := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-T) T) hg.continuousOn
  refine integrable_of_cont_decay hg (max C (|B| * T ^ 2)) (fun t ht => ?_)
  have hpos : 0 < t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  rcases le_or_gt T |t| with hT' | hT'
  · exact (hC t hT').trans (div_le_div_of_nonneg_right (le_max_left _ _) hpos.le)
  · rw [le_div_iff₀ hpos]
    have hb := (hB t (abs_le.mp hT'.le)).trans (le_abs_self B)
    have hs2 : t ^ 2 ≤ T ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    calc ‖g t‖ * t ^ 2 ≤ |B| * T ^ 2 := mul_le_mul hb hs2 hpos.le (abs_nonneg _)
      _ ≤ max C (|B| * T ^ 2) := le_max_right _ _

/-- `Mellin(h(y²))(s) = ½ Mellin(h)(s/2)`. -/
theorem mellin_sq (g : ℝ → ℂ) (s : ℂ) :
    mellin (fun y : ℝ => g (y ^ 2)) s = (1 / 2 : ℂ) * mellin g (s / 2) := by
  have h1 : mellin (fun y : ℝ => g (y ^ 2)) s = mellin (fun y : ℝ => g (y ^ (2:ℝ))) s := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    simp only [Real.rpow_two]
  rw [h1, mellin_comp_rpow g s 2]
  rw [Complex.real_smul]
  norm_num


theorem pow_div_aux (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (1 + x) ^ n / (x / 2) ^ (n + 2) ≤ 4 ^ (n + 1) / x ^ 2 := by
  have h1 : (1 + x) ^ n ≤ (2 * x) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
  have hx0 : 0 < x := by linarith
  have hx0' : x ≠ 0 := hx0.ne'
  calc (1 + x) ^ n / (x / 2) ^ (n + 2) = (1 + x) ^ n * (2 / x) ^ (n + 2) := by
        rw [div_eq_mul_inv, ← inv_pow, inv_div]
    _ ≤ (2 * x) ^ n * (2 / x) ^ (n + 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2 * x * (2 / x)) ^ n * (2 / x) ^ 2 := by rw [pow_add, ← mul_assoc, ← mul_pow]
    _ = 4 ^ n * (4 / x ^ 2) := by
        congr 1
        · congr 1; field_simp; norm_num
        · rw [div_pow]; norm_num
    _ = 4 ^ (n + 1) / x ^ 2 := by rw [pow_succ]; ring

theorem pow_div_aux' (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (1 + x) ^ n / (x / 2) ^ n ≤ 4 ^ n := by
  have h1 : (1 + x) ^ n ≤ (2 * x) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
  have hx0 : 0 < x := by linarith
  have hx0' : x ≠ 0 := hx0.ne'
  calc (1 + x) ^ n / (x / 2) ^ n = (1 + x) ^ n * (2 / x) ^ n := by
        rw [div_eq_mul_inv, ← inv_pow, inv_div]
    _ ≤ (2 * x) ^ n * (2 / x) ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2 * x * (2 / x)) ^ n := by rw [← mul_pow]
    _ = 4 ^ n := by congr 1; field_simp; norm_num

theorem not_nonpos_int_one_sub {u : ℂ} (h1 : 1/2 ≤ u.re) (h2 : u.re ≤ 3/2) (hu1 : u ≠ 1) :
    ∀ m : ℕ, 1 - u ≠ -m := by
  intro m hm
  have hre := congrArg Complex.re hm
  simp at hre
  have hm1 : (m : ℝ) ≤ 1/2 := by linarith
  have hm0 : m = 0 := by
    by_contra h
    have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    linarith
  subst hm0
  have h0 : 1 - u = 0 := by simpa using hm
  exact hu1 (sub_eq_zero.mp h0).symm

/-! ### Case A -/

/-- The Mellin data of `h(y²)`. -/
def caseAPhi (h : ℝ → ℂ) (s : ℂ) : ℂ := (1 / 2 : ℂ) * qsPhiH h (s / 2)

theorem caseAPhi_eq (h : ℝ → ℂ) (s : ℂ) (hs : s ≠ 0) :
    caseAPhi h s = -(1 / s) * mellin (deriv h) (s / 2 + 1) := by
  unfold caseAPhi qsPhiH
  field_simp

theorem mellin_caseA {h : ℝ → ℂ} (hh : IsQSWeight h) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun y : ℝ => h (y ^ 2)) s = caseAPhi h s := by
  rw [mellin_sq, mellin_qsWeight hh (by simp; linarith), caseAPhi]

theorem continuous_caseAPhi_line {h : ℝ → ℂ} (hh : IsQSWeight h) {σ : ℝ} (hσ : σ ≠ 0) :
    Continuous (fun t : ℝ => caseAPhi h (σ + t * I)) := by
  refine continuous_iff_continuousAt.2 (fun t => ?_)
  have hne : ((σ : ℂ) + t * I) / 2 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    exact hσ this
  refine (ContinuousAt.mul continuousAt_const ?_)
  exact ((differentiableAt_qsPhiH hh hne).continuousAt).comp (f := fun t : ℝ => ((σ : ℂ) + t * I) / 2)
    (by fun_prop)

theorem caseAPhi_line_decay {h : ℝ → ℂ} (hh : IsQSWeight h) (σ : ℝ) :
    ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| → ‖caseAPhi h (σ + t * I)‖ ≤ C / t ^ 2 := by
  obtain ⟨C, hC⟩ := qsPhiH_decay hh 2 (σ / 2) (σ / 2)
  refine ⟨4 * |C|, fun t ht => ?_⟩
  have hre : (((σ : ℂ) + t * I) / 2).re = σ / 2 := by simp
  have him : (((σ : ℂ) + t * I) / 2).im = t / 2 := by simp
  have h1 : 1 ≤ |(((σ : ℂ) + t * I) / 2).im| := by
    rw [him, abs_div, abs_two]; linarith
  have hb := hC _ (by rw [hre]) (by rw [hre]) h1
  rw [him, abs_div, abs_two] at hb
  unfold caseAPhi
  rw [norm_mul]
  have ht0 : 0 < |t| := by linarith
  have hpos : 0 < t ^ 2 := by nlinarith [sq_abs t]
  have hnorm : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hnorm]
  calc 1 / 2 * ‖qsPhiH h (((σ : ℂ) + t * I) / 2)‖ ≤ 1 / 2 * (C / (|t| / 2) ^ 2) := by gcongr
    _ ≤ 4 * |C| / t ^ 2 := by
        rw [div_pow, sq_abs]
        field_simp
        rw [div_le_div_iff_of_pos_right (by positivity)]
        nlinarith [le_abs_self C, abs_nonneg C, hpos]

/-- The P2 data of `h(y²)`. -/
def caseAData [IsTotallyComplex K] {h : ℝ → ℂ} (hh : IsQSWeight h) :
    P2Data K (fun y : ℝ => h (y ^ 2)) where
  Φ := caseAPhi h
  Ψ := fun s => -(Z1 K s) * mellin (deriv h) (s / 2 + 1)
  D := fun u => -(Hecke.dedekindPrefactor K u) * zetaE K (1 - u) * mellin (deriv h) ((1 - u) / 2 + 1)
  inv := by
    intro x hx
    obtain ⟨B, hB⟩ := hh.2.1
    set T₀ : ℝ := max B 1 with hT₀
    have hconv : MellinConvergent (fun y : ℝ => h (y ^ 2)) ((3/2 : ℝ) : ℂ) := by
      have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (((3/2 : ℝ) : ℂ) - 1) • h (t ^ 2))
          (Icc 0 T₀) := by
        refine ContinuousOn.integrableOn_Icc ?_
        show ContinuousOn (fun t : ℝ => (t : ℂ) ^ (((3/2 : ℝ) : ℂ) - 1) * h (t ^ 2)) _
        refine ContinuousOn.mul ?_ (hh.1.continuous.comp (continuous_pow 2)).continuousOn
        intro t _
        exact (continuousAt_ofReal_cpow_const _ _ (Or.inl (by simp; norm_num))).continuousWithinAt
      refine hint.of_forall_sdiff_eq_zero measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (0:ℝ) < t := ht.1
      have hnot : ¬ (0 ≤ t ∧ t ≤ T₀) := ht.2
      have htT : T₀ < t := by push Not at hnot; exact hnot ht0.le
      have hT1 : 1 ≤ T₀ := le_max_right _ _
      have hBt : B ≤ t ^ 2 := by nlinarith [le_max_left B 1]
      rw [smul_eq_mul, hB _ hBt, mul_zero]
    have hvert : VerticalIntegrable (mellin (fun y : ℝ => h (y ^ 2))) (3/2) := by
      unfold Complex.VerticalIntegrable
      obtain ⟨C, hC⟩ := caseAPhi_line_decay hh (3/2)
      have := integrable_of_cont_decay_T (continuous_caseAPhi_line hh (by norm_num)) (by norm_num) hC
      refine this.congr (Eventually.of_forall fun t => ?_)
      exact (mellin_caseA hh (by simp)).symm
    have hcont : ContinuousAt (fun y : ℝ => h (y ^ 2)) x :=
      (hh.1.continuous.comp (continuous_pow 2)).continuousAt
    rw [← mellinInv_mellin_eq (3/2) _ hx hconv hvert hcont]
    simp only [mellinInv]
    congr 2
    funext t
    rw [mellin_caseA hh (by simp)]
  Φint := by
    obtain ⟨C, hC⟩ := caseAPhi_line_decay hh (3/2)
    exact integrable_of_cont_decay_T (continuous_caseAPhi_line hh (by norm_num)) (by norm_num) hC
  mel := fun s h1 _ => mellin_caseA hh h1
  Φc1 := by
    have : (1 : ℂ) / 2 ≠ 0 := by norm_num
    exact (continuousAt_const.mul ((differentiableAt_qsPhiH hh this).continuousAt.comp
      (f := fun s : ℂ => s / 2) (by fun_prop)))
  Ψd := by
    intro s _ _
    refine (differentiable_Z1 (K := K) s).neg.mul ?_
    exact DifferentiableAt.comp (g := mellin (deriv h)) (f := fun s : ℂ => s / 2 + 1) s
      ((qsWeight_deriv_bump hh).differentiableAt_mellin _) (by fun_prop)
  Ψeq := by
    intro s _ _ hs0 _
    rw [caseAPhi_eq h s hs0]
    field_simp
  Ψbd := by
    obtain ⟨CZ, hCZ0, hCZ⟩ := exists_Z1_poly (K := K)
    set N := 2 * InfinitePlace.nrComplexPlaces K + 1
    obtain ⟨CM, hCM⟩ := (qsWeight_deriv_bump hh).mellin_decay N (3/4) (7/4)
    refine strip_bounded_extend (F := fun s => -(Z1 K s) * mellin (deriv h) (s / 2 + 1))
      (a := -1/2) (b := 3/2) (T := 2) (C := CZ * |CM| * 4 ^ N) (fun s h1 h2 => ?_)
      (fun s h1 h2 ht => ?_)
    · exact ((differentiable_Z1 (K := K) s).neg.mul (DifferentiableAt.comp
        (g := mellin (deriv h)) (f := fun s : ℂ => s / 2 + 1) s
        ((qsWeight_deriv_bump hh).differentiableAt_mellin _) (by fun_prop))).continuousAt
    · have hre : (s / 2 + 1).re = s.re / 2 + 1 := by simp
      have him : (s / 2 + 1).im = s.im / 2 := by simp
      have hb := hCM (s / 2 + 1) (by rw [hre]; linarith) (by rw [hre]; linarith)
        (by rw [him, abs_div, abs_two]; linarith)
      rw [him, abs_div, abs_two] at hb
      have hz := hCZ s h1 h2
      have ht1 : 1 ≤ |s.im| := by linarith
      have hpos : 0 < (|s.im| / 2) ^ N := by positivity
      rw [norm_mul, norm_neg]
      calc ‖Z1 K s‖ * ‖mellin (deriv h) (s / 2 + 1)‖
          ≤ (CZ * (1 + |s.im|) ^ N) * (|CM| / (|s.im| / 2) ^ N) :=
            mul_le_mul hz (hb.trans (div_le_div_of_nonneg_right (le_abs_self _) hpos.le))
              (norm_nonneg _) (by positivity)
        _ = CZ * |CM| * ((1 + |s.im|) ^ N / (|s.im| / 2) ^ N) := by ring
        _ ≤ CZ * |CM| * 4 ^ N := by
            gcongr
            exact pow_div_aux' N ht1
  Dd := by
    intro u h1 _
    refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
    · exact (differentiableAt_prefactor (not_nonpos_int_of_re_pos (by linarith))).neg
    · exact (differentiable_zetaE (K := K) (1 - u)).comp u (by fun_prop)
    · exact DifferentiableAt.comp (g := mellin (deriv h)) (f := fun u : ℂ => (1 - u) / 2 + 1) u
        ((qsWeight_deriv_bump hh).differentiableAt_mellin _) (by fun_prop)
  Deq := by
    intro u h1 h2 hu1
    have h1u : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
    have hnint := not_nonpos_int_one_sub h1 h2 hu1
    have hG : Hecke.dedekindPrefactor K (1 - u) ≠ 0 := prefactor_ne_zero hnint
    show -(Hecke.dedekindPrefactor K u) * zetaE K (1 - u) * mellin (deriv h) ((1 - u) / 2 + 1) = _
    rw [qsGammaRatio, caseAPhi_eq h (1 - u) h1u, zetaE_eq hnint]
    field_simp
  Dbd := by
    obtain ⟨CR, hCR0, hCR⟩ := exists_ratio_poly (K := K)
    set r := InfinitePlace.nrComplexPlaces K
    obtain ⟨C, hC⟩ := qsPhiH_decay hh (2 * r + 2) (-1/4) (1/4)
    refine strip_decay_extend (F := fun u => -(Hecke.dedekindPrefactor K u) * zetaE K (1 - u) *
      mellin (deriv h) ((1 - u) / 2 + 1)) (a := 1/2) (b := 3/2) (T := 2)
      (C := CR * (|C| / 2) * 4 ^ (2 * r + 1)) (by norm_num)
      (fun u h1 h2 _ => ?_) (fun u h1 h2 ht => ?_)
    · have hd : DifferentiableAt ℂ (fun u => -(Hecke.dedekindPrefactor K u) * zetaE K (1 - u) *
          mellin (deriv h) ((1 - u) / 2 + 1)) u := by
        refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
        · exact (differentiableAt_prefactor (not_nonpos_int_of_re_pos (by linarith))).neg
        · exact (differentiable_zetaE (K := K) (1 - u)).comp u (by fun_prop)
        · exact DifferentiableAt.comp (g := mellin (deriv h)) (f := fun u : ℂ => (1 - u) / 2 + 1) u
            ((qsWeight_deriv_bump hh).differentiableAt_mellin _) (by fun_prop)
      exact hd.continuousAt
    · have hu1 : u ≠ 1 := by
        intro h; rw [h] at ht; simp at ht; linarith
      have h1u : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
      have hnint := not_nonpos_int_one_sub h1 h2 hu1
      have hG : Hecke.dedekindPrefactor K (1 - u) ≠ 0 := prefactor_ne_zero hnint
      have heq : -(Hecke.dedekindPrefactor K u) * zetaE K (1 - u) *
          mellin (deriv h) ((1 - u) / 2 + 1) = qsGammaRatio K u * caseAPhi h (1 - u) := by
        rw [qsGammaRatio, caseAPhi_eq h (1 - u) h1u, zetaE_eq hnint]
        field_simp
      rw [heq, norm_mul]
      have hR := hCR u h1 h2
      have hre : ((1 - u) / 2).re = (1 - u.re) / 2 := by simp
      have him : ((1 - u) / 2).im = -u.im / 2 := by simp
      have ht1 : 1 ≤ |u.im| := by linarith
      have hφ := hC ((1 - u) / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
        (by rw [him, abs_div, abs_neg, abs_two]; linarith)
      rw [him, abs_div, abs_neg, abs_two] at hφ
      have hcase : ‖caseAPhi h (1 - u)‖ ≤ (|C| / 2) / (|u.im| / 2) ^ (2 * r + 2) := by
        unfold caseAPhi
        rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num,
          show (1 - u) / 2 = (1 - u) / 2 from rfl]
        have hpos : 0 < (|u.im| / 2) ^ (2 * r + 2) := by positivity
        calc 1 / 2 * ‖qsPhiH h ((1 - u) / 2)‖ ≤ 1 / 2 * (|C| / (|u.im| / 2) ^ (2 * r + 2)) := by
              gcongr
              exact hφ.trans (div_le_div_of_nonneg_right (le_abs_self _) hpos.le)
          _ = (|C| / 2) / (|u.im| / 2) ^ (2 * r + 2) := by ring
      have hsq : u.im ^ 2 = |u.im| ^ 2 := (sq_abs _).symm
      calc ‖qsGammaRatio K u‖ * ‖caseAPhi h (1 - u)‖
          ≤ (CR * (1 + |u.im|) ^ (2 * r)) * ((|C| / 2) / (|u.im| / 2) ^ (2 * r + 2)) :=
            mul_le_mul hR hcase (norm_nonneg _) (by positivity)
        _ = CR * (|C| / 2) * ((1 + |u.im|) ^ (2 * r) / (|u.im| / 2) ^ (2 * r + 2)) := by ring
        _ ≤ CR * (|C| / 2) * (4 ^ (2 * r + 1) / |u.im| ^ 2) :=
            mul_le_mul_of_nonneg_left (pow_div_aux (2 * r) ht1) (by positivity)
        _ = CR * (|C| / 2) * 4 ^ (2 * r + 1) / u.im ^ 2 := by rw [hsq]; ring

end ArtinPrimitiveRoots.A2.QSP2
