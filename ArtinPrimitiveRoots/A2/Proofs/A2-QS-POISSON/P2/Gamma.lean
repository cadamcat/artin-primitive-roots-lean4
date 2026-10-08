import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2.PL
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».Defs

/-!
# Gamma-factor estimates for P2 (totally complex fields)

`G_K(s) = |d_K|^{s/2} Γ_ℂ(s)^{r₂}` (`Hecke.dedekindPrefactor`), the ratio
`R(u) = G_K(u)/G_K(1-u)` (`qsGammaRatio`): holomorphy, `‖R‖ = 1` on `Re u = 1/2`, the exact
recurrence `R(v+1) = |d|(-v²/4π²)^{r₂} R(v)`, and polynomial bounds on vertical strips
(Phragmén–Lindelöf between `Re u = 1/2` and `Re u = 3/2`).
-/

set_option autoImplicit false

open Complex Filter Topology MeasureTheory NumberField
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSP2

/-! ### Elementary Complex.Gamma bounds -/

theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) : ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Gamma_eq_integral hz, GammaIntegral, Real.Gamma_eq_integral hz]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by rw [Complex.norm_exp]; simp
  calc ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
        gcongr
        exact norm_sub_le _ _
    _ = (Real.exp z.im + Real.exp (-z.im)) / 2 := by rw [h1, h2]
    _ ≤ Real.exp |z.im| := by
        have ha := Real.exp_le_exp.2 (le_abs_self z.im)
        have hb := Real.exp_le_exp.2 (neg_le_abs z.im)
        linarith

theorem exists_Gamma_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Set.Icc (1/2 : ℝ) 4, Real.Gamma x ≤ M := by
  have hc : ContinuousOn Real.Gamma (Set.Icc (1/2 : ℝ) 4) := by
    intro x hx
    refine (Real.differentiableAt_Gamma ?_).continuousAt.continuousWithinAt
    intro m hm
    have : (0:ℝ) < x := by linarith [hx.1]
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 1, by positivity, fun x hx => ?_⟩
  have := hM x hx
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

/-- Crude growth of `1/Γ`: `‖Γ(w)⁻¹‖ ≤ M e^{π|Im w|}` for `-1 ≤ Re w ≤ 5/2`, `|Im w| ≥ 1`. -/
theorem exists_norm_inv_Gamma_le :
    ∃ M : ℝ, 0 < M ∧ ∀ w : ℂ, -1 ≤ w.re → w.re ≤ 5/2 → 1 ≤ |w.im| →
      ‖(Complex.Gamma w)⁻¹‖ ≤ M * Real.exp (Real.pi * |w.im|) := by
  obtain ⟨M, hM0, hM⟩ := exists_Gamma_bound
  refine ⟨M / Real.pi, by positivity, fun w h1 h2 ht => ?_⟩
  have him0 : w.im ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  have hw1 : w - 1 ≠ 0 := by intro h; apply him0; simpa using congrArg Complex.im h
  have hw2 : w - 2 ≠ 0 := by intro h; apply him0; simpa using congrArg Complex.im h
  have hΓ1 : Complex.Gamma w = (w - 1) * Complex.Gamma (w - 1) := by
    have := Complex.Gamma_add_one (w - 1) hw1
    simpa using this
  have hΓ2 : Complex.Gamma (w - 1) = (w - 2) * Complex.Gamma (w - 2) := by
    have := Complex.Gamma_add_one (w - 2) hw2
    rw [show w - 2 + 1 = w - 1 by ring] at this
    exact this
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (w - 2)
  rw [show (1 : ℂ) - (w - 2) = 3 - w by ring] at hrefl
  have hre3 : 0 < (3 - w).re := by simp; linarith
  have hΓ3 : Complex.Gamma (3 - w) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre3
  have hsin : Complex.sin (Real.pi * (w - 2)) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have := congrArg Complex.im hk
    have h1 : ((Real.pi : ℂ) * (w - 2)).im = Real.pi * w.im := by simp
    have h2 : ((k : ℂ) * (Real.pi : ℂ)).im = 0 := by simp
    rw [h1, h2] at this
    exact him0 ((mul_eq_zero.mp this).resolve_left Real.pi_ne_zero)
  have hΓw2 : Complex.Gamma (w - 2) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrefl
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hsin hrefl.symm
  have hinv : (Complex.Gamma w)⁻¹ = Complex.sin (Real.pi * (w - 2)) * Complex.Gamma (3 - w) /
      (Real.pi * ((w - 1) * (w - 2))) := by
    rw [hΓ1, hΓ2]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have key : Complex.Gamma (w - 2) =
        Real.pi / (Complex.sin (Real.pi * (w - 2)) * Complex.Gamma (3 - w)) := by
      rw [← div_div]
      exact eq_div_of_mul_eq hΓ3 hrefl
    rw [key]
    field_simp
  rw [hinv, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hsinb : ‖Complex.sin (Real.pi * (w - 2))‖ ≤ Real.exp (Real.pi * |w.im|) := by
    refine (norm_sin_le_exp _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  have hΓb : ‖Complex.Gamma (3 - w)‖ ≤ M :=
    (norm_Gamma_le_Gamma_re hre3).trans (hM _ ⟨by simp; linarith, by simp; linarith⟩)
  have hn1 : 1 ≤ ‖w - 1‖ := by
    have := Complex.abs_im_le_norm (w - 1)
    simp at this
    linarith
  have hn2 : 1 ≤ ‖w - 2‖ := by
    have := Complex.abs_im_le_norm (w - 2)
    simp at this
    linarith
  have hden : Real.pi ≤ Real.pi * (‖w - 1‖ * ‖w - 2‖) := by
    have : 1 ≤ ‖w - 1‖ * ‖w - 2‖ := one_le_mul_of_one_le_of_one_le hn1 hn2
    nlinarith [Real.pi_pos]
  rw [div_le_iff₀ (by positivity)]
  calc ‖Complex.sin (Real.pi * (w - 2))‖ * ‖Complex.Gamma (3 - w)‖
      ≤ Real.exp (Real.pi * |w.im|) * M := mul_le_mul hsinb hΓb (norm_nonneg _) (by positivity)
    _ = M / Real.pi * Real.exp (Real.pi * |w.im|) * Real.pi := by field_simp
    _ ≤ M / Real.pi * Real.exp (Real.pi * |w.im|) * (Real.pi * (‖w - 1‖ * ‖w - 2‖)) := by
        gcongr

/-! ### The prefactor `G_K` of a totally complex field -/

variable {K : Type} [Field K] [NumberField K]

/-- `|d_K|` as a positive real. -/
abbrev dK (K : Type) [Field K] [NumberField K] : ℝ := |(NumberField.discr K : ℝ)|

theorem dK_pos : 0 < dK K := by
  simp only [dK]
  exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)

theorem prefactor_tc [IsTotallyComplex K] (s : ℂ) :
    Hecke.dedekindPrefactor K s =
      ((dK K : ℝ) : ℂ) ^ (s / 2) * Gammaℂ s ^ InfinitePlace.nrComplexPlaces K := by
  have h0 : InfinitePlace.nrRealPlaces K = 0 :=
    NumberField.nrRealPlaces_eq_zero_iff.mpr inferInstance
  simp [Hecke.dedekindPrefactor, h0, dK]

theorem norm_Gammaℂ (s : ℂ) : ‖Gammaℂ s‖ = 2 * (2 * Real.pi) ^ (-s.re) * ‖Complex.Gamma s‖ := by
  rw [Gammaℂ_def, norm_mul, norm_mul, Complex.norm_two]
  have : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

theorem norm_prefactor [IsTotallyComplex K] (s : ℂ) :
    ‖Hecke.dedekindPrefactor K s‖ =
      dK K ^ (s.re / 2) *
        (2 * (2 * Real.pi) ^ (-s.re) * ‖Complex.Gamma s‖) ^ InfinitePlace.nrComplexPlaces K := by
  rw [prefactor_tc, norm_mul, norm_pow, norm_Gammaℂ,
    Complex.norm_cpow_eq_rpow_re_of_pos dK_pos]
  congr 2
  simp

theorem prefactor_ne_zero [IsTotallyComplex K] {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    Hecke.dedekindPrefactor K s ≠ 0 := by
  rw [prefactor_tc]
  refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast dK_pos.ne'))
  · rw [Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero hs)
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by simp [Real.pi_ne_zero]))

theorem not_nonpos_int_of_re_pos {s : ℂ} (hs : 0 < s.re) : ∀ m : ℕ, s ≠ -m := by
  intro m h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

theorem not_nonpos_int_of_im_ne {s : ℂ} (hs : s.im ≠ 0) : ∀ m : ℕ, s ≠ -m := by
  intro m h
  apply hs
  have := congrArg Complex.im h
  simpa using this

theorem differentiableAt_prefactor [IsTotallyComplex K] {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    DifferentiableAt ℂ (Hecke.dedekindPrefactor K) s := by
  have : Hecke.dedekindPrefactor K = fun s : ℂ =>
      ((dK K : ℝ) : ℂ) ^ (s / 2) * Gammaℂ s ^ InfinitePlace.nrComplexPlaces K :=
    funext prefactor_tc
  rw [this]
  refine DifferentiableAt.mul ?_ (DifferentiableAt.pow ?_ _)
  · exact (differentiableAt_id.div_const 2).const_cpow
      (Or.inl (by exact_mod_cast dK_pos.ne'))
  · rw [show Gammaℂ = fun s : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s from
      funext Gammaℂ_def]
    refine DifferentiableAt.mul ?_ (Complex.differentiableAt_Gamma s hs)
    refine DifferentiableAt.const_mul ?_ _
    exact differentiableAt_id.neg.const_cpow (Or.inl (by simp [Real.pi_ne_zero]))

theorem differentiable_prefactor_inv [IsTotallyComplex K] :
    Differentiable ℂ (fun s => (Hecke.dedekindPrefactor K s)⁻¹) := by
  have : (fun s => (Hecke.dedekindPrefactor K s)⁻¹) = fun s : ℂ =>
      (((dK K : ℝ) : ℂ) ^ (s / 2))⁻¹ * ((Gammaℂ s)⁻¹) ^ InfinitePlace.nrComplexPlaces K := by
    funext s
    rw [prefactor_tc, mul_inv, inv_pow]
  rw [this]
  refine Differentiable.mul ?_ (Differentiable.pow differentiable_Gammaℂ_inv _)
  intro s
  refine DifferentiableAt.inv ?_ ?_
  · exact (differentiableAt_id.div_const 2).const_cpow (Or.inl (by exact_mod_cast dK_pos.ne'))
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast dK_pos.ne'))

theorem ratio_eq_mul_inv (u : ℂ) :
    qsGammaRatio K u = Hecke.dedekindPrefactor K u * (Hecke.dedekindPrefactor K (1 - u))⁻¹ :=
  div_eq_mul_inv _ _

theorem differentiableAt_ratio [IsTotallyComplex K] {u : ℂ} (hu : ∀ m : ℕ, u ≠ -m) :
    DifferentiableAt ℂ (qsGammaRatio K) u := by
  have : qsGammaRatio K = fun u =>
      Hecke.dedekindPrefactor K u * (Hecke.dedekindPrefactor K (1 - u))⁻¹ :=
    funext ratio_eq_mul_inv
  rw [this]
  exact (differentiableAt_prefactor hu).mul
    ((differentiable_prefactor_inv (K := K)).differentiableAt.comp u
      (differentiableAt_const _ |>.sub differentiableAt_id))

/-- `‖R(u)‖ = 1` on the critical line. -/
theorem norm_ratio_half [IsTotallyComplex K] {u : ℂ} (hu : u.re = 1/2) :
    ‖qsGammaRatio K u‖ = 1 := by
  have hc : 1 - u = (starRingEnd ℂ) u := by
    apply Complex.ext <;> simp [hu]; norm_num
  have hpos : 0 < u.re := by rw [hu]; norm_num
  have hne : Hecke.dedekindPrefactor K u ≠ 0 := prefactor_ne_zero (not_nonpos_int_of_re_pos hpos)
  rw [qsGammaRatio, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr ?_)]
  · rw [norm_prefactor, norm_prefactor, hc, Complex.Gamma_conj, Complex.norm_conj]
    simp
  · rw [hc]
    refine prefactor_ne_zero (not_nonpos_int_of_re_pos ?_)
    simpa using hpos

theorem dK_one_le : 1 ≤ dK K := by
  simp only [dK]
  have h : (NumberField.discr K : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero K
  have : (1 : ℝ) ≤ |((NumberField.discr K : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)
  exact this

theorem one_le_nrComplexPlaces [IsTotallyComplex K] : 1 ≤ InfinitePlace.nrComplexPlaces K := by
  have h0 : InfinitePlace.nrRealPlaces K = 0 :=
    NumberField.nrRealPlaces_eq_zero_iff.mpr inferInstance
  have hrank := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

/-- The recurrence `R(v+1) = |d| (-v²/4π²)^{r₂} R(v)`. -/
theorem ratio_add_one [IsTotallyComplex K] {v : ℂ} (hv0 : v ≠ 0) (h1 : ∀ m : ℕ, -v ≠ -m)
    (h2 : ∀ m : ℕ, 1 - v ≠ -m) :
    qsGammaRatio K (v + 1) = ((dK K : ℝ) : ℂ) *
      (-v ^ 2 / (4 * (Real.pi : ℂ) ^ 2)) ^ InfinitePlace.nrComplexPlaces K * qsGammaRatio K v := by
  set r := InfinitePlace.nrComplexPlaces K
  set D : ℂ := ((dK K : ℝ) : ℂ) with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact_mod_cast dK_pos.ne'
  have hg1 : Hecke.dedekindPrefactor K (-v) ≠ 0 := prefactor_ne_zero h1
  have hg2 : Hecke.dedekindPrefactor K (1 - v) ≠ 0 := prefactor_ne_zero h2
  have hGv : Gammaℂ (v + 1) = Gammaℂ v * v / 2 / Real.pi := Gammaℂ_add_one hv0
  have hGmv : Gammaℂ (1 - v) = Gammaℂ (-v) * (-v) / 2 / Real.pi := by
    rw [show (1 : ℂ) - v = -v + 1 by ring]
    exact Gammaℂ_add_one (neg_ne_zero.mpr hv0)
  have hcp1 : D ^ ((v + 1) / 2) = D ^ (v / 2) * D ^ ((1 : ℂ) / 2) := by
    rw [← Complex.cpow_add _ _ hD0]; ring_nf
  have hcp2 : D ^ ((1 - v) / 2) = D ^ ((1 : ℂ) / 2) * D ^ ((-v) / 2) := by
    rw [← Complex.cpow_add _ _ hD0]; ring_nf
  have hhalf : D ^ ((1 : ℂ) / 2) * D ^ ((1 : ℂ) / 2) = D := by
    rw [← Complex.cpow_add _ _ hD0]; norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : Hecke.dedekindPrefactor K (v + 1) * Hecke.dedekindPrefactor K (1 - v) =
      D * (-v ^ 2 / (4 * (Real.pi : ℂ) ^ 2)) ^ r *
        (Hecke.dedekindPrefactor K v * Hecke.dedekindPrefactor K (-v)) := by
    rw [prefactor_tc, prefactor_tc, prefactor_tc, prefactor_tc, hGv, hGmv, hcp1, hcp2]
    have hX : (-v ^ 2 / (4 * (Real.pi : ℂ) ^ 2)) = (v / 2 / Real.pi) * ((-v) / 2 / Real.pi) := by
      field_simp
      ring
    rw [hX]
    calc D ^ (v / 2) * D ^ ((1 : ℂ) / 2) * (Gammaℂ v * v / 2 / Real.pi) ^ r *
          (D ^ ((1 : ℂ) / 2) * D ^ ((-v) / 2) * (Gammaℂ (-v) * (-v) / 2 / Real.pi) ^ r)
        = (D ^ ((1 : ℂ) / 2) * D ^ ((1 : ℂ) / 2)) * (D ^ (v / 2) * D ^ ((-v) / 2)) *
            ((Gammaℂ v * v / 2 / Real.pi) ^ r * (Gammaℂ (-v) * (-v) / 2 / Real.pi) ^ r) := by
          ring
      _ = D * (D ^ (v / 2) * D ^ ((-v) / 2)) *
            ((Gammaℂ v * v / 2 / Real.pi) * (Gammaℂ (-v) * (-v) / 2 / Real.pi)) ^ r := by
          rw [hhalf, mul_pow]
      _ = D * (D ^ (v / 2) * D ^ ((-v) / 2)) *
            (((v / 2 / Real.pi) * ((-v) / 2 / Real.pi)) * (Gammaℂ v * Gammaℂ (-v))) ^ r := by
          congr 2
          ring
      _ = D * ((v / 2 / Real.pi) * ((-v) / 2 / Real.pi)) ^ r *
            (D ^ (v / 2) * Gammaℂ v ^ r * (D ^ ((-v) / 2) * Gammaℂ (-v) ^ r)) := by
          rw [mul_pow, mul_pow]
          ring
  have hsplit : qsGammaRatio K (v + 1) =
      Hecke.dedekindPrefactor K (v + 1) * Hecke.dedekindPrefactor K (1 - v) /
        (Hecke.dedekindPrefactor K (-v) * Hecke.dedekindPrefactor K (1 - v)) := by
    rw [qsGammaRatio, show (1 : ℂ) - (v + 1) = -v by ring, mul_div_mul_right _ _ hg2]
  rw [hsplit, key, qsGammaRatio, mul_div_assoc,
    mul_comm (Hecke.dedekindPrefactor K v) (Hecke.dedekindPrefactor K (-v)),
    mul_div_mul_left _ _ hg1]

theorem norm_ratio_add_one [IsTotallyComplex K] {v : ℂ} (hv0 : v ≠ 0) (h1 : ∀ m : ℕ, -v ≠ -m)
    (h2 : ∀ m : ℕ, 1 - v ≠ -m) :
    ‖qsGammaRatio K (v + 1)‖ = dK K * (‖v‖ ^ 2 / (4 * Real.pi ^ 2)) ^ InfinitePlace.nrComplexPlaces K *
      ‖qsGammaRatio K v‖ := by
  rw [ratio_add_one hv0 h1 h2, norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos dK_pos]
  congr 3
  rw [norm_div, norm_neg, norm_pow, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  norm_num

theorem not_nonpos_int_of_re_not_int {s : ℂ} (hs : ∀ m : ℤ, s.re ≠ m) : ∀ m : ℕ, s ≠ -m := by
  intro m h
  apply hs (-m)
  have := congrArg Complex.re h
  simpa using this

/-- On `Re u = 3/2`: `‖R(u)‖ = |d| (‖u - 1‖²/4π²)^{r₂}`. -/
theorem norm_ratio_three_halves [IsTotallyComplex K] {u : ℂ} (hu : u.re = 3/2) :
    ‖qsGammaRatio K u‖ = dK K * (‖u - 1‖ ^ 2 / (4 * Real.pi ^ 2)) ^ InfinitePlace.nrComplexPlaces K := by
  have hv : (u - 1).re = 1/2 := by simp [hu]; norm_num
  have hv0 : u - 1 ≠ 0 := by intro h; rw [h] at hv; simp at hv
  have h1 : ∀ m : ℕ, -(u - 1) ≠ -m := by
    refine not_nonpos_int_of_re_not_int (fun m hm => ?_)
    simp [hu] at hm
    have : (2 : ℝ) * m = -1 := by linarith
    have h' : (2 * m : ℤ) = -1 := by exact_mod_cast this
    omega
  have h2 : ∀ m : ℕ, 1 - (u - 1) ≠ -m := by
    refine not_nonpos_int_of_re_not_int (fun m hm => ?_)
    simp [hu] at hm
    have : (2 : ℝ) * m = 1 := by linarith
    have h' : (2 * m : ℤ) = 1 := by exact_mod_cast this
    omega
  have := norm_ratio_add_one (K := K) hv0 h1 h2
  rw [show u - 1 + 1 = u by ring, norm_ratio_half hv, mul_one] at this
  exact this

/-- `‖G_K(w)⁻¹‖ = |d|^{-Re w/2} ((2π)^{Re w}/2 · ‖Γ(w)⁻¹‖)^{r₂}`. -/
theorem norm_prefactor_inv [IsTotallyComplex K] (w : ℂ) :
    ‖(Hecke.dedekindPrefactor K w)⁻¹‖ =
      (dK K ^ (w.re / 2))⁻¹ *
        ((2 * Real.pi) ^ w.re / 2 * ‖(Complex.Gamma w)⁻¹‖) ^ InfinitePlace.nrComplexPlaces K := by
  rw [norm_inv, norm_prefactor, mul_inv, ← inv_pow, norm_inv]
  congr 2
  rw [mul_inv, mul_inv, Real.rpow_neg (by positivity), inv_inv]
  ring

/-- Crude growth of `R(u)` on `1/2 ≤ Re u ≤ 3/2`. -/
theorem exists_ratio_growth [IsTotallyComplex K] :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, 1/2 ≤ u.re → u.re ≤ 3/2 → 1 ≤ |u.im| →
      ‖qsGammaRatio K u‖ ≤
        C * Real.exp ((InfinitePlace.nrComplexPlaces K * Real.pi) * |u.im|) := by
  obtain ⟨M, hM0, hM⟩ := exists_Gamma_bound
  obtain ⟨M', hM'0, hM'⟩ := exists_norm_inv_Gamma_le
  set r := InfinitePlace.nrComplexPlaces K
  refine ⟨dK K ^ ((3:ℝ)/4) * (2 * M) ^ r * (dK K ^ ((1:ℝ)/4) * (2 * Real.pi * M') ^ r),
    by have := dK_pos (K := K); positivity, fun u h1 h2 ht => ?_⟩
  have hd1 := dK_one_le (K := K)
  have hupos : 0 < u.re := by linarith
  rw [ratio_eq_mul_inv, norm_mul]
  have hA : ‖Hecke.dedekindPrefactor K u‖ ≤ dK K ^ ((3:ℝ)/4) * (2 * M) ^ r := by
    rw [norm_prefactor]
    have e1 : dK K ^ (u.re / 2) ≤ dK K ^ ((3:ℝ)/4) :=
      Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
    have hle1 : (2 * Real.pi) ^ (-u.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
    have hΓ : ‖Complex.Gamma u‖ ≤ M :=
      (norm_Gamma_le_Gamma_re hupos).trans (hM _ ⟨h1, by linarith⟩)
    have e2 : 2 * (2 * Real.pi) ^ (-u.re) * ‖Complex.Gamma u‖ ≤ 2 * M := by
      have h0 : 0 ≤ (2 * Real.pi) ^ (-u.re) := by positivity
      nlinarith [norm_nonneg (Complex.Gamma u)]
    have e3 : (2 * (2 * Real.pi) ^ (-u.re) * ‖Complex.Gamma u‖) ^ r ≤ (2 * M) ^ r :=
      pow_le_pow_left₀ (by positivity) e2 r
    exact mul_le_mul e1 e3 (by positivity) (by positivity)
  have hB : ‖(Hecke.dedekindPrefactor K (1 - u))⁻¹‖ ≤
      dK K ^ ((1:ℝ)/4) * (2 * Real.pi * M') ^ r * Real.exp ((r * Real.pi) * |u.im|) := by
    rw [norm_prefactor_inv]
    have hw1 : -1 ≤ (1 - u).re := by simp; linarith
    have hw2 : (1 - u).re ≤ 5/2 := by simp; linarith
    have hwt : 1 ≤ |(1 - u).im| := by simpa using ht
    have hΓ := hM' (1 - u) hw1 hw2 hwt
    have him : |(1 - u).im| = |u.im| := by simp
    rw [him] at hΓ
    have hd : (dK K ^ ((1 - u).re / 2))⁻¹ ≤ dK K ^ ((1:ℝ)/4) := by
      rw [← Real.rpow_neg (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le hd1 (by simp; linarith)
    have h2pi : (2 * Real.pi) ^ (1 - u).re / 2 ≤ 2 * Real.pi := by
      have : (2 * Real.pi) ^ (1 - u).re ≤ (2 * Real.pi) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by simp; linarith)
      rw [Real.rpow_one] at this
      linarith [Real.pi_pos]
    calc (dK K ^ ((1 - u).re / 2))⁻¹ * ((2 * Real.pi) ^ (1 - u).re / 2 * ‖(Complex.Gamma (1 - u))⁻¹‖) ^ r
        ≤ dK K ^ ((1:ℝ)/4) * (2 * Real.pi * (M' * Real.exp (Real.pi * |u.im|))) ^ r := by
          gcongr
      _ = dK K ^ ((1:ℝ)/4) * (2 * Real.pi * M') ^ r * Real.exp ((r * Real.pi) * |u.im|) := by
          rw [show 2 * Real.pi * (M' * Real.exp (Real.pi * |u.im|)) =
              (2 * Real.pi * M') * Real.exp (Real.pi * |u.im|) by ring, mul_pow,
            ← Real.exp_nat_mul]
          ring_nf
  calc ‖Hecke.dedekindPrefactor K u‖ * ‖(Hecke.dedekindPrefactor K (1 - u))⁻¹‖
      ≤ (dK K ^ ((3:ℝ)/4) * (2 * M) ^ r) *
          (dK K ^ ((1:ℝ)/4) * (2 * Real.pi * M') ^ r * Real.exp ((r * Real.pi) * |u.im|)) :=
        mul_le_mul hA hB (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Polynomial bound for `R(u)` on `1/2 ≤ Re u ≤ 3/2` (Phragmén–Lindelöf). -/
theorem exists_ratio_poly [IsTotallyComplex K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, 1/2 ≤ u.re → u.re ≤ 3/2 →
      ‖qsGammaRatio K u‖ ≤ C * (1 + |u.im|) ^ (2 * InfinitePlace.nrComplexPlaces K) := by
  obtain ⟨C₀, hC₀, hgr⟩ := exists_ratio_growth (K := K)
  set r := InfinitePlace.nrComplexPlaces K
  have hd1 := dK_one_le (K := K)
  have hbd := pl_poly_strip (f := qsGammaRatio K) (a := 1/2) (b := 3/2) (by norm_num)
    (fun s h1 h2 => differentiableAt_ratio (not_nonpos_int_of_re_pos (by linarith)))
    (r * Real.pi) C₀ hgr (2 * r) (dK K) ?_ ?_
  · refine ⟨dK K * 2 ^ (2 * r) * (3/2 - 1/2 + 2) ^ (2 * r), by positivity, fun u h1 h2 => ?_⟩
    exact hbd u h1 h2
  · intro s hs
    rw [norm_ratio_half hs]
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ dK K * (1 + |s.im|) ^ (2 * r) := by
        gcongr
        exact one_le_pow₀ (by linarith [abs_nonneg s.im])
  · intro s hs
    rw [norm_ratio_three_halves hs]
    gcongr
    have hn : ‖s - 1‖ ^ 2 = 1/4 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [hs]
      ring
    rw [pow_mul, hn]
    gcongr
    have hpi : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    rw [div_le_iff₀ (by positivity)]
    have : 1/4 + s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by
      nlinarith [abs_nonneg s.im, sq_abs s.im]
    nlinarith [sq_nonneg (1 + |s.im|)]

/-- Polynomial bound for `R(w)` on `-1/2 ≤ Re w ≤ 3/2` away from the real axis. -/
theorem exists_ratio_poly_wide [IsTotallyComplex K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, -1/2 ≤ w.re → w.re ≤ 3/2 → 1/2 ≤ |w.im| →
      ‖qsGammaRatio K w‖ ≤ C * (1 + |w.im|) ^ (2 * InfinitePlace.nrComplexPlaces K) := by
  obtain ⟨C, hC, hpoly⟩ := exists_ratio_poly (K := K)
  set r := InfinitePlace.nrComplexPlaces K
  have hd1 := dK_one_le (K := K)
  refine ⟨C * (16 * Real.pi ^ 2) ^ r, by positivity, fun w h1 h2 ht => ?_⟩
  by_cases hw : 1/2 ≤ w.re
  · calc ‖qsGammaRatio K w‖ ≤ C * (1 + |w.im|) ^ (2 * r) := hpoly w hw h2
      _ ≤ C * (16 * Real.pi ^ 2) ^ r * (1 + |w.im|) ^ (2 * r) := by
        have : 1 ≤ (16 * Real.pi ^ 2) ^ r := one_le_pow₀ (by nlinarith [Real.pi_gt_three])
        nlinarith [mul_nonneg hC (pow_nonneg (by linarith [abs_nonneg w.im] : (0:ℝ) ≤ 1 + |w.im|) (2 * r))]
  · push Not at hw
    have hwim : w.im ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
    have hw0 : w ≠ 0 := fun h => hwim (by simp [h])
    have hrec := norm_ratio_add_one (K := K) hw0
      (not_nonpos_int_of_im_ne (by simpa using hwim))
      (not_nonpos_int_of_im_ne (by simpa using hwim))
    have hb := hpoly (w + 1) (by simp; linarith) (by simp; linarith)
    rw [hrec, show (w + 1).im = w.im by simp] at hb
    have hwn : 1/4 ≤ ‖w‖ ^ 2 := by
      have := Complex.abs_im_le_norm w
      nlinarith [abs_nonneg w.im]
    have hfac : 0 < dK K * (‖w‖ ^ 2 / (4 * Real.pi ^ 2)) ^ r := by
      have : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      positivity
    have hinv : 1 ≤ dK K * (‖w‖ ^ 2 / (4 * Real.pi ^ 2)) ^ r * (16 * Real.pi ^ 2) ^ r := by
      rw [mul_assoc, ← mul_pow]
      have : 1 ≤ ‖w‖ ^ 2 / (4 * Real.pi ^ 2) * (16 * Real.pi ^ 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [Real.pi_pos]
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ dK K * (‖w‖ ^ 2 / (4 * Real.pi ^ 2) * (16 * Real.pi ^ 2)) ^ r :=
          mul_le_mul hd1 (one_le_pow₀ this) zero_le_one (by linarith)
    have hX : 0 ≤ C * (1 + |w.im|) ^ (2 * r) := by positivity
    calc ‖qsGammaRatio K w‖ ≤ ‖qsGammaRatio K w‖ *
          (dK K * (‖w‖ ^ 2 / (4 * Real.pi ^ 2)) ^ r * (16 * Real.pi ^ 2) ^ r) :=
        le_mul_of_one_le_right (norm_nonneg _) hinv
      _ = (dK K * (‖w‖ ^ 2 / (4 * Real.pi ^ 2)) ^ r * ‖qsGammaRatio K w‖) *
          (16 * Real.pi ^ 2) ^ r := by ring
      _ ≤ C * (1 + |w.im|) ^ (2 * r) * (16 * Real.pi ^ 2) ^ r :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ = C * (16 * Real.pi ^ 2) ^ r * (1 + |w.im|) ^ (2 * r) := by ring

end ArtinPrimitiveRoots.A2.QSP2
