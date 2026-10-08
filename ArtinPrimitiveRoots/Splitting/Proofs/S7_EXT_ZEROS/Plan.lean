import ArtinPrimitiveRoots.Splitting.Defs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.Jensen
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.Growth
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.GammaRatio
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.Strip
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.GammaGrowth
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.DeligneGrowth
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.XiGrowth
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.DeligneRatio
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.XiBoundary
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.XiSphere

set_option autoImplicit false
open scoped NumberField BigOperators
open Classical ArtinPrimitiveRoots.Splitting

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- Removing the nonvanishing prefactor preserves orders in the critical strip. -/
theorem sharp_xi_order (K : Type*) [Field K] [NumberField K] {z : ℂ}
    (hz : 0 < z.re) (hz1 : z.re < 1) :
    analyticOrderNatAt (dedekindZetaSharp K) z = analyticOrderNatAt (dedekindXi K) z := by
  let d : ℝ := absoluteDiscriminant K
  let r1 : ℕ := NumberField.InfinitePlace.nrRealPlaces K
  let r2 : ℕ := NumberField.InfinitePlace.nrComplexPlaces K
  let F : ℂ → ℂ := fun s => (d : ℂ) ^ (-(s / 2)) *
    ((Complex.Gammaℝ s)⁻¹) ^ r1 * ((Complex.Gammaℂ s)⁻¹) ^ r2
  have hd : (d : ℂ) ≠ 0 := by
    simp only [d, absoluteDiscriminant, Complex.ofReal_ne_zero, abs_ne_zero,
      Int.cast_ne_zero]
    exact NumberField.discr_ne_zero K
  have hD : Differentiable ℂ (fun s : ℂ => (d : ℂ) ^ (-(s / 2))) :=
    (differentiable_id.div_const (2 : ℂ)).neg.const_cpow (Or.inl hd)
  have hF : Differentiable ℂ F :=
    (hD.mul (Complex.differentiable_Gammaℝ_inv.pow r1)).mul
      (Complex.differentiable_Gammaℂ_inv.pow r2)
  have hFeq (s : ℂ) : F s = (ArtinPrimitiveRoots.Hecke.dedekindPrefactor K s)⁻¹ := by
    simp only [F, d, r1, r2, absoluteDiscriminant,
      ArtinPrimitiveRoots.Hecke.dedekindPrefactor, Complex.cpow_neg,
      mul_inv, inv_pow, mul_assoc]
  have hR : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hz
  have hC : Complex.Gammaℂ z ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hz)
    simp [Real.pi_ne_zero]
  have hFz : F z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hd))
      (pow_ne_zero _ (inv_ne_zero hR))) (pow_ne_zero _ (inv_ne_zero hC))
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hz1ne : z - 1 ≠ 0 := by
    intro h
    have hz1eq : z = 1 := sub_eq_zero.mp h
    simp [hz1eq] at hz1
  have hpz : z * (z - 1) ≠ 0 := mul_ne_zero hz0 hz1ne
  let Q : ℂ → ℂ := fun s => F s / (s * (s - 1))
  have hp : AnalyticAt ℂ (fun s : ℂ => s * (s - 1)) z := by fun_prop
  have hQ : AnalyticAt ℂ Q z := (hF.analyticAt z).div hp hpz
  have hQz : Q z ≠ 0 := div_ne_zero hFz hpz
  have hsharp : dedekindZetaSharp K = (dedekindXi K) * Q := by
    funext s
    simp only [dedekindZetaSharp, Pi.mul_apply, Q, hFeq, div_eq_mul_inv, mul_inv]
    ring
  have hXi : Differentiable ℂ (dedekindXi K) :=
    (Classical.choose_spec (ArtinPrimitiveRoots.Hecke.dedekind_completed K)).1
  have hQorder : analyticOrderAt Q z = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hQz)
  have horder : analyticOrderAt (dedekindZetaSharp K) z =
      analyticOrderAt (dedekindXi K) z := by
    rw [hsharp, analyticOrderAt_mul (hXi.analyticAt z) hQ, hQorder, add_zero]
  exact congrArg ENat.toNat horder

/-- Uniform translated Jensen estimate for the entire completed function. -/
theorem xi_window_count
    (hdigamma : ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, 1 ≤ u.re → u.re ≤ 10 →
      ‖deriv Complex.Gamma u / Complex.Gamma u‖ ≤ C * Real.log (|u.im| + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (T : ℝ),
      Summable (fun z : ℂ => if z ∈ nontrivialZeros K ∧ T ≤ z.im ∧ z.im < T + 1 then
        (analyticOrderNatAt (dedekindXi K) z : ℝ) else 0) ∧
      (∑' z : ℂ, if z ∈ nontrivialZeros K ∧ T ≤ z.im ∧ z.im < T + 1 then
        (analyticOrderNatAt (dedekindXi K) z : ℝ) else 0) ≤ C *
        (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K * Real.log (2 + |T|)) := by
  classical
  obtain ⟨C, hC, hbound⟩ := xi_normalized_sphere_bound hdigamma
  have hlog : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨C / Real.log (4 / 3), div_pos hC hlog, ?_⟩
  intro K _ _ T
  let c : ℂ := (2 : ℂ) + (T + 1 / 2) * Complex.I
  let W : ℝ := Real.log (absoluteDiscriminant K) +
    (Module.finrank ℚ K : ℝ) * Real.log (2 + |T|)
  let U : Set ℂ := {z | z ∈ nontrivialZeros K ∧ T ≤ z.im ∧ z.im < T + 1}
  let G : ℂ → ℂ := fun z => dedekindXi K z / dedekindXi K c
  obtain ⟨hc, hsphere⟩ := hbound K T
  have hXi : Differentiable ℂ (dedekindXi K) :=
    (Classical.choose_spec (ArtinPrimitiveRoots.Hecke.dedekind_completed K)).1
  have hGa : AnalyticOnNhd ℂ G (Metric.closedBall c 4) := by
    intro z _
    exact (hXi.div_const (dedekindXi K c)).analyticAt z
  have hGc : G c = 1 := div_self hc
  have hd1 : 1 ≤ absoluteDiscriminant K := by
    unfold absoluteDiscriminant
    have hne := NumberField.discr_ne_zero K
    by_cases hpos : 0 ≤ NumberField.discr K
    · rw [abs_of_nonneg (show (0 : ℝ) ≤ (NumberField.discr K : ℝ) by
        exact_mod_cast hpos)]
      have hh : (1 : ℤ) ≤ NumberField.discr K := by omega
      exact_mod_cast hh
    · rw [abs_of_neg (show (NumberField.discr K : ℝ) < 0 by
        exact_mod_cast (lt_of_not_ge hpos))]
      have hh : (1 : ℤ) ≤ -NumberField.discr K := by omega
      exact_mod_cast hh
  have hW : 0 ≤ W := add_nonneg (Real.log_nonneg hd1)
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg T])))
  have hM : 1 ≤ Real.exp (C * W) := Real.one_le_exp_iff.mpr (mul_nonneg hC.le hW)
  have hcre : c.re = 2 := by simp [c]
  have hcim : c.im = T + 1 / 2 := by simp [c]
  have hU : U ⊆ Metric.closedBall c 3 := by
    intro z hz
    change z ∈ nontrivialZeros K ∧ T ≤ z.im ∧ z.im < T + 1 at hz
    have hre : |(z - c).re| ≤ 2 := by
      rw [Complex.sub_re, hcre, abs_of_nonpos (by linarith [hz.1.2.1])]
      linarith [hz.1.1]
    have him : |(z - c).im| ≤ 1 / 2 := by
      rw [Complex.sub_im, hcim, abs_le]
      exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    calc
      ‖z - c‖ ≤ |(z - c).re| + |(z - c).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 2 + 1 / 2 := add_le_add hre him
      _ ≤ 3 := by norm_num
  have horder (z : ℂ) :
      analyticOrderNatAt G z = analyticOrderNatAt (dedekindXi K) z := by
    have hconst : analyticOrderAt (fun _ : ℂ => (dedekindXi K c)⁻¹) z = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (inv_ne_zero hc))
    have hh : analyticOrderAt G z = analyticOrderAt (dedekindXi K) z := by
      calc
        analyticOrderAt G z =
            analyticOrderAt ((dedekindXi K) * (fun _ : ℂ => (dedekindXi K c)⁻¹)) z := by
          congr 1
        _ = analyticOrderAt (dedekindXi K) z +
            analyticOrderAt (fun _ : ℂ => (dedekindXi K c)⁻¹) z :=
          analyticOrderAt_mul (hXi.analyticAt z) analyticAt_const
        _ = analyticOrderAt (dedekindXi K) z := by rw [hconst, add_zero]
    exact congrArg ENat.toNat hh
  obtain ⟨hsum, hj⟩ := jensen_multiplicity_count
    (G := G) (c := c) (r := 3) (R := 4) (M := Real.exp (C * W)) (U := U)
    (by norm_num) (by norm_num) hM hGa
    (by rw [hGc]; exact one_ne_zero)
    (by intro z hz; exact hsphere z hz) hU
  simp only [horder] at hsum hj
  refine ⟨hsum, ?_⟩
  calc
    (∑' z : ℂ, if z ∈ nontrivialZeros K ∧ T ≤ z.im ∧ z.im < T + 1 then
        (analyticOrderNatAt (dedekindXi K) z : ℝ) else 0) ≤
        Real.log (Real.exp (C * W) / ‖G c‖) / Real.log (4 / 3) := hj
    _ = (C / Real.log (4 / 3)) * W := by rw [hGc, norm_one, div_one, Real.log_exp]; ring

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
