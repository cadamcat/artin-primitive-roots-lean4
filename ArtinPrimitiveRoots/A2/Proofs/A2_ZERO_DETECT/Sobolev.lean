import Mathlib

/-!
# A2-ZERO-DETECT: elementary one-dimensional Sobolev control

For a `C¹` function `f : ℝ → ℂ` and a point `x` of a compact interval `[a, b]`,
`‖f x‖² ≤ (b - a)⁻¹ ∫ ‖f‖² + ∫ (‖f‖² + ‖f'‖²)`, proved by the fundamental theorem of calculus
applied to `‖f‖²` and averaging over the base point. The family form sums this bound over a
finite family evaluated at arbitrary points of the interval.
-/

set_option autoImplicit false

open MeasureTheory intervalIntegral Set

noncomputable section

namespace ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect

/-- Pointwise Sobolev control of `‖f x‖²` on a compact interval. -/
theorem sobolev_sq_le (f f' : ℝ → ℂ) {a b : ℝ} (hab : a < b)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x‖ ^ 2 ≤ (b - a)⁻¹ * (∫ t in a..b, ‖f t‖ ^ 2) +
      ∫ t in a..b, (‖f t‖ ^ 2 + ‖f' t‖ ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  let g : ℝ → ℝ := fun t => ‖f t‖ ^ 2
  let g' : ℝ → ℝ := fun t => 2 * inner ℝ (f t) (f' t)
  let h : ℝ → ℝ := fun t => ‖f t‖ ^ 2 + ‖f' t‖ ^ 2
  have hgd : ∀ t, HasDerivAt g (g' t) t := fun t => (hf t).norm_sq
  have hgc : Continuous g := by fun_prop
  have hg'c : Continuous g' := by
    have : Continuous fun t => inner ℝ (f t) (f' t) := hfc.inner hf'
    exact continuous_const.mul this
  have hhc : Continuous h := by fun_prop
  have hh0 : ∀ t, 0 ≤ h t := fun t => by positivity
  have hg'le : ∀ t, |g' t| ≤ h t := by
    intro t
    have h1 : |inner ℝ (f t) (f' t)| ≤ ‖f t‖ * ‖f' t‖ := abs_real_inner_le_norm _ _
    have h2 : 2 * (‖f t‖ * ‖f' t‖) ≤ ‖f t‖ ^ 2 + ‖f' t‖ ^ 2 := by
      nlinarith [sq_nonneg (‖f t‖ - ‖f' t‖)]
    have h3 : |g' t| = 2 * |inner ℝ (f t) (f' t)| := by
      simp only [g', abs_mul, abs_two]
    rw [h3]
    change _ ≤ ‖f t‖ ^ 2 + ‖f' t‖ ^ 2
    linarith
  set H : ℝ := ∫ t in a..b, h t with hH
  have hstep : ∀ y ∈ Icc a b, g x ≤ g y + H := by
    intro y hy
    have hftc : ∫ t in y..x, g' t = g x - g y :=
      integral_eq_sub_of_hasDerivAt (fun t _ => hgd t) (hg'c.intervalIntegrable _ _)
    rcases le_total y x with hyx | hxy
    · have h1 : ∫ t in y..x, g' t ≤ ∫ t in y..x, h t :=
        integral_mono_on hyx (hg'c.intervalIntegrable _ _) (hhc.intervalIntegrable _ _)
          (fun t _ => (le_abs_self _).trans (hg'le t))
      have h2 : ∫ t in y..x, h t ≤ H :=
        integral_mono_interval hy.1 hyx hx.2 (Filter.Eventually.of_forall hh0)
          (hhc.intervalIntegrable _ _)
      linarith
    · have hftc' : ∫ t in x..y, -g' t = g x - g y := by
        rw [intervalIntegral.integral_neg, integral_symm, hftc]
        ring
      have h1 : ∫ t in x..y, -g' t ≤ ∫ t in x..y, h t :=
        integral_mono_on hxy (hg'c.neg.intervalIntegrable _ _) (hhc.intervalIntegrable _ _)
          (fun t _ => (neg_le_abs _).trans (hg'le t))
      have h2 : ∫ t in x..y, h t ≤ H :=
        integral_mono_interval hx.1 hxy hy.2 (Filter.Eventually.of_forall hh0)
          (hhc.intervalIntegrable _ _)
      linarith
  have hint : ∫ _ in a..b, g x ≤ ∫ y in a..b, (g y + H) :=
    integral_mono_on hab.le intervalIntegrable_const
      ((hgc.add continuous_const).intervalIntegrable _ _) hstep
  rw [intervalIntegral.integral_const, integral_add (hgc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const] at hint
  simp only [smul_eq_mul] at hint
  have hba : 0 < b - a := sub_pos.2 hab
  have hfinal : g x ≤ (b - a)⁻¹ * (∫ t in a..b, g t) + H := by
    calc g x = (b - a)⁻¹ * ((b - a) * g x) := by field_simp
      _ ≤ (b - a)⁻¹ * ((∫ t in a..b, g t) + (b - a) * H) := by gcongr
      _ = (b - a)⁻¹ * (∫ t in a..b, g t) + H := by field_simp
  exact hfinal

/-- Family form: a finite sum of `‖f i (x i)‖²` at arbitrary points of `[a, b]` is controlled by
uniform bounds for the sums of `‖f i t‖²` and `‖f' i t‖²` on that interval. -/
theorem family_sobolev_sum_le {ι : Type*} (X : Finset ι) (f f' : ι → ℝ → ℂ) {a b : ℝ}
    (hab : a < b) (hf : ∀ i t, HasDerivAt (f i) (f' i t) t) (hf' : ∀ i, Continuous (f' i))
    (x : ι → ℝ) (hx : ∀ i ∈ X, x i ∈ Icc a b) {A A' : ℝ}
    (hA : ∀ t ∈ Icc a b, ∑ i ∈ X, ‖f i t‖ ^ 2 ≤ A)
    (hA' : ∀ t ∈ Icc a b, ∑ i ∈ X, ‖f' i t‖ ^ 2 ≤ A') :
    ∑ i ∈ X, ‖f i (x i)‖ ^ 2 ≤ (1 + (b - a)) * A + (b - a) * A' := by
  have hfc : ∀ i, Continuous (f i) := fun i =>
    continuous_iff_continuousAt.2 fun t => (hf i t).continuousAt
  have hba : 0 < b - a := sub_pos.2 hab
  have hpt : ∀ i ∈ X, ‖f i (x i)‖ ^ 2 ≤ (b - a)⁻¹ * (∫ t in a..b, ‖f i t‖ ^ 2) +
      ∫ t in a..b, (‖f i t‖ ^ 2 + ‖f' i t‖ ^ 2) := fun i hi =>
    sobolev_sq_le (f i) (f' i) hab (hf i) (hf' i) (hx i hi)
  have hgi : ∀ i ∈ X, IntervalIntegrable (fun t => ‖f i t‖ ^ 2) volume a b := fun i _ =>
    (by fun_prop : Continuous fun t => ‖f i t‖ ^ 2).intervalIntegrable _ _
  have hg'i : ∀ i ∈ X, IntervalIntegrable (fun t => ‖f' i t‖ ^ 2) volume a b := fun i _ =>
    ((hf' i).norm.pow 2).intervalIntegrable _ _
  have hsum1 : ∫ t in a..b, ∑ i ∈ X, ‖f i t‖ ^ 2 ≤ (b - a) * A := by
    have hc : Continuous fun t => ∑ i ∈ X, ‖f i t‖ ^ 2 :=
      continuous_finsetSum _ fun i _ => ((hfc i).norm.pow 2)
    have := integral_mono_on hab.le (hc.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume)) hA
    simpa [intervalIntegral.integral_const, smul_eq_mul] using this
  have hsum2 : ∫ t in a..b, ∑ i ∈ X, ‖f' i t‖ ^ 2 ≤ (b - a) * A' := by
    have hc : Continuous fun t => ∑ i ∈ X, ‖f' i t‖ ^ 2 :=
      continuous_finsetSum _ fun i _ => ((hf' i).norm.pow 2)
    have := integral_mono_on hab.le (hc.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume)) hA'
    simpa [intervalIntegral.integral_const, smul_eq_mul] using this
  have hsplit : ∀ i ∈ X, ∫ t in a..b, (‖f i t‖ ^ 2 + ‖f' i t‖ ^ 2) =
      (∫ t in a..b, ‖f i t‖ ^ 2) + ∫ t in a..b, ‖f' i t‖ ^ 2 := fun i hi =>
    integral_add (hgi i hi) (hg'i i hi)
  calc ∑ i ∈ X, ‖f i (x i)‖ ^ 2
      ≤ ∑ i ∈ X, ((b - a)⁻¹ * (∫ t in a..b, ‖f i t‖ ^ 2) +
          ((∫ t in a..b, ‖f i t‖ ^ 2) + ∫ t in a..b, ‖f' i t‖ ^ 2)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← hsplit i hi]
        exact hpt i hi
    _ = (b - a)⁻¹ * (∫ t in a..b, ∑ i ∈ X, ‖f i t‖ ^ 2) +
          ((∫ t in a..b, ∑ i ∈ X, ‖f i t‖ ^ 2) + ∫ t in a..b, ∑ i ∈ X, ‖f' i t‖ ^ 2) := by
        rw [integral_finsetSum hgi, integral_finsetSum hg'i, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (b - a)⁻¹ * ((b - a) * A) + ((b - a) * A + (b - a) * A') := by
        gcongr
    _ = (1 + (b - a)) * A + (b - a) * A' := by
        field_simp
        ring

end ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect
