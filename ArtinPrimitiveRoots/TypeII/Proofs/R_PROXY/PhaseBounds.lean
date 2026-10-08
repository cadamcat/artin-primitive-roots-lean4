import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.TruncatedSource
import Mathlib.Algebra.Order.Chebyshev

/-!
Finite Abel weighting tools for the reciprocal-log Type II source.
-/

namespace ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY

open ArtinPrimitiveRoots.TypeII
open Classical

/-- A complex sum inherits the Abel bound for positive antitone weights from
uniform bounds on the unweighted prefix sums. -/
theorem norm_sum_range_weighted_le_of_prefix
    (a : ℕ → ℂ) (w : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hprefix : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, a i‖ ≤ B)
    (hwNonneg : ∀ i, 0 ≤ w i)
    (hwAnti : AntitoneOn w (Set.Iio n)) :
    ‖∑ i ∈ Finset.range n, (w i : ℂ) * a i‖ ≤ 2 * B * w 0 := by
  have hRePrefix : ∀ k ≤ n,
      |∑ i ∈ Finset.range k, (a i).re| ≤ B := by
    intro k hk
    have hsum : ∑ i ∈ Finset.range k, (a i).re =
        (∑ i ∈ Finset.range k, a i).re := by
      simp only [Complex.re_sum]
    rw [hsum]
    exact (Complex.abs_re_le_norm _).trans (hprefix k hk)
  have hImPrefix : ∀ k ≤ n,
      |∑ i ∈ Finset.range k, (a i).im| ≤ B := by
    intro k hk
    have hsum : ∑ i ∈ Finset.range k, (a i).im =
        (∑ i ∈ Finset.range k, a i).im := by
      simp only [Complex.im_sum]
    rw [hsum]
    exact (Complex.abs_im_le_norm _).trans (hprefix k hk)
  have hReAbel := Finset.abs_sum_mul_le_mul_of_abs_sum_range_le
    (f := fun i => (a i).re) (g := w) (n := n) hRePrefix hwNonneg hwAnti
  have hImAbel := Finset.abs_sum_mul_le_mul_of_abs_sum_range_le
    (f := fun i => (a i).im) (g := w) (n := n) hImPrefix hwNonneg hwAnti
  have hReEq : (∑ i ∈ Finset.range n, (w i : ℂ) * a i).re =
      ∑ i ∈ Finset.range n, (a i).re * w i := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Complex.mul_re]
    ring
  have hImEq : (∑ i ∈ Finset.range n, (w i : ℂ) * a i).im =
      ∑ i ∈ Finset.range n, (a i).im * w i := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Complex.mul_im]
    ring
  have hRe : |(∑ i ∈ Finset.range n, (w i : ℂ) * a i).re| ≤ B * w 0 := by
    rw [hReEq]
    exact hReAbel
  have hIm : |(∑ i ∈ Finset.range n, (w i : ℂ) * a i).im| ≤ B * w 0 := by
    rw [hImEq]
    exact hImAbel
  calc
    ‖∑ i ∈ Finset.range n, (w i : ℂ) * a i‖ ≤
        |(∑ i ∈ Finset.range n, (w i : ℂ) * a i).re| +
          |(∑ i ∈ Finset.range n, (w i : ℂ) * a i).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ B * w 0 + B * w 0 := add_le_add hRe hIm
    _ = 2 * B * w 0 := by ring

/-- One residue-class phase sum with the reciprocal logarithm attached. -/
noncomputable def reciprocalLogResiduePhaseSum
    (d q : ℕ) (a : ZMod q) (u l r : ℝ) : ℂ :=
  ∑ h ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (h : ℕ) =>
      l ≤ (h : ℝ) ∧ (h : ℝ) ≤ r ∧ (h : ZMod q) = a),
    Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
      Real.log ((d * h : ℕ) : ℝ)

/-- Moderate-phase residue sums after Abel weighting by `1/log(d*h)`. -/
theorem moderate_reciprocal_log_residue_bound
    (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ C₀ cδ x₀ : ℝ, 0 < C₀ ∧ 0 < cδ ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        let T := Real.exp (L / Real.log L ^ 2)
        ∀ N M : ℝ, Real.rpow x δ ≤ N → 1 < M →
          1 ≤ Real.log M → ∀ d : ℕ, 0 < d →
            M ≤ (d : ℝ) * N →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ a : ZMod q, ∀ u : ℝ, 1 ≤ |u| → |u| ≤ T →
                ∀ l r : ℝ, N ≤ l → l ≤ r → r ≤ 2 * N →
                  ‖reciprocalLogResiduePhaseSum d q a u l r‖ ≤
                    4 * C₀ * (N / (q : ℝ)) / Real.log M *
                      (|u|⁻¹ + Real.rpow x (-cδ)) := by
  sorry

/-- High-phase residue sums after Abel weighting by `1/log(d*h)`. -/
theorem high_reciprocal_log_residue_bound :
    ∃ C₃p : ℝ, 0 < C₃p ∧
      ∀ C : ℝ, 0 < C →
        ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            let L := Real.log x
            let T := Real.log L
            ∀ N M : ℝ, Real.exp (L / T ^ 2) ≤ N →
              N ≤ 2 * Real.rpow x 5 → 1 < M →
              1 ≤ Real.log M → ∀ d : ℕ, 0 < d →
                M ≤ (d : ℝ) * N →
                ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
                  ∀ a : ZMod q, ∀ u : ℝ,
                    Real.exp (L / (2 * T ^ 2)) ≤ |u| →
                    |u| ≤ 4 * Real.rpow x 3 →
                      ∀ l r : ℝ, N ≤ l → l ≤ r → r ≤ 2 * N →
                        ‖reciprocalLogResiduePhaseSum d q a u l r‖ ≤
                          4 * C₀ * (N / (q : ℝ)) / Real.log M *
                            Real.exp (-L / Real.rpow T C₃p) := by
  sorry

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
