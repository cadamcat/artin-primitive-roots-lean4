import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».PoleIntegrals
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Basic

set_option autoImplicit false

open scoped Interval BigOperators
open MeasureTheory intervalIntegral

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

/-- Subtracting finitely many interior principal parts reduces a rectangle integral to Cauchy. -/
theorem rectangle_finite_residues (H G : ℂ → ℂ) (S : Finset ℂ)
    (coeff : ℂ → ℂ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hS : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    (hG : AnalyticOnNhd ℂ G
      {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ c ≤ s.im ∧ s.im ≤ d})
    (hEq : ∀ s : ℂ, s ∉ S → G s = H s - ∑ p ∈ S, coeff p / (s - p)) :
    (∫ t : ℝ in a..b, H ((t : ℂ) + (c : ℂ) * Complex.I)) -
      (∫ t : ℝ in a..b, H ((t : ℂ) + (d : ℂ) * Complex.I)) +
      Complex.I * (∫ t : ℝ in c..d, H ((b : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t : ℝ in c..d, H ((a : ℂ) + (t : ℂ) * Complex.I)) =
      2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ S, coeff p := by
  classical
  let U : Set ℂ := {s | a ≤ s.re ∧ s.re ≤ b ∧ c ≤ s.im ∧ s.im ≤ d}
  have hline (e f : ℝ) (path : ℝ → ℂ) (hpath : Continuous path)
      (hU : Set.MapsTo path (Set.uIcc e f) U)
      (havoid : ∀ t : ℝ, path t ∉ S) :
      (∫ t : ℝ in e..f, H (path t)) =
        (∫ t : ℝ in e..f, G (path t)) +
          ∑ p ∈ S, ∫ t : ℝ in e..f, coeff p / (path t - p) := by
    have hGi : IntervalIntegrable (fun t => G (path t)) volume e f :=
      (hG.continuousOn.comp' hpath.continuousOn hU).intervalIntegrable
    have hPi : ∀ p ∈ S, IntervalIntegrable
        (fun t => coeff p / (path t - p)) volume e f := by
      intro p hp
      apply Continuous.intervalIntegrable
      refine continuous_const.div (hpath.sub continuous_const) ?_
      intro t ht
      exact havoid t ((sub_eq_zero.mp ht).symm ▸ hp)
    have hsum : IntervalIntegrable
        (fun t => ∑ p ∈ S, coeff p / (path t - p)) volume e f := by
      convert IntervalIntegrable.sum S hPi using 1
      ext t
      simp only [Finset.sum_apply]
    calc
      _ = ∫ t : ℝ in e..f, G (path t) + ∑ p ∈ S, coeff p / (path t - p) :=
        integral_congr fun t _ => (eq_sub_iff_add_eq.mp (hEq (path t) (havoid t))).symm
      _ = _ := by
        rw [intervalIntegral.integral_add hGi hsum, intervalIntegral.integral_finsetSum hPi]
  have hHcont (y : ℝ) : Continuous (fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  have hVcont (x : ℝ) : Continuous (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hHmaps (y : ℝ) (hy : c ≤ y ∧ y ≤ d) :
      Set.MapsTo (fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (Set.uIcc a b) U := by
    intro t ht
    have htt : a ≤ t ∧ t ≤ b := by simpa [Set.uIcc_of_le hab] using ht
    simpa [U] using (show a ≤ t ∧ t ≤ b ∧ c ≤ y ∧ y ≤ d from
      ⟨htt.1, htt.2, hy.1, hy.2⟩)
  have hVmaps (x : ℝ) (hx : a ≤ x ∧ x ≤ b) :
      Set.MapsTo (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) (Set.uIcc c d) U := by
    intro t ht
    have htt : c ≤ t ∧ t ≤ d := by simpa [Set.uIcc_of_le hcd] using ht
    simpa [U] using (show a ≤ x ∧ x ≤ b ∧ c ≤ t ∧ t ≤ d from
      ⟨hx.1, hx.2, htt.1, htt.2⟩)
  have hHavoid (y : ℝ) (hy : y = c ∨ y = d) :
      ∀ t : ℝ, (t : ℂ) + (y : ℂ) * Complex.I ∉ S := by
    intro t ht
    have hcy : c < y := by simpa using (hS ((t : ℂ) + (y : ℂ) * Complex.I) ht).2.2.1
    have hyd : y < d := by simpa using (hS ((t : ℂ) + (y : ℂ) * Complex.I) ht).2.2.2
    rcases hy with rfl | rfl
    · exact (lt_irrefl _) hcy
    · exact (lt_irrefl _) hyd
  have hVavoid (x : ℝ) (hx : x = a ∨ x = b) :
      ∀ t : ℝ, (x : ℂ) + (t : ℂ) * Complex.I ∉ S := by
    intro t ht
    have hax : a < x := by simpa using (hS ((x : ℂ) + (t : ℂ) * Complex.I) ht).1
    have hxb : x < b := by simpa using (hS ((x : ℂ) + (t : ℂ) * Complex.I) ht).2.1
    rcases hx with rfl | rfl
    · exact (lt_irrefl _) hax
    · exact (lt_irrefl _) hxb
  have hbottom := hline a b (fun t : ℝ => (t : ℂ) + (c : ℂ) * Complex.I)
    (hHcont c) (hHmaps c ⟨le_rfl, hcd⟩) (hHavoid c (Or.inl rfl))
  have htop := hline a b (fun t : ℝ => (t : ℂ) + (d : ℂ) * Complex.I)
    (hHcont d) (hHmaps d ⟨hcd, le_rfl⟩) (hHavoid d (Or.inr rfl))
  have hright := hline c d (fun t : ℝ => (b : ℂ) + (t : ℂ) * Complex.I)
    (hVcont b) (hVmaps b ⟨hab, le_rfl⟩) (hVavoid b (Or.inr rfl))
  have hleft := hline c d (fun t : ℝ => (a : ℂ) + (t : ℂ) * Complex.I)
    (hVcont a) (hVmaps a ⟨le_rfl, hab⟩) (hVavoid a (Or.inl rfl))
  have hcauchy :
      (∫ t : ℝ in a..b, G ((t : ℂ) + (c : ℂ) * Complex.I)) -
        (∫ t : ℝ in a..b, G ((t : ℂ) + (d : ℂ) * Complex.I)) +
        Complex.I * (∫ t : ℝ in c..d, G ((b : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I * (∫ t : ℝ in c..d, G ((a : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
      ((a : ℂ) + (c : ℂ) * Complex.I) ((b : ℂ) + (d : ℂ) * Complex.I) (by
        intro s hs
        have hsU : s ∈ U := by
          simpa [U, Complex.reProdIm, Set.uIcc_of_le hab, Set.uIcc_of_le hcd, and_assoc] using hs
        exact (hG s hsU).differentiableAt.differentiableWithinAt)
    simpa [smul_eq_mul] using h
  calc
    _ = ((∫ t : ℝ in a..b, G ((t : ℂ) + (c : ℂ) * Complex.I)) -
          (∫ t : ℝ in a..b, G ((t : ℂ) + (d : ℂ) * Complex.I)) +
          Complex.I * (∫ t : ℝ in c..d, G ((b : ℂ) + (t : ℂ) * Complex.I)) -
          Complex.I * (∫ t : ℝ in c..d, G ((a : ℂ) + (t : ℂ) * Complex.I))) +
        ∑ p ∈ S,
          ((∫ t : ℝ in a..b, coeff p / ((t : ℂ) + (c : ℂ) * Complex.I - p)) -
            (∫ t : ℝ in a..b, coeff p / ((t : ℂ) + (d : ℂ) * Complex.I - p)) +
            Complex.I * (∫ t : ℝ in c..d, coeff p / ((b : ℂ) + (t : ℂ) * Complex.I - p)) -
            Complex.I * (∫ t : ℝ in c..d, coeff p / ((a : ℂ) + (t : ℂ) * Complex.I - p))) := by
      rw [hbottom, htop, hright, hleft]
      simp only [mul_add, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      abel
    _ = 0 + ∑ p ∈ S, 2 * (Real.pi : ℂ) * Complex.I * coeff p := by
      rw [hcauchy]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      exact rectangle_shifted_pole_integral (coeff p) p a b c d
        (hS p hp).1 (hS p hp).2.1 (hS p hp).2.2.1 (hS p hp).2.2.2
    _ = _ := by simp only [zero_add, Finset.mul_sum]

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
