import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

/-- A nonsquare coefficient separates the two quadratic pushforward supports near one.
The unscaled square preimage has positive finite Haar measure, whereas the scaled square
preimage is empty. This is the support test needed for the actual Gaussian nondegeneracy
argument. No Gaussian or Fourier identity is assumed. -/
theorem nonsquare_quadratic_support_test {K : Type*} [NormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [Measure.IsAddHaarMeasure μ]
    (a : Kˣ) (ha : ¬ IsSquare (a : K)) :
    ∃ r : ℝ, 0 < r ∧
      (fun x : K => (a : K) * x ^ 2) ⁻¹' Metric.ball 1 r = ∅ ∧
      0 < μ ((fun x : K => x ^ 2) ⁻¹' Metric.ball 1 r) ∧
      μ ((fun x : K => x ^ 2) ⁻¹' Metric.ball 1 r) < ⊤ := by
  have hclosed : IsClosed (Set.range fun x : K => (a : K) * x ^ 2) :=
    ((Homeomorph.mulLeft₀ (a : K) a.ne_zero).isClosedMap.comp
      (isClosedMap_pow K 2)).isClosed_range
  have hnot : (1 : K) ∉ Set.range (fun x : K => (a : K) * x ^ 2) := by
    rintro ⟨x, hx⟩
    change (a : K) * x ^ 2 = 1 at hx
    apply ha
    refine ⟨(a : K) * x, ?_⟩
    calc
      (a : K) = (a : K) * ((a : K) * x ^ 2) := by rw [hx, mul_one]
      _ = ((a : K) * x) * ((a : K) * x) := by ring
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl 1 hnot
  have hempty : (fun x : K => (a : K) * x ^ 2) ⁻¹' Metric.ball 1 r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hball hx ⟨x, rfl⟩
  have hopen : IsOpen ((fun x : K => x ^ 2) ⁻¹' Metric.ball 1 r) :=
    Metric.isOpen_ball.preimage (continuous_id.pow 2)
  have hnonempty : ((fun x : K => x ^ 2) ⁻¹' Metric.ball 1 r).Nonempty := by
    refine ⟨1, ?_⟩
    simpa only [Set.mem_preimage, one_pow] using Metric.mem_ball_self hr
  have hproper : IsProperMap (fun x : K => x ^ 2) := by
    convert (Polynomial.X ^ 2 : Polynomial K).isProperMap_eval (by simp) using 1
    funext x
    simp
  have hcompact : IsCompact ((fun x : K => x ^ 2) ⁻¹' Metric.closedBall 1 r) :=
    hproper.isCompact_preimage (isCompact_closedBall 1 r)
  refine ⟨r, hr, hempty, hopen.measure_pos μ hnonempty, ?_⟩
  exact (measure_mono (Set.preimage_mono Metric.ball_subset_closedBall)).trans_lt
    hcompact.measure_lt_top

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
