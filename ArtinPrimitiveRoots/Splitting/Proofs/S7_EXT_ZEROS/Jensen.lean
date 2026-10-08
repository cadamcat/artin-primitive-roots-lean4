import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false

open scoped BigOperators
open Classical Metric MeromorphicOn

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- Jensen's disk count in the multiplicity and summation conventions of the targets. -/
theorem jensen_multiplicity_count {G : ℂ → ℂ} {c : ℂ} {r R M : ℝ} {U : Set ℂ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hG : AnalyticOnNhd ℂ G (closedBall c R)) (hc : G c ≠ 0)
    (hbound : ∀ z ∈ sphere c R, ‖G z‖ ≤ M) (hU : U ⊆ closedBall c r) :
    Summable (fun z : ℂ => if z ∈ U then (analyticOrderNatAt G z : ℝ) else 0) ∧
      (∑' z : ℂ, if z ∈ U then (analyticOrderNatAt G z : ℝ) else 0) ≤
        Real.log (M / ‖G c‖) / Real.log (R / r) := by
  classical
  have hR : 0 < R := hr.trans hrR
  have hin : AnalyticOnNhd ℂ G (closedBall c r) :=
    hG.mono (closedBall_subset_closedBall hrR.le)
  let D := divisor G (closedBall c r)
  let F : ℂ → ℝ := fun z => if z ∈ U then (analyticOrderNatAt G z : ℝ) else 0
  have hD : Function.HasFiniteSupport D :=
    (divisor G (closedBall c r)).finiteSupport (isCompact_closedBall c r)
  have horder (z : ℂ) (hz : z ∈ closedBall c r) :
      D z = (analyticOrderNatAt G z : ℤ) := by
    simp only [D, hin.divisor_apply hz]
    cases h : analyticOrderAt G z with
    | top => simp [analyticOrderNatAt, h]
    | coe n => simp [analyticOrderNatAt, h]
  have hF : Function.HasFiniteSupport F := by
    apply hD.subset
    intro z hz
    change F z ≠ 0 at hz
    change D z ≠ 0
    by_cases hzU : z ∈ U
    · have hz0 : (analyticOrderNatAt G z : ℝ) ≠ 0 := by simpa [F, hzU] using hz
      rw [horder z (hU hzU)]
      exact_mod_cast hz0
    · exact (hz (by simp [F, hzU])).elim
  have hDreal : Function.HasFiniteSupport (fun z : ℂ => (D z : ℝ)) := by
    apply hD.subset
    intro z hz
    simpa only [Function.mem_support, ne_eq, Int.cast_eq_zero] using hz
  have hpoint (z : ℂ) : F z ≤ (D z : ℝ) := by
    by_cases hzU : z ∈ U
    · simp only [F, if_pos hzU, horder z (hU hzU), Int.cast_natCast]
      exact le_rfl
    · simp only [F, if_neg hzU]
      exact_mod_cast hin.divisor_nonneg z
  have hsumF : Summable F := summable_of_hasFiniteSupport hF
  refine ⟨hsumF, ?_⟩
  calc
    (∑' z : ℂ, F z) = ∑ᶠ z : ℂ, F z := tsum_eq_finsum hF
    _ ≤ ∑ᶠ z : ℂ, (D z : ℝ) := finsum_le_finsum hF hDreal hpoint
    _ = ((∑ᶠ z : ℂ, D z : ℤ) : ℝ) := (map_finsum (Int.castRingHom ℝ) hD).symm
    _ ≤ Real.log (M / ‖G c‖) / Real.log (R / r) := by
      have hG' : AnalyticOnNhd ℂ G (closedBall c |R|) := by
        simpa only [abs_of_pos hR] using hG
      have hj := hG'.sum_divisor_le (r := r) (R := R) (M := M)
          (by simpa only [abs_of_pos hr] using hr)
          (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
          hM hc (by simpa only [abs_of_pos hR] using hbound)
      rw [abs_of_pos hr] at hj
      exact hj

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
