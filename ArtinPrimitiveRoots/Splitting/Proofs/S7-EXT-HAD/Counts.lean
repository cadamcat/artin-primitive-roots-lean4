import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.Jensen

set_option autoImplicit false
open scoped BigOperators
open Classical

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

def zeroOrderWeights (G : ℂ → ℂ) (z : ℂ) : ℕ :=
  if G z = 0 then analyticOrderNatAt G z else 0

/-- Jensen gives finite disk supports and a dyadic count majorant for order-one growth. -/
theorem entire_dyadic_zero_count (G : ℂ → ℂ) (hG : Differentiable ℂ G) (hG0 : G 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖G s‖ ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2))) :
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ R : ℝ, 0 < R → Function.HasFiniteSupport
        (fun z : ℂ => if ‖z‖ ≤ R then (zeroOrderWeights G z : ℝ) else 0)) ∧
      ∀ n : ℕ,
        (∑' z : ℂ, if ‖z‖ ≤ (2 : ℝ) ^ (n + 1) then (zeroOrderWeights G z : ℝ) else 0) ≤
          A * ((n : ℝ) + 2) * (2 : ℝ) ^ (n + 1) := by
  sorry

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
