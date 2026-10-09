import Mathlib

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical

noncomputable section

/-- Successive finite coordinate bounds control the crossed tensor matrix. -/
theorem finite_tensor_norm_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (U : Finset β) (k : α → β → ℂ) (l : β → α → ℂ)
    (f : α → β → ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hk : ∀ g : β → ℂ, (∑ x ∈ T, ‖∑ v ∈ U, k x v*g v‖^2) ≤
      a*(∑ v ∈ U, ‖g v‖^2))
    (hl : ∀ g : α → ℂ, (∑ y ∈ U, ‖∑ u ∈ T, l y u*g u‖^2) ≤
      b*(∑ u ∈ T, ‖g u‖^2)) :
    (∑ x ∈ T, ∑ y ∈ U, ‖∑ u ∈ T, ∑ v ∈ U, k x v*l y u*f u v‖^2) ≤
      a*b*(∑ u ∈ T, ∑ v ∈ U, ‖f u v‖^2) := by
  let g (x u : α) : ℂ := ∑ v ∈ U, k x v*f u v
  have hrep (x : α) (y : β) :
      (∑ u ∈ T, ∑ v ∈ U, k x v*l y u*f u v) = ∑ u ∈ T, l y u*g x u := by
    dsimp only [g]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    ring
  have hpoint (x : α) :
      (∑ y ∈ U, ‖∑ u ∈ T, ∑ v ∈ U, k x v*l y u*f u v‖^2) ≤
      b*(∑ u ∈ T, ‖g x u‖^2) := by
    simp_rw [hrep]
    exact hl (g x)
  calc
    _ ≤ ∑ x ∈ T, b*(∑ u ∈ T, ‖g x u‖^2) :=
      Finset.sum_le_sum fun x hx => hpoint x
    _ = b*(∑ x ∈ T, ∑ u ∈ T, ‖g x u‖^2) := (Finset.mul_sum _ _ _).symm
    _ = b*(∑ u ∈ T, ∑ x ∈ T, ‖g x u‖^2) := by rw [Finset.sum_comm]
    _ ≤ b*(∑ u ∈ T, a*(∑ v ∈ U, ‖f u v‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ hb
      apply Finset.sum_le_sum
      intro u hu
      exact hk (f u)
    _ = _ := by rw [← Finset.mul_sum]; ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
