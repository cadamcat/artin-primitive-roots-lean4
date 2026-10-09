import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical
open scoped BigOperators

noncomputable section

/-- An injective finite change of coordinates preserves a weighted bound and a common mass factor. -/
theorem finite_weighted_injective_kernel_transfer {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (T : Finset α) (Φ : α → β) (hΦ : Set.InjOn Φ (T : Set α))
    (ν : β → ℝ) (k : β → β → ℂ) (R W : ℝ) (hW : 0 ≤ W)
    (hk : ∀ g : β → ℂ,
      (∑ u ∈ T.image Φ, ν u*‖∑ v ∈ T.image Φ, k u v*(ν v : ℂ)*g v‖^2) ≤
        R^2*(∑ v ∈ T.image Φ, ν v*‖g v‖^2))
    (f : α → ℂ) :
    (∑ u ∈ T, (W*ν (Φ u))*‖∑ v ∈ T, k (Φ u) (Φ v)*(ν (Φ v) : ℂ)*f v‖^2) ≤
      R^2*(∑ v ∈ T, (W*ν (Φ v))*‖f v‖^2) := by
  let g : β → ℂ := fun b => ∑ t ∈ T, if Φ t = b then f t else 0
  have hvalue (t : α) (ht : t ∈ T) : g (Φ t) = f t := by
    dsimp only [g]
    rw [Finset.sum_eq_single t]
    · simp only [ite_true]
    · intro s hs hst
      have hne : Φ s ≠ Φ t := fun he => hst (hΦ hs ht he)
      simp only [hne, if_false]
    · intro hnot
      exact (hnot ht).elim
  have hrow (s : α) :
      (∑ b ∈ T.image Φ, k (Φ s) b*(ν b : ℂ)*g b) =
        ∑ t ∈ T, k (Φ s) (Φ t)*(ν (Φ t) : ℂ)*f t := by
    rw [Finset.sum_image hΦ]
    exact Finset.sum_congr rfl (fun t ht => by rw [hvalue t ht])
  have houtput :
      (∑ u ∈ T.image Φ, ν u*‖∑ v ∈ T.image Φ, k u v*(ν v : ℂ)*g v‖^2) =
        ∑ u ∈ T, ν (Φ u)*‖∑ v ∈ T, k (Φ u) (Φ v)*(ν (Φ v) : ℂ)*f v‖^2 := by
    rw [Finset.sum_image hΦ]
    exact Finset.sum_congr rfl (fun u hu => by rw [hrow u])
  have henergy : (∑ v ∈ T.image Φ, ν v*‖g v‖^2) =
      ∑ v ∈ T, ν (Φ v)*‖f v‖^2 := by
    rw [Finset.sum_image hΦ]
    exact Finset.sum_congr rfl (fun v hv => by rw [hvalue v hv])
  have hbound := hk g
  rw [houtput, henergy] at hbound
  have hfactor (b : α → ℝ) : (∑ u ∈ T, (W*ν (Φ u))*b u) =
      W*(∑ u ∈ T, ν (Φ u)*b u) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun u hu => by ring)
  calc
    _ = W*(∑ u ∈ T, ν (Φ u)*‖∑ v ∈ T, k (Φ u) (Φ v)*(ν (Φ v) : ℂ)*f v‖^2) := hfactor _
    _ ≤ W*(R^2*(∑ v ∈ T, ν (Φ v)*‖f v‖^2)) := mul_le_mul_of_nonneg_left hbound hW
    _ = _ := by rw [hfactor]; ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
