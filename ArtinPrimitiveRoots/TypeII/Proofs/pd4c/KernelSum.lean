import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical
open scoped BigOperators

noncomputable section

/-- A finite sum of weighted kernel bounds loses only the number of summands in norm. -/
theorem finite_weighted_kernel_sum_bound {α ι : Type*}
    [DecidableEq α] [DecidableEq ι]
    (T : Finset α) (E : Finset ι) (μ : α → ℝ) (hμ : ∀ u ∈ T, 0 ≤ μ u)
    (k : ι → α → α → ℂ) (R : ℝ)
    (hk : ∀ j ∈ E, ∀ g : α → ℂ,
      (∑ u ∈ T, μ u*‖∑ v ∈ T, k j u v*(μ v : ℂ)*g v‖^2) ≤
        R^2*(∑ v ∈ T, μ v*‖g v‖^2))
    (f : α → ℂ) :
    (∑ u ∈ T, μ u*‖∑ v ∈ T, (∑ j ∈ E, k j u v)*(μ v : ℂ)*f v‖^2) ≤
      (((E.card : ℝ)*R)^2)*(∑ v ∈ T, μ v*‖f v‖^2) := by
  let row : ι → α → ℂ := fun j u => ∑ v ∈ T, k j u v*(μ v : ℂ)*f v
  let Ec : ℝ := (E.card : ℝ)
  have hEc : 0 ≤ Ec := Nat.cast_nonneg _
  have hrows (u : α) : (∑ v ∈ T, (∑ j ∈ E, k j u v)*(μ v : ℂ)*f v) =
      ∑ j ∈ E, row j u := by
    dsimp only [row]
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  have hpoint (u : α) : ‖∑ j ∈ E, row j u‖^2 ≤ Ec*(∑ j ∈ E, ‖row j u‖^2) := by
    have hnorm := norm_sum_le E (fun j => row j u)
    calc
      _ ≤ (∑ j ∈ E, ‖row j u‖)^2 := by
        simpa only [pow_two] using mul_le_mul hnorm hnorm (norm_nonneg _)
          (Finset.sum_nonneg (fun j hj => norm_nonneg (row j u)))
      _ ≤ _ := by
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq E (fun _ : ι => (1 : ℝ))
          (fun j => ‖row j u‖)
        simpa only [Ec, one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using hcs
  have hterm (u : α) : μ u*(Ec*(∑ j ∈ E, ‖row j u‖^2)) =
      Ec*(∑ j ∈ E, μ u*‖row j u‖^2) := by
    rw [← Finset.mul_sum]
    ring
  calc
    _ = ∑ u ∈ T, μ u*‖∑ j ∈ E, row j u‖^2 :=
      Finset.sum_congr rfl (fun u hu => by rw [hrows u])
    _ ≤ ∑ u ∈ T, μ u*(Ec*(∑ j ∈ E, ‖row j u‖^2)) :=
      Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hpoint u) (hμ u hu))
    _ = Ec*(∑ u ∈ T, ∑ j ∈ E, μ u*‖row j u‖^2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun u hu => hterm u)
    _ = Ec*(∑ j ∈ E, ∑ u ∈ T, μ u*‖row j u‖^2) :=
      congrArg (fun x : ℝ => Ec*x) Finset.sum_comm
    _ ≤ Ec*(∑ j ∈ E, R^2*(∑ v ∈ T, μ v*‖f v‖^2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j hj => hk j hj f)) hEc
    _ = _ := by
      simp only [Ec, Finset.sum_const, nsmul_eq_mul]
      ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
