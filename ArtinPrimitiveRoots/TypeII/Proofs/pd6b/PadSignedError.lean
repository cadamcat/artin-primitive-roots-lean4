import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadMass

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical

/-- Signed pad subtraction separates pad losses from restored noncoprime comparison terms. -/
theorem pad_signed_difference_bound {ι : Type*} (T : Finset ι) (cop : ι → Prop) [DecidablePred cop]
    (θ : ι → ℝ) (R M : ι → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hθ : ∀ i ∈ T, cop i → 0 ≤ θ i ∧ θ i ≤ 1 ∧ 1 - θ i ≤ ε) :
    ‖(∑ i ∈ T, if cop i then (θ i : ℂ) * (R i - M i) else 0) -
      ((∑ i ∈ T, if cop i then R i else 0) - ∑ i ∈ T, M i)‖ ≤
      ε * (∑ i ∈ T, if cop i then ‖R i‖ + ‖M i‖ else 0) +
        ∑ i ∈ T, if cop i then 0 else ‖M i‖ := by
  have heq : (∑ i ∈ T, if cop i then (θ i : ℂ) * (R i - M i) else 0) -
      ((∑ i ∈ T, if cop i then R i else 0) - ∑ i ∈ T, M i) =
      ∑ i ∈ T, if cop i then ((θ i : ℂ) - 1) * (R i - M i) else M i := by
    rw [sub_sub_eq_add_sub, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [heq]
  calc
    _ ≤ ∑ i ∈ T, ‖if cop i then ((θ i : ℂ) - 1) * (R i - M i) else M i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ T,
        ((if cop i then ε * (‖R i‖ + ‖M i‖) else 0) + (if cop i then 0 else ‖M i‖)) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hc : cop i
      · rw [if_pos hc, if_pos hc, if_pos hc, add_zero, norm_mul]
        have h := hθ i hi hc
        have hnorm : ‖(θ i : ℂ) - 1‖ ≤ ε := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonpos (sub_nonpos.mpr h.2.1)]
          linarith [h.2.2]
        exact mul_le_mul hnorm (norm_sub_le _ _) (norm_nonneg _) hε
      · simp [hc]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp

/-- Uniform absolute-square estimates turn the signed subtraction into a scalar error bound. -/
theorem pad_signed_difference_uniform {ι : Type*} (T : Finset ι) (cop : ι → Prop) [DecidablePred cop]
    (θ : ι → ℝ) (R M : ι → ℂ) (ε RawAbs CompAbs CollisionAbs : ℝ) (hε : 0 ≤ ε)
    (hθ : ∀ i ∈ T, cop i → 0 ≤ θ i ∧ θ i ≤ 1 ∧ 1 - θ i ≤ ε)
    (hRaw : (∑ i ∈ T, if cop i then ‖R i‖ else 0) ≤ RawAbs)
    (hComp : (∑ i ∈ T, if cop i then ‖M i‖ else 0) ≤ CompAbs)
    (hCollision : (∑ i ∈ T, if cop i then 0 else ‖M i‖) ≤ CollisionAbs) :
    ‖(∑ i ∈ T, if cop i then (θ i : ℂ) * (R i - M i) else 0) -
      ((∑ i ∈ T, if cop i then R i else 0) - ∑ i ∈ T, M i)‖ ≤
      ε * (RawAbs + CompAbs) + CollisionAbs := by
  apply (pad_signed_difference_bound T cop θ R M ε hε hθ).trans
  have hsum : (∑ i ∈ T, if cop i then ‖R i‖ + ‖M i‖ else 0) =
      (∑ i ∈ T, if cop i then ‖R i‖ else 0) + (∑ i ∈ T, if cop i then ‖M i‖ else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  rw [hsum]
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hRaw hComp) hε) hCollision

end ArtinPrimitiveRoots.TypeII.PD
