import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.IntervalPacking

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- A circle-separated finite set meets a nearest-integer window in bounded cardinality. -/
theorem circle_window_card_bound {α : Type*} [DecidableEq α]
    (T : Finset α) (φ : α → ℝ) (δ r : ℝ)
    (hδ : 0 < δ) (hr : 0 ≤ r)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      δ ≤ circleDistance (φ i - φ j)) :
    ((T.filter fun i => circleDistance (φ i) ≤ r).card : ℝ) ≤ 2*r/δ+1 := by
  let U := T.filter fun i => circleDistance (φ i) ≤ r
  let center (i : α) := φ i - (round (φ i) : ℤ)
  have hrange (i : α) (hi : i ∈ U) : -r ≤ center i ∧ center i ≤ r := by
    have h := (Finset.mem_filter.mp hi).2
    rw [pd4c_circleDistance_eq_round] at h
    exact abs_le.mp h
  have hsepc (i : α) (hi : i ∈ U) (j : α) (hj : j ∈ U) (hne : i ≠ j) :
      δ ≤ |center i - center j| := by
    calc
      _ ≤ circleDistance (φ i - φ j) := hsep i (Finset.mem_filter.mp hi).1
        j (Finset.mem_filter.mp hj).1 hne
      _ ≤ |(φ i - φ j) - ((round (φ i) - round (φ j) : ℤ) : ℝ)| :=
        pd4c_circleDistance_le_abs_sub_int _ _
      _ = _ := by
        dsimp only [center]
        push_cast
        congr 1
        ring
  have h := interval_spacing_card_bound U center (-r) r δ hδ (by linarith) hrange hsepc
  convert h using 1 <;> ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
