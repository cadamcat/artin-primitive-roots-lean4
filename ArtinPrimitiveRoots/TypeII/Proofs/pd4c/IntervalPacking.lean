import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Circle

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Separated real phases in a bounded interval have bounded finite cardinality. -/
theorem interval_spacing_card_bound {α : Type*} [DecidableEq α]
    (T : Finset α) (φ : α → ℝ) (a b δ : ℝ)
    (hδ : 0 < δ) (hab : a ≤ b)
    (hrange : ∀ i ∈ T, a ≤ φ i ∧ φ i ≤ b)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → δ ≤ |φ i - φ j|) :
    (T.card : ℝ) ≤ (b - a) / δ + 1 := by
  let f : α → ℤ := fun i => ⌊(φ i - a) / δ⌋
  let R := (b - a) / δ
  let z : ℤ := ⌊R⌋
  have hR : 0 ≤ R := div_nonneg (sub_nonneg.mpr hab) hδ.le
  have hz : 0 ≤ z := Int.floor_nonneg.mpr hR
  have hinj : Set.InjOn f (T : Set α) := by
    intro i hi j hj heq
    by_contra hne
    have hilo : (f i : ℝ) ≤ (φ i - a) / δ := Int.floor_le _
    have hihi : (φ i - a) / δ < (f i : ℝ) + 1 := Int.lt_floor_add_one _
    have hjlo : (f j : ℝ) ≤ (φ j - a) / δ := Int.floor_le _
    have hjhi : (φ j - a) / δ < (f j : ℝ) + 1 := Int.lt_floor_add_one _
    rw [← heq] at hjlo hjhi
    have hilo' := (le_div_iff₀ hδ).mp hilo
    have hihi' := (div_lt_iff₀ hδ).mp hihi
    have hjlo' := (le_div_iff₀ hδ).mp hjlo
    have hjhi' := (div_lt_iff₀ hδ).mp hjhi
    have hclose : |φ i - φ j| < δ := by
      apply abs_lt.mpr
      constructor <;> nlinarith only [hilo', hihi', hjlo', hjhi']
    exact (not_lt_of_ge (hsep i hi j hj hne)) hclose
  have hsub : T.image f ⊆ Finset.Icc (0 : ℤ) z := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_Icc.mpr
    constructor
    · exact Int.floor_nonneg.mpr (div_nonneg (sub_nonneg.mpr (hrange i hi).1) hδ.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right
        (sub_le_sub_right (hrange i hi).2 a) hδ.le)
  have hcard : T.card ≤ (Finset.Icc (0 : ℤ) z).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hcast : ((Finset.Icc (0 : ℤ) z).card : ℝ) = (z : ℝ) + 1 := by
    have hInt : ((Finset.Icc (0 : ℤ) z).card : ℤ) = z + 1 := by
      rw [Int.card_Icc]
      simp only [sub_zero, Int.toNat_of_nonneg (by omega : 0 ≤ z + 1)]
    exact_mod_cast hInt
  calc
    _ ≤ ((Finset.Icc (0 : ℤ) z).card : ℝ) := by exact_mod_cast hcard
    _ = (z : ℝ) + 1 := hcast
    _ ≤ R + 1 := by
      have hzle : (z : ℝ) ≤ R := Int.floor_le R
      linarith only [hzle]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
