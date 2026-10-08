import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.GridCover

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

/-- A finite closed cover gives an upper counting bound without requiring disjoint cells. -/
theorem finiteCover_count_upper {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (S : Finset α) (T : Finset κ) (cell : κ → Finset α) (vol : κ → ℝ)
    (hcover : S ⊆ T.biUnion cell) (M E : ℝ)
    (hcell : ∀ k ∈ T, ((cell k).card : ℝ) ≤ M * vol k + E) :
    (S.card : ℝ) ≤ M * (∑ k ∈ T, vol k) + (T.card : ℝ) * E := by
  have hNat : S.card ≤ ∑ k ∈ T, (cell k).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hReal : (S.card : ℝ) ≤ ∑ k ∈ T, ((cell k).card : ℝ) := by exact_mod_cast hNat
  calc
    _ ≤ ∑ k ∈ T, ((cell k).card : ℝ) := hReal
    _ ≤ ∑ k ∈ T, (M * vol k + E) := Finset.sum_le_sum hcell
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp

/-- Constant bad-selected cells lie inside the bad set; only nonconstant cells may add excess. -/
theorem true_of_selected_constant_cell {α : Type*} (P : α → Prop) (s : Set α)
    (hselected : ∃ x ∈ s, P x)
    (hconstant : ¬ ∃ x ∈ s, ∃ y ∈ s, P x ∧ ¬ P y) :
    ∀ y ∈ s, P y := by
  obtain ⟨x, hx, hPx⟩ := hselected
  intro y hy
  by_contra hPy
  exact hconstant ⟨x, hx, y, hy, hPx, hPy⟩

end ArtinPrimitiveRoots.TypeII.PD
