import ArtinPrimitiveRoots.TypeII.Defs

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical

noncomputable section

/-- Zero extension through a finite injection preserves the counting matrix norm bound. -/
theorem finite_injective_matrix_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (U : Finset β) (e : α → β)
    (hmap : ∀ t ∈ T, e t ∈ U) (hinj : Set.InjOn e (T : Set α))
    (k : β → β → ℂ) (R : ℝ)
    (hk : ∀ g : β → ℂ,
      (∑ b ∈ U, ‖∑ c ∈ U, k b c*g c‖^2) ≤ R^2*(∑ c ∈ U, ‖g c‖^2))
    (f : α → ℂ) :
    (∑ s ∈ T, ‖∑ t ∈ T, k (e s) (e t)*f t‖^2) ≤
      R^2*(∑ t ∈ T, ‖f t‖^2) := by
  let E : Finset β := T.image e
  let g : β → ℂ := fun b => ∑ t ∈ T, if e t = b then f t else 0
  have hEU : E ⊆ U := by
    intro b hb
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    exact hmap t ht
  have hzero (b : β) (hb : b ∉ E) : g b = 0 := by
    dsimp only [g]
    apply Finset.sum_eq_zero
    intro t ht
    have hne : e t ≠ b := fun he => hb (Finset.mem_image.mpr ⟨t, ht, he⟩)
    simp only [hne, if_false]
  have hvalue (t : α) (ht : t ∈ T) : g (e t) = f t := by
    dsimp only [g]
    rw [Finset.sum_eq_single t]
    · simp
    · intro s hs hst
      have hne : e s ≠ e t := fun he => hst (hinj hs ht he)
      simp only [hne, if_false]
    · intro hnot
      exact (hnot ht).elim
  have hrow (s : α) :
      (∑ b ∈ U, k (e s) b*g b) = ∑ t ∈ T, k (e s) (e t)*f t := by
    dsimp only [g]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_eq_single (e t)]
    · simp
    · intro b hb hne
      simp only [Ne.symm hne, if_false]
    · intro hnot
      exact (hnot (hmap t ht)).elim
  have henergy : (∑ b ∈ U, ‖g b‖^2) = ∑ t ∈ T, ‖f t‖^2 := by
    calc
      _ = ∑ b ∈ E, ‖g b‖^2 := (Finset.sum_subset hEU (fun b hb hnot => by
        simp only [hzero b hnot, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])).symm
      _ = ∑ t ∈ T, ‖g (e t)‖^2 := by dsimp only [E]; rw [Finset.sum_image hinj]
      _ = _ := Finset.sum_congr rfl (fun t ht => by rw [hvalue t ht])
  calc
    _ = ∑ b ∈ E, ‖∑ c ∈ U, k b c*g c‖^2 := by
      dsimp only [E]
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl (fun s hs => by rw [hrow s])
    _ ≤ ∑ b ∈ U, ‖∑ c ∈ U, k b c*g c‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hEU (fun b hb hnot => sq_nonneg _)
    _ ≤ R^2*(∑ b ∈ U, ‖g b‖^2) := hk g
    _ = _ := by rw [henergy]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
