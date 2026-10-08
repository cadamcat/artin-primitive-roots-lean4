import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_ordered_distinct_batch_sum

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Cancel a distinct batch's factorial while retaining a complex continuation that is
invariant under permutations of the batch. The empty batch is included. -/
theorem ordered_batch_sum_of_perm_invariant
    (T : Finset ℕ) (ν : ℕ → ℝ) (f : List ℕ → ℂ)
    (hf : ∀ l l', List.Perm l l' → f l = f l') :
    (∑ new : Fin T.card → T,
      if Function.Bijective new then
        (((∏ k, ν (new k).1) / (T.card.factorial : ℝ) : ℝ) : ℂ) *
          f (List.ofFn fun k => (new k).1)
      else 0) =
      ((∏ p ∈ T, ν p : ℝ) : ℂ) * f T.toList := by
  classical
  have hList (new : Fin T.card → T) (hnew : Function.Bijective new) :
      f (List.ofFn fun k => (new k).1) = f T.toList := by
    have hNodup : (List.ofFn fun k => (new k).1).Nodup :=
      List.nodup_ofFn.mpr (Subtype.val_injective.comp hnew.injective)
    apply hf
    apply (List.perm_ext_iff_of_nodup hNodup T.nodup_toList).mpr
    intro p
    constructor
    · intro hp
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hp
      exact Finset.mem_toList.mpr (hk ▸ (new k).2)
    · intro hp
      have hpT : p ∈ T := Finset.mem_toList.mp hp
      obtain ⟨k, hk⟩ := hnew.surjective ⟨p, hpT⟩
      exact List.mem_ofFn.mpr ⟨k, congrArg Subtype.val hk⟩
  calc
    _ = ∑ new : Fin T.card → T,
        ((if Function.Bijective new then
            (∏ k, ν (new k).1) / (T.card.factorial : ℝ)
          else 0 : ℝ) : ℂ) * f T.toList := by
      apply Finset.sum_congr rfl
      intro new hmem
      by_cases hnew : Function.Bijective new
      · simp only [if_pos hnew, hList new hnew]
      · simp only [if_neg hnew, Complex.ofReal_zero, zero_mul]
    _ = ((∑ new : Fin T.card → T,
        if Function.Bijective new then
          (∏ k, ν (new k).1) / (T.card.factorial : ℝ)
        else 0 : ℝ) : ℂ) * f T.toList := by
      push_cast
      rw [Finset.sum_mul]
    _ = _ := by rw [pd_ordered_distinct_batch_sum]

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
