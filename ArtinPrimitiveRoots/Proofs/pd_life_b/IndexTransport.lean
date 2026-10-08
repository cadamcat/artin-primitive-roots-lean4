import Mathlib.Data.List.Perm.Basic
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

/-- A list permutation matches its individual indices, including repeated elements. -/
theorem perm_index_equiv {α : Type*} (l m : List α) (hperm : l.Perm m) :
    ∃ e : Fin l.length ≃ Fin m.length,
      ∀ k, l.get k = m.get (e k) := by
  induction hperm with
  | nil =>
      refine ⟨Equiv.refl _, ?_⟩
      intro k
      exact Fin.elim0 k
  | @cons x xs ys h ih =>
      obtain ⟨e, he⟩ := ih
      let e' : Fin (xs.length + 1) ≃ Fin (ys.length + 1) :=
        (finSuccEquiv xs.length).trans
          ((Equiv.optionCongr e).trans (finSuccEquiv ys.length).symm)
      have he0 : e' 0 = 0 := by
        simp [e', Equiv.trans_apply, Equiv.optionCongr]
      have heSucc (j : Fin xs.length) : e' j.succ = (e j).succ := by
        simp [e', Equiv.trans_apply, Equiv.optionCongr]
      refine ⟨e', ?_⟩
      intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · rw [he0]
        rfl
      · rw [heSucc]
        exact he j
  | swap x y xs =>
      refine ⟨Equiv.swap 0 1, ?_⟩
      intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · rw [Equiv.swap_apply_left]
        rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · change _ = (x :: y :: xs).get (Equiv.swap 0 1 1)
          rw [Equiv.swap_apply_right]
          rfl
        · have hzero : j.succ.succ ≠ (0 : Fin (xs.length + 2)) := by
            intro heq
            have hval := congrArg Fin.val heq
            simp only [Fin.val_succ, Fin.val_zero] at hval
            omega
          have hone : j.succ.succ ≠ (1 : Fin (xs.length + 2)) := by
            intro heq
            have hval := congrArg Fin.val heq
            simp only [Fin.val_succ, Fin.val_one] at hval
            omega
          rw [Equiv.swap_apply_of_ne_of_ne hzero hone]
          rfl
  | trans h₁ h₂ ih₁ ih₂ =>
      obtain ⟨e₁, he₁⟩ := ih₁
      obtain ⟨e₂, he₂⟩ := ih₂
      refine ⟨e₁.trans e₂, ?_⟩
      intro k
      exact (he₁ k).trans (he₂ (e₁ k))

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
