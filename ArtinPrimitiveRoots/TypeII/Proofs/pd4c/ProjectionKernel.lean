import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Adjoint
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.SlicePairing

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

def pd4c_listSym (f : List Particle → ℂ) (l : List Particle) : ℂ :=
  (Fintype.card (Equiv.Perm (Fin l.length)) : ℂ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin l.length), f (List.ofFn fun k => l.get (σ k))

def pd4c_listDelta (m l : List Particle) : ℂ :=
  pd4c_listSym (fun u => if u = m then 1 else 0) l

theorem pd4c_delta_forall_eq_prod {ι : Type*} [Fintype ι] (P : ι → Prop) :
    (if ∀ i, P i then (1 : ℂ) else 0) = ∏ i : ι, if P i then (1 : ℂ) else 0 := by
  by_cases h : ∀ i, P i
  · simp only [if_pos h]
    symm
    exact Finset.prod_eq_one fun i hi => if_pos (h i)
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Memory projection of a point mass separates into its one-group projected point masses. -/
theorem pd4c_memorySym_delta_factor {x : ℝ} {K : ℕ} (s t : MemPoint x K) :
    memorySym (fun u => if u = t then (1 : ℂ) else 0) s =
      if s.1 = t.1 ∧ s.2.1 = t.2.1 then
        ∏ i : Fin K, pd4c_listDelta (t.2.2 i) (s.2.2 i) else 0 := by
  by_cases hp : s.1 = t.1 ∧ s.2.1 = t.2.1
  · rw [if_pos hp]
    have heq (σ : MemoryPermutation s) :
        memoryPermute s σ = t ↔ ∀ i, (List.ofFn fun k => (s.2.2 i).get (σ i k)) = t.2.2 i := by
      constructor
      · intro h i
        exact congrFun (congrArg (fun u : MemPoint x K => u.2.2) h) i
      · intro h
        exact Prod.ext hp.1 (Prod.ext hp.2 (funext h))
    have hδ (σ : MemoryPermutation s) :
        (if memoryPermute s σ = t then (1 : ℂ) else 0) =
          ∏ i : Fin K, if (List.ofFn fun k => (s.2.2 i).get (σ i k)) = t.2.2 i then (1 : ℂ) else 0 := by
      by_cases hσ : memoryPermute s σ = t
      · rw [if_pos hσ]
        symm
        exact Finset.prod_eq_one fun i hi => if_pos ((heq σ).mp hσ i)
      · rw [if_neg hσ]
        have hn : ¬ ∀ i, (List.ofFn fun k => (s.2.2 i).get (σ i k)) = t.2.2 i :=
          fun h => hσ ((heq σ).mpr h)
        push_neg at hn
        obtain ⟨i, hi⟩ := hn
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm
    have hcard : (Fintype.card (MemoryPermutation s) : ℂ) =
        ∏ i : Fin K, (Fintype.card (Equiv.Perm (Fin (s.2.2 i).length)) : ℂ) := by
      simp only [MemoryPermutation, Fintype.card_pi, Nat.cast_prod]
    unfold memorySym
    simp only [hδ]
    rw [hcard]
    have hprod : (∑ σ : MemoryPermutation s, ∏ i : Fin K,
        if (List.ofFn fun k => (s.2.2 i).get (σ i k)) = t.2.2 i then (1 : ℂ) else 0) =
        ∏ i : Fin K, ∑ σ : Equiv.Perm (Fin (s.2.2 i).length),
          if (List.ofFn fun k => (s.2.2 i).get (σ k)) = t.2.2 i then (1 : ℂ) else 0 :=
      (Fintype.prod_sum (fun (i : Fin K) (σ : Equiv.Perm (Fin (s.2.2 i).length)) =>
        if (List.ofFn fun k => (s.2.2 i).get (σ k)) = t.2.2 i then (1 : ℂ) else 0)).symm
    rw [hprod]
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    rfl
  · rw [if_neg hp]
    unfold memorySym
    have hzero : (∑ σ : MemoryPermutation s, if memoryPermute s σ = t then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro σ hσ
      have hne : memoryPermute s σ ≠ t := by
        intro h
        have h₁ := congrArg (fun u : MemPoint x K => u.1) h
        have h₂ := congrArg (fun u : MemPoint x K => u.2.1) h
        change s.1 = t.1 at h₁
        change s.2.1 = t.2.1 at h₂
        exact hp ⟨h₁, h₂⟩
      exact if_neg hne
    rw [hzero, mul_zero]

theorem pd4c_listDelta_empty : pd4c_listDelta [] [] = 1 := by
  simp [pd4c_listDelta, pd4c_listSym]

theorem pd4c_listDelta_star (m l : List Particle) : star (pd4c_listDelta m l) = pd4c_listDelta m l := by
  simp [pd4c_listDelta, pd4c_listSym, star_mul, star_inv, star_sum]
  <;> ring

def pd4c_singleMemoryPoint (l : List Particle) : MemPoint 0 1 :=
  ((1, 0), (fun _ _ => 0), fun _ => l)

theorem pd4c_single_memory_delta (m l : List Particle) :
    memorySym (fun u => if u = pd4c_singleMemoryPoint m then (1 : ℂ) else 0)
      (pd4c_singleMemoryPoint l) = pd4c_listDelta m l := by
  rw [pd4c_memorySym_delta_factor]
  simp [pd4c_singleMemoryPoint, Fin.prod_univ_one]

theorem pd4c_listDelta_perm (m : List Particle) {l l' : List Particle} (h : l.Perm l') :
    pd4c_listDelta m l = pd4c_listDelta m l' := by
  rw [← pd4c_single_memory_delta, ← pd4c_single_memory_delta]
  exact pd4c_memory_symmetric_list_perm _ (memorySym_isMemorySymmetric _)
    (pd4c_singleMemoryPoint l) (pd4c_singleMemoryPoint l') rfl rfl (fun _ => h)

theorem pd4c_listDelta_zero_of_length_ne (m l : List Particle) (hne : l.length ≠ m.length) :
    pd4c_listDelta m l = 0 := by
  unfold pd4c_listDelta pd4c_listSym
  have hzero : (∑ σ : Equiv.Perm (Fin l.length),
      if (List.ofFn fun k => l.get (σ k)) = m then (1 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro σ hσ
    have hn : (List.ofFn fun k => l.get (σ k)) ≠ m := by
      intro hm
      exact hne (by simpa only [List.length_ofFn] using congrArg List.length hm)
    exact if_neg hn
  rw [hzero, mul_zero]

theorem pd4c_listSym_word {T : Finset Particle} {n : ℕ} (w : Fin n → T)
    (f : List Particle → ℂ) :
    pd4c_listSym f (pd4c_word w) = (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ *
      ∑ π : Equiv.Perm (Fin n), f (pd4c_word (fun k => w (π k))) := by
  let e := pd4c_wordFinEquiv w
  let E := e.symm.permCongr
  have hcard : Fintype.card (Equiv.Perm (Fin (pd4c_word w).length)) =
      Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_congr E.symm
  have hlist (π : Equiv.Perm (Fin n)) :
      (List.ofFn fun j => (pd4c_word w).get (E π j)) = pd4c_word (fun k => w (π k)) := by
    calc
      _ = List.ofFn (fun k : Fin n => (pd4c_word w).get (E π (e.symm k))) :=
        List.ofFn_congr (by simp [pd4c_word]) _
      _ = _ := by
        congr 1
        funext k
        simp only [E, Equiv.permCongr_apply, Equiv.apply_symm_apply]
        exact pd4c_word_get w (π k)
  unfold pd4c_listSym
  rw [hcard]
  congr 1
  have hsum := Equiv.sum_comp E (fun σ => f (List.ofFn fun j => (pd4c_word w).get (σ j)))
  rw [← hsum]
  simp only [hlist]

end

end ArtinPrimitiveRoots.TypeII.PD
