import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Density
import Mathlib.GroupTheory.Perm.Fin

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

/-- A finite memory word with its indexed particles. -/
def pd4c_word {T : Finset Particle} {n : ℕ} (w : Fin n → T) : List Particle :=
  List.ofFn fun i => (w i : Particle)

def pd4c_wordFinEquiv {T : Finset Particle} {n : ℕ} (w : Fin n → T) :
    Fin (pd4c_word w).length ≃ Fin n := finCongr (by simp [pd4c_word])

def pd4c_wordIndex {T : Finset Particle} {n : ℕ} (w : Fin n → T) (i : Fin n) :
    Fin (pd4c_word w).length := (pd4c_wordFinEquiv w).symm i

theorem pd4c_word_get {T : Finset Particle} {n : ℕ} (w : Fin n → T) (i : Fin n) :
    (pd4c_word w).get (pd4c_wordIndex w i) = (w i : Particle) := by
  simp [pd4c_word, pd4c_wordIndex, pd4c_wordFinEquiv]
  congr 1

private theorem pd4c_word_perm {T : Finset Particle} {n : ℕ}
    (w : Fin n → T) (π : Equiv.Perm (Fin n)) :
    List.Perm (pd4c_word (fun i => w (π i))) (pd4c_word w) := by
  simpa only [pd4c_word, Function.comp_def] using
    Equiv.Perm.ofFn_comp_perm π (fun i => (w i : Particle))

private theorem pd4c_word_remove_perm {T : Finset Particle} {n : ℕ}
    (w : Fin n → T) (π : Equiv.Perm (Fin n)) (k : Fin n) :
    List.Perm (removeIndices (pd4c_word (fun i => w (π i)))
      {pd4c_wordIndex (fun i => w (π i)) k})
      (removeIndices (pd4c_word w) {pd4c_wordIndex w (π k)}) := by
  let w' := fun i => w (π i)
  let e : Fin (pd4c_word w').length ≃ Fin (pd4c_word w).length :=
    (pd4c_wordFinEquiv w').trans (π.trans (pd4c_wordFinEquiv w).symm)
  have hindex (i : Fin n) : e (pd4c_wordIndex w' i) = pd4c_wordIndex w (π i) := by
    simp [e, pd4c_wordIndex, Equiv.trans_apply]
  have hget (j : Fin (pd4c_word w').length) :
      (pd4c_word w').get j = (pd4c_word w).get (e j) := by
    have hleft := pd4c_word_get w' ((pd4c_wordFinEquiv w') j)
    simp only [pd4c_wordIndex, Equiv.symm_apply_apply] at hleft
    have hright : (pd4c_word w).get (e j) =
        (w (π ((pd4c_wordFinEquiv w') j)) : Particle) := by
      exact pd4c_word_get w (π ((pd4c_wordFinEquiv w') j))
    exact hleft.trans hright.symm
  have h := pd4c_removeIndices_perm_of_getEquiv e hget {pd4c_wordIndex w' k}
  simpa only [Finset.image_singleton, hindex, w'] using h

private theorem pd4c_word_density {T : Finset Particle} {n : ℕ}
    (ν : Particle → ℝ) (w : Fin n → T) :
    pd4c_listDensity ν (pd4c_word w) =
      (∏ i : Fin n, ν (w i)) / (n.factorial : ℝ) := by
  simp [pd4c_listDensity, pd4c_word, List.prod_ofFn, Function.comp_def]

private theorem pd4c_word_density_perm {T : Finset Particle} {n : ℕ}
    (ν : Particle → ℝ) (w : Fin n → T) (π : Equiv.Perm (Fin n)) :
    pd4c_listDensity ν (pd4c_word (fun i => w (π i))) = pd4c_listDensity ν (pd4c_word w) := by
  rw [pd4c_word_density, pd4c_word_density]
  exact congrArg (fun a : ℝ => a / (n.factorial : ℝ))
    (Equiv.prod_comp π (fun i => ν (w i)))

private theorem pd4c_remove_cons_zero (a : Particle) (l : List Particle) :
    removeIndices (a :: l) {(0 : Fin (a :: l).length)} = l := by
  have hmap : (List.finRange l.length).map l.get = l := by
    simpa only [List.ofFn_eq_map] using List.ofFn_get l
  simpa [removeIndices, List.finRange_succ, List.filterMap_map, Function.comp_def] using hmap

private theorem pd4c_word_cons {T : Finset Particle} {n : ℕ} (a : T) (w : Fin n → T) :
    pd4c_word (Fin.cons a w) = (a : Particle) :: pd4c_word w := by
  have hfun : (fun i : Fin (n + 1) => ((Fin.cons a w : Fin (n + 1) → T) i : Particle)) =
      Fin.cons (a : Particle) (fun i => (w i : Particle)) := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  unfold pd4c_word
  rw [hfun, List.ofFn_cons]

private theorem pd4c_remove_head (L : List Particle) (a : Particle) (l : List Particle)
    (hL : L = a :: l) (k : Fin L.length) (hk : k.val = 0) : removeIndices L {k} = l := by
  subst L
  have hk0 : k = (0 : Fin (a :: l).length) := by
    apply Fin.ext
    exact hk
  rw [hk0]
  exact pd4c_remove_cons_zero a l

private theorem pd4c_word_remove_zero {T : Finset Particle} {n : ℕ} (a : T) (w : Fin n → T) :
    removeIndices (pd4c_word (Fin.cons a w)) {pd4c_wordIndex (Fin.cons a w) 0} = pd4c_word w := by
  exact pd4c_remove_head _ _ _ (pd4c_word_cons a w) _ (by rfl)

private def pd4c_annihilationTerm {T : Finset Particle} {n : ℕ}
    (ν : Particle → ℝ) (e : T) (F G : List Particle → ℂ)
    (w : Fin n → T) (k : Fin n) : ℂ :=
  (pd4c_listDensity ν (pd4c_word w) : ℂ) * F (pd4c_word w) *
    (if (w k : Particle) = (e : Particle) then
      G (removeIndices (pd4c_word w) {pd4c_wordIndex w k}) else 0)

private theorem pd4c_annihilationTerm_permute {T : Finset Particle} {n : ℕ}
    (ν : Particle → ℝ) (e : T) (F G : List Particle → ℂ)
    (hF : ∀ l l', List.Perm l l' → F l = F l')
    (hG : ∀ l l', List.Perm l l' → G l = G l')
    (w : Fin n → T) (π : Equiv.Perm (Fin n)) (k : Fin n) :
    pd4c_annihilationTerm ν e F G (fun i => w (π i)) k =
      pd4c_annihilationTerm ν e F G w (π k) := by
  have hF' := hF _ _ (pd4c_word_perm w π)
  have hG' := hG _ _ (pd4c_word_remove_perm w π k)
  unfold pd4c_annihilationTerm
  rw [pd4c_word_density_perm, hF']
  by_cases he : (w (π k) : Particle) = (e : Particle) <;> simp only [he, if_pos, if_neg, hG']

private theorem pd4c_annihilation_sum_index {T : Finset Particle} (n : ℕ)
    (ν : Particle → ℝ) (e : T) (F G : List Particle → ℂ)
    (hF : ∀ l l', List.Perm l l' → F l = F l')
    (hG : ∀ l l', List.Perm l l' → G l = G l') (k : Fin (n + 1)) :
    (∑ w : Fin (n + 1) → T, pd4c_annihilationTerm ν e F G w k) =
      ∑ w : Fin (n + 1) → T, pd4c_annihilationTerm ν e F G w 0 := by
  let π : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 k
  let E : (Fin (n + 1) → T) ≃ (Fin (n + 1) → T) := {
    toFun := fun w i => w (π i)
    invFun := fun w i => w (π.symm i)
    left_inv := by intro w; funext i; simp
    right_inv := by intro w; funext i; simp
  }
  have h := Equiv.sum_comp E (fun w => pd4c_annihilationTerm ν e F G w 0)
  change (∑ w : Fin (n + 1) → T, pd4c_annihilationTerm ν e F G (fun i => w (π i)) 0) =
    (∑ w : Fin (n + 1) → T, pd4c_annihilationTerm ν e F G w 0) at h
  simp_rw [pd4c_annihilationTerm_permute ν e F G hF hG] at h
  simpa only [π, Equiv.swap_apply_left] using h


/-- The factorial memory measure turns creation into indexed deletion on symmetric functions. -/
theorem pd4c_creation_pairing (T : Finset Particle) (ν : Particle → ℝ)
    (e : T) (n : ℕ) (F G : List Particle → ℂ)
    (hF : ∀ l l', List.Perm l l' → F l = F l')
    (hG : ∀ l l', List.Perm l l' → G l = G l') :
    (ν e : ℂ) *
        (∑ w : Fin n → T, (pd4c_listDensity ν (pd4c_word w) : ℂ) *
          G (pd4c_word w) * F (pd4c_word w ++ [(e : Particle)])) =
      ∑ w : Fin (n + 1) → T, (pd4c_listDensity ν (pd4c_word w) : ℂ) *
        F (pd4c_word w) *
        (∑ k : Fin (n + 1), if (w k : Particle) = (e : Particle) then
          G (removeIndices (pd4c_word w) {pd4c_wordIndex w k}) else 0) := by
  let split : (Fin (n + 1) → T) ≃ T × (Fin n → T) := {
    toFun := fun w => (w 0, fun i => w i.succ)
    invFun := fun p => Fin.cons p.1 p.2
    left_inv := by
      intro w
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    right_inv := by
      intro p
      apply Prod.ext
      · simp
      · funext i
        simp
  }
  have hFixed : (∑ w : Fin (n + 1) → T, pd4c_annihilationTerm ν e F G w 0) =
      ∑ w : Fin n → T, (pd4c_listDensity ν ((e : Particle) :: pd4c_word w) : ℂ) *
        F ((e : Particle) :: pd4c_word w) * G (pd4c_word w) := by
    have h := Equiv.sum_comp split.symm (fun w => pd4c_annihilationTerm ν e F G w 0)
    change (∑ p : T × (Fin n → T), pd4c_annihilationTerm ν e F G (Fin.cons p.1 p.2) 0) =
      (∑ w : Fin (n + 1) → T, pd4c_annihilationTerm ν e F G w 0) at h
    rw [← h, Fintype.sum_prod_type]
    simp only [pd4c_annihilationTerm, Fin.cons_zero, pd4c_word_remove_zero, pd4c_word_cons]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    simp [Subtype.coe_inj, mul_ite]
  have hTotal :
      (∑ w : Fin (n + 1) → T, (pd4c_listDensity ν (pd4c_word w) : ℂ) * F (pd4c_word w) *
        (∑ k : Fin (n + 1), if (w k : Particle) = (e : Particle) then
          G (removeIndices (pd4c_word w) {pd4c_wordIndex w k}) else 0)) =
        ((n + 1 : ℕ) : ℂ) * ∑ w : Fin n → T,
          (pd4c_listDensity ν ((e : Particle) :: pd4c_word w) : ℂ) *
            F ((e : Particle) :: pd4c_word w) * G (pd4c_word w) := by
    calc
      _ = ∑ w : Fin (n + 1) → T, ∑ k : Fin (n + 1), pd4c_annihilationTerm ν e F G w k := by
        apply Finset.sum_congr rfl
        intro w hw
        exact Finset.mul_sum _ _ _
      _ = ∑ k : Fin (n + 1), ∑ w : Fin (n + 1) → T, pd4c_annihilationTerm ν e F G w k := by
        rw [Finset.sum_comm]
      _ = ∑ k : Fin (n + 1), ∑ w : Fin (n + 1) → T, pd4c_annihilationTerm ν e F G w 0 := by
        simp_rw [pd4c_annihilation_sum_index n ν e F G hF hG]
      _ = ((n + 1 : ℕ) : ℂ) * ∑ w : Fin (n + 1) → T, pd4c_annihilationTerm ν e F G w 0 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = _ := by rw [hFixed]
  rw [hTotal, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hDensity : ((n + 1 : ℕ) : ℂ) *
      (pd4c_listDensity ν ((e : Particle) :: pd4c_word w) : ℂ) =
        (ν e : ℂ) * (pd4c_listDensity ν (pd4c_word w) : ℂ) := by
    have h := congrArg (fun r : ℝ => (r : ℂ))
      (pd4c_listDensity_cons ν (pd4c_word w) (e : Particle))
    simpa only [Complex.ofReal_mul, Complex.ofReal_natCast, pd4c_word, List.length_ofFn] using h
  have hF' : F (pd4c_word w ++ [(e : Particle)]) = F ((e : Particle) :: pd4c_word w) := by
    apply hF
    simpa using List.perm_append_comm (pd4c_word w) [(e : Particle)]
  rw [hF']
  calc
    _ = ((ν e : ℂ) * (pd4c_listDensity ν (pd4c_word w) : ℂ)) *
        F ((e : Particle) :: pd4c_word w) * G (pd4c_word w) := by ring
    _ = _ := by rw [← hDensity]; ring

/-- Reindex indexed retrieval from word positions to the actual list-position type. -/
theorem pd4c_word_retrieve_sum {T : Finset Particle} {n : ℕ}
    (w : Fin n → T) (e : Particle) (g : List Particle → ℂ) :
    (∑ k : Fin (pd4c_word w).length, if (pd4c_word w).get k = e then
      g (removeIndices (pd4c_word w) {k}) else 0) =
      ∑ k : Fin n, if (w k : Particle) = e then
        g (removeIndices (pd4c_word w) {pd4c_wordIndex w k}) else 0 := by
  have h := Equiv.sum_comp (pd4c_wordFinEquiv w).symm
    (fun k : Fin (pd4c_word w).length => if (pd4c_word w).get k = e then
      g (removeIndices (pd4c_word w) {k}) else 0)
  rw [← h]
  apply Finset.sum_congr rfl
  intro k hk
  change (if (pd4c_word w).get (pd4c_wordIndex w k) = e then
    g (removeIndices (pd4c_word w) {pd4c_wordIndex w k}) else 0) = _
  rw [pd4c_word_get]

end

end ArtinPrimitiveRoots.TypeII.PD
