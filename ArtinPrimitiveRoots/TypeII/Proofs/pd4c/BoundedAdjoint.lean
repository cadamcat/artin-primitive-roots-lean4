import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Adjoint

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

/-- All ordered words up to the memory cutoff in one finite particle alphabet. -/
abbrev Pd4cBoundedWord (T : Finset Particle) (B : ℕ) := Σ n : Fin (B + 1), Fin n.val → T

/-- The creation/deletion adjoint remains exact after the memory cutoff. -/
theorem pd4c_bounded_creation_pairing (T : Finset Particle) (B : ℕ) (ν : Particle → ℝ)
    (e : T) (F G : List Particle → ℂ)
    (hF : ∀ l l', List.Perm l l' → F l = F l')
    (hG : ∀ l l', List.Perm l l' → G l = G l')
    (hFzero : ∀ l, B < l.length → F l = 0) :
    (ν e : ℂ) *
        (∑ w : Pd4cBoundedWord T B, (pd4c_listDensity ν (pd4c_word w.2) : ℂ) *
          G (pd4c_word w.2) * F (pd4c_word w.2 ++ [(e : Particle)])) =
      ∑ w : Pd4cBoundedWord T B, (pd4c_listDensity ν (pd4c_word w.2) : ℂ) *
        F (pd4c_word w.2) *
        (∑ k : Fin w.1.val, if (w.2 k : Particle) = (e : Particle) then
          G (removeIndices (pd4c_word w.2) {pd4c_wordIndex w.2 k}) else 0) := by
  let H (n : ℕ) : ℂ := ∑ w : Fin n → T, (pd4c_listDensity ν (pd4c_word w) : ℂ) *
    G (pd4c_word w) * F (pd4c_word w ++ [(e : Particle)])
  let J (n : ℕ) : ℂ := ∑ w : Fin n → T, (pd4c_listDensity ν (pd4c_word w) : ℂ) *
    F (pd4c_word w) *
    (∑ k : Fin n, if (w k : Particle) = (e : Particle) then
      G (removeIndices (pd4c_word w) {pd4c_wordIndex w k}) else 0)
  have hH : H B = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    have hzero : F (pd4c_word w ++ [(e : Particle)]) = 0 := by
      apply hFzero
      simp [pd4c_word]
    simp only [hzero, mul_zero]
  have hJ : J 0 = 0 := by simp [J]
  have hpair (n : ℕ) : (ν e : ℂ) * H n = J (n + 1) :=
    pd4c_creation_pairing T ν e n F G hF hG
  have hsplitH : (∑ w : Pd4cBoundedWord T B, (pd4c_listDensity ν (pd4c_word w.2) : ℂ) *
      G (pd4c_word w.2) * F (pd4c_word w.2 ++ [(e : Particle)])) =
        ∑ n : Fin (B + 1), H n.val := by
    exact Fintype.sum_sigma' (fun (n : Fin (B + 1)) (w : Fin n.val → T) =>
      (pd4c_listDensity ν (pd4c_word w) : ℂ) * G (pd4c_word w) *
        F (pd4c_word w ++ [(e : Particle)]))
  have hsplitJ : (∑ w : Pd4cBoundedWord T B, (pd4c_listDensity ν (pd4c_word w.2) : ℂ) *
      F (pd4c_word w.2) *
      (∑ k : Fin w.1.val, if (w.2 k : Particle) = (e : Particle) then
        G (removeIndices (pd4c_word w.2) {pd4c_wordIndex w.2 k}) else 0)) =
        ∑ n : Fin (B + 1), J n.val := by
    exact Fintype.sum_sigma' (fun (n : Fin (B + 1)) (w : Fin n.val → T) =>
      (pd4c_listDensity ν (pd4c_word w) : ℂ) * F (pd4c_word w) *
        (∑ k : Fin n.val, if (w k : Particle) = (e : Particle) then
          G (removeIndices (pd4c_word w) {pd4c_wordIndex w k}) else 0))
  rw [hsplitH, hsplitJ, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, Fin.val_succ, hH, hJ,
    add_zero, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact hpair n.val

end

end ArtinPrimitiveRoots.TypeII.PD
