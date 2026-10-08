import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.Defs

set_option autoImplicit false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

/-- Bijections from indexed slots to a distinct prime set cancel the local batch factorial.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:418–433. Uses no other part; feeds
pd_ordered_birth_bijection. The existing private ordered_distinct_batch_sum proof in
MemoryResults can be reused verbatim, with all old memory indices remaining indexed. -/
theorem pd_ordered_distinct_batch_sum (T : Finset ℕ) (ν : ℕ → ℝ) :
    (∑ new : Fin T.card → T,
      if Function.Bijective new then
      (∏ k, ν (new k).1) / (T.card.factorial : ℝ) else 0) =
      ∏ p ∈ T, ν p := by
  classical
  let n := T.card
  let B : Type := {f : Fin n → T // Function.Bijective f}
  let e0 : Fin n ≃ T := (Finset.equivFin T).symm
  let e : B ≃ Equiv.Perm (Fin n) :=
    { toFun := fun f => (Equiv.ofBijective f.1 f.2).trans e0.symm
      invFun := fun σ => ⟨σ.trans e0, (σ.trans e0).bijective⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        simp [e0, Equiv.ofBijective]
      right_inv := by
        intro σ
        ext i
        simp [e0] }
  have hcard : Fintype.card B = n.factorial := by
    calc
      Fintype.card B = Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_congr e
      _ = (Fintype.card (Fin n)).factorial := Fintype.card_perm
      _ = n.factorial := by simp [n]
  let Q : ℝ := ∏ p ∈ T, ν p
  have hprod (f : B) : (∏ k : Fin n, ν (f.1 k).1) = Q := by
    calc
      (∏ k : Fin n, ν (f.1 k).1) = ∏ t : T, ν t.1 :=
        Function.Bijective.prod_comp f.2 (fun t : T => ν t.1)
      _ = Q := by
        simpa [Q] using (Finset.prod_attach T ν)
  have hsumB :
      (∑ f : B, (∏ k : Fin n, ν (f.1 k).1) / (n.factorial : ℝ)) = Q := by
    calc
      _ = ∑ f : B, Q / (n.factorial : ℝ) := by
            apply Finset.sum_congr rfl
            intro f hf
            rw [hprod]
      _ = (Fintype.card B : ℝ) * (Q / (n.factorial : ℝ)) := by simp
      _ = Q := by rw [hcard]; field_simp
  change (∑ new : Fin n → T,
      if Function.Bijective new then
        (∏ k, ν (new k).1) / (n.factorial : ℝ) else 0) = Q
  calc
    _ = ∑ new ∈ (Finset.univ : Finset (Fin n → T)).filter Function.Bijective,
          (∏ k, ν (new k).1) / (n.factorial : ℝ) := by
          rw [Finset.sum_filter]
    _ = ∑ f : B, (∏ k, ν (f.1 k).1) / (n.factorial : ℝ) := by
          rw [← Finset.sum_subtype_eq_sum_filter]
          simp [B]
    _ = Q := hsumB

end
end ArtinPrimitiveRoots.TypeII.PD
