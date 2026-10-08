import ArtinPrimitiveRoots.Proofs.pd_life_b.MemoryPrimeHits

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- The prime-set and exact-size update for a promotion and optional source-slot store. -/
theorem edge_memory_prime_transport {K : ℕ} (F : PDFix K) (S : PDScale)
    (σ : LogPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (σ.1.2.2 i) i)
    (hσ : LiveLogValid σ) (i : Fin K) :
    ((edgeNewMemory F S σ.1 c i).map Prod.fst).toFinset =
      (((σ.1.2.2 i).map Prod.fst).toFinset \
        (match (c i).2 with
          | Sum.inl k => {((σ.1.2.2 i).get k).1}
          | Sum.inr _ => ∅)) ∪
        (if (c i).1 then {σ.1.2.1 i (lastSlot S.x)} else ∅) ∧
    (edgeNewMemory F S σ.1 c i).length =
      ((σ.1.2.2 i).length - (if (c i).2.isLeft then 1 else 0)) +
        (if (c i).1 then 1 else 0) := by
  classical
  have hn : ((σ.1.2.2 i).map Prod.fst).Nodup :=
    (List.nodup_append.mp (hσ.1 i)).2.1
  let D : Finset (Fin (σ.1.2.2 i).length) :=
    match (c i).2 with
    | Sum.inl k => {k}
    | Sum.inr _ => ∅
  have hD := memory_prime_deletion_transport (σ.1.2.2 i) hn D
  have hImage : D.image (fun k => ((σ.1.2.2 i).get k).1) =
      (match (c i).2 with
        | Sum.inl k => {((σ.1.2.2 i).get k).1}
        | Sum.inr _ => ∅) := by
    cases hc : (c i).2 <;> simp [D, hc]
  have hCard : D.card = (if (c i).2.isLeft then 1 else 0) := by
    cases hc : (c i).2 <;> simp [D, hc]
  have hOutput : edgeNewMemory F S σ.1 c i =
      removeIndices (σ.1.2.2 i) D ++
        (if (c i).1 then [anchorAt (σ.1.2.1 i (lastSlot S.x)) σ.1.1] else []) := by
    cases hc : (c i).2 <;> simp only [edgeNewMemory, D, hc]
  constructor
  · rw [hOutput, List.map_append, List.toFinset_append, hD.1, hImage]
    congr 1
    cases (c i).1 <;> simp [anchorAt]
  · rw [hOutput, List.length_append, hD.2, hCard]
    congr 1
    cases (c i).1 <;> simp

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
