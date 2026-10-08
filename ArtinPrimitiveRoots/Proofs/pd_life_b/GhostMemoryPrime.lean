import ArtinPrimitiveRoots.Proofs.pd_life_b.EdgeMemoryPrime

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- Canonical finite ghost births update the memory prime set and its exact list length. -/
theorem ghost_memory_prime_transport {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℕ) (σ : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (σ.1.2.2 i).length))
    (T : (i : Fin K) → (primeBand S.x (F.a i)).powerset)
    (hσ : LiveLogValid σ) (i : Fin K) :
    (((subsetGhostPoint F S j σ D T).1.2.2 i).map Prod.fst).toFinset =
      (((σ.1.2.2 i).map Prod.fst).toFinset \
        (D i).image (fun k => ((σ.1.2.2 i).get k).1)) ∪ (T i).1 ∧
    ((subsetGhostPoint F S j σ D T).1.2.2 i).length =
      ((σ.1.2.2 i).length - (D i).card) + (T i).1.card := by
  classical
  have hn : ((σ.1.2.2 i).map Prod.fst).Nodup :=
    (List.nodup_append.mp (hσ.1 i)).2.1
  have hD := memory_prime_deletion_transport (σ.1.2.2 i) hn (D i)
  have hPrimes : ((subsetGhostPoint F S j σ D T).1.2.2 i).map Prod.fst =
      (removeIndices (σ.1.2.2 i) (D i)).map Prod.fst ++ (T i).1.toList := by
    simp only [subsetGhostPoint, List.map_append, List.map_map,
      Function.comp_def, anchorAt, List.map_id_fun', id_eq]
  constructor
  · rw [hPrimes, List.toFinset_append, hD.1, Finset.toList_toFinset]
  · simp only [subsetGhostPoint, List.length_append, List.length_map,
      Finset.length_toList, hD.2]

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
