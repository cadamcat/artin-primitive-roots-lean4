import ArtinPrimitiveRoots.Proofs.pd_life_b.InitialLive

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- Slot permutations preserve distinct live values and their birth-log membership. -/
theorem permuteLists_live_log_valid {x : ℝ} {K : ℕ}
    (σ : LogPoint x K)
    (π : Fin K → Equiv.Perm (Fin (slotCount x)))
    (hσ : LiveLogValid σ) :
    LiveLogValid
      ((σ.1.1, permuteLists π σ.1.2.1, σ.1.2.2), σ.2) := by
  have hPerm (i : Fin K) :
      (groupLivePrimes (σ.1.1, permuteLists π σ.1.2.1, σ.1.2.2) i).Perm
        (groupLivePrimes σ.1 i) := by
    change (List.ofFn (σ.1.2.1 i ∘ π i) ++ (σ.1.2.2 i).map Prod.fst).Perm
      (List.ofFn (σ.1.2.1 i) ++ (σ.1.2.2 i).map Prod.fst)
    exact ((π i).ofFn_comp_perm (σ.1.2.1 i)).append_right _
  constructor
  · intro i
    exact (hPerm i).nodup_iff.mpr (hσ.1 i)
  · intro i p hp
    exact hσ.2 i p ((hPerm i).mem_iff.mp hp)

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
