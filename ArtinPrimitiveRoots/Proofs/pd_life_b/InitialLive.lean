import ArtinPrimitiveRoots.Proofs.pd_life_b.EdgeLive

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- Empty-memory initial states have distinct live values, all recorded in their initial log. -/
theorem initialPoint_live_log_valid {x : ℝ} {K : ℕ}
    (s : MemPoint x K)
    (hEmpty : ∀ i, s.2.2 i = [])
    (hActive : ∀ i, Function.Injective (s.2.1 i)) :
    LiveLogValid (s, initialLog s) := by
  constructor
  · intro i
    simpa only [groupLivePrimes, hEmpty i, List.map_nil, List.append_nil] using
      List.nodup_ofFn.mpr (hActive i)
  · intro i p hp
    have hp' : p ∈ List.ofFn (s.2.1 i) := by
      simpa only [groupLivePrimes, hEmpty i, List.map_nil, List.append_nil] using hp
    rcases List.mem_ofFn.mp hp' with ⟨j, rfl⟩
    apply List.mem_map.mpr
    refine ⟨(BirthAddress.initial i j.val, s.2.1 i j), ?_, rfl⟩
    unfold initialLog
    apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_finRange i, ?_⟩
    exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
