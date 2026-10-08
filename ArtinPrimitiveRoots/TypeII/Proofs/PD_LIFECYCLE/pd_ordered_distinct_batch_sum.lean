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
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
