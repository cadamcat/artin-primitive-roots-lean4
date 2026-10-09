import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.BlockBounds

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open ArtinPrimitiveRoots.Construction.Proofs.C_BINS

/-- A conditioned prime disjoint from the sieve primes is recovered from its modulus. -/
theorem conditioned_modulus_injective
    (P N : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hN : ∀ n ∈ N, n.Prime)
    (hdisjoint : Disjoint P N) :
    ∀ n ∈ N, ∀ n' ∈ N, ∀ D E : Finset ℕ, D ⊆ P → E ⊆ P →
      n * (∏ p ∈ D, p) = n' * (∏ p ∈ E, p) → n = n' ∧ D = E := by
  classical
  intro n hn n' hn' D E hDP hEP hprod
  have hUnion : ∀ p ∈ P ∪ N, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hN p hp
  have hnP : n ∉ P := fun hp => (Finset.disjoint_left.mp hdisjoint) hp hn
  have hn'P : n' ∉ P := fun hp => (Finset.disjoint_left.mp hdisjoint) hp hn'
  have hnD : n ∉ D := fun hd => hnP (hDP hd)
  have hn'E : n' ∉ E := fun he => hn'P (hEP he)
  have hInsertD : insert n D ⊆ P ∪ N := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_union_right P hn
    · exact Finset.mem_union_left N (hDP hp)
  have hInsertE : insert n' E ⊆ P ∪ N := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_union_right P hn'
    · exact Finset.mem_union_left N (hEP hp)
  have hProducts : (∏ p ∈ insert n D, p) = (∏ p ∈ insert n' E, p) := by
    rw [Finset.prod_insert hnD, Finset.prod_insert hn'E]
    exact hprod
  have hSets : insert n D = insert n' E :=
    prime_subset_product_injective (P ∪ N) hUnion
      (insert n D) (insert n' E) hInsertD hInsertE hProducts
  have hnn' : n = n' := by
    have hmem : n ∈ insert n' E := hSets ▸ Finset.mem_insert_self n D
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exact (hnP (hEP h)).elim
  refine ⟨hnn', ?_⟩
  rw [← hnn'] at hSets hn'E
  simpa [hnD, hn'E] using congrArg (fun S : Finset ℕ => S.erase n) hSets

end ArtinPrimitiveRoots.Proofs.c_bins_sol
