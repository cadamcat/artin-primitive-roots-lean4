import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.BlockBounds

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.Construction.Proofs.C_BINS

/-- Conditioning on a distinct prime coprime to the progression contributes `1/(n-1)`. -/
theorem conditioned_density_product
    (M r n : ℕ) (D : Finset ℕ)
    (hn : n.Prime) (hn3 : 3 ≤ n) (hcop : Nat.Coprime n (M * r))
    (hnot : n ∉ D) (hD : ∀ p ∈ D, p.Prime ∧ 3 ≤ p) :
    localSieveDensity M r (n * (∏ p ∈ D, p)) =
      localSieveDensity M r (∏ p ∈ D, p) / ((n : ℝ) - 1) := by
  classical
  have hInsert : ∀ p ∈ insert n D, p.Prime ∧ 3 ≤ p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨hn, hn3⟩
    · exact hD p hp
  have hnDensity : localSieveDensity M r n = 1 / ((n : ℝ) - 1) := by
    simp [localSieveDensity, hcop, Nat.totient_prime hn, Nat.cast_sub hn.one_le]
  calc
    localSieveDensity M r (n * (∏ p ∈ D, p)) =
        localSieveDensity M r (∏ p ∈ insert n D, p) := by
      rw [Finset.prod_insert hnot]
    _ = ∏ p ∈ insert n D, localSieveDensity M r p :=
      (localSieveDensity_product_of_primes M r (insert n D) hInsert).symm
    _ = localSieveDensity M r n * (∏ p ∈ D, localSieveDensity M r p) :=
      Finset.prod_insert hnot
    _ = (1 / ((n : ℝ) - 1)) * localSieveDensity M r (∏ p ∈ D, p) := by
      rw [hnDensity, localSieveDensity_product_of_primes M r D hD]
    _ = localSieveDensity M r (∏ p ∈ D, p) / ((n : ℝ) - 1) := by ring

end ArtinPrimitiveRoots.Proofs.c_bins_sol
