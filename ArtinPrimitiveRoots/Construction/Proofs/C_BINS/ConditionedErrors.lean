import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.ConditionedModuli

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open ArtinPrimitiveRoots.Construction

/-- Distinct conditioned moduli charge the double error sum to one sieve-modulus sum. -/
theorem conditioned_moduli_absError_sum_le
    (B : ℝ) (P N : Finset ℕ) (T : Finset (Finset ℕ))
    (hP : ∀ p ∈ P, p.Prime) (hN : ∀ n ∈ N, n.Prime)
    (hdisjoint : Disjoint P N) (hsubset : ∀ D ∈ T, D ⊆ P)
    (himage : ∀ n ∈ N, ∀ D ∈ T,
      n * (∏ p ∈ D, p) ∈ oddSquarefreeUpTo B)
    (e : ℕ → ℝ) :
    (∑ n ∈ N, ∑ D ∈ T, |e (n * (∏ p ∈ D, p))|) ≤
      ∑ ℓ ∈ oddSquarefreeUpTo B, |e ℓ| := by
  classical
  let f : ℕ × Finset ℕ → ℕ := fun t => t.1 * (∏ p ∈ t.2, p)
  let pairs := N ×ˢ T
  let image := pairs.image f
  have hInj : Set.InjOn f pairs := by
    intro t ht t' ht' hEq
    obtain ⟨hn, hD⟩ := Finset.mem_product.mp ht
    obtain ⟨hn', hD'⟩ := Finset.mem_product.mp ht'
    have h := conditioned_modulus_injective P N hP hN hdisjoint
      t.1 hn t'.1 hn' t.2 t'.2 (hsubset t.2 hD) (hsubset t'.2 hD') hEq
    exact Prod.ext h.1 h.2
  have hImageSub : image ⊆ oddSquarefreeUpTo B := by
    intro ℓ hℓ
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hℓ
    obtain ⟨hn, hD⟩ := Finset.mem_product.mp ht
    exact himage t.1 hn t.2 hD
  calc
    (∑ n ∈ N, ∑ D ∈ T, |e (n * (∏ p ∈ D, p))|) =
        ∑ t ∈ pairs, |e (f t)| := by
      simpa only [pairs, f] using
        (Finset.sum_product N T (fun t => |e (f t)|)).symm
    _ = ∑ ℓ ∈ image, |e ℓ| := by
      simpa only [image] using
        (Finset.sum_image (f := fun ℓ : ℕ => |e ℓ|) (g := f) hInj).symm
    _ ≤ ∑ ℓ ∈ oddSquarefreeUpTo B, |e ℓ| :=
      Finset.sum_le_sum_of_subset_of_nonneg hImageSub (fun ℓ _ _ => abs_nonneg _)

end ArtinPrimitiveRoots.Proofs.c_bins_sol
