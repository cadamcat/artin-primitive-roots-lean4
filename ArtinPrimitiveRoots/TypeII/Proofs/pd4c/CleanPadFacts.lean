import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.UnionLabels

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Actual valid source lists supply the squarefree pad and its Diophantine test. -/
theorem clean_shared_pad_facts {K : ℕ} (x Y d₀ r : ℝ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (hgood : goodTestOne x Y d₀ p r)
    (hpad : d₀ ≤ (sharedProduct p : ℝ) ∧ (sharedProduct p : ℝ) < 2*d₀) :
    Squarefree (sharedProduct p) ∧
      ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Real.rpow Y (1/5 : ℝ) →
        Real.rpow Y (-(7/10 : ℝ)) < circleDistance ((l : ℝ)*(sharedProduct p : ℝ)*r) := by
  have hrow (i : Fin K) : Function.Injective (p i) := by
    intro j j' heq
    by_contra hne
    exact hp.2 i j j' hne heq
  have hfull := primeMatrixProduct_squarefree p hp.1 hrow hbands
  have hdvd : sharedProduct p ∣ ∏ i : Fin K, ∏ j : Fin (slotCount x), p i j := by
    rw [listProduct_eq_shared_mul_last]
    exact dvd_mul_right _ _
  refine ⟨Squarefree.squarefree_of_dvd hdvd hfull, ?_⟩
  have h := hgood (fun _ => lastSlot x)
  rw [← sharedProduct_eq_omission_last p] at h
  exact h hpad.1 hpad.2

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
