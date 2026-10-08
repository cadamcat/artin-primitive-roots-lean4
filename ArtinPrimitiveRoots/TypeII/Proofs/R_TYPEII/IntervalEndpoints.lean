import ArtinPrimitiveRoots.TypeII.Marked

namespace ArtinPrimitiveRoots.Proofs.r_typeii_p

/-- A finite convex subset of `ℕ` is the closed interval between its extrema. -/
theorem finite_nat_interval_endpoints (S : Finset ℕ)
    (hS : ArtinPrimitiveRoots.TypeII.IsNatInterval (S : Set ℕ))
    (hne : S.Nonempty) :
    ∃ a b : ℕ, a ≤ b ∧ S = Finset.Icc a b := by
  classical
  let a := S.min' hne
  let b := S.max' hne
  have ha : a ∈ S := Finset.min'_mem S hne
  have hb : b ∈ S := Finset.max'_mem S hne
  have hab : a ≤ b := Finset.min'_le_max' S hne
  refine ⟨a, b, hab, ?_⟩
  ext n
  simp only [Finset.mem_Icc]
  constructor
  · intro hn
    constructor
    · simpa [a] using Finset.min'_le S n hn
    · simpa [b] using Finset.le_max' S n hn
  · intro hn
    have hleft : min a b ≤ n := by
      simpa [min_eq_left hab] using hn.1
    have hright : n ≤ max a b := by
      simpa [max_eq_right hab] using hn.2
    exact hS ha hb hleft hright

end ArtinPrimitiveRoots.Proofs.r_typeii_p
