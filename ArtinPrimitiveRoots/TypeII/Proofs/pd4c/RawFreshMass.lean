import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.RawChoices

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Finite fresh-label draws are exactly the normalized functions in the second
goodness test; this reindexing includes empty prime bands. -/
theorem raw_fresh_sum_reindex {K : ℕ} (x : ℝ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) (Φ : (Fin K → ℕ) → ℝ) :
    (∑ fresh : RawFreshLabels x a I, Φ (rawFreshFunction x a I fresh)) =
      ∑' g : Fin K → ℕ, if IsFreshChoice x a I g then Φ g else 0 := by
  let f := rawFreshFunction x a I
  let T : Finset (Fin K → ℕ) := Finset.univ.image f
  have hvalid (fresh : RawFreshLabels x a I) : IsFreshChoice x a I (f fresh) := by
    constructor
    · intro i hi
      simp only [f, rawFreshFunction, dif_pos hi]
    · intro i hi
      simpa only [f, rawFreshFunction, dif_neg hi] using
        (fresh ⟨i, Finset.mem_compl.mpr hi⟩).property
  have hinj : Function.Injective f := by
    intro fresh fresh' heq
    funext i
    apply Subtype.ext
    have hi : i.1 ∉ I := Finset.mem_compl.mp i.2
    have h := congrArg (fun g => g i.1) heq
    simpa only [f, rawFreshFunction, dif_neg hi] using h
  have hsurj (g : Fin K → ℕ) (hg : IsFreshChoice x a I g) :
      ∃ fresh : RawFreshLabels x a I, f fresh = g := by
    let fresh : RawFreshLabels x a I :=
      fun i => ⟨g i.1, hg.2 i.1 (Finset.mem_compl.mp i.2)⟩
    refine ⟨fresh, ?_⟩
    funext i
    by_cases hi : i ∈ I
    · simpa only [f, rawFreshFunction, dif_pos hi] using (hg.1 i hi).symm
    · simp only [f, rawFreshFunction, dif_neg hi, fresh]
  have hmem (g : Fin K → ℕ) : g ∈ T ↔ IsFreshChoice x a I g := by
    constructor
    · intro hg
      obtain ⟨fresh, _, rfl⟩ := Finset.mem_image.mp hg
      exact hvalid fresh
    · intro hg
      obtain ⟨fresh, h⟩ := hsurj g hg
      exact Finset.mem_image.mpr ⟨fresh, Finset.mem_univ _, h⟩
  calc
    _ = ∑ g ∈ T, Φ g := by
      apply Finset.sum_bij (fun fresh _ => f fresh)
      · intro fresh hfresh
        exact Finset.mem_image.mpr ⟨fresh, hfresh, rfl⟩
      · intro fresh hfresh fresh' hfresh' h
        exact hinj h
      · intro g hg
        obtain ⟨fresh, hfresh, h⟩ := Finset.mem_image.mp hg
        exact ⟨fresh, hfresh, h⟩
      · intro fresh hfresh
        rfl
    _ = ∑' g : Fin K → ℕ, if IsFreshChoice x a I g then Φ g else 0 := by
      rw [tsum_eq_sum (s := T)]
      · apply Finset.sum_congr rfl
        intro g hg
        simp only [if_pos ((hmem g).mp hg)]
      · intro g hg
        have hnot : ¬ IsFreshChoice x a I g := fun h => hg ((hmem g).mpr h)
        simp only [if_neg hnot]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
