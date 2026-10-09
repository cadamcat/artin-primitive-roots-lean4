import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.Positivity

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Classical ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Construction.Proofs.C_BINS

/-- Natural multiplication by a positive rough integer reindexes its divisor sum. -/
theorem rough_divisor_convolution
    (x W : ℝ) (q : ℕ) (w : ℕ → ℝ)
    (hx : 0 < x) (hq : 0 < q) (hQrough : roughAbove q W)
    (hSupport : ∀ d, w d ≠ 0 → (d : ℝ) < 2 * x) :
    (∑ m ∈ Finset.range (⌊2 * x⌋₊ + 1),
      if roughAbove m W then w (m * q) else 0) =
      ∑ d ∈ Finset.range (⌊2 * x⌋₊ + 1),
        if q ∣ d ∧ roughAbove d W then w d else 0 := by
  classical
  let R : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let f : ℕ → ℝ := fun m => if roughAbove m W then w (m * q) else 0
  let g : ℕ → ℝ := fun d => if q ∣ d ∧ roughAbove d W then w d else 0
  have hLink (m : ℕ) : g (m * q) = f m := by
    have hDiv : q ∣ m * q := ⟨m, Nat.mul_comm _ _⟩
    have hRough : roughAbove (m * q) W ↔ roughAbove m W := by
      rw [roughAbove_mul_iff]
      constructor
      · exact And.left
      · intro hm
        exact ⟨hm, hQrough⟩
    simp only [g, f, hDiv, true_and, hRough]
  have hWeightNZ (m : ℕ) (hm : f m ≠ 0) : w (m * q) ≠ 0 := by
    intro hzero
    apply hm
    simp [f, hzero]
  have hRightFacts (d : ℕ) (hd : g d ≠ 0) : q ∣ d ∧ roughAbove d W := by
    by_contra hbad
    apply hd
    simp [g, hbad]
  have hEq : (∑ m ∈ R, f m) = ∑ d ∈ R, g d := by
    apply Finset.sum_bij_ne_zero (fun m hm hNZ => m * q)
    · intro m hm hNZ
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_iff.mpr
      apply (Nat.le_floor_iff (by positivity : 0 ≤ 2 * x)).mpr
      exact (hSupport (m * q) (hWeightNZ m hNZ)).le
    · intro m₁ hm₁ hNZ₁ m₂ hm₂ hNZ₂ hprod
      exact mul_right_cancel₀ (ne_of_gt hq) hprod
    · intro d hd hNZ
      have hDiv := (hRightFacts d hNZ).1
      have hMq : (d / q) * q = d := Nat.div_mul_cancel hDiv
      have hMem : d / q ∈ R := by
        apply Finset.mem_range.mpr
        exact (Nat.div_le_self d q).trans_lt (Finset.mem_range.mp hd)
      have hfNZ : f (d / q) ≠ 0 := by
        intro hzero
        apply hNZ
        rw [← hMq, hLink, hzero]
      exact ⟨d / q, hMem, hfNZ, hMq⟩
    · intro m hm hNZ
      exact (hLink m).symm
  exact hEq

end ArtinPrimitiveRoots.Proofs.c_bins_sol
