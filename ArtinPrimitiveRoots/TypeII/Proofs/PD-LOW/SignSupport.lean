import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- A supplied symmetric continuation equals its finite permutation average. -/
theorem pd5_memorySym_eq_self {x : ℝ} {K : ℕ} (f : MemPoint x K → ℂ)
    (hf : IsMemorySymmetric f) : memorySym f = f := by
  funext s
  have hc : (Fintype.card (MemoryPermutation s) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (MemoryPermutation s) ≠ 0)
  have hsum : (∑ σ : MemoryPermutation s, f (memoryPermute s σ)) =
      (Fintype.card (MemoryPermutation s) : ℂ) * f s := by
    calc
      _ = ∑ _σ : MemoryPermutation s, f s :=
        Finset.sum_congr rfl (fun σ _ => hf s σ)
      _ = _ := by simp
  change (Fintype.card (MemoryPermutation s) : ℂ)⁻¹ *
    (∑ σ : MemoryPermutation s, f (memoryPermute s σ)) = f s
  rw [hsum]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Reordering memory preserves its total size. -/
theorem pd5_memSize_memoryPermute {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) : memSize (memoryPermute s σ) = memSize s := by
  simp [memSize, memoryPermute]

/-- Every removed coordinate is counted once, including repeated equal particles. -/
theorem pd5_removeIndices_length_balance (l : List Particle)
    (D : Finset (Fin l.length)) : (removeIndices l D).length + D.card = l.length := by
  unfold removeIndices
  rw [List.length_filterMap_eq_countP]
  have hp : (fun k : Fin l.length =>
      (if k ∈ D then (none : Option Particle) else some (l.get k)).isSome) =
      (fun k => decide (k ∉ D)) := by
    funext k
    by_cases hk : k ∈ D <;> simp [hk]
  rw [hp]
  rw [← (List.nodup_finRange l.length).card_eq_countP (P := fun k => k ∉ D)]
  have hu : (List.finRange l.length).toFinset = Finset.univ := by
    ext k
    simp
  rw [hu]
  have hf : (Finset.univ.filter fun k : Fin l.length => k ∉ D) = Finset.univ \ D := by
    ext k
    simp
  rw [hf, Finset.card_sdiff_of_subset (Finset.subset_univ D)]
  have hD : D.card ≤ l.length := by simpa using Finset.card_le_univ D
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- The ghost's total birth/deletion balance follows from indexed list removal. -/
theorem pd5_ghost_output_size_balance {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → ℕ) :
    memSize (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
      List.ofFn fun k => anchorAt (new i k) s.1) + (∑ i, (D i).card) =
      memSize s + ∑ i, l i := by
  have hbalance (i : Fin K) :
      (removeIndices (s.2.2 i) (D i) ++
        List.ofFn fun k => anchorAt (new i k) s.1).length + (D i).card =
          (s.2.2 i).length + l i := by
    have h := pd5_removeIndices_length_balance (s.2.2 i) (D i)
    simp only [List.length_append, List.length_ofFn]
    omega
  simp only [memSize]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => hbalance i)

/-- Deletion-plus-birth parity is determined by the two endpoint sizes. All counts are
natural; the size balance is supplied before reasoning about truncated subtraction. -/
theorem pd5_ghost_sign_parity (source target deleted born : ℕ)
    (hbalance : target + deleted = source + born) :
    (-1 : ℝ) ^ (deleted + born) = (-1 : ℝ) ^ (source + target) := by
  have he : deleted + born + 2 * target = source + target + 2 * born := by omega
  have hpow := congrArg (fun n : ℕ => (-1 : ℝ) ^ n) he
  simpa [pow_add, pow_mul] using hpow

/-- The literal ghost coefficient splits into a parity sign and its nonnegative factors. -/
theorem pd5_ghostGroupCoeff_sign {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (j : ℕ) (i : Fin K) (hits deleted born : ℕ) (batch : List ℕ) :
    ghostGroupCoeff F S ρ j i hits deleted born batch =
      (-1 : ℝ) ^ (deleted + born) *
        ((memoryEta S.x F.q_d j / ρ) ^ deleted *
          (memoryQ S.x F.q_d j / ρ ^ 2) ^ (hits - deleted) *
          (memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ) ^ born /
            (born.factorial : ℝ) *
          (batch.map fun p => memoryNu S.x K F.a F.q_d i p).prod) := by
  unfold ghostGroupCoeff
  rw [neg_div, neg_mul, neg_div, neg_pow, neg_pow, pow_add]
  ring

/-- Bounded local phases cannot increase a finite sum whose real coefficients have one sign. -/
theorem pd5_common_sign_sum_domination {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (ε : ℂ) (hε : ‖ε‖ = 1)
    (W : ι → ℂ) (hW : ∀ i, ‖W i‖ ≤ 1) :
    ‖∑ i, ε * (a i : ℂ) * W i‖ ≤ ‖∑ i, ε * (a i : ℂ)‖ := by
  have hsum : (∑ i, ε * (a i : ℂ)) = ε * ((∑ i, a i : ℝ) : ℂ) := by
    simp [Finset.mul_sum]
  have hright : ‖∑ i, ε * (a i : ℂ)‖ = ∑ i, a i := by
    rw [hsum, norm_mul, hε, one_mul, Complex.norm_real]
    exact abs_of_nonneg (Finset.sum_nonneg fun i _ => ha i)
  rw [hright]
  calc
    _ ≤ ∑ i, ‖ε * (a i : ℂ) * W i‖ := norm_sum_le _ _
    _ ≤ ∑ i, a i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, norm_mul, hε, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha i)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hW i) (ha i)

end
end ArtinPrimitiveRoots.TypeII.PD
