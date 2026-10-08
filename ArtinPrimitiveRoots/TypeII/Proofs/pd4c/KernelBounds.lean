import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.ActiveKernel

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

theorem pd4c_bandFactor_bounds {K : ℕ} (F : PDFix K) (S : PDScale) (I : Finset (Fin K))
    (lo hi : ℝ) (hlo : 0 < lo) (hV : ∀ i, lo ≤ bandMass S.x (F.a i) ∧ bandMass S.x (F.a i) ≤ hi) :
    0 < pd4c_bandFactor F S I ∧ (min 1 lo) ^ K ≤ pd4c_bandFactor F S I ∧
      pd4c_bandFactor F S I ≤ (max 1 hi) ^ K := by
  have hm : 0 < min 1 lo := lt_min (by norm_num) hlo
  have hlow (i : Fin K) : min 1 lo ≤ if i ∈ I then bandMass S.x (F.a i) else 1 := by
    by_cases h : i ∈ I
    · rw [if_pos h]
      exact (min_le_right _ _).trans (hV i).1
    · rw [if_neg h]
      exact min_le_left _ _
  have hhigh (i : Fin K) : (if i ∈ I then bandMass S.x (F.a i) else 1) ≤ max 1 hi := by
    by_cases h : i ∈ I
    · rw [if_pos h]
      exact (hV i).2.trans (le_max_right _ _)
    · rw [if_neg h]
      exact le_max_left _ _
  have hpos (i : Fin K) : 0 < if i ∈ I then bandMass S.x (F.a i) else 1 :=
    lt_of_lt_of_le hm (hlow i)
  refine ⟨Finset.prod_pos (fun i hi => hpos i), ?_, ?_⟩
  · have h := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin K)))
      (fun i hi => hm.le) (fun i hi => hlow i)
    simpa only [pd4c_bandFactor, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  · have h := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin K)))
      (fun i hi => (hpos i).le) (fun i hi => hhigh i)
    simpa only [pd4c_bandFactor, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

/-- A fixed positive band-mass interval gives a uniform projected kernel-reversal bound. -/
theorem pd4c_memEdgePiece_kernel_transpose_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ)
    (s t : MemPoint S.x K) (hs : MemValid F S s) (ht : MemValid F S t)
    (lo hi : ℝ) (hlo : 0 < lo) (hV : ∀ i, lo ≤ bandMass S.x (F.a i) ∧ bandMass S.x (F.a i) ≤ hi)
    (hμs : 0 ≤ memMeasure F S s) (hμt : 0 ≤ memMeasure F S t)
    (hbands : ∀ i i' : Fin K, i ≠ i' → Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i'))) :
    memMeasure F S s *
      ‖memKernel (fun f => memEdgePiece F S ρ w raw St Pr j (memorySym f)) s t‖ ≤
    ((max 1 hi / min 1 lo) ^ K) * memMeasure F S t *
      ‖memKernel (fun f => memEdgePiece F S ρ w raw Pr St (j + 1) (memorySym f)) t s‖ := by
  have hm : 0 < min 1 lo := lt_min (by norm_num) hlo
  have hVi (i : Fin K) : bandMass S.x (F.a i) ≠ 0 := (lt_of_lt_of_le hlo (hV i).1).ne'
  obtain ⟨hPr, hPrLow, hPrHigh⟩ := pd4c_bandFactor_bounds F S Pr lo hi hlo hV
  obtain ⟨hSt, hStLow, hStHigh⟩ := pd4c_bandFactor_bounds F S St lo hi hlo hV
  have heq := pd4c_memEdgePiece_kernel_measure_transpose F S ρ w raw St Pr j s t hs ht hVi hbands
  have hn := congrArg norm heq
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hμs, abs_of_nonneg hμt, abs_of_pos hPr, abs_of_pos hSt] at hn
  let a := ‖memKernel (fun f => memEdgePiece F S ρ w raw St Pr j (memorySym f)) s t‖
  let b := ‖memKernel (fun f => memEdgePiece F S ρ w raw Pr St (j + 1) (memorySym f)) t s‖
  have hb : 0 ≤ memMeasure F S t * b := mul_nonneg hμt (norm_nonneg _)
  have hratio : pd4c_bandFactor F S St / pd4c_bandFactor F S Pr ≤ (max 1 hi / min 1 lo) ^ K := by
    calc
      _ ≤ (max 1 hi) ^ K / (min 1 lo) ^ K :=
        div_le_div₀ (pow_nonneg (by have h := le_max_left (1 : ℝ) hi; linarith) _) hStHigh
          (pow_pos hm _) hPrLow
      _ = _ := (div_pow _ _ _).symm
  calc
    memMeasure F S s * a = (pd4c_bandFactor F S St / pd4c_bandFactor F S Pr) *
        (memMeasure F S t * b) := by
      field_simp [hPr.ne']
      convert hn using 1 <;> dsimp [a, b] <;> ring
    _ ≤ ((max 1 hi / min 1 lo) ^ K) * (memMeasure F S t * b) :=
      mul_le_mul_of_nonneg_right hratio hb
    _ = _ := by ring

end

end ArtinPrimitiveRoots.TypeII.PD
