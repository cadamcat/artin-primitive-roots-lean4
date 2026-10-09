import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.RawChoices

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- The total modified mass of finite fresh draws has no memory-cutoff cost. -/
theorem raw_fresh_nu_mass_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (I : Finset (Fin K))
    (hν : ∀ i, ∀ p : primeBand S.x (F.a i),
      0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hνsum : ∀ i, (∑ p : primeBand S.x (F.a i),
      memoryNu S.x K F.a F.q_d i p) ≤ 2) :
    (∑ fresh : RawFreshLabels S.x F.a I,
      ∏ i : Fin K, if i ∉ I then
        memoryNu S.x K F.a F.q_d i (rawFreshFunction S.x F.a I fresh i)
      else 1) ≤ (2 : ℝ) ^ K := by
  let J : Finset (Fin K) := Iᶜ
  let ν (i : J) (p : primeBand S.x (F.a i.1)) : ℝ :=
    memoryNu S.x K F.a F.q_d i.1 p
  have hpoint (fresh : RawFreshLabels S.x F.a I) :
      (∏ i : Fin K, if i ∉ I then
        memoryNu S.x K F.a F.q_d i (rawFreshFunction S.x F.a I fresh i) else 1) =
      ∏ i : J, ν i (fresh i) := by
    calc
      _ = ∏ i : Fin K, if i ∈ J then
          memoryNu S.x K F.a F.q_d i (rawFreshFunction S.x F.a I fresh i) else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [J, Finset.mem_compl]
      _ = ∏ i : J,
          memoryNu S.x K F.a F.q_d i.1 (rawFreshFunction S.x F.a I fresh i.1) := by
        rw [Finset.prod_ite_mem_eq]
        exact (Finset.prod_coe_sort J (fun i : Fin K =>
          memoryNu S.x K F.a F.q_d i (rawFreshFunction S.x F.a I fresh i))).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i hi
        have hnot : i.1 ∉ I := Finset.mem_compl.mp i.2
        have harg :
            (⟨i.1, Finset.mem_compl.mpr hnot⟩ : (Iᶜ : Finset (Fin K))) = i :=
          Subtype.ext rfl
        simp only [ν, rawFreshFunction, dif_neg hnot]
        exact congrArg (fun p : ℕ => memoryNu S.x K F.a F.q_d i.1 p)
          (congrArg (fun k : (Iᶜ : Finset (Fin K)) => (fresh k : ℕ)) harg)
  have hcard : J.card ≤ K := by simpa using Finset.card_le_univ J
  calc
    _ = ∑ fresh : RawFreshLabels S.x F.a I, ∏ i : J, ν i (fresh i) := by
      exact Finset.sum_congr rfl (fun fresh hfresh => hpoint fresh)
    _ = ∏ i : J, ∑ p : primeBand S.x (F.a i.1), ν i p := by
      rw [← Fintype.piFinset_univ]
      simpa using (Finset.prod_univ_sum
        (fun i : J => (Finset.univ : Finset (primeBand S.x (F.a i.1)))) ν).symm
    _ ≤ ∏ _i : J, (2 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg (fun p hp => hν i.1 p)
      · intro i hi
        exact hνsum i.1
    _ = (2 : ℝ) ^ J.card := by simp
    _ ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hcard

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
