import ArtinPrimitiveRoots.Sieve.Block.Global

namespace ArtinPrimitiveRoots.Sieve.Block

open Finset

theorem blockUProfileCoefficient_ne_zero_iff {α : Type*} [DecidableEq α]
    {N : ℕ} (B : Fin N → Finset α) (h : Fin N → ℕ) (D : Finset α) :
    blockUProfileCoefficient B h D ≠ 0 ↔
      ∀ j, (D ∩ B j).card ≤ h j := by
  classical
  rw [blockUProfileCoefficient, Finset.prod_ne_zero_iff]
  constructor
  · intro hprod j
    have hj := hprod j (Finset.mem_univ _)
    by_contra hnot
    simp [blockUProfileLocalCoefficient, hnot] at hj
  · intro hdeg j hj
    simpa [blockUProfileLocalCoefficient, hdeg j]

theorem blockTProfileCoefficient_ne_zero_iff {α : Type*} [DecidableEq α]
    {N : ℕ} (B : Fin N → Finset α) (h : Fin N → ℕ) (j : Fin N) (D : Finset α) :
    blockTProfileCoefficient B h j D ≠ 0 ↔
      (D ∩ B j).card = h j + 1 ∧
        ∀ k, k ≠ j → (D ∩ B k).card ≤ h k := by
  classical
  rw [blockTProfileCoefficient, Finset.prod_ne_zero_iff]
  constructor
  · intro hprod
    have hj := hprod j (Finset.mem_univ _)
    have hEq : (D ∩ B j).card = h j + 1 := by
      simpa [blockTProfileLocalCoefficient] using hj
    refine ⟨hEq, ?_⟩
    intro k hne
    have hk := hprod k (Finset.mem_univ _)
    simpa [hne, blockUProfileLocalCoefficient] using hk
  · rintro ⟨hEq, hdeg⟩ k hk
    by_cases hkj : k = j
    · subst k
      simp [blockTProfileLocalCoefficient, hEq]
    · simp [hkj, blockUProfileLocalCoefficient, hdeg k hkj]

theorem blockUProfileCoefficient_abs_le {α : Type*} [DecidableEq α]
    {N : ℕ} (B : Fin N → Finset α) (h : Fin N → ℕ) (D : Finset α) :
    |blockUProfileCoefficient B h D| ≤ 1 := by
  classical
  rw [blockUProfileCoefficient, Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro j hj
    exact abs_nonneg _
  · intro j hj
    by_cases hcard : (D ∩ B j).card ≤ h j
    · simpa [hcard]
    · simpa [hcard]

theorem blockTProfileCoefficient_abs_le {α : Type*} [DecidableEq α]
    {N : ℕ} (B : Fin N → Finset α) (h : Fin N → ℕ) (j : Fin N) (D : Finset α) :
    |blockTProfileCoefficient B h j D| ≤ 1 := by
  classical
  rw [blockTProfileCoefficient, Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro k hk
    exact abs_nonneg _
  · intro k hk
    by_cases hkj : k = j
    · subst k
      by_cases heq : (D ∩ B j).card = h j + 1
      · simpa [blockTProfileLocalCoefficient, heq]
      · simpa [blockTProfileLocalCoefficient, heq]
    · by_cases hdeg : (D ∩ B k).card ≤ h k
      · simpa [blockUProfileLocalCoefficient, hkj, hdeg]
      · simpa [blockUProfileLocalCoefficient, hkj, hdeg]

/-- A high degree in any block is outside the support of the corrected polynomial. -/
theorem blockLowerProfileCoefficient_eq_zero_of_big_degree {α : Type*} [DecidableEq α]
    {N : ℕ} (B : Fin N → Finset α) (h : Fin N → ℕ) (D : Finset α)
    (k : Fin N) (hbig : h k + 1 < (D ∩ B k).card) :
    blockLowerProfileCoefficient B h D = 0 := by
  classical
  have hu : blockUProfileCoefficient B h D = 0 := by
    unfold blockUProfileCoefficient
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [blockUProfileLocalCoefficient]
    omega
  have hv : ∀ j, blockTProfileCoefficient B h j D = 0 := by
    intro j
    unfold blockTProfileCoefficient
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases hkj : k = j
    · subst j
      simp [blockTProfileLocalCoefficient]
      omega
    · simp [hkj, blockUProfileLocalCoefficient]
      omega
  simp [blockLowerProfileCoefficient, hu, hv]

/-- The corrected coefficient has magnitude at most one: the one-block correction supports are
pairwise disjoint and are disjoint from the U support. -/
theorem blockLowerProfileCoefficient_abs_le {α : Type*} [DecidableEq α]
    {N : ℕ} (B : Fin N → Finset α) (h : Fin N → ℕ) (D : Finset α) :
    |blockLowerProfileCoefficient B h D| ≤ 1 := by
  classical
  let V : Finset (Fin N) := Finset.univ.filter
    (fun j => blockTProfileCoefficient B h j D ≠ 0)
  have hVcard : V.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro j k hj hk
    have hjprof := (blockTProfileCoefficient_ne_zero_iff B h j D).mp
      (Finset.mem_filter.mp hj).2
    have hkprof := (blockTProfileCoefficient_ne_zero_iff B h k D).mp
      (Finset.mem_filter.mp hk).2
    by_contra hne
    have hkj : k ≠ j := by
      intro heq
      exact hne heq.symm
    have hdeg := hjprof.2 k hkj
    omega
  have hVsum : (∑ j, blockTProfileCoefficient B h j D) =
      ∑ j ∈ V, blockTProfileCoefficient B h j D := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hnot
    have hzero : blockTProfileCoefficient B h j D = 0 := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    simp [hzero]
  have hVabs :
      |∑ j ∈ V, blockTProfileCoefficient B h j D| ≤ 1 := by
    calc
      |∑ j ∈ V, blockTProfileCoefficient B h j D| ≤
          ∑ j ∈ V, |blockTProfileCoefficient B h j D| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ V, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact blockTProfileCoefficient_abs_le B h j D
      _ = (V.card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hVcard
  by_cases hu : blockUProfileCoefficient B h D = 0
  · rw [blockLowerProfileCoefficient, hu, hVsum]
    simpa [abs_neg] using hVabs
  · have hdeg := (blockUProfileCoefficient_ne_zero_iff B h D).mp hu
    have hvzero : ∀ j, blockTProfileCoefficient B h j D = 0 := by
      intro j
      unfold blockTProfileCoefficient
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      have hle := hdeg j
      have hneq : (D ∩ B j).card ≠ h j + 1 := by omega
      simp [blockTProfileLocalCoefficient, hneq]
    have hsumzero : (∑ j, blockTProfileCoefficient B h j D) = 0 :=
      Finset.sum_eq_zero (fun j hj => hvzero j)
    rw [blockLowerProfileCoefficient, hsumzero]
    simpa using blockUProfileCoefficient_abs_le B h D

/-- The U coefficient polynomial has the product of its local Bernoulli expansions as main term. -/
theorem blockUProfile_main_eq {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (P : Finset α) (B : Fin N → Finset α) (h : Fin N → ℕ)
    (hBsub : ∀ k, B k ⊆ P) (hcover : ∀ x ∈ P, ∃ k, x ∈ B k)
    (hdisj : ∀ k l, k ≠ l → Disjoint (B k) (B l)) (g : α → ℝ) :
    (∑ D ∈ P.powerset,
      blockUProfileCoefficient B h D * ∏ p ∈ D, g p) =
      ∏ k, bernoulliBlockUExpansionOn (B k) g (h k) := by
  classical
  let c : Fin N → Finset α → ℝ := fun k D =>
    blockUProfileLocalCoefficient h k D
  have hreindex := product_block_subset_sums_eq P B hBsub hcover hdisj g c
  have hlocal : ∀ k,
      (∑ D ∈ (B k).powerset, c k D * ∏ p ∈ D, g p) =
        bernoulliBlockUExpansionOn (B k) g (h k) := by
    intro k
    simp [bernoulliBlockUExpansionOn, c, blockUProfileLocalCoefficient]
  calc
    (∑ D ∈ P.powerset,
      blockUProfileCoefficient B h D * ∏ p ∈ D, g p) =
        ∑ D ∈ P.powerset,
          (∏ k, c k (D ∩ B k)) * ∏ p ∈ D, g p := by
            apply Finset.sum_congr rfl
            intro D hD
            rfl
    _ = ∏ k, ∑ D ∈ (B k).powerset, c k D * ∏ p ∈ D, g p := hreindex.symm
    _ = ∏ k, bernoulliBlockUExpansionOn (B k) g (h k) := by
      apply Finset.prod_congr rfl
      intro k hk
      exact hlocal k

/-- The one-block correction coefficient sum is its elementary symmetric model mean. -/
theorem blockTProfileLocal_main_eq {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (g : α → ℝ) (h : ℕ) :
    (∑ D ∈ s.powerset,
      (if D.card = h + 1 then (1 : ℝ) else 0) * ∏ p ∈ D, g p) =
      bernoulliBlockTExpansionOn s g h := by
  classical
  unfold bernoulliBlockTExpansionOn
  calc
    (∑ D ∈ s.powerset,
      (if D.card = h + 1 then (1 : ℝ) else 0) * ∏ p ∈ D, g p) =
        ∑ D ∈ s.powerset, if D.card = h + 1 then ∏ p ∈ D, g p else 0 := by
          apply Finset.sum_congr rfl
          intro D hD
          split_ifs <;> simp
    _ = ∑ D ∈ (s.powerset).filter (fun D => D.card = h + 1),
        ∏ p ∈ D, g p := by rw [← Finset.sum_filter]
    _ = ∑ D ∈ s.powersetCard (h + 1), ∏ p ∈ D, g p := by
      rw [← Finset.powersetCard_eq_filter]

/-- A product with one correction coefficient has the corresponding product of local model sums. -/
theorem blockTProfile_main_eq {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (P : Finset α) (B : Fin N → Finset α) (h : Fin N → ℕ)
    (hBsub : ∀ k, B k ⊆ P) (hcover : ∀ x ∈ P, ∃ k, x ∈ B k)
    (hdisj : ∀ k l, k ≠ l → Disjoint (B k) (B l))
    (g : α → ℝ) (j : Fin N) :
    (∑ D ∈ P.powerset,
      blockTProfileCoefficient B h j D * ∏ p ∈ D, g p) =
      bernoulliBlockTExpansionOn (B j) g (h j) *
        ∏ k ∈ Finset.univ.erase j, bernoulliBlockUExpansionOn (B k) g (h k) := by
  classical
  let c : Fin N → Finset α → ℝ := fun k D =>
    if k = j then blockTProfileLocalCoefficient h j D
      else blockUProfileLocalCoefficient h k D
  have hreindex := product_block_subset_sums_eq P B hBsub hcover hdisj g c
  have hlocal : ∀ k,
      (∑ D ∈ (B k).powerset, c k D * ∏ p ∈ D, g p) =
        if k = j then bernoulliBlockTExpansionOn (B k) g (h k)
        else bernoulliBlockUExpansionOn (B k) g (h k) := by
    intro k
    by_cases hkj : k = j
    · subst k
      dsimp only [c, blockTProfileLocalCoefficient]
      simp only [if_pos rfl]
      exact blockTProfileLocal_main_eq (B j) g (h j)
    · simp [c, hkj, bernoulliBlockUExpansionOn, blockUProfileLocalCoefficient]
  have hfactor : (∏ k,
      if k = j then bernoulliBlockTExpansionOn (B k) g (h k)
      else bernoulliBlockUExpansionOn (B k) g (h k)) =
      bernoulliBlockTExpansionOn (B j) g (h j) *
        ∏ k ∈ Finset.univ.erase j, bernoulliBlockUExpansionOn (B k) g (h k) := by
    have herase :
        (∏ k ∈ Finset.univ.erase j,
          if k = j then bernoulliBlockTExpansionOn (B k) g (h k)
          else bernoulliBlockUExpansionOn (B k) g (h k)) =
        ∏ k ∈ Finset.univ.erase j, bernoulliBlockUExpansionOn (B k) g (h k) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hne : k ≠ j := (Finset.mem_erase.mp hk).1
      simp [hne]
    calc
      (∏ k, if k = j then bernoulliBlockTExpansionOn (B k) g (h k)
          else bernoulliBlockUExpansionOn (B k) g (h k)) =
          (if j = j then bernoulliBlockTExpansionOn (B j) g (h j)
            else bernoulliBlockUExpansionOn (B j) g (h j)) *
            ∏ k ∈ Finset.univ.erase j,
              (if k = j then bernoulliBlockTExpansionOn (B k) g (h k)
                else bernoulliBlockUExpansionOn (B k) g (h k)) :=
        (Finset.mul_prod_erase Finset.univ
          (fun k => if k = j then bernoulliBlockTExpansionOn (B k) g (h k)
            else bernoulliBlockUExpansionOn (B k) g (h k)) (Finset.mem_univ j)).symm
      _ = bernoulliBlockTExpansionOn (B j) g (h j) *
            ∏ k ∈ Finset.univ.erase j, bernoulliBlockUExpansionOn (B k) g (h k) := by
          rw [herase]
          simp
  calc
    (∑ D ∈ P.powerset,
      blockTProfileCoefficient B h j D * ∏ p ∈ D, g p) =
        ∏ k, ∑ D ∈ (B k).powerset, c k D * ∏ p ∈ D, g p := by
          apply hreindex.symm
    _ = ∏ k, if k = j then bernoulliBlockTExpansionOn (B k) g (h k)
          else bernoulliBlockUExpansionOn (B k) g (h k) := by
            apply Finset.prod_congr rfl
            intro k hk
            exact hlocal k
    _ = bernoulliBlockTExpansionOn (B j) g (h j) *
          ∏ k ∈ Finset.univ.erase j, bernoulliBlockUExpansionOn (B k) g (h k) := hfactor

/-- The main term of the corrected global polynomial is the product U mean minus its blockwise
next-degree corrections. -/
theorem blockLowerProfile_main_eq {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (P : Finset α) (B : Fin N → Finset α) (h : Fin N → ℕ)
    (hBsub : ∀ k, B k ⊆ P) (hcover : ∀ x ∈ P, ∃ k, x ∈ B k)
    (hdisj : ∀ k l, k ≠ l → Disjoint (B k) (B l)) (g : α → ℝ) :
    (∑ D ∈ P.powerset,
      blockLowerProfileCoefficient B h D * ∏ p ∈ D, g p) =
      (∏ k, bernoulliBlockUExpansionOn (B k) g (h k)) -
        ∑ j, bernoulliBlockTExpansionOn (B j) g (h j) *
          ∏ k ∈ Finset.univ.erase j, bernoulliBlockUExpansionOn (B k) g (h k) := by
  classical
  have hmainU := blockUProfile_main_eq P B h hBsub hcover hdisj g
  have hmainT : ∀ j,
      (∑ D ∈ P.powerset,
        blockTProfileCoefficient B h j D * ∏ p ∈ D, g p) =
        bernoulliBlockTExpansionOn (B j) g (h j) *
          ∏ k ∈ Finset.univ.erase j, bernoulliBlockUExpansionOn (B k) g (h k) := by
    intro j
    exact blockTProfile_main_eq P B h hBsub hcover hdisj g j
  let correctionTerm : Finset α → ℝ := fun D =>
    (∑ j, blockTProfileCoefficient B h j D) * ∏ p ∈ D, g p
  have hterm (D : Finset α) :
      blockLowerProfileCoefficient B h D * ∏ p ∈ D, g p =
        blockUProfileCoefficient B h D * ∏ p ∈ D, g p - correctionTerm D := by
    dsimp [blockLowerProfileCoefficient, correctionTerm]
    ring

  have hCorrDist :
      (∑ D ∈ P.powerset, correctionTerm D) =
        ∑ j, ∑ D ∈ P.powerset,
          blockTProfileCoefficient B h j D * ∏ p ∈ D, g p := by
    calc
      (∑ D ∈ P.powerset, correctionTerm D) =
          ∑ D ∈ P.powerset,
            (∑ j, blockTProfileCoefficient B h j D) * ∏ p ∈ D, g p := by
              rfl
      _ = ∑ D ∈ P.powerset, ∑ j,
            blockTProfileCoefficient B h j D * ∏ p ∈ D, g p := by
              apply Finset.sum_congr rfl
              intro D hD
              rw [Finset.sum_mul]
      _ = ∑ j, ∑ D ∈ P.powerset,
            blockTProfileCoefficient B h j D * ∏ p ∈ D, g p := Finset.sum_comm
  have hsplit :
      (∑ D ∈ P.powerset,
        blockLowerProfileCoefficient B h D * ∏ p ∈ D, g p) =
        (∑ D ∈ P.powerset, blockUProfileCoefficient B h D * ∏ p ∈ D, g p) -
          ∑ j, ∑ D ∈ P.powerset,
            blockTProfileCoefficient B h j D * ∏ p ∈ D, g p := by
    calc
      (∑ D ∈ P.powerset,
        blockLowerProfileCoefficient B h D * ∏ p ∈ D, g p) =
          Finset.sum P.powerset (fun D =>
            blockUProfileCoefficient B h D * ∏ p ∈ D, g p - correctionTerm D) := by
                apply Finset.sum_congr rfl
                intro D hD
                exact hterm D
      _ = (∑ D ∈ P.powerset, blockUProfileCoefficient B h D * ∏ p ∈ D, g p) -
            Finset.sum P.powerset correctionTerm :=
        by rw [Finset.sum_sub_distrib]
      _ = (∑ D ∈ P.powerset, blockUProfileCoefficient B h D * ∏ p ∈ D, g p) -
            ∑ j, ∑ D ∈ P.powerset,
              blockTProfileCoefficient B h j D * ∏ p ∈ D, g p := by
        rw [hCorrDist]
  calc
    (∑ D ∈ P.powerset,
      blockLowerProfileCoefficient B h D * ∏ p ∈ D, g p) =
        (∑ D ∈ P.powerset, blockUProfileCoefficient B h D * ∏ p ∈ D, g p) -
          ∑ j, ∑ D ∈ P.powerset,
            blockTProfileCoefficient B h j D * ∏ p ∈ D, g p := hsplit
    _ = (∏ k, bernoulliBlockUExpansionOn (B k) g (h k)) -
          ∑ j, bernoulliBlockTExpansionOn (B j) g (h j) *
            ∏ k ∈ Finset.univ.erase j, bernoulliBlockUExpansionOn (B k) g (h k) := by
      rw [hmainU]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact hmainT j

end ArtinPrimitiveRoots.Sieve.Block
