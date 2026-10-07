import ArtinPrimitiveRoots.Sieve.Block.Combinatorics
import ArtinPrimitiveRoots.Sieve.Block.Model

namespace ArtinPrimitiveRoots.Sieve.Block

open Finset

/-- The coordinates selected as bad by a Boolean assignment. -/
def selectedBad {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → Bool) : Finset ι :=
  Finset.univ.filter (fun i => x i = true)

/-- The selected bad coordinates inside a specified block. -/
def selectedBadOn {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → Bool) : Finset ι :=
  s.filter (fun i => x i = true)

/-- The exact avoidance indicator for an assignment, in product form. -/
theorem selectedBad_avoid_indicator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) :
    (if (selectedBad x).card = 0 then (1 : ℝ) else 0) =
      ∏ i, if x i then (0 : ℝ) else 1 := by
  classical
  have hprod : (∏ i, if x i then (0 : ℝ) else 1) =
      if ∀ i, x i = false then 1 else 0 := by
    calc
      _ = ∏ i ∈ (Finset.univ : Finset ι), if x i = false then (1 : ℝ) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        cases x i <;> rfl
      _ = _ := by
        simpa using (Finset.prod_ite_zero (s := (Finset.univ : Finset ι))
          (p := fun i => x i = false) (f := fun _ => (1 : ℝ)))
  rw [hprod]
  simp [selectedBad]

/-- A block polynomial can be expanded over the full ambient powerset, with zero outside the
selected bad coordinates. -/
theorem blockU_eq_fullSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (h : ℕ) :
    blockU s h =
      ∑ D ∈ (Finset.univ : Finset ι).powerset,
        if D.card ≤ h ∧ D ⊆ s then (-1 : ℝ) ^ D.card else 0 := by
  classical
  unfold blockU
  rw [Finset.sum_filter]
  calc
    _ = ∑ D ∈ s.powerset,
        if D.card ≤ h ∧ D ⊆ s then (-1 : ℝ) ^ D.card else 0 := by
      apply Finset.sum_congr rfl
      intro D hD
      simp [Finset.mem_powerset.mp hD]
    _ = ∑ D ∈ (Finset.univ : Finset ι).powerset,
        if D.card ≤ h ∧ D ⊆ s then (-1 : ℝ) ^ D.card else 0 := by
      apply Finset.sum_subset
        (Finset.powerset_mono.mpr (Finset.subset_univ s))
      intro D hD hnot
      have hDs : ¬ D ⊆ s := by
        intro hs
        exact hnot (Finset.mem_powerset.mpr hs)
      simp [hDs]

/-- The product of Boolean indicators records whether a subset is selected. -/
theorem selectedBad_subset_indicator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Finset ι) (x : ι → Bool) :
    (if D ⊆ selectedBad x then (1 : ℝ) else 0) =
      ∏ i ∈ D, if x i then (1 : ℝ) else 0 := by
  classical
  have hprod : (∏ i ∈ D, if x i then (1 : ℝ) else 0) =
      if ∀ i ∈ D, x i = true then 1 else 0 := by
    calc
      _ = ∏ i ∈ D, if x i = true then (1 : ℝ) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        cases x i <;> rfl
      _ = _ := by
        rw [Finset.prod_boole]
        split_ifs <;> rfl
  rw [hprod]
  simp [selectedBad, Finset.subset_iff]

/-- The product indicator records whether a subset lies in the selected part of a block. -/
theorem selectedBadOn_subset_indicator {ι : Type*} [DecidableEq ι]
    (s D : Finset ι) (x : ι → Bool) :
    (if D ⊆ selectedBadOn s x then (1 : ℝ) else 0) =
      ∏ i ∈ D, if i ∈ s ∧ x i = true then (1 : ℝ) else 0 := by
  classical
  have hprod' : (∏ i ∈ D, if i ∈ s ∧ x i = true then (1 : ℝ) else 0) =
      if ∀ i ∈ D, i ∈ s ∧ x i = true then 1 else 0 := by
    calc
      _ = ∏ i ∈ D, if i ∈ s ∧ x i = true then (1 : ℝ) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases his : i ∈ s <;> cases x i <;> simp [his]
      _ = _ := by rw [Finset.prod_boole]
  rw [hprod']
  simp [selectedBadOn, Finset.subset_iff]

/-- The selected-set block polynomial as a squarefree polynomial on all coordinates. -/
theorem blockU_selected_fullSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) (h : ℕ) :
    blockU (selectedBad x) h =
      ∑ D ∈ (Finset.univ : Finset ι).powerset,
        if D.card ≤ h then (-1 : ℝ) ^ D.card *
          (∏ i ∈ D, if x i then (1 : ℝ) else 0) else 0 := by
  classical
  rw [blockU_eq_fullSupport]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hc : D.card ≤ h
  · by_cases hs : D ⊆ selectedBad x
    · have hp : (∏ i ∈ D, if x i then (1 : ℝ) else 0) = 1 := by
        simpa [hs] using (selectedBad_subset_indicator D x).symm
      simp [hc, hs, hp]
    · have hp : (∏ i ∈ D, if x i then (1 : ℝ) else 0) = 0 := by
        simpa [hs] using (selectedBad_subset_indicator D x).symm
      simp [hc, hs, hp]
  · simp [hc]

/-- A block polynomial is supported only on subsets of its block. -/
theorem blockU_selectedOn_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (x : ι → Bool) (h : ℕ) :
    blockU (selectedBadOn s x) h =
      ∑ D ∈ s.powerset,
        if D.card ≤ h then (-1 : ℝ) ^ D.card *
          (∏ i ∈ D, if x i then (1 : ℝ) else 0) else 0 := by
  classical
  rw [blockU_eq_fullSupport]
  rw [← Finset.sum_subset (Finset.powerset_mono.mpr (Finset.subset_univ s))]
  · apply Finset.sum_congr rfl
    intro D hD
    have hsub := Finset.mem_powerset.mp hD
    have hprodEq : (∏ i ∈ D, if x i then (1 : ℝ) else 0) =
        ∏ i ∈ D, if i ∈ s ∧ x i = true then (1 : ℝ) else 0 := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [hsub hi]
    by_cases hc : D.card ≤ h
    · by_cases hs : D ⊆ selectedBadOn s x
      · have hp : (∏ i ∈ D, if x i then (1 : ℝ) else 0) = 1 := by
          exact hprodEq.trans
            (by simpa [hs] using (selectedBadOn_subset_indicator s D x).symm)
        simp [hc, hs, hp]
      · have hp : (∏ i ∈ D, if x i then (1 : ℝ) else 0) = 0 := by
          exact hprodEq.trans
            (by simpa [hs] using (selectedBadOn_subset_indicator s D x).symm)
        simp [hc, hs, hp]
    · simp [hc]
  · intro D hD hnot
    have hDs : ¬ D ⊆ s := by
      intro hsub
      exact hnot (Finset.mem_powerset.mpr hsub)
    have hnotSelected : ¬ D ⊆ selectedBadOn s x := by
      intro hsub
      exact hDs (Finset.Subset.trans hsub (Finset.filter_subset _ _))
    simp [hnotSelected]

/-- The expected value of one even block polynomial. -/
noncomputable def bernoulliBlockUMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (h : ℕ) : ℝ :=
  bernoulliExpectation g (fun x => blockU (selectedBad x) h)

/-- The squarefree coefficient expansion of the expected even block polynomial. -/
noncomputable def bernoulliBlockUExpansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (h : ℕ) : ℝ :=
  ∑ D ∈ (Finset.univ : Finset ι).powerset,
    if D.card ≤ h then (-1 : ℝ) ^ D.card * ∏ i ∈ D, g i else 0

/-- The independent-model mean of a block polynomial is its squarefree coefficient sum. -/
theorem bernoulliBlockUMean_eq_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (h : ℕ) : bernoulliBlockUMean g h = bernoulliBlockUExpansion g h := by
  classical
  unfold bernoulliBlockUMean bernoulliBlockUExpansion bernoulliExpectation
  calc
    (∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
        bernoulliWeight g x * blockU (selectedBad x) h) =
      ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
        ∑ D ∈ (Finset.univ : Finset ι).powerset,
          bernoulliWeight g x * (if D.card ≤ h then (-1 : ℝ) ^ D.card *
            (∏ i ∈ D, if x i then (1 : ℝ) else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [blockU_selected_fullSupport]
      rw [Finset.mul_sum]
    _ = ∑ D ∈ (Finset.univ : Finset ι).powerset,
        ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
          bernoulliWeight g x * (if D.card ≤ h then (-1 : ℝ) ^ D.card *
            (∏ i ∈ D, if x i then (1 : ℝ) else 0) else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ D ∈ (Finset.univ : Finset ι).powerset,
        if D.card ≤ h then (-1 : ℝ) ^ D.card * ∏ i ∈ D, g i else 0 := by
      apply Finset.sum_congr rfl
      intro D hD
      by_cases hc : D.card ≤ h
      · simp [hc]
        calc
          (∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
              bernoulliWeight g x * ((-1 : ℝ) ^ D.card *
                (∏ i ∈ D, if x i then (1 : ℝ) else 0))) =
            (-1 : ℝ) ^ D.card * bernoulliExpectation g
              (fun x => ∏ i ∈ D, if x i then (1 : ℝ) else 0) := by
              unfold bernoulliExpectation
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              ring
          _ = (-1 : ℝ) ^ D.card * ∏ i ∈ D, g i := by
              rw [bernoulliExpectation_monomial_eq]
      · simp [hc]

/-- The probability of avoiding a specified subset of coordinates is its product density. -/
theorem bernoulliExpectation_avoidanceOn_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) :
    bernoulliExpectation g (fun x => ∏ i ∈ s, if x i then (0 : ℝ) else 1) =
      ∏ i ∈ s, (1 - g i) := by
  classical
  unfold bernoulliExpectation bernoulliWeight
  calc
    (∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
        (∏ i, if x i then g i else 1 - g i) *
          (∏ i ∈ s, if x i then (0 : ℝ) else 1)) =
      ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
        ∏ i, (if x i then g i else 1 - g i) *
          if i ∈ s then (if x i then (0 : ℝ) else 1) else 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hsub : (∏ i ∈ s, if x i then (0 : ℝ) else 1) =
          ∏ i, if i ∈ s then (if x i then (0 : ℝ) else 1) else 1 := by
        simpa [Finset.univ_inter] using
          (Finset.prod_ite_mem s (fun i => if x i then (0 : ℝ) else 1)).symm
      rw [hsub, ← Finset.prod_mul_distrib]
    _ = ∏ i : ι,
        ∑ b ∈ (Finset.univ : Finset Bool),
          (if b then g i else 1 - g i) *
            if i ∈ s then (if b then (0 : ℝ) else 1) else 1 := by
      rw [Finset.sum_prod_piFinset
        (s := (Finset.univ : Finset Bool))
        (g := fun (i : ι) b => (if b then g i else 1 - g i) *
          if i ∈ s then (if b then (0 : ℝ) else 1) else 1)]
    _ = ∏ i ∈ (Finset.univ : Finset ι), if i ∈ s then (1 - g i) else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases his : i ∈ s <;> simp [his]
    _ = ∏ i ∈ s, (1 - g i) := by
      rw [← Finset.prod_filter]
      simp

/-- The exact no-bad indicator within a block is the product of its local indicators. -/
theorem selectedBadOn_avoid_indicator {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → Bool) :
    (if (selectedBadOn s x).card = 0 then (1 : ℝ) else 0) =
      ∏ i ∈ s, if x i then (0 : ℝ) else 1 := by
  classical
  have hprod : (∏ i ∈ s, if x i then (0 : ℝ) else 1) =
      if ∀ i ∈ s, x i = false then 1 else 0 := by
    calc
      _ = ∏ i ∈ s, if x i = false then (1 : ℝ) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        cases x i <;> rfl
      _ = _ := by
        rw [Finset.prod_ite_zero]
        split_ifs <;> simp
  rw [hprod]
  simp [selectedBadOn]

/-- Expected inclusion-exclusion polynomial for a specified finite block. -/
noncomputable def bernoulliBlockUMeanOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (h : ℕ) : ℝ :=
  bernoulliExpectation g (fun x => blockU (selectedBadOn s x) h)

/-- The squarefree coefficient sum for a specified block. -/
noncomputable def bernoulliBlockUExpansionOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (h : ℕ) : ℝ :=
  ∑ D ∈ s.powerset, if D.card ≤ h then (-1 : ℝ) ^ D.card * ∏ i ∈ D, g i else 0

/-- The expected value of a block polynomial is its squarefree coefficient sum on that block. -/
theorem bernoulliBlockUMeanOn_eq_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (h : ℕ) :
    bernoulliBlockUMeanOn s g h = bernoulliBlockUExpansionOn s g h := by
  classical
  unfold bernoulliBlockUMeanOn bernoulliBlockUExpansionOn bernoulliExpectation
  calc
    (∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
        bernoulliWeight g x * blockU (selectedBadOn s x) h) =
      ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
        ∑ D ∈ s.powerset,
          bernoulliWeight g x * (if D.card ≤ h then (-1 : ℝ) ^ D.card *
            (∏ i ∈ D, if x i then (1 : ℝ) else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [blockU_selectedOn_support, Finset.mul_sum]
    _ = ∑ D ∈ s.powerset,
        ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
          bernoulliWeight g x * (if D.card ≤ h then (-1 : ℝ) ^ D.card *
            (∏ i ∈ D, if x i then (1 : ℝ) else 0) else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ D ∈ s.powerset,
        if D.card ≤ h then (-1 : ℝ) ^ D.card * ∏ i ∈ D, g i else 0 := by
      apply Finset.sum_congr rfl
      intro D hD
      by_cases hc : D.card ≤ h
      · simp [hc]
        calc
          (∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
              bernoulliWeight g x * ((-1 : ℝ) ^ D.card *
                (∏ i ∈ D, if x i then (1 : ℝ) else 0))) =
            (-1 : ℝ) ^ D.card * bernoulliExpectation g
              (fun x => ∏ i ∈ D, if x i then (1 : ℝ) else 0) := by
              unfold bernoulliExpectation
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              ring
          _ = (-1 : ℝ) ^ D.card * ∏ i ∈ D, g i := by
              rw [bernoulliExpectation_monomial_eq]
      · simp [hc]

/-- The next-degree correction is supported on the cardinality layer inside its block. -/
theorem blockT_eq_fullSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (h : ℕ) :
    blockT s h =
      ∑ D ∈ (Finset.univ : Finset ι).powersetCard (h + 1),
        if D ⊆ s then (1 : ℝ) else 0 := by
  classical
  unfold blockT
  have hset : s.powersetCard (h + 1) =
      ((Finset.univ : Finset ι).powersetCard (h + 1)).filter (fun D => D ⊆ s) := by
    ext D
    simp [Finset.mem_powersetCard, and_comm]
  rw [hset]
  have hcard : ((((Finset.univ : Finset ι).powersetCard (h + 1)).filter
      (fun D => D ⊆ s)).card) =
      ∑ D ∈ ((Finset.univ : Finset ι).powersetCard (h + 1)).filter
        (fun D => D ⊆ s), (1 : ℕ) := by
    exact Finset.card_eq_sum_ones _
  rw [hcard]
  norm_cast
  rw [← Finset.sum_filter]

theorem blockT_selectedOn_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (x : ι → Bool) (h : ℕ) :
    blockT (selectedBadOn s x) h =
      ∑ D ∈ s.powersetCard (h + 1), ∏ i ∈ D, if x i then (1 : ℝ) else 0 := by
  classical
  rw [blockT_eq_fullSupport]
  calc
    (∑ D ∈ (Finset.univ : Finset ι).powersetCard (h + 1),
        if D ⊆ selectedBadOn s x then (1 : ℝ) else 0) =
      ∑ D ∈ s.powersetCard (h + 1),
        if D ⊆ selectedBadOn s x then (1 : ℝ) else 0 := by
      symm
      apply Finset.sum_subset
        (Finset.powersetCard_mono (Finset.subset_univ s))
      intro D hD hnot
      have hDs : ¬ D ⊆ selectedBadOn s x := by
        intro hsub
        apply hnot
        exact Finset.mem_powersetCard.mpr
          ⟨hsub.trans (Finset.filter_subset _ _), (Finset.mem_powersetCard.mp hD).2⟩
      simp [hDs]
    _ = ∑ D ∈ s.powersetCard (h + 1),
        ∏ i ∈ D, if x i then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro D hD
      have hDs := Finset.mem_powersetCard.mp hD
      calc
        (if D ⊆ selectedBadOn s x then (1 : ℝ) else 0) =
            ∏ i ∈ D, if i ∈ s ∧ x i = true then (1 : ℝ) else 0 :=
          selectedBadOn_subset_indicator s D x
        _ = ∏ i ∈ D, if x i then (1 : ℝ) else 0 := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [hDs.1 hi]

/-- The model mean of a specified block's correction. -/
noncomputable def bernoulliBlockTMeanOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (h : ℕ) : ℝ :=
  bernoulliExpectation g (fun x => blockT (selectedBadOn s x) h)

/-- The coefficient expansion of the mean correction on a specified block. -/
noncomputable def bernoulliBlockTExpansionOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (h : ℕ) : ℝ :=
  ∑ D ∈ s.powersetCard (h + 1), ∏ i ∈ D, g i

/-- The model mean correction is its elementary symmetric sum. -/
theorem bernoulliBlockTMeanOn_eq_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (h : ℕ) :
    bernoulliBlockTMeanOn s g h = bernoulliBlockTExpansionOn s g h := by
  classical
  unfold bernoulliBlockTMeanOn bernoulliBlockTExpansionOn bernoulliExpectation
  calc
    (∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
        bernoulliWeight g x * blockT (selectedBadOn s x) h) =
      ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
        ∑ D ∈ s.powersetCard (h + 1),
          bernoulliWeight g x * ∏ i ∈ D, if x i then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [blockT_selectedOn_support, Finset.mul_sum]
    _ = ∑ D ∈ s.powersetCard (h + 1),
        ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
          bernoulliWeight g x * ∏ i ∈ D, if x i then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ D ∈ s.powersetCard (h + 1), ∏ i ∈ D, g i := by
      apply Finset.sum_congr rfl
      intro D hD
      exact bernoulliExpectation_monomial_eq g D

/-- Averaging the pointwise block Bonferroni inequalities under the ambient finite model. -/
theorem bernoulliBlockOn_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (h : ℕ) (hh : Even h)
    (hg : ∀ i, 0 ≤ g i ∧ g i ≤ 1) :
    (∏ i ∈ s, (1 - g i)) ≤ bernoulliBlockUMeanOn s g h ∧
      bernoulliBlockUMeanOn s g h - (∏ i ∈ s, (1 - g i)) ≤ bernoulliBlockTMeanOn s g h := by
  classical
  let I : (ι → Bool) → ℝ := fun x => ∏ i ∈ s, if x i then (0 : ℝ) else 1
  let U : (ι → Bool) → ℝ := fun x => blockU (selectedBadOn s x) h
  let T : (ι → Bool) → ℝ := fun x => blockT (selectedBadOn s x) h
  have havoid : bernoulliExpectation g I = ∏ i ∈ s, (1 - g i) := by
    simpa [I] using bernoulliExpectation_avoidanceOn_eq s g
  have hIU : ∀ x, I x ≤ U x := by
    intro x
    change (∏ i ∈ s, if x i then (0 : ℝ) else 1) ≤ blockU (selectedBadOn s x) h
    rw [← selectedBadOn_avoid_indicator s x]
    exact blockU_ge_avoid (selectedBadOn s x) hh
  have hgap : ∀ x, U x - I x ≤ T x := by
    intro x
    change blockU (selectedBadOn s x) h -
        (∏ i ∈ s, if x i then (0 : ℝ) else 1) ≤ blockT (selectedBadOn s x) h
    rw [← selectedBadOn_avoid_indicator s x]
    exact blockU_sub_avoid_le_T (selectedBadOn s x) hh
  have hlow := bernoulliExpectation_mono g I U hg hIU
  have hlin : bernoulliExpectation g (fun x => U x - I x) =
      bernoulliBlockUMeanOn s g h - bernoulliExpectation g I := by
    simp only [bernoulliExpectation, bernoulliBlockUMeanOn, bernoulliWeight]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  have hhigh := bernoulliExpectation_mono g (fun x => U x - I x) T hg hgap
  constructor
  · simpa [havoid, U, bernoulliBlockUMeanOn] using hlow
  · rw [hlin, havoid] at hhigh
    have hT : bernoulliExpectation g T = bernoulliBlockTMeanOn s g h := rfl
    rw [hT] at hhigh
    linarith

/-- The next-degree correction evaluated on a Boolean assignment. -/
theorem blockT_selected_fullSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) (h : ℕ) :
    blockT (selectedBad x) h =
      ∑ D ∈ (Finset.univ : Finset ι).powersetCard (h + 1),
        ∏ i ∈ D, if x i then (1 : ℝ) else 0 := by
  classical
  rw [blockT_eq_fullSupport]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs : D ⊆ selectedBad x
  · have hp : (∏ i ∈ D, if x i then (1 : ℝ) else 0) = 1 := by
      simpa [hs] using (selectedBad_subset_indicator D x).symm
    simp [hs, hp]
  · have hp : (∏ i ∈ D, if x i then (1 : ℝ) else 0) = 0 := by
      simpa [hs] using (selectedBad_subset_indicator D x).symm
    simp [hs, hp]

/-- The expected value of one block's next-degree correction. -/
noncomputable def bernoulliBlockTMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (h : ℕ) : ℝ :=
  bernoulliExpectation g (fun x => blockT (selectedBad x) h)

/-- The coefficient expansion of the expected next-degree correction. -/
noncomputable def bernoulliBlockTExpansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (h : ℕ) : ℝ :=
  ∑ D ∈ (Finset.univ : Finset ι).powersetCard (h + 1), ∏ i ∈ D, g i

/-- The mean of the next-degree correction is the corresponding elementary symmetric sum. -/
theorem bernoulliBlockTMean_eq_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (h : ℕ) : bernoulliBlockTMean g h = bernoulliBlockTExpansion g h := by
  classical
  unfold bernoulliBlockTMean bernoulliBlockTExpansion bernoulliExpectation
  calc
    (∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
        bernoulliWeight g x * blockT (selectedBad x) h) =
      ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
        ∑ D ∈ (Finset.univ : Finset ι).powersetCard (h + 1),
          bernoulliWeight g x * ∏ i ∈ D, if x i then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [blockT_selected_fullSupport, Finset.mul_sum]
    _ = ∑ D ∈ (Finset.univ : Finset ι).powersetCard (h + 1),
        ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
          bernoulliWeight g x * ∏ i ∈ D, if x i then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ D ∈ (Finset.univ : Finset ι).powersetCard (h + 1), ∏ i ∈ D, g i := by
      apply Finset.sum_congr rfl
      intro D hD
      exact bernoulliExpectation_monomial_eq g D

/-- Averaging the one-block Bonferroni inequalities bounds its mean between avoidance and the
next-degree correction. -/
theorem bernoulliBlock_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (h : ℕ) (hh : Even h)
    (hg : ∀ i, 0 ≤ g i ∧ g i ≤ 1) :
    (∏ i, (1 - g i)) ≤ bernoulliBlockUMean g h ∧
      bernoulliBlockUMean g h - (∏ i, (1 - g i)) ≤ bernoulliBlockTMean g h := by
  classical
  let I : (ι → Bool) → ℝ := fun x => ∏ i, if x i then (0 : ℝ) else 1
  let U : (ι → Bool) → ℝ := fun x => blockU (selectedBad x) h
  let T : (ι → Bool) → ℝ := fun x => blockT (selectedBad x) h
  have havoid : bernoulliExpectation g I = ∏ i, (1 - g i) := by
    calc
      bernoulliExpectation g I = bernoulliAvoidanceMean g :=
        (bernoulliAvoidanceMean_eq_expectation g).symm
      _ = ∏ i, (1 - g i) := bernoulliAvoidanceMean_eq g
  have hIU : ∀ x, I x ≤ U x := by
    intro x
    change (∏ i, if x i then (0 : ℝ) else 1) ≤ blockU (selectedBad x) h
    rw [← selectedBad_avoid_indicator x]
    exact blockU_ge_avoid (selectedBad x) hh
  have hgap : ∀ x, U x - I x ≤ T x := by
    intro x
    change blockU (selectedBad x) h -
        (∏ i, if x i then (0 : ℝ) else 1) ≤ blockT (selectedBad x) h
    rw [← selectedBad_avoid_indicator x]
    exact blockU_sub_avoid_le_T (selectedBad x) hh
  have hlow := bernoulliExpectation_mono g I U hg hIU
  have hlin : bernoulliExpectation g (fun x => U x - I x) =
      bernoulliBlockUMean g h - bernoulliExpectation g I := by
    simp only [bernoulliExpectation, bernoulliBlockUMean, bernoulliWeight]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  have hhigh := bernoulliExpectation_mono g (fun x => U x - I x) T hg hgap
  constructor
  · simpa [havoid, U, bernoulliBlockUMean] using hlow
  · rw [hlin, havoid] at hhigh
    have hT : bernoulliExpectation g T = bernoulliBlockTMean g h := rfl
    rw [hT] at hhigh
    linarith

end ArtinPrimitiveRoots.Sieve.Block
