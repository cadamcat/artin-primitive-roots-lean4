import ArtinPrimitiveRoots.Sieve.Block.PowerBlocks

namespace ArtinPrimitiveRoots.Sieve.Block

open Finset

/-- The product of local even truncations minus all one-block next-degree corrections is at most
the exact product of the local avoidance indicators. -/
theorem product_sub_corrections_le {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (s : Finset ι) (I U T : ι → ℝ)
    (hIU : ∀ i ∈ s, 0 ≤ I i ∧ I i ≤ U i)
    (hUT : ∀ i ∈ s, U i - I i ≤ T i) :
    (∏ i ∈ s, U i) - ∑ i ∈ s, T i * ∏ j ∈ s.erase i, U j ≤ ∏ i ∈ s, I i := by
  classical
  have htel : (∏ i ∈ s, I i) =
      (∏ i ∈ s, U i) -
        ∑ i ∈ s, (U i - I i) * (∏ j ∈ s with j < i, I j) *
          ∏ j ∈ s with i < j, U j := by
    simpa only [sub_sub_cancel] using
      (Finset.prod_sub_ordered s U (fun i => U i - I i))
  have hterm : ∀ i ∈ s,
      (U i - I i) * (∏ j ∈ s with j < i, I j) *
          ∏ j ∈ s with i < j, U j ≤ T i * ∏ j ∈ s.erase i, U j := by
    intro i hi
    let before : Finset ι := s.filter (fun j => j < i)
    let after : Finset ι := s.filter (fun j => i < j)
    have hbeforeI : 0 ≤ ∏ j ∈ before, I j :=
      Finset.prod_nonneg fun j hj => (hIU j (Finset.mem_filter.mp hj).1).1
    have hbeforeCmp : (∏ j ∈ before, I j) ≤ ∏ j ∈ before, U j :=
      Finset.prod_le_prod₀
        (fun j hj => (hIU j (Finset.mem_filter.mp hj).1).1)
        (fun j hj => (hIU j (Finset.mem_filter.mp hj).1).2)
    have hafterNonneg : 0 ≤ ∏ j ∈ after, U j :=
      Finset.prod_nonneg fun j hj =>
        ((hIU j (Finset.mem_filter.mp hj).1).1).trans
          (hIU j (Finset.mem_filter.mp hj).1).2
    have hdisj : Disjoint before after := by
      apply Finset.disjoint_left.mpr
      intro j hjb hja
      have hji := (Finset.mem_filter.mp hjb).2
      have hij := (Finset.mem_filter.mp hja).2
      exact (not_lt_of_ge (le_of_lt hji) hij).elim
    have hunion : before ∪ after = s.erase i := by
      ext j
      simp only [Finset.mem_union, before, after, Finset.mem_filter,
        Finset.mem_erase]
      constructor
      · rintro (⟨hjs, hlt⟩ | ⟨hjs, hgt⟩)
        · exact ⟨hlt.ne, hjs⟩
        · exact ⟨hgt.ne.symm, hjs⟩
      · rintro ⟨hne, hjs⟩
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ⟨hjs, hlt⟩
        · exact Or.inr ⟨hjs, hgt⟩
    have hprod : (∏ j ∈ before, U j) * (∏ j ∈ after, U j) =
        ∏ j ∈ s.erase i, U j := by
      rw [← Finset.prod_union hdisj, hunion]
    have hdiff0 : 0 ≤ U i - I i := sub_nonneg.mpr (hIU i hi).2
    have hT0 : 0 ≤ T i := le_trans hdiff0 (hUT i hi)
    have hdiffT : U i - I i ≤ T i := hUT i hi
    have hprodCmp :
        (∏ j ∈ before, I j) * (∏ j ∈ after, U j) ≤
          (∏ j ∈ before, U j) * (∏ j ∈ after, U j) :=
      mul_le_mul_of_nonneg_right hbeforeCmp hafterNonneg
    have hUbefore0 : 0 ≤ ∏ j ∈ before, U j :=
      Finset.prod_nonneg fun j hj =>
        ((hIU j (Finset.mem_filter.mp hj).1).1).trans
          (hIU j (Finset.mem_filter.mp hj).1).2
    have hbase0 : 0 ≤ (∏ j ∈ before, U j) * ∏ j ∈ after, U j :=
      mul_nonneg hUbefore0 hafterNonneg
    have hcombined :
        (U i - I i) * ((∏ j ∈ before, I j) * ∏ j ∈ after, U j) ≤
          T i * ((∏ j ∈ before, U j) * ∏ j ∈ after, U j) := by
      calc
        (U i - I i) * ((∏ j ∈ before, I j) * ∏ j ∈ after, U j) ≤
            (U i - I i) * ((∏ j ∈ before, U j) * ∏ j ∈ after, U j) :=
          mul_le_mul_of_nonneg_left hprodCmp hdiff0
        _ ≤ T i * ((∏ j ∈ before, U j) * ∏ j ∈ after, U j) :=
          mul_le_mul_of_nonneg_right hdiffT hbase0
    calc
      (U i - I i) * (∏ j ∈ s with j < i, I j) *
          ∏ j ∈ s with i < j, U j =
        (U i - I i) * ((∏ j ∈ before, I j) * ∏ j ∈ after, U j) := by
          simp only [before, after]
          ring
      _ ≤ T i * ((∏ j ∈ before, U j) * ∏ j ∈ after, U j) := hcombined
      _ = T i * ∏ j ∈ s.erase i, U j := by rw [hprod]
  have hsum := Finset.sum_le_sum hterm
  linarith [htel]

/-- Removing one factor no larger than a product's factors only decreases a nonnegative product. -/
theorem prod_erase_le_of_one_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) {i : ι} (hi : i ∈ s)
    (hf : ∀ j ∈ s, 1 ≤ f j) :
    ∏ j ∈ s.erase i, f j ≤ ∏ j ∈ s, f j := by
  have heq := Finset.prod_erase_mul s f hi
  have hnonneg : 0 ≤ ∏ j ∈ s.erase i, f j :=
    Finset.prod_nonneg (fun j hj => le_trans (by norm_num) (hf j (Finset.mem_of_mem_erase hj)))
  have hdiff : 0 ≤ (∏ j ∈ s.erase i, f j) * (f i - 1) :=
    mul_nonneg hnonneg (sub_nonneg.mpr (hf i hi))
  rw [← heq]
  nlinarith

/-- Aggregate local Bernoulli block estimates into bounds for the product polynomial and its
one-block correction. -/
theorem product_local_model_estimates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a u t r : ι → ℝ)
    (hlocal : ∀ i, 0 ≤ a i ∧ a i ≤ u i ∧ u i ≤ a i * (1 + r i) ∧
      0 ≤ t i ∧ t i ≤ a i * r i ∧ 0 ≤ r i)
    (hR : (∑ i, r i) ≤ 1) :
    (∏ i, u i ≤ (∏ i, a i) * (1 + 2 * ∑ i, r i)) ∧
      (∏ i, a i) * (1 - (∑ i, r i) * Real.exp (∑ i, r i)) ≤
        (∏ i, u i) - ∑ i, t i * ∏ j ∈ Finset.univ.erase i, u j := by
  classical
  let R : ℝ := ∑ i, r i
  let A : ℝ := ∏ i, a i
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg (fun i hi => (hlocal i).2.2.2.2.2)
  have haNonneg : 0 ≤ A := by
    dsimp [A]
    exact Finset.prod_nonneg (fun i hi => (hlocal i).1)
  have huNonneg : ∀ i, 0 ≤ u i := fun i => le_trans (hlocal i).1 (hlocal i).2.1
  have hfactorNonneg : ∀ i, 0 ≤ a i * (1 + r i) := by
    intro i
    exact mul_nonneg (hlocal i).1 (by linarith [(hlocal i).2.2.2.2.2])
  have hprodU : (∏ i, u i) ≤ ∏ i, (a i * (1 + r i)) :=
    Finset.prod_le_prod₀ (fun i hi => huNonneg i) (fun i hi => (hlocal i).2.2.1)
  have hprodFactor : (∏ i, (a i * (1 + r i))) = A * ∏ i, (1 + r i) := by
    dsimp [A]
    rw [Finset.prod_mul_distrib]
  have hprodExp : (∏ i, (1 + r i)) ≤ Real.exp R := by
    dsimp [R]
    exact Real.prod_one_add_le_exp_sum Finset.univ (fun i => (hlocal i).2.2.2.2.2)
  have hexp : Real.exp R ≤ 1 + 2 * R := by
    have h := exp_sub_one_le_two_mul hR0 hR
    linarith
  have hupper : (∏ i, u i) ≤ A * (1 + 2 * R) := by
    calc
      (∏ i, u i) ≤ ∏ i, (a i * (1 + r i)) := hprodU
      _ = A * ∏ i, (1 + r i) := hprodFactor
      _ ≤ A * Real.exp R := mul_le_mul_of_nonneg_left hprodExp haNonneg
      _ ≤ A * (1 + 2 * R) := mul_le_mul_of_nonneg_left hexp haNonneg
  have hprodA : A ≤ ∏ i, u i := by
    dsimp [A]
    exact Finset.prod_le_prod₀ (fun i hi => (hlocal i).1)
      (fun i hi => (hlocal i).2.1)
  have hcorrection :
      (∑ i, t i * ∏ j ∈ Finset.univ.erase i, u j) ≤ A * (R * Real.exp R) := by
    have hterm : ∀ i : ι,
        t i * ∏ j ∈ Finset.univ.erase i, u j ≤ A * (r i * Real.exp R) := by
      intro i
      have hprodOthers :
          (∏ j ∈ Finset.univ.erase i, u j) ≤
            ∏ j ∈ Finset.univ.erase i, (a j * (1 + r j)) :=
        Finset.prod_le_prod₀
          (fun j hj => huNonneg j)
          (fun j hj => (hlocal j).2.2.1)
      have huOthers0 : 0 ≤ ∏ j ∈ Finset.univ.erase i, u j :=
        Finset.prod_nonneg (fun j hj => huNonneg j)
      have hupperOthers0 :
          0 ≤ ∏ j ∈ Finset.univ.erase i, (a j * (1 + r j)) :=
        Finset.prod_nonneg (fun j hj => hfactorNonneg j)
      have haR0 : 0 ≤ a i * r i := mul_nonneg (hlocal i).1 (hlocal i).2.2.2.2.2
      have hfirst :
          t i * ∏ j ∈ Finset.univ.erase i, u j ≤
            (a i * r i) * ∏ j ∈ Finset.univ.erase i, (a j * (1 + r j)) := by
        calc
          t i * ∏ j ∈ Finset.univ.erase i, u j ≤
              t i * ∏ j ∈ Finset.univ.erase i, (a j * (1 + r j)) :=
            mul_le_mul_of_nonneg_left hprodOthers (hlocal i).2.2.2.1
          _ ≤ (a i * r i) * ∏ j ∈ Finset.univ.erase i, (a j * (1 + r j)) :=
            mul_le_mul_of_nonneg_right (hlocal i).2.2.2.2.1 hupperOthers0
      have hsplit :
          (∏ j ∈ Finset.univ.erase i, (a j * (1 + r j))) =
            (∏ j ∈ Finset.univ.erase i, a j) *
              ∏ j ∈ Finset.univ.erase i, (1 + r j) := by
        rw [Finset.prod_mul_distrib]
      have haAll : a i * ∏ j ∈ Finset.univ.erase i, a j = A := by
        dsimp [A]
        exact Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)
      have hqErase :
          (∏ j ∈ Finset.univ.erase i, (1 + r j)) ≤ ∏ j, (1 + r j) :=
        prod_erase_le_of_one_le Finset.univ (fun j => 1 + r j) (Finset.mem_univ i)
          (fun j hj => by linarith [(hlocal j).2.2.2.2.2])
      calc
        t i * ∏ j ∈ Finset.univ.erase i, u j ≤
            (a i * r i) * ∏ j ∈ Finset.univ.erase i, (a j * (1 + r j)) := hfirst
        _ = A * (r i * ∏ j ∈ Finset.univ.erase i, (1 + r j)) := by
          rw [hsplit]
          calc
            (a i * r i) *
                ((∏ j ∈ Finset.univ.erase i, a j) *
                  ∏ j ∈ Finset.univ.erase i, (1 + r j)) =
              (a i * ∏ j ∈ Finset.univ.erase i, a j) *
                (r i * ∏ j ∈ Finset.univ.erase i, (1 + r j)) := by ring
            _ = A * (r i * ∏ j ∈ Finset.univ.erase i, (1 + r j)) := by rw [haAll]
        _ ≤ A * (r i * ∏ j, (1 + r j)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hqErase ((hlocal i).2.2.2.2.2)) haNonneg
        _ ≤ A * (r i * Real.exp R) := by
          have := mul_le_mul_of_nonneg_left hprodExp ((hlocal i).2.2.2.2.2)
          exact mul_le_mul_of_nonneg_left this haNonneg
    calc
      (∑ i, t i * ∏ j ∈ Finset.univ.erase i, u j) ≤
          ∑ i, A * (r i * Real.exp R) := Finset.sum_le_sum (fun i hi => hterm i)
      _ = A * (R * Real.exp R) := by
        calc
          (∑ i, A * (r i * Real.exp R)) =
              (A * Real.exp R) * ∑ i, r i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = A * (R * Real.exp R) := by dsimp [R]; ring
  have hlower : A * (1 - R * Real.exp R) ≤
      (∏ i, u i) - ∑ i, t i * ∏ j ∈ Finset.univ.erase i, u j := by
    dsimp [A]
    have hcorr := hcorrection
    dsimp [A, R] at hcorr
    nlinarith
  constructor
  · simpa [A, R] using hupper
  · simpa [A, R] using hlower

/-- The upper product estimate with no small-tail assumption. -/
theorem product_local_model_upper_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a u r : ι → ℝ)
    (hlocal : ∀ i, 0 ≤ a i ∧ a i ≤ u i ∧ u i ≤ a i * (1 + r i) ∧ 0 ≤ r i) :
    (∏ i, u i) ≤ (∏ i, a i) * Real.exp (∑ i, r i) := by
  classical
  let R : ℝ := ∑ i, r i
  let A : ℝ := ∏ i, a i
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg (fun i hi => (hlocal i).2.2.2)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.prod_nonneg (fun i hi => (hlocal i).1)
  have hu : ∀ i, 0 ≤ u i := fun i => le_trans (hlocal i).1 (hlocal i).2.1
  have hprodU : (∏ i, u i) ≤ ∏ i, (a i * (1 + r i)) :=
    Finset.prod_le_prod₀ (fun i hi => hu i) (fun i hi => (hlocal i).2.2.1)
  have hprodFactor : (∏ i, (a i * (1 + r i))) = A * ∏ i, (1 + r i) := by
    dsimp [A]
    rw [Finset.prod_mul_distrib]
  have hprodExp : (∏ i, (1 + r i)) ≤ Real.exp R := by
    dsimp [R]
    exact Real.prod_one_add_le_exp_sum Finset.univ (fun i => (hlocal i).2.2.2)
  calc
    (∏ i, u i) ≤ ∏ i, (a i * (1 + r i)) := hprodU
    _ = A * ∏ i, (1 + r i) := hprodFactor
    _ ≤ A * Real.exp R := mul_le_mul_of_nonneg_left hprodExp hA
    _ = A * Real.exp (∑ i, r i) := by simp [R]
    _ = (∏ i, a i) * Real.exp (∑ i, r i) := by simp [A]

/-- A local coefficient in the even block polynomial. -/
def blockUProfileLocalCoefficient {α : Type*} {N : ℕ} (h : Fin N → ℕ)
    (j : Fin N) (D : Finset α) : ℝ :=
  if D.card ≤ h j then (-1 : ℝ) ^ D.card else 0

/-- A local coefficient in the next-degree correction polynomial. -/
def blockTProfileLocalCoefficient {α : Type*} {N : ℕ} (h : Fin N → ℕ)
    (j : Fin N) (D : Finset α) : ℝ :=
  if D.card = h j + 1 then 1 else 0

/-- Coefficients for one correction term in the global product polynomial. -/
noncomputable def blockTProfileCoefficient {α : Type*} [DecidableEq α]
    {N : ℕ} (B : Fin N → Finset α) (h : Fin N → ℕ)
    (j : Fin N) (D : Finset α) : ℝ :=
  ∏ k, if k = j then blockTProfileLocalCoefficient h j (D ∩ B k)
    else blockUProfileLocalCoefficient h k (D ∩ B k)

/-- Coefficients of the global Brun--Hooley correction polynomial. -/
noncomputable def blockLowerProfileCoefficient {α : Type*} [DecidableEq α]
    {N : ℕ} (B : Fin N → Finset α) (h : Fin N → ℕ) (D : Finset α) : ℝ :=
  blockUProfileCoefficient B h D - ∑ j, blockTProfileCoefficient B h j D

/-- The coefficient form of a block's truncated inclusion--exclusion polynomial. -/
theorem blockU_local_polynomial_eq {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (x : α → Bool) (h : ℕ) :
    (∑ D ∈ s.powerset,
      (if D.card ≤ h then (-1 : ℝ) ^ D.card else 0) *
        (if D ⊆ selectedBadOn s x then (1 : ℝ) else 0)) =
      blockU (selectedBadOn s x) h := by
  classical
  rw [blockU_selectedOn_support]
  apply Finset.sum_congr rfl
  intro D hD
  have hDsub : D ⊆ s := Finset.mem_powerset.mp hD
  have hind : (if D ⊆ selectedBadOn s x then (1 : ℝ) else 0) =
      ∏ i ∈ D, if x i then (1 : ℝ) else 0 := by
    rw [selectedBadOn_subset_indicator]
    apply Finset.prod_congr rfl
    intro i hi
    simp [hDsub hi]
  by_cases hc : D.card ≤ h <;> simp [hc, hind]

/-- The coefficient form of a block's next-degree correction polynomial. -/
theorem blockT_local_polynomial_eq {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (x : α → Bool) (h : ℕ) :
    (∑ D ∈ s.powerset,
      (if D.card = h + 1 then (1 : ℝ) else 0) *
        (if D ⊆ selectedBadOn s x then (1 : ℝ) else 0)) =
      blockT (selectedBadOn s x) h := by
  classical
  let q := fun D : Finset α => ∏ i ∈ D, if x i then (1 : ℝ) else 0
  have hind : ∀ D ∈ s.powerset,
      (if D ⊆ selectedBadOn s x then (1 : ℝ) else 0) = q D := by
    intro D hD
    have hDsub : D ⊆ s := Finset.mem_powerset.mp hD
    rw [selectedBadOn_subset_indicator]
    dsimp [q]
    apply Finset.prod_congr rfl
    intro i hi
    simp [hDsub hi]
  have hfilter : (s.powerset).filter (fun D => D.card = h + 1) =
      s.powersetCard (h + 1) := by
    rw [Finset.powersetCard_eq_filter]
  calc
    (∑ D ∈ s.powerset,
      (if D.card = h + 1 then (1 : ℝ) else 0) *
        (if D ⊆ selectedBadOn s x then (1 : ℝ) else 0)) =
      ∑ D ∈ s.powerset, if D.card = h + 1 then q D else 0 := by
        apply Finset.sum_congr rfl
        intro D hD
        rw [hind D hD]
        split_ifs <;> simp
    _ = ∑ D ∈ (s.powerset).filter (fun D => D.card = h + 1), q D := by
      rw [← Finset.sum_filter]
    _ = ∑ D ∈ s.powersetCard (h + 1), q D := by rw [hfilter]
    _ = blockT (selectedBadOn s x) h := by
      simpa [q] using (blockT_selectedOn_support s x h).symm

/-- A product with one correction factor expands into its global squarefree polynomial. -/
theorem product_blockT_U_eq_polynomial {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (P : Finset α) (B : Fin N → Finset α) (h : Fin N → ℕ)
    (hBsub : ∀ k, B k ⊆ P) (hcover : ∀ x ∈ P, ∃ k, x ∈ B k)
    (hdisj : ∀ k l, k ≠ l → Disjoint (B k) (B l))
    (j : Fin N) (x : α → Bool) :
    blockT (selectedBadOn (B j) x) (h j) *
        ∏ k ∈ Finset.univ.erase j, blockU (selectedBadOn (B k) x) (h k) =
      ∑ D ∈ P.powerset,
        blockTProfileCoefficient B h j D *
          (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
  classical
  let c : Fin N → Finset α → ℝ := fun k D =>
    if k = j then blockTProfileLocalCoefficient h j D
      else blockUProfileLocalCoefficient h k D
  let localPoly : Fin N → ℝ := fun k =>
    ∑ D ∈ (B k).powerset, c k D *
      (if D ⊆ selectedBadOn (B k) x then (1 : ℝ) else 0)
  have hlocal : ∀ k, localPoly k =
      if k = j then blockT (selectedBadOn (B k) x) (h k)
      else blockU (selectedBadOn (B k) x) (h k) := by
    intro k
    by_cases hkj : k = j
    · subst k
      dsimp only [localPoly, c, blockTProfileLocalCoefficient]
      simp only [if_pos rfl]
      exact blockT_local_polynomial_eq (B j) x (h j)
    · dsimp only [localPoly, c, blockUProfileLocalCoefficient]
      simp only [if_neg hkj]
      exact blockU_local_polynomial_eq (B k) x (h k)
  have hfactor : (∏ k, localPoly k) =
      blockT (selectedBadOn (B j) x) (h j) *
        ∏ k ∈ Finset.univ.erase j, blockU (selectedBadOn (B k) x) (h k) := by
    have hprod : (∏ k, localPoly k) =
        ∏ k, if k = j then blockT (selectedBadOn (B k) x) (h k)
          else blockU (selectedBadOn (B k) x) (h k) := by
      apply Finset.prod_congr rfl
      intro k hk
      exact hlocal k
    have hfactor' :
        (∏ k, if k = j then blockT (selectedBadOn (B k) x) (h k)
          else blockU (selectedBadOn (B k) x) (h k)) =
        blockT (selectedBadOn (B j) x) (h j) *
          ∏ k ∈ Finset.univ.erase j, blockU (selectedBadOn (B k) x) (h k) := by
      have herase :
          (∏ k ∈ Finset.univ.erase j,
            if k = j then blockT (selectedBadOn (B k) x) (h k)
            else blockU (selectedBadOn (B k) x) (h k)) =
          ∏ k ∈ Finset.univ.erase j, blockU (selectedBadOn (B k) x) (h k) := by
        apply Finset.prod_congr rfl
        intro k hk
        have hne : k ≠ j := (Finset.mem_erase.mp hk).1
        simp [hne]
      calc
        (∏ k, if k = j then blockT (selectedBadOn (B k) x) (h k)
            else blockU (selectedBadOn (B k) x) (h k)) =
          (if j = j then blockT (selectedBadOn (B j) x) (h j)
            else blockU (selectedBadOn (B j) x) (h j)) *
              ∏ k ∈ Finset.univ.erase j,
                (if k = j then blockT (selectedBadOn (B k) x) (h k)
                  else blockU (selectedBadOn (B k) x) (h k)) :=
          (Finset.mul_prod_erase Finset.univ
            (fun k => if k = j then blockT (selectedBadOn (B k) x) (h k)
              else blockU (selectedBadOn (B k) x) (h k)) (Finset.mem_univ j)).symm
        _ = blockT (selectedBadOn (B j) x) (h j) *
              ∏ k ∈ Finset.univ.erase j, blockU (selectedBadOn (B k) x) (h k) := by
          rw [herase]
          simp
    exact hprod.trans hfactor'
  calc
    blockT (selectedBadOn (B j) x) (h j) *
        ∏ k ∈ Finset.univ.erase j, blockU (selectedBadOn (B k) x) (h k) =
      ∏ k, localPoly k := hfactor.symm
    _ = ∏ k, ∑ D ∈ (B k).powerset,
        c k D * (if D ⊆ selectedBadOn (B k) x then (1 : ℝ) else 0) := by
          simp [localPoly]
    _ = ∑ D ∈ P.powerset,
        (∏ k, c k (D ∩ B k)) *
          (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) :=
      product_blockPolynomials_eq P B hBsub hcover hdisj c x
    _ = ∑ D ∈ P.powerset,
        blockTProfileCoefficient B h j D *
          (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro D hD
          rfl

end ArtinPrimitiveRoots.Sieve.Block
