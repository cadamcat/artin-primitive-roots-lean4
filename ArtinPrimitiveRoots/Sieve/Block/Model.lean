import Mathlib

namespace ArtinPrimitiveRoots.Sieve.Block

open Finset

/-- The probability weight of one Boolean assignment in a finite independent model. -/
noncomputable def bernoulliWeight {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i then g i else 1 - g i

/-- Expectation of a function on the Boolean assignments of a finite type. -/
noncomputable def bernoulliExpectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
    bernoulliWeight g x * F x

/-- The weighted mean of the indicator that every coordinate in `J` is selected. -/
noncomputable def bernoulliMonomialMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (J : Finset ι) : ℝ :=
  ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
    ∏ i, (if x i then g i else 1 - g i) *
      if i ∈ J then (if x i then (1 : ℝ) else 0) else 1

/-- In the independent model, the mean of a squarefree monomial is the product of its means. -/
theorem bernoulliMonomialMean_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (J : Finset ι) :
    bernoulliMonomialMean g J = ∏ i ∈ J, g i := by
  classical
  unfold bernoulliMonomialMean
  rw [Finset.sum_prod_piFinset
    (s := (Finset.univ : Finset Bool))
    (g := fun (i : ι) b => (if b then g i else 1 - g i) *
      if i ∈ J then (if b then (1 : ℝ) else 0) else 1)]
  have hlocal : ∀ i : ι,
      (∑ b ∈ (Finset.univ : Finset Bool),
        (if b then g i else 1 - g i) *
          if i ∈ J then (if b then (1 : ℝ) else 0) else 1) =
        if i ∈ J then g i else 1 := by
    intro i
    by_cases hi : i ∈ J <;> simp [hi]
  simp_rw [hlocal]
  change (∏ i ∈ (Finset.univ : Finset ι), if i ∈ J then g i else 1) = _
  rw [← Finset.prod_filter]
  simp

/-- The local-product monomial mean is ordinary expectation of its event indicator. -/
theorem bernoulliMonomialMean_eq_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (J : Finset ι) :
    bernoulliMonomialMean g J = bernoulliExpectation g
      (fun x => ∏ i, if i ∈ J then (if x i then (1 : ℝ) else 0) else 1) := by
  classical
  unfold bernoulliMonomialMean bernoulliExpectation bernoulliWeight
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.prod_mul_distrib]

/-- The expected indicator that all coordinates in `J` are selected. -/
theorem bernoulliExpectation_monomial_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (J : Finset ι) :
    bernoulliExpectation g (fun x => ∏ i ∈ J, if x i then (1 : ℝ) else 0) =
      ∏ i ∈ J, g i := by
  classical
  have hfun : (fun x : ι → Bool => ∏ i ∈ J, if x i then (1 : ℝ) else 0) =
      (fun x => ∏ i, if i ∈ J then (if x i then (1 : ℝ) else 0) else 1) := by
    funext x
    change (∏ i ∈ J, if x i then (1 : ℝ) else 0) =
      ∏ i ∈ (Finset.univ : Finset ι),
        if i ∈ J then (if x i then (1 : ℝ) else 0) else 1
    rw [← Finset.prod_filter]
    simp
  rw [hfun, ← bernoulliMonomialMean_eq_expectation, bernoulliMonomialMean_eq]

/-- The Bernoulli-model no-event mean, written as a product of local no-event weights. -/
noncomputable def bernoulliAvoidanceMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) : ℝ :=
  ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
    ∏ i, if x i then 0 else 1 - g i

/-- The no-event summand is the Bernoulli weight times the no-event indicator. -/
theorem bernoulliAvoidanceMean_eq_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) :
    bernoulliAvoidanceMean g = bernoulliExpectation g
      (fun x => ∏ i, if x i then (0 : ℝ) else 1) := by
  classical
  unfold bernoulliAvoidanceMean bernoulliExpectation bernoulliWeight
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hxi : x i <;> simp [hxi]

/-- Evaluating the local avoidance choices gives the product density. -/
theorem bernoulliAvoidanceMean_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) : bernoulliAvoidanceMean g = ∏ i, (1 - g i) := by
  classical
  unfold bernoulliAvoidanceMean
  rw [Finset.sum_prod_piFinset
    (s := (Finset.univ : Finset Bool))
    (g := fun (i : ι) b => if b then (0 : ℝ) else 1 - g i)]
  have hlocal : ∀ i : ι,
      (∑ b ∈ (Finset.univ : Finset Bool), if b then (0 : ℝ) else 1 - g i) =
        1 - g i := by
    intro i
    simp
  simp_rw [hlocal]

/-- Model weights are nonnegative when all coordinate means lie in `[0,1]`. -/
theorem bernoulliWeight_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (x : ι → Bool) (hg : ∀ i, 0 ≤ g i ∧ g i ≤ 1) :
    0 ≤ bernoulliWeight g x := by
  classical
  unfold bernoulliWeight
  apply Finset.prod_nonneg
  intro i hi
  split_ifs with hx
  · exact (hg i).1
  · linarith [(hg i).2]

/-- Expectation preserves pointwise inequalities for nonnegative Bernoulli weights. -/
theorem bernoulliExpectation_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (F G : (ι → Bool) → ℝ) (hg : ∀ i, 0 ≤ g i ∧ g i ≤ 1)
    (hFG : ∀ x, F x ≤ G x) :
    bernoulliExpectation g F ≤ bernoulliExpectation g G := by
  classical
  unfold bernoulliExpectation
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_left (hFG x) (bernoulliWeight_nonneg g x hg)

end ArtinPrimitiveRoots.Sieve.Block
