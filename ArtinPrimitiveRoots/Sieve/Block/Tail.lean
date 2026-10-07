import ArtinPrimitiveRoots.Sieve.Block.ModelSieve

namespace ArtinPrimitiveRoots.Sieve.Block

open Finset

/-- A degree-`n` elementary symmetric sum is bounded by an exponential moment. -/
theorem elementarySymmetric_le_exp_three {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (n : ℕ) (C : ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hsum : (∑ i ∈ s, g i) ≤ C) :
    (3 : ℝ) ^ n * ∑ D ∈ s.powersetCard n, ∏ i ∈ D, g i ≤ Real.exp (3 * C) := by
  classical
  have hscale : ∀ D ∈ s.powersetCard n,
      (∏ i ∈ D, (3 : ℝ) * g i) = (3 : ℝ) ^ n * ∏ i ∈ D, g i := by
    intro D hD
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_const]
    simp [Finset.mem_powersetCard.mp hD]
  let f : ι → ℝ := fun i => if i ∈ s then 3 * g i else 0
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    by_cases hi : i ∈ s
    · simp [f, hi, hg i hi]
    · simp [f, hi]
  have hfsum : (∑ i ∈ s, f i) = 3 * ∑ i ∈ s, g i := by
    simp [f, Finset.mul_sum]
  have hfprod : (∏ i ∈ s, (1 + f i)) = ∏ i ∈ s, (1 + 3 * g i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [f, hi]
  calc
    (3 : ℝ) ^ n * ∑ D ∈ s.powersetCard n, ∏ i ∈ D, g i =
        ∑ D ∈ s.powersetCard n, ∏ i ∈ D, (3 : ℝ) * g i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      rw [hscale D hD]
    _ ≤ ∑ D ∈ s.powerset, ∏ i ∈ D, (3 : ℝ) * g i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (fun D hD => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hD).1)
      intro D hD hnot
      exact Finset.prod_nonneg (fun i hi => mul_nonneg (by norm_num) (hg i (Finset.mem_powerset.mp hD hi)))
    _ = ∏ i ∈ s, (1 + 3 * g i) := by
      rw [Finset.prod_one_add]
    _ = ∏ i ∈ s, (1 + f i) := hfprod.symm
    _ ≤ Real.exp (∑ i ∈ s, f i) := Real.prod_one_add_le_exp_sum s hf
    _ = Real.exp (3 * ∑ i ∈ s, g i) := by rw [hfsum]
    _ ≤ Real.exp (3 * C) := Real.exp_le_exp.mpr (by nlinarith)

/-- A degree-`n` elementary symmetric sum has an exponential-over-power bound. -/
theorem elementarySymmetric_le_exp_div_three_pow {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (n : ℕ) (C : ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hsum : (∑ i ∈ s, g i) ≤ C) :
    ∑ D ∈ s.powersetCard n, ∏ i ∈ D, g i ≤ Real.exp (3 * C) / (3 : ℝ) ^ n := by
  have hpos : 0 < (3 : ℝ) ^ n := pow_pos (by norm_num) _
  apply (le_div_iff₀ hpos).2
  have h := elementarySymmetric_le_exp_three s g n C hg hsum
  nlinarith [h]

/-- A local factor is bounded below by an exponential when its mean stays away from one. -/
theorem one_sub_ge_exp_neg_div {u η : ℝ} (hη : 0 < η) (hu : 0 ≤ u)
    (huη : u ≤ 1 - η) : Real.exp (-(u / η)) ≤ 1 - u := by
  have hx : 0 ≤ u / η := div_nonneg hu hη.le
  have hadd : 1 + u / η ≤ Real.exp (u / η) := by
    simpa [add_comm] using Real.add_one_le_exp (u / η)
  have hrecip : (Real.exp (u / η))⁻¹ ≤ (1 + u / η)⁻¹ :=
    by simpa [one_div] using one_div_le_one_div_of_le (by positivity) hadd
  have hExp : Real.exp (-(u / η)) ≤ (1 + u / η)⁻¹ := by
    rw [Real.exp_neg]
    exact hrecip
  have hden' : 1 / (1 + u / η) ≤ 1 - u := by
    rw [div_le_iff₀ (by positivity)]
    field_simp [ne_of_gt hη]
    nlinarith [mul_nonneg hu (sub_nonneg.mpr huη)]
  have hden : (1 + u / η)⁻¹ ≤ 1 - u := by simpa [one_div] using hden'
  exact hExp.trans hden

/-- The product of avoidance factors is bounded below using a bound on the total mean. -/
theorem avoidanceProduct_ge_exp {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (η C : ℝ) (hη : 0 < η)
    (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1 - η)
    (hsum : (∑ i ∈ s, g i) ≤ C) :
    Real.exp (-C / η) ≤ ∏ i ∈ s, (1 - g i) := by
  classical
  have hloc : ∀ i ∈ s, Real.exp (-(g i / η)) ≤ 1 - g i := by
    intro i hi
    exact one_sub_ge_exp_neg_div hη (hg i hi).1 (hg i hi).2
  have hsumexp : (∑ i ∈ s, -(g i / η)) = -(∑ i ∈ s, g i) / η := by
    simp [div_eq_mul_inv, Finset.sum_neg_distrib, Finset.sum_mul]
  have hdiv : (∑ i ∈ s, g i) / η ≤ C / η :=
    div_le_div_of_nonneg_right hsum hη.le
  calc
    Real.exp (-C / η) ≤ Real.exp (-(∑ i ∈ s, g i) / η) :=
      Real.exp_le_exp.mpr (by simpa [neg_div] using (neg_le_neg hdiv))
    _ = Real.exp (∑ i ∈ s, -(g i / η)) := by rw [← hsumexp]
    _ = ∏ i ∈ s, Real.exp (-(g i / η)) := by rw [Real.exp_sum]
    _ ≤ ∏ i ∈ s, (1 - g i) := by
      apply Finset.prod_le_prod₀
        (fun i hi => Real.exp_nonneg _)
        hloc

/-- The geometric sequence of reciprocal powers has an `exp (-H)` tail. -/
theorem reciprocal_three_geometric_le_exp {N H : ℕ} (hH : 1 ≤ H) :
    ∑ j ∈ Finset.range N, 1 / (3 : ℝ) ^ ((j + 1) * H) ≤
      2 * Real.exp (-(H : ℝ)) := by
  classical
  let q : ℝ := 1 / (3 : ℝ) ^ H
  have hpowone : ∀ n : ℕ, 1 ≤ (3 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      nlinarith
  have h3pow : 3 ≤ (3 : ℝ) ^ H := by
    cases H with
    | zero => omega
    | succ n =>
      rw [pow_succ]
      nlinarith [hpowone n]
  have hqpos : 0 < q := by positivity [hpowone H]
  have hqle : q ≤ 1 / 3 := by
    dsimp [q]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) h3pow
  have hq_lt : q < 1 := lt_of_le_of_lt hqle (by norm_num)
  have hgeom : (∑ j ∈ Finset.range N, q ^ j) ≤ 2 := by
    have hmul : (∑ j ∈ Finset.range N, q ^ j) * (1 - q) = 1 - q ^ N :=
      geom_sum_mul_neg q N
    have hden : (1 / 2 : ℝ) ≤ 1 - q := by nlinarith [hqle]
    have hnum : 1 - q ^ N ≤ 1 := by
      have : 0 ≤ q ^ N := pow_nonneg hqpos.le N
      linarith
    have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range N, q ^ j :=
      Finset.sum_nonneg (fun j hj => pow_nonneg hqpos.le _)
    have hmul' : (∑ j ∈ Finset.range N, q ^ j) * (1 / 2) ≤ 1 := by
      calc
        _ ≤ (∑ j ∈ Finset.range N, q ^ j) * (1 - q) :=
          mul_le_mul_of_nonneg_left hden hsum_nonneg
        _ ≤ 1 := by rw [hmul]; exact hnum
    nlinarith
  have hgeomShift : (∑ j ∈ Finset.range N, q ^ (j + 1)) ≤ 2 * q := by
    calc
      (∑ j ∈ Finset.range N, q ^ (j + 1)) = q * ∑ j ∈ Finset.range N, q ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_succ]
        ring
      _ ≤ q * 2 := mul_le_mul_of_nonneg_left hgeom hqpos.le
      _ = 2 * q := by ring
  have hexp1 : Real.exp 1 ≤ 3 := by
    have h := Real.exp_le_two_add_div_two_sub (x := 1) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hbase : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
    have h : 1 / 3 ≤ 1 / Real.exp 1 :=
      one_div_le_one_div_of_le (Real.exp_pos 1) hexp1
    simpa [Real.exp_neg] using h
  have hqexp : q ≤ Real.exp (-(H : ℝ)) := by
    dsimp [q]
    calc
      1 / (3 : ℝ) ^ H = (1 / 3 : ℝ) ^ H := by rw [one_div_pow]
      _ ≤ Real.exp (-1) ^ H := pow_le_pow_left₀ (by norm_num) hbase H
      _ = Real.exp (-(H : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  have hsum : (∑ j ∈ Finset.range N, 1 / (3 : ℝ) ^ ((j + 1) * H)) =
      ∑ j ∈ Finset.range N, q ^ (j + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [q]
    calc
      1 / (3 : ℝ) ^ ((j + 1) * H) = 1 / (3 : ℝ) ^ (H * (j + 1)) := by
        rw [Nat.mul_comm]
      _ = 1 / ((3 : ℝ) ^ H) ^ (j + 1) := by rw [pow_mul]
      _ = (1 / (3 : ℝ) ^ H) ^ (j + 1) := by rw [one_div_pow]
  calc
    _ = ∑ j ∈ Finset.range N, q ^ (j + 1) := hsum
    _ ≤ 2 * q := hgeomShift
    _ ≤ 2 * Real.exp (-(H : ℝ)) := mul_le_mul_of_nonneg_left hqexp (by norm_num)

/-- The expected correction of a block has a uniform exponential-over-power bound. -/
theorem bernoulliBlockTMean_le_exp_div_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (h : ℕ) (C : ℝ) (hg : ∀ i, 0 ≤ g i)
    (hsum : (∑ i, g i) ≤ C) :
    bernoulliBlockTMean g h ≤ Real.exp (3 * C) / (3 : ℝ) ^ (h + 1) := by
  rw [bernoulliBlockTMean_eq_expansion]
  simpa [bernoulliBlockTExpansion] using
    (elementarySymmetric_le_exp_div_three_pow (Finset.univ : Finset ι) g (h + 1) C
      (by simpa using hg) hsum)

/-- The product density of one block is bounded below in terms of its total mean. -/
theorem bernoulliAvoidanceMean_ge_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (η C : ℝ) (hη : 0 < η) (hgη : ∀ i, g i ≤ 1 - η)
    (hg0 : ∀ i, 0 ≤ g i) (hsum : (∑ i, g i) ≤ C) :
    Real.exp (-C / η) ≤ bernoulliAvoidanceMean g := by
  rw [bernoulliAvoidanceMean_eq]
  exact avoidanceProduct_ge_exp (Finset.univ : Finset ι) g η C hη
    (fun i hi => ⟨hg0 i, hgη i⟩) (by simpa using hsum)

/-- The model mean of one truncated block differs from its avoidance product by a relative
exponential-over-power tail. -/
theorem bernoulliBlockUMean_le_relative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (h : ℕ) (hh : Even h) (η C : ℝ) (hη : 0 < η)
    (hg : ∀ i, 0 ≤ g i ∧ g i ≤ 1 - η) (hsum : (∑ i, g i) ≤ C) :
    bernoulliBlockUMean g h ≤ (∏ i, (1 - g i)) *
      (1 + Real.exp (3 * C + C / η) / (3 : ℝ) ^ (h + 1)) := by
  have hbounds := bernoulliBlock_bounds g h hh (fun i =>
    ⟨(hg i).1, by linarith [(hg i).2]⟩)
  have ha : Real.exp (-C / η) ≤ ∏ i, (1 - g i) := by
    calc
      Real.exp (-C / η) ≤ bernoulliAvoidanceMean g :=
        bernoulliAvoidanceMean_ge_exp g η C hη (fun i => (hg i).2)
          (fun i => (hg i).1) hsum
      _ = ∏ i, (1 - g i) := bernoulliAvoidanceMean_eq g
  have ht : bernoulliBlockTMean g h ≤ Real.exp (3 * C) / (3 : ℝ) ^ (h + 1) :=
    bernoulliBlockTMean_le_exp_div_three g h C (fun i => (hg i).1) hsum
  let a : ℝ := ∏ i, (1 - g i)
  let r : ℝ := Real.exp (3 * C + C / η) / (3 : ℝ) ^ (h + 1)
  have hfac : Real.exp (3 * C) / (3 : ℝ) ^ (h + 1) ≤ a * r := by
    have hr : 0 ≤ r := by positivity [r]
    have hmul : Real.exp (-C / η) * r = Real.exp (3 * C) / (3 : ℝ) ^ (h + 1) := by
      dsimp [r]
      calc
        Real.exp (-C / η) * (Real.exp (3 * C + C / η) / (3 : ℝ) ^ (h + 1)) =
            (Real.exp (-C / η) * Real.exp (3 * C + C / η)) /
              (3 : ℝ) ^ (h + 1) := by ring
        _ = Real.exp ((-C / η) + (3 * C + C / η)) / (3 : ℝ) ^ (h + 1) := by
          rw [← Real.exp_add]
        _ = Real.exp (3 * C) / (3 : ℝ) ^ (h + 1) := by congr 1 <;> ring_nf
    rw [← hmul]
    exact mul_le_mul_of_nonneg_right (by simpa [a] using ha) hr
  have hsumU : bernoulliBlockUMean g h ≤ a + bernoulliBlockTMean g h := by
    have h2 : bernoulliBlockUMean g h - a ≤ bernoulliBlockTMean g h := by
      simpa [a] using hbounds.2
    linarith
  calc
    bernoulliBlockUMean g h ≤ a + bernoulliBlockTMean g h := hsumU
    _ ≤ a + a * r := by
      simpa [add_comm] using add_le_add_left (ht.trans hfac) a
    _ = a * (1 + r) := by ring
    _ = (∏ i, (1 - g i)) *
        (1 + Real.exp (3 * C + C / η) / (3 : ℝ) ^ (h + 1)) := by simp [a, r]

/-- Relative one-block estimate when the coordinates live inside an ambient finite model. -/
theorem bernoulliBlockUMeanOn_le_relative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (h : ℕ) (hh : Even h) (η C : ℝ) (hη : 0 < η)
    (hg : ∀ i, 0 ≤ g i ∧ g i ≤ 1)
    (hgη : ∀ i ∈ s, g i ≤ 1 - η) (hsum : (∑ i ∈ s, g i) ≤ C) :
    bernoulliBlockUMeanOn s g h ≤ (∏ i ∈ s, (1 - g i)) *
      (1 + Real.exp (3 * C + C / η) / (3 : ℝ) ^ (h + 1)) := by
  have hbounds := bernoulliBlockOn_bounds s g h hh hg
  have ha : Real.exp (-C / η) ≤ ∏ i ∈ s, (1 - g i) :=
    avoidanceProduct_ge_exp s g η C hη (fun i hi => ⟨(hg i).1, hgη i hi⟩) hsum
  have ht : bernoulliBlockTMeanOn s g h ≤ Real.exp (3 * C) / (3 : ℝ) ^ (h + 1) := by
    rw [bernoulliBlockTMeanOn_eq_expansion]
    exact elementarySymmetric_le_exp_div_three_pow s g (h + 1) C
      (fun i hi => (hg i).1) hsum
  let a : ℝ := ∏ i ∈ s, (1 - g i)
  let r : ℝ := Real.exp (3 * C + C / η) / (3 : ℝ) ^ (h + 1)
  have hfac : Real.exp (3 * C) / (3 : ℝ) ^ (h + 1) ≤ a * r := by
    have hr : 0 ≤ r := by positivity [r]
    have hmul : Real.exp (-C / η) * r = Real.exp (3 * C) / (3 : ℝ) ^ (h + 1) := by
      dsimp [r]
      calc
        Real.exp (-C / η) * (Real.exp (3 * C + C / η) / (3 : ℝ) ^ (h + 1)) =
            (Real.exp (-C / η) * Real.exp (3 * C + C / η)) /
              (3 : ℝ) ^ (h + 1) := by ring
        _ = Real.exp ((-C / η) + (3 * C + C / η)) / (3 : ℝ) ^ (h + 1) := by
          rw [← Real.exp_add]
        _ = Real.exp (3 * C) / (3 : ℝ) ^ (h + 1) := by congr 1 <;> ring_nf
    rw [← hmul]
    exact mul_le_mul_of_nonneg_right (by simpa [a] using ha) hr
  have hsumU : bernoulliBlockUMeanOn s g h ≤ a + bernoulliBlockTMeanOn s g h := by
    have h2 : bernoulliBlockUMeanOn s g h - a ≤ bernoulliBlockTMeanOn s g h := by
      simpa [a] using hbounds.2
    linarith
  calc
    bernoulliBlockUMeanOn s g h ≤ a + bernoulliBlockTMeanOn s g h := hsumU
    _ ≤ a + a * r := by
      simpa [add_comm] using add_le_add_left (ht.trans hfac) a
    _ = a * (1 + r) := by ring
    _ = (∏ i ∈ s, (1 - g i)) *
        (1 + Real.exp (3 * C + C / η) / (3 : ℝ) ^ (h + 1)) := by simp [a, r]

/-- Sum of the relative block tails at degrees `(j+1)H`. -/
theorem sum_block_relative_tail {N H : ℕ} (hH : 1 ≤ H) (A : ℝ) (hA : 0 ≤ A) :
    ∑ j ∈ Finset.range N, A / (3 : ℝ) ^ ((j + 1) * H + 1) ≤
      2 * A * Real.exp (-(H : ℝ)) := by
  classical
  have hterm : ∀ j ∈ Finset.range N,
      A / (3 : ℝ) ^ ((j + 1) * H + 1) ≤ A / (3 : ℝ) ^ ((j + 1) * H) := by
    intro j hj
    have hp : (3 : ℝ) ^ ((j + 1) * H) ≤ (3 : ℝ) ^ ((j + 1) * H + 1) := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) ((j + 1) * H)]
    exact div_le_div_of_nonneg_left hA (pow_pos (by norm_num : (0 : ℝ) < 3) _) hp
  have hscale : (∑ j ∈ Finset.range N, A / (3 : ℝ) ^ ((j + 1) * H)) =
      A * ∑ j ∈ Finset.range N, 1 / (3 : ℝ) ^ ((j + 1) * H) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    ∑ j ∈ Finset.range N, A / (3 : ℝ) ^ ((j + 1) * H + 1) ≤
        ∑ j ∈ Finset.range N, A / (3 : ℝ) ^ ((j + 1) * H) :=
      Finset.sum_le_sum hterm
    _ = A * ∑ j ∈ Finset.range N, 1 / (3 : ℝ) ^ ((j + 1) * H) := hscale
    _ ≤ A * (2 * Real.exp (-(H : ℝ))) :=
      mul_le_mul_of_nonneg_left (reciprocal_three_geometric_le_exp hH) hA
    _ = 2 * A * Real.exp (-(H : ℝ)) := by ring

/-- For `0 ≤ x ≤ 1`, the relative excess of `exp x` is at most `2x`. -/
theorem exp_sub_one_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ 2 * x := by
  have hxabs : |x| ≤ 1 := by simpa [abs_of_nonneg hx0] using hx1
  have h := Real.abs_exp_sub_one_le (x := x) hxabs
  have hxexp : 1 ≤ Real.exp x := Real.one_le_exp hx0
  simpa [abs_of_nonneg (sub_nonneg.mpr hxexp), abs_of_nonneg hx0] using h

/-- The finite dyadic first moment is at most its infinite value, four. -/
theorem sum_range_succ_div_pow_two_eq {n : ℕ} :
    (∑ j ∈ Finset.range (n + 1), ((j + 1 : ℝ) / (2 : ℝ) ^ j)) =
      4 - ((n + 3 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

theorem sum_range_succ_div_pow_two_le (N : ℕ) :
    (∑ j ∈ Finset.range N, ((j + 1 : ℝ) / (2 : ℝ) ^ j)) ≤ 4 := by
  cases N with
  | zero => simp
  | succ n =>
    rw [sum_range_succ_div_pow_two_eq]
    have hnonneg : 0 ≤ ((n + 3 : ℕ) : ℝ) / (2 : ℝ) ^ n := by positivity
    linarith

/-- The ordinary dyadic geometric sum is at most two. -/
theorem sum_range_inv_two_pow_le_two (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / (2 : ℝ) ^ j) ≤ 2 := by
  have hgeom :
      (∑ j ∈ Finset.range N, 1 / (2 : ℝ) ^ j) * (1 / 2) =
        1 - (1 / 2 : ℝ) ^ N := by
    have h := geom_sum_mul_neg (1 / 2 : ℝ) N
    norm_num at h ⊢
    simpa [one_div_pow] using h
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ N := pow_nonneg (by norm_num) N
  nlinarith [hgeom, hpow]

/-- The degree profile `(j+1)H`, with one extra correction degree in any block, has total
logarithmic exponent at most `4H+2`. -/
theorem sum_fin_degree_profile_le {N H : ℕ} :
    (∑ j : Fin N, (((j.val + 1) * H + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j.val) ≤
      4 * (H : ℝ) + 2 := by
  have h := sum_range_succ_div_pow_two_le N
  have h' := sum_range_inv_two_pow_le_two N
  let f : ℕ → ℝ := fun j => (((j + 1) * H + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j
  have hsum : (∑ j : Fin N, f j) = ∑ j ∈ Finset.range N, f j :=
    Fin.sum_univ_eq_sum_range f N
  calc
    (∑ j : Fin N, (((j.val + 1) * H + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j.val) =
        ∑ j ∈ Finset.range N, f j := by simpa [f] using hsum
    _ = ∑ j ∈ Finset.range N,
          ((j + 1 : ℝ) * H / (2 : ℝ) ^ j + 1 / (2 : ℝ) ^ j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      push_cast
      ring
    _ = (H : ℝ) * ∑ j ∈ Finset.range N, ((j + 1 : ℝ) / (2 : ℝ) ^ j) +
          ∑ j ∈ Finset.range N, 1 / (2 : ℝ) ^ j := by
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ j ∈ Finset.range N, ((j + 1 : ℝ) * H / (2 : ℝ) ^ j)) =
            (∑ j ∈ Finset.range N, ((j + 1 : ℝ) / (2 : ℝ) ^ j)) * H := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (H : ℝ) * ∑ j ∈ Finset.range N, ((j + 1 : ℝ) / (2 : ℝ) ^ j) := by ring
    _ ≤ (H : ℝ) * 4 + 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg H)) h'
    _ = 4 * (H : ℝ) + 2 := by ring

end ArtinPrimitiveRoots.Sieve.Block
