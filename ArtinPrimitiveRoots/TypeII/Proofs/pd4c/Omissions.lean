import ArtinPrimitiveRoots.TypeII.PD.Memory
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

/-- Independent uniform slot permutations induce the uniform law on omission tuples. -/
theorem omission_average_uniform {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] [Nonempty α] (x : ι → α) (f : (ι → α) → ℝ) :
    (Fintype.card (ι → Equiv.Perm α) : ℝ)⁻¹ *
        ∑ σ : ι → Equiv.Perm α, f (fun i => σ i (x i)) =
      (Fintype.card (ι → α) : ℝ)⁻¹ * ∑ y : ι → α, f y := by
  have hbase (y : ι → α) :
      (∑ σ : ι → Equiv.Perm α, f (fun i => σ i (y i))) =
        ∑ σ : ι → Equiv.Perm α, f (fun i => σ i (x i)) := by
    let τ : ι → Equiv.Perm α := fun i => Equiv.swap (x i) (y i)
    have h := Equiv.sum_comp (Equiv.mulRight τ) (fun σ : ι → Equiv.Perm α =>
      f (fun i => σ i (x i)))
    simpa [τ, Equiv.Perm.mul_apply] using h
  have hinner (σ : ι → Equiv.Perm α) :
      (∑ y : ι → α, f (fun i => σ i (y i))) = ∑ y : ι → α, f y := by
    exact (Equiv.piCongrRight fun i => σ i).sum_comp f
  have hcount : (Fintype.card (ι → α) : ℝ) *
        (∑ σ : ι → Equiv.Perm α, f (fun i => σ i (x i))) =
      (Fintype.card (ι → Equiv.Perm α) : ℝ) * ∑ y : ι → α, f y := by
    calc
      _ = ∑ y : ι → α, ∑ σ : ι → Equiv.Perm α, f (fun i => σ i (y i)) := by
        simp only [hbase, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ σ : ι → Equiv.Perm α, ∑ y : ι → α, f (fun i => σ i (y i)) := by
        rw [Finset.sum_comm]
      _ = _ := by simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hX : (Fintype.card (ι → α) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ι → α) ≠ 0)
  have hG : (Fintype.card (ι → Equiv.Perm α) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ι → Equiv.Perm α) ≠ 0)
  field_simp [hX, hG]
  nlinarith [hcount]

/-- At most one compatible omission tuple has permutation mass at most `M^{-K}`. -/
theorem omission_probability_le_singleton (K M : ℕ) (hM : 0 < M)
    (x : Fin K → Fin M) (P : (Fin K → Fin M) → Prop)
    (y₀ : Fin K → Fin M) (hP : ∀ y, P y → y = y₀) :
    (Fintype.card (Fin K → Equiv.Perm (Fin M)) : ℝ)⁻¹ *
        ∑ σ : Fin K → Equiv.Perm (Fin M),
          (if P (fun i => σ i (x i)) then (1 : ℝ) else 0) ≤
      1 / (M : ℝ) ^ K := by
  letI : DecidablePred P := fun y => Classical.propDecidable (P y)
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have havg := omission_average_uniform x (fun y => if P y then (1 : ℝ) else 0)
  change (Fintype.card (Fin K → Equiv.Perm (Fin M)) : ℝ)⁻¹ *
    (∑ σ : Fin K → Equiv.Perm (Fin M), if P (fun i => σ i (x i)) then (1 : ℝ) else 0) ≤ _
  calc
    _ = _ := havg
    _ ≤ _ := by
      have hsum : (∑ y : Fin K → Fin M, if P y then (1 : ℝ) else 0) ≤ 1 := by
        calc
          _ ≤ ∑ y : Fin K → Fin M, if y = y₀ then (1 : ℝ) else 0 := by
            apply Finset.sum_le_sum
            intro y hy
            by_cases hp : P y
            · have hy₀ := hP y hp
              subst y
              simp [hp]
            · simp only [if_neg hp]
              split_ifs <;> norm_num
          _ = 1 := by simp
      have hcard : (Fintype.card (Fin K → Fin M) : ℝ) = (M : ℝ) ^ K := by
        simp [Fintype.card_fun]
      rw [hcard]
      simpa only [one_div, mul_one] using
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg M) K))

/-- A deleted label cannot divide the complementary product when all labels are distinct. -/
theorem omitted_prime_not_dvd {x : ℝ} {K : ℕ} (p : PrimeLists x K)
    (hp : ∀ i j, (p i j).Prime)
    (hinj : Function.Injective (fun q : Fin K × Fin (slotCount x) => p q.1 q.2))
    (om : Fin K → Fin (slotCount x)) (i : Fin K) :
    ¬ p i (om i) ∣ omissionProduct p om := by
  intro hdiv
  rw [omissionProduct, (hp i (om i)).prime.dvd_finsetProd_iff] at hdiv
  obtain ⟨i', _, hdiv⟩ := hdiv
  rw [(hp i (om i)).prime.dvd_finsetProd_iff] at hdiv
  obtain ⟨j, _, hdiv⟩ := hdiv
  by_cases hj : j ≠ om i'
  · rw [if_pos hj] at hdiv
    have heq : p i (om i) = p i' j := ((hp i' j).dvd_iff_eq (hp i (om i)).ne_one).mp hdiv |>.symm
    have hq : (i, om i) = (i', j) := hinj heq
    have hi : i = i' := congrArg Prod.fst hq
    have hslot : om i = j := congrArg Prod.snd hq
    exact hj (by simpa [← hi] using hslot.symm)
  · rw [if_neg hj] at hdiv
    exact (hp i (om i)).not_dvd_one hdiv

/-- Distinct source labels make the numeric omission product identify every omitted slot. -/
theorem omissionProduct_injective {x : ℝ} {K : ℕ} (p : PrimeLists x K)
    (hp : ∀ i j, (p i j).Prime)
    (hinj : Function.Injective (fun q : Fin K × Fin (slotCount x) => p q.1 q.2)) :
    Function.Injective (omissionProduct p) := by
  intro om om' hprod
  funext i
  by_contra hneq
  have hslot : om i ≠ om' i := hneq
  have hinner : p i (om i) ∣
      ∏ j : Fin (slotCount x), if j ≠ om' i then p i j else 1 := by
    have h := Finset.dvd_prod_of_mem
      (fun j : Fin (slotCount x) => if j ≠ om' i then p i j else 1)
      (Finset.mem_univ (om i))
    simpa [hslot] using h
  have houter : (∏ j : Fin (slotCount x), if j ≠ om' i then p i j else 1) ∣
      omissionProduct p om' := by
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hdiv := dvd_trans hinner houter
  rw [← hprod] at hdiv
  exact omitted_prime_not_dvd p hp hinj om i hdiv

/-- A banned target prime cannot divide the shared source product. -/
theorem pd4c_prime_not_dvd_sharedProduct {x : ℝ} {K : ℕ} (p : PrimeLists x K)
    (hp : ∀ i j, (p i j).Prime) (q : ℕ) (hq : q.Prime)
    (hban : ∀ i j, q ≠ p i j) : ¬ q ∣ sharedProduct p := by
  intro hdiv
  rw [sharedProduct, hq.prime.dvd_finsetProd_iff] at hdiv
  obtain ⟨i, _, hdiv⟩ := hdiv
  rw [hq.prime.dvd_finsetProd_iff] at hdiv
  obtain ⟨j, _, hdiv⟩ := hdiv
  by_cases hj : j.val < momentJ x
  · rw [if_pos hj] at hdiv
    have heq : p i j = q := ((hp i j).dvd_iff_eq hq.ne_one).mp hdiv
    exact hban i j heq.symm
  · rw [if_neg hj] at hdiv
    exact hq.not_dvd_one hdiv

/-- Slot reordering sends each omission to its corresponding original slot. -/
theorem pd4c_omissionProduct_permuteLists {x : ℝ} {K : ℕ} (p : PrimeLists x K)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (om : Fin K → Fin (slotCount x)) :
    omissionProduct (permuteLists σ p) om = omissionProduct p (fun i => σ i (om i)) := by
  unfold omissionProduct permuteLists
  apply Finset.prod_congr rfl
  intro i hi
  calc
    (∏ j : Fin (slotCount x), if j ≠ om i then p i (σ i j) else 1) =
        ∏ j : Fin (slotCount x), if σ i j ≠ σ i (om i) then p i (σ i j) else 1 := by
      apply Finset.prod_congr rfl
      intro j hj
      by_cases h : j = om i
      · subst j
        simp
      · have hσ : σ i j ≠ σ i (om i) := fun heq => h ((σ i).injective heq)
        simp only [if_pos h, if_pos hσ]
    _ = ∏ j : Fin (slotCount x), if j ≠ σ i (om i) then p i j else 1 := by
      simpa only [Function.comp_def] using
        Equiv.prod_comp (σ i) (fun j => if j ≠ σ i (om i) then p i j else 1)

/-- The set of numeric goodness trial values is independent of the internal slot ordering. -/
theorem pd4c_goodnessTrial_permuteLists_iff {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (p : PrimeLists x K) (σ : Fin K → Equiv.Perm (Fin (slotCount x)))
    (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K) (fresh : Fin K → ℕ) (n : ℕ) :
    IsGoodnessTrialValue a (permuteLists σ p) d₀ I iStar fresh n ↔
      IsGoodnessTrialValue a p d₀ I iStar fresh n := by
  constructor
  · rintro ⟨om, z, hn, hlo, hhi, hz⟩
    refine ⟨fun i => σ i (om i), z, ?_, ?_, ?_, hz⟩
    · simpa only [pd4c_omissionProduct_permuteLists] using hn
    · simpa only [pd4c_omissionProduct_permuteLists] using hlo
    · simpa only [pd4c_omissionProduct_permuteLists] using hhi
  · rintro ⟨om, z, hn, hlo, hhi, hz⟩
    refine ⟨fun i => (σ i).symm (om i), z, ?_, ?_, ?_, hz⟩
    · simpa only [pd4c_omissionProduct_permuteLists, Equiv.apply_symm_apply] using hn
    · simpa only [pd4c_omissionProduct_permuteLists, Equiv.apply_symm_apply] using hlo
    · simpa only [pd4c_omissionProduct_permuteLists, Equiv.apply_symm_apply] using hhi

theorem pd4c_goodTestOne_permuteLists_iff {x : ℝ} {K : ℕ} (Y d₀ : ℝ)
    (p : PrimeLists x K) (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (r : ℝ) :
    goodTestOne x Y d₀ (permuteLists σ p) r ↔ goodTestOne x Y d₀ p r := by
  constructor
  · intro h om hlo hhi l hl hly
    have hlo' : d₀ ≤ (omissionProduct (permuteLists σ p) (fun i => (σ i).symm (om i)) : ℝ) := by
      simpa only [pd4c_omissionProduct_permuteLists, Equiv.apply_symm_apply] using hlo
    have hhi' : (omissionProduct (permuteLists σ p) (fun i => (σ i).symm (om i)) : ℝ) < 2 * d₀ := by
      simpa only [pd4c_omissionProduct_permuteLists, Equiv.apply_symm_apply] using hhi
    simpa only [pd4c_omissionProduct_permuteLists, Equiv.apply_symm_apply] using
      h (fun i => (σ i).symm (om i)) hlo' hhi' l hl hly
  · intro h om hlo hhi l hl hly
    have hlo' : d₀ ≤ (omissionProduct p (fun i => σ i (om i)) : ℝ) := by
      simpa only [pd4c_omissionProduct_permuteLists] using hlo
    have hhi' : (omissionProduct p (fun i => σ i (om i)) : ℝ) < 2 * d₀ := by
      simpa only [pd4c_omissionProduct_permuteLists] using hhi
    simpa only [pd4c_omissionProduct_permuteLists] using
      h (fun i => σ i (om i)) hlo' hhi' l hl hly

theorem pd4c_goodTestTwo_permuteLists_iff {x : ℝ} {K : ℕ} (d₀ : ℝ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (r : ℝ) :
    goodTestTwo x d₀ K a (permuteLists σ p) r ↔ goodTestTwo x d₀ K a p r := by
  unfold goodTestTwo
  simp only [pd4c_goodnessTrial_permuteLists_iff]

theorem pd4c_goodRatio_permuteLists_iff {x : ℝ} {K : ℕ} (Y d₀ : ℝ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (r : ℝ) :
    IsGoodRatio x Y d₀ K a (permuteLists σ p) r ↔ IsGoodRatio x Y d₀ K a p r := by
  exact and_congr (pd4c_goodTestOne_permuteLists_iff Y d₀ p σ r)
    (pd4c_goodTestTwo_permuteLists_iff d₀ a p σ r)

theorem pd4c_primeBand_disjoint_eventually (a b : ℝ) (hab : a < b) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → Disjoint (primeBand x a) (primeBand x b) := by
  have hpow : Filter.Tendsto (fun x : ℝ => Real.rpow (Real.log x) (b - a))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp Real.tendsto_log_atTop
  have hevent : ∀ᶠ x : ℝ in Filter.atTop, 2 < Real.rpow (Real.log x) (b - a) :=
    hpow.eventually_gt_atTop 2
  rcases Filter.eventually_atTop.mp hevent with ⟨x₁, hx₁⟩
  refine ⟨max 2 x₁, le_max_left _ _, ?_⟩
  intro x hx
  have hx₂ : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hgap : 2 < Real.rpow (Real.log x) (b - a) := hx₁ x (le_trans (le_max_right _ _) hx)
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hpa : 0 < Real.rpow (Real.log x) a := Real.rpow_pos_of_pos hLpos a
  have hpowMul : Real.rpow (Real.log x) b =
      Real.rpow (Real.log x) a * Real.rpow (Real.log x) (b - a) := by
    calc
      Real.rpow (Real.log x) b = Real.rpow (Real.log x) (a + (b - a)) := by congr 1 <;> ring
      _ = Real.rpow (Real.log x) a * Real.rpow (Real.log x) (b - a) :=
        Real.rpow_add hLpos _ _
  have hsep : 2 * Real.rpow (Real.log x) a < Real.rpow (Real.log x) b := by
    rw [hpowMul]
    nlinarith [mul_lt_mul_of_pos_left hgap hpa]
  apply Finset.disjoint_left.mpr
  intro p hp hq
  rcases Finset.mem_filter.mp hp with ⟨_, ⟨_, _, hpupper⟩⟩
  rcases Finset.mem_filter.mp hq with ⟨_, ⟨_, hqlower, _⟩⟩
  have hexp : Real.exp (2 * Real.rpow (Real.log x) a) <
      Real.exp (Real.rpow (Real.log x) b) := Real.exp_lt_exp.mpr hsep
  have hupper' : (p : ℝ) < Real.exp (Real.rpow (Real.log x) b) := lt_of_le_of_lt hpupper hexp
  linarith

/-- Valid ordered band data give one threshold at which all distinct marked bands are disjoint. -/
theorem pd4c_validBands_disjoint_eventually (K : ℕ) (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand x (a i)) (primeBand x (a j)) := by
  have hevent : ∀ᶠ x : ℝ in Filter.atTop, ∀ ij : Fin K × Fin K,
      ij.1 = ij.2 ∨ Disjoint (primeBand x (a ij.1)) (primeBand x (a ij.2)) := by
    rw [Filter.eventually_all]
    intro ij
    by_cases hij : ij.1 = ij.2
    · exact Filter.Eventually.of_forall fun _ => Or.inl hij
    · rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hab : a ij.1 < a ij.2 := ha.2.2 _ _ hlt
        obtain ⟨x₁, hx₁₂, hdis⟩ := pd4c_primeBand_disjoint_eventually (a ij.1) (a ij.2) hab
        filter_upwards [Filter.eventually_ge_atTop x₁] with x hx
        exact Or.inr (hdis x hx)
      · have hab : a ij.2 < a ij.1 := ha.2.2 _ _ hgt
        obtain ⟨x₁, hx₁₂, hdis⟩ := pd4c_primeBand_disjoint_eventually (a ij.2) (a ij.1) hab
        filter_upwards [Filter.eventually_ge_atTop x₁] with x hx
        exact Or.inr (disjoint_comm.mp (hdis x hx))
  rcases Filter.eventually_atTop.mp hevent with ⟨x₁, hx₁⟩
  refine ⟨max 2 x₁, le_max_left _ _, ?_⟩
  intro x hx i j hij
  have hxpair := hx₁ x (le_trans (le_max_right _ _) hx) (i, j)
  rcases hxpair with heq | hdis
  · exact (hij heq).elim
  · exact hdis

/-- Within-group distinctness becomes global distinctness when bands are disjoint. -/
theorem pd4c_validPrimeLists_global_injective {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    Function.Injective (fun ij : Fin K × Fin (slotCount x) => p ij.1 ij.2) := by
  intro ij ij' heq
  have hgroup : ij.1 = ij'.1 := by
    by_contra hne
    have hdis := hbands ij.1 ij'.1 hne
    have hnot := (Finset.disjoint_left.mp hdis) (hp.1 ij.1 ij.2).2
    exact hnot (by simpa only [heq] using (hp.1 ij'.1 ij'.2).2)
  have hslot : ij.2 = ij'.2 := by
    by_contra hne
    apply hp.2 ij.1 ij.2 ij'.2 hne
    simpa only [hgroup] using heq
  exact Prod.ext hgroup hslot


/-- A nonzero raw multiplier forces its exact integer determinant equation. -/
theorem pd4c_rawMultiplier_support {K : ℕ} (F : PDFix K) (S : PDScale)
    (D a b : ℕ) (t : ℤ) (h : rawMultiplier F S D a b t ≠ 0) :
    t = (b : ℤ) - a := by
  by_contra ht
  apply h
  simp [rawMultiplier, ht]

/-- The raw determinant equation has the same orientation for the two alternating edge types. -/
theorem pd4c_raw_edge_det {K : ℕ} (F : PDFix K) (S : PDScale)
    (forward : Bool) (p q : PrimeLists S.x K) (z z' : ℤ × ℤ)
    (hdiv : (sharedProduct p : ℤ) ∣ det2 z z')
    (h : edgeMultiplier F S forward true p q z z' ≠ 0) :
    det2 z z' = (sharedProduct p : ℤ) * ((lastProduct p : ℤ) - lastProduct q) := by
  cases forward with
  | false =>
    have hraw : rawMultiplier F S (sharedProduct p) (lastProduct p) (lastProduct q)
        (det2 z' z / (sharedProduct p : ℤ)) ≠ 0 := by
      intro hz
      apply h
      simp [edgeMultiplier, hz]
    have hswap : det2 z' z = -det2 z z' := by dsimp [det2]; ring
    have hdiv' : (sharedProduct p : ℤ) ∣ det2 z' z := by
      rw [hswap]
      exact dvd_neg.mpr hdiv
    have ht := pd4c_rawMultiplier_support F S _ _ _ _ hraw
    have hmul := Int.mul_ediv_cancel' hdiv'
    rw [ht, hswap] at hmul
    linear_combination hmul
  | true =>
    have hraw : rawMultiplier F S (sharedProduct p) (lastProduct q) (lastProduct p)
        (det2 z z' / (sharedProduct p : ℤ)) ≠ 0 := by
      intro hz
      apply h
      simp [edgeMultiplier, hz]
    have ht := pd4c_rawMultiplier_support F S _ _ _ _ hraw
    have hmul := Int.mul_ediv_cancel' hdiv
    rw [ht] at hmul
    exact hmul.symm

end

end ArtinPrimitiveRoots.TypeII.PD
