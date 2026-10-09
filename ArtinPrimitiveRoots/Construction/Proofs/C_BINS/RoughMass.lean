import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.Positivity
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.ProgressionSieve

namespace ArtinPrimitiveRoots.Construction.Proofs.C_BINS

open Classical
open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.TypeII

private theorem smallGroupBound (x ε : ℝ) (r : ℕ)
    (hx : 1 ≤ x) (hε : ε < 11 / 100)
    (hr : r ∈ Finset.range (⌊Real.rpow x ε⌋₊ + 1)) :
    (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) := by
  have hrNat : r ≤ ⌊Real.rpow x ε⌋₊ := by
    have hr' : r < ⌊Real.rpow x ε⌋₊ + 1 := Finset.mem_range.mp hr
    omega
  have hrε : (r : ℝ) ≤ Real.rpow x ε :=
    (Nat.cast_le.mpr hrNat).trans (Nat.floor_le (Real.rpow_nonneg (by linarith) ε))
  exact hrε.trans (Real.rpow_le_rpow_of_exponent_le hx hε.le)

private theorem pairWeight_map_injective
    (x : ℝ) (c K : ℕ) (a : Fin K → ℝ) (Ψ : ℝ → ℝ)
    (hΨ : IsTestFunction Ψ)
    (T : Finset (ℕ × ℕ)) (hcpos : 0 < c) (hx2 : 2 ≤ x)
    (hSmall : ∀ z ∈ T, (z.1 : ℝ) ≤ Real.rpow x (11 / 100 : ℝ))
    (hGood : ∀ z ∈ T,
      z.2.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (z.2 : ℝ) ∧
        Ψ (((c * z.1 * z.2 + 1 : ℕ) : ℝ) / x) *
          markedWeight x K a (1 / 2 : ℝ) z.1 ≠ 0) :
    Set.InjOn (fun z : ℕ × ℕ => c * z.1 * z.2 + 1) T := by
  intro z hz z' hz' hEq
  rcases hGood z hz with ⟨hq, hlarge, hweight⟩
  rcases hGood z' hz' with ⟨hq', hlarge', hweight'⟩
  have hval : c * z.1 * z.2 = c * z'.1 * z'.2 := Nat.add_right_cancel hEq
  have hxgt : 1 < x := by linarith
  have hrpos : 0 < z.1 := by
    have hb := pairWeight_ne_zero_bounds x c K a z.1 z.2 Ψ hΨ
      (lt_of_lt_of_le (by norm_num) hx2) hweight
    by_contra hnot
    have hz0 : z.1 = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz0] at hb
    norm_num at hb
    linarith [hb.1, hx2]
  have hprodpos : 0 < c * z.1 * z.2 := Nat.mul_pos (Nat.mul_pos hcpos hrpos) hq.pos
  have hfac := largePrimeFactorization_unique x c (c * z.1 * z.2)
    z.1 z'.1 z.2 z'.2 hxgt hcpos hq hq' (hSmall z' hz') hlarge hprodpos rfl
      (by simpa [Nat.mul_assoc] using hval)
  exact Prod.ext hfac.1 hfac.2

theorem roughConstructionMass_ge_smallSiftedSum
    (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ) (Ψ : ℝ → ℝ)
    (ε b : ℝ) (hc24 : c = 2 ∨ c = 4) (ha : ValidBands K a)
    (hΨ : IsTestFunction Ψ) (hε : 0 < ε) (hεsmall : ε < 11 / 100) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      roughConstructionMass x M c u K a Ψ (Real.rpow x b) ≥
        (∑ r ∈ (Finset.range (⌊Real.rpow x ε⌋₊ + 1)).filter
            (fun r => IsGroupInteger x K a r),
          markedWeight x K a (1 / 2 : ℝ) r *
            siftedProgressionPrimeSum x M c u Ψ r (Real.rpow x b)) := by
  classical
  have hcpos : 0 < c := by rcases hc24 with h | h <;> omega
  obtain ⟨xCut, hCut⟩ := markedPrimes_avoid_fixed_and_large K a ha c hcpos
  refine ⟨max xCut 2, le_max_right _ _, ?_⟩
  intro x hx
  have hxCut : xCut ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  let z : ℝ := Real.rpow x b
  rcases hCut x hxCut with ⟨hcmarked, hQmarked⟩
  let Qset : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let R : Finset ℕ := (Finset.range (⌊Real.rpow x ε⌋₊ + 1)).filter
    (fun r => IsGroupInteger x K a r)
  let pairWeight : ℕ × ℕ → ℝ := fun z =>
    Ψ (((c * z.1 * z.2 + 1 : ℕ) : ℝ) / x) *
      markedWeight x K a (1 / 2 : ℝ) z.1
  let good : ℕ × ℕ → Prop := fun pair =>
    progressionSieveBaseCondition x M c u pair.1 pair.2 ∧
      roughAbove (c * pair.1 * pair.2 + 1) z ∧ pairWeight pair ≠ 0
  let T : Finset (ℕ × ℕ) := (R.product Qset).filter good
  let D : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let roughD : Finset ℕ := D.filter (fun d => roughAbove d z)
  have hGroupBound (r : ℕ) (hr : r ∈ R) :
      (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) :=
    smallGroupBound x ε r hxone hεsmall (Finset.mem_filter.mp hr).1
  have hGoodFactor (z' : ℕ × ℕ) (hz' : z' ∈ T) :
      z'.2.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (z'.2 : ℝ) ∧ pairWeight z' ≠ 0 := by
    rcases Finset.mem_filter.mp hz' with ⟨_, ⟨hbase, _, hne⟩⟩
    exact ⟨hbase.1, hbase.2.1, hne⟩
  have hSmallBound (z' : ℕ × ℕ) (hz' : z' ∈ T) :
      (z'.1 : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) := by
    have hzProd := (Finset.mem_filter.mp hz').1
    have hrMem := (Finset.mem_product.mp hzProd).1
    exact hGroupBound z'.1 hrMem
  have hInjective : Set.InjOn (fun z' : ℕ × ℕ => c * z'.1 * z'.2 + 1) T :=
    pairWeight_map_injective x c K a Ψ hΨ T hcpos hx2 hSmallBound hGoodFactor
  let map : ℕ × ℕ → ℕ := fun z' => c * z'.1 * z'.2 + 1
  let image := T.image map
  have hImageSub : image ⊆ roughD := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨z', hz', rfl⟩
    rcases Finset.mem_filter.mp hz' with ⟨hzProd, ⟨_, hrough, hne⟩⟩
    rcases Finset.mem_product.mp hzProd with ⟨hr, hq⟩
    have hb := pairWeight_ne_zero_bounds x c K a z'.1 z'.2 Ψ hΨ hxpos hne
    have hdNat : map z' ≤ ⌊2 * x⌋₊ :=
      (Nat.le_floor_iff (by positivity)).2 hb.2.le
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hdNat), by simpa [map] using hrough⟩
  have hPairEq (z' : ℕ × ℕ) (hz' : z' ∈ T) :
      conWeight x M c u K a Ψ (map z') = pairWeight z' := by
    rcases Finset.mem_filter.mp hz' with ⟨hzProd, ⟨hbase, hrough, hne⟩⟩
    rcases Finset.mem_product.mp hzProd with ⟨hr, hq⟩
    have hrGroup : IsGroupInteger x K a z'.1 := (Finset.mem_filter.mp hr).2
    have hrpos : 0 < z'.1 := by
      have hb := pairWeight_ne_zero_bounds x c K a z'.1 z'.2 Ψ hΨ hxpos hne
      by_contra hnot
      have hz0 : z'.1 = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hz0] at hb
      norm_num at hb
      linarith [hb.1, hx2]
    have hprime : z'.2.Prime := hbase.1
    have hlarge : Real.rpow x (9 / 10 : ℝ) < (z'.2 : ℝ) := hbase.2.1
    have hres : (((c * z'.1 * z'.2 + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) := hbase.2.2
    exact conWeight_eq_pair_weight x M c u K a Ψ z'.1 z'.2 hrGroup hcpos hrpos hprime
      hlarge hcmarked (hQmarked z'.2 hprime hlarge) hres
  have hImageSum :
      (∑ d ∈ image, conWeight x M c u K a Ψ d) =
        ∑ z' ∈ T, pairWeight z' := by
    calc
      _ = ∑ z' ∈ T, conWeight x M c u K a Ψ (map z') := by
        simpa [image, map] using
          (Finset.sum_image (f := fun d => conWeight x M c u K a Ψ d)
            (g := map) hInjective)
      _ = ∑ z' ∈ T, pairWeight z' := by
        apply Finset.sum_congr rfl
        intro z' hz'
        exact hPairEq z' hz'
  have hMassReindex :
      roughConstructionMass x M c u K a Ψ z =
        ∑ d ∈ roughD, conWeight x M c u K a Ψ d := by
    unfold roughConstructionMass
    dsimp [D, roughD]
    rw [← Finset.sum_filter]
  have hWeightNonneg (d : ℕ) : 0 ≤ conWeight x M c u K a Ψ d :=
    conWeight_nonneg x M c u K a Ψ hΨ d
  have hLowerImage :
      (∑ d ∈ image, conWeight x M c u K a Ψ d) ≤
        ∑ d ∈ roughD, conWeight x M c u K a Ψ d :=
    Finset.sum_le_sum_of_subset_of_nonneg hImageSub (fun d _ _ => hWeightNonneg d)
  have hPairSum :
      (∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r *
          siftedProgressionPrimeSum x M c u Ψ r z) =
        ∑ z' ∈ T, pairWeight z' := by
    let Qweight : ℕ × ℕ → ℝ := fun z' =>
      if progressionSieveBaseCondition x M c u z'.1 z'.2 ∧
          roughAbove (c * z'.1 * z'.2 + 1) z then pairWeight z' else 0
    have hExpand :
        (∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r *
          siftedProgressionPrimeSum x M c u Ψ r z) =
        ∑ r ∈ R, ∑ q ∈ Qset, Qweight (r, q) := by
      apply Finset.sum_congr rfl
      intro r hr
      dsimp [Qweight, siftedProgressionPrimeSum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hbase : progressionSieveBaseCondition x M c u r q
      · by_cases hrough : roughAbove (c * r * q + 1) z <;>
          simp [pairWeight, hbase, hrough] <;> ring
      · simp [hbase]
    calc
      _ = ∑ r ∈ R, ∑ q ∈ Qset, Qweight (r, q) := hExpand
      _ = ∑ z' ∈ R.product Qset, Qweight z' := by
        rw [← Finset.sum_product]
        rfl
      _ = ∑ z' ∈ T, pairWeight z' := by
        dsimp [T, good]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z' hz'
        by_cases hbase : progressionSieveBaseCondition x M c u z'.1 z'.2
        · by_cases hrough : roughAbove (c * z'.1 * z'.2 + 1) z
          · by_cases hne : pairWeight z' ≠ 0
            · simp [Qweight, hbase, hrough, hne]
            · have hzero : pairWeight z' = 0 := not_ne_iff.mp hne
              simp [Qweight, hbase, hrough, hzero]
          · simp [Qweight, hbase, hrough]
        · simp [Qweight, hbase]
  calc
    roughConstructionMass x M c u K a Ψ z =
        ∑ d ∈ roughD, conWeight x M c u K a Ψ d := hMassReindex
    _ ≥ ∑ d ∈ image, conWeight x M c u K a Ψ d := hLowerImage
    _ = ∑ z' ∈ T, pairWeight z' := hImageSum
    _ = _ := hPairSum.symm

end ArtinPrimitiveRoots.Construction.Proofs.C_BINS
