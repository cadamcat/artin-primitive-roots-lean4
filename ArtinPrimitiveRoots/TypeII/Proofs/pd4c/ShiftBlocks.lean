import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.WeightedBlocks
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.WeightedRestriction

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical
open scoped BigOperators

noncomputable section

/-- Weighted common blocks assemble into the kernel of one fixed cell shift. -/
theorem finite_weighted_fixed_shift_kernel_bound {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (T : Finset ι) (μ : ι → ℝ) (hμ : ∀ u ∈ T, 0 ≤ μ u)
    (line : ι → κ) (cell : ι → ℤ) (m : ℤ) (C : ℝ)
    (hC : 0 ≤ C) (hm : |(m : ℝ)| ≤ C)
    (base : ι → ι → ℂ) (d e : ι → ℂ) (R : ℝ)
    (hcommon : ∀ z ∈ T, ∀ U : Finset ι, U ⊆ T →
      (∀ u ∈ U, line z = line u ∧ |((cell u-cell z : ℤ) : ℝ)| ≤ C) →
      ∀ g : ι → ℂ,
      (∑ u ∈ U, μ u*‖d u*(∑ v ∈ U, base u v*(μ v : ℂ)*e v*g v)‖^2) ≤
        R^2*(∑ v ∈ U, μ v*‖g v‖^2))
    (f : ι → ℂ) :
    let k := fun u v : ι => if line u = line v ∧ cell v-cell u = m then base u v else 0
    (∑ u ∈ T, μ u*‖d u*(∑ v ∈ T, k u v*(μ v : ℂ)*e v*f v)‖^2) ≤
      R^2*(∑ v ∈ T, μ v*‖f v‖^2) := by
  let outClass : ι → κ × ℤ := fun u => (line u, cell u)
  let inClass : ι → κ × ℤ := fun u => (line u, cell u-m)
  let k : ι → ι → ℂ := fun u v =>
    if line u = line v ∧ cell v-cell u = m then base u v else 0
  let H : ι → ι → ℂ := fun u v => d u*k u v*e v
  have hrow (I : Finset ι) (u : ι) :
      (∑ v ∈ I, H u v*(μ v : ℂ)*f v) =
        d u*(∑ v ∈ I, k u v*(μ v : ℂ)*e v*f v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [H]
    ring
  have hsupport (u : ι) (hu : u ∈ T) (v : ι) (hv : v ∈ T)
      (hne : outClass u ≠ inClass v) : H u v = 0 := by
    by_cases h : line u = line v ∧ cell v-cell u = m
    · have heq : outClass u = inClass v := Prod.ext h.1 (by
        change cell u = cell v-m
        omega)
      exact (hne heq).elim
    · simp only [H, k, if_neg h, mul_zero, zero_mul]
  have hblocks (b : κ × ℤ) (hb : b ∈ T.image outClass ∪ T.image inClass) :
      (∑ u ∈ T.filter (fun u => outClass u = b),
        μ u*‖∑ v ∈ T.filter (fun v => inClass v = b), H u v*(μ v : ℂ)*f v‖^2) ≤
      R^2*(∑ v ∈ T.filter (fun v => inClass v = b), μ v*‖f v‖^2) := by
    let O := T.filter (fun u => outClass u = b)
    let J := T.filter (fun v => inClass v = b)
    let U := O ∪ J
    have hOT : O ⊆ T := Finset.filter_subset _ _
    have hJT : J ⊆ T := Finset.filter_subset _ _
    have hUT : U ⊆ T := Finset.union_subset hOT hJT
    change (∑ u ∈ O, μ u*‖∑ v ∈ J, H u v*(μ v : ℂ)*f v‖^2) ≤
      R^2*(∑ v ∈ J, μ v*‖f v‖^2)
    by_cases hO : O = ∅
    · rw [hO, Finset.sum_empty]
      exact mul_nonneg (sq_nonneg R)
        (Finset.sum_nonneg (fun v hv => mul_nonneg (hμ v (hJT hv)) (sq_nonneg _)))
    · obtain ⟨z, hzO⟩ := Finset.nonempty_iff_ne_empty.mpr hO
      have hzb : outClass z = b := (Finset.mem_filter.mp hzO).2
      have hgeom (u : ι) (hu : u ∈ U) :
          line z = line u ∧ |((cell u-cell z : ℤ) : ℝ)| ≤ C := by
        rcases Finset.mem_union.mp hu with huO | huJ
        · have hub : outClass u = b := (Finset.mem_filter.mp huO).2
          have heq := hzb.trans hub.symm
          have hl : line z = line u := congrArg Prod.fst heq
          have hc : cell z = cell u := congrArg Prod.snd heq
          have hzero : cell u-cell z = 0 := sub_eq_zero.mpr hc.symm
          refine ⟨hl, ?_⟩
          simpa only [hzero, Int.cast_zero, abs_zero] using hC
        · have hub : inClass u = b := (Finset.mem_filter.mp huJ).2
          have heq := hzb.trans hub.symm
          have hl : line z = line u := congrArg Prod.fst heq
          have hc : cell z = cell u-m := congrArg Prod.snd heq
          have hshift : cell u-cell z = m := by omega
          refine ⟨hl, ?_⟩
          simpa only [hshift] using hm
      have hrect := finite_weighted_rectangular_kernel_bound U O J
        (Finset.subset_union_left) (Finset.subset_union_right) μ
        (fun u hu => hμ u (hUT hu)) base d e R
        (hcommon z (hOT hzO) U hUT hgeom) f
      have hpair (u : ι) (hu : u ∈ O) (v : ι) (hv : v ∈ J) :
          H u v = d u*base u v*e v := by
        have hub : outClass u = b := (Finset.mem_filter.mp hu).2
        have hvb : inClass v = b := (Finset.mem_filter.mp hv).2
        have heq := hub.trans hvb.symm
        have hl : line u = line v := congrArg Prod.fst heq
        have hc : cell u = cell v-m := congrArg Prod.snd heq
        have hshift : cell v-cell u = m := by omega
        simp only [H, k, if_pos (And.intro hl hshift)]
      have hrows (u : ι) (hu : u ∈ O) :
          (∑ v ∈ J, H u v*(μ v : ℂ)*f v) =
            d u*(∑ v ∈ J, base u v*(μ v : ℂ)*e v*f v) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        rw [hpair u hu v hv]
        ring
      have heq := Finset.sum_congr rfl (fun u hu =>
        congrArg (fun y : ℂ => μ u*‖y‖^2) (hrows u hu))
      rw [heq]
      exact hrect
  have hglobal := finite_weighted_block_kernel_bound T μ outClass inClass H R f hsupport hblocks
  have hout : (∑ u ∈ T, μ u*‖∑ v ∈ T, H u v*(μ v : ℂ)*f v‖^2) =
      ∑ u ∈ T, μ u*‖d u*(∑ v ∈ T, k u v*(μ v : ℂ)*e v*f v)‖^2 :=
    Finset.sum_congr rfl (fun u hu =>
      congrArg (fun y : ℂ => μ u*‖y‖^2) (hrow T u))
  rw [hout] at hglobal
  exact hglobal

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
