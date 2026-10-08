import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.CircleArcIntegral

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma pd7d_major_arc_indicator_sum (x Y A₀ theta : ℝ) (hL : 1 ≤ Real.log x)
    (hA₀ : 0 ≤ A₀) (hY : 4 * (Real.rpow (Real.log x) A₀) ^ 3 < Y) (f : ℝ → ℂ) :
    (if majorArc x Y A₀ theta then f theta else 0) =
      ∑ p ∈ pd7dReducedPairs (Real.rpow (Real.log x) A₀),
        if pd7dPairArc (Real.rpow (Real.log x) A₀) Y p theta then f theta else 0 := by
  let M := Real.rpow (Real.log x) A₀
  have hM : 1 ≤ M := Real.one_le_rpow hL hA₀
  have hiff := pd7d_majorArc_eq_reduced x Y A₀ theta (by linarith)
  by_cases hmajor : majorArc x Y A₀ theta
  · obtain ⟨p, hp, hpArc⟩ := hiff.mp hmajor
    rw [if_pos hmajor]
    symm
    calc
      _ = (if pd7dPairArc M Y p theta then f theta else 0) := by
        apply Finset.sum_eq_single_of_mem p hp
        intro q hq hqp
        have hnot : ¬pd7dPairArc M Y q theta := by
          intro hqArc
          have hdis := pd7d_pair_arcs_disjoint M Y hM hY p q hp hq (Ne.symm hqp)
          exact (Set.disjoint_left.mp hdis) hpArc hqArc
        exact if_neg hnot
      _ = _ := if_pos hpArc
  · rw [if_neg hmajor]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    have hnot : ¬pd7dPairArc M Y p theta := fun hpArc => hmajor (hiff.mpr ⟨p, hp, hpArc⟩)
    exact if_neg hnot

lemma pd7d_pair_arc_indicator_integrable (M Y : ℝ) (p : ℕ × ℕ)
    (f : ℝ → ℂ) (hf : Continuous f) :
    IntegrableOn (fun theta => if pd7dPairArc M Y p theta then f theta else 0) (Set.Icc (0 : ℝ) 1) := by
  have hset : MeasurableSet {theta : ℝ | pd7dPairArc M Y p theta} := by
    unfold pd7dPairArc
    simp only [Set.setOf_exists]
    measurability
  have hfun : (fun theta => if pd7dPairArc M Y p theta then f theta else 0) =
      ({theta : ℝ | pd7dPairArc M Y p theta}.indicator f) := by funext theta; rfl
  rw [hfun]
  exact hf.integrableOn_Icc.indicator hset

lemma pd7d_integer_phase_periodic (d : ℤ) :
    Function.Periodic (fun theta : ℝ => additiveCharacter (theta * (d : ℝ))) 1 := by
  intro theta
  simpa only [Int.cast_one] using pd7d_integer_phase_period theta 1 d

lemma pd7d_major_arc_interval_sum (x Y A₀ : ℝ) (hL : 1 ≤ Real.log x) (hA₀ : 0 ≤ A₀)
    (hY : 4 * (Real.rpow (Real.log x) A₀) ^ 3 < Y) (d : ℤ) :
    (∫ theta in (0 : ℝ)..1, if majorArc x Y A₀ theta then additiveCharacter (theta * (d : ℝ)) else 0) =
      ∑ p ∈ pd7dReducedPairs (Real.rpow (Real.log x) A₀),
        ∫ theta in ((p.1 : ℝ) / p.2 - 2 * Real.rpow (Real.log x) A₀ / Y)..
          ((p.1 : ℝ) / p.2 + 2 * Real.rpow (Real.log x) A₀ / Y),
          additiveCharacter (theta * (d : ℝ)) := by
  let M := Real.rpow (Real.log x) A₀
  let f := fun theta : ℝ => additiveCharacter (theta * (d : ℝ))
  have hM : 1 ≤ M := Real.one_le_rpow hL hA₀
  have hf : Continuous f := by dsimp [f]; unfold additiveCharacter; fun_prop
  have hRadius := pd7d_arc_radius_bounds M Y hM hY
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_Icc_eq_integral_Ioc]
  have hsumFun : (fun theta => if majorArc x Y A₀ theta then f theta else 0) =
      (fun theta => ∑ p ∈ pd7dReducedPairs M, if pd7dPairArc M Y p theta then f theta else 0) := by
    funext theta
    exact pd7d_major_arc_indicator_sum x Y A₀ theta hL hA₀ hY f
  rw [hsumFun, integral_finsetSum _ (fun p hp => pd7d_pair_arc_indicator_integrable M Y p f hf)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact pd7d_circle_arc_integral ((p.1 : ℝ) / p.2) (2 * M / Y) hRadius.2.1 hRadius.2.2.2
    f (pd7d_integer_phase_periodic d)

lemma pd7d_arc_affine_phase_integral (c M Y : ℝ) (d : ℤ) :
    (∫ theta in (c - 2 * M / Y)..(c + 2 * M / Y), additiveCharacter (theta * (d : ℝ))) =
      (1 / Y : ℂ) * ∫ lam in (-2 * M)..(2 * M),
        additiveCharacter (c * (d : ℝ)) * additiveCharacter (lam * (d : ℝ) / Y) := by
  let f := fun theta : ℝ => additiveCharacter (theta * (d : ℝ))
  have hvar := intervalIntegral.inv_smul_integral_comp_div_add (a := -2 * M) (b := 2 * M) f Y c
  have hlo : (-2 * M) / Y + c = c - 2 * M / Y := by ring
  have hhi : (2 * M) / Y + c = c + 2 * M / Y := by ring
  rw [hlo, hhi] at hvar
  have hfun : (fun lam : ℝ => f (lam / Y + c)) =
      fun lam => additiveCharacter (c * (d : ℝ)) * additiveCharacter (lam * (d : ℝ) / Y) := by
    funext lam
    dsimp [f]
    rw [show (lam / Y + c) * (d : ℝ) = c * d + lam * d / Y by ring,
      pd7d_additiveCharacter_add]
  rw [hfun] at hvar
  symm
  simpa [Algebra.smul_def, one_div] using hvar

lemma pd7d_major_kernel_arc_expansion (x Y A₀ : ℝ) (hL : 1 ≤ Real.log x) (hA₀ : 0 ≤ A₀)
    (hY : 4 * (Real.rpow (Real.log x) A₀) ^ 3 < Y) (d : ℤ) :
    (∫ theta in (0 : ℝ)..1, if majorArc x Y A₀ theta then additiveCharacter (theta * (d : ℝ)) else 0) =
      ∑ p ∈ pd7dReducedPairs (Real.rpow (Real.log x) A₀),
        (1 / Y : ℂ) * ∫ lam in (-2 * Real.rpow (Real.log x) A₀)..(2 * Real.rpow (Real.log x) A₀),
          additiveCharacter ((p.1 : ℝ) * (d : ℝ) / p.2) * additiveCharacter (lam * (d : ℝ) / Y) := by
  rw [pd7d_major_arc_interval_sum x Y A₀ hL hA₀ hY d]
  apply Finset.sum_congr rfl
  intro p hp
  have hh := pd7d_arc_affine_phase_integral ((p.1 : ℝ) / p.2) (Real.rpow (Real.log x) A₀) Y d
  simpa only [div_mul_eq_mul_div] using hh

end ArtinPrimitiveRoots.TypeII.PD
