import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ArcIntervals

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
set_option autoImplicit false

def pd7dCircleArc (c r theta : ℝ) : Prop := ∃ z : ℤ, |theta - c - (z : ℝ)| ≤ r

lemma pd7dCircleArc_add_one (c r theta : ℝ) :
    pd7dCircleArc c r (theta + 1) ↔ pd7dCircleArc c r theta := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z - 1, ?_⟩
    have harg : theta - c - ((z - 1 : ℤ) : ℝ) = theta + 1 - c - (z : ℝ) := by push_cast; ring
    rw [harg]
    exact hz
  · rintro ⟨z, hz⟩
    refine ⟨z + 1, ?_⟩
    have harg : theta + 1 - c - ((z + 1 : ℤ) : ℝ) = theta - c - (z : ℝ) := by push_cast; ring
    rw [harg]
    exact hz

lemma pd7d_circle_arc_on_centered_interval (c r theta : ℝ) (hr : r < 1 / 2)
    (htheta : theta ∈ Set.Icc (c - 1 / 2) (c + 1 / 2)) :
    pd7dCircleArc c r theta ↔ theta ∈ Set.Icc (c - r) (c + r) := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hlo, hhi⟩ := abs_le.mp hz
    have hzlo : (-1 : ℝ) < (z : ℝ) := by linarith [htheta.1]
    have hzhi : (z : ℝ) < 1 := by linarith [htheta.2]
    have hzloI : (-1 : ℤ) < z := by exact_mod_cast hzlo
    have hzhiI : z < (1 : ℤ) := by exact_mod_cast hzhi
    have hz0 : z = 0 := by omega
    rw [hz0, Int.cast_zero] at hlo hhi
    constructor <;> linarith
  · intro ht
    refine ⟨0, ?_⟩
    rw [Int.cast_zero, sub_zero]
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2]

lemma pd7d_circle_arc_integral (c r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1 / 2)
    (f : ℝ → ℂ) (hf : Function.Periodic f 1) :
    (∫ theta in (0 : ℝ)..1, if pd7dCircleArc c r theta then f theta else 0) =
      ∫ theta in (c - r)..(c + r), f theta := by
  let g := fun theta : ℝ => if pd7dCircleArc c r theta then f theta else 0
  have hg : Function.Periodic g 1 := by
    intro theta
    have hp := pd7dCircleArc_add_one c r theta
    by_cases htheta : pd7dCircleArc c r theta
    · have htheta' := hp.mpr htheta
      simp only [g, ite_eq_left_iff, if_pos htheta, if_pos htheta', hf theta]
    · have htheta' : ¬pd7dCircleArc c r (theta + 1) := fun h => htheta (hp.mp h)
      simp only [g, if_neg htheta, if_neg htheta']
  have hwindow : (∫ theta in (0 : ℝ)..1, g theta) =
      ∫ theta in (c - 1 / 2)..(c + 1 / 2), g theta := by
    have hh := hg.intervalIntegral_add_eq 0 (c - 1 / 2)
    simpa only [zero_add, show c - 1 / 2 + 1 = c + 1 / 2 by ring] using hh
  have hsub : Set.Icc (c - r) (c + r) ⊆ Set.Icc (c - 1 / 2) (c + 1 / 2) := by
    intro theta ht
    constructor <;> linarith [ht.1, ht.2]
  change (∫ theta in (0 : ℝ)..1, g theta) = _
  rw [hwindow]
  calc
    _ = ∫ theta in (c - 1 / 2)..(c + 1 / 2),
        (Set.Icc (c - r) (c + r)).indicator f theta := by
      apply intervalIntegral.integral_congr
      intro theta htheta
      rw [Set.uIcc_of_le (by linarith : c - 1 / 2 ≤ c + 1 / 2)] at htheta
      have hp := pd7d_circle_arc_on_centered_interval c r theta hr htheta
      simp only [g, Set.indicator, hp]
      split_ifs <;> rfl
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by linarith : c - 1 / 2 ≤ c + 1 / 2),
        ← integral_Icc_eq_integral_Ioc, setIntegral_indicator measurableSet_Icc,
        Set.inter_eq_right.mpr hsub, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : c - r ≤ c + r)]

end ArtinPrimitiveRoots.TypeII.PD
