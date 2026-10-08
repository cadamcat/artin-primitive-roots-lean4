import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.RootWindows

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory

noncomputable section

def normalizedRootRegion : Set (ℝ × ℝ × ℝ) :=
  Set.Icc (1 : ℝ) 16 ×ˢ (Set.Icc (1 : ℝ) 2 ×ˢ Set.Icc (0 : ℝ) 1)

/-- A clipped cube is a product of three closed intervals. -/
theorem clippedCube_eq_box (h : ℝ) (k : ℤ × ℤ × ℤ) :
    normalizedRootRegion ∩ gridCube h k =
      Set.Icc (clippedCubeLo h k).1 (clippedCubeHi h k).1 ×ˢ
        (Set.Icc (clippedCubeLo h k).2.1 (clippedCubeHi h k).2.1 ×ˢ
          Set.Icc (clippedCubeLo h k).2.2 (clippedCubeHi h k).2.2) := by
  ext y
  simp only [normalizedRootRegion, gridCube, clippedCubeLo, clippedCubeHi, Set.mem_inter_iff,
    Set.mem_prod, Set.mem_Icc, max_le_iff, le_min_iff, Set.mem_setOf_eq]
  aesop

theorem clippedCube_measurable (h : ℝ) (k : ℤ × ℤ × ℤ) :
    MeasurableSet (normalizedRootRegion ∩ gridCube h k) := by
  rw [clippedCube_eq_box]
  exact measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

/-- Its volume is the product of the clipped side lengths. -/
theorem clippedCube_volume (h : ℝ) (k : ℤ × ℤ × ℤ)
    (hb : (clippedCubeLo h k).1 ≤ (clippedCubeHi h k).1 ∧
      (clippedCubeLo h k).2.1 ≤ (clippedCubeHi h k).2.1 ∧
      (clippedCubeLo h k).2.2 ≤ (clippedCubeHi h k).2.2) :
    volume.real (normalizedRootRegion ∩ gridCube h k) =
      ((clippedCubeHi h k).1 - (clippedCubeLo h k).1) *
        ((clippedCubeHi h k).2.1 - (clippedCubeLo h k).2.1) *
        ((clippedCubeHi h k).2.2 - (clippedCubeLo h k).2.2) := by
  rw [clippedCube_eq_box]
  change ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))).real
    (Set.Icc (clippedCubeLo h k).1 (clippedCubeHi h k).1 ×ˢ
      (Set.Icc (clippedCubeLo h k).2.1 (clippedCubeHi h k).2.1 ×ˢ
        Set.Icc (clippedCubeLo h k).2.2 (clippedCubeHi h k).2.2)) = _
  rw [measureReal_prod_prod, measureReal_prod_prod]
  simp only [Measure.real, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hb.1),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hb.2.1), ENNReal.toReal_ofReal (sub_nonneg.mpr hb.2.2)]
  ring

/-- A clipped cube has at most the volume of its original side-h cube. -/
theorem clippedCube_volume_le (h : ℝ) (hh : 0 ≤ h) (k : ℤ × ℤ × ℤ)
    (hb : (clippedCubeLo h k).1 ≤ (clippedCubeHi h k).1 ∧
      (clippedCubeLo h k).2.1 ≤ (clippedCubeHi h k).2.1 ∧
      (clippedCubeLo h k).2.2 ≤ (clippedCubeHi h k).2.2) :
    volume.real (normalizedRootRegion ∩ gridCube h k) ≤ h ^ 3 := by
  have hside (a b t : ℝ) : min b ((t + 1) * h) - max a (t * h) ≤ h := by
    have hl := le_max_right a (t * h)
    have hr := min_le_right b ((t + 1) * h)
    nlinarith
  have h₁ := hside 1 16 (k.1 : ℝ)
  have h₂ := hside 1 2 (k.2.1 : ℝ)
  have h₃ := hside 0 1 (k.2.2 : ℝ)
  rw [clippedCube_volume h k hb]
  have hlo₁ : 0 ≤ (clippedCubeHi h k).1 - (clippedCubeLo h k).1 := sub_nonneg.mpr hb.1
  have hlo₂ : 0 ≤ (clippedCubeHi h k).2.1 - (clippedCubeLo h k).2.1 := sub_nonneg.mpr hb.2.1
  have hlo₃ : 0 ≤ (clippedCubeHi h k).2.2 - (clippedCubeLo h k).2.2 := sub_nonneg.mpr hb.2.2
  change _ ≤ h ^ 3
  have hm := mul_le_mul (mul_le_mul h₁ h₂ hlo₂ hh) h₃ hlo₃ (mul_nonneg hh hh)
  simpa only [clippedCubeHi, clippedCubeLo, pow_succ, pow_two, pow_one, pow_zero, one_mul] using hm

theorem gridCube_measurable (h : ℝ) (k : ℤ × ℤ × ℤ) : MeasurableSet (gridCube h k) := by
  have hset : gridCube h k = Set.Icc ((k.1 : ℝ) * h) (((k.1 : ℝ) + 1) * h) ×ˢ
      (Set.Icc ((k.2.1 : ℝ) * h) (((k.2.1 : ℝ) + 1) * h) ×ˢ
        Set.Icc ((k.2.2 : ℝ) * h) (((k.2.2 : ℝ) + 1) * h)) := by
    ext y
    simp only [gridCube, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc]
    aesop
  rw [hset]
  exact measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

theorem normalizedRootRegion_compact : IsCompact normalizedRootRegion :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

theorem clippedCube_volume_le_all (h : ℝ) (hh : 0 ≤ h) (k : ℤ × ℤ × ℤ) :
    volume.real (normalizedRootRegion ∩ gridCube h k) ≤ h ^ 3 := by
  by_cases hne : (normalizedRootRegion ∩ gridCube h k).Nonempty
  · obtain ⟨y, hy⟩ := hne
    have hRegion : (1 ≤ y.1 ∧ y.1 ≤ 16) ∧ (1 ≤ y.2.1 ∧ y.2.1 ≤ 2) ∧
        (0 ≤ y.2.2 ∧ y.2.2 ≤ 1) := hy.1
    have hb := clippedCube_bounds h k y hRegion hy.2
    exact clippedCube_volume_le h hh k ⟨hb.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.2.2.1⟩
  · have heq := Set.not_nonempty_iff_eq_empty.mp hne
    rw [heq]
    simpa only [Measure.real, measure_empty, ENNReal.toReal_zero] using pow_nonneg hh 3

end
end ArtinPrimitiveRoots.TypeII.PD
