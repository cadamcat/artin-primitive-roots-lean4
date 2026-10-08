import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.EdgePredicates

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory

noncomputable section

/-- Product measure turns the source bad-ratio integral into bad-root volume. -/
theorem rootRegion_badRatio_volume (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) :
    volume.real (normalizedRootRegion ∩
      {y : ℝ × ℝ × ℝ | ¬ IsGoodRatio x Y d₀ K a p y.2.2}) =
      15 * (∫ r in (0 : ℝ)..1, if IsGoodRatio x Y d₀ K a p r then (0 : ℝ) else 1) := by
  let B : Set ℝ := {r | ¬ IsGoodRatio x Y d₀ K a p r}
  have hB : MeasurableSet B := (measurableSet_isGoodRatio x Y d₀ K a p).compl
  have hset : normalizedRootRegion ∩
      {y : ℝ × ℝ × ℝ | ¬ IsGoodRatio x Y d₀ K a p y.2.2} =
      Set.Icc (1 : ℝ) 16 ×ˢ (Set.Icc (1 : ℝ) 2 ×ˢ (Set.Icc (0 : ℝ) 1 ∩ B)) := by
    ext y
    simp only [normalizedRootRegion, Set.mem_inter_iff, Set.mem_prod, Set.mem_setOf_eq, B]
    aesop
  have hratio : (∫ r in (0 : ℝ)..1, if IsGoodRatio x Y d₀ K a p r then (0 : ℝ) else 1) =
      volume.real (Set.Icc (0 : ℝ) 1 ∩ B) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_Icc_eq_integral_Ioc]
    have hfun : (fun r : ℝ => if IsGoodRatio x Y d₀ K a p r then (0 : ℝ) else 1) =
        B.indicator (fun _ => (1 : ℝ)) := by
      funext r
      by_cases h : IsGoodRatio x Y d₀ K a p r <;> simp [B, h]
    rw [hfun, integral_indicator hB, Measure.restrict_restrict hB]
    simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ, Set.inter_comm]
  rw [hset]
  change ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))).real
    (Set.Icc (1 : ℝ) 16 ×ˢ (Set.Icc (1 : ℝ) 2 ×ˢ (Set.Icc (0 : ℝ) 1 ∩ B))) = _
  rw [measureReal_prod_prod, measureReal_prod_prod, hratio]
  have hv₁ : (volume : Measure ℝ).real (Set.Icc (1 : ℝ) 16) = 15 := by
    norm_num [Measure.real, Real.volume_Icc]
  have hv₂ : (volume : Measure ℝ).real (Set.Icc (1 : ℝ) 2) = 1 := by
    norm_num [Measure.real, Real.volume_Icc]
  rw [hv₁, hv₂]
  ring

end
end ArtinPrimitiveRoots.TypeII.PD
