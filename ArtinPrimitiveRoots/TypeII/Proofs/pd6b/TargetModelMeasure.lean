import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.SourceModelMeasure
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.CoverVolume
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.TargetCounting

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory

noncomputable section

theorem normalizedArchRoot_inRegion (S : PDScale) (hU : 0 < S.U) (hV : 0 < S.V)
    (y : ℝ × ℝ × ℝ) (hy : y ∈ normalizedRootRegion) : (normalizedArchRoot S y).InRegion S := by
  obtain ⟨h₁, h₂, h₃⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, h₃.1, h₃.2⟩
  · simpa only [normalizedArchRoot, mul_one] using mul_le_mul_of_nonneg_left h₁.1 hU.le
  · simpa only [normalizedArchRoot, mul_comm] using mul_le_mul_of_nonneg_left h₁.2 hU.le
  · simpa only [normalizedArchRoot, mul_one] using mul_le_mul_of_nonneg_left h₂.1 hV.le
  · simpa only [normalizedArchRoot, mul_comm] using mul_le_mul_of_nonneg_left h₂.2 hV.le

/-- A uniformly bounded target fiber may be integrated over the source bad-root set. -/
theorem targetModel_bad_volume_upper {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (p : PrimeLists S.x K) (Z : Finset (ℤ × ℤ))
    (condition : ℤ × ℤ → Prop) (M : ℝ) (hM : 0 ≤ M)
    (hcount : ∀ w : ArchRoot, w.InRegion S →
      ((Z.filter fun z => condition z ∧ envBox S w z).card : ℝ) ≤ M) :
    (∑ z ∈ Z, volume.real (normalizedRootRegion ∩
      {y : ℝ × ℝ × ℝ | ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p y.2.2 ∧
        condition z ∧ envBox S (normalizedArchRoot S y) z})) ≤
      M * (15 * (∫ r in (0 : ℝ)..1,
        if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p r then (0 : ℝ) else 1)) := by
  let R := normalizedRootRegion
  let μ := volume.restrict R
  letI : IsFiniteMeasure μ := ⟨by
    change volume.restrict R Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact normalizedRootRegion_compact.measure_lt_top⟩
  let B : Set (ℝ × ℝ × ℝ) := R ∩ {y | ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p y.2.2}
  let C (z : ℤ × ℤ) : Set (ℝ × ℝ × ℝ) := R ∩
    {y | ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p y.2.2 ∧ condition z ∧
      envBox S (normalizedArchRoot S y) z}
  have hRmeas : MeasurableSet R := normalizedRootRegion_compact.measurableSet
  have hBadMeas : MeasurableSet {y : ℝ × ℝ × ℝ | ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p y.2.2} :=
    ((measurableSet_isGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p).preimage (by fun_prop)).compl
  have hBmeas : MeasurableSet B := hRmeas.inter hBadMeas
  have hCmeas (z : ℤ × ℤ) : MeasurableSet (C z) := by
    by_cases hc : condition z
    · have heq : C z = B ∩ {y | envBox S (normalizedArchRoot S y) z} := by ext y; simp [C, B, hc]; aesop
      rw [heq]
      exact hBmeas.inter (measurableSet_normalized_envBox S z)
    · have heq : C z = ∅ := by ext y; simp [C, hc]
      rw [heq]
      exact MeasurableSet.empty
  have hsub (z : ℤ × ℤ) : C z ⊆ B := by intro y hy; exact ⟨hy.1, hy.2.1⟩
  have hoverlap (y : ℝ × ℝ × ℝ) : ((Z.filter fun z => y ∈ C z).card : ℝ) ≤ M := by
    by_cases hy : y ∈ R
    · have hs : (Z.filter fun z => y ∈ C z) ⊆ Z.filter fun z => condition z ∧ envBox S (normalizedArchRoot S y) z := by
        intro z hz
        have hm := (Finset.mem_filter.mp hz).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, hm.2.2⟩
      have hcard : ((Z.filter fun z => y ∈ C z).card : ℝ) ≤
          ((Z.filter fun z => condition z ∧ envBox S (normalizedArchRoot S y) z).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hs
      exact hcard.trans (hcount _ (normalizedArchRoot_inRegion S hU hV y hy))
    · have heq : (Z.filter fun z => y ∈ C z) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro z hz hmem
        exact hy hmem.1
      rw [heq, Finset.card_empty, Nat.cast_zero]
      exact hM
  have hvolume := selectedCell_volume_upper_real μ Z Z ∅ C (fun z hz => hCmeas z)
    (fun y => y ∈ B) hBmeas M (by intro z hz; exact hz) (by simp)
    (fun z hz hnot y hy => hsub z hy) (fun y => by
      refine le_trans ?_ (hoverlap y)
      apply le_of_eq
      congr 1
      apply congrArg Finset.card
      ext z
      simp only [Finset.mem_filter])
  have hreal (z : ℤ × ℤ) : μ.real (C z) = volume.real (C z) := by
    dsimp [μ, Measure.real]
    rw [Measure.restrict_apply (hCmeas z)]
    have heq : C z ∩ R = C z := Set.inter_eq_left.mpr (fun y hy => hy.1)
    rw [heq]
  have hrealB : μ.real B = volume.real B := by
    dsimp [μ, Measure.real]
    rw [Measure.restrict_apply hBmeas]
    have heq : B ∩ R = B := Set.inter_eq_left.mpr (fun y hy => hy.1)
    rw [heq]
  have hsum : (∑ z ∈ Z, μ.real (C z)) = ∑ z ∈ Z, volume.real (C z) :=
    Finset.sum_congr rfl (fun z hz => hreal z)
  have hpred : {y | y ∈ B} = B := rfl
  rw [hsum, hpred, hrealB] at hvolume
  try simp only [Finset.sum_empty, add_zero] at hvolume
  have hmodel := rootRegion_badRatio_volume S.x S.Y (S.d₀ : ℝ) K F.a p
  have hvolB : volume.real B = 15 * (∫ r in (0 : ℝ)..1,
      if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p r then (0 : ℝ) else 1) := hmodel
  rw [hvolB] at hvolume
  exact hvolume

theorem rawTargetModel_bad_volume_upper {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (p : PrimeLists S.x K) (Z : Finset (ℤ × ℤ)) (d : ℤ) :
    (∑ z ∈ Z, volume.real (normalizedRootRegion ∩
      {y : ℝ × ℝ × ℝ | ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p y.2.2 ∧
        z.2 = d ∧ envBox S (normalizedArchRoot S y) z})) ≤
      17 * (15 * (∫ r in (0 : ℝ)..1,
        if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p r then (0 : ℝ) else 1)) := by
  apply targetModel_bad_volume_upper F S hU hV p Z (fun z => z.2 = d) 17 (by norm_num)
  intro w hw
  norm_cast
  convert envBox_rawTargets_card_le S w hU hw Z d using 1
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter]

theorem comparisonTargetModel_bad_volume_upper {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (p : PrimeLists S.x K) (Z : Finset (ℤ × ℤ))
    (D : ℤ) (R : ℝ) (hY : 0 < S.Y) (hR : 0 ≤ R) :
    (∑ z ∈ Z, volume.real (normalizedRootRegion ∩
      {y : ℝ × ℝ × ℝ | ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p y.2.2 ∧
        (∃ t : ℤ, |(t : ℝ)| ≤ R * S.Y ∧ z.2 = D * t) ∧ envBox S (normalizedArchRoot S y) z})) ≤
      (17 * (2 * R * S.Y + 1)) * (15 * (∫ r in (0 : ℝ)..1,
        if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p r then (0 : ℝ) else 1)) := by
  apply targetModel_bad_volume_upper F S hU hV p Z
    (fun z => ∃ t : ℤ, |(t : ℝ)| ≤ R * S.Y ∧ z.2 = D * t) (17 * (2 * R * S.Y + 1)) (by positivity)
  intro w hw
  exact envBox_comparisonTargets_card_le S w hU hw Z D S.Y R hY hR


end
end ArtinPrimitiveRoots.TypeII.PD
