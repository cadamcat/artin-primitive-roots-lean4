import ArtinPrimitiveRoots.TypeII.PD.Defs
import Mathlib.Algebra.Order.Round

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory

lemma pd1c_int_eq_natAbs_or_neg (n : ℤ) :
    n = (n.natAbs : ℤ) ∨ n = -(n.natAbs : ℤ) := by
  obtain h | h := Int.natAbs_eq n
  · exact Or.inl h
  · exact Or.inr h

lemma pd1c_circleDistance_nonneg (t : ℝ) : 0 ≤ circleDistance t := by
  unfold circleDistance
  apply le_csInf
  · exact ⟨|t - (0 : ℝ)|, ⟨0, by simp⟩⟩
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    exact abs_nonneg _

lemma pd1c_circleDistance_le_abs_sub_int (t : ℝ) (z : ℤ) :
    circleDistance t ≤ |t - (z : ℝ)| := by
  unfold circleDistance
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨w, rfl⟩
    exact abs_nonneg _
  · exact ⟨z, rfl⟩

lemma pd1c_circleDistance_le_half (t : ℝ) : circleDistance t ≤ 1 / 2 := by
  calc
    circleDistance t ≤ |t - (round t : ℝ)| :=
      pd1c_circleDistance_le_abs_sub_int t (round t)
    _ ≤ 1 / 2 := abs_sub_round t

lemma pd1c_circleDistance_attained (t : ℝ) :
    ∃ z : ℤ, circleDistance t = |t - (z : ℝ)| := by
  let j : ℤ := round t
  have hmin : ∀ z : ℤ, |t - (j : ℝ)| ≤ |t - (z : ℝ)| := by
    intro z
    simpa [j] using round_le t z
  have hbdd : BddBelow (Set.range fun z : ℤ => |t - (z : ℝ)|) :=
    ⟨0, fun y hy => by rcases hy with ⟨z, rfl⟩; exact abs_nonneg _⟩
  refine ⟨j, ?_⟩
  unfold circleDistance
  apply le_antisymm
  · exact csInf_le hbdd ⟨j, rfl⟩
  · apply le_csInf
    · exact ⟨|t - (j : ℝ)|, ⟨j, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨z, rfl⟩
      exact hmin z

lemma pd1c_circleDistance_le_iff_exists_int (t e : ℝ) :
    circleDistance t ≤ e ↔ ∃ z : ℤ, |t - (z : ℝ)| ≤ e := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := pd1c_circleDistance_attained t
    exact ⟨z, hz ▸ h⟩
  · rintro ⟨z, hz⟩
    exact (pd1c_circleDistance_le_abs_sub_int t z).trans hz

lemma pd1c_circleDistance_neg (t : ℝ) : circleDistance (-t) = circleDistance t := by
  unfold circleDistance
  congr 1
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨-z, ?_⟩
    simp only [Int.cast_neg, sub_neg_eq_add]
    calc
      |t + (z : ℝ)| = |-(t + (z : ℝ))| := by rw [abs_neg]
      _ = |-t - (z : ℝ)| := by congr 1 <;> ring
  · rintro ⟨z, rfl⟩
    refine ⟨-z, ?_⟩
    simp only [Int.cast_neg, sub_neg_eq_add]
    calc
      |-t + (z : ℝ)| = |(z : ℝ) - t| := by congr 1 <;> ring
      _ = |t - (z : ℝ)| := abs_sub_comm _ _

lemma pd1c_circleDistance_natAbs_mul (n : ℤ) (r : ℝ) :
    circleDistance ((n : ℝ) * r) =
      circleDistance ((n.natAbs : ℝ) * r) := by
  rcases pd1c_int_eq_natAbs_or_neg n with h | h
  · have hc : (n : ℝ) = (n.natAbs : ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) h
    rw [hc]
  · have hc : (n : ℝ) = -(n.natAbs : ℝ) := by
      simpa only [Int.cast_natCast, Int.cast_neg] using
        congrArg (fun z : ℤ => (z : ℝ)) h
    rw [hc, neg_mul, pd1c_circleDistance_neg]

lemma pd1c_circleDistance_int_add (t : ℝ) (j : ℤ) :
    circleDistance (t + (j : ℝ)) = circleDistance t := by
  unfold circleDistance
  congr 1
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z - j, ?_⟩
    congr 1 <;> push_cast <;> ring
  · rintro ⟨z, rfl⟩
    refine ⟨z + j, ?_⟩
    congr 1 <;> push_cast <;> ring

lemma pd1c_circleDistance_lipschitz : LipschitzWith 1 circleDistance := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [dist_eq_norm, Real.norm_eq_abs, one_mul]
  rcases pd1c_circleDistance_attained t with ⟨w, hw⟩
  have hs : circleDistance s ≤ |s - t| + circleDistance t := by
    calc
      circleDistance s ≤ |s - (w : ℝ)| := pd1c_circleDistance_le_abs_sub_int s w
      _ ≤ |s - t| + |t - (w : ℝ)| := by
        rw [show s - (w : ℝ) = (s - t) + (t - (w : ℝ)) by ring]
        exact abs_add_le _ _
      _ = |s - t| + circleDistance t := by rw [← hw]
  rcases pd1c_circleDistance_attained s with ⟨z, hz⟩
  have ht : circleDistance t ≤ |s - t| + circleDistance s := by
    calc
      circleDistance t ≤ |t - (z : ℝ)| := pd1c_circleDistance_le_abs_sub_int t z
      _ ≤ |t - s| + |s - (z : ℝ)| := by
        rw [show t - (z : ℝ) = (t - s) + (s - (z : ℝ)) by ring]
        exact abs_add_le _ _
      _ = |s - t| + circleDistance s := by rw [abs_sub_comm t s, ← hz]
  have hfinal :
      |circleDistance s - circleDistance t| ≤ |s - t| := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  simpa using hfinal

lemma pd1c_circleDistance_continuous : Continuous circleDistance :=
  pd1c_circleDistance_lipschitz.continuous

lemma pd1c_circleDistance_sublevel_measurable (n : ℤ) (e : ℝ) :
    MeasurableSet {r : ℝ | circleDistance ((n : ℝ) * r) ≤ e} := by
  exact isClosed_Iic.measurableSet.preimage
    (pd1c_circleDistance_continuous.comp
      (continuous_const.mul continuous_id)).measurable

lemma pd1c_circleDistance_realSublevel_measurable (c e : ℝ) :
    MeasurableSet {r : ℝ | circleDistance (c * r) ≤ e} := by
  exact isClosed_Iic.measurableSet.preimage
    (pd1c_circleDistance_continuous.comp
      (continuous_const.mul continuous_id)).measurable

lemma pd1c_circle_interval_cover_bound (N : ℕ) (hN : 0 < N) (e : ℝ) (he : 0 ≤ e) :
    volume (⋃ k ∈ Finset.range (N + 1),
      Set.Icc (((k : ℝ) - e) / (N : ℝ)) (((k : ℝ) + e) / (N : ℝ))) ≤
        ENNReal.ofReal (4 * e) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let I (k : ℕ) : Set ℝ :=
    Set.Icc (((k : ℝ) - e) / (N : ℝ)) (((k : ℝ) + e) / (N : ℝ))
  have hpiece (k : ℕ) : volume (I k) = ENNReal.ofReal (2 * e / (N : ℝ)) := by
    dsimp [I]
    rw [Real.volume_Icc]
    congr 1
    field_simp
    ring
  have hsum :
      (∑ k ∈ Finset.range (N + 1), volume (I k)) =
        ENNReal.ofReal (((N + 1 : ℕ) : ℝ) • (2 * e / (N : ℝ))) := by
    simp_rw [hpiece]
    rw [Finset.sum_const, Finset.card_range, ← ENNReal.ofReal_nsmul]
    congr 1
    exact (Nat.cast_smul_eq_nsmul ℝ _ _).symm
  have hscalar : ((N + 1 : ℕ) : ℝ) • (2 * e / (N : ℝ)) ≤ 4 * e := by
    rw [smul_eq_mul]
    have hratio : ((N + 1 : ℕ) : ℝ) / (N : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hNreal]
      have hNreal1 : 1 ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
      norm_num
      linarith
    have hnonneg : 0 ≤ 2 * e := by positivity
    calc
      ((N + 1 : ℕ) : ℝ) * (2 * e / (N : ℝ)) =
          (((N + 1 : ℕ) : ℝ) / (N : ℝ)) * (2 * e) := by ring
      _ ≤ 2 * (2 * e) := mul_le_mul_of_nonneg_right hratio hnonneg
      _ = 4 * e := by ring
  calc
    volume (⋃ k ∈ Finset.range (N + 1), I k) ≤
        ∑ k ∈ Finset.range (N + 1), volume (I k) :=
          MeasureTheory.measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal (((N + 1 : ℕ) : ℝ) • (2 * e / (N : ℝ))) := hsum
    _ ≤ ENNReal.ofReal (4 * e) := ENNReal.ofReal_le_ofReal hscalar

lemma pd1c_circle_small_set_measure (n : ℤ) (hn : n ≠ 0) (e : ℝ) (he : 0 ≤ e) :
    volume {r : ℝ | r ∈ Set.Icc 0 1 ∧ circleDistance ((n : ℝ) * r) ≤ e} ≤
      ENNReal.ofReal (4 * e) := by
  by_cases hehalf : e ≤ 1 / 2
  · let N := n.natAbs
    have hN : 0 < N := Int.natAbs_pos.mpr hn
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    let I (k : ℕ) : Set ℝ :=
      Set.Icc (((k : ℝ) - e) / (N : ℝ)) (((k : ℝ) + e) / (N : ℝ))
    have hsub :
        {r : ℝ | r ∈ Set.Icc 0 1 ∧ circleDistance ((n : ℝ) * r) ≤ e} ⊆
          ⋃ k ∈ Finset.range (N + 1), I k := by
      intro r hr
      rcases hr with ⟨hrange, hgood⟩
      have hred : circleDistance ((N : ℝ) * r) ≤ e := by
        rw [pd1c_circleDistance_natAbs_mul n r] at hgood
        simpa [N] using hgood
      obtain ⟨z, hnear⟩ :=
        (pd1c_circleDistance_le_iff_exists_int ((N : ℝ) * r) e).mp hred
      have htrange0 : 0 ≤ (N : ℝ) * r :=
        mul_nonneg (Nat.cast_nonneg _) hrange.1
      have htrangeN : (N : ℝ) * r ≤ (N : ℝ) := by
        calc
          (N : ℝ) * r ≤ (N : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hrange.2 (Nat.cast_nonneg _)
          _ = (N : ℝ) := by ring
      have hnearBounds := (abs_le.mp hnear)
      have hzlo : 0 ≤ z := by
        by_contra hz
        have hzle : z ≤ -1 := by omega
        have hzleR : (z : ℝ) ≤ -1 := by exact_mod_cast hzle
        have hlarge : 1 ≤ (N : ℝ) * r - (z : ℝ) := by nlinarith [htrange0, hzleR]
        nlinarith [hnearBounds.2]
      have hzhi : z ≤ (N : ℤ) := by
        by_contra hz
        have hzge : (N : ℤ) + 1 ≤ z := by omega
        have hzgeR : (N : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hzge
        have hsmall : (N : ℝ) * r - (z : ℝ) ≤ -1 := by nlinarith [htrangeN, hzgeR]
        nlinarith [hnearBounds.1]
      let k := z.toNat
      have hkz : (k : ℤ) = z := Int.toNat_of_nonneg hzlo
      have hkN : k ≤ N := by omega
      have hkmem : k ∈ Finset.range (N + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hkN)
      have hkcast : (k : ℝ) = (z : ℝ) := by exact_mod_cast hkz
      have hlo : ((k : ℝ) - e) / (N : ℝ) ≤ r := by
        rw [div_le_iff₀ hNreal]
        nlinarith [hnearBounds.1, hkcast]
      have hhi : r ≤ ((k : ℝ) + e) / (N : ℝ) := by
        rw [le_div_iff₀ hNreal]
        nlinarith [hnearBounds.2, hkcast]
      refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hkmem, ?_⟩⟩
      exact ⟨hlo, hhi⟩
    calc
      volume {r : ℝ | r ∈ Set.Icc 0 1 ∧ circleDistance ((n : ℝ) * r) ≤ e} ≤
          volume (⋃ k ∈ Finset.range (N + 1), I k) := measure_mono hsub
      _ ≤ ENNReal.ofReal (4 * e) := by
        simpa [I] using pd1c_circle_interval_cover_bound N hN e he
  · have hsubset :
        {r : ℝ | r ∈ Set.Icc 0 1 ∧ circleDistance ((n : ℝ) * r) ≤ e} ⊆
          Set.Icc 0 1 := fun _ hr => hr.1
    calc
      volume {r : ℝ | r ∈ Set.Icc 0 1 ∧ circleDistance ((n : ℝ) * r) ≤ e} ≤
          volume (Set.Icc 0 1) := measure_mono hsubset
      _ = ENNReal.ofReal 1 := by simp [Real.volume_Icc]
      _ ≤ ENNReal.ofReal (4 * e) := ENNReal.ofReal_le_ofReal (by
        have hbig : 1 / 2 < e := lt_of_not_ge hehalf
        linarith)

lemma pd1c_interval_indicator_le_volume (A : Set ℝ)
    (hA : A ⊆ Set.Icc 0 1) (hAm : MeasurableSet A) :
    (∫ r in (0 : ℝ)..1, if r ∈ A then (1 : ℝ) else 0) ≤ (volume A).toReal := by
  have hAfinite : volume A ≠ ⊤ := by
    apply ne_of_lt
    calc
      volume A ≤ volume (Set.Icc 0 1) := measure_mono hA
      _ = ENNReal.ofReal 1 := by simp [Real.volume_Icc]
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hAm' : MeasurableSet (A ∩ Set.Ioc 0 1) := hAm.inter measurableSet_Ioc
  have hIndicator : (fun r : ℝ => if r ∈ A then (1 : ℝ) else 0) =
      A.indicator (fun _ => (1 : ℝ)) := by
    funext r
    by_cases hr : r ∈ A <;> simp [Set.indicator, hr]
  have hIndicatorInter : (Set.Ioc 0 1).indicator
      (A.indicator (fun _ => (1 : ℝ))) =
        (A ∩ Set.Ioc 0 1).indicator (fun _ => (1 : ℝ)) := by
    funext r
    by_cases hA' : r ∈ A <;> by_cases hI : r ∈ Set.Ioc 0 1 <;>
      simp [Set.indicator, hA', hI]
  calc
    (∫ r in (0 : ℝ)..1, if r ∈ A then (1 : ℝ) else 0) =
        volume.real (A ∩ Set.Ioc 0 1) := by
          rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hIndicator,
            ← MeasureTheory.integral_indicator measurableSet_Ioc, hIndicatorInter,
            MeasureTheory.integral_indicator_const (1 : ℝ) hAm']
          simp
    _ ≤ volume.real A := measureReal_mono (Set.inter_subset_left) hAfinite

lemma pd1c_interval_indicator_weight_le_volume (A : Set ℝ)
    (hA : A ⊆ Set.Icc 0 1) (hAm : MeasurableSet A) (w : ℝ) (hw : 0 ≤ w) :
    (∫ r in (0 : ℝ)..1, if r ∈ A then w else 0) ≤ volume.real A * w := by
  have hAfinite : volume A ≠ ⊤ := by
    apply ne_of_lt
    calc
      volume A ≤ volume (Set.Icc 0 1) := measure_mono hA
      _ = ENNReal.ofReal 1 := by simp [Real.volume_Icc]
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hAm' : MeasurableSet (A ∩ Set.Ioc 0 1) := hAm.inter measurableSet_Ioc
  have hfun : (fun r : ℝ => if r ∈ A then w else 0) = A.indicator (fun _ => w) := by
    funext r
    by_cases hr : r ∈ A <;> simp [Set.indicator, hr]
  have hIndicatorInter : (Set.Ioc 0 1).indicator
      (A.indicator (fun _ => w)) =
        (A ∩ Set.Ioc 0 1).indicator (fun _ => w) := by
    funext r
    by_cases hA' : r ∈ A <;> by_cases hI : r ∈ Set.Ioc 0 1 <;>
      simp [Set.indicator, hA', hI]
  have hIntegral :
      (∫ r in (0 : ℝ)..1, if r ∈ A then w else 0) =
        volume.real (A ∩ Set.Ioc 0 1) * w := by
    rw [hfun, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← MeasureTheory.integral_indicator measurableSet_Ioc, hIndicatorInter,
      MeasureTheory.integral_indicator_const w hAm', smul_eq_mul]
  calc
    (∫ r in (0 : ℝ)..1, if r ∈ A then w else 0) =
        volume.real (A ∩ Set.Ioc 0 1) * w := hIntegral
    _ ≤ volume.real A * w :=
      mul_le_mul_of_nonneg_right
        (measureReal_mono Set.inter_subset_left hAfinite) hw

lemma pd1c_interval_markov_bad_integral (f : ℝ → ℝ)
    (hf : Measurable f) (hInt : IntervalIntegrable f volume 0 1)
    (hf_nonneg : ∀ r, 0 ≤ f r) (θ : ℝ) (hθ : 0 < θ) :
    (∫ r in (0 : ℝ)..1, if θ < f r then (1 : ℝ) else 0) ≤
      (∫ r in (0 : ℝ)..1, f r) / θ := by
  let μ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let C : Set ℝ := {r | r ∈ Set.Ioc 0 1 ∧ θ < f r}
  let S : Set ℝ := {r | θ ≤ f r}
  have hCmeas : MeasurableSet C := by
    exact measurableSet_Ioc.inter (measurableSet_lt measurable_const hf)
  have hCsub : C ⊆ Set.Icc 0 1 := by
    intro r hr
    exact ⟨le_of_lt hr.1.1, hr.1.2⟩
  have hCtoS : C ⊆ S := by
    intro r hr
    exact le_of_lt hr.2
  have hSmeas : MeasurableSet S := measurableSet_le measurable_const hf
  have hIntOn : Integrable f μ := by
    change IntegrableOn f (Set.Ioc 0 1) volume
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).1 hInt
  have hnonneg : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hf_nonneg
  have hMarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hIntOn θ
  have hMarkov' : θ * μ.real S ≤ ∫ r in (0 : ℝ)..1, f r := by
    simpa [μ, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hMarkov
  have hCrestrict : μ.real C = volume.real C := by
    rw [measureReal_restrict_apply hCmeas]
    congr 1
    exact Set.inter_eq_left.mpr fun r hr => hr.1
  have hCmeasure : volume.real C ≤ (∫ r in (0 : ℝ)..1, f r) / θ := by
    calc
      volume.real C = μ.real C := hCrestrict.symm
      _ ≤ μ.real S := measureReal_mono hCtoS (by finiteness)
      _ ≤ (∫ r in (0 : ℝ)..1, f r) / θ :=
        (le_div_iff₀ hθ).2 (by simpa [mul_comm] using hMarkov')
  have hcongr :
      (∫ r in (0 : ℝ)..1, if θ < f r then (1 : ℝ) else 0) =
        ∫ r in (0 : ℝ)..1, C.indicator (fun _ => (1 : ℝ)) r := by
    apply intervalIntegral.integral_congr_ae'
    · exact Filter.Eventually.of_forall fun r hr => by
        have hrC : r ∈ Set.Ioc (0 : ℝ) 1 := hr
        by_cases hbad : θ < f r
        · have hmem : r ∈ C := ⟨hrC, hbad⟩
          rw [if_pos hbad, Set.indicator_of_mem hmem]
        · have hnot : r ∉ C := by
            rintro ⟨_, hcontra⟩
            exact hbad hcontra
          rw [if_neg hbad, Set.indicator_of_notMem hnot]
    · exact Filter.Eventually.of_forall fun r hr => by
        have hr' : r ∈ Set.Ioc (1 : ℝ) 0 := hr
        simp only [Set.mem_Ioc] at hr'
        linarith
  calc
    (∫ r in (0 : ℝ)..1, if θ < f r then (1 : ℝ) else 0) =
        ∫ r in (0 : ℝ)..1, C.indicator (fun _ => (1 : ℝ)) r := hcongr
    _ ≤ volume.real C := pd1c_interval_indicator_le_volume C hCsub hCmeas
    _ ≤ (∫ r in (0 : ℝ)..1, f r) / θ := hCmeasure

end ArtinPrimitiveRoots.TypeII.PD
