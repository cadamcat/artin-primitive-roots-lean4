import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.FrequencyWeights

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory Function
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def pd7dPSeries (j : ℕ) : ℝ := ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ j)

lemma pd7dPSeries_nonneg (j : ℕ) : 0 ≤ pd7dPSeries j := tsum_nonneg (fun n => by positivity)

lemma pd7d_positive_weighted_tail (H S C : ℝ) (hH : 0 < H) (hS : 0 < S) (hC : 0 ≤ C)
    (j : ℕ) (hj : 2 ≤ j) (f : ℝ → ℝ) (hf : Continuous f) (hfn : ∀ t, 0 ≤ f t)
    (hweighted : IntegrableOn (fun t => pd7dFrequencyWeight H j t * f t) (Set.Ioi S))
    (hmean : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, f t) ≤ C * (1 + (b - a))) :
    (∫ t in Set.Ioi S, pd7dFrequencyWeight H j t * f t) ≤
      C * (1 + S) * (H / S) ^ j * pd7dPSeries j := by
  let g := fun t : ℝ => pd7dFrequencyWeight H j t * f t
  let coeff := fun n : ℕ => (H / S) ^ j / (((n + 1 : ℕ) : ℝ) ^ j)
  have hc (n : ℕ) : 0 ≤ coeff n := by dsimp [coeff]; positivity
  have hwindow (n : ℕ) :
      (∫ t in pd7dFrequencyWindow S n, g t) ≤ coeff n * (C * (1 + S)) := by
    let a := ((n + 1 : ℕ) : ℝ) * S
    let b := ((n + 2 : ℕ) : ℝ) * S
    have hlength : b - a = S := by dsimp [a, b]; push_cast; ring
    have hab : a ≤ b := by linarith
    have hsub : pd7dFrequencyWindow S n ⊆ Set.Ioi S := by
      rw [← pd7d_frequency_windows_union S hS]
      exact Set.subset_iUnion (pd7dFrequencyWindow S) n
    have hgi : IntegrableOn g (pd7dFrequencyWindow S n) := hweighted.mono_set hsub
    have hfi : IntegrableOn f (pd7dFrequencyWindow S n) :=
      hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have hpoint : ∀ t ∈ pd7dFrequencyWindow S n, g t ≤ coeff n * f t := by
      intro t ht
      exact mul_le_mul_of_nonneg_right (pd7d_frequency_weight_on_window H S hH hS j n t ht) (hfn t)
    have hmono := integral_mono_ae hgi (hfi.const_mul (coeff n))
      (ae_restrict_of_forall_mem (by exact measurableSet_Ioc) hpoint)
    rw [integral_const_mul] at hmono
    have hmeanWin : (∫ t in pd7dFrequencyWindow S n, f t) ≤ C * (1 + S) := by
      change (∫ t in Set.Ioc a b, f t) ≤ _
      rw [← intervalIntegral.integral_of_le hab]
      simpa only [hlength] using hmean a b hab
    exact hmono.trans (mul_le_mul_of_nonneg_left hmeanWin (hc n))
  have hgsum : Summable (fun n : ℕ => ∫ t in pd7dFrequencyWindow S n, g t) := by
    have hgu : IntegrableOn g (⋃ n : ℕ, pd7dFrequencyWindow S n) := by
      rw [pd7d_frequency_windows_union S hS]
      exact hweighted
    exact (hasSum_integral_iUnion (fun _ => measurableSet_Ioc)
      (pd7d_frequency_windows_disjoint S hS) hgu).summable
  have hpsum := pd7d_shifted_pseries_summable j hj
  let K := C * (1 + S) * (H / S) ^ j
  have hmajfun : (fun n : ℕ => coeff n * (C * (1 + S))) =
      (fun n : ℕ => K * (1 / (((n + 1 : ℕ) : ℝ) ^ j))) := by
    funext n
    dsimp [coeff, K]
    ring
  have hmajsum : Summable (fun n : ℕ => coeff n * (C * (1 + S))) := by
    rw [hmajfun]
    exact hpsum.mul_left K
  calc
    _ = ∑' n : ℕ, ∫ t in pd7dFrequencyWindow S n, g t :=
      pd7d_integral_frequency_windows S hS g hweighted
    _ ≤ ∑' n : ℕ, coeff n * (C * (1 + S)) := hgsum.tsum_le_tsum hwindow hmajsum
    _ = _ := by rw [hmajfun, tsum_mul_left]; rfl

lemma pd7d_positive_weighted_full (H C : ℝ) (hH : 0 < H) (hC : 0 ≤ C)
    (j : ℕ) (hj : 2 ≤ j) (f : ℝ → ℝ) (hf : Continuous f) (hfn : ∀ t, 0 ≤ f t)
    (hweighted : Integrable (fun t => pd7dFrequencyWeight H j t * f t))
    (hmean : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, f t) ≤ C * (1 + (b - a))) :
    (∫ t in Set.Ioi (0 : ℝ), pd7dFrequencyWeight H j t * f t) ≤
      C * (1 + H) * (1 + pd7dPSeries j) := by
  let g := fun t => pd7dFrequencyWeight H j t * f t
  have hsplit := intervalIntegral.integral_interval_add_Ioi (a := (0 : ℝ)) (b := H)
    hweighted.integrableOn hweighted.integrableOn
  have hcentral : (∫ t in (0 : ℝ)..H, g t) ≤ C * (1 + H) := by
    have hgc : Continuous g := (pd7dFrequencyWeight_continuous H hH j).mul hf
    calc
      _ ≤ ∫ t in (0 : ℝ)..H, f t := intervalIntegral.integral_mono_on hH.le
        (hgc.intervalIntegrable _ _) (hf.intervalIntegrable _ _) (fun t _ => by
          have hh := mul_le_mul_of_nonneg_right (pd7dFrequencyWeight_le_one H hH j t) (hfn t)
          simpa only [one_mul] using hh)
      _ ≤ _ := by simpa only [sub_zero] using hmean 0 H hH.le
  have htail := pd7d_positive_weighted_tail H H C hH hH hC j hj f hf hfn hweighted.integrableOn hmean
  have htail' : (∫ t in Set.Ioi H, g t) ≤ C * (1 + H) * pd7dPSeries j := by
    simpa only [div_self (ne_of_gt hH), one_pow, mul_one] using htail
  rw [← hsplit]
  calc
    _ ≤ C * (1 + H) + C * (1 + H) * pd7dPSeries j := add_le_add hcentral htail'
    _ = _ := by ring

end ArtinPrimitiveRoots.TypeII.PD
