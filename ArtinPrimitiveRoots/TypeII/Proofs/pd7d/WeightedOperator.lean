import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.SymmetricWeights
import Mathlib.MeasureTheory.Integral.Prod

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
set_option autoImplicit false

lemma pd7d_integral_three_parts (S : ℝ) (hS : 0 ≤ S) (f : ℝ → ℝ) (hf : Integrable f) :
    (∫ t : ℝ, f t) = (∫ t in (-S)..S, f t) +
      (∫ t in Set.Iio (-S), f t) + (∫ t in Set.Ioi S, f t) := by
  have hh := intervalIntegral.integral_Ici_sub_Ici hf.integrableOn (by linarith : -S ≤ S)
  simp_rw [integral_Ici_eq_integral_Ioi] at hh
  have hs := intervalIntegral.integral_Iio_add_Ici (b := -S) hf.integrableOn hf.integrableOn
  rw [integral_Ici_eq_integral_Ioi] at hs
  rw [integral_Ico_eq_integral_Ioc] at hh
  rw [intervalIntegral.integral_of_le (by linarith : -S ≤ S)]
  linarith

lemma pd7d_weighted_center_tail (H S C eps : ℝ) (hH : 1 ≤ H) (hS : 1 ≤ S) (hC : 0 ≤ C)
    (j : ℕ) (hj : 2 ≤ j) (f : ℝ → ℝ) (hf : Continuous f) (hfn : ∀ t, 0 ≤ f t)
    (hweighted : Integrable (fun t => pd7dFrequencyWeight H j t * f t))
    (hmean : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, f t) ≤ C * (1 + (b - a)))
    (hcenter : (∫ t in (-S)..S, f t) ≤ eps) :
    (∫ t : ℝ, pd7dFrequencyWeight H j t * f t) ≤
      eps + 4 * C * S * (H / S) ^ j * (1 + pd7dPSeries j) := by
  have hHp : 0 < H := by linarith
  have hmid : (∫ t in (-S)..S, pd7dFrequencyWeight H j t * f t) ≤ eps := by
    calc
      _ ≤ ∫ t in (-S)..S, f t := intervalIntegral.integral_mono_on (by linarith)
        (((pd7dFrequencyWeight_continuous H hHp j).mul hf).intervalIntegrable _ _)
        (hf.intervalIntegrable _ _) (fun t _ => by
          exact mul_le_of_le_one_left (hfn t) (pd7dFrequencyWeight_le_one H hHp j t))
      _ ≤ _ := hcenter
  have htail := pd7d_weighted_tails H S C hHp hS hC j hj f hf hfn hweighted hmean
  rw [pd7d_integral_three_parts S (by linarith) _ hweighted]
  linarith

lemma pd7d_weighted_double_bound (H S C eps R : ℝ) (hH : 1 ≤ H) (hS : 1 ≤ S)
    (hC : 0 ≤ C) (heps : 0 ≤ eps) (j : ℕ) (hj : 2 ≤ j)
    (f : ℝ × ℝ → ℝ) (hf : Continuous f) (hfn : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ R)
    (hmean : ∀ s a b : ℝ, a ≤ b → (∫ t in a..b, f (s,t)) ≤ C * (1 + (b-a)))
    (hcenter : ∀ s ∈ Set.Icc (-S) S, (∫ t in (-S)..S, f (s,t)) ≤ eps) :
    (∫ s : ℝ, ∫ t : ℝ, pd7dFrequencyWeight H j s * pd7dFrequencyWeight H j t * f (s,t)) ≤
      2 * S * eps + 32 * C * H * S * (H / S) ^ j * (1 + pd7dPSeries j) ^ 2 := by
  let w := pd7dFrequencyWeight H j
  let Z := 1 + pd7dPSeries j
  have hZ : 0 ≤ Z := by dsimp [Z]; linarith [pd7dPSeries_nonneg j]
  have hHp : 0 < H := by linarith
  have hw := pd7dFrequencyWeight_integrable H hHp j hj
  have hwi (s : ℝ) : Integrable (fun t => w t * f (s,t)) := by
    exact hw.mul_bdd (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hfn _)]; exact hfb _)
  have hprod : Integrable (fun z : ℝ × ℝ => w z.1 * w z.2 * f z) :=
    (hw.mul_prod hw).mul_bdd hf.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hfn _)]; exact hfb _)
  let W (s : ℝ) := ∫ t : ℝ, w t * f (s,t)
  have houter : Integrable (fun s => w s * W s) := by
    have hh := hprod.integral_prod_left
    convert hh using 1
    funext s
    exact (integral_const_mul (w s) (fun t => w t * f (s,t))).symm.trans
      (integral_congr_ae (ae_of_all _ fun t => by ring))
  have hW (s : ℝ) : W s ≤ 4 * C * H * Z :=
    pd7d_weighted_full H C hH hC j hj _ (hf.comp (continuous_const.prodMk continuous_id))
      (fun t => hfn _) (hwi s) (hmean s)
  have hsmall (s : ℝ) (hs : s ∈ Set.Icc (-S) S) : W s ≤ eps + 4 * C * S * (H / S) ^ j * Z :=
    pd7d_weighted_center_tail H S C eps hH hS hC j hj _
      (hf.comp (continuous_const.prodMk continuous_id)) (fun t => hfn _)
      (hwi s) (hmean s) (hcenter s hs)
  let T := 4 * C * S * (H/S)^j * Z
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hfullw : (∫ s : ℝ, w s) ≤ 4 * H * Z := by
    have hh := pd7d_weighted_full H 1 hH (by norm_num) j hj (fun _ => 1)
      continuous_const (by intros; norm_num) (by simpa only [mul_one] using hw)
      (by intro a b hab; simp only [intervalIntegral.integral_const, smul_eq_mul]; linarith)
    simpa only [mul_one, one_mul] using hh
  have hmid : (∫ s in (-S)..S, w s * W s) ≤
      2 * S * eps + 16 * C * H * S * (H/S)^j * Z^2 := by
    rw [intervalIntegral.integral_of_le (by linarith : -S ≤ S)]
    have hc : IntegrableOn (fun _ : ℝ => eps) (Set.Ioc (-S) S) :=
      (continuous_const : Continuous (fun _ : ℝ => eps)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    calc
      _ ≤ ∫ s in Set.Ioc (-S) S, (eps + w s * T) :=
        setIntegral_mono_on houter.integrableOn (hc.add (hw.mul_const T).integrableOn) measurableSet_Ioc
          (fun s hs => by
            have hh := mul_le_mul_of_nonneg_left (hsmall s ⟨hs.1.le,hs.2⟩)
              (pd7dFrequencyWeight_nonneg H hHp j s)
            have he := mul_le_of_le_one_left heps (pd7dFrequencyWeight_le_one H hHp j s)
            dsimp [T] at *
            nlinarith)
      _ = 2*S*eps + T * ∫ s in Set.Ioc (-S) S, w s := by
        rw [integral_add hc (hw.mul_const T).integrableOn, integral_mul_const]
        simp only [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul]
        rw [max_eq_left (by linarith : 0 ≤ S - -S)]
        ring
      _ ≤ 2*S*eps + T * (4*H*Z) := by
        apply add_le_add_right
        exact mul_le_mul_of_nonneg_left
          ((setIntegral_le_integral hw (ae_of_all _ fun s => pd7dFrequencyWeight_nonneg H hHp j s)).trans hfullw) hT
      _ = _ := by dsimp [T]; ring
  have hout (T : Set ℝ) (hT : MeasurableSet T) :
      (∫ s in T, w s * W s) ≤ (4*C*H*Z) * ∫ s in T, w s := by
    calc
      _ ≤ ∫ s in T, (4*C*H*Z) * w s := setIntegral_mono_on houter.integrableOn
        (hw.const_mul _).integrableOn hT (fun s _ => by
          calc
            _ ≤ w s * (4*C*H*Z) := mul_le_mul_of_nonneg_left (hW s) (pd7dFrequencyWeight_nonneg H hHp j s)
            _ = _ := mul_comm _ _)
      _ = _ := integral_const_mul _ _
  have htailw : (∫ s in Set.Iio (-S), w s) + (∫ s in Set.Ioi S, w s) ≤
      4 * S * (H/S)^j * Z := by
    have hh := pd7d_weighted_tails H S 1 hHp hS (by norm_num) j hj (fun _ => 1)
      continuous_const (by intros; norm_num) (by simpa only [mul_one] using hw)
      (by intro a b hab; simp only [intervalIntegral.integral_const, smul_eq_mul]; linarith)
    simpa only [mul_one, one_mul] using hh
  have hneg := hout (Set.Iio (-S)) measurableSet_Iio
  have hpos := hout (Set.Ioi S) measurableSet_Ioi
  have htail : (∫ s in Set.Iio (-S), w s * W s) + (∫ s in Set.Ioi S, w s * W s) ≤
      16 * C * H * S * (H/S)^j * Z^2 := by
    have hh := mul_le_mul_of_nonneg_left htailw (by positivity : 0 ≤ 4*C*H*Z)
    nlinarith
  rw [show (∫ s : ℝ, ∫ t : ℝ, pd7dFrequencyWeight H j s * pd7dFrequencyWeight H j t * f (s,t)) =
    ∫ s : ℝ, w s * W s by
      apply integral_congr_ae
      exact ae_of_all _ fun s => by dsimp [W,w]; rw [← integral_const_mul]; apply integral_congr_ae; exact ae_of_all _ fun t => by ring]
  rw [pd7d_integral_three_parts S (by linarith) _ houter]
  linarith

end ArtinPrimitiveRoots.TypeII.PD
