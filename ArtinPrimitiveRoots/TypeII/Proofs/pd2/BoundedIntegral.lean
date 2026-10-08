import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ArtinPrimitiveRoots.TypeII.PD
open MeasureTheory Set

noncomputable section

def rootBoxMeasure : Measure (ℝ × ℝ × ℝ) :=
  (volume.restrict (Icc (1 : ℝ) 16)).prod
    ((volume.restrict (Icc (1 : ℝ) 2)).prod (volume.restrict (Icc (0 : ℝ) 1)))

instance : IsFiniteMeasure rootBoxMeasure := by
  unfold rootBoxMeasure
  infer_instance

lemma bounded_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, |f y| ≤ B) : Integrable f μ := by
  apply (integrable_const B).mono hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hB] using hb y)

lemma interval_integral_eq_Icc (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ t in a..b, f t) = ∫ t in Icc a b, f t := by
  rw [intervalIntegral.integral_of_le hab, setIntegral_congr_set
    (Ioc_ae_eq_Icc : Ioc a b =ᵐ[volume] Icc a b)]

lemma triple_integral_eq_rootBox (f : ℝ × ℝ × ℝ → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, |f y| ≤ B) :
    (∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, f (u, v, r)) =
      ∫ y, f y ∂rootBoxMeasure := by
  have hi := bounded_integrable rootBoxMeasure f hf B hB hb
  have hsec (u : ℝ) : Integrable (fun z : ℝ × ℝ => f (u, z))
      ((volume.restrict (Icc (1 : ℝ) 2)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    apply bounded_integrable _ _ (hf.comp (measurable_const.prodMk measurable_id)) B hB
    exact fun z => hb (u, z)
  calc
    _ = ∫ u in Icc (1 : ℝ) 16, ∫ v in Icc (1 : ℝ) 2, ∫ r in Icc (0 : ℝ) 1,
        f (u, v, r) := by
      simp_rw [interval_integral_eq_Icc 0 1 (by norm_num),
        interval_integral_eq_Icc 1 2 (by norm_num), interval_integral_eq_Icc 1 16 (by norm_num)]
    _ = ∫ u in Icc (1 : ℝ) 16, ∫ z, f (u, z)
        ∂((volume.restrict (Icc (1 : ℝ) 2)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => (integral_prod _ (hsec u)).symm)
    _ = _ := (integral_prod f hi).symm

lemma triple_integral_finset_sum {ι : Type*} (T : Finset ι)
    (f : ι → ℝ × ℝ × ℝ → ℝ) (B : ι → ℝ)
    (hf : ∀ i ∈ T, Measurable (f i)) (hB : ∀ i ∈ T, 0 ≤ B i)
    (hb : ∀ i ∈ T, ∀ y, |f i y| ≤ B i) :
    (∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, ∑ i ∈ T, f i (u,v,r)) =
      ∑ i ∈ T, ∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, f i (u,v,r) := by
  classical
  have hsum : Measurable (fun y => ∑ i ∈ T, f i y) := Finset.measurable_sum T hf
  have hsumB : 0 ≤ ∑ i ∈ T, B i := Finset.sum_nonneg hB
  have hsumBound (y : ℝ × ℝ × ℝ) : |∑ i ∈ T, f i y| ≤ ∑ i ∈ T, B i := by
    calc
      _ ≤ ∑ i ∈ T, |f i y| := by simpa only [Real.norm_eq_abs] using norm_sum_le T (fun i => f i y)
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hb i hi y)
  rw [triple_integral_eq_rootBox _ hsum _ hsumB hsumBound,
    integral_finsetSum T (fun i hi => bounded_integrable _ _ (hf i hi) _ (hB i hi) (hb i hi))]
  apply Finset.sum_congr rfl
  intro i hi
  exact (triple_integral_eq_rootBox _ (hf i hi) _ (hB i hi) (hb i hi)).symm

lemma rootBoxMeasure_eq_restrict : rootBoxMeasure =
    (volume.prod (volume.prod volume)).restrict
      (Icc (1 : ℝ) 16 ×ˢ (Icc (1 : ℝ) 2 ×ˢ Icc (0 : ℝ) 1)) := by
  simp_rw [rootBoxMeasure, Measure.prod_restrict]

lemma rootBoxMeasure_ae_region : ∀ᵐ y ∂rootBoxMeasure,
    y ∈ Icc (1 : ℝ) 16 ×ˢ (Icc (1 : ℝ) 2 ×ˢ Icc (0 : ℝ) 1) := by
  rw [rootBoxMeasure_eq_restrict]
  exact ae_restrict_mem (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc))

lemma triple_integral_mono (f g : ℝ × ℝ × ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (Bf Bg : ℝ) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (hbf : ∀ y, |f y| ≤ Bf) (hbg : ∀ y, |g y| ≤ Bg)
    (hfg : ∀ y ∈ Icc (1 : ℝ) 16 ×ˢ (Icc (1 : ℝ) 2 ×ˢ Icc (0 : ℝ) 1), f y ≤ g y) :
    (∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, f (u,v,r)) ≤
      ∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, g (u,v,r) := by
  rw [triple_integral_eq_rootBox f hf Bf hBf hbf,
    triple_integral_eq_rootBox g hg Bg hBg hbg]
  apply integral_mono_ae (bounded_integrable _ _ hf _ hBf hbf)
    (bounded_integrable _ _ hg _ hBg hbg)
  exact rootBoxMeasure_ae_region.mono (fun y hy => hfg y hy)

lemma triple_integral_const (c : ℝ) :
    (∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, c) = 15 * c := by
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

end
end ArtinPrimitiveRoots.TypeII.PD
