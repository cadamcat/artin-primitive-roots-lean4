import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.EndpointEnergy
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.WeightedOperator

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
set_option autoImplicit false

lemma pd7d_affine_energy_mean (Q : ℝ → ℂ) (X C s a b : ℝ) (hX : 0 < X) (hab : a ≤ b)
    (hmean : ∀ u v : ℝ, u ≤ v → (∫ t in u..v, ‖Q t‖^2) ≤ C * (1+(v-u)/X)) :
    (∫ t in a..b, ‖Q (X*t-s)‖^2) ≤ (C/X) * (1+(b-a)) := by
  have hbound := hmean (X*a-s) (X*b-s) (by nlinarith)
  have hchange := intervalIntegral.integral_comp_mul_sub
    (f := fun t : ℝ => ‖Q t‖^2) (a := a) (b := b) (c := X) (ne_of_gt hX) s
  rw [hchange, smul_eq_mul]
  calc
    _ ≤ X⁻¹ * (C * (1+(X*b-s-(X*a-s))/X)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hX.le)
    _ = _ := by field_simp; ring

lemma pd7d_affine_energy_center (Q : ℝ → ℂ) (X S eps s : ℝ)
    (hQ : Continuous Q) (hX : 1 ≤ X) (hS : 0 ≤ S) (hs : |s| ≤ S)
    (henergy : (∫ t in (-2*X*S)..(2*X*S), ‖Q t‖^2) ≤ eps) :
    (∫ t in (-S)..S, ‖Q (X*t-s)‖^2) ≤ eps/X := by
  have hXp : 0 < X := by linarith
  have hchange := intervalIntegral.integral_comp_mul_sub
    (f := fun t : ℝ => ‖Q t‖^2) (a := -S) (b := S) (c := X) (ne_of_gt hXp) s
  rw [hchange, smul_eq_mul]
  have hleft : -2*X*S ≤ X*(-S)-s := by
    have hh := abs_le.mp hs
    have hXS : S ≤ X*S := by nlinarith
    nlinarith
  have hright : X*S-s ≤ 2*X*S := by
    have hh := abs_le.mp hs
    have hXS : S ≤ X*S := by nlinarith
    nlinarith
  have hsub : (∫ t in (X*(-S)-s)..(X*S-s), ‖Q t‖^2) ≤
      ∫ t in (-2*X*S)..(2*X*S), ‖Q t‖^2 := by
    rw [intervalIntegral.integral_of_le (by nlinarith : X*(-S)-s ≤ X*S-s),
      intervalIntegral.integral_of_le (by nlinarith : -2*X*S ≤ 2*X*S)]
    exact setIntegral_mono_set ((hQ.norm.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ (fun t ht => (Set.Ioc_subset_Ioc hleft hright) ht))
  calc
    _ ≤ X⁻¹ * eps := mul_le_mul_of_nonneg_left (hsub.trans henergy) (inv_nonneg.mpr hXp.le)
    _ = _ := by ring

lemma pd7d_affine_endpoint_product_mean (Q P : ℝ → ℂ) (X C s : ℝ) (hX : 0 < X)
    (hQ : Continuous Q) (hP : Continuous P)
    (hQmean : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, ‖Q t‖^2) ≤ C*(1+(b-a)/X))
    (hPmean : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, ‖P t‖^2) ≤ C*(1+(b-a)/X)) :
    ∀ a b : ℝ, a ≤ b →
      (∫ t in a..b, ‖Q (X*t) * star (P (X*t-s))‖) ≤ (C/X)*(1+(b-a)) := by
  intro a b hab
  have hQc : Continuous (fun t : ℝ => Q (X*t)) := by fun_prop
  have hPc : Continuous (fun t : ℝ => star (P (X*t-s))) := by fun_prop
  apply pd7d_endpoint_product_energy_le _ _ a b _ hab hQc hPc
  · simpa only [sub_zero] using pd7d_affine_energy_mean Q X C 0 a b hX hab hQmean
  · simpa only [norm_star] using pd7d_affine_energy_mean P X C s a b hX hab hPmean

lemma pd7d_affine_endpoint_product_center (Q P : ℝ → ℂ) (X S eps : ℝ)
    (hX : 1 ≤ X) (hS : 0 ≤ S) (hQ : Continuous Q) (hP : Continuous P)
    (hQenergy : (∫ t in (-2*X*S)..(2*X*S), ‖Q t‖^2) ≤ eps)
    (hPenergy : (∫ t in (-2*X*S)..(2*X*S), ‖P t‖^2) ≤ eps) :
    ∀ s ∈ Set.Icc (-S) S,
      (∫ t in (-S)..S, ‖Q (X*t) * star (P (X*t-s))‖) ≤ eps/X := by
  intro s hs
  have hQc : Continuous (fun t : ℝ => Q (X*t)) := by fun_prop
  have hPc : Continuous (fun t : ℝ => star (P (X*t-s))) := by fun_prop
  apply pd7d_endpoint_product_energy_le _ _ (-S) S _ (by linarith) hQc hPc
  · simpa only [sub_zero] using pd7d_affine_energy_center Q X S eps 0 hQ hX hS (by simpa using hS) hQenergy
  · simpa only [norm_star] using pd7d_affine_energy_center P X S eps s hP hX hS (abs_le.mpr hs) hPenergy

end ArtinPrimitiveRoots.TypeII.PD
