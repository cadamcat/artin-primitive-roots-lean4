import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.PlaneIntegration
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.EndpointPolynomials
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.AffineEndpointEnergy

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical MeasureTheory
set_option autoImplicit false

lemma pd7d_plane_endpoint_operator (F : PDPlane → ℂ) (Q P : ℝ → ℂ)
    (X H S C eps CF D MQ MP : ℝ) (hX : 1 ≤ X) (hH : 1 ≤ H) (hS : 1 ≤ S)
    (hC : 0 ≤ C) (heps : 0 ≤ eps) (hCF : 0 ≤ CF) (j : ℕ) (hj : 2 ≤ j)
    (hF : Integrable F) (hQ : Continuous Q) (hP : Continuous P)
    (hQb : ∀ t, ‖Q t‖ ≤ MQ) (hPb : ∀ t, ‖P t‖ ≤ MP)
    (hdecay : ∀ v, ‖F v‖ ≤ CF * pd7dFrequencyWeight H j (v 0) * pd7dFrequencyWeight H j (v 1))
    (hQmean : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, ‖Q t‖^2) ≤ C*(1+(b-a)/X))
    (hPmean : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, ‖P t‖^2) ≤ C*(1+(b-a)/X))
    (hQenergy : (∫ t in (-2*X*S)..(2*X*S), ‖Q t‖^2) ≤ eps)
    (hPenergy : (∫ t in (-2*X*S)..(2*X*S), ‖P t‖^2) ≤ eps) :
    ‖∫ v : PDPlane, F v * Complex.exp (-Complex.I * v 1 * Real.log D) *
      Q (X * v 0) * star (P (X * v 0 - v 1))‖ ≤
      CF * ((2*S*eps + 32*C*H*S*(H/S)^j*(1+pd7dPSeries j)^2)/X) := by
  have hXp : 0 < X := by linarith
  have hHp : 0 < H := by linarith
  let w := pd7dFrequencyWeight H j
  let f (z : ℝ × ℝ) := ‖Q (X*z.2) * star (P (X*z.2-z.1))‖
  have hfc : Continuous f := by dsimp [f]; fun_prop
  have hfn : ∀ z, 0 ≤ f z := fun z => norm_nonneg _
  have hfb : ∀ z, f z ≤ MQ*MP := by
    intro z
    dsimp [f]
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hQb _) (hPb _) (norm_nonneg _) ((norm_nonneg (Q 0)).trans (hQb 0))
  have hm := pd7d_affine_endpoint_product_mean Q P X C 0 hXp hQ hP hQmean hPmean
  have hcenter := pd7d_affine_endpoint_product_center Q P X S eps hX (by linarith) hQ hP hQenergy hPenergy
  have hoperator := pd7d_weighted_double_bound H S (C/X) (eps/X) (MQ*MP) hH hS
    (by positivity) (by positivity) j hj f hfc hfn hfb
    (fun s => pd7d_affine_endpoint_product_mean Q P X C s hXp hQ hP hQmean hPmean) hcenter
  let U (v : PDPlane) := Complex.exp (-Complex.I * v 1 * Real.log D) *
    Q (X * v 0) * star (P (X * v 0-v 1))
  have hUc : Continuous U := by dsimp [U]; fun_prop
  have hUb (v : PDPlane) : ‖U v‖ ≤ MQ*MP := by
    have hp : ‖Complex.exp (-Complex.I * v 1 * Real.log D)‖ = 1 := by
      convert pd7d_complex_phase_norm (-v 1) (Real.log D) using 1 <;> congr 1 <;> push_cast <;> ring
    dsimp [U]
    rw [norm_mul, norm_mul, hp, Complex.norm_conj, one_mul]
    exact mul_le_mul (hQb _) (hPb _) (norm_nonneg _) ((norm_nonneg (Q 0)).trans (hQb 0))
  have hGi : Integrable (fun v => F v * U v) :=
    hF.mul_bdd hUc.aestronglyMeasurable (ae_of_all _ hUb)
  have hGn := pd7d_plane_real_integrable_product _ hGi.norm
  have hw := pd7dFrequencyWeight_integrable H hHp j hj
  let g (z : ℝ × ℝ) := w z.1 * w z.2 * f (z.2,z.1)
  have hgc : Continuous (fun z : ℝ × ℝ => f (z.2,z.1)) := hfc.comp continuous_swap
  have hgi : Integrable g := (hw.mul_prod hw).mul_bdd hgc.aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hfn _)]; exact hfb _)
  calc
    _ = ‖∫ v : PDPlane, F v * U v‖ := by congr 1; apply integral_congr_ae; exact ae_of_all _ fun v => by dsimp [U]; ring
    _ ≤ ∫ v : PDPlane, ‖F v * U v‖ := norm_integral_le_integral_norm _
    _ = ∫ z : ℝ × ℝ, ‖F (pd7dPlanePoint z.1 z.2) * U (pd7dPlanePoint z.1 z.2)‖ :=
      pd7d_plane_real_integral_eq_product _
    _ ≤ ∫ z : ℝ × ℝ, CF * g z := integral_mono hGn (hgi.const_mul CF) (fun z => by
      rw [norm_mul]
      have hb := hdecay (pd7dPlanePoint z.1 z.2)
      simp only [pd7dPlanePoint_zero, pd7dPlanePoint_one] at hb
      have hp : ‖U (pd7dPlanePoint z.1 z.2)‖ = f (z.2,z.1) := by
        dsimp only [U,f]
        simp only [pd7dPlanePoint_zero, pd7dPlanePoint_one]
        rw [norm_mul, norm_mul, norm_mul]
        have hphase : ‖Complex.exp (-Complex.I * z.2 * Real.log D)‖ = 1 := by
          convert pd7d_complex_phase_norm (-z.2) (Real.log D) using 1 <;> congr 1 <;> push_cast <;> ring
        rw [hphase, one_mul]
      rw [hp]
      calc
        _ ≤ (CF * w z.1 * w z.2) * f (z.2,z.1) := mul_le_mul_of_nonneg_right hb (hfn _)
        _ = _ := by dsimp [g]; ring)
    _ = CF * (∫ s : ℝ, ∫ t : ℝ, w s * w t * f (s,t)) := by
      rw [integral_const_mul]
      rw [Measure.volume_eq_prod, integral_prod_symm g hgi]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun s => by apply integral_congr_ae; exact ae_of_all _ fun t => by dsimp [g]; ring
    _ ≤ CF * (2*S*(eps/X) + 32*(C/X)*H*S*(H/S)^j*(1+pd7dPSeries j)^2) :=
      mul_le_mul_of_nonneg_left hoperator hCF
    _ = _ := by field_simp
end ArtinPrimitiveRoots.TypeII.PD
