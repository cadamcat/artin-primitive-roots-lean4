import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.KernelMellin
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.TailPolynomial
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ConjugateCharacters

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open scoped FourierTransform
set_option autoImplicit false

noncomputable def pd7dEndpointPolynomial {α : Type*} (S : Finset α) (n : α → ℕ)
    (c : α → ℂ) (t : ℝ) : ℂ := ∑ i ∈ S, c i * Complex.exp (Complex.I * t * Real.log (n i : ℝ))

lemma pd7dEndpointPolynomial_continuous {α : Type*} (S : Finset α) (n : α → ℕ) (c : α → ℂ) :
    Continuous (pd7dEndpointPolynomial S n c) := by
  change Continuous (fun t : ℝ => ∑ i ∈ S, c i * Complex.exp (Complex.I * t * Real.log (n i : ℝ)))
  fun_prop

lemma pd7dEndpointPolynomial_norm_le {α : Type*} (S : Finset α) (n : α → ℕ) (c : α → ℂ) (t : ℝ) :
    ‖pd7dEndpointPolynomial S n c t‖ ≤ ∑ i ∈ S, ‖c i‖ := by
  unfold pd7dEndpointPolynomial
  calc
    _ ≤ ∑ i ∈ S, ‖c i * Complex.exp (Complex.I * t * Real.log (n i : ℝ))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, pd7d_complex_phase_norm, mul_one]

lemma pd7dFourier2_integrable (f : PDPlane → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    Integrable (pd7dFourier2 f) := by
  let F : SchwartzMap PDPlane ℂ := hc.toSchwartzMap hf
  have hFt : 𝓕 f = ((𝓕 F : SchwartzMap PDPlane ℂ) : PDPlane → ℂ) := rfl
  have hfi : Integrable (𝓕 f) := by rw [hFt]; exact (𝓕 F : SchwartzMap PDPlane ℂ).integrable
  have hscaled := hfi.comp_smul (R := (2 * Real.pi)⁻¹) (by positivity : (2 * Real.pi)⁻¹ ≠ 0)
  exact hscaled.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ) ^ 2)

lemma pd7d_mellin_ratio_phase (a b D t u : ℝ) (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) :
    Complex.exp (Complex.I * ((t * Real.log (b / D) + (u - t) * Real.log (a / D) : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * u * Real.log D) *
        Complex.exp (Complex.I * t * Real.log b) * Complex.exp (Complex.I * ((u - t : ℝ) : ℂ) * Real.log a) := by
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt hD), Real.log_div (ne_of_gt ha) (ne_of_gt hD),
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end ArtinPrimitiveRoots.TypeII.PD

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
set_option autoImplicit false

lemma pd7d_complex_exp_real_norm (s : ℝ) :
    ‖Complex.exp (Complex.I * (s : ℂ))‖ = 1 := by
  simpa only [Complex.ofReal_one, mul_one] using pd7d_complex_phase_norm s 1

lemma pd7dEndpointPolynomial_mul {α β : Type*} (S : Finset α) (T : Finset β)
    (n : α → ℕ) (m : β → ℕ) (c : α → ℂ) (d : β → ℂ)
    (hn : ∀ i ∈ S, 0 < n i) (hm : ∀ j ∈ T, 0 < m j) (t : ℝ) :
    pd7dEndpointPolynomial S n c t * pd7dEndpointPolynomial T m d t =
      pd7dEndpointPolynomial (S ×ˢ T) (fun z => n z.1 * m z.2)
        (fun z => c z.1 * d z.2) t := by
  unfold pd7dEndpointPolynomial
  rw [Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hnp : 0 < (n i : ℝ) := by exact_mod_cast hn i hi
  have hmp : 0 < (m j : ℝ) := by exact_mod_cast hm j hj
  rw [Nat.cast_mul, Real.log_mul (ne_of_gt hnp) (ne_of_gt hmp)]
  have hphase : Complex.exp (Complex.I * t * ((Real.log (n i : ℝ) + Real.log (m j : ℝ) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * t * Real.log (n i : ℝ)) * Complex.exp (Complex.I * t * Real.log (m j : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

lemma pd7d_finite_mellin_pair {α β : Type*} (S : Finset α) (T : Finset β)
    (n : α → ℕ) (m : β → ℕ) (c : α → ℂ) (d : β → ℂ)
    (κ ψ : ℝ → ℝ) (X lam R D : ℝ) (hX : 1 ≤ X) (hR : 0 ≤ R) (hD : 0 < D)
    (hκ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hκsupp : Function.support κ ⊆ Set.Icc (1 / 2 : ℝ) 32)
    (hψsupp : Function.support ψ ⊆ Set.Icc (-R) R)
    (hκone : ∀ y ∈ Set.Icc (1 : ℝ) 16, κ y = 1)
    (hn : ∀ i ∈ S, c i ≠ 0 → (n i : ℝ) / D ∈ Set.Icc (1 : ℝ) 16)
    (hm : ∀ j ∈ T, d j ≠ 0 → (m j : ℝ) / D ∈ Set.Icc (1 : ℝ) 16) :
    (∑ i ∈ S, ∑ j ∈ T, c i * d j *
      ((ψ (X * ((n i : ℝ) / D - (m j : ℝ) / D)) : ℂ) *
        ArtinPrimitiveRoots.TypeII.additiveCharacter (lam * X * ((n i : ℝ) / D - (m j : ℝ) / D)))) =
      ∫ v : PDPlane, pd7dFourier2 (pd7dScaledKernel κ ψ X lam) v *
        Complex.exp (-Complex.I * v 1 * Real.log D) *
        pd7dEndpointPolynomial S n c (X * v 0) *
        pd7dEndpointPolynomial T m d (v 1 - X * v 0) := by
  let F := pd7dFourier2 (pd7dScaledKernel κ ψ X lam)
  have hFi : Integrable F := pd7dFourier2_integrable _
    (pd7d_scaled_kernel_contDiff κ ψ X lam hκ hψ)
    (pd7d_scaled_kernel_hasCompactSupport κ ψ X lam R hX hR hκsupp hψsupp)
  let g (i : α) (j : β) (v : PDPlane) := F v *
    Complex.exp (-Complex.I * v 1 * Real.log D) *
    (c i * Complex.exp (Complex.I * (X * v 0) * Real.log (n i : ℝ))) *
    (d j * Complex.exp (Complex.I * (v 1 - X * v 0) * Real.log (m j : ℝ)))
  have hgi (i : α) (j : β) : Integrable (g i j) := by
    have hc : Continuous (fun v : PDPlane =>
        Complex.exp (-Complex.I * v 1 * Real.log D) *
        (c i * Complex.exp (Complex.I * (X * v 0) * Real.log (n i : ℝ))) *
        (d j * Complex.exp (Complex.I * (v 1 - X * v 0) * Real.log (m j : ℝ)))) := by fun_prop
    have hp (v : PDPlane) : ‖Complex.exp (-Complex.I * v 1 * Real.log D)‖ = 1 := by
      convert pd7d_complex_phase_norm (-v 1) (Real.log D) using 1 <;> congr 1 <;> push_cast <;> ring
    have hp₀ (v : PDPlane) : ‖Complex.exp (Complex.I * (X * v 0) * Real.log (n i : ℝ))‖ = 1 :=
      by simpa only [Complex.ofReal_mul] using pd7d_complex_phase_norm (X * v 0) (Real.log (n i : ℝ))
    have hp₁ (v : PDPlane) : ‖Complex.exp (Complex.I * (v 1 - X * v 0) * Real.log (m j : ℝ))‖ = 1 :=
      by simpa only [Complex.ofReal_mul, Complex.ofReal_sub] using pd7d_complex_phase_norm (v 1 - X * v 0) (Real.log (m j : ℝ))
    have hh := hFi.mul_bdd hc.aestronglyMeasurable (ae_of_all _ (fun v => by
      change _ ≤ ‖c i‖ * ‖d j‖
      rw [norm_mul, norm_mul, norm_mul, norm_mul, hp, hp₀, hp₁]
      simp only [mul_one, one_mul]
      exact le_rfl))
    convert hh using 1
    funext v
    dsimp [g]
    ring
  have hterm (i : α) (hi : i ∈ S) (j : β) (hj : j ∈ T) :
      c i * d j * ((ψ (X * ((n i : ℝ) / D - (m j : ℝ) / D)) : ℂ) *
        ArtinPrimitiveRoots.TypeII.additiveCharacter (lam * X * ((n i : ℝ) / D - (m j : ℝ) / D))) =
        ∫ v : PDPlane, g i j v := by
    by_cases hci : c i = 0
    · simp [hci, g]
    by_cases hdj : d j = 0
    · simp [hdj, g]
    have hni := hn i hi hci
    have hmj := hm j hj hdj
    have hnpos : 0 < (n i : ℝ) := by
      have hh := (le_div_iff₀ hD).mp hni.1
      linarith
    have hmpos : 0 < (m j : ℝ) := by
      have hh := (le_div_iff₀ hD).mp hmj.1
      linarith
    rw [pd7d_scaled_kernel_mellin κ ψ X lam R _ _ hX hR hκ hψ hκsupp hψsupp hκone hni hmj,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [pd7d_mellin_ratio_phase _ _ D (X * v 0) (v 1) hmpos hnpos hD]
    dsimp [g, F]
    push_cast
    ring
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∫ v : PDPlane, g i j v := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm i hi j hj
    _ = _ := by
      simp_rw [← integral_finset_sum T (fun j hj => hgi _ j)]
      rw [← integral_finset_sum S (fun i hi => integrable_finset_sum T (fun j hj => hgi i j))]
      apply integral_congr_ae
      filter_upwards [] with v
      unfold pd7dEndpointPolynomial
      simp only [g, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [F]
      push_cast
      ring

end ArtinPrimitiveRoots.TypeII.PD

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option autoImplicit false
lemma pd7dEndpointPolynomial_star {α : Type*} (S : Finset α) (n : α → ℕ) (c : α → ℂ) (t : ℝ) :
    pd7dEndpointPolynomial S n (fun i => star (c i)) t =
      star (pd7dEndpointPolynomial S n c (-t)) := by
  unfold pd7dEndpointPolynomial
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [star_mul, pd7d_negative_phase_star]
  ring

lemma pd7dEndpointPolynomial_const_mul {α : Type*} (S : Finset α) (n : α → ℕ) (c : α → ℂ) (a : ℂ) (t : ℝ) :
    pd7dEndpointPolynomial S n (fun i => a * c i) t = a * pd7dEndpointPolynomial S n c t := by
  unfold pd7dEndpointPolynomial
  simp only [Finset.mul_sum, mul_assoc]
end ArtinPrimitiveRoots.TypeII.PD
