import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Complex

open MeasureTheory MeasureTheory.Measure Set
open scoped FourierTransform RealInnerProductSpace

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_weights

open ArtinPrimitiveRoots A1 A2

private theorem complexGaussianMellin (s : ℂ) (hs : 0 < s.re) (t : ℝ) (ht : 0 < t) :
    ∫ z : ℂ, (Complex.normSq z : ℂ) ^ (s - 1) *
        Complex.exp (-(t : ℂ) * (Complex.normSq z : ℂ)) =
      (Real.pi : ℂ) * (t : ℂ) ^ (-s) * Complex.Gamma s := by
  let g : ℝ → ℂ := fun u => (u : ℂ) ^ (s - 1) * Complex.exp (-(t : ℂ) * (u : ℂ))
  have hnorm (p : ℝ × ℝ) : Complex.normSq (Complex.polarCoord.symm p) = p.1 ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, sq_abs]
  have hsub :
      ∫ r in Ioi (0 : ℝ), (2 * r : ℝ) • g (r ^ 2) = ∫ u in Ioi (0 : ℝ), g u := by
    simpa [g, smul_eq_mul, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
      (integral_comp_rpow_Ioi_of_pos (g := g) (p := (2 : ℝ)) (by norm_num))
  have hrad :
      ∫ r in Ioi (0 : ℝ), (r : ℂ) * g (r ^ 2) =
        (1 / 2 : ℂ) * ∫ u in Ioi (0 : ℝ), g u := by
    calc
      ∫ r in Ioi (0 : ℝ), (r : ℂ) * g (r ^ 2) =
          (1 / 2 : ℂ) * ∫ r in Ioi (0 : ℝ), (2 * r : ℝ) • g (r ^ 2) := by
            rw [← integral_const_mul]
            refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
            simp only [smul_eq_mul, Complex.real_smul]
            push_cast
            ring
      _ = (1 / 2 : ℂ) * ∫ u in Ioi (0 : ℝ), g u := by rw [hsub]
  have hΓ := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := s) hs ht
  have hΓ' : (∫ u in Ioi (0 : ℝ), g u) =
      (1 / (t : ℂ)) ^ s * Complex.Gamma s := by
    simpa [g, mul_comm] using hΓ
  have hangle : ∫ θ in Ioo (-Real.pi) Real.pi, (1 : ℂ) = (2 * Real.pi : ℝ) := by
    rw [integral_const]
    simp [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_real_Ioo_of_le (a := -Real.pi) (b := Real.pi)
        (by linarith [Real.pi_pos]), sub_neg_eq_add, smul_eq_mul, mul_one]
    ring
  calc
    ∫ z : ℂ, (Complex.normSq z : ℂ) ^ (s - 1) *
        Complex.exp (-(t : ℂ) * (Complex.normSq z : ℂ)) =
        ∫ p in Complex.polarCoord.target,
          p.1 • ((p.1 ^ 2 : ℝ) : ℂ) ^ (s - 1) *
            Complex.exp (-(t : ℂ) * ((p.1 ^ 2 : ℝ) : ℂ)) := by
          rw [← Complex.integral_comp_polarCoord_symm]
          refine setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet fun p hp => ?_
          rw [hnorm]
          simp only [smul_eq_mul, Complex.real_smul]
          ring
    _ = (∫ r in Ioi (0 : ℝ), (r : ℂ) * g (r ^ 2)) *
          ∫ θ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
          rw [Complex.polarCoord_target, ← setIntegral_prod_mul, volume_eq_prod]
          simp_rw [mul_one]
          congr! 2 <;> simp [g, Complex.real_smul] <;> ring_nf
    _ = (2 * Real.pi : ℝ) * ∫ r in Ioi (0 : ℝ), (r : ℂ) * g (r ^ 2) := by
          rw [hangle]
          push_cast
          ring
    _ = (Real.pi : ℂ) * ∫ u in Ioi (0 : ℝ), g u := by
          rw [hrad]
          push_cast
          ring
    _ = (Real.pi : ℂ) * (t : ℂ) ^ (-s) * Complex.Gamma s := by
          change (Real.pi : ℂ) *
              (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) *
                Complex.exp (-(t : ℂ) * (u : ℂ))) = _
          rw [hΓ']
          rw [show (1 / (t : ℂ)) ^ s = (t : ℂ) ^ (-s) by
          rw [one_div, Complex.inv_cpow_ofReal_nonneg ht.le, Complex.cpow_neg]]
          ring

private theorem complexGaussianFourier (t : ℝ) (ht : 0 < t) (x : ℂ) :
    ∫ y : ℂ, Complex.exp (-(t : ℂ) * (Complex.normSq y : ℂ)) *
        A1.psiC (-(x * y)) =
      (Real.pi / (t : ℝ) : ℂ) *
        Complex.exp (-((4 * Real.pi ^ 2 * Complex.normSq x / t : ℝ) : ℂ)) := by
  let w : ℂ := (-2 : ℝ) • star x
  have hinner (y : ℂ) : inner ℝ y w = -2 * (x * y).re := by
    change inner ℝ y ((-2 : ℝ) • star x) = _
    rw [inner_smul_right_eq_smul, Complex.inner]
    simp [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have hw : ‖w‖ = 2 * ‖x‖ := by simp [w]
  have hnorm : ‖w‖ ^ 2 = 4 * Complex.normSq x := by
    rw [hw, Complex.normSq_eq_norm_sq]
    ring_nf
  have hnormC : (‖w‖ : ℂ) ^ 2 = ((4 * Complex.normSq x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hnorm]
  have hb : 0 < (t : ℂ).re := by simpa using ht
  have hgauss := fourier_gaussian_innerProductSpace (b := (t : ℂ)) hb w
  calc
    ∫ y : ℂ, Complex.exp (-(t : ℂ) * (Complex.normSq y : ℂ)) *
        A1.psiC (-(x * y)) =
        𝓕 (fun y : ℂ => Complex.exp (-(t : ℂ) * (‖y‖ : ℂ) ^ 2)) w := by
          rw [Real.fourier_eq']
          apply integral_congr_ae
          filter_upwards with y
          rw [hinner y]
          simp only [smul_eq_mul]
          have hq : (Complex.normSq y : ℂ) = (‖y‖ : ℂ) ^ 2 := by
            rw [Complex.normSq_eq_norm_sq]
            norm_cast
          rw [hq]
          simp [A1.psiC, Complex.neg_re]
          push_cast
          ring
    _ = (↑Real.pi / (t : ℂ)) ^ (Module.finrank ℝ ℂ / 2 : ℂ) *
          Complex.exp (-↑Real.pi ^ 2 * (‖w‖ : ℂ) ^ 2 / (t : ℂ)) := hgauss
    _ = (Real.pi / (t : ℝ) : ℂ) *
          Complex.exp (-((4 * Real.pi ^ 2 * Complex.normSq x / t : ℝ) : ℂ)) := by
          rw [Complex.finrank_real_complex]
          have hscalar : (↑Real.pi / (t : ℂ)) ^ ((↑(2 : ℕ) : ℂ) / 2) =
              (Real.pi / t : ℝ) := by
            rw [show ((↑(2 : ℕ) : ℂ) / 2) = 1 by norm_num, Complex.cpow_one]
            push_cast
            ring_nf
          rw [hscalar]
          have hexp : -↑Real.pi ^ 2 * (‖w‖ : ℂ) ^ 2 / (t : ℂ) =
              -((4 * Real.pi ^ 2 * Complex.normSq x / t : ℝ) : ℂ) := by
            rw [hnormC]
            push_cast
            ring_nf
          rw [hexp]
          push_cast
          ring_nf

private def complexScaledConj : ℂ →ₗ[ℝ] ℂ :=
  (-2 : ℝ) • Complex.conjLIE.toLinearMap

private def complexTatePairing : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => inner ℝ x (complexScaledConj y))
    (by intro x₁ x₂ y; simp [inner_add_left])
    (by intro c x y; simp [inner_smul_left] <;> ring)
    (by intro x y₁ y₂; simp [map_add, inner_add_right])
    (by intro c x y; simp [complexScaledConj, map_smul, inner_smul_right] <;> ring)

private theorem complexTatePairing_apply (x y : ℂ) :
    complexTatePairing x y = -2 * (x * y).re := by
  simp only [complexTatePairing, LinearMap.mk₂_apply, complexScaledConj,
    LinearMap.smul_apply]
  rw [inner_smul_right_eq_smul, Complex.inner]
  simp [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring_nf

private theorem complexTatePhase (x y : ℂ) :
    ((Real.fourierChar (-complexTatePairing x y) : Circle) : ℂ) =
      A1.psiC (-(x * y)) := by
  rw [complexTatePairing_apply]
  simp [Real.fourierChar_apply, Circle.coe_exp, A1.psiC, Complex.neg_re]
  push_cast
  ring_nf

private theorem complexGaussianPairing (f : SchwartzMap ℂ ℂ) (t : ℝ) (ht : 0 < t) :
    ∫ y : ℂ, (∫ x : ℂ, f x * A1.psiC (-(x * y))) *
        Complex.exp (-(t : ℂ) * (Complex.normSq y : ℂ)) =
      (Real.pi / (t : ℝ) : ℂ) *
        ∫ x : ℂ, f x * Complex.exp
          (-((4 * Real.pi ^ 2 * Complex.normSq x / t : ℝ) : ℂ)) := by
  let g : ℂ → ℂ := fun y => Complex.exp (-(t : ℂ) * (Complex.normSq y : ℂ))
  have hg0 : Integrable
      (fun y : ℂ => Complex.exp (-(t : ℂ) * (‖y‖ : ℂ) ^ 2)) := by
    have hb : 0 < (t : ℂ).re := by simpa using ht
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb (0 : ℂ) (0 : ℂ)
  have hg : Integrable g := by
    apply hg0.congr
    filter_upwards with y
    simp [g, Complex.normSq_eq_norm_sq]
  have hL : Continuous (fun p : ℂ × ℂ => complexTatePairing p.1 p.2) := by
    change Continuous (fun p : ℂ × ℂ => inner ℝ p.1 ((-2 : ℝ) • star p.2))
    fun_prop
  have hdual := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))
    (L := complexTatePairing) Real.continuous_fourierChar hL f.integrable hg
  have hleft (y : ℂ) :
      VectorFourier.fourierIntegral Real.fourierChar volume complexTatePairing
        (f : ℂ → ℂ) y = ∫ x : ℂ, f x * A1.psiC (-(x * y)) := by
    rw [VectorFourier.fourierIntegral]
    apply integral_congr_ae
    filter_upwards with x
    rw [Circle.smul_def, complexTatePhase]
    ring
  have hright (x : ℂ) :
      VectorFourier.fourierIntegral Real.fourierChar volume complexTatePairing.flip
        g x = (Real.pi / (t : ℝ) : ℂ) *
          Complex.exp (-((4 * Real.pi ^ 2 * Complex.normSq x / t : ℝ) : ℂ)) := by
    rw [VectorFourier.fourierIntegral]
    have hkernel : ∀ y : ℂ,
        (Real.fourierChar (-(complexTatePairing.flip y x)) : Circle) =
          Real.fourierChar (-complexTatePairing x y) := by
      intro y
      rfl
    calc
      ∫ y : ℂ, Real.fourierChar (-(complexTatePairing.flip y x)) • g y =
          ∫ y : ℂ, Complex.exp (-(t : ℂ) * (Complex.normSq y : ℂ)) *
            A1.psiC (-(x * y)) := by
              apply integral_congr_ae
              filter_upwards with y
              rw [Circle.smul_def, hkernel y, complexTatePhase]
              simp [g]
              ring
      _ = (Real.pi / (t : ℝ) : ℂ) *
            Complex.exp (-((4 * Real.pi ^ 2 * Complex.normSq x / t : ℝ) : ℂ)) :=
              complexGaussianFourier t ht x
  calc
    ∫ y : ℂ, (∫ x : ℂ, f x * A1.psiC (-(x * y))) * g y =
        ∫ y : ℂ,
          VectorFourier.fourierIntegral Real.fourierChar volume complexTatePairing
            (f : ℂ → ℂ) y • g y := by
              apply integral_congr_ae
              filter_upwards with y
              rw [hleft y]
              simp [smul_eq_mul]
    _ = ∫ x : ℂ, f x •
          VectorFourier.fourierIntegral Real.fourierChar volume complexTatePairing.flip
            g x := hdual
    _ = ∫ x : ℂ, f x *
          ((Real.pi / (t : ℝ) : ℂ) *
            Complex.exp (-((4 * Real.pi ^ 2 * Complex.normSq x / t : ℝ) : ℂ))) := by
              apply integral_congr_ae
              filter_upwards with x
              rw [hright x]
              simp [smul_eq_mul]
    _ = (Real.pi / (t : ℝ) : ℂ) *
          ∫ x : ℂ, f x * Complex.exp
            (-((4 * Real.pi ^ 2 * Complex.normSq x / t : ℝ) : ℂ)) := by
              calc
                _ = ∫ x : ℂ, (Real.pi / (t : ℝ) : ℂ) *
                      (f x * Complex.exp
                        (-((4 * Real.pi ^ 2 * Complex.normSq x / t : ℝ) : ℂ))) := by
                          apply integral_congr_ae
                          filter_upwards with x
                          ring
                _ = _ := by rw [integral_const_mul]

private theorem complexSchwartz_weighted_volume_integrable (g : SchwartzMap ℂ ℂ)
    (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun y : ℂ => ‖g y‖ * Complex.normSq y ^ (σ - 1)) := by
  let H : ℂ → ℂ := g
  have hmul : Integrable (fun y : ℂ => ‖H y‖ * Complex.normSq y ^ σ)
      A1.Theta.mulHaarC := by
    simpa [H] using complexSchwartz_weighted_integrable g σ hσ
  have hne : ∀ᵐ y : ℂ ∂(volume : Measure ℂ), y ≠ 0 := by
    simp [ae_iff]
  have htop : ∀ᵐ y : ℂ ∂(volume : Measure ℂ),
      ENNReal.ofReal ((Complex.normSq y)⁻¹) < ⊤ := by
    filter_upwards with y
    exact ENNReal.ofReal_lt_top
  have hweightMeas : Measurable (fun y : ℂ => ENNReal.ofReal ((Complex.normSq y)⁻¹)) :=
    by fun_prop
  rw [A1.Theta.mulHaarC] at hmul
  have hvol' : Integrable
      (fun y : ℂ => (ENNReal.ofReal ((Complex.normSq y)⁻¹)).toReal •
        (‖H y‖ * Complex.normSq y ^ σ)) (volume : Measure ℂ) :=
    (integrable_withDensity_iff_integrable_smul' hweightMeas htop).1 hmul
  apply hvol'.congr
  filter_upwards [hne] with y hy
  have hq : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
  have hdens : (ENNReal.ofReal ((Complex.normSq y)⁻¹)).toReal =
      (Complex.normSq y)⁻¹ := by
    simp [hq.le]
  rw [hdens, smul_eq_mul, Real.rpow_sub hq]
  simp only [Real.rpow_one]
  ring

private theorem complexExpMellinConvergent (a : ℂ) (ha : 0 < a.re) :
    MellinConvergent (fun t : ℝ => Complex.exp (-(t : ℂ))) a := by
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) • Complex.exp (-(t : ℂ)))
    (Set.Ioi 0)
  simpa [smul_eq_mul, mul_comm] using Complex.GammaIntegral_convergent ha

private theorem complexScaledLaplaceIntegrable (q : ℝ) (hq : 0 < q) (s : ℂ)
    (hs : 0 < s.re) (h1s : s.re < 1) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s) * Complex.exp (-((q * t : ℝ) : ℂ)))
      (Set.Ioi 0) := by
  have hscaled :=
    (MellinConvergent.comp_mul_left (f := fun u : ℝ => Complex.exp (-(u : ℂ)))
      (s := 1 - s) hq)
  have hmc : MellinConvergent (fun t : ℝ => Complex.exp (-((q * t : ℝ) : ℂ))) (1 - s) := by
    exact hscaled.2 (complexExpMellinConvergent (1 - s) (by dsimp; linarith))
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((1 - s) - 1) •
    Complex.exp (-((q * t : ℝ) : ℂ))) (Set.Ioi 0) at hmc
  simpa [smul_eq_mul, show (1 - s) - 1 = -s by ring, mul_comm] using hmc

private theorem complexLaplaceNorm_integral (c : ℂ) (q : ℝ) (s : ℂ) (hq : 0 < q)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ∫ t in Set.Ioi (0 : ℝ),
      ‖c * (t : ℂ) ^ (-s) * Complex.exp (-((q * t : ℝ) : ℂ))‖ =
      ‖c‖ * q ^ (s.re - 1) * Real.Gamma (1 - s.re) := by
  have hgamma := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := -s.re) (b := q) one_pos (by linarith) hq
  have harg : (-s.re + 1) / 1 = 1 - s.re := by ring
  have hexp : -((-s.re + 1) / 1) = s.re - 1 := by ring
  have hgamma' :
      ∫ t in Set.Ioi (0 : ℝ), t ^ (-s.re) * Real.exp (-(q * t)) =
        q ^ (s.re - 1) * Real.Gamma (1 - s.re) := by
    calc
      _ = q ^ (-((-s.re + 1) / 1)) * (1 / 1) *
            Real.Gamma ((-s.re + 1) / 1) := by
              simpa [Real.rpow_one] using hgamma
      _ = q ^ (s.re - 1) * Real.Gamma (1 - s.re) := by
            rw [hexp, harg]
            norm_num
  calc
    ∫ t in Set.Ioi (0 : ℝ),
        ‖c * (t : ℂ) ^ (-s) * Complex.exp (-((q * t : ℝ) : ℂ))‖ =
        ∫ t in Set.Ioi (0 : ℝ),
          ‖c‖ * (t ^ (-s.re)) * Real.exp (-(q * t)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            dsimp
            rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
              Complex.norm_exp]
            norm_num [Complex.mul_re]
    _ = ‖c‖ * ∫ t in Set.Ioi (0 : ℝ),
          t ^ (-s.re) * Real.exp (-(q * t)) := by
            rw [← integral_const_mul]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            ring
    _ = ‖c‖ * (q ^ (s.re - 1) * Real.Gamma (1 - s.re)) := by rw [hgamma']
    _ = ‖c‖ * q ^ (s.re - 1) * Real.Gamma (1 - s.re) := by ring

private theorem complexMellinLaplace_swap (g : SchwartzMap ℂ ℂ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Complex.Gamma (1 - s) *
        ∫ y : ℂ, g y * (Complex.normSq y : ℂ) ^ (s - 1) =
      ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-s) *
        (∫ y : ℂ, g y * Complex.exp (-((t * Complex.normSq y : ℝ) : ℂ))) := by
  let H : ℂ → ℂ := g
  let K : ℂ × ℝ → ℂ := fun p => H p.1 * (p.2 : ℂ) ^ (-s) *
    Complex.exp (-((p.2 * Complex.normSq p.1 : ℝ) : ℂ))
  have hHmeas : Measurable H := by exact g.continuous.measurable
  have hKmeas : Measurable K := by
    dsimp [K]
    fun_prop
  have hne : ∀ᵐ y : ℂ ∂(volume : Measure ℂ), y ≠ 0 := by
    simp [ae_iff]
  have hsections : ∀ᵐ y : ℂ ∂(volume : Measure ℂ),
      Integrable (fun t : ℝ => K (y, t)) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [hne] with y hy
    have hq : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
    have hqscaled := complexScaledLaplaceIntegrable (Complex.normSq y) hq s hs0 hs1
    have hqscaled' : Integrable
        (fun t : ℝ => H y * (t : ℂ) ^ (-s) *
          Complex.exp (-((t * Complex.normSq y : ℝ) : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      apply (hqscaled.const_mul (H y)).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      ring
    simpa [K] using hqscaled'
  have hnormOuter : Integrable (fun y : ℂ =>
      ∫ t : ℝ, ‖K (y, t)‖ ∂(volume.restrict (Set.Ioi (0 : ℝ))))
      (volume : Measure ℂ) := by
    have hw := complexSchwartz_weighted_volume_integrable g s.re hs0
    have hmain : Integrable (fun y : ℂ =>
        (‖H y‖ * Complex.normSq y ^ (s.re - 1)) * Real.Gamma (1 - s.re))
        (volume : Measure ℂ) := by
      simpa [H, mul_assoc] using hw.mul_const (Real.Gamma (1 - s.re))
    apply hmain.congr
    filter_upwards [hne] with y hy
    have hq : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
    simpa [K, mul_comm] using
      (complexLaplaceNorm_integral (H y) (Complex.normSq y) s hq hs0 hs1).symm
  have hKae : AEStronglyMeasurable K
      ((volume : Measure ℂ).prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
    hKmeas.aestronglyMeasurable
  have hKint : Integrable K
      ((volume : Measure ℂ).prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
    (integrable_prod_iff hKae).2 ⟨hsections, hnormOuter⟩
  have hswap := (integral_integral_swap
    (f := fun (y : ℂ) (t : ℝ) => K (y, t)) hKint)
  have hgamma (y : ℂ) (hy : y ≠ 0) :
      ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-s) *
          Complex.exp (-((t * Complex.normSq y : ℝ) : ℂ)) =
        (Complex.normSq y : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) := by
    have hq : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
    have hg := Complex.integral_cpow_mul_exp_neg_mul_Ioi
      (a := 1 - s) (r := Complex.normSq y) (by dsimp; linarith) hq
    have hpow : ((Complex.normSq y : ℂ)⁻¹) ^ (1 - s) =
        (Complex.normSq y : ℂ) ^ (s - 1) := by
      rw [Complex.inv_cpow_ofReal_nonneg hq.le,
        show s - 1 = -(1 - s) by ring, Complex.cpow_neg]
    simpa [show (1 - s) - 1 = -s by ring, Complex.ofReal_mul, mul_comm, hpow] using hg
  calc
    Complex.Gamma (1 - s) *
        ∫ y : ℂ, H y * (Complex.normSq y : ℂ) ^ (s - 1) =
      ∫ y : ℂ, (H y * (Complex.normSq y : ℂ) ^ (s - 1)) * Complex.Gamma (1 - s) := by
        rw [integral_mul_const]
        ring
    _ = ∫ y : ℂ, ∫ t : ℝ, K (y, t) ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
        apply integral_congr_ae
        filter_upwards [hne] with y hy
        calc
          (H y * (Complex.normSq y : ℂ) ^ (s - 1)) * Complex.Gamma (1 - s) =
              H y * ((Complex.normSq y : ℂ) ^ (s - 1) * Complex.Gamma (1 - s)) := by ring
          _ = H y * ∫ t in Set.Ioi (0 : ℝ),
                (t : ℂ) ^ (-s) * Complex.exp (-((t * Complex.normSq y : ℝ) : ℂ)) := by
                rw [hgamma y hy]
          _ = ∫ t : ℝ, K (y, t) ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
                rw [← integral_const_mul]
                apply setIntegral_congr_fun measurableSet_Ioi
                intro t ht
                simp [K, H, mul_assoc, Complex.ofReal_mul]
    _ = ∫ t : ℝ, ∫ y : ℂ, K (y, t) ∂volume ∂(volume.restrict (Set.Ioi (0 : ℝ))) := hswap
    _ = ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-s) *
          ∫ y : ℂ, H y * Complex.exp (-((t * Complex.normSq y : ℝ) : ℂ)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        calc
          ∫ y : ℂ, K (y, t) ∂volume =
              ∫ y : ℂ, (t : ℂ) ^ (-s) *
                (H y * Complex.exp (-((t * Complex.normSq y : ℝ) : ℂ))) := by
                  apply integral_congr_ae
                  filter_upwards with y
                  simp [K, mul_assoc]
                  ring
          _ = (t : ℂ) ^ (-s) *
                ∫ y : ℂ, H y * Complex.exp (-((t * Complex.normSq y : ℝ) : ℂ)) := by
                  rw [integral_const_mul]

private theorem complexMellin_inv_scale (M : ℝ → ℂ) (A : ℝ) (hA : 0 < A) (s : ℂ) :
    ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-s) * (Real.pi / t : ℝ) *
        M (A / t) =
      (Real.pi : ℂ) * (A : ℂ) ^ (-s) * mellin M s := by
  let N : ℝ → ℂ := fun u => M (A * u)
  have hinv : mellin (fun t : ℝ => M (A / t)) (-s) = mellin N s := by
    calc
      mellin (fun t : ℝ => M (A / t)) (-s) =
          mellin (fun t : ℝ => N (t ^ (-1 : ℝ))) (-s) := by
            unfold mellin
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            have hpow : t ^ (-1 : ℝ) = t⁻¹ := by
              rw [Real.rpow_neg ht.le, Real.rpow_one]
            simp [N, hpow, div_eq_mul_inv]
      _ = |(-1 : ℝ)|⁻¹ • mellin N ((-s) / (-1 : ℝ)) :=
            mellin_comp_rpow N (-s) (-1)
      _ = mellin N s := by norm_num
  have hscale : mellin N s = (A : ℂ) ^ (-s) • mellin M s := by
    simpa [N] using mellin_comp_mul_left M s hA
  have hkernel :
      ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-s) * (Real.pi / t : ℝ) * M (A / t) =
        (Real.pi : ℂ) * mellin (fun t : ℝ => M (A / t)) (-s) := by
    calc
      _ = ∫ t in Set.Ioi (0 : ℝ), (Real.pi : ℂ) *
            ((t : ℂ) ^ ((-s) - 1) * M (A / t)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro t ht
              have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
              have hdiv : ((Real.pi / t : ℝ) : ℂ) =
                  (Real.pi : ℂ) / (t : ℂ) := by norm_cast
              dsimp
              rw [hdiv, Complex.cpow_sub (-s) 1 ht0, Complex.cpow_one]
              ring
      _ = (Real.pi : ℂ) * mellin (fun t : ℝ => M (A / t)) (-s) := by
              rw [mellin, ← integral_const_mul]
              apply setIntegral_congr_fun measurableSet_Ioi
              intro t ht
              simp [smul_eq_mul]
  calc
    _ = (Real.pi : ℂ) * mellin (fun t : ℝ => M (A / t)) (-s) := hkernel
    _ = (Real.pi : ℂ) * mellin N s := by rw [hinv]
    _ = (Real.pi : ℂ) * (A : ℂ) ^ (-s) * mellin M s := by
          rw [hscale]
          simp only [smul_eq_mul]
          ring

def complexTateFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ) * ((4 * Real.pi ^ 2 : ℝ) : ℂ) ^ (-s) *
    Complex.Gamma s / Complex.Gamma (1 - s)

theorem complexTateFactor_sixth_ne_zero :
    complexTateFactor (1 / 6) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hA : ((4 * Real.pi ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hpow : ((4 * Real.pi ^ 2 : ℝ) : ℂ) ^ (-(1 / 6 : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
  have hΓ : Complex.Gamma (1 / 6 : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ' : Complex.Gamma (1 - (1 / 6 : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  unfold complexTateFactor
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hpi hpow) hΓ) hΓ'

theorem complexLocalTateEquation_volume (f : SchwartzMap ℂ ℂ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ∫ y : ℂ, complexFourierSchwartz f y * (Complex.normSq y : ℂ) ^ (s - 1) =
      complexTateFactor s *
        ∫ x : ℂ, f x * (Complex.normSq x : ℂ) ^ (-s) := by
  let A : ℝ := 4 * Real.pi ^ 2
  let M : ℝ → ℂ := fun u =>
    ∫ x : ℂ, f x * Complex.exp (-((u * Complex.normSq x : ℝ) : ℂ))
  have hA : 0 < A := by dsimp [A]; positivity
  have hgauss (t : ℝ) (ht : 0 < t) :
      ∫ y : ℂ, complexFourierSchwartz f y *
          Complex.exp (-((t * Complex.normSq y : ℝ) : ℂ)) =
        (Real.pi / t : ℝ) * M (A / t) := by
    calc
      _ = ∫ y : ℂ, (∫ x : ℂ, f x * A1.psiC (-(x * y))) *
            Complex.exp (-(t : ℂ) * (Complex.normSq y : ℂ)) := by
              apply integral_congr_ae
              filter_upwards with y
              rw [complexFourierSchwartz_eq_integral]
              congr 1
              push_cast
              ring_nf
      _ = (Real.pi / (t : ℝ) : ℂ) *
            ∫ x : ℂ, f x * Complex.exp
              (-((4 * Real.pi ^ 2 * Complex.normSq x / t : ℝ) : ℂ)) :=
              complexGaussianPairing f t ht
      _ = (Real.pi / t : ℝ) * M (A / t) := by
            rw [Complex.ofReal_div]
            dsimp [M]
            congr 1
            apply integral_congr_ae
            filter_upwards with x
            congr 1
            dsimp [A]
            push_cast
            ring_nf
  have hleft := complexMellinLaplace_swap (complexFourierSchwartz f) s hs0 hs1
  have houter :
      ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-s) *
          (∫ y : ℂ, complexFourierSchwartz f y *
            Complex.exp (-((t * Complex.normSq y : ℝ) : ℂ))) =
        (Real.pi : ℂ) * (A : ℂ) ^ (-s) * mellin M s := by
    calc
      _ = ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-s) *
            ((Real.pi / t : ℝ) * M (A / t)) := by
              apply integral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              rw [hgauss t ht]
      _ = ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-s) *
            (Real.pi / t : ℝ) * M (A / t) := by
              apply integral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              ring
      _ = (Real.pi : ℂ) * (A : ℂ) ^ (-s) * mellin M s :=
            complexMellin_inv_scale M A hA s
  have hright := complexMellinLaplace_swap f (1 - s)
    (by dsimp; linarith) (by dsimp; linarith)
  have hMellin : Complex.Gamma s *
      ∫ x : ℂ, f x * (Complex.normSq x : ℂ) ^ (-s) = mellin M s := by
    simpa [M, mellin, smul_eq_mul, show 1 - (1 - s) = s by ring,
      show (1 - s) - 1 = -s by ring, show -(1 - s) = s - 1 by ring] using hright
  have hden : Complex.Gamma (1 - s) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hbig : Complex.Gamma (1 - s) *
      (∫ y : ℂ, complexFourierSchwartz f y *
        (Complex.normSq y : ℂ) ^ (s - 1)) =
      (Real.pi : ℂ) * (A : ℂ) ^ (-s) *
        (Complex.Gamma s * ∫ x : ℂ, f x * (Complex.normSq x : ℂ) ^ (-s)) := by
    calc
      _ = ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-s) *
            (∫ y : ℂ, complexFourierSchwartz f y *
              Complex.exp (-((t * Complex.normSq y : ℝ) : ℂ))) := hleft
      _ = (Real.pi : ℂ) * (A : ℂ) ^ (-s) * mellin M s := houter
      _ = _ := by rw [← hMellin]
  calc
    _ = (Complex.Gamma (1 - s))⁻¹ *
          (Complex.Gamma (1 - s) *
            ∫ y : ℂ, complexFourierSchwartz f y * (Complex.normSq y : ℂ) ^ (s - 1)) := by
          calc
            _ = 1 * (∫ y : ℂ, complexFourierSchwartz f y *
                  (Complex.normSq y : ℂ) ^ (s - 1)) := by simp
            _ = ((Complex.Gamma (1 - s))⁻¹ * Complex.Gamma (1 - s)) *
                  ∫ y : ℂ, complexFourierSchwartz f y *
                    (Complex.normSq y : ℂ) ^ (s - 1) := by
                      exact congrArg (fun z : ℂ => z *
                        (∫ y : ℂ, complexFourierSchwartz f y *
                          (Complex.normSq y : ℂ) ^ (s - 1)))
                        (inv_mul_cancel₀ hden).symm
            _ = (Complex.Gamma (1 - s))⁻¹ *
                  (Complex.Gamma (1 - s) *
                    ∫ y : ℂ, complexFourierSchwartz f y *
                      (Complex.normSq y : ℂ) ^ (s - 1)) := by ac_rfl
    _ = (Complex.Gamma (1 - s))⁻¹ *
          ((Real.pi : ℂ) * (A : ℂ) ^ (-s) *
            (Complex.Gamma s * ∫ x : ℂ, f x * (Complex.normSq x : ℂ) ^ (-s))) := by
          rw [hbig]
    _ = complexTateFactor s *
          ∫ x : ℂ, f x * (Complex.normSq x : ℂ) ^ (-s) := by
          unfold complexTateFactor A
          rw [div_eq_mul_inv]
          ac_rfl

private theorem complexMulHaar_mellin_eq_volume (f : ℂ → ℂ) (s : ℂ) :
    ∫ z, f z * (Complex.normSq z : ℂ) ^ s ∂A1.Theta.mulHaarC =
      ∫ z, f z * (Complex.normSq z : ℂ) ^ (s - 1) := by
  have hne : ∀ᵐ z : ℂ ∂(volume : Measure ℂ), z ≠ 0 := by
    simp [ae_iff]
  have htop : ∀ᵐ z : ℂ ∂(volume : Measure ℂ),
      ENNReal.ofReal ((Complex.normSq z)⁻¹) < ⊤ := by
    filter_upwards with z
    exact ENNReal.ofReal_lt_top
  rw [A1.Theta.mulHaarC]
  change (∫ z, f z * (Complex.normSq z : ℂ) ^ s ∂volume.withDensity
      (fun z => ENNReal.ofReal ((Complex.normSq z)⁻¹))) = _
  calc
    _ = ∫ z, (ENNReal.ofReal ((Complex.normSq z)⁻¹)).toReal •
          (f z * (Complex.normSq z : ℂ) ^ s) :=
          integral_withDensity_eq_integral_toReal_smul (by fun_prop) htop _
    _ = ∫ z, f z * (Complex.normSq z : ℂ) ^ (s - 1) := by
          apply integral_congr_ae
          filter_upwards [hne] with z hz
          have hq : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
          have hden : (ENNReal.ofReal ((Complex.normSq z)⁻¹)).toReal =
              (Complex.normSq z)⁻¹ := by
            simp [hq.le]
          have hpow : (Complex.normSq z : ℂ) ^ (s - 1) =
              (Complex.normSq z : ℂ) ^ s / (Complex.normSq z : ℂ) := by
            rw [Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr hq.ne'), Complex.cpow_one]
          rw [hden, Complex.real_smul]
          simp only [Complex.ofReal_inv]
          rw [hpow]
          ring

theorem complexLocalTateEquation (f : SchwartzMap ℂ ℂ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ∫ y : ℂ, (∫ x : ℂ, f x * A1.psiC (-(x * y))) *
        (Complex.normSq y : ℂ) ^ s ∂A1.Theta.mulHaarC =
      complexTateFactor s *
        ∫ y : ℂ, f y * (Complex.normSq y : ℂ) ^ (1 - s) ∂A1.Theta.mulHaarC := by
  have hFourierEq : (fun y : ℂ => ∫ x : ℂ, f x * A1.psiC (-(x * y))) =
      complexFourierSchwartz f := by
    funext y
    exact (complexFourierSchwartz_eq_integral f y).symm
  have hR := complexMulHaar_mellin_eq_volume (fun y : ℂ => f y) (1 - s)
  have hR' : ∫ y : ℂ, f y * (Complex.normSq y : ℂ) ^ (-s) =
      ∫ y : ℂ, f y * (Complex.normSq y : ℂ) ^ (1 - s) ∂A1.Theta.mulHaarC := by
    simpa only [show (1 - s) - 1 = -s by ring] using hR.symm
  calc
    ∫ y : ℂ, (∫ x : ℂ, f x * A1.psiC (-(x * y))) *
        (Complex.normSq y : ℂ) ^ s ∂A1.Theta.mulHaarC =
        ∫ y : ℂ, (∫ x : ℂ, f x * A1.psiC (-(x * y))) *
          (Complex.normSq y : ℂ) ^ (s - 1) :=
            complexMulHaar_mellin_eq_volume _ s
    _ = ∫ y : ℂ, complexFourierSchwartz f y *
          (Complex.normSq y : ℂ) ^ (s - 1) := by
            apply integral_congr_ae
            filter_upwards with y
            exact congrArg (fun z : ℂ => z * (Complex.normSq y : ℂ) ^ (s - 1))
              (congrFun hFourierEq y)
    _ = complexTateFactor s *
          ∫ y : ℂ, f y * (Complex.normSq y : ℂ) ^ (-s) :=
            complexLocalTateEquation_volume f s hs0 hs1
    _ = complexTateFactor s *
          ∫ y : ℂ, f y * (Complex.normSq y : ℂ) ^ (1 - s) ∂A1.Theta.mulHaarC := by
            rw [hR']

end ArtinPrimitiveRoots.Proofs.a2_weights
end
