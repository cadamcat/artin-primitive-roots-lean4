import ArtinPrimitiveRoots.A1.AddChar
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory
open scoped FourierTransform

namespace ArtinPrimitiveRoots.Proofs.a2_zf_top

open ArtinPrimitiveRoots.A1

private noncomputable def archNegConj : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ (E := ℂ))

private noncomputable def archQ : ℂ ≃L[ℝ] ℂ :=
  archNegConj.toContinuousLinearEquiv.trans
    (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) (by norm_num)))

/-- The additive self-dual measure for the complex character `psiC`. -/
noncomputable def complexSelfDualHaar : Measure ℂ := (ENNReal.ofReal 2) • volume

theorem complexSelfDualHaar_isAddHaar : Measure.IsAddHaarMeasure complexSelfDualHaar := by
  have hzero : ENNReal.ofReal 2 ≠ 0 := by norm_num
  have htop : ENNReal.ofReal 2 < ⊤ := ENNReal.ofReal_lt_top
  simpa [complexSelfDualHaar] using
    (Measure.IsAddHaarMeasure.smul (μ := (volume : Measure ℂ)) hzero htop.ne)

noncomputable def complexFourier (f : ℂ → ℂ) (x : ℂ) : ℂ :=
  ∫ y, psiC (-(x * y)) * f y ∂complexSelfDualHaar

private theorem archQ_inner (x y : ℂ) :
    inner ℝ y (archQ x) = -(2 : ℝ) * (x * y).re := by
  rw [Complex.inner]
  simp [archQ, archNegConj, Complex.conjLIE_apply, Units.smul_def]
  ring

private theorem archKernel (x y : ℂ) :
    psiC (-(x * y)) =
      Complex.exp ((↑(-2 * Real.pi * inner ℝ y (archQ x)) : ℂ) * Complex.I) := by
  change Complex.exp (-(4 * Real.pi * Complex.I * ((-(x * y)).re : ℂ))) = _
  apply congrArg Complex.exp
  rw [Complex.neg_re]
  rw [archQ_inner]
  push_cast
  ring

private theorem archFourier_eq_standard (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    complexFourier (f : ℂ → ℂ) x = (2 : ℂ) * 𝓕 f (archQ x) := by
  unfold complexFourier complexSelfDualHaar
  rw [integral_smul_measure]
  have hfun : (fun y : ℂ => psiC (-(x * y)) * f y) =
      fun y => Complex.exp ((↑(-2 * Real.pi * inner ℝ y (archQ x)) : ℂ) * Complex.I) * f y := by
    funext y
    rw [archKernel]
  rw [hfun]
  calc
    (ENNReal.ofReal 2).toReal •
        ∫ y, Complex.exp ((↑(-2 * Real.pi * inner ℝ y (archQ x)) : ℂ) * Complex.I) * f y
          ∂(volume : Measure ℂ) =
        (2 : ℂ) * ∫ y, Complex.exp
          ((↑(-2 * Real.pi * inner ℝ y (archQ x)) : ℂ) * Complex.I) * f y
            ∂(volume : Measure ℂ) := by simp [ENNReal.toReal_ofReal, smul_eq_mul]
    _ = (2 : ℂ) * 𝓕 (f : ℂ → ℂ) (archQ x) := by
          rw [Real.fourier_eq']
          simp [smul_eq_mul]
    _ = (2 : ℂ) * 𝓕 f (archQ x) := by rfl

/-- The complex Fourier transform sends a Schwartz function to another Schwartz function. -/
noncomputable def complexFourierSchwartz (f : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (2 : ℂ) • (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ archQ) (𝓕 f)

theorem complexFourier_eq_schwartz (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    complexFourier (f : ℂ → ℂ) x = complexFourierSchwartz f x := by
  rw [archFourier_eq_standard]
  simp [complexFourierSchwartz, archQ]

private theorem integral_archQ (h : ℂ → ℂ) :
    ∫ y, h (archQ y) ∂(volume : Measure ℂ) =
      (1 / 4 : ℂ) * ∫ z, h z ∂(volume : Measure ℂ) := by
  calc
    (∫ y, h (archQ y) ∂(volume : Measure ℂ)) =
        ∫ y, h ((2 : ℝ) • archNegConj y) ∂(volume : Measure ℂ) := by
          simpa [archQ]
    _ = ∫ z, h ((2 : ℝ) • z) ∂(volume : Measure ℂ) := by
          let h' : ℂ → ℂ := fun z => h ((2 : ℝ) • z)
          change ∫ y, h' (archNegConj y) ∂(volume : Measure ℂ) = ∫ z, h' z ∂volume
          exact MeasureTheory.integral_comp archNegConj h'
    _ = (1 / 4 : ℝ) • ∫ z, h z ∂(volume : Measure ℂ) := by
          have hcomp := MeasureTheory.Measure.integral_comp_smul (volume : Measure ℂ) h 2
          have hfin : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
          rw [hfin] at hcomp
          norm_num at hcomp
          simpa [smul_eq_mul] using hcomp
    _ = (1 / 4 : ℂ) * ∫ z, h z ∂(volume : Measure ℂ) := by simp [smul_eq_mul]

/-- Fourier inversion on the complex place with the normalization of `psiC`. -/
theorem complexFourier_inversion (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    complexFourier (fun y => complexFourier (f : ℂ → ℂ) y) x = f (-x) := by
  let g : SchwartzMap ℂ ℂ :=
    (2 : ℂ) • (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ archQ) (𝓕 f)
  have hg (y : ℂ) : complexFourier (f : ℂ → ℂ) y = g y := by
    rw [archFourier_eq_standard]
    simp [g, archQ]
  have hqSym (y : ℂ) : inner ℝ y (archQ x) = inner ℝ (archQ y) x := by
    calc
      inner ℝ y (archQ x) = -(2 : ℝ) * (x * y).re := archQ_inner x y
      _ = -(2 : ℝ) * (y * x).re := by
            have hxy : (x * y).re = (y * x).re := congrArg Complex.re (mul_comm x y)
            rw [hxy]
      _ = inner ℝ x (archQ y) := (archQ_inner y x).symm
      _ = inner ℝ (archQ y) x := real_inner_comm _ _
  have hker (y : ℂ) :
      psiC (-(x * y)) =
        Complex.exp ((↑(-2 * Real.pi * inner ℝ (archQ y) x) : ℂ) * Complex.I) := by
    rw [archKernel, hqSym]
  have hfun : (fun y : ℂ => psiC (-(x * y)) * g y) =
      fun y => 2 * (Complex.exp
        ((↑(-2 * Real.pi * inner ℝ (archQ y) x) : ℂ) * Complex.I) * 𝓕 f (archQ y)) := by
    funext y
    rw [← hg y, archFourier_eq_standard, hker]
    ring
  have hfunc : (fun y => complexFourier (f : ℂ → ℂ) y) = (g : ℂ → ℂ) := funext hg
  calc
    complexFourier (fun y => complexFourier (f : ℂ → ℂ) y) x =
        complexFourier (g : ℂ → ℂ) x := by
      rw [hfunc]
    _ = 2 *
        ∫ y, psiC (-(x * y)) * g y ∂(volume : Measure ℂ) := by
          unfold complexFourier complexSelfDualHaar
          rw [integral_smul_measure]
          simp [ENNReal.toReal_ofReal, smul_eq_mul]
    _ = 4 * ∫ y, Complex.exp
          ((↑(-2 * Real.pi * inner ℝ (archQ y) x) : ℂ) * Complex.I) *
            𝓕 f (archQ y) ∂(volume : Measure ℂ) := by rw [hfun, integral_const_mul]; ring
    _ = 4 * ((1 / 4 : ℂ) *
          ∫ z, Complex.exp ((↑(-2 * Real.pi * inner ℝ z x) : ℂ) * Complex.I) *
            𝓕 f z ∂(volume : Measure ℂ)) := by
          congr 2
          exact integral_archQ (fun z =>
            Complex.exp ((↑(-2 * Real.pi * inner ℝ z x) : ℂ) * Complex.I) * 𝓕 f z)
    _ = ∫ z, Complex.exp ((↑(-2 * Real.pi * inner ℝ z x) : ℂ) * Complex.I) *
          𝓕 f z ∂(volume : Measure ℂ) := by ring
    _ = 𝓕 ((𝓕 f : SchwartzMap ℂ ℂ) : ℂ → ℂ) x := by
          have hFT2 : 𝓕 ((𝓕 f : SchwartzMap ℂ ℂ) : ℂ → ℂ) x =
              ∫ z, Complex.exp ((↑(-2 * Real.pi * inner ℝ z x) : ℂ) * Complex.I) *
                𝓕 f z ∂(volume : Measure ℂ) := by
            rw [Real.fourier_eq']
            simp [smul_eq_mul]
          exact hFT2.symm
    _ = 𝓕 (𝓕 f) x := by simpa only [SchwartzMap.fourier_coe]
    _ = f (-x) := by
          have hInv : 𝓕⁻ (𝓕 f) = f := FourierTransform.fourierInv_fourier_eq f
          have hInvx := congrArg (fun g : SchwartzMap ℂ ℂ => g (-x)) hInv
          rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe,
            Real.fourierInv_eq_fourier_neg] at hInvx
          simpa only [SchwartzMap.fourier_coe, neg_neg] using hInvx

private abbrev archV (ι : Type*) := PiLp 2 (fun _ : ι => ℂ)

private noncomputable def archNegConjPi (ι : Type*) [Fintype ι] :
    archV ι ≃ₗᵢ[ℝ] archV ι :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => archNegConj)

private noncomputable def archQPi (ι : Type*) [Fintype ι] :
    archV ι ≃L[ℝ] archV ι :=
  (archNegConjPi ι).toContinuousLinearEquiv.trans
    (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) (by norm_num)))

private theorem archQPi_apply {ι : Type*} [Fintype ι]
    (x : archV ι) (i : ι) : archQPi ι x i = archQ (x i) := by
  simp [archQPi, archNegConjPi, archQ]

private def archScale (ι : Type*) [Fintype ι] : ℝ := (2 : ℝ) ^ Fintype.card ι

private noncomputable def archPiEuclideanHaar (ι : Type*) [Fintype ι] : Measure (archV ι) :=
  ENNReal.ofReal (archScale ι) • (volume : Measure (archV ι))

private noncomputable def archPiChar {ι : Type*} [Fintype ι]
    (x y : ι → ℂ) : ℂ := ∏ i, psiC (-(x i * y i))

private noncomputable def archPiFourierV {ι : Type*} [Fintype ι]
    (f : archV ι → ℂ) (x : archV ι) : ℂ :=
  ∫ y, archPiChar (fun i => x i) (fun i => y i) * f y ∂archPiEuclideanHaar ι

private theorem archQPi_inner {ι : Type*} [Fintype ι]
    (x y : archV ι) :
    inner ℝ y (archQPi ι x) = -(2 : ℝ) * ∑ i, (x i * y i).re := by
  rw [PiLp.inner_apply]
  simp_rw [archQPi_apply]
  calc
    ∑ i, inner ℝ (y i) (archQ (x i)) =
        ∑ i, -(2 : ℝ) * (x i * y i).re := by
          apply Finset.sum_congr rfl
          intro i hi
          exact archQ_inner (x i) (y i)
    _ = -(2 : ℝ) * ∑ i, (x i * y i).re := by rw [Finset.mul_sum]

private theorem archPiKernel {ι : Type*} [Fintype ι]
    (x y : archV ι) :
    archPiChar (fun i => x i) (fun i => y i) =
      Complex.exp ((↑(-2 * Real.pi * inner ℝ y (archQPi ι x)) : ℂ) * Complex.I) := by
  unfold archPiChar
  calc
    ∏ i, psiC (-(x i * y i)) =
        ∏ i, Complex.exp
          ((↑(-2 * Real.pi * inner ℝ (y i) (archQ (x i)) : ℝ) : ℂ) * Complex.I) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact archKernel (x i) (y i)
    _ = Complex.exp (∑ i,
          (↑(-2 * Real.pi * inner ℝ (y i) (archQ (x i)) : ℝ) : ℂ) * Complex.I) := by
            rw [← Complex.exp_sum]
    _ = Complex.exp ((↑(-2 * Real.pi * inner ℝ y (archQPi ι x)) : ℂ) * Complex.I) := by
            congr 1
            rw [archQPi_inner]
            simp_rw [archQ_inner]
            push_cast
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
            rw [Finset.sum_mul]

private theorem archV_finrank (ι : Type*) [Fintype ι] :
    Module.finrank ℝ (archV ι) = 2 * Fintype.card ι := by
  change Module.finrank ℝ (PiLp 2 (fun _ : ι => ℂ)) = _
  calc
    Module.finrank ℝ (PiLp 2 (fun _ : ι => ℂ)) = Module.finrank ℝ (ι → ℂ) :=
      (WithLp.linearEquiv 2 ℝ (ι → ℂ)).finrank_eq
    _ = ∑ i, Module.finrank ℝ ℂ :=
      Module.finrank_pi_fintype ℝ (M := fun _ : ι => ℂ)
    _ = 2 * Fintype.card ι := by simp [Complex.finrank_real_complex]; ring

private theorem archScale_sq (ι : Type*) [Fintype ι] :
    archScale ι ^ 2 = (2 : ℝ) ^ Module.finrank ℝ (archV ι) := by
  rw [archV_finrank]
  simp [archScale, pow_mul, Nat.mul_comm]

private theorem archPiFourierV_eq_standard {ι : Type*} [Fintype ι]
    (f : SchwartzMap (archV ι) ℂ) (x : archV ι) :
    archPiFourierV (f : archV ι → ℂ) x =
      (archScale ι : ℂ) * 𝓕 f (archQPi ι x) := by
  unfold archPiFourierV archPiEuclideanHaar
  rw [integral_smul_measure]
  have hfun : (fun y => archPiChar (fun i => x i) (fun i => y i) * f y) =
      fun y => Complex.exp
        ((↑(-2 * Real.pi * inner ℝ y (archQPi ι x)) : ℂ) * Complex.I) * f y := by
    funext y
    rw [archPiKernel]
  rw [hfun]
  calc
    (ENNReal.ofReal (archScale ι)).toReal •
        ∫ y, Complex.exp ((↑(-2 * Real.pi * inner ℝ y (archQPi ι x)) : ℂ) * Complex.I) *
          f y ∂(volume : Measure (archV ι)) =
        (archScale ι : ℂ) * ∫ y, Complex.exp
          ((↑(-2 * Real.pi * inner ℝ y (archQPi ι x)) : ℂ) * Complex.I) * f y
          ∂(volume : Measure (archV ι)) := by
            have hscale : 0 ≤ archScale ι := by
              change 0 ≤ (2 : ℝ) ^ Fintype.card ι
              positivity
            simp [ENNReal.toReal_ofReal, hscale, smul_eq_mul]
    _ = (archScale ι : ℂ) * 𝓕 (f : archV ι → ℂ) (archQPi ι x) := by
          rw [Real.fourier_eq']
          simp [smul_eq_mul]
    _ = (archScale ι : ℂ) * 𝓕 f (archQPi ι x) := by rfl

private theorem integral_archQPi {ι : Type*} [Fintype ι] (h : archV ι → ℂ) :
    ∫ y, h (archQPi ι y) ∂(volume : Measure (archV ι)) =
      |((2 : ℝ) ^ Module.finrank ℝ (archV ι))⁻¹| •
        ∫ z, h z ∂(volume : Measure (archV ι)) := by
  let U := archNegConjPi ι
  let h' : archV ι → ℂ := fun z => h ((2 : ℝ) • z)
  have hU : ∫ y, h' (U y) ∂(volume : Measure (archV ι)) =
      ∫ z, h' z ∂(volume : Measure (archV ι)) := MeasureTheory.integral_comp U h'
  calc
    ∫ y, h (archQPi ι y) ∂(volume : Measure (archV ι)) =
        ∫ y, h' (U y) ∂(volume : Measure (archV ι)) := by
          simp [h', archQPi, U]
    _ = ∫ z, h' z ∂(volume : Measure (archV ι)) := hU
    _ = |((2 : ℝ) ^ Module.finrank ℝ (archV ι))⁻¹| •
          ∫ z, h z ∂(volume : Measure (archV ι)) := by
            rw [MeasureTheory.Measure.integral_comp_smul (volume : Measure (archV ι)) h 2]

private theorem archPiScale_cancel {ι : Type*} [Fintype ι] :
    (archScale ι : ℂ) ^ 2 *
      (|((2 : ℝ) ^ Module.finrank ℝ (archV ι))⁻¹| : ℝ) = 1 := by
  have hscale : (archScale ι : ℂ) ^ 2 =
      ((2 : ℝ) ^ Module.finrank ℝ (archV ι) : ℂ) := by exact_mod_cast archScale_sq ι
  rw [hscale]
  have hpos : 0 < (2 : ℝ) ^ Module.finrank ℝ (archV ι) := by positivity
  rw [abs_of_pos (inv_pos.mpr hpos)]
  push_cast
  field_simp

/-- Fourier inversion for the finite product of complex places, with the product of the local
self-dual measures. -/
private theorem archPiFourierV_inversion {ι : Type*} [Fintype ι]
    (f : SchwartzMap (archV ι) ℂ) (x : archV ι) :
    archPiFourierV (fun y => archPiFourierV (f : archV ι → ℂ) y) x = f (-x) := by
  let g : SchwartzMap (archV ι) ℂ :=
    (archScale ι : ℂ) • (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archQPi ι)) (𝓕 f)
  have hg (y : archV ι) : archPiFourierV (f : archV ι → ℂ) y = g y := by
    rw [archPiFourierV_eq_standard]
    simp [g, archQPi]
  have hqSym (y : archV ι) :
      inner ℝ y (archQPi ι x) = inner ℝ (archQPi ι y) x := by
    calc
      inner ℝ y (archQPi ι x) = -(2 : ℝ) * ∑ i, (x i * y i).re := archQPi_inner x y
      _ = -(2 : ℝ) * ∑ i, (y i * x i).re := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg Complex.re (mul_comm (x i) (y i))
      _ = inner ℝ x (archQPi ι y) := (archQPi_inner y x).symm
      _ = inner ℝ (archQPi ι y) x := real_inner_comm _ _
  have hker (y : archV ι) :
      archPiChar (fun i => x i) (fun i => y i) =
        Complex.exp ((↑(-2 * Real.pi * inner ℝ (archQPi ι y) x) : ℂ) * Complex.I) := by
    rw [archPiKernel, hqSym]
  have hfun : (fun y => archPiChar (fun i => x i) (fun i => y i) * g y) =
      fun y => (archScale ι : ℂ) * (Complex.exp
        ((↑(-2 * Real.pi * inner ℝ (archQPi ι y) x) : ℂ) * Complex.I) *
          𝓕 f (archQPi ι y)) := by
    funext y
    rw [← hg y, archPiFourierV_eq_standard, hker]
    ring
  have hfunc : (fun y => archPiFourierV (f : archV ι → ℂ) y) = (g : archV ι → ℂ) :=
    funext hg
  have hFT2 : 𝓕 ((𝓕 f : SchwartzMap (archV ι) ℂ) : archV ι → ℂ) x =
      ∫ z, Complex.exp ((↑(-2 * Real.pi * inner ℝ z x) : ℂ) * Complex.I) *
        𝓕 f z ∂(volume : Measure (archV ι)) := by
    rw [Real.fourier_eq']
    simp [smul_eq_mul]
  let H : archV ι → ℂ := fun z =>
    Complex.exp ((↑(-2 * Real.pi * inner ℝ z x) : ℂ) * Complex.I) * 𝓕 f z
  have hchange := integral_archQPi H
  calc
    archPiFourierV (fun y => archPiFourierV (f : archV ι → ℂ) y) x =
        archPiFourierV (g : archV ι → ℂ) x := by rw [hfunc]
    _ = (archScale ι : ℂ) *
          ∫ y, archPiChar (fun i => x i) (fun i => y i) * g y
            ∂(volume : Measure (archV ι)) := by
              unfold archPiFourierV archPiEuclideanHaar
              rw [integral_smul_measure]
              have hscale : 0 ≤ archScale ι := by
                change 0 ≤ (2 : ℝ) ^ Fintype.card ι
                positivity
              rw [ENNReal.toReal_ofReal hscale]
              simp [smul_eq_mul]
    _ = (archScale ι : ℂ) ^ 2 *
          ∫ y, Complex.exp ((↑(-2 * Real.pi * inner ℝ (archQPi ι y) x) : ℂ) * Complex.I) *
            𝓕 f (archQPi ι y) ∂(volume : Measure (archV ι)) := by
              rw [hfun, integral_const_mul]
              ring
    _ = ∫ z, H z ∂(volume : Measure (archV ι)) := by
          change (archScale ι : ℂ) ^ 2 *
              ∫ y, H (archQPi ι y) ∂(volume : Measure (archV ι)) = _
          rw [hchange]
          calc
            _ = ((archScale ι : ℂ) ^ 2 *
                (|((2 : ℝ) ^ Module.finrank ℝ (archV ι))⁻¹| : ℝ)) *
                  ∫ z, H z ∂(volume : Measure (archV ι)) := by
                    rw [RCLike.real_smul_eq_coe_mul]
                    ac_rfl
            _ = ∫ z, H z ∂(volume : Measure (archV ι)) := by
                    rw [archPiScale_cancel]
                    simp
    _ = 𝓕 ((𝓕 f : SchwartzMap (archV ι) ℂ) : archV ι → ℂ) x := hFT2.symm
    _ = 𝓕 (𝓕 f) x :=
      (congrArg (fun g : archV ι → ℂ => g x)
        (SchwartzMap.fourier_coe (𝓕 f))).symm
    _ = f (-x) := by
          have hInv : 𝓕⁻ (𝓕 f) = f := FourierTransform.fourierInv_fourier_eq f
          have hInvx := congrArg (fun g : SchwartzMap (archV ι) ℂ => g (-x)) hInv
          rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe,
            Real.fourierInv_eq_fourier_neg] at hInvx
          rw [← SchwartzMap.fourier_coe f] at hInvx
          exact (congrArg (fun g : archV ι → ℂ => g x)
            (SchwartzMap.fourier_coe (𝓕 f))).trans (by simpa only [neg_neg] using hInvx)

private noncomputable def archToPiCLE (ι : Type*) [Fintype ι] :
    archV ι ≃L[ℝ] (ι → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℂ)

private noncomputable def archToPiMeasurableEquiv (ι : Type*) [Fintype ι] :
    archV ι ≃ᵐ (ι → ℂ) := (archToPiCLE ι).toHomeomorph.toMeasurableEquiv

/-- The product self-dual Haar measure on a finite product of complex places. -/
noncomputable def complexPiSelfDualHaar (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  Measure.map (archToPiMeasurableEquiv ι) (archPiEuclideanHaar ι)

theorem complexPiSelfDualHaar_isAddHaar {ι : Type*} [Fintype ι] :
    Measure.IsAddHaarMeasure (complexPiSelfDualHaar ι) := by
  have hscale : 0 < archScale ι := by
    change 0 < (2 : ℝ) ^ Fintype.card ι
    positivity
  have hzero : ENNReal.ofReal (archScale ι) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hscale
  have htop : ENNReal.ofReal (archScale ι) < ⊤ := ENNReal.ofReal_lt_top
  have hhaar : Measure.IsAddHaarMeasure (archPiEuclideanHaar ι) := by
    dsimp [archPiEuclideanHaar]
    exact Measure.IsAddHaarMeasure.smul (μ := (volume : Measure (archV ι))) hzero htop.ne
  letI : Measure.IsAddHaarMeasure (archPiEuclideanHaar ι) := hhaar
  exact (archToPiCLE ι).isAddHaarMeasure_map (archPiEuclideanHaar ι)

/-- Fourier transform on the product of complex places, with the product self-dual measure. -/
noncomputable def complexPiFourier {ι : Type*} [Fintype ι]
    (f : (ι → ℂ) → ℂ) (x : ι → ℂ) : ℂ :=
  ∫ y, archPiChar x y * f y ∂complexPiSelfDualHaar ι

private theorem complexPiFourier_map {ι : Type*} [Fintype ι]
    (f : (ι → ℂ) → ℂ) (x : ι → ℂ) :
    complexPiFourier f x =
      archPiFourierV (fun y => f (archToPiCLE ι y))
        ((archToPiCLE ι).symm x) := by
  unfold complexPiFourier complexPiSelfDualHaar archPiFourierV
  rw [MeasureTheory.integral_map_equiv (archToPiMeasurableEquiv ι)]
  congr 1

/-- Fourier inversion on the archimedean factor `ι → ℂ`, with the product of the local
self-dual complex measures. -/
theorem complexPiFourier_inversion {ι : Type*} [Fintype ι]
    (f : SchwartzMap (ι → ℂ) ℂ) (x : ι → ℂ) :
    complexPiFourier (fun y => complexPiFourier (f : (ι → ℂ) → ℂ) y) x = f (-x) := by
  let e := archToPiCLE ι
  let fV : SchwartzMap (archV ι) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hmap (y : ι → ℂ) :
      complexPiFourier (f : (ι → ℂ) → ℂ) y =
        archPiFourierV (fV : archV ι → ℂ) (e.symm y) := by
    rw [complexPiFourier_map]
    rfl
  have hinner (y : archV ι) :
      complexPiFourier (f : (ι → ℂ) → ℂ) (e y) =
        archPiFourierV (fV : archV ι → ℂ) y := by
    rw [hmap]
    simp [e]
  calc
    complexPiFourier (fun y => complexPiFourier (f : (ι → ℂ) → ℂ) y) x =
        archPiFourierV
          (fun y => complexPiFourier (f : (ι → ℂ) → ℂ) (e y)) (e.symm x) := by
            exact complexPiFourier_map _ _
    _ = archPiFourierV
          (fun y => archPiFourierV (fV : archV ι → ℂ) y) (e.symm x) := by
            congr 1
            funext y
            exact hinner y
    _ = fV (-e.symm x) := archPiFourierV_inversion fV (e.symm x)
    _ = f (-x) := by
      change f (e (-e.symm x)) = f (-x)
      rw [map_neg, e.apply_symm_apply]

private noncomputable def archQOnPi (ι : Type*) [Fintype ι] :
    (ι → ℂ) ≃L[ℝ] (ι → ℂ) :=
  (archToPiCLE ι).symm.trans ((archQPi ι).trans (archToPiCLE ι))

/-- The product archimedean Fourier transform represented as a Schwartz map. -/
noncomputable def complexPiFourierSchwartz {ι : Type*} [Fintype ι]
    (f : SchwartzMap (ι → ℂ) ℂ) : SchwartzMap (ι → ℂ) ℂ := by
  let fV : SchwartzMap (archV ι) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archToPiCLE ι) f
  let fHatW : SchwartzMap (ι → ℂ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archToPiCLE ι).symm (𝓕 fV)
  exact (archScale ι : ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archQOnPi ι)) fHatW

/-- The integral archimedean product transform agrees with its Schwartz representative. -/
theorem complexPiFourier_eq_schwartz {ι : Type*} [Fintype ι]
    (f : SchwartzMap (ι → ℂ) ℂ) (x : ι → ℂ) :
    complexPiFourier (f : (ι → ℂ) → ℂ) x = complexPiFourierSchwartz f x := by
  rw [complexPiFourier_map]
  let e := archToPiCLE ι
  let fV : SchwartzMap (archV ι) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hFT := archPiFourierV_eq_standard fV (e.symm x)
  change archPiFourierV (fV : archV ι → ℂ) (e.symm x) = _
  rw [hFT]
  simp [complexPiFourierSchwartz, archQOnPi, fV, e, archToPiCLE]

end ArtinPrimitiveRoots.Proofs.a2_zf_top
