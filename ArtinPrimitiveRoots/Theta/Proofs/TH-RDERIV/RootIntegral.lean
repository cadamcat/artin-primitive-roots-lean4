import ArtinPrimitiveRoots.Theta.Proofs.«TH-RDERIV».BoundedIntegralDerivative
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_translation_regular_fields
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

open NumberField IsDedekindDomain Module MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private def rootSingleL (w : InfinitePlace F) :
    ℂ →L[ℝ] (InfinitePlace F → ℂ) :=
  ContinuousLinearMap.pi fun v => if v = w then ContinuousLinearMap.id ℝ ℂ else 0

omit [NumberField F] in
private theorem rootSingleL_apply (w : InfinitePlace F) (z : ℂ) :
    rootSingleL w z = Pi.single w z := by
  classical
  funext v
  change (ContinuousLinearMap.pi (fun v : InfinitePlace F =>
    if v = w then ContinuousLinearMap.id ℝ ℂ else 0)) z v =
      (Pi.single w z : InfinitePlace F → ℂ) v
  rw [ContinuousLinearMap.pi_apply]
  by_cases hv : v = w <;> simp [Pi.single, hv]

private theorem root_joint_smooth {P : CoverPackage D S H A}
    (w : InfinitePlace F) (Ψ : P.tc.G → ℂ) (hΨ : JointRootSmooth P Ψ) (g : P.tc.G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (InfinitePlace F → ℂ) × ℂ =>
        Ψ (nInf P p.1 * g * nInf P (Pi.single w p.2))) := by
  have hparam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (InfinitePlace F → ℂ) × ℂ => (p.1, rootSingleL w p.2)) :=
    contDiff_fst.prodMk ((rootSingleL w).contDiff.comp contDiff_snd)
  have h := (hΨ g).comp hparam
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : (InfinitePlace F → ℂ) × ℂ =>
      Ψ (nInf P p.1 * g * nInf P (rootSingleL w p.2))) at h
  simpa only [rootSingleL_apply] using h

private theorem psiInf_smooth (ν : F) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiInf ν) := by
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psiC := by
    unfold psiC
    have hre : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℂ => (z.re : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff
    exact Complex.contDiff_exp.comp ((contDiff_const.mul hre).neg)
  unfold psiInf
  apply contDiff_prod
  intro w hw
  exact hψ.comp (contDiff_const.mul
    (ContinuousLinearMap.proj w : (InfinitePlace F → ℂ) →L[ℝ] ℂ).contDiff)

theorem root_step_torusCoeff (P : CoverPackage D S H A)
    (w : InfinitePlace F) (m : ℤ) (Ψ : P.tc.G → ℂ)
    (hΨ : JointRootSmooth P Ψ)
    (g : P.tc.G) (Pd : Set (InfinitePlace F → ℂ)) (ν : F)
    (hb : Bornology.IsBounded Pd) (hm : MeasurableSet Pd) :
    torusCoeff P (thetaRootStep w m Ψ) g Pd ν =
      thetaRootStep w m (fun h => torusCoeff P Ψ h Pd ν) g := by
  classical
  let E := InfinitePlace F → ℂ
  let χ : E → ℂ := psiInf (-ν)
  let Φ : E × ℂ → ℂ := fun p => Ψ (nInf P p.1 * g * nInf P (Pi.single w p.2))
  have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ :=
    root_joint_smooth w Ψ hΨ g
  let f : E × ℂ → ℂ := fun p => Φ p * χ p.1
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
    hΦ.mul ((psiInf_smooth (-ν)).comp contDiff_fst)
  obtain ⟨hDInt, hD⟩ := bounded_integral_hasFDerivAt volume f hf Pd hb hm
  let κ : ℂ := (((volume Pd).toReal)⁻¹ : ℝ)
  let DF : E → ℂ →L[ℝ] ℂ := fun x => fderiv ℝ (fun z : ℂ => f (x, z)) 0
  let DΦ : E → ℂ →L[ℝ] ℂ := fun x => fderiv ℝ (fun z : ℂ => Φ (x, z)) 0
  have hDFInt : Integrable DF (volume.restrict Pd) := hDInt
  have hΦDiff (x : E) : DifferentiableAt ℝ (fun z : ℂ => Φ (x, z)) 0 :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) 0
  have hProduct (x : E) (a : ℂ) : DF x a = DΦ x a * χ x := by
    dsimp only [DF, DΦ, f]
    rw [fderiv_mul_const (hΦDiff x) (χ x)]
    simp only [smul_apply, smul_eq_mul]
    exact mul_comm _ _
  have hIntegrand (x : E) :
      thetaRootStep w m Ψ (nInf P x * g) * psiInf (-ν) x =
        DF x 1 - (m : ℂ) * Complex.I * DF x Complex.I := by
    change (DΦ x 1 - (m : ℂ) * Complex.I * DΦ x Complex.I) * χ x = _
    rw [hProduct x 1, hProduct x Complex.I]
    ring
  have hLeft : torusCoeff P (thetaRootStep w m Ψ) g Pd ν =
      κ * ∫ x in Pd, DF x 1 - (m : ℂ) * Complex.I * DF x Complex.I := by
    change κ * (∫ x in Pd, thetaRootStep w m Ψ (nInf P x * g) * psiInf (-ν) x) = _
    congr 1
    exact integral_congr_ae (Eventually.of_forall hIntegrand)
  have hCurve :
      (fun z : ℂ => torusCoeff P Ψ (g * nInf P (Pi.single w z)) Pd ν) =
        (fun z : ℂ => κ * ∫ x in Pd, f (x, z)) := by
    funext z
    simp only [torusCoeff, κ, f, Φ, χ, mul_assoc]
  have hRight : thetaRootStep w m (fun h => torusCoeff P Ψ h Pd ν) g =
      κ * (∫ x in Pd, DF x) 1 -
        (m : ℂ) * Complex.I * (κ * (∫ x in Pd, DF x) Complex.I) := by
    change fderiv ℝ
        (fun z : ℂ => torusCoeff P Ψ (g * nInf P (Pi.single w z)) Pd ν) 0 1 -
      (m : ℂ) * Complex.I * fderiv ℝ
        (fun z : ℂ => torusCoeff P Ψ (g * nInf P (Pi.single w z)) Pd ν) 0 Complex.I = _
    rw [hCurve, (hD.const_mul κ).fderiv]
    simp only [smul_apply, smul_eq_mul, DF] <;> rfl
  calc
    torusCoeff P (thetaRootStep w m Ψ) g Pd ν =
        κ * ∫ x in Pd, DF x 1 - (m : ℂ) * Complex.I * DF x Complex.I := hLeft
    _ = κ * (∫ x in Pd, DF x) 1 -
        (m : ℂ) * Complex.I * (κ * (∫ x in Pd, DF x) Complex.I) := by
      rw [integral_sub (hDFInt.apply_continuousLinearMap 1)
        ((hDFInt.apply_continuousLinearMap Complex.I).const_mul ((m : ℂ) * Complex.I)),
        integral_const_mul,
        ← ContinuousLinearMap.integral_apply hDFInt 1,
        ← ContinuousLinearMap.integral_apply hDFInt Complex.I]
      ring
    _ = thetaRootStep w m (fun h => torusCoeff P Ψ h Pd ν) g := hRight.symm


end ArtinPrimitiveRoots.Proofs.thsol_torusf
