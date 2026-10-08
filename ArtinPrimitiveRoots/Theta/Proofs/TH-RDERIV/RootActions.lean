import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_translation_regular_fields
import Mathlib.Analysis.Calculus.FDeriv.Mul

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

private theorem root_curve_smooth {P : CoverPackage D S H A}
    (w : InfinitePlace F) (Ψ : P.tc.G → ℂ) (hΨ : JointRootSmooth P Ψ) (g : P.tc.G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => Ψ (g * P.tc.nS (Multiplicative.ofAdd
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) := by
  have hn0 : nInf P 0 = 1 := by
    change P.tc.nS 1 = 1
    exact map_one _
  have hparam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => ((0 : InfinitePlace F → ℂ), rootSingleL w z)) :=
    contDiff_const.prodMk (rootSingleL w).contDiff
  have h := (hΨ g).comp hparam
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : ℂ => Ψ (nInf P 0 * g * nInf P (rootSingleL w z))) at h
  simp only [hn0, one_mul, rootSingleL_apply] at h
  simpa only [nInf] using h

private abbrev RootActions (P : CoverPackage D S H A) (Ψ : P.tc.G → ℂ) : Prop :=
  (∀ γ g, Ψ (P.tc.rat γ * g) = Ψ g) ∧
  (∀ ζ g, Ψ (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * Ψ g) ∧
  (∀ g, ∀ k ∈ P.tc.Kext, Ψ (g * k) = Ψ g)

private theorem root_step_actions {P : CoverPackage D S H A}
    (w : InfinitePlace F) (m : ℤ) (Ψ : P.tc.G → ℂ)
    (hΨ : JointRootSmooth P Ψ) (hActions : RootActions P Ψ) :
    RootActions P (thetaRootStep w m Ψ) := by
  classical
  rcases hActions with ⟨hAut, hGen, hRight⟩
  let n : ℂ → P.tc.G := fun z => P.tc.nS (Multiplicative.ofAdd
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))
  refine ⟨?_, ?_, ?_⟩
  · intro γ g
    have hcurve : (fun z : ℂ => Ψ ((P.tc.rat γ * g) * n z)) =
        (fun z => Ψ (g * n z)) := by
      funext z
      rw [mul_assoc, hAut]
    simp only [thetaRootStep]
    rw [hcurve]
  · intro ζ g
    let q : ℂ := ((ζ : ℂˣ) : ℂ)
    have hcurve : (fun z : ℂ => Ψ ((P.tc.z ζ * g) * n z)) =
        (fun z => q * Ψ (g * n z)) := by
      funext z
      rw [mul_assoc, hGen]
    have hd : DifferentiableAt ℝ (fun z : ℂ => Ψ (g * n z)) 0 :=
      (root_curve_smooth w Ψ hΨ g).differentiable (by simp) 0
    simp only [thetaRootStep]
    rw [hcurve, fderiv_const_mul hd q]
    simp only [smul_apply, smul_eq_mul]
    change q * fderiv ℝ (fun z => Ψ (g * n z)) 0 1 -
        (m : ℂ) * Complex.I * (q * fderiv ℝ (fun z => Ψ (g * n z)) 0 Complex.I) =
      q * (fderiv ℝ (fun z => Ψ (g * n z)) 0 1 -
        (m : ℂ) * Complex.I * fderiv ℝ (fun z => Ψ (g * n z)) 0 Complex.I)
    ring
  · intro g k hk
    have hcurve : (fun z : ℂ => Ψ ((g * k) * n z)) =
        (fun z => Ψ (g * n z)) := by
      funext z
      have hcomm : k * n z = n z * k :=
        P.tc.Kext_comm_S k hk (n z) (P.tc.nS_mem _)
      rw [mul_assoc, hcomm, ← mul_assoc, hRight]
      exact hk
    simp only [thetaRootStep]
    rw [hcurve]

theorem rderiv_actions (P : CoverPackage D S H A) (m : InfinitePlace F → ℤ)
    (Ψ : P.tc.G → ℂ) (hΨ : JointRootSmooth P Ψ)
    (hAut : ∀ γ g, Ψ (P.tc.rat γ * g) = Ψ g)
    (hGen : ∀ ζ g, Ψ (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * Ψ g)
    (hRight : ∀ g, ∀ k ∈ P.tc.Kext, Ψ (g * k) = Ψ g) :
    (∀ γ g, thetaFamilyDeriv P m Ψ (P.tc.rat γ * g) = thetaFamilyDeriv P m Ψ g) ∧
    (∀ ζ g, thetaFamilyDeriv P m Ψ (P.tc.z ζ * g) =
      ((ζ : ℂˣ) : ℂ) * thetaFamilyDeriv P m Ψ g) ∧
    (∀ g, ∀ k ∈ P.tc.Kext,
      thetaFamilyDeriv P m Ψ (g * k) = thetaFamilyDeriv P m Ψ g) := by
  classical
  have hfold (ws : List (InfinitePlace F)) :
      JointRootSmooth P (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) ∧
        RootActions P (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) := by
    induction ws with
    | nil => exact ⟨hΨ, hAut, hGen, hRight⟩
    | cons w ws ih =>
        exact ⟨thetaRootStep_jointRootSmooth w (m w)
          (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) ih.1,
          root_step_actions w (m w)
            (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) ih.1 ih.2⟩
  change RootActions P (((Finset.univ : Finset (InfinitePlace F)).toList).foldr
    (fun w acc => thetaRootStep w (m w) acc) Ψ)
  exact (hfold (Finset.univ : Finset (InfinitePlace F)).toList).2

end ArtinPrimitiveRoots.Proofs.thsol_torusf
