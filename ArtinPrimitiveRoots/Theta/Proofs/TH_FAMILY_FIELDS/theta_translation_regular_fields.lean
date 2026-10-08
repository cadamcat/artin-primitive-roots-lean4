import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private def thetaRootStep {P : CoverPackage D S H A} (w : InfinitePlace F) (m : ℤ)
    (Ψ : P.tc.G → ℂ) : P.tc.G → ℂ := fun g =>
  fderiv ℝ (fun z : ℂ => Ψ (g * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 1 -
    (m : ℂ) * Complex.I *
      fderiv ℝ (fun z : ℂ => Ψ (g * P.tc.nS
        (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 Complex.I

private theorem nInf_add {P : CoverPackage D S H A} (x y : InfinitePlace F → ℂ) :
    nInf P (x + y) = nInf P x * nInf P y := by
  have hp : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y) =
      ((0, x) : S.FS) + ((0, y) : S.FS) := by
    ext v <;> simp
  change P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y)) =
    P.tc.nS (Multiplicative.ofAdd ((0, x) : S.FS)) *
      P.tc.nS (Multiplicative.ofAdd ((0, y) : S.FS))
  rw [hp, ofAdd_add, map_mul]

private theorem thetaRootStep_jointRootSmooth {P : CoverPackage D S H A}
    (w : InfinitePlace F) (m : ℤ) (Ψ : P.tc.G → ℂ)
    (hΨ : JointRootSmooth P Ψ) : JointRootSmooth P (thetaRootStep w m Ψ) := by
  classical
  intro g
  let E := InfinitePlace F → ℂ
  let singleL : ℂ →L[ℝ] E := ContinuousLinearMap.pi fun v =>
    if v = w then ContinuousLinearMap.id ℝ ℂ else 0
  have hsingleL (z : ℂ) : singleL z = Pi.single w z := by
    funext v
    change (ContinuousLinearMap.pi (fun v : InfinitePlace F =>
      if v = w then ContinuousLinearMap.id ℝ ℂ else 0)) z v = (Pi.single w z : E) v
    rw [ContinuousLinearMap.pi_apply]
    by_cases hv : v = w <;> simp [Pi.single, hv]
  let K : ℂ →L[ℝ] (E × E) := (0 : ℂ →L[ℝ] E).prod singleL
  have hK (z : ℂ) : K z = (0, Pi.single w z) := by simp [K, hsingleL]
  let f : (E × E) → ℂ := fun p => Ψ (nInf P p.1 * g * nInf P p.2)
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := hΨ g
  have hdir (v : E × E) :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => fderiv ℝ f p v) := by
    have hdf := hf.contDiff_fderiv_apply (m := (⊤ : ℕ∞)) (by simp)
    have hparam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × E => (p, v)) :=
      contDiff_id.prodMk contDiff_const
    simpa [Function.comp_def] using hdf.comp hparam
  have hcurve (p : E × E) (z : ℂ) :
      Ψ (nInf P p.1 * g * nInf P p.2 *
        P.tc.nS (Multiplicative.ofAdd
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))) = f (p + K z) := by
    change Ψ (nInf P p.1 * g * nInf P p.2 * nInf P (Pi.single w z)) = _
    rw [mul_assoc, ← nInf_add]
    simp [f, hK, mul_assoc]
  have hcurveDeriv (p : E × E) (v : ℂ) :
      fderiv ℝ
        (fun z : ℂ => Ψ (nInf P p.1 * g * nInf P p.2 *
          P.tc.nS (Multiplicative.ofAdd
            ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 v =
        fderiv ℝ f p (K v) := by
    have hA : fderiv ℝ (fun z : ℂ => p + K z) 0 = K := by
      rw [fderiv_const_add]
      exact K.hasFDerivAt.fderiv
    have hAdiff : DifferentiableAt ℝ (fun z : ℂ => p + K z) 0 := by fun_prop
    have hfD : Differentiable ℝ f := hf.differentiable (by simp)
    calc
      _ = fderiv ℝ (fun z : ℂ => f (p + K z)) 0 v := by
        apply congrArg (fun φ : ℂ → ℂ => fderiv ℝ φ 0 v)
        funext z
        exact hcurve p z
      _ = ((fderiv ℝ f (p + K 0)).comp (fderiv ℝ (fun z : ℂ => p + K z) 0)) v := by
        change fderiv ℝ (f ∘ (fun z : ℂ => p + K z)) 0 v = _
        rw [fderiv_comp 0 (hfD (p + K 0)) hAdiff]
      _ = fderiv ℝ f p (K v) := by simp [hA]
  have hrep (p : E × E) :
      thetaRootStep w m Ψ (nInf P p.1 * g * nInf P p.2) =
        fderiv ℝ f p (0, Pi.single w 1) -
          (m : ℂ) * Complex.I * fderiv ℝ f p (0, Pi.single w Complex.I) := by
    simp only [thetaRootStep]
    rw [hcurveDeriv p 1, hcurveDeriv p Complex.I, hK 1, hK Complex.I]
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × E => thetaRootStep w m Ψ (nInf P p.1 * g * nInf P p.2)) := by
    have h₁ := hdir (0, Pi.single w 1)
    have hᵢ := hdir (0, Pi.single w Complex.I)
    rw [show (fun p : E × E => thetaRootStep w m Ψ (nInf P p.1 * g * nInf P p.2)) =
        fun p => fderiv ℝ f p (0, Pi.single w 1) -
          (m : ℂ) * Complex.I * fderiv ℝ f p (0, Pi.single w Complex.I) by
      funext p
      exact hrep p]
    exact h₁.sub (contDiff_const.mul hᵢ)
  exact hsm

theorem thetaFamilyDeriv_jointRootSmooth {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ) (hΨ : JointRootSmooth P Ψ) :
    JointRootSmooth P (thetaFamilyDeriv P m Ψ) := by
  classical
  have hfold (ws : List (InfinitePlace F)) :
      JointRootSmooth P (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) := by
    induction ws with
    | nil => exact hΨ
    | cons w ws ih =>
        exact thetaRootStep_jointRootSmooth w (m w)
          (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) ih
  change JointRootSmooth P
    (((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaRootStep w (m w) acc) Ψ)
  exact hfold (Finset.univ : Finset (InfinitePlace F)).toList

private theorem thetaFamilyDeriv_archSmooth {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ) (hΨ : JointRootSmooth P Ψ)
    (g : P.tc.G) (w : InfinitePlace F) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => thetaFamilyDeriv P m Ψ
        (g * P.tc.nS (Multiplicative.ofAdd
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) := by
  let E := InfinitePlace F → ℂ
  have hJ := thetaFamilyDeriv_jointRootSmooth m Ψ hΨ g
  let singleL : ℂ →L[ℝ] E := ContinuousLinearMap.pi fun v =>
    if v = w then ContinuousLinearMap.id ℝ ℂ else 0
  have hsingleL (z : ℂ) : singleL z = Pi.single w z := by
    funext v
    change (ContinuousLinearMap.pi (fun v : InfinitePlace F =>
      if v = w then ContinuousLinearMap.id ℝ ℂ else 0)) z v = (Pi.single w z : E) v
    rw [ContinuousLinearMap.pi_apply]
    by_cases hv : v = w <;> simp [Pi.single, hv]
  let paramL : ℂ →L[ℝ] (E × E) := (0 : ℂ →L[ℝ] E).prod singleL
  have hparam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => paramL z) := by
    fun_prop
  have h := hJ.comp hparam
  have hzero : nInf P (0 : E) = 1 := by
    change P.tc.nS (1 : Multiplicative S.FS) = 1
    exact map_one P.tc.nS
  have hval (z : ℂ) :
      nInf P (Pi.single w z) = P.tc.nS (Multiplicative.ofAdd
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) := rfl
  have hEqfun :
      (fun z : ℂ => thetaFamilyDeriv P m Ψ
        (nInf P (paramL z).1 * g * nInf P (paramL z).2)) =
      fun z => thetaFamilyDeriv P m Ψ
        (g * P.tc.nS (Multiplicative.ofAdd
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))) := by
    funext z
    simp [paramL, hzero, hval, hsingleL]
  simpa only [Function.comp_def, hEqfun] using h

/-- Retain torus continuity and both root smoothness fields through the iterated derivative of the actual common-family residue.
Guide: sol-thin-thglobal/PROOFS.md:1200–1204.
Uses ThetaCommonSections.C, ContinuedEis.jointRoots and mixed derivative estimates; the formal Rderiv_spec alone does not supply these fields. -/
theorem theta_translation_regular_fields {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛)
    (L : SChar S) (hL : L ∈ 𝓛) :
    (∀ g h, Continuous fun y : S.FSˣ => thetaFamilyTheta B L (g * P.tc.aS y * h)) ∧
    (∀ (g : P.tc.G) (w : InfinitePlace F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ =>
        thetaFamilyTheta B L (g * P.tc.nS
          (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))))) ∧
    JointRootSmooth P (thetaFamilyTheta B L) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Separate continuity and root smoothness do not control mixed derivatives in the torus parameter.
    sorry
  · intro g w
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => (thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m B.C.theta
          (g * P.tc.nS (Multiplicative.ofAdd
            ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))))
    exact contDiff_const.mul
      (thetaFamilyDeriv_archSmooth L.m B.C.theta B.C.jointRoots g w)
  · intro g
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) =>
        (thetaNormalizationScalar N)⁻¹ *
          thetaFamilyDeriv P L.m B.C.theta (nInf P p.1 * g * nInf P p.2))
    exact contDiff_const.mul
      (thetaFamilyDeriv_jointRootSmooth L.m B.C.theta B.C.jointRoots g)
end ArtinPrimitiveRoots.A1.Theta
