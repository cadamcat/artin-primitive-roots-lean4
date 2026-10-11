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

private def thetaWSRootStep {P : CoverPackage D S H A} (w : InfinitePlace F) (m : ℤ)
    (Ψ : P.tc.G → ℂ) : P.tc.G → ℂ := fun g =>
  fderiv ℝ (fun z : ℂ => Ψ (g * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 1 -
    (m : ℂ) * Complex.I *
      fderiv ℝ (fun z : ℂ => Ψ (g * P.tc.nS
        (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 Complex.I

private theorem thetaWSRootStep_left_scalar {P : CoverPackage D S H A}
    (w : InfinitePlace F) (m : ℤ) (Ψ : P.tc.G → ℂ) (a : P.tc.G) (c : ℂ)
    (hc : c ≠ 0) (hΨ : ∀ g, Ψ (a * g) = c * Ψ g) (g : P.tc.G) :
    thetaWSRootStep w m Ψ (a * g) = c * thetaWSRootStep w m Ψ g := by
  let Φ : ℂ → ℂ := fun z => Ψ (g * P.tc.nS
    (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))
  let cUnit : ℂˣ := Units.mk0 c hc
  let cEquiv : ℂ ≃L[ℝ] ℂ := (cUnit.mulLeftLinearEquiv ℝ ℂ).toContinuousLinearEquiv
  have hcEquiv (z : ℂ) : cEquiv z = c * z := by
    simp [cEquiv, cUnit, Units.mulLeftLinearEquiv_apply]
  have hcurve :
      (fun z : ℂ => Ψ (a * g * P.tc.nS
        (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) =
      (fun z : ℂ => cEquiv (Φ z)) := by
    funext z
    calc
      Ψ (a * g * P.tc.nS (Multiplicative.ofAdd
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))) = c * Φ z := by
            simpa [mul_assoc, Φ] using hΨ (g * P.tc.nS
              (Multiplicative.ofAdd
                ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))
      _ = cEquiv (Φ z) := (hcEquiv (Φ z)).symm
  have h₁ : fderiv ℝ (fun z : ℂ => cEquiv (Φ z)) 0 1 = c * fderiv ℝ Φ 0 1 := by
    have h := cEquiv.comp_fderiv (f := Φ) (x := 0)
    have h' := congrArg (fun T : ℂ →L[ℝ] ℂ => T 1) h
    change fderiv ℝ (cEquiv ∘ Φ) 0 1 = _
    exact h'
  have hᵢ : fderiv ℝ (fun z : ℂ => cEquiv (Φ z)) 0 Complex.I =
      c * fderiv ℝ Φ 0 Complex.I := by
    have h := cEquiv.comp_fderiv (f := Φ) (x := 0)
    have h' := congrArg (fun T : ℂ →L[ℝ] ℂ => T Complex.I) h
    change fderiv ℝ (cEquiv ∘ Φ) 0 Complex.I = _
    exact h'
  change fderiv ℝ (fun z : ℂ => Ψ (a * g * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 1 -
      (m : ℂ) * Complex.I *
        fderiv ℝ (fun z : ℂ => Ψ (a * g * P.tc.nS
          (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 Complex.I = _
  rw [hcurve]
  rw [h₁, hᵢ]
  dsimp [thetaWSRootStep, Φ]
  ring

private theorem thetaFamilyDeriv_left_scalar {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ) (a : P.tc.G) (c : ℂ)
    (hc : c ≠ 0) (hΨ : ∀ g, Ψ (a * g) = c * Ψ g) :
    ∀ g, thetaFamilyDeriv P m Ψ (a * g) = c * thetaFamilyDeriv P m Ψ g := by
  classical
  have hfold (ws : List (InfinitePlace F)) :
      ∀ g, ws.foldr (fun w acc => thetaWSRootStep w (m w) acc) Ψ (a * g) =
        c * ws.foldr (fun w acc => thetaWSRootStep w (m w) acc) Ψ g := by
    induction ws with
    | nil => intro g; exact hΨ g
    | cons w ws ih =>
        intro g
        exact thetaWSRootStep_left_scalar w (m w)
          (ws.foldr (fun w acc => thetaWSRootStep w (m w) acc) Ψ) a c hc
          (fun g => ih g) g
  intro g
  change (((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaWSRootStep w (m w) acc) Ψ) (a * g) =
    c * (((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaWSRootStep w (m w) acc) Ψ) g
  exact hfold (Finset.univ : Finset (InfinitePlace F)).toList g

/-- Retain S-unipotent equivariance and genuineness of the normalized derivative Whittaker coefficient.
Uses thetaWhit_equiv, thetaFamilyDeriv and differentiation of scalar multiples. -/
theorem theta_WS_fields {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (L : SChar S) (hL : L ∈ 𝓛) :
    (∀ x g, thetaFamilyW B L (P.tc.nS (Multiplicative.ofAdd x) * g) = S.e A x * thetaFamilyW B L g) ∧
    (∀ ζ g, thetaFamilyW B L (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaFamilyW B L g) := by
  obtain ⟨hZ, hN, _⟩ := thetaWhit_equiv B.Fam B.C
  refine ⟨?_, ?_⟩
  · intro x g
    have heA : S.e A x ≠ 0 := by
      unfold SData.e
      apply mul_ne_zero
      · apply Finset.prod_ne_zero_iff.mpr
        intro v hv
        exact (A.ψ v.1).val_isUnit (x.1 v) |>.ne_zero
      · apply Finset.prod_ne_zero_iff.mpr
        intro w hw
        exact Complex.exp_ne_zero _
    have h := thetaFamilyDeriv_left_scalar L.m (thetaWhit B.C)
      (P.tc.nS (Multiplicative.ofAdd x)) (S.e A x) heA (fun h => hN x h) g
    change (thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m (thetaWhit B.C)
          (P.tc.nS (Multiplicative.ofAdd x) * g) =
      S.e A x * ((thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m (thetaWhit B.C) g)
    rw [h]
    ring
  · intro ζ g
    have hc : ((ζ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have h := thetaFamilyDeriv_left_scalar L.m (thetaWhit B.C)
      (P.tc.z ζ) ((ζ : ℂˣ) : ℂ) hc (fun h => hZ ζ h) g
    change (thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m (thetaWhit B.C) (P.tc.z ζ * g) =
      ((ζ : ℂˣ) : ℂ) * ((thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m (thetaWhit B.C) g)
    rw [h]
    ring
end ArtinPrimitiveRoots.A1.Theta
