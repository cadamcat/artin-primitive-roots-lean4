import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs

set_option autoImplicit false

open NumberField
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private def thetaRootDerivativeStep (P : CoverPackage D S H A)
    (m : InfinitePlace F → ℤ) (w : InfinitePlace F)
    (Ψ : P.tc.G → ℂ) : P.tc.G → ℂ := fun g =>
  fderiv ℝ (fun z : ℂ => Ψ (g * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 1 -
    (m w : ℂ) * Complex.I *
      fderiv ℝ (fun z : ℂ => Ψ (g * P.tc.nS
        (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 Complex.I

private theorem thetaRootDerivativeStep_left_invariant (P : CoverPackage D S H A)
    (m : InfinitePlace F → ℤ) (w : InfinitePlace F) (Ψ : P.tc.G → ℂ)
    (k : P.tc.G) (hΨ : ∀ g, Ψ (k * g) = Ψ g) :
    ∀ g, thetaRootDerivativeStep P m w Ψ (k * g) =
      thetaRootDerivativeStep P m w Ψ g := by
  intro g
  unfold thetaRootDerivativeStep
  have h : (fun z : ℂ => Ψ (k * g * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) =
      fun z => Ψ (g * P.tc.nS
        (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))) := by
    funext z
    simpa [mul_assoc] using hΨ (g * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))
  rw [h]

private theorem thetaRootDerivativeStep_right_invariant (P : CoverPackage D S H A)
    (m : InfinitePlace F → ℤ) (w : InfinitePlace F) (Ψ : P.tc.G → ℂ)
    (k : P.tc.G) (hΨ : ∀ g, Ψ (g * k) = Ψ g)
    (hcomm : ∀ z : ℂ, k * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) =
      P.tc.nS (Multiplicative.ofAdd
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) * k) :
    ∀ g, thetaRootDerivativeStep P m w Ψ (g * k) =
      thetaRootDerivativeStep P m w Ψ g := by
  intro g
  unfold thetaRootDerivativeStep
  have h : (fun z : ℂ => Ψ (g * k * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) =
      fun z => Ψ (g * P.tc.nS
        (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))) := by
    funext z
    rw [mul_assoc, hcomm, ← mul_assoc]
    exact hΨ _
  rw [h]

private theorem listFold_left_invariant (P : CoverPackage D S H A)
    (m : InfinitePlace F → ℤ) (ws : List (InfinitePlace F)) (Ψ : P.tc.G → ℂ)
    (k : P.tc.G) (hΨ : ∀ g, Ψ (k * g) = Ψ g) :
    ∀ g, List.foldr (fun w acc => thetaRootDerivativeStep P m w acc) Ψ ws (k * g) =
      List.foldr (fun w acc => thetaRootDerivativeStep P m w acc) Ψ ws g := by
  induction ws with
  | nil => simpa
  | cons w ws ih =>
    simpa only [List.foldr_cons] using
      thetaRootDerivativeStep_left_invariant P m w
        (List.foldr (fun w acc => thetaRootDerivativeStep P m w acc) Ψ ws) k
        ih

private theorem listFold_right_invariant (P : CoverPackage D S H A)
    (m : InfinitePlace F → ℤ) (ws : List (InfinitePlace F)) (Ψ : P.tc.G → ℂ)
    (k : P.tc.G) (hΨ : ∀ g, Ψ (g * k) = Ψ g)
    (hcomm : ∀ w (z : ℂ), k * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) =
      P.tc.nS (Multiplicative.ofAdd
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) * k) :
    ∀ g, List.foldr (fun w acc => thetaRootDerivativeStep P m w acc) Ψ ws (g * k) =
      List.foldr (fun w acc => thetaRootDerivativeStep P m w acc) Ψ ws g := by
  induction ws with
  | nil => simpa
  | cons w ws ih =>
    simpa only [List.foldr_cons] using
      thetaRootDerivativeStep_right_invariant P m w
        (List.foldr (fun w acc => thetaRootDerivativeStep P m w acc) Ψ ws) k
        ih (hcomm w)

theorem thetaFamilyDeriv_left_invariant (P : CoverPackage D S H A)
    (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ) (k : P.tc.G)
    (hΨ : ∀ g, Ψ (k * g) = Ψ g) :
    ∀ g, thetaFamilyDeriv P m Ψ (k * g) = thetaFamilyDeriv P m Ψ g := by
  change ∀ g, List.foldr (fun w acc => thetaRootDerivativeStep P m w acc) Ψ
    (Finset.univ.toList) (k * g) =
      List.foldr (fun w acc => thetaRootDerivativeStep P m w acc) Ψ
        (Finset.univ.toList) g
  exact listFold_left_invariant P m (Finset.univ.toList) Ψ k hΨ

theorem thetaFamilyDeriv_right_invariant (P : CoverPackage D S H A)
    (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ) (k : P.tc.G)
    (hΨ : ∀ g, Ψ (g * k) = Ψ g)
    (hcomm : ∀ w (z : ℂ), k * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) =
      P.tc.nS (Multiplicative.ofAdd
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) * k) :
    ∀ g, thetaFamilyDeriv P m Ψ (g * k) = thetaFamilyDeriv P m Ψ g := by
  change ∀ g, List.foldr (fun w acc => thetaRootDerivativeStep P m w acc) Ψ
    (Finset.univ.toList) (g * k) =
      List.foldr (fun w acc => thetaRootDerivativeStep P m w acc) Ψ
        (Finset.univ.toList) g
  exact listFold_right_invariant P m (Finset.univ.toList) Ψ k hΨ hcomm

end ArtinPrimitiveRoots.A1.Theta
