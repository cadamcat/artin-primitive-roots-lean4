import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_fourier_expansion
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_translation_regular_fields

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem thetaRootStep_const_mul {P : CoverPackage D S H A}
    (w : InfinitePlace F) (m : ℤ) (Ψ : P.tc.G → ℂ)
    (c : ℂ) (g : P.tc.G) :
    thetaRootStep w m (fun h => c * Ψ h) g = c * thetaRootStep w m Ψ g := by
  by_cases hc : c = 0
  · subst c
    simp [thetaRootStep]
  · let Φ : ℂ → ℂ := fun z => Ψ (g * P.tc.nS
    (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))
    let cUnit : ℂˣ := Units.mk0 c hc
    let cEquiv : ℂ ≃L[ℝ] ℂ := (cUnit.mulLeftLinearEquiv ℝ ℂ).toContinuousLinearEquiv
    have hcEquiv (z : ℂ) : cEquiv z = c * z := by
      simp [cEquiv, cUnit, Units.mulLeftLinearEquiv_apply]
    have hcurve :
        (fun z : ℂ => (fun h => c * Ψ h) (g * P.tc.nS
          (Multiplicative.ofAdd
            ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) =
        (fun z => cEquiv (Φ z)) := by
      funext z
      exact (hcEquiv (Φ z)).symm
    have h1 : fderiv ℝ (fun z : ℂ => cEquiv (Φ z)) 0 1 =
        c * fderiv ℝ Φ 0 1 := by
      have h := cEquiv.comp_fderiv (f := Φ) (x := 0)
      have h' := congrArg (fun T : ℂ →L[ℝ] ℂ => T 1) h
      change fderiv ℝ (cEquiv ∘ Φ) 0 1 = _
      exact h'
    have hI : fderiv ℝ (fun z : ℂ => cEquiv (Φ z)) 0 Complex.I =
        c * fderiv ℝ Φ 0 Complex.I := by
      have h := cEquiv.comp_fderiv (f := Φ) (x := 0)
      have h' := congrArg (fun T : ℂ →L[ℝ] ℂ => T Complex.I) h
      change fderiv ℝ (cEquiv ∘ Φ) 0 Complex.I = _
      exact h'
    change fderiv ℝ (fun z : ℂ => (fun h => c * Ψ h)
        (g * P.tc.nS (Multiplicative.ofAdd
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 1 -
      (m : ℂ) * Complex.I * fderiv ℝ (fun z : ℂ => (fun h => c * Ψ h)
        (g * P.tc.nS (Multiplicative.ofAdd
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 Complex.I = _
    rw [hcurve]
    rw [h1, hI]
    dsimp [thetaRootStep, Φ]
    ring

private theorem thetaFamilyDeriv_const_mul {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ) (c : ℂ) :
    ∀ g, thetaFamilyDeriv P m (fun h => c * Ψ h) g = c * thetaFamilyDeriv P m Ψ g := by
  classical
  have hFold (ws : List (InfinitePlace F)) :
      ∀ g, ws.foldr (fun w acc => thetaRootStep w (m w) acc) (fun h => c * Ψ h) g =
        c * ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ g := by
    induction ws with
    | nil => intro g; rfl
    | cons w ws ih =>
        intro g
        have hacc : ws.foldr (fun w acc => thetaRootStep w (m w) acc) (fun h => c * Ψ h) =
            fun h => c * ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ h := by
          funext h
          exact ih h
        change thetaRootStep w (m w)
            (ws.foldr (fun w acc => thetaRootStep w (m w) acc) (fun h => c * Ψ h)) g =
          c * thetaRootStep w (m w)
            (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) g
        rw [hacc]
        exact thetaRootStep_const_mul w (m w)
          (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) c g
  intro g
  change (((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaRootStep w (m w) acc) (fun h => c * Ψ h)) g =
    c * (((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaRootStep w (m w) acc) Ψ) g
  exact hFold (Finset.univ : Finset (InfinitePlace F)).toList g

/-- Differentiate the frozen base factorization through commuting exterior translators and preserve its exact finite and finite-support products.
Uses ThetaBaseFactorization (supplied by thetaWhit_factor), thetaFamilyDeriv and CoverPackage.comm_S. -/
theorem theta_family_factor {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (hFactor : ThetaBaseFactorization B)
    (L : SChar S) (hL : L ∈ 𝓛) (ν : Fˣ) (ε : Bool) (gS : P.tc.G)
    (hgS : gS ∈ P.tc.GS) (T : Finset (FinPlace F)) (hT : ∀ v ∈ T, v ∉ S.Sf)
    (g : FinPlace F → P.tc.G) (hg : ∀ v ∈ T, g v ∈ P.tc.Gloc v) :
    thetaFamilyW B L (P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS * (T.toList.map g).prod) =
      thetaFamilyW B L (P.tc.aS (S.diagU ν) * (if ε then P.tc.wS else 1) * gS) *
        (∏ v ∈ T, thetaExteriorWv P N.G N.μ v (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)) *
        ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T), thetaExteriorWv P N.G N.μ v (P.tc.a v (toLoc v ν)) := by
  classical
  have hlocal (v : FinPlace F) (hv : v ∈ T) (y : InfinitePlace F → ℂ) :
      g v * nInf P y = nInf P y * g v := by
    exact P.tc.comm_S v (hT v hv) (g v) (hg v hv) (nInf P y)
      (P.tc.nS_mem (Multiplicative.ofAdd
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y)))
  have hprodComm (l : List (FinPlace F)) (hl : ∀ v ∈ l, v ∈ T)
      (y : InfinitePlace F → ℂ) :
      (l.map g).prod * nInf P y = nInf P y * (l.map g).prod := by
    induction l with
    | nil => simp
    | cons v l ih =>
        have hvT : v ∈ T := hl v (by simp)
        have hlT : ∀ v' ∈ l, v' ∈ T := fun v' hv' => hl v' (by simp [hv'])
        change (g v * (l.map g).prod) * nInf P y =
          nInf P y * (g v * (l.map g).prod)
        calc
          (g v * (l.map g).prod) * nInf P y =
              g v * ((l.map g).prod * nInf P y) := by group
          _ = g v * (nInf P y * (l.map g).prod) := by rw [ih hlT]
          _ = (g v * nInf P y) * (l.map g).prod := by group
          _ = (nInf P y * g v) * (l.map g).prod := by rw [hlocal v hvT y]
          _ = nInf P y * (g v * (l.map g).prod) := by group
  let lhsBase : P.tc.G := P.tc.rat (diagGL ν) *
    (if ε then P.tc.rat weylGL else 1) * gS * (T.toList.map g).prod
  let rhsBase : P.tc.G := P.tc.aS (S.diagU ν) *
    (if ε then P.tc.wS else 1) * gS
  let extFinite : ℂ := ∏ v ∈ T,
    thetaExteriorWv P N.G N.μ v
      (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)
  let extTail : ℂ := ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T),
    thetaExteriorWv P N.G N.μ v (P.tc.a v (toLoc v ν))
  let c : ℂ := extFinite * extTail
  have hOrbit (y : InfinitePlace F → ℂ) :
      thetaWhit B.C (lhsBase * nInf P y) =
        c * thetaWhit B.C (rhsBase * nInf P y) := by
    let ny : P.tc.G := nInf P y
    have hny : ny ∈ P.tc.GS := P.tc.nS_mem (Multiplicative.ofAdd
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y))
    have hmove : lhsBase * ny = P.tc.rat (diagGL ν) *
        (if ε then P.tc.rat weylGL else 1) * (gS * ny) * (T.toList.map g).prod := by
      dsimp [lhsBase]
      calc
        _ = P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) *
            gS * ((T.toList.map g).prod * ny) := by group
        _ = P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) *
            gS * (ny * (T.toList.map g).prod) := by
              rw [hprodComm T.toList (by intro v hv; exact Finset.mem_toList.mp hv) y]
        _ = P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) *
            (gS * ny) * (T.toList.map g).prod := by group
    have hfactor := hFactor ν ε (gS * ny) (P.tc.GS.mul_mem hgS hny)
      T hT g hg
    have hR : rhsBase * ny = P.tc.aS (S.diagU ν) *
        (if ε then P.tc.wS else 1) * (gS * ny) := by
      dsimp [rhsBase]
      group
    rw [← hR] at hfactor
    calc
      thetaWhit B.C (lhsBase * ny) = thetaWhit B.C
          (P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) *
            (gS * ny) * (T.toList.map g).prod) := by rw [hmove]
      _ = thetaWhit B.C (rhsBase * ny) *
          (∏ v ∈ T, thetaExteriorWv P N.G N.μ v
            (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)) *
          ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T),
            thetaExteriorWv P N.G N.μ v (P.tc.a v (toLoc v ν)) := hfactor
      _ = (∏ v ∈ T, thetaExteriorWv P N.G N.μ v
            (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)) *
          (∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T),
            thetaExteriorWv P N.G N.μ v (P.tc.a v (toLoc v ν))) *
          thetaWhit B.C (rhsBase * ny) := by ring
  have hroot := thetaFamilyDeriv_congr_rootOrbit L.m (thetaWhit B.C)
      (fun h => c * thetaWhit B.C h) lhsBase rhsBase Set.univ isOpen_univ
      (Set.mem_univ _) (fun y _ => hOrbit y)
  have hhom := thetaFamilyDeriv_const_mul L.m (thetaWhit B.C) c rhsBase
  change (thetaNormalizationScalar N)⁻¹ *
      thetaFamilyDeriv P L.m (thetaWhit B.C) lhsBase =
    ((thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m (thetaWhit B.C) rhsBase) *
      extFinite * extTail
  calc
    _ = (thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m (fun h => c * thetaWhit B.C h) rhsBase := by rw [hroot]
    _ = (thetaNormalizationScalar N)⁻¹ *
        (c * thetaFamilyDeriv P L.m (thetaWhit B.C) rhsBase) := by rw [hhom]
    _ = ((thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m (thetaWhit B.C) rhsBase) * extFinite * extTail := by
          dsimp [c]
          ring
end ArtinPrimitiveRoots.A1.Theta
