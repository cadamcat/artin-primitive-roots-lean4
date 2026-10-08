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

/-- Export the finite tensor expansion at the Weyl translate with δ = 1/3, including the one empty tensor when S.Sf is empty.
Guide: sol-thin-thglobal/PROOFS.md:1191–1199.
Uses theta_complex_derivative_tensor, rotatedCoord_sheetHyp, sheetHypC_bessel, derivVecC_rotate and the finite-place bases. -/
theorem theta_T6_sheet_bound {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B) (L : SChar S) (hL : L ∈ 𝓛) :
    ∃ (J : ℕ) (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
      (fc : Fin J → InfinitePlace F → ℂ → ℂ),
      (∀ ℓ v, SheetHypFin v.1 (1 / 3) (ff ℓ v)) ∧
      (∀ ℓ w, SheetHypC (1 / 3) (fc ℓ w)) ∧
      ∀ y : S.FSˣ, thetaFamilyW B L (P.tc.aS y * P.tc.wS) =
        ∑ ℓ : Fin J, (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
          ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
