import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.sectionSpace_family_spanning
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.analyticFamily_add_smul

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

/-- Take simple Laurent residues of finitely many section-coordinate coefficient functions.
This constructs a multilinear section functional with local psi-equivariance and separates the
complex spherical Jacquet factors by analytic continuation, including their zeros.
Guide: sol-thin-thglobal/PROOFS.md:1007–1030.
Uses: sectionSpace_family_spanning, analyticFamily_add_smul, whittakerE_multilinear,
ThetaResidueLaws.fourierCoeff, ThetaResidueLaws.linearTranslate, ContinuedEis.laurent_torus.
Feeds: thetaWhit_multilinear via thetaWhit_jacquet_factorization. -/
theorem thetaWhit_section_multilinear (Fam : AnalyticFamily P G μ) (x0 : P.RP)
    (laws : ThetaResidueLaws P G μ) :
    ∃ W : MultilinearMap ℂ
        (fun v : S.Sf => sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) ℂ,
      (∀ (v : S.Sf) (f : ∀ w : S.Sf, sectionSpace (P.loc w.1) (G.T w.1) (1 / 6))
        (t : v.1.adicCompletion F),
        W (Function.update f v (sectionRtr (P.loc v.1) (G.T v.1) (1 / 6)
          ((P.loc v.1).n (Multiplicative.ofAdd t)) (f v))) = A.ψ v.1 t * W f) ∧
      ∀ (Fam' : AnalyticFamily P G μ) (C' : ContinuedEis Fam') (x : P.RP),
        Fam'.T0 = Fam.T0 →
        (∀ s v, v ∉ S.Sf → (Fam'.sec s).f v = (Fam.sec s).f v) →
        (∀ v, v ∉ S.Sf → P.compF v x = P.compF v x0) →
        thetaWhit C' (P.q x) = W (familySectionCoords Fam' x) *
          ∏ w, jacquetC (rtr (P.compC w x) (sphC (1 / 6))) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
