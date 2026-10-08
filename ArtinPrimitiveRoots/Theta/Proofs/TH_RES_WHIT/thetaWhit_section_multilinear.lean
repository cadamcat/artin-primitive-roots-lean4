import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.sectionSpace_family_spanning
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.analyticFamily_add_smul
import ArtinPrimitiveRoots.Proofs.th_res_whit_b.SectionMatch

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
  obtain ⟨W, hW, hWvalue⟩ := thetaWhit_section_residue_form Fam x0 laws
  let xStar := sectionReferenceRP x0
  have hStar := sectionReferenceRP_spec x0
  have hAStar : complexArchFactor xStar (1 / 6) ≠ 0 :=
    complexArchFactor_ref_ne_zero xStar hStar.2.2
  let W' : MultilinearMap ℂ
      (fun v : S.Sf => sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) ℂ :=
    (complexArchFactor xStar (1 / 6))⁻¹ • W
  have hW'apply (u : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) :
      W' u = (complexArchFactor xStar (1 / 6))⁻¹ * W u := by
    simp [W', smul_eq_mul]
  refine ⟨W', ?_, ?_⟩
  · intro v u t
    have hBase := hW v u t
    calc
      W' (Function.update u v (sectionRtr (P.loc v.1) (G.T v.1) (1 / 6)
          ((P.loc v.1).n (Multiplicative.ofAdd t)) (u v))) =
          (complexArchFactor xStar (1 / 6))⁻¹ *
            W (Function.update u v (sectionRtr (P.loc v.1) (G.T v.1) (1 / 6)
              ((P.loc v.1).n (Multiplicative.ofAdd t)) (u v))) := hW'apply _
      _ = A.ψ v.1 t * W' u := by rw [hBase, hW'apply]; ring
  · intro Fam' C' x hT hOff hcomp
    obtain ⟨FamTr, hFamTrT, hFamTrOff, hFamTrCoord⟩ :=
      analyticFamily_translate_S Fam Fam' hT hOff x
    let CTr := sectionFamilyContinuation laws FamTr
    have hCoord : ∀ s (v : S.Sf),
        rtr (P.compF v.1 xStar) ((FamTr.sec s).f v.1) =
          rtr (P.compF v.1 x) ((Fam'.sec s).f v.1) := by
      intro s v
      rw [hStar.1 v, hFamTrCoord s v]
      ext y
      simp [rtr]
    let u := familySectionCoords Fam' x
    have hCan := sectionFamilyRealizer_spec Fam x0 laws u
    let FamCan := sectionFamilyRealizer Fam x0 laws u
    let CCan := sectionFamilyContinuation laws FamCan
    have hTrCoord : ∀ v : S.Sf, (FamTr.sec (1 / 6)).f v.1 = (u v).1 := by
      intro v
      simpa [u, familySectionCoords] using hFamTrCoord (1 / 6) v
    have hCanTrCoord : ∀ v : S.Sf,
        (FamCan.sec (1 / 6)).f v.1 = (FamTr.sec (1 / 6)).f v.1 := by
      intro v
      calc
        (FamCan.sec (1 / 6)).f v.1 = (u v).1 := hCan.2.1 v
        _ = (FamTr.sec (1 / 6)).f v.1 := (hTrCoord v).symm
    have hTCanTr : FamCan.T0 = FamTr.T0 := hCan.1.trans hFamTrT.symm
    have hOffCanTr : ∀ s v, v ∉ S.Sf →
        (FamCan.sec s).f v = (FamTr.sec s).f v := by
      intro s v hv
      calc
        (FamCan.sec s).f v = (Fam.sec s).f v := hCan.2.2 s v hv
        _ = (FamTr.sec s).f v := (hFamTrOff s v hv).symm
    have hThetaCanTr := thetaWhit_eq_of_section_family_realizers FamCan FamTr CCan CTr
      hTCanTr hCanTrCoord hOffCanTr (P.q xStar) laws
    have hWvalue' : W u = thetaWhit CTr (P.q xStar) := by
      calc
        W u = sectionResidueValue Fam x0 laws u := hWvalue u
        _ = thetaWhit CCan (P.q xStar) := rfl
        _ = thetaWhit CTr (P.q xStar) := hThetaCanTr
    have hCross := thetaWhit_arch_cross Fam Fam' FamTr C' CTr x x0 xStar laws
      hOff hFamTrOff hcomp hStar.2.1 hCoord
    have hCross' : thetaWhit C' (P.q x) * complexArchFactor xStar (1 / 6) =
        W u * complexArchFactor x (1 / 6) := by
      rw [← hWvalue'] at hCross
      exact hCross
    have hRatio : thetaWhit C' (P.q x) =
        (W u * complexArchFactor x (1 / 6)) / complexArchFactor xStar (1 / 6) :=
      (eq_div_iff_mul_eq hAStar).2 hCross'
    calc
      thetaWhit C' (P.q x) =
          (W u * complexArchFactor x (1 / 6)) / complexArchFactor xStar (1 / 6) := hRatio
      _ = (complexArchFactor xStar (1 / 6))⁻¹ * W u * complexArchFactor x (1 / 6) := by
        rw [div_eq_mul_inv]
        ring
      _ = W' u * complexArchFactor x (1 / 6) := by rw [hW'apply]
      _ = W' u * ∏ w, jacquetC (rtr (P.compC w x) (sphC (1 / 6))) := rfl

end ArtinPrimitiveRoots.A1.Theta
