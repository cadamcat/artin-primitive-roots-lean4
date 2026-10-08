import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.sectionSpace_family_spanning
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.analyticFamily_add_smul
import ArtinPrimitiveRoots.Proofs.th_res_whit_b.IntertwineLinear
import ArtinPrimitiveRoots.Proofs.th_res_whit_b.CommonFourier

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

private abbrev LambdaGen (Fam : AnalyticFamily P G μ) (v0 : FinPlace F) :=
  {Fam' : AnalyticFamily P G μ // ExteriorFamily Fam v0 Fam'}

private def lambdaGenSection (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (i : LambdaGen Fam v0) : sectionSpace (P.loc v0) (G.T v0) (1 / 6 : ℂ) :=
  ⟨(i.1.sec (1 / 6)).f v0, (i.1.sec (1 / 6)).f_sec v0⟩

private def lambdaGenAt (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (i : LambdaGen Fam v0) (s : ℂ) : (P.loc v0).L → (G.T v0).V :=
  (i.1.sec s).f v0

private def lambdaGenCombination (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (x : LambdaGen Fam v0 →₀ ℂ) (s : ℂ) : (P.loc v0).L → (G.T v0).V :=
  Finsupp.linearCombination ℂ (fun i => lambdaGenAt Fam v0 i s) x

private def lambdaGenResidues (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (g : P.tc.G) (laws : ThetaResidueLaws P G μ) : LambdaGen Fam v0 → ℂ :=
  fun i => thetaWhit (Classical.choice (laws.continuation i.1)) g

private def lambdaResidueCombination (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (g : P.tc.G) (laws : ThetaResidueLaws P G μ) :
    (LambdaGen Fam v0 →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (lambdaGenResidues Fam v0 g laws)

private theorem lambda_exists_zero_family (Fam : AnalyticFamily P G μ) (v0 : FinPlace F) :
    ∃ Z : AnalyticFamily P G μ, ExteriorFamily Fam v0 Z ∧
      ∀ s, (Z.sec s).f v0 = 0 := by
  let φ : v0.adicCompletion F → (G.T v0).V := fun _ => 0
  have hφ : IsLocallyConstant φ := IsLocallyConstant.const 0
  have hφc : HasCompactSupport φ := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_empty
    intro x hx
    simp [φ] at hx
  rcases analyticFamily_bigCell_rtr Fam v0 φ hφ hφc 1 with ⟨Z, hZ, hcoord⟩
  refine ⟨Z, hZ, ?_⟩
  intro s
  funext x
  rw [hcoord s]
  simp [rtr, bigCell, φ]

theorem thetaWhit_zero_local_family (v0 : FinPlace F)
    (Z : AnalyticFamily P G μ) (hZ : ∀ s, (Z.sec s).f v0 = 0)
    (g : P.tc.G) (laws : ThetaResidueLaws P G μ) (C : ContinuedEis Z) :
    thetaWhit C g = 0 := by
  have hlinear := (laws.linearTranslate v0 Z Z Z C C C).1
    (fun s v hv => ⟨rfl, rfl⟩) (1 : ℂ)
    (by intro s; rw [hZ s]; simp)
  have hzero : ∀ x, C.theta x = 0 := by
    intro x
    have hpoint : C.theta x = C.theta x + C.theta x := by
      simpa using congrFun hlinear x
    have hcancel : C.theta x + 0 = C.theta x + C.theta x := by simpa using hpoint.symm
    exact (add_left_cancel hcancel).symm
  unfold thetaWhit
  split <;> simp [torusCoeff, hzero]

private def lambdaFreeToSection (Fam : AnalyticFamily P G μ) (v0 : FinPlace F) :
    (LambdaGen Fam v0 →₀ ℂ) →ₗ[ℂ] sectionSpace (P.loc v0) (G.T v0) (1 / 6 : ℂ) :=
  Finsupp.linearCombination ℂ (lambdaGenSection Fam v0)

private theorem lambda_exists_combo (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (g : P.tc.G) (laws : ThetaResidueLaws P G μ)
    (x : LambdaGen Fam v0 →₀ ℂ) :
    ∃ H' : AnalyticFamily P G μ, ∃ C' : ContinuedEis H',
      ExteriorFamily Fam v0 H' ∧
      (∀ s, (H'.sec s).f v0 = lambdaGenCombination Fam v0 x s) ∧
      thetaWhit C' g = lambdaResidueCombination Fam v0 g laws x := by
  classical
  obtain ⟨Z, hZ, hZcoord⟩ := lambda_exists_zero_family Fam v0
  let CZ : ContinuedEis Z := Classical.choice (laws.continuation Z)
  have hZres := thetaWhit_zero_local_family v0 Z hZcoord g laws CZ
  induction x using Finsupp.induction_linear with
  | zero =>
      refine ⟨Z, CZ, hZ, ?_, ?_⟩
      · exact hZcoord
      · simpa [lambdaResidueCombination] using hZres
  | single i c =>
      let Ci : ContinuedEis i.1 := Classical.choice (laws.continuation i.1)
      rcases analyticFamily_add_smul Fam v0 Z i.1 hZ i.2 c with
        ⟨H', hH, hcomb⟩
      let CH : ContinuedEis H' := Classical.choice (laws.continuation H')
      have hout : ∀ s v, v ≠ v0 →
          ((i.1.sec s).f v = (Z.sec s).f v ∧ (H'.sec s).f v = (Z.sec s).f v) := by
        intro s v hv
        exact ⟨(i.2.2 s v hv).trans (hZ.2 s v hv).symm,
          (hH.2 s v hv).trans (hZ.2 s v hv).symm⟩
      have hlin := (laws.linearTranslate v0 Z i.1 H' CZ Ci CH).1 hout c hcomb
      have hθlinear := thetaWhit_linear_common_domain Z i.1 H' CZ Ci CH g laws c hlin
      refine ⟨H', CH, hH, ?_, ?_⟩
      · intro s
        rw [hcomb s, hZcoord s]
        simp [lambdaGenCombination, lambdaGenAt, Finsupp.linearCombination_single]
      · have hpoint := congrFun hlin g
        calc
          thetaWhit CH g = thetaWhit CZ g + c • thetaWhit Ci g := hθlinear
          _ = c • lambdaGenResidues Fam v0 g laws i := by
            rw [hZres]
            simp [lambdaGenResidues, Ci]
          _ = lambdaResidueCombination Fam v0 g laws (Finsupp.single i c) := by
            simp [lambdaResidueCombination, Finsupp.linearCombination_single]
  | add x y hx hy =>
      obtain ⟨X, CX, hX, hXcoord, hXtheta⟩ := hx
      obtain ⟨Y, CY, hY, hYcoord, hYtheta⟩ := hy
      rcases analyticFamily_add_smul Fam v0 X Y hX hY (1 : ℂ) with
        ⟨H', hH, hcomb⟩
      let CH : ContinuedEis H' := Classical.choice (laws.continuation H')
      have hout : ∀ s v, v ≠ v0 →
          ((Y.sec s).f v = (X.sec s).f v ∧ (H'.sec s).f v = (X.sec s).f v) := by
        intro s v hv
        exact ⟨(hY.2 s v hv).trans (hX.2 s v hv).symm,
          (hH.2 s v hv).trans (hX.2 s v hv).symm⟩
      have hlin := (laws.linearTranslate v0 X Y H' CX CY CH).1 hout (1 : ℂ) hcomb
      have hθlinear := thetaWhit_linear_common_domain X Y H' CX CY CH g laws 1 hlin
      refine ⟨H', CH, hH, ?_, ?_⟩
      · intro s
        calc
          (H'.sec s).f v0 = (X.sec s).f v0 + (Y.sec s).f v0 := by
            rw [hcomb s]
            simp
          _ = lambdaGenCombination Fam v0 x s + lambdaGenCombination Fam v0 y s := by
            rw [hXcoord s, hYcoord s]
          _ = lambdaGenCombination Fam v0 (x + y) s := by
            symm
            exact map_add (Finsupp.linearCombination ℂ (fun i => lambdaGenAt Fam v0 i s)) x y
      · have hpoint := congrFun hlin g
        calc
          thetaWhit CH g = thetaWhit CX g + thetaWhit CY g := by simpa using hθlinear
          _ = lambdaResidueCombination Fam v0 g laws x +
              lambdaResidueCombination Fam v0 g laws y := by rw [hXtheta, hYtheta]
          _ = lambdaResidueCombination Fam v0 g laws (x + y) := by
            symm
            exact map_add (lambdaResidueCombination Fam v0 g laws) x y

/-- Every local section at s0 is realized exactly by an analytic family with the fixed exterior
sections. This is the family-valued form of `sectionSpace_family_spanning`. -/
theorem analyticFamily_realize_section (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (f : (P.loc v0).L → (G.T v0).V)
    (hf : f ∈ sectionSpace (P.loc v0) (G.T v0) (1 / 6))
    (g : P.tc.G) (laws : ThetaResidueLaws P G μ) :
    ∃ H' : AnalyticFamily P G μ, ExteriorFamily Fam v0 H' ∧
      (H'.sec (1 / 6)).f v0 = f := by
  classical
  obtain ⟨n, c, fams, hExts, hsum⟩ := sectionSpace_family_spanning Fam v0 f hf
  let X : LambdaGen Fam v0 →₀ ℂ :=
    ∑ j : Fin n, Finsupp.single ⟨fams j, hExts j⟩ (c j)
  obtain ⟨H', C', hHext, hHcoord, _⟩ := lambda_exists_combo Fam v0 g laws X
  refine ⟨H', hHext, ?_⟩
  calc
    (H'.sec (1 / 6)).f v0 = lambdaGenCombination Fam v0 X (1 / 6) := hHcoord _
    _ = ∑ j, c j • ((fams j).sec (1 / 6)).f v0 := by
      change Finsupp.linearCombination ℂ
        (fun i => lambdaGenAt Fam v0 i (1 / 6)) X = _
      dsimp only [X]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp [lambdaGenAt, Finsupp.linearCombination_single]
    _ = f := hsum.symm

private theorem lambda_gen_span_top (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (hv0 : v0 ∉ S.Sf) :
    Submodule.span ℂ (Set.range (lambdaGenSection Fam v0)) = ⊤ := by
  apply top_unique
  intro f _
  obtain ⟨n, c, fams, hext, hsum⟩ :=
    sectionSpace_family_spanning Fam v0 f.1 f.2
  let i : Fin n → LambdaGen Fam v0 := fun j => ⟨fams j, hext j⟩
  have hsub : f = ∑ j, c j • lambdaGenSection Fam v0 (i j) := by
    apply Subtype.ext
    simpa [lambdaGenSection, i] using hsum
  rw [hsub]
  exact Submodule.sum_mem _ (fun j hj =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i j, rfl⟩))

/-- Build the residue functional on the section space and extend it through the intertwiner. -/
theorem theta_lambda_descent_core (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (hv0 : v0 ∉ S.Sf) (g : P.tc.G) (laws : ThetaResidueLaws P G μ) :
    ∃ Λ : ((P.loc v0).L → (G.T v0).V) →ₗ[ℂ] ℂ,
      ∃ θ : sectionSpace (P.loc v0) (G.T v0) (1 / 6 : ℂ) →ₗ[ℂ] ℂ,
        (∀ f, Λ (intertwine (P.loc v0) (μ v0) f.1) = θ f) ∧
        ∀ (Fam' : AnalyticFamily P G μ) (C' : ContinuedEis Fam'),
          ExteriorFamily Fam v0 Fam' →
            thetaWhit C' g = θ ⟨(Fam'.sec (1 / 6)).f v0, (Fam'.sec (1 / 6)).f_sec v0⟩ := by
  classical
  let L := P.loc v0
  let T := G.T v0
  let Zdata := lambda_exists_zero_family Fam v0
  let Z : AnalyticFamily P G μ := Classical.choose Zdata
  have hZext : ExteriorFamily Fam v0 Z := (Classical.choose_spec Zdata).1
  have hZcoord : ∀ s, (Z.sec s).f v0 = 0 := (Classical.choose_spec Zdata).2
  let CZ : ContinuedEis Z := Classical.choice (laws.continuation Z)
  have hZres := thetaWhit_zero_local_family v0 Z hZcoord g laws CZ
  let toSection : (LambdaGen Fam v0 →₀ ℂ) →ₗ[ℂ] sectionSpace L T (1 / 6 : ℂ) :=
    lambdaFreeToSection Fam v0
  have hspan := lambda_gen_span_top Fam v0 hv0
  have hsurj : Function.Surjective toSection := by
    change Function.Surjective (Finsupp.linearCombination ℂ (lambdaGenSection Fam v0))
    apply LinearMap.range_eq_top.mp
    rw [Finsupp.range_linearCombination]
    exact hspan
  have hsectionCoord (x : LambdaGen Fam v0 →₀ ℂ) :
      (toSection x : L.L → T.V) = lambdaGenCombination Fam v0 x (1 / 6 : ℂ) := by
    change (Submodule.subtype (sectionSpace L T (1 / 6 : ℂ))
      (Finsupp.linearCombination ℂ (lambdaGenSection Fam v0) x)) =
        Finsupp.linearCombination ℂ (fun i => lambdaGenAt Fam v0 i (1 / 6 : ℂ)) x
    change (Submodule.subtype (sectionSpace L T (1 / 6 : ℂ))
      (Finsupp.linearCombination ℂ (lambdaGenSection Fam v0) x)) =
        Finsupp.linearCombination ℂ
          (fun i => (lambdaGenSection Fam v0 i : (P.loc v0).L → (G.T v0).V)) x
    exact Finsupp.apply_linearCombination ℂ
      (Submodule.subtype (sectionSpace L T (1 / 6 : ℂ))) (lambdaGenSection Fam v0) x
  let rho : (LambdaGen Fam v0 →₀ ℂ) →ₗ[ℂ] ℂ :=
    lambdaResidueCombination Fam v0 g laws
  have hrhoKer : LinearMap.ker toSection ≤ LinearMap.ker rho := by
    intro x hx
    have hx' : toSection x = 0 := LinearMap.mem_ker.mp hx
    obtain ⟨H', C', hHext, hHcoord, hHtheta⟩ :=
      lambda_exists_combo Fam v0 g laws x
    have hlocal : (H'.sec (1 / 6)).f v0 = (Z.sec (1 / 6)).f v0 := by
      calc
        (H'.sec (1 / 6)).f v0 = lambdaGenCombination Fam v0 x (1 / 6 : ℂ) := hHcoord _
        _ = (toSection x : L.L → T.V) := (hsectionCoord x).symm
        _ = 0 := congrArg Subtype.val hx'
        _ = (Z.sec (1 / 6)).f v0 := (hZcoord _).symm
    have hT : H'.T0 = Z.T0 := hHext.1.trans hZext.1.symm
    have hM : ∀ v ∈ H'.T0,
        intertwine (P.loc v) (μ v) ((H'.sec (1 / 6)).f v) =
          intertwine (P.loc v) (μ v) ((Z.sec (1 / 6)).f v) := by
      intro v hv
      by_cases hv0' : v = v0
      · subst v
        rw [hlocal]
      · have hout : (H'.sec (1 / 6)).f v = (Z.sec (1 / 6)).f v := by
          calc
            (H'.sec (1 / 6)).f v = (Fam.sec (1 / 6)).f v := hHext.2 _ _ hv0'
            _ = (Z.sec (1 / 6)).f v := (hZext.2 _ _ hv0').symm
        rw [hout]
    have hdep := laws.dependsOnM H' Z C' CZ hT hM
    have hdepWhit := thetaWhit_eq_of_theta_eq H' Z C' CZ g laws hdep
    rw [LinearMap.mem_ker]
    calc
      rho x = thetaWhit C' g := hHtheta.symm
      _ = thetaWhit CZ g := hdepWhit
      _ = 0 := hZres
  let thetaOnSection : sectionSpace L T (1 / 6 : ℂ) →ₗ[ℂ] ℂ :=
    ((LinearMap.ker toSection).liftQ rho hrhoKer).comp
      (toSection.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hthetaGen (i : LambdaGen Fam v0) :
      thetaOnSection (lambdaGenSection Fam v0 i) = lambdaGenResidues Fam v0 g laws i := by
    have hsingle : toSection (Finsupp.single i 1) = lambdaGenSection Fam v0 i := by
      simp [toSection, lambdaFreeToSection]
    calc
      thetaOnSection (lambdaGenSection Fam v0 i) =
          thetaOnSection (toSection (Finsupp.single i 1)) := by rw [hsingle]
      _ = rho (Finsupp.single i 1) := by
        simp [thetaOnSection, rho, lambdaResidueCombination,
          LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
      _ = lambdaGenResidues Fam v0 g laws i := by
        simp [rho, lambdaResidueCombination, lambdaGenResidues]
  let M : sectionSpace L T (1 / 6 : ℂ) →ₗ[ℂ] (L.L → T.V) :=
    intertwineSectionLinear L T (μ v0) (1 / 6 : ℂ) (by norm_num)
  have hMker : LinearMap.ker M ≤ LinearMap.ker thetaOnSection := by
    intro f hf
    obtain ⟨x, hx⟩ := hsurj f
    obtain ⟨H', C', hHext, hHcoord, hHtheta⟩ :=
      lambda_exists_combo Fam v0 g laws x
    have hlocal : (H'.sec (1 / 6)).f v0 = f.1 := by
      calc
        (H'.sec (1 / 6)).f v0 = lambdaGenCombination Fam v0 x (1 / 6 : ℂ) := hHcoord _
        _ = (toSection x : L.L → T.V) := (hsectionCoord x).symm
        _ = f.1 := congrArg Subtype.val hx
    have htheta : thetaOnSection f = rho x := by
      rw [← hx]
      simp [thetaOnSection, rho, lambdaResidueCombination,
        LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    have hMzero : intertwine L (μ v0) ((H'.sec (1 / 6)).f v0) =
        intertwine L (μ v0) ((Z.sec (1 / 6)).f v0) := by
      rw [hlocal]
      have hfzero : intertwine L (μ v0) f.1 = 0 := by
        change M f = 0
        exact LinearMap.mem_ker.mp hf
      rw [hfzero, hZcoord]
      funext x
      simp [intertwine]
    have hT : H'.T0 = Z.T0 := hHext.1.trans hZext.1.symm
    have hM' : ∀ v ∈ H'.T0,
        intertwine (P.loc v) (μ v) ((H'.sec (1 / 6)).f v) =
          intertwine (P.loc v) (μ v) ((Z.sec (1 / 6)).f v) := by
      intro v hv
      by_cases hv0' : v = v0
      · subst v
        exact hMzero
      · have hout : (H'.sec (1 / 6)).f v = (Z.sec (1 / 6)).f v := by
          calc
            (H'.sec (1 / 6)).f v = (Fam.sec (1 / 6)).f v := hHext.2 _ _ hv0'
            _ = (Z.sec (1 / 6)).f v := (hZext.2 _ _ hv0').symm
        rw [hout]
    have hdep := laws.dependsOnM H' Z C' CZ hT hM'
    have hdepWhit := thetaWhit_eq_of_theta_eq H' Z C' CZ g laws hdep
    have hzero : rho x = 0 := by
      calc
        rho x = thetaWhit C' g := hHtheta.symm
        _ = thetaWhit CZ g := hdepWhit
        _ = 0 := hZres
    change thetaOnSection f = 0
    rw [htheta, hzero]
  let thetaRange : LinearMap.range M →ₗ[ℂ] ℂ :=
    ((LinearMap.ker M).liftQ thetaOnSection hMker).comp
      M.quotKerEquivRange.symm.toLinearMap
  obtain ⟨Λ, hΛext⟩ := LinearMap.exists_extend thetaRange
  have hfactor (f : sectionSpace L T (1 / 6 : ℂ)) :
      Λ (intertwine L (μ v0) f.1) = thetaOnSection f := by
    have hEval := congrArg (fun φ : LinearMap.range M →ₗ[ℂ] ℂ =>
      φ ⟨M f, ⟨f, rfl⟩⟩) hΛext
    have hEval' : Λ (M f) = thetaRange ⟨M f, ⟨f, rfl⟩⟩ := by
      change Λ (M f) = thetaRange ⟨M f, ⟨f, rfl⟩⟩ at hEval
      exact hEval
    have hrange : thetaRange ⟨M f, ⟨f, rfl⟩⟩ = thetaOnSection f := by
      change ((LinearMap.ker M).liftQ thetaOnSection hMker)
          (M.quotKerEquivRange.symm ⟨M f, ⟨f, rfl⟩⟩) = thetaOnSection f
      rw [LinearMap.quotKerEquivRange_symm_apply_image (f := M) (x := f) ⟨f, rfl⟩]
      simp [Submodule.liftQ_apply]
    change Λ (M f) = thetaOnSection f
    exact hEval'.trans hrange
  refine ⟨Λ, thetaOnSection, ?_, ?_⟩
  · exact hfactor
  · intro Fam' C' hExt
    let i : LambdaGen Fam v0 := ⟨Fam', hExt⟩
    have hdep := laws.dependsOnM Fam' Fam'
      C' (Classical.choice (laws.continuation Fam')) rfl (by intro v hv; rfl)
    have hwhit : thetaWhit C' g =
        thetaWhit (Classical.choice (laws.continuation Fam')) g := by
      exact thetaWhit_eq_of_theta_eq Fam' Fam' C'
        (Classical.choice (laws.continuation Fam')) g laws hdep
    calc
      thetaWhit C' g = lambdaGenResidues Fam v0 g laws i := by
        simpa [lambdaGenResidues, i] using hwhit
      _ = thetaOnSection (lambdaGenSection Fam v0 i) := (hthetaGen i).symm
      _ = thetaOnSection ⟨(Fam'.sec (1 / 6)).f v0,
          (Fam'.sec (1 / 6)).f_sec v0⟩ := by rfl

end ArtinPrimitiveRoots.A1.Theta
