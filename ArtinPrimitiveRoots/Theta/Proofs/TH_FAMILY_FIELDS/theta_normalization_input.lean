import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import ArtinPrimitiveRoots.Proofs.th_family_a.ThetaNormalization
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_tail_invariance
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.WvAll_properties

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem thetaNormalization_scalar_right_tail
    (P : CoverPackage D S H A) (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v)
    (Fam : AnalyticFamily P G μ) (hT : Fam.T0 = S.Sf) (tail : P.RP)
    (hS : ∀ v : S.Sf, P.compF v.1 tail = 1)
    (hK : ∀ v (hv : v ∉ S.Sf), P.compF v tail ∈ (P.tame v hv).Kmax)
    (hC : ∀ w, P.compC w tail = 1) :
    ∀ s h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * P.q tail) =
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by
  classical
  intro s h
  obtain ⟨x, hxq⟩ := P.q_surj h
  have hxk : P.q (x * tail) = h * P.q tail := by rw [(P.q).map_mul, hxq]
  have hfun : (fun v => G.lam v ((Fam.sec s).f v (P.compF v (x * tail)))) =
      fun v => G.lam v ((Fam.sec s).f v (P.compF v x) : (G.T v).V) := by
    funext v
    rw [(P.compF v).map_mul]
    by_cases hv : v ∈ S.Sf
    · rw [hS ⟨v, hv⟩, mul_one]
    · have hTsec : (Fam.sec s).T0 = S.Sf := (Fam.T0_eq s).trans hT
      have hvT : v ∉ Fam.T0 := by simpa [hT] using hv
      have hvTsec : v ∉ (Fam.sec s).T0 := by rw [hTsec]; exact hv
      have htail_mem : P.compF v tail ∈
          (P.tame v (fun hs => hvTsec ((Fam.sec s).sub hs))).Kmax := by
        simpa using hK v hv
      have hInv := ((Fam.sec s).f_sph v hvTsec).2
        (P.compF v x) (P.compF v tail) htail_mem
      exact congrArg (G.lam v) hInv
  have hfin : (∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v (x * tail)))) =
      ∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v x)) := by
    apply finprod_congr
    intro v
    exact congrFun hfun v
  have harch : (∏ w, (Fam.sec s).fC w (P.compC w (x * tail))) =
      ∏ w, (Fam.sec s).fC w (P.compC w x) := by
    apply Finset.prod_congr rfl
    intro w hw
    rw [(P.compC w).map_mul, hC w, mul_one]
  have hformX := (scalarOf_q P G (Fam.sec s) x).2
  have hformXT := (scalarOf_q P G (Fam.sec s) (x * tail)).2
  calc
    scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * P.q tail) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC (P.q (x * tail)) := by rw [hxk]
    _ = (∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v (x * tail)))) *
        ∏ w, (Fam.sec s).fC w (P.compC w (x * tail)) := hformXT
    _ = (∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v x))) *
        ∏ w, (Fam.sec s).fC w (P.compC w x) := by rw [hfin, harch]
    _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (P.q x) := hformX.symm
    _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by rw [hxq]

/-- Choose the actual global datum, Haar measures and a nonzero multilinear evaluation.
Uses exists_globalDatum, LocHaar.nonempty, exists_theta_ne_zero, thetaWhit_ne_zero thetaWhit_multilinear and the supplied thetaWhit_factor conclusion. -/
theorem theta_normalization_input (P : CoverPackage D S H A)
    (hSt : ∀ v, SteinbergAt H v) (hFactor : ThetaFactorizationInput P) : Nonempty (ThetaNormalizationInput P) := by
  classical
  obtain ⟨G⟩ := exists_globalDatum P hSt
  let μ : ∀ v : FinPlace F, LocHaar v := fun v => Classical.choice (LocHaar.nonempty v)
  obtain ⟨Fam, C, hFamLevel, hLocal, hTheta⟩ := exists_theta_ne_zero P G μ
  obtain ⟨g, hWg⟩ := thetaWhit_ne_zero Fam C hTheta
  obtain ⟨r, hr⟩ := P.q_surj g
  obtain ⟨ξ, sRP, tail, T, hsGS, hsExt, hTOutside, hTailK, hTailS, hTailC, hFactorR⟩ :=
    thetaNormalizationRPFactorization (P := P) r
  let gS : P.tc.G := P.q sRP
  let gExt : FinPlace F → P.tc.G := fun v => P.emb v (P.compF v r)
  have hgExt : ∀ v ∈ T, gExt v ∈ P.tc.Gloc v := by
    intro v hv
    rw [← P.emb_Gloc v (hTOutside v hv)]
    exact ⟨P.compF v r, rfl⟩
  have htailFix : ∀ s h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC
      (h * P.q tail) = scalarOf P G (Fam.sec s).f (Fam.sec s).fC h :=
    thetaNormalization_scalar_right_tail P G μ Fam hFamLevel tail hTailS hTailK hTailC
  have htailWhit := thetaWhit_tail_invariance Fam C (P.q tail) htailFix
  have hcenterWhit := (thetaWhit_equiv Fam C).1 ξ
    (gS * (T.toList.map gExt).prod * P.q tail)
  have hWprefix : thetaWhit C (gS * (T.toList.map gExt).prod) ≠ 0 := by
    have hWq : thetaWhit C (P.q r) ≠ 0 := by rw [hr]; exact hWg
    rw [hFactorR, hcenterWhit] at hWq
    have hWtail : thetaWhit C
        (gS * (T.toList.map gExt).prod * P.q tail) ≠ 0 :=
      (mul_ne_zero_iff.mp hWq).2
    rw [htailWhit (gS * (T.toList.map gExt).prod)] at hWtail
    exact hWtail
  have hdiagOne : diagGL (1 : Fˣ) = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [diagGL]
  have hratOne : P.tc.rat (diagGL (1 : Fˣ)) = 1 := by
    rw [hdiagOne]
    exact map_one P.tc.rat
  let gBase : P.tc.G := P.tc.aS (S.diagU (1 : Fˣ)) * gS
  have hgBase : gBase ∈ P.tc.GS := by
    exact P.tc.GS.mul_mem (P.tc.aS_mem _) hsGS
  have hFactorEq := hFactor G μ Fam hFamLevel C (1 : Fˣ) false gS hsGS T hTOutside gExt hgExt
  have haOne (v : FinPlace F) (hv : v ∉ S.Sf) : P.tc.a v (toLoc v (1 : Fˣ)) = 1 := by
    calc
      P.tc.a v (toLoc v (1 : Fˣ)) = P.emb v ((P.loc v).a (toLoc v (1 : Fˣ))) :=
        (P.emb_a v hv (toLoc v (1 : Fˣ))).symm
      _ = P.emb v 1 := by rw [map_one (toLoc v), (P.loc v).a_one]
      _ = 1 := map_one (P.emb v)
  have haOne' (v : FinPlace F) (hv : v ∉ S.Sf) : P.tc.a v 1 = 1 := by
    simpa using haOne v hv
  have hWvOne (v : FinPlace F) (hv : v ∉ S.Sf) :
      thetaExteriorWv P G μ v (P.tc.a v (toLoc v (1 : Fˣ))) = 1 := by
    have hu : ((toLoc v (1 : Fˣ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
        v.adicCompletionIntegers F := by simp
    have huinv : (((toLoc v (1 : Fˣ))⁻¹ : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) ∈ v.adicCompletionIntegers F := by simp
    have htable := (WvAll_properties P G μ).2.2.2 v hv 0 1 hu huinv
    change WvAll P G μ v (P.tc.a v (toLoc v (1 : Fˣ))) = 1
    rw [haOne v hv]
    have htable' : WvAll P G μ v (P.tc.a v (toLoc v (1 : Fˣ))) = 1 := by
      simpa [sphericalTable] using htable
    rw [haOne v hv] at htable'
    exact htable'
  have htailExteriorSub :
      (∏ᶠ (v : {v : FinPlace F // v ∉ S.Sf ∧ v ∉ T}),
        thetaExteriorWv P G μ v.1 (P.tc.a v.1 (toLoc v.1 (1 : Fˣ)))) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    exact hWvOne v.1 v.2.1
  have htailExterior :
      (∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T),
        thetaExteriorWv P G μ v (P.tc.a v (toLoc v (1 : Fˣ)))) = 1 := by
    rw [← finprod_subtype_eq_finprod_cond (p := fun v : FinPlace F =>
      v ∉ S.Sf ∧ v ∉ T)]
    exact htailExteriorSub
  have hWvOne' (v : FinPlace F) (hv : v ∉ S.Sf) :
      thetaExteriorWv P G μ v (P.tc.a v 1) = 1 := by
    have harg : P.tc.a v 1 = P.tc.a v (toLoc v (1 : Fˣ)) := by
      rw [haOne' v hv, haOne v hv]
    rw [harg]
    exact hWvOne v hv
  have htailExteriorSub' :
      (∏ᶠ (v : {v : FinPlace F // v ∉ S.Sf ∧ v ∉ T}),
        thetaExteriorWv P G μ v.1 (P.tc.a v.1 1)) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    exact hWvOne' v.1 v.2.1
  have htailExterior' :
      (∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T),
        thetaExteriorWv P G μ v (P.tc.a v 1)) = 1 := by
    rw [← finprod_subtype_eq_finprod_cond (p := fun v : FinPlace F =>
      v ∉ S.Sf ∧ v ∉ T)]
    exact htailExteriorSub'
  have hfiniteExt :
      (∏ v ∈ T, thetaExteriorWv P G μ v (P.tc.a v 1 * gExt v)) =
        ∏ v ∈ T, thetaExteriorWv P G μ v (gExt v) := by
    apply Finset.prod_congr rfl
    intro v hv
    rw [haOne' v (hTOutside v hv), one_mul]
  have hFactorEq0 :
      thetaWhit C (gS * (T.toList.map gExt).prod) =
        thetaWhit C gBase *
          (∏ v ∈ T, thetaExteriorWv P G μ v (P.tc.a v 1 * gExt v)) *
          (∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T),
            thetaExteriorWv P G μ v (P.tc.a v 1)) := by
    simpa [gBase, gS, hratOne, mul_assoc] using hFactorEq
  have hFactorEq' :
      thetaWhit C (gS * (T.toList.map gExt).prod) =
        thetaWhit C gBase * (∏ v ∈ T, thetaExteriorWv P G μ v (gExt v)) := by
    calc
      thetaWhit C (gS * (T.toList.map gExt).prod) =
          thetaWhit C gBase *
            (∏ v ∈ T, thetaExteriorWv P G μ v (P.tc.a v 1 * gExt v)) *
            (∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T),
              thetaExteriorWv P G μ v (P.tc.a v 1)) := hFactorEq0
      _ = thetaWhit C gBase * (∏ v ∈ T, thetaExteriorWv P G μ v (gExt v)) := by
        rw [hfiniteExt, htailExterior']
        simp
  have hBaseNe : thetaWhit C gBase ≠ 0 := by
    intro hzero
    rw [hFactorEq', hzero] at hWprefix
    simp at hWprefix
  obtain ⟨xA, hxAq, hxAF, hxAC⟩ := P.aS_components (S.diagU (1 : Fˣ))
  let x₀ : P.RP := xA * sRP
  have hx₀q : P.q x₀ = gBase := by
    dsimp [x₀, gBase, gS]
    rw [(P.q).map_mul, hxAq]
  have hx₀Ext : ∀ v, v ∉ S.Sf → P.compF v x₀ = 1 := by
    intro v hv
    rw [(P.compF v).map_mul, hxAF v, hsExt v hv]
    simp [hv]
  obtain ⟨Λ, hΛ⟩ := thetaWhit_multilinear Fam x₀
  let J : ∀ v : S.Sf, (G.T v.1).V := fun v =>
    jacquet (P.loc v.1) A (μ v.1)
      (rtr (P.compF v.1 x₀) ((Fam.sec (1 / 6)).f v.1))
  have hMultValue : thetaWhit C gBase = Λ J * ∏ w : InfinitePlace F,
      jacquetC (rtr (P.compC w x₀) (sphC (1 / 6))) := by
    have h := hΛ Fam C x₀ rfl (by intro s v hv; rfl) (by intro v hv; rfl)
    rw [hx₀q] at h
    exact h
  have hEval : Λ J ≠ 0 := by
    intro hzero
    apply hBaseNe
    rw [hMultValue, hzero]
    simp
  refine ⟨{
    G := G
    μ := μ
    Fam := Fam
    C := C
    level := hFamLevel
    nonzero := hTheta
    Λ := Λ
    x := J
    eval_ne_zero := hEval
    coefficient := ?_ }⟩
  intro Fam' C' r' hT' hext houtside
  have hT'' : Fam'.T0 = Fam.T0 := hT'.trans hFamLevel.symm
  have houtside' : ∀ v, v ∉ S.Sf → P.compF v r' = P.compF v x₀ := by
    intro v hv
    rw [houtside v hv, hx₀Ext v hv]
  exact hΛ Fam' C' r' hT'' hext houtside'
end ArtinPrimitiveRoots.A1.Theta
