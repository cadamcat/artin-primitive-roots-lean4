import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.theta_adapted_domain_exists
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_argument_decomposition
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.RestrictedProduct
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.TailSupport
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.CompactConjugation
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.DomainRefinement
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.DerivativeInvariance
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.LocalBall
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.FractionalIndex
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.FiniteUnipotentLift

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical Pointwise
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Choose one nonzero period ideal and bounded measurable fundamental domain for all points of a compact set in the canonical restricted-product quotient.
Uses HasRestrictedProductTopology, CoverPackage.q_quotient, uniform common-family finite level and finite compact chart covers. -/
theorem theta_uniform_adapted_lattice {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B)
    (K : Set P.tc.G) (hK : @IsCompact P.tc.G P.tc.topology K) :
    ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (Pd : Set (InfinitePlace F → ℂ)),
      𝔞 ≠ 0 ∧
      IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume ∧
      Bornology.IsBounded Pd ∧ MeasurableSet Pd ∧
      (∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf 1 (infEmbA ξ) = 1) ∧
      (∀ g ∈ K, ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
          scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC h) ∧
      (∀ L ∈ 𝓛, ∀ g ∈ K, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ x,
        thetaFamilyTheta B L (nInf P (x + infEmbA ξ) * g) =
          thetaFamilyTheta B L (nInf P x * g)) := by
  classical
  letI : TopologicalSpace P.RP := P.rpTopology
  letI : TopologicalSpace P.tc.G := P.tc.topology
  letI : @IsTopologicalGroup P.RP P.rpTopology P.rpGrp := P.rpTopGroup
  have hFam : FourierFamilyHyp N.μ B.Fam.sec B.Fam.T0 := B.Fam.fourierHyp
  obtain ⟨a₀, p₀, hAdapt, hp₀Meas⟩ := theta_adapted_domain_exists hFam (1 : P.tc.G)
  rcases hAdapt with ⟨ha₀, hfix₀, hfd₀, hp₀Bound, hψ₀⟩
  obtain ⟨charts, liftChart, hChartCompact, hChartCover⟩ :=
    compact_quotient_lift_charts P hRP K hK
  let chartIndex := charts.attach
  let chartTail (c : {g : P.tc.G // g ∈ charts}) : Finset (FinPlace F) :=
    Classical.choose
      (compact_chart_uniform_tame_support P hRP (liftChart c.1) (hChartCompact c.1 c.2))
  have hchartTail (c : {g : P.tc.G // g ∈ charts}) :
      ∀ x ∈ liftChart c.1, ∀ v, v ∉ S.Sf → v ∉ chartTail c →
        P.compF v x ∈ referenceSubset P (.inl v) :=
    Classical.choose_spec
      (compact_chart_uniform_tame_support P hRP (liftChart c.1) (hChartCompact c.1 c.2))
  let exceptional : Finset (FinPlace F) :=
    S.Sf ∪ chartIndex.biUnion chartTail
  let coordCompact (v : FinPlace F) : Set (P.loc v).L :=
    ⋃ c ∈ chartIndex, P.compF v '' liftChart c.1
  have hcoordCompact (v : FinPlace F) : IsCompact (coordCompact v) := by
    dsimp [coordCompact]
    exact chartIndex.isCompact_biUnion fun c hc =>
      (hChartCompact c.1 c.2).image (P.compF_cont v)
  have hchartLift (g : P.tc.G) (hg : g ∈ K) :
      ∃ c ∈ charts, ∃ x ∈ liftChart c, P.q x = g := hChartCover g hg
  have hFamilyLevel (v : FinPlace F) (hv : v ∈ S.Sf) :
      ∃ m, (P.loc v).m0 ≤ m ∧ ∀ s g k, k ∈ (P.loc v).Kc m →
        (B.Fam.sec s).f v (g * k) = (B.Fam.sec s).f v g := by
    apply B.Fam.level v
    simpa [B.level] using hv
  let familyDepth : (v : FinPlace F) → v ∈ S.Sf → ℕ := fun v hv =>
    Classical.choose (hFamilyLevel v hv)
  have hfamilyDepth v hv :
      (P.loc v).m0 ≤ familyDepth v hv ∧ ∀ s g k,
        k ∈ (P.loc v).Kc (familyDepth v hv) →
          (B.Fam.sec s).f v (g * k) = (B.Fam.sec s).f v g :=
    Classical.choose_spec (hFamilyLevel v hv)
  let targetSub (v : FinPlace F) : Subgroup (P.loc v).L :=
    if hv : v ∈ S.Sf then (P.loc v).Kc (familyDepth v hv) else (P.tame v hv).Kmax
  have htargetOpen (v : FinPlace F) : IsOpen (targetSub v : Set (P.loc v).L) := by
    by_cases hv : v ∈ S.Sf
    · simpa [targetSub, hv] using
        (P.loc v).Kc_open (familyDepth v hv) (hfamilyDepth v hv).1
    · simpa [targetSub, hv] using (P.tame v hv).open_
  have htargetOne (v : FinPlace F) : (1 : (P.loc v).L) ∈ targetSub v :=
    (targetSub v).one_mem
  have hdepth (v : FinPlace F) (hv : v ∈ exceptional) :
      ∃ m, (P.loc v).m0 ≤ m ∧ ∀ ξ ∈ ball v (m : ℤ), ∀ g ∈ coordCompact v,
        g⁻¹ * (P.loc v).n (Multiplicative.ofAdd ξ) * g ∈ targetSub v := by
    obtain ⟨U, hUopen, hUone, hUconj⟩ :=
      compact_conjugation_neighborhood (hcoordCompact v) (htargetOpen v) (htargetOne v)
    obtain ⟨m, hm0, hmU⟩ := (P.loc v).Kc_nhds U (hUopen.mem_nhds hUone)
    refine ⟨m, hm0, ?_⟩
    intro ξ hξ g hg
    apply hUconj
    · exact hmU ((P.loc v).n_Kc m hm0 ξ hξ)
    · exact hg
  let localDepth (v : FinPlace F) : ℕ :=
    if hv : v ∈ exceptional then Classical.choose (hdepth v hv) else 0
  have hlocalDepth (v : FinPlace F) (hv : v ∈ exceptional) :
      (P.loc v).m0 ≤ localDepth v ∧
        ∀ ξ ∈ ball v ((localDepth v : ℕ) : ℤ), ∀ g ∈ coordCompact v,
          g⁻¹ * (P.loc v).n (Multiplicative.ofAdd ξ) * g ∈ targetSub v := by
    simpa [localDepth, hv] using Classical.choose_spec (hdepth v hv)
  let Jideal : Ideal (𝓞 F) := ∏ v ∈ exceptional, v.asIdeal ^ (localDepth v)
  have hJideal : Jideal ≠ ⊥ := by
    change (∏ v ∈ exceptional, v.asIdeal ^ (localDepth v)) ≠ (0 : Ideal (𝓞 F))
    rw [Finset.prod_ne_zero_iff]
    intro v hv
    exact pow_ne_zero _ v.ne_bot
  obtain ⟨t, htJ, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJideal
  have htInf : t ∈ Finset.inf exceptional (fun v => v.asIdeal ^ (localDepth v)) := by
    have hle : Jideal ≤ Finset.inf exceptional (fun v => v.asIdeal ^ (localDepth v)) :=
      by
        dsimp [Jideal]
        exact Ideal.prod_le_inf (s := exceptional) (f := fun v => v.asIdeal ^ (localDepth v))
    exact (SetLike.le_def.mp hle) htJ
  have htPow (v : FinPlace F) (hv : v ∈ exceptional) :
      t ∈ v.asIdeal ^ (localDepth v) := by
    have hle : Finset.inf exceptional (fun v => v.asIdeal ^ (localDepth v)) ≤
        v.asIdeal ^ (localDepth v) := Finset.inf_le hv
    exact (SetLike.le_def.mp hle) htInf
  obtain ⟨d, J₀, hd, hA₀⟩ := FractionalIdeal.exists_eq_spanSingleton_mul a₀
  let u : 𝓞 F := d * t
  have hu : algebraMap (𝓞 F) F u ≠ 0 := by
    simp [u, map_mul, map_ne_zero, hd, ht0]
  let 𝔞 := scalarFractionalIdeal u a₀
  have h𝔞 : 𝔞 ≠ 0 := by
    dsimp [𝔞, scalarFractionalIdeal]
    exact mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hu) ha₀
  have h𝔞sub : 𝔞 ≤ a₀ := by
    dsimp [𝔞, scalarFractionalIdeal]
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro z hz
    have hz' : u • z ∈ (a₀ : Submodule (𝓞 F) F) :=
      Submodule.smul_mem _ u hz
    simpa [Algebra.smul_def] using hz'
  have hψ : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf 1 (infEmbA ξ) = 1 := by
    intro ξ hξ
    exact hψ₀ ξ (h𝔞sub hξ)
  have hξRep (ξ : F) (hξ : ξ ∈ (𝔞 : Submodule (𝓞 F) F)) :
      ∃ j : 𝓞 F, j ∈ J₀ ∧ ξ = algebraMap (𝓞 F) F (t * j) := by
    have hξa : ξ ∈ 𝔞 := by exact hξ
    change ξ ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
      (algebraMap (𝓞 F) F u) * a₀ at hξa
    obtain ⟨y, hy, hxy⟩ := FractionalIdeal.mem_singleton_mul.mp hξa
    rw [hA₀] at hy
    obtain ⟨jF, hjF, hY⟩ := FractionalIdeal.mem_singleton_mul.mp hy
    rcases (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 F))).mp hjF with ⟨j, hj, rfl⟩
    refine ⟨j, hj, ?_⟩
    have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
      (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 F) F).not.2 hd
    calc
      ξ = (algebraMap (𝓞 F) F u) * y := hxy
      _ = (algebraMap (𝓞 F) F u) *
          ((algebraMap (𝓞 F) F d)⁻¹ * algebraMap (𝓞 F) F j) := by rw [hY]
      _ = algebraMap (𝓞 F) F (t * j) := by
        have hU : algebraMap (𝓞 F) F u =
            algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F t := by simp [u]
        rw [hU]
        calc
          (algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F t) *
              ((algebraMap (𝓞 F) F d)⁻¹ * algebraMap (𝓞 F) F j) =
              (algebraMap (𝓞 F) F d * (algebraMap (𝓞 F) F d)⁻¹) *
                (algebraMap (𝓞 F) F t * algebraMap (𝓞 F) F j) := by ac_rfl
          _ = algebraMap (𝓞 F) F t * algebraMap (𝓞 F) F j := by
            rw [mul_inv_cancel₀ hdF, one_mul]
          _ = algebraMap (𝓞 F) F (t * j) := by rw [map_mul]
  have hξSmall (ξ : F) (hξ : ξ ∈ (𝔞 : Submodule (𝓞 F) F))
      (v : FinPlace F) (hv : v ∈ exceptional) :
      algebraMap F (v.adicCompletion F) ξ ∈ ball v ((localDepth v : ℕ) : ℤ) := by
    obtain ⟨j, hj, rfl⟩ := hξRep ξ hξ
    have htpow : t * j ∈ v.asIdeal ^ (localDepth v) := by
      have h := (v.asIdeal ^ (localDepth v)).mul_mem_left j (htPow v hv)
      simpa [mul_comm] using h
    have hball := algebraicIdealPower_mem_ball v (localDepth v) (t * j) htpow
    simpa using hball
  have hξIntegral (ξ : F) (hξ : ξ ∈ (𝔞 : Submodule (𝓞 F) F))
      (v : FinPlace F) : algebraMap F (v.adicCompletion F) ξ ∈ v.adicCompletionIntegers F := by
    obtain ⟨j, hj, rfl⟩ := hξRep ξ hξ
    change (↑(algebraMap (𝓞 F) F (t * j)) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F
    exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem
      (R := 𝓞 F) (K := F) (v := v) (r := t * j)
  let A₀ : AddSubgroup (InfinitePlace F → ℂ) := archFractionalIdealLattice a₀
  let A₁ : AddSubgroup (InfinitePlace F → ℂ) := archFractionalIdealLattice 𝔞
  have hA₁A₀ : A₁ ≤ A₀ := by
    intro x hx
    rcases AddSubgroup.mem_map.mp hx with ⟨ξ, hξ, rfl⟩
    exact AddSubgroup.mem_map.mpr ⟨ξ, h𝔞sub hξ, rfl⟩
  have hFinite : Finite (A₀ ⧸ A₁.comap A₀.subtype) :=
    finite_archFractionalIdeal_scale_quotient a₀ u hu
  have hp0ShiftMeas : ∀ z : InfinitePlace F → ℂ, MeasurableSet (z +ᵥ p₀) := by
    intro z
    change MeasurableSet ((Homeomorph.addLeft z) '' p₀)
    exact (Homeomorph.addLeft z).measurableEmbedding.measurableSet_image.mpr hp₀Meas
  obtain ⟨Pd, hPd, hPdBound, hPdMeas⟩ :=
    addFundamentalDomain_refine_finite (α := InfinitePlace F → ℂ) volume A₀ A₁
      hA₁A₀ hFinite p₀ hp0ShiftMeas hfd₀ hp₀Bound
  have hReference (v : FinPlace F) (hv : v ∉ S.Sf) :
      referenceSubset P (.inl v) = ((P.tame v hv).Kmax : Set (P.loc v).L) := by
    simp [referenceSubset, LocalComponent, hv]
  have hLocalSectionFix (s : ℂ) (v : FinPlace F) (g k : (P.loc v).L)
      (hk : k ∈ targetSub v) :
      (B.Fam.sec s).f v (g * k) = (B.Fam.sec s).f v g := by
    by_cases hv : v ∈ S.Sf
    · have hk' : k ∈ (P.loc v).Kc (familyDepth v hv) := by
        simpa [targetSub, hv] using hk
      exact (hfamilyDepth v hv).2 s g k hk'
    · have hvT : v ∉ (B.Fam.sec s).T0 := by
        rw [B.Fam.T0_eq s, B.level]
        exact hv
      have hk' : k ∈ (P.tame v hv).Kmax := by simpa [targetSub, hv] using hk
      exact (B.Fam.sec s).f_sph v hvT |>.2 g k hk'
  have hScalarFix (g : P.tc.G) (hg : g ∈ K) (ξ : F)
      (hξ : ξ ∈ (𝔞 : Submodule (𝓞 F) F)) :
      ∀ s h, scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC
        (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC h := by
    obtain ⟨c, hc, xg, hxg, hqxg⟩ := hchartLift g hg
    obtain ⟨xFin, hqFin, hcompFinF, hcompFinC⟩ := nFin_has_finite_only_lift P ξ
    let xK := xg⁻¹ * xFin * xg
    have hqK : P.q xK = g⁻¹ * nFin P ξ * g := by
      dsimp [xK]
      rw [(P.q).map_mul, (P.q).map_mul, (P.q).map_inv, hqxg, hqFin]
    have hcompK (v : FinPlace F) :
        P.compF v xK = (P.compF v xg)⁻¹ *
          (P.loc v).n (Multiplicative.ofAdd (algebraMap F (v.adicCompletion F) ξ)) *
            P.compF v xg := by
      dsimp [xK]
      rw [(P.compF v).map_mul, (P.compF v).map_mul, (P.compF v).map_inv, hcompFinF]
    have hcompCK (w : InfinitePlace F) : P.compC w xK = 1 := by
      dsimp [xK]
      rw [(P.compC w).map_mul, (P.compC w).map_mul, (P.compC w).map_inv, hcompFinC]
      simp
    have hcoord (v : FinPlace F) : P.compF v xg ∈ coordCompact v := by
      apply Set.mem_iUnion₂.2
      refine ⟨⟨c, hc⟩, Finset.mem_attach _ _, ?_⟩
      exact ⟨xg, hxg, rfl⟩
    have htargetK (v : FinPlace F) : P.compF v xK ∈ targetSub v := by
      by_cases hvE : v ∈ exceptional
      · have hsmall := hξSmall ξ hξ v hvE
        rw [hcompK v]
        exact (hlocalDepth v hvE).2 _ hsmall (P.compF v xg) (hcoord v)
      · have hvS : v ∉ S.Sf := by
          intro hvS
          exact hvE (Finset.mem_union_left _ hvS)
        have hvTail : v ∉ chartTail ⟨c, hc⟩ := by
          intro htail
          have hcIndex : (⟨c, hc⟩ : {g : P.tc.G // g ∈ charts}) ∈ chartIndex := by
            simp [chartIndex]
          exact hvE (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨⟨c, hc⟩, hcIndex, htail⟩))
        have hgK : P.compF v xg ∈ (P.tame v hvS).Kmax := by
          have h := hchartTail ⟨c, hc⟩ xg hxg v hvS hvTail
          rw [hReference v hvS] at h
          exact h
        have hnK : (P.loc v).n
            (Multiplicative.ofAdd (algebraMap F (v.adicCompletion F) ξ)) ∈
              (P.tame v hvS).Kmax :=
          (P.tame v hvS).n_mem _ (hξIntegral ξ hξ v)
        have hkK : P.compF v xK ∈ (P.tame v hvS).Kmax := by
          rw [hcompK v]
          have hleft := (P.tame v hvS).Kmax.mul_mem
            ((P.tame v hvS).Kmax.inv_mem hgK) hnK
          exact (P.tame v hvS).Kmax.mul_mem hleft hgK
        simpa [targetSub, hvS] using hkK
    have hFixLocal (s : ℂ) (v : FinPlace F) (h : (P.loc v).L) :
        (B.Fam.sec s).f v (h * P.compF v xK) = (B.Fam.sec s).f v h :=
      hLocalSectionFix s v h (P.compF v xK) (htargetK v)
    intro s h
    let yh := Function.surjInv P.q_surj h
    have hqy : P.q yh = h := Function.surjInv_eq P.q_surj h
    have hqMul : P.q (yh * xK) = h * (g⁻¹ * nFin P ξ * g) := by
      rw [(P.q).map_mul, hqy, hqK]
    calc
      scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC
          (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P N.G (B.Fam.sec s).f
              (B.Fam.sec s).fC (P.q (yh * xK)) := by rw [hqMul]
      _ = (∏ᶠ v, N.G.lam v ((B.Fam.sec s).f v (P.compF v (yh * xK)))) *
            ∏ w, (B.Fam.sec s).fC w (P.compC w (yh * xK)) :=
          (scalarOf_q P N.G (B.Fam.sec s) (yh * xK)).2
      _ = (∏ᶠ v, N.G.lam v ((B.Fam.sec s).f v (P.compF v yh))) *
            ∏ w, (B.Fam.sec s).fC w (P.compC w yh) := by
          congr 1
          · apply finprod_congr
            intro v
            rw [(P.compF v).map_mul]
            congr 1
            exact hFixLocal s v (P.compF v yh)
          · apply Finset.prod_congr rfl
            intro w hw
            rw [(P.compC w).map_mul, hcompCK w]
            simp
      _ = scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC (P.q yh) :=
          (scalarOf_q P N.G (B.Fam.sec s) yh).2.symm
      _ = scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC h := by rw [hqy]
  refine ⟨𝔞, Pd, h𝔞, hPd, hPdBound, hPdMeas, hψ, ?_, ?_⟩
  · intro g hg s ξ hξ h
    exact hScalarFix g hg ξ hξ s h
  · intro L hL g hg ξ hξ x
    have hneg : (-ξ : F) ∈ (𝔞 : Submodule (𝓞 F) F) := by
      exact (𝔞 : Submodule (𝓞 F) F).neg_mem hξ
    let k := g⁻¹ * nFin P (-ξ) * g
    have hfixK := hScalarFix g hg (-ξ) hneg
    have hthetaK : ∀ y, B.C.theta (y * k) = B.C.theta y :=
      theta_right_of_scalar_fix B.Fam B.C k hfixK
    obtain ⟨c, hc, xg, hxg, hqxg⟩ := hchartLift g hg
    obtain ⟨xFin, hqFin, hcompFinF, hcompFinC⟩ := nFin_has_finite_only_lift P (-ξ)
    let xK := xg⁻¹ * xFin * xg
    have hqK : P.q xK = k := by
      dsimp [xK, k]
      rw [(P.q).map_mul, (P.q).map_mul, (P.q).map_inv, hqxg, hqFin]
    have hcompCK (w : InfinitePlace F) : P.compC w xK = 1 := by
      dsimp [xK]
      rw [(P.compC w).map_mul, (P.compC w).map_mul, (P.compC w).map_inv, hcompFinC]
      simp
    have hcommK (w : InfinitePlace F) (z : ℂ) : k * P.tc.nS
        (Multiplicative.ofAdd
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) =
        P.tc.nS (Multiplicative.ofAdd
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) * k := by
      have h := finite_only_commutes_with_nInf P xK hcompCK
        (Pi.single w z)
      rw [hqK] at h
      simpa [nInf] using h
    have hderivRight := thetaFamilyDeriv_right_invariant P L.m B.C.theta k hthetaK hcommK
    rcases Q.action L.m with ⟨hRat, -, -⟩
    have hderivLeft := hRat (upperGL ξ)
    have hupper : upperGL ξ * upperGL (-ξ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperGL, Matrix.mul_apply]
    have hrat : P.tc.rat (upperGL ξ) * P.tc.rat (upperGL (-ξ)) = 1 := by
      rw [← (P.tc.rat).map_mul, hupper, map_one]
    have hfactor : nInf P (infEmbA ξ) = P.tc.rat (upperGL ξ) * nFin P (-ξ) := by
      have hnegInf : -infEmbA (-ξ) = infEmbA ξ := by simp
      calc
        nInf P (infEmbA ξ) = 1 * nInf P (infEmbA ξ) := by simp
        _ = (P.tc.rat (upperGL ξ) * P.tc.rat (upperGL (-ξ))) *
            nInf P (infEmbA ξ) := by rw [← hrat]
        _ = P.tc.rat (upperGL ξ) *
            (P.tc.rat (upperGL (-ξ)) * nInf P (infEmbA ξ)) := by rw [mul_assoc]
        _ = P.tc.rat (upperGL ξ) * nFin P (-ξ) := by
          simp [nFin, hnegInf]
    have hadd : nInf P (x + infEmbA ξ) = nInf P (infEmbA ξ) * nInf P x := by
      have hEta :
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + infEmbA ξ) =
            ((0 : ∀ v : S.Sf, v.1.adicCompletion F), infEmbA ξ) +
              ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x) := by
        ext <;> simp [add_comm]
      change P.tc.nS (Multiplicative.ofAdd
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + infEmbA ξ)) = _
      rw [hEta, ofAdd_add, map_mul]
      simp only [nInf]
    obtain ⟨xFinNeg, hqFinNeg, -, hcompFinNegC⟩ := nFin_has_finite_only_lift P (-ξ)
    have hcommFin : nFin P (-ξ) * nInf P x = nInf P x * nFin P (-ξ) := by
      have h := finite_only_commutes_with_nInf P xFinNeg hcompFinNegC x
      simpa [hqFinNeg] using h
    have hbase : nInf P (x + infEmbA ξ) * g =
        P.tc.rat (upperGL ξ) * (nInf P x * g * k) := by
      calc
        nInf P (x + infEmbA ξ) * g =
            (nInf P (infEmbA ξ) * nInf P x) * g := by rw [hadd]
        _ = (P.tc.rat (upperGL ξ) * nFin P (-ξ) * nInf P x) * g := by
            rw [hfactor]
        _ = (P.tc.rat (upperGL ξ) * (nFin P (-ξ) * nInf P x)) * g := by
            exact congrArg (fun z => z * g)
              (mul_assoc (P.tc.rat (upperGL ξ)) (nFin P (-ξ)) (nInf P x))
        _ = (P.tc.rat (upperGL ξ) * (nInf P x * nFin P (-ξ))) * g := by
            exact congrArg (fun z => (P.tc.rat (upperGL ξ) * z) * g) hcommFin
        _ = P.tc.rat (upperGL ξ) * (nInf P x * g * k) := by
            simp [k, mul_assoc]
    have hderiv : thetaFamilyDeriv P L.m B.C.theta
        (nInf P (x + infEmbA ξ) * g) =
        thetaFamilyDeriv P L.m B.C.theta (nInf P x * g) := by
      calc
        thetaFamilyDeriv P L.m B.C.theta (nInf P (x + infEmbA ξ) * g) =
            thetaFamilyDeriv P L.m B.C.theta
              (P.tc.rat (upperGL ξ) * (nInf P x * g * k)) := by rw [hbase]
        _ = thetaFamilyDeriv P L.m B.C.theta (nInf P x * g * k) :=
            hderivLeft (nInf P x * g * k)
        _ = thetaFamilyDeriv P L.m B.C.theta (nInf P x * g) :=
            hderivRight (nInf P x * g)
    change (thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m B.C.theta (nInf P (x + infEmbA ξ) * g) =
      (thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m B.C.theta (nInf P x * g)
    rw [hderiv]
end ArtinPrimitiveRoots.A1.Theta
