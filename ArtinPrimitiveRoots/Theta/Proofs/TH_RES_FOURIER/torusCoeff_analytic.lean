import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.adapted_domain_measurable_representative
import ArtinPrimitiveRoots.Proofs.th_res_fourier_a.AnalyticIntegral
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_uniform_level_components
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_reconstruction
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_torus_charts
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_series_analytic

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical BoundedContinuousFunction
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The continued torus integral is analytic on a possibly smaller continuation domain.
The radius is chosen after g and Pd; pointwise E_analytic alone is not an integration theorem.
Uses red_decompose, P-SPEC compact-valued continuation, and analytic uniqueness.
Feeds theta_constantTerm and analytic_residue_unique applications in Fourier assembly. -/
theorem torusCoeff_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0)
    (R : FourierResidueData sec) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : FourierIdealFix sec g 𝔞) (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (hb : Bornology.IsBounded Pd) (hm : MeasurableSet Pd) (ν : F) :
    ∃ η : ℝ, 0 < η ∧ η ≤ R.ε ∧ η ≤ (1 / 6 : ℝ) ∧
      AnalyticOnNhd ℂ (fun s => torusCoeff P (R.E s) g Pd ν)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let I : ContinuedEisInput P G := {
    sec := sec
    T0 := T0
    T0_eq := hFam.T0_eq
    fC_sph := hFam.fC_sph
    f_analytic := hFam.f_analytic
    level := hFam.level }
  obtain ⟨C⟩ := continuedEis_uniform_level_components I
  let R' : ContinuedEisReconstruction C := Classical.choice
    (continuedEis_component_reconstruction C)
  have hcharts : ContinuedEisTorusCharts R' := continuedEis_torus_charts R'
  obtain ⟨hseries, hEanalytic, _⟩ := continuedEis_series_analytic R'
  let η := min R.ε C.ε
  have hηpos : 0 < η := lt_min R.ε_pos C.ε_pos
  have hηR : η ≤ R.ε := min_le_left _ _
  have hηC : η ≤ C.ε := min_le_right _ _
  have hηsix : η ≤ (1 / 6 : ℝ) := by
    exact hηC.trans (C.ε_le.trans (by norm_num))
  have hdom_mono {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
      ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε₁ ⊆
        ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε₂ := by
    intro s hs
    simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hs ⊢
    rcases hs with (hs | hs) | hs
    · exact Or.inl (Or.inl hs)
    · exact Or.inl (Or.inr hs)
    · exact Or.inr ⟨Metric.ball_subset_ball hε hs.1, hs.2⟩
  have hball_subset : Metric.ball (5 / 2 : ℂ) (1 / 2) ⊆
      ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η := by
    intro s hs
    simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union]
    exact Or.inl (Or.inr hs)
  have hEeq : ∀ s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η,
      R.E s = R'.E s := by
    intro s hs
    funext h
    have hanR : AnalyticOnNhd ℂ (fun z => R.E z h)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) :=
      (R.E_analytic h).mono (hdom_mono hηR)
    have hanR' : AnalyticOnNhd ℂ (fun z => R'.E z h)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) :=
      (hEanalytic h).mono (hdom_mono hηC)
    have hseriesEq : Set.EqOn (fun z => R.E z h) (fun z => R'.E z h)
        (Metric.ball (5 / 2 : ℂ) (1 / 2)) := by
      intro z hz
      change R.E z h = R'.E z h
      rw [R.E_series z hz h, hseries z hz h]
    have hanchor : (5 / 2 : ℂ) ∈ Metric.ball (5 / 2 : ℂ) (1 / 2) := by simp
    have hEqOn : Set.EqOn (fun z => R.E z h) (fun z => R'.E z h)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
      exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        (𝕜 := ℂ) (f := fun z => R.E z h) (g := fun z => R'.E z h)
        hanR hanR'
        (ArtinPrimitiveRoots.A1.Spec.isPreconnected_contDomain (1 / 6) η
          (by norm_num) (by norm_num) hηpos)
        (hball_subset hanchor)
        (hseriesEq.eventuallyEq_of_mem
          (Metric.isOpen_ball.mem_nhds hanchor))
    exact hEqOn hs
  obtain ⟨Q, hQm, hQb, _, hQeq⟩ :=
    adapted_domain_measurable_representative 𝔞 Pd hPd hb
  let μQ : Measure Q := Measure.comap Subtype.val volume
  have hμQfin : μQ Set.univ < ⊤ := by
    change (Measure.comap Subtype.val volume) Set.univ < ⊤
    rw [comap_subtype_coe_apply hQm]
    simpa using hQb.measure_lt_top
  letI : IsFiniteMeasure μQ := ⟨hμQfin⟩
  obtain ⟨j, a, p, hpcont, hppos, hOrbit, _⟩ := hcharts g
  let K : Set (ArtinPrimitiveRoots.A1.Spec.Coord F) := p '' closure Q
  have hKcompact : IsCompact K := (hQb.isCompact_closure).image hpcont
  have hKpos : K ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    rintro y ⟨x, hx, rfl⟩
    exact hppos x
  let pQ : C(Q, K) := {
    toFun := fun x => ⟨p x, ⟨x.1, subset_closure x.2, rfl⟩⟩
    continuous_toFun := by fun_prop }
  let ψQ := psiInfBounded Q (-ν)
  let φ : ∀ i : Fin (C.cuspCount j), ℂ → K →ᵇ ℂ := fun i =>
    Classical.choose ((C.d j i).E_analytic K hKcompact hKpos 0 Fin.elim0)
  have hφ := fun i => Classical.choose_spec
    ((C.d j i).E_analytic K hKcompact hKpos 0 Fin.elim0)
  have hηposDomain :
      ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    have hη12 : η ≤ (1 / 12 : ℝ) := hηC.trans C.ε_le
    have hs' := hs
    simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hs'
    rcases hs' with (hs' | hs') | hs'
    · exact hs'.1
    · have hb' := Metric.mem_ball.mp hs'
      have habs : |s.re - (5 / 2 : ℝ)| < (1 / 2 : ℝ) := by
        have hle := Complex.abs_re_le_norm (s - (5 / 2 : ℂ))
        rw [dist_eq_norm] at hb'
        simpa [Complex.sub_re] using lt_of_le_of_lt hle hb'
      have hlow := (abs_lt.mp habs).1
      change 0 < s.re
      nlinarith [hlow]
    · have hb' := Metric.mem_ball.mp hs'.1
      have habs : |s.re - (1 / 6 : ℝ)| < (1 / 12 : ℝ) := by
        have hle := Complex.abs_re_le_norm (s - (1 / 6 : ℂ))
        rw [dist_eq_norm] at hb'
        exact lt_of_le_of_lt (by simpa [Complex.sub_re] using hle)
          (lt_of_lt_of_le hb' hη12)
      have hlow := (abs_lt.mp habs).1
      change 0 < s.re
      nlinarith [hlow]
  let u : ℂ → K →ᵇ ℂ := fun s =>
    ∑ i : Fin (C.cuspCount j), (a * C.c j i s) • φ i s
  have hu : AnalyticOnNhd ℂ u
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
    change AnalyticOnNhd ℂ
      (fun s => ∑ i : Fin (C.cuspCount j), (a * C.c j i s) • φ i s) _
    apply Finset.analyticOnNhd_fun_sum
    intro i hi
    have hc : AnalyticOnNhd ℂ (fun s => a * C.c j i s)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
      have hc0 := (C.c_analytic j i).mono hηposDomain
      have hconsta : AnalyticOnNhd ℂ (fun _ : ℂ => a)
          (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by fun_prop
      exact hconsta.mul hc0
    have hφana : AnalyticOnNhd ℂ (φ i)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
      have hdom : ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η ⊆
          ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) (C.d j i).ε :=
        hdom_mono (by rw [C.d_radius j i]; exact hηC)
      simpa [φ, C.d_radius j i] using (hφ i).1.mono hdom
    exact hc.smul hφana
  let base : ℂ → ℂ := fun s => boundedIntegralCLM μQ
    (boundedMulRightCLM ψQ
      (BoundedContinuousFunction.compContinuousCLM ℂ ℂ pQ (u s)))
  have hbase : AnalyticOnNhd ℂ base
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
    simpa [base] using analytic_boundedIntegral μQ pQ ψQ u hu
  let normFactor : ℂ := (((volume Q).toReal⁻¹ : ℝ) : ℂ)
  let fambient (s : ℂ) (x : InfinitePlace F → ℂ) : ℂ :=
    if hx : p x ∈ K then u s ⟨p x, hx⟩ * psiInf (-ν) x else 0
  have hpQ_mem (x : Q) : p x ∈ K :=
    ⟨x.1, subset_closure x.2, rfl⟩
  have hu_eval (s : ℂ) (hs : s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η)
      (x : Q) : u s ⟨p x, hpQ_mem x⟩ =
        a * C.componentE j s (ArtinPrimitiveRoots.A1.Spec.ptX F (p x)) := by
    have hsumEval :
        (∑ i : Fin (C.cuspCount j), (a * C.c j i s) • φ i s)
            ⟨p x, hpQ_mem x⟩ =
          ∑ i : Fin (C.cuspCount j),
            (a * C.c j i s) * φ i s ⟨p x, hpQ_mem x⟩ := by
      change BoundedContinuousFunction.evalCLM ℂ ⟨p x, hpQ_mem x⟩
        (∑ i : Fin (C.cuspCount j), (a * C.c j i s) • φ i s) = _
      rw [map_sum]
      simp [BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
    rw [show u s ⟨p x, hpQ_mem x⟩ =
        (∑ i : Fin (C.cuspCount j), (a * C.c j i s) • φ i s)
          ⟨p x, hpQ_mem x⟩ by rfl, hsumEval]
    simp only [ContinuedEisComponents.componentE]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hsC : s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) (C.d j i).ε := by
      exact hdom_mono (by rw [C.d_radius j i]; exact hηC) hs
    have hEval := (hφ i).2 s hsC ⟨p x, hpQ_mem x⟩
    rw [hEval]
    rw [iteratedFDeriv_zero_apply]
    ring
  have hfambient (s : ℂ) (hs : s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η)
      (x : InfinitePlace F → ℂ) (hx : x ∈ Q) :
      fambient s x = R'.E s (nInf P x * g) * psiInf (-ν) x := by
    have hpK : p x ∈ K := ⟨x, subset_closure hx, rfl⟩
    dsimp [fambient]
    rw [dif_pos hpK, hu_eval s hs ⟨x, hx⟩,
      ← hOrbit s (hdom_mono hηC hs) x]
  have hIntegral (s : ℂ)
      (hs : s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) :
      base s = ∫ x in Q, R'.E s (nInf P x * g) * psiInf (-ν) x := by
    change boundedIntegralCLM μQ
      (boundedMulRightCLM ψQ
        (BoundedContinuousFunction.compContinuousCLM ℂ ℂ pQ (u s))) = _
    rw [boundedIntegralCLM_apply, boundedMulRightCLM_apply]
    change (∫ x : Q, (u s).compContinuous pQ x * ψQ x ∂μQ) = _
    have hsubtype :
        (∫ x : Q, ((u s).compContinuous pQ) x * ψQ x ∂μQ) =
          ∫ x : Q, fambient s x ∂μQ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [pQ, ψQ, psiInfBounded, fambient, hpQ_mem]
    rw [hsubtype, integral_subtype_comap hQm (fambient s)]
    apply setIntegral_congr_ae hQm
    exact Filter.Eventually.of_forall fun x hx => hfambient s hs x hx
  have hsmall : AnalyticOnNhd ℂ
      (fun s => torusCoeff P (R'.E s) g Q (ν))
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
    have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => normFactor)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by fun_prop
    have hprod := hconst.mul hbase
    have hEqOn : Set.EqOn (fun s => normFactor * base s)
        (fun s => torusCoeff P (R'.E s) g Q ν)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
      intro s hs
      unfold torusCoeff normFactor
      change (((volume Q).toReal⁻¹ : ℝ) : ℂ) * base s =
        (((volume Q).toReal⁻¹ : ℝ) : ℂ) *
          ∫ x in Q, R'.E s (nInf P x * g) * psiInf (-ν) x
      rw [hIntegral s hs]
    exact hprod.congr (ArtinPrimitiveRoots.A1.Spec.isOpen_contDomain (1 / 6) η) hEqOn
  have htarget : AnalyticOnNhd ℂ
      (fun s => torusCoeff P (R.E s) g Pd (ν))
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
    apply hsmall.congr (ArtinPrimitiveRoots.A1.Spec.isOpen_contDomain (1 / 6) η)
    intro s hs
    change torusCoeff P (R'.E s) g Q ν = torusCoeff P (R.E s) g Pd ν
    have hE := hEeq s hs
    rw [← hE]
    unfold torusCoeff
    rw [measure_congr hQeq, setIntegral_congr_set hQeq]
  refine ⟨η, hηpos, hηR, hηsix, htarget⟩

end ArtinPrimitiveRoots.A1.Theta
