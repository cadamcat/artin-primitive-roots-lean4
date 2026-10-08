import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical BoundedContinuousFunction
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem continuedEis_psiC_norm (z : ℂ) : ‖ArtinPrimitiveRoots.A1.psiC z‖ = 1 := by
  unfold ArtinPrimitiveRoots.A1.psiC
  rw [Complex.norm_exp]
  have harg : (-(4 * Real.pi * Complex.I * (z.re : ℂ))).re = 0 := by
    simp
  rw [harg, Real.exp_zero]

private theorem continuedEis_psiInf_norm (ν : F) (x : InfinitePlace F → ℂ) :
    ‖psiInf ν x‖ = 1 := by
  classical
  unfold psiInf
  simp [continuedEis_psiC_norm]

private noncomputable def continuedEis_extendBCF
    (K0 : Set (InfinitePlace F → ℂ)) (f : K0 →ᵇ ℂ) :
    (InfinitePlace F → ℂ) → ℂ :=
  Function.extend Subtype.val (fun x : K0 => f x) (fun _ => 0)

private theorem continuedEis_extendBCF_measurable
    (K0 : Set (InfinitePlace F → ℂ)) (hK0 : MeasurableSet K0) (f : K0 →ᵇ ℂ) :
    Measurable (continuedEis_extendBCF K0 f) := by
  unfold continuedEis_extendBCF
  exact (MeasurableEmbedding.subtype_coe hK0).measurable_extend
    f.continuous.measurable measurable_const

private theorem continuedEis_extendBCF_apply
    (K0 : Set (InfinitePlace F → ℂ)) (f : K0 →ᵇ ℂ)
    (x : InfinitePlace F → ℂ) (hx : x ∈ K0) :
    continuedEis_extendBCF K0 f x = f ⟨x, hx⟩ := by
  unfold continuedEis_extendBCF
  exact Subtype.val_injective.extend_apply (fun q : K0 => f q) (fun _ => 0) ⟨x, hx⟩

private theorem continuedEis_extendBCF_apply_not
    (K0 : Set (InfinitePlace F → ℂ)) (f : K0 →ᵇ ℂ)
    (x : InfinitePlace F → ℂ) (hx : x ∉ K0) :
    continuedEis_extendBCF K0 f x = 0 := by
  unfold continuedEis_extendBCF
  apply Function.extend_apply'
  rintro ⟨q, hq⟩
  exact hx (hq ▸ q.property)

private theorem continuedEis_extendBCF_add
    (K0 : Set (InfinitePlace F → ℂ)) (f g : K0 →ᵇ ℂ) :
    continuedEis_extendBCF K0 (f + g) =
      continuedEis_extendBCF K0 f + continuedEis_extendBCF K0 g := by
  funext x
  classical
  change continuedEis_extendBCF K0 (f + g) x =
    continuedEis_extendBCF K0 f x + continuedEis_extendBCF K0 g x
  by_cases hx : x ∈ K0
  · rw [continuedEis_extendBCF_apply K0 (f + g) x hx,
      continuedEis_extendBCF_apply K0 f x hx,
      continuedEis_extendBCF_apply K0 g x hx]
    simp
  · rw [continuedEis_extendBCF_apply_not K0 (f + g) x hx,
      continuedEis_extendBCF_apply_not K0 f x hx,
      continuedEis_extendBCF_apply_not K0 g x hx]
    simp

private theorem continuedEis_extendBCF_smul
    (K0 : Set (InfinitePlace F → ℂ)) (c : ℂ) (f : K0 →ᵇ ℂ) :
    continuedEis_extendBCF K0 (c • f) = c • continuedEis_extendBCF K0 f := by
  funext x
  classical
  change continuedEis_extendBCF K0 (c • f) x =
    c • continuedEis_extendBCF K0 f x
  by_cases hx : x ∈ K0
  · rw [continuedEis_extendBCF_apply K0 (c • f) x hx,
      continuedEis_extendBCF_apply K0 f x hx]
    rfl
  · rw [continuedEis_extendBCF_apply_not K0 (c • f) x hx,
      continuedEis_extendBCF_apply_not K0 f x hx]
    simp

private theorem continuedEis_extendBCF_norm_le
    (K0 : Set (InfinitePlace F → ℂ)) (f : K0 →ᵇ ℂ)
    (x : InfinitePlace F → ℂ) :
    ‖continuedEis_extendBCF K0 f x‖ ≤ ‖f‖ := by
  classical
  by_cases hx : x ∈ K0
  · rw [continuedEis_extendBCF_apply K0 f x hx]
    exact f.norm_coe_le_norm ⟨x, hx⟩
  · rw [continuedEis_extendBCF_apply_not K0 f x hx]
    simpa using norm_nonneg f

private theorem continuedEis_residueBall_pos_here {ε : ℝ} (hε : ε ≤ 1 / 12) :
    Metric.ball (1 / 6 : ℂ) ε ⊆ {s : ℂ | 0 < s.re} := by
  intro s hs
  have hdist : ‖s - (1 / 6 : ℂ)‖ < ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  have hRe : |s.re - (1 / 6 : ℝ)| < ε := by
    calc
      |s.re - (1 / 6 : ℝ)| = |(s - (1 / 6 : ℂ)).re| := by simp
      _ ≤ ‖s - (1 / 6 : ℂ)‖ := Complex.abs_re_le_norm _
      _ < ε := hdist
  have hlo := (abs_lt.mp hRe).1
  have hεsmall : ε < (1 / 6 : ℝ) := by
    calc
      ε ≤ 1 / 12 := hε
      _ < 1 / 6 := by norm_num
  change 0 < s.re
  linarith

/-- Commute the residue with every bounded measurable torus integral. Pull each spectral
Banach-valued Laurent field back along the fixed torus chart on closure(Pd), form the finite
analytic sum with the coefficient functions, and apply the continuous linear weighted
integral. The statement includes zero-volume sets and needs no period-lattice hypothesis.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:812–823`.
Uses `ContinuedEisTorusCharts` (produced by `continuedEis_torus_charts`), component data,
and `Spec.ContinuedEisenstein.laurent`; no pointwise limit interchange.
Consumed by frozen `exists_continuedEis`. LEAD part. -/
theorem continuedEis_laurent_torus {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) (hcharts : ContinuedEisTorusCharts R) :
    ∀ (g : P.tc.G) (Pd : Set (InfinitePlace F → ℂ)), Bornology.IsBounded Pd →
      MeasurableSet Pd → ∀ ν : F, ∃ Ψ : ℂ → ℂ,
        AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) C.ε) ∧
        Ψ (1 / 6) = torusCoeff P R.theta g Pd ν ∧
        ∀ s ∈ Metric.ball (1 / 6 : ℂ) C.ε, s ≠ 1 / 6 →
          Ψ s = (s - 1 / 6) * torusCoeff P (R.E s) g Pd ν := by
  classical
  intro g Pd hPdBounded hPdMeas ν
  obtain ⟨j, a, p, hpContinuous, hpPositive, hEchart, hThetaChart⟩ := hcharts g
  let K0 : Set (InfinitePlace F → ℂ) := closure Pd
  have hK0 : IsCompact K0 := hPdBounded.isCompact_closure
  have hK0Closed : IsClosed K0 := isClosed_closure
  have hK0Meas : MeasurableSet K0 := hK0Closed.measurableSet
  have hPdSub : Pd ⊆ K0 := subset_closure
  have hPdVol : volume Pd < ⊤ := by
    exact lt_of_le_of_lt (measure_mono hPdSub) hK0.measure_lt_top
  let K : Set (ArtinPrimitiveRoots.A1.Spec.Coord F) := p '' K0
  have hK : IsCompact K := hK0.image hpContinuous
  have hKPositive : K ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    rintro q ⟨x, hx, rfl⟩
    exact hpPositive x
  let pK : C(K0, {q : ArtinPrimitiveRoots.A1.Spec.Coord F // q ∈ K}) :=
    { toFun := fun x => ⟨p x, ⟨x, x.property, rfl⟩⟩
      continuous_toFun := Continuous.subtype_mk
        (hpContinuous.comp continuous_subtype_val) (fun x => ⟨x, x.property, rfl⟩) }
  let pullCLM : (K →ᵇ ℂ) →L[ℂ] (K0 →ᵇ ℂ) :=
    BoundedContinuousFunction.compContinuousCLM ℂ ℂ pK
  let phiData (i : Fin (C.cuspCount j)) :=
    (C.d j i).laurent K hK hKPositive 0 (Fin.elim0)
  let phiField (i : Fin (C.cuspCount j)) := Classical.choose (phiData i)
  have phiField_spec (i : Fin (C.cuspCount j)) :=
    Classical.choose_spec (phiData i)
  let phi (i : Fin (C.cuspCount j)) : ℂ → (K0 →ᵇ ℂ) :=
    fun s => pullCLM (phiField i s)
  have hcast : ((1 / 6 : ℝ) : ℂ) = (1 / 6 : ℂ) := by norm_num
  have hphiAnalytic (i : Fin (C.cuspCount j)) :
      AnalyticOnNhd ℂ (phi i) (Metric.ball (1 / 6 : ℂ) C.ε) := by
    have hcomp := pullCLM.comp_analyticOnNhd (phiField_spec i).1
    have hdomain : Metric.ball ((1 / 6 : ℝ) : ℂ) (C.d j i).ε =
        Metric.ball (1 / 6 : ℂ) C.ε := by
      rw [hcast, C.d_radius j i]
    change AnalyticOnNhd ℂ (pullCLM ∘ phiField i) _
    rw [← hdomain]
    exact hcomp
  have hphiCenter (i : Fin (C.cuspCount j)) (x : K0) :
      phi i (1 / 6) x = (C.d j i).res
        (ArtinPrimitiveRoots.A1.Spec.ptX F (p x)) := by
    change (Classical.choose (phiData i) (1 / 6)) (pK x) = _
    rw [← show (pK x : ArtinPrimitiveRoots.A1.Spec.Coord F) = p x by rfl]
    simpa only [hcast, iteratedFDeriv_zero_apply] using
      (Classical.choose_spec (phiData i)).2.1 (pK x)
  have hphiPunct (i : Fin (C.cuspCount j)) (s : ℂ)
      (hs : s ∈ Metric.ball (1 / 6 : ℂ) C.ε) (hne : s ≠ 1 / 6) (x : K0) :
      phi i s x = (s - 1 / 6) * (C.d j i).E s
        (ArtinPrimitiveRoots.A1.Spec.ptX F (p x)) := by
    have hdomain : Metric.ball ((1 / 6 : ℝ) : ℂ) (C.d j i).ε =
        Metric.ball (1 / 6 : ℂ) C.ε := by
      rw [hcast, C.d_radius j i]
    have hs' : s ∈ Metric.ball ((1 / 6 : ℝ) : ℂ) (C.d j i).ε := by
      rw [hdomain]
      exact hs
    have hne' : s ≠ ((1 / 6 : ℝ) : ℂ) := by simpa [hcast] using hne
    change (Classical.choose (phiData i) s) (pK x) = _
    rw [← show (pK x : ArtinPrimitiveRoots.A1.Spec.Coord F) = p x by rfl]
    simpa only [hcast, iteratedFDeriv_zero_apply] using
      (Classical.choose_spec (phiData i)).2.2 s hs' hne' (pK x)
  have hcoeff (i : Fin (C.cuspCount j)) :
      AnalyticOnNhd ℂ (fun s => C.c j i s • phi i s)
        (Metric.ball (1 / 6 : ℂ) C.ε) := by
    have hc : AnalyticOnNhd ℂ (C.c j i) (Metric.ball (1 / 6 : ℂ) C.ε) :=
      (C.c_analytic j i).mono (continuedEis_residueBall_pos_here C.ε_le)
    exact hc.smul (hphiAnalytic i)
  let H : ℂ → (K0 →ᵇ ℂ) :=
    fun s => a • ∑ i, C.c j i s • phi i s
  have hHAnalytic : AnalyticOnNhd ℂ H (Metric.ball (1 / 6 : ℂ) C.ε) := by
    have hsum : AnalyticOnNhd ℂ (fun s => ∑ i, C.c j i s • phi i s)
        (Metric.ball (1 / 6 : ℂ) C.ε) := by
      apply Finset.analyticOnNhd_fun_sum (Finset.univ : Finset (Fin (C.cuspCount j)))
      intro i hi
      exact hcoeff i
    have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => a)
        (Metric.ball (1 / 6 : ℂ) C.ε) := analyticOnNhd_const
    simpa [H] using hconst.smul hsum

  let weight (f : K0 →ᵇ ℂ) (x : InfinitePlace F → ℂ) : ℂ :=
    continuedEis_extendBCF K0 f x * psiInf (-ν) x
  have hpsiContinuous : Continuous (fun x : InfinitePlace F → ℂ => psiInf (-ν) x) := by
    have hpsiC : Continuous ArtinPrimitiveRoots.A1.psiC := by
      unfold ArtinPrimitiveRoots.A1.psiC
      fun_prop
    unfold psiInf
    apply continuous_finsetProd
    intro w hw
    exact hpsiC.comp (continuous_const.mul (continuous_apply w))
  have hweightMeasurable (f : K0 →ᵇ ℂ) : Measurable (weight f) := by
    exact (continuedEis_extendBCF_measurable K0 hK0Meas f).mul hpsiContinuous.measurable
  have hweightBound (f : K0 →ᵇ ℂ) (x : InfinitePlace F → ℂ) :
      ‖weight f x‖ ≤ ‖f‖ := by
    change ‖continuedEis_extendBCF K0 f x * psiInf (-ν) x‖ ≤ ‖f‖
    rw [norm_mul, continuedEis_psiInf_norm, mul_one]
    exact continuedEis_extendBCF_norm_le K0 f x
  have hweightIntegrable (f : K0 →ᵇ ℂ) :
    Integrable (weight f) (volume.restrict Pd) := by
    apply (Measure.integrableOn_of_bounded (ne_of_lt hPdVol)
      (hweightMeasurable f).aestronglyMeasurable
      (Filter.Eventually.of_forall (hweightBound f))).integrable

  let Llin : (K0 →ᵇ ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun f => Complex.ofReal ((volume Pd).toReal⁻¹) *
      ∫ x, weight f x ∂(volume.restrict Pd)
    map_add' := by
      intro f g
      have hwadd : weight (f + g) = weight f + weight g := by
        funext x
        change continuedEis_extendBCF K0 (f + g) x * psiInf (-ν) x =
          (continuedEis_extendBCF K0 f x * psiInf (-ν) x) +
            (continuedEis_extendBCF K0 g x * psiInf (-ν) x)
        rw [continuedEis_extendBCF_add]
        simp only [Pi.add_apply]
        ring
      change Complex.ofReal ((volume Pd).toReal⁻¹) *
        ∫ x, weight (f + g) x ∂(volume.restrict Pd) = _
      rw [hwadd]
      simp only [Pi.add_apply]
      rw [integral_add (hweightIntegrable f) (hweightIntegrable g)]
      ring
    map_smul' := by
      intro c f
      have hwsmul : weight (c • f) = c • weight f := by
        funext x
        change continuedEis_extendBCF K0 (c • f) x * psiInf (-ν) x =
          c * (continuedEis_extendBCF K0 f x * psiInf (-ν) x)
        rw [continuedEis_extendBCF_smul]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      change Complex.ofReal ((volume Pd).toReal⁻¹) *
        ∫ x, weight (c • f) x ∂(volume.restrict Pd) = _
      rw [hwsmul]
      simp only [Pi.smul_apply]
      change Complex.ofReal ((volume Pd).toReal⁻¹) *
        ∫ x, c • weight f x ∂(volume.restrict Pd) =
          c • (Complex.ofReal ((volume Pd).toReal⁻¹) *
            ∫ x, weight f x ∂(volume.restrict Pd))
      rw [integral_smul]
      simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  }
  have hLbound : ∀ f : K0 →ᵇ ℂ, ‖Llin f‖ ≤ 1 * ‖f‖ := by
    intro f
    let v : ℝ := (volume Pd).toReal
    by_cases hv0 : v = 0
    · simp [Llin, v, hv0]
    · have hvpos : 0 < v := lt_of_le_of_ne (by positivity) (Ne.symm hv0)
      have hIntBound : ‖∫ x in Pd, weight f x ∂volume‖ ≤ ‖f‖ * volume.real Pd :=
        norm_setIntegral_le_of_norm_le_const hPdVol (fun x _ => hweightBound f x)
      have hIntBound' :
          ‖∫ x, weight f x ∂(volume.restrict Pd)‖ ≤ ‖f‖ * v := by
        simpa [v, Measure.real_def] using hIntBound
      dsimp [Llin]
      change ‖Complex.ofReal (v⁻¹) *
        ∫ x, weight f x ∂(volume.restrict Pd)‖ ≤ 1 * ‖f‖
      have hnormInv : ‖Complex.ofReal (v⁻¹)‖ = v⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]
      calc
        _ = v⁻¹ * ‖∫ x, weight f x ∂(volume.restrict Pd)‖ := by
          rw [norm_mul, hnormInv]
        _ ≤ v⁻¹ * (‖f‖ * v) := by
          exact mul_le_mul_of_nonneg_left hIntBound' (le_of_lt (inv_pos.mpr hvpos))
        _ = 1 * ‖f‖ := by field_simp
  let L : (K0 →ᵇ ℂ) →L[ℂ] ℂ := LinearMap.mkContinuous Llin 1 hLbound
  let Ψ : ℂ → ℂ := fun s => L (H s)
  have hHCenter (x : K0) : H (1 / 6) x = a * C.componentTheta j
      (ArtinPrimitiveRoots.A1.Spec.ptX F (p x)) := by
    calc
      H (1 / 6) x = a * (∑ i, C.c j i (1 / 6) * phi i (1 / 6) x) := by
        simp [H, BoundedContinuousFunction.smul_apply, smul_eq_mul]
      _ = a * C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p x)) := by
        unfold ContinuedEisComponents.componentTheta
        apply congrArg (fun z : ℂ => a * z)
        apply Finset.sum_congr rfl
        intro i hi
        rw [hphiCenter]
  have hHPunct (s : ℂ) (hs : s ∈ Metric.ball (1 / 6 : ℂ) C.ε)
      (hne : s ≠ 1 / 6) (x : K0) :
      H s x = (s - 1 / 6) *
        (a * C.componentE j s (ArtinPrimitiveRoots.A1.Spec.ptX F (p x))) := by
    calc
      H s x = a * (∑ i, C.c j i s * phi i s x) := by
        simp [H, BoundedContinuousFunction.smul_apply, smul_eq_mul]
      _ = a * ((s - 1 / 6) * (∑ i, C.c j i s * (C.d j i).E s
          (ArtinPrimitiveRoots.A1.Spec.ptX F (p x)))) := by
        have hsum : (∑ i, C.c j i s * phi i s x) =
            (s - 1 / 6) * (∑ i, C.c j i s * (C.d j i).E s
              (ArtinPrimitiveRoots.A1.Spec.ptX F (p x))) := by
          calc
            _ = ∑ i, C.c j i s * ((s - 1 / 6) * (C.d j i).E s
                (ArtinPrimitiveRoots.A1.Spec.ptX F (p x))) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [hphiPunct i s hs hne x]
            _ = ∑ i, (s - 1 / 6) * (C.c j i s * (C.d j i).E s
                (ArtinPrimitiveRoots.A1.Spec.ptX F (p x))) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = (s - 1 / 6) * _ := by rw [Finset.mul_sum]
        rw [hsum]
      _ = (s - 1 / 6) *
          (a * C.componentE j s (ArtinPrimitiveRoots.A1.Spec.ptX F (p x))) := by
        unfold ContinuedEisComponents.componentE
        ring
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · exact L.comp_analyticOnNhd hHAnalytic
  · change Complex.ofReal ((volume Pd).toReal⁻¹) *
      ∫ x in Pd, weight (H (1 / 6)) x ∂volume = _
    unfold torusCoeff
    congr 1
    apply setIntegral_congr_fun hPdMeas
    intro x hx
    have hxK : x ∈ K0 := hPdSub hx
    change continuedEis_extendBCF K0 (H (1 / 6)) x * psiInf (-ν) x =
      R.theta (nInf P x * g) * psiInf (-ν) x
    rw [continuedEis_extendBCF_apply K0 (H (1 / 6)) x hxK,
      hHCenter ⟨x, hxK⟩, ← hThetaChart x]
  · intro s hs hne
    have hsDomain : s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε := by
      change s ∈ _ ∪ _ ∪ _
      have hs' : s ∈ Metric.ball ((1 / 6 : ℝ) : ℂ) C.ε := by
        simpa [hcast] using hs
      have hne' : s ≠ ((1 / 6 : ℝ) : ℂ) := by simpa [hcast] using hne
      exact Or.inr ⟨hs', by simpa [Set.mem_singleton_iff] using hne'⟩
    change Complex.ofReal ((volume Pd).toReal⁻¹) *
      ∫ x in Pd, weight (H s) x ∂volume = _
    unfold torusCoeff
    calc
      Complex.ofReal ((volume Pd).toReal⁻¹) *
          ∫ x in Pd, weight (H s) x ∂volume =
        Complex.ofReal ((volume Pd).toReal⁻¹) *
          ∫ x in Pd, (s - 1 / 6) * (R.E s (nInf P x * g) * psiInf (-ν) x) ∂volume := by
            congr 1
            apply setIntegral_congr_fun hPdMeas
            intro x hx
            have hxK : x ∈ K0 := hPdSub hx
            change continuedEis_extendBCF K0 (H s) x * psiInf (-ν) x =
              (s - 1 / 6) * (R.E s (nInf P x * g) * psiInf (-ν) x)
            rw [continuedEis_extendBCF_apply K0 (H s) x hxK,
              hHPunct s hs hne ⟨x, hxK⟩, ← hEchart s hsDomain x]
            ring
      _ = (s - 1 / 6) *
          (Complex.ofReal ((volume Pd).toReal⁻¹) *
            ∫ x in Pd, R.E s (nInf P x * g) * psiInf (-ν) x ∂volume) := by
            rw [integral_const_mul]
            ring
      _ = (s - 1 / 6) * torusCoeff P (R.E s) g Pd ν := by
        simp [torusCoeff]

end ArtinPrimitiveRoots.A1.Theta
