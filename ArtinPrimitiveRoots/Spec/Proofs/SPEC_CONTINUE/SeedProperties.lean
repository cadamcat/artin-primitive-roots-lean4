import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.SeedScaling
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.All
import ArtinPrimitiveRoots.Spec.Geometry

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

open ArtinPrimitiveRoots.A1.Spec

namespace ArtinPrimitiveRoots.Proofs.spec_continue_p

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem specSeed_posSet_open : IsOpen (posSet F) := by
  rw [posSet, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro w
  have hc : Continuous (fun p : Coord F => (p w).2) := by fun_prop
  exact IsOpen.preimage hc (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

theorem specCoordsX_continuous : Continuous (coordsX F) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩ := G1_h3_basics (F := F)
  obtain ⟨e, _, heinv⟩ := hchart
  have h := continuous_subtype_val.comp e.symm.continuous
  exact h.congr (fun z => heinv z)

theorem specPtX_coordsX (z : X F) : ptX F (coordsX F z) = z := by
  obtain ⟨_, _, _, _, _, _, _, h, _, _, _, _⟩ := G1_h3_basics (F := F)
  exact h z

theorem specCoordsX_mem_pos (z : X F) : coordsX F z ∈ posSet F := by
  intro w
  change 0 < height (z w)
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private theorem specScalePower_inv_analytic (c : ℝ) (hc : 0 < c) :
    AnalyticOnNhd ℂ (fun s : ℂ => (c : ℂ) ^ (-(1 + 2 * s))) Set.univ := by
  have hcnz : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  intro s hs
  have hfun : (fun w : ℂ => (c : ℂ) ^ (-(1 + 2 * w))) =
      fun w => Complex.exp (Complex.log (c : ℂ) * (-(1 + 2 * w))) := by
    funext w
    exact Complex.cpow_def_of_ne_zero hcnz _
  rw [hfun]
  fun_prop

private theorem specScalePower_inv_mul (c : ℝ) (hc : 0 < c) (s : ℂ) :
    (c : ℂ) ^ (-(1 + 2 * s)) * (c : ℂ) ^ (1 + 2 * s) = 1 := by
  have hcnz : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  rw [Complex.cpow_def_of_ne_zero hcnz, Complex.cpow_def_of_ne_zero hcnz,
    ← Complex.exp_add]
  have hsum : Complex.log (c : ℂ) * (-(1 + 2 * s)) +
      Complex.log (c : ℂ) * (1 + 2 * s) = 0 := by ring
  rw [hsum]
  simp

/-- The smooth cutoff seed is integrable on every compact subset of X. -/
theorem specSeed_integrableOn_compact (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : MeasureTheory.IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (A : ℝ) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ)
    (hseed : ∀ s, IsSmoothX F (eisSeed F Γ σ τ s)) (s : ℂ)
    (W : Set (X F)) (hW : IsCompact W) :
    IntegrableOn (eisSeed F Γ σ τ s) W (volX F) := by
  have hcoord : ContDiffOn ℝ ∞
      (fun p => eisSeed F Γ σ τ s (ptX F p)) (posSet F) := hseed s
  have hcoordCont : ContinuousOn
      (fun p => eisSeed F Γ σ τ s (ptX F p)) (posSet F) := hcoord.continuousOn
  have hcoordsCont : ContinuousOn (coordsX F) W :=
    specCoordsX_continuous.continuousOn
  have hmaps : Set.MapsTo (coordsX F) W (posSet F) := fun z hz => specCoordsX_mem_pos z
  have hcomp : ContinuousOn
      (fun z => eisSeed F Γ σ τ s (ptX F (coordsX F z))) W :=
    hcoordCont.comp hcoordsCont hmaps
  have hEq : Set.EqOn (eisSeed F Γ σ τ s)
      (fun z => eisSeed F Γ σ τ s (ptX F (coordsX F z))) W := by
    intro z hz
    change eisSeed F Γ σ τ s z = eisSeed F Γ σ τ s (ptX F (coordsX F z))
    rw [specPtX_coordsX]
  have hcont : ContinuousOn (eisSeed F Γ σ τ s) W := hcomp.congr hEq
  letI : T2Space H3 := OAI.CubicEisenstein.upperCoordinatesHomeomorph.t2Space
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchartX⟩ := G1_h3_basics (F := F)
  obtain ⟨eChartX, _, _⟩ := hchartX
  letI : T2Space (X F) := eChartX.t2Space
  letI : IsFiniteMeasureOnCompacts (volX F) :=
    ⟨(G3_volume (F := F)).2.2.1⟩
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  exact @ContinuousOn.integrableOn_compact' (X F) ℂ
    (inferInstance : MeasurableSpace (X F)) (inferInstance : TopologicalSpace (X F))
    (inferInstance : NormedAddCommGroup ℂ) (volX F)
    (inferInstance : OpensMeasurableSpace (X F)) W (eisSeed F Γ σ τ s)
    (inferInstance : IsFiniteMeasureOnCompacts (volX F)) hW hW.measurableSet hcont

theorem l2Lift_integrableOn_compact (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : MeasureTheory.IsFundamentalDomain Γ D (volX F))
    (u : L2Space F D) (W : Set (X F)) (hW : IsCompact W) :
    IntegrableOn (l2Lift F Γ D u) W (volX F) := by
  obtain ⟨T, _, hrep⟩ := localLiftCLM Γ D hD W hW
  let μW := (volX F).restrict W
  have hWmeasure : volX F W < ⊤ := (G3_volume (F := F)).2.2.1 W hW
  have hfinite : μW Set.univ < ⊤ := by simpa [μW] using hWmeasure
  letI : IsFiniteMeasure μW := ⟨hfinite⟩
  have hLp : MemLp (fun z => l2Lift F Γ D u z) 2 μW := by
    have hT : MemLp (T u) 2 μW := Lp.memLp (T u)
    have hLiftAES : AEStronglyMeasurable (l2Lift F Γ D u) μW :=
      ((T1_l2 Γ D hD).1 u).1.restrict
    apply hT.congr_enorm hLiftAES
    filter_upwards [hrep u] with z hz
    rw [hz]
  have hL1 : MemLp (fun z => l2Lift F Γ D u z) 1 μW :=
    hLp.mono_exponent (by norm_num)
  exact memLp_one_iff_integrable.mp hL1

theorem smoothing_seed_isSmooth (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : MeasureTheory.IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (k₀ τ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (A : ℝ) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (hτ : IsCuspCutoff A τ)
    (hseed : ∀ s, IsSmoothX F (eisSeed F Γ σ τ s)) (s : ℂ) :
    IsSmoothX F (smoothingOperator F k₀ (eisSeed F Γ σ τ s)) := by
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  have hseedContCoord : ContinuousOn
      (fun p => eisSeed F Γ σ τ s (ptX F p)) (posSet F) :=
    (hseed s).continuousOn
  have hseedCont : Continuous (eisSeed F Γ σ τ s) := by
    apply continuousOn_univ.mp
    have hcomp : ContinuousOn (fun z => eisSeed F Γ σ τ s (ptX F (coordsX F z))) Set.univ :=
      hseedContCoord.comp (specCoordsX_continuous.continuousOn) (fun z _ => specCoordsX_mem_pos z)
    have hEq : Set.EqOn (eisSeed F Γ σ τ s)
        (fun z => eisSeed F Γ σ τ s (ptX F (coordsX F z))) Set.univ := by
      intro z hz
      change eisSeed F Γ σ τ s z = eisSeed F Γ σ τ s (ptX F (coordsX F z))
      rw [specPtX_coordsX]
    exact hcomp.congr hEq
  have hmeas : AEStronglyMeasurable (eisSeed F Γ σ τ s) (volX F) :=
    hseedCont.measurable.aestronglyMeasurable
  intro p hp
  let K : Set (Coord F) := {p}
  have hK : IsCompact K := isCompact_singleton
  have hKpos : K ⊆ posSet F := by
    intro q hq
    have : q = p := by simpa [K] using hq
    subst q
    exact hp
  obtain ⟨U, W, hUopen, hKsubset, hUpos, hW, hcontrol⟩ :=
    radialKernel_compact_control k₀ hkSmooth hkSupport K hK hKpos
  have hInt := specSeed_integrableOn_compact Γ D hD σ A hA hsep τ hτ hseed s W hW
  have hdiff := param_deriv_integral_formula k₀ U hUopen hUpos W hW hcontrol
    (eisSeed F Γ σ τ s) hmeas hInt
  have hpU : p ∈ U := hKsubset (by simp [K])
  exact (hdiff.1.contDiffAt (hUopen.mem_nhds hpU)).contDiffWithinAt

theorem smoothing_seed_add_lift_isSmooth (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : MeasureTheory.IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (k₀ τ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (A : ℝ) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (hτ : IsCuspCutoff A τ)
    (hseed : ∀ s, IsSmoothX F (eisSeed F Γ σ τ s))
    (u : L2Space F D) (s : ℂ) :
    IsSmoothX F (smoothingOperator F k₀
      (fun z => eisSeed F Γ σ τ s z + l2Lift F Γ D u z)) := by
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  have hseedCoord : ContinuousOn (fun p => eisSeed F Γ σ τ s (ptX F p)) (posSet F) :=
    (hseed s).continuousOn
  have hseedCont : Continuous (eisSeed F Γ σ τ s) := by
    apply continuousOn_univ.mp
    have hmaps : Set.MapsTo (coordsX F) Set.univ (posSet F) := by
      intro z hz
      exact specCoordsX_mem_pos z
    have hcomp : ContinuousOn (fun z => eisSeed F Γ σ τ s (ptX F (coordsX F z))) Set.univ :=
      hseedCoord.comp
        (specCoordsX_continuous.continuousOn : ContinuousOn (coordsX F) Set.univ) hmaps
    have hEq : Set.EqOn (eisSeed F Γ σ τ s)
        (fun z => eisSeed F Γ σ τ s (ptX F (coordsX F z))) Set.univ := by
      intro z hz
      change eisSeed F Γ σ τ s z = eisSeed F Γ σ τ s (ptX F (coordsX F z))
      rw [specPtX_coordsX]
    exact hcomp.congr hEq
  have hmeas : AEStronglyMeasurable
      (fun z => eisSeed F Γ σ τ s z + l2Lift F Γ D u z) (volX F) := by
    exact hseedCont.measurable.aestronglyMeasurable.add ((T1_l2 Γ D hD).1 u).1
  intro p hp
  let K : Set (Coord F) := {p}
  have hK : IsCompact K := isCompact_singleton
  have hKpos : K ⊆ posSet F := by
    intro q hq
    have : q = p := by simpa [K] using hq
    subst q
    exact hp
  obtain ⟨U, W, hUopen, hKsubset, hUpos, hW, hcontrol⟩ :=
    radialKernel_compact_control k₀ hkSmooth hkSupport K hK hKpos
  have hseedInt := specSeed_integrableOn_compact Γ D hD σ A hA hsep τ hτ hseed s W hW
  have hliftInt := l2Lift_integrableOn_compact Γ D hD u W hW
  have hInt : IntegrableOn
      (fun z => eisSeed F Γ σ τ s z + l2Lift F Γ D u z) W (volX F) :=
    hseedInt.add hliftInt
  have hdiff := param_deriv_integral_formula k₀ U hUopen hUpos W hW hcontrol
    (fun z => eisSeed F Γ σ τ s z + l2Lift F Γ D u z) hmeas hInt
  have hpU : p ∈ U := hKsubset (by simp [K])
  exact (hdiff.1.contDiffAt (hUopen.mem_nhds hpU)).contDiffWithinAt

set_option maxHeartbeats 1000000 in
/-- The cutoff seed remains smooth, invariant and entire on compact coordinate sets even when
the supplied cutoff scale is below the normalization used by `E5_seed`. -/
theorem specSeed_smooth_analytic (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : MeasureTheory.IsFundamentalDomain Γ D (volX F)) (σ : SL(2,F))
    (A : ℝ) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) :
    (∀ s, IsSmoothX F (eisSeed F Γ σ τ s) ∧
      IsGammaInvariant F Γ (eisSeed F Γ σ τ s)) ∧
    (∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
      ∀ n : ℕ, ∀ v : Fin n → Coord F,
        ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
          ∀ s p, Φ s p = iteratedFDeriv ℝ n
            (fun q => eisSeed F Γ σ τ s (ptX F q)) p.1 v) := by
  obtain ⟨t, ht, hlarge⟩ := exists_specVerticalScale_large (F := F) A hA
  let c : ℝ := specVerticalScaleFactor t
  have hc : 0 < c := by
    dsimp [c, specVerticalScaleFactor]
    apply Finset.prod_pos
    intro w hw
    apply Complex.normSq_pos.mpr
    have hEmbed : w.embedding t ≠ 0 := by
      intro h
      exact ht (w.embedding.injective (by simpa using h))
    exact hEmbed
  have hlarge' : 1 ≤ c * A := by
    simpa [c, mul_comm] using hlarge
  let σ' : SL(2,F) := σ * specVerticalScale t ht
  let τ' : ℝ → ℝ := specScaledCuspCutoff c τ
  have hτ' : IsCuspCutoff (c * A) τ' := by
    exact isCuspCutoff_specScaled A c hc τ hτ
  have hsep' : ∀ γ γ' : Γ, ∀ z : X F,
      c * A ≤ normHeight F (σ'⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      c * A ≤ normHeight F (σ'⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ' := by
    intro γ γ' z hγ hγ'
    exact specScaledSeparation Γ σ A hsep t ht hc γ γ' z (by simpa [σ', c] using hγ)
      (by simpa [σ', c] using hγ')
  have hE5 := E5_seed Γ D hD σ' (c * A) (c * A) hlarge' le_rfl hsep' τ' hτ'
  have hseed' : ∀ s, IsSmoothX F (eisSeed F Γ σ' τ' s) ∧
      IsGammaInvariant F Γ (eisSeed F Γ σ' τ' s) := fun s =>
    ⟨(hE5.2.1 s).1, (hE5.2.1 s).2.1⟩
  have hE5analytic := hE5.2.2.2.2.1
  have hβanalytic := specScalePower_inv_analytic c hc
  have hβα (s : ℂ) :
      (c : ℂ) ^ (-(1 + 2 * s)) * (c : ℂ) ^ (1 + 2 * s) = 1 :=
    specScalePower_inv_mul c hc s
  have hseedRel (s : ℂ) (z : X F) :
      eisSeed F Γ σ τ s z =
        (c : ℂ) ^ (-(1 + 2 * s)) * eisSeed F Γ σ' τ' s z := by
    have hscaled := eisSeed_specScaled Γ σ τ c hc t ht rfl s z
    calc
      eisSeed F Γ σ τ s z = 1 * eisSeed F Γ σ τ s z := by simp
      _ = ((c : ℂ) ^ (-(1 + 2 * s)) * (c : ℂ) ^ (1 + 2 * s)) *
          eisSeed F Γ σ τ s z := by rw [hβα]
      _ = (c : ℂ) ^ (-(1 + 2 * s)) *
          ((c : ℂ) ^ (1 + 2 * s) * eisSeed F Γ σ τ s z) := by ring
      _ = (c : ℂ) ^ (-(1 + 2 * s)) * eisSeed F Γ σ' τ' s z := by rw [← hscaled]
  refine ⟨?_, ?_⟩
  · intro s
    refine ⟨?_, ?_⟩
    · change ContDiffOn ℝ ∞ (fun p => eisSeed F Γ σ τ s (ptX F p)) (posSet F)
      have hfun : (fun p => eisSeed F Γ σ τ s (ptX F p)) =
          fun p => (c : ℂ) ^ (-(1 + 2 * s)) *
            eisSeed F Γ σ' τ' s (ptX F p) := by
        funext p
        exact hseedRel s (ptX F p)
      rw [hfun]
      simpa [smul_eq_mul] using (hseed' s).1.const_smul ((c : ℂ) ^ (-(1 + 2 * s)))
    · intro γ hγ z
      calc
        eisSeed F Γ σ τ s ((γ : SL(2,𝓞 F)) • z) =
            (c : ℂ) ^ (-(1 + 2 * s)) *
              eisSeed F Γ σ' τ' s ((γ : SL(2,𝓞 F)) • z) := hseedRel s _
        _ = (c : ℂ) ^ (-(1 + 2 * s)) * eisSeed F Γ σ' τ' s z := by
          rw [(hseed' s).2 γ hγ z]
        _ = eisSeed F Γ σ τ s z := (hseedRel s z).symm
  · intro K hK hKpos n v
    obtain ⟨Φ, hΦ, hΦvalue⟩ := hE5analytic K hK hKpos n v
    let Ψ : ℂ → (K →ᵇ ℂ) := fun s => (c : ℂ) ^ (-(1 + 2 * s)) • Φ s
    have hΨ : AnalyticOnNhd ℂ Ψ Set.univ := by
      simpa [Ψ] using hβanalytic.smul hΦ
    refine ⟨Ψ, hΨ, ?_⟩
    intro s p
    have hpos : p.1 ∈ posSet F := hKpos p.2
    have hcont : ContDiffAt ℝ ∞
        (fun q => eisSeed F Γ σ' τ' s (ptX F q)) p.1 :=
      (hseed' s).1.contDiffAt (specSeed_posSet_open.mem_nhds hpos)
    have hcontN : ContDiffAt ℝ n
        (fun q => eisSeed F Γ σ' τ' s (ptX F q)) p.1 := by
      exact hcont.of_le (by simp)
    have hfun : (fun q => eisSeed F Γ σ τ s (ptX F q)) =
        fun q => (c : ℂ) ^ (-(1 + 2 * s)) •
          eisSeed F Γ σ' τ' s (ptX F q) := by
      funext q
      simpa only [smul_eq_mul] using hseedRel s (ptX F q)
    calc
      Ψ s p = (c : ℂ) ^ (-(1 + 2 * s)) * Φ s p := by simp [Ψ, smul_eq_mul]
      _ = (c : ℂ) ^ (-(1 + 2 * s)) *
          iteratedFDeriv ℝ n (fun q => eisSeed F Γ σ' τ' s (ptX F q)) p.1 v := by
        rw [hΦvalue]
      _ = iteratedFDeriv ℝ n (fun q => eisSeed F Γ σ τ s (ptX F q)) p.1 v := by
        have hder := iteratedFDeriv_const_smul_apply'
          (𝕜 := ℝ) (i := n) (a := (c : ℂ) ^ (-(1 + 2 * s)))
          (f := fun q => eisSeed F Γ σ' τ' s (ptX F q)) (x := p.1) hcontN
        have hderV : iteratedFDeriv ℝ n
            (fun q => (c : ℂ) ^ (-(1 + 2 * s)) •
              eisSeed F Γ σ' τ' s (ptX F q)) p.1 v =
            (c : ℂ) ^ (-(1 + 2 * s)) *
              iteratedFDeriv ℝ n
                (fun q => eisSeed F Γ σ' τ' s (ptX F q)) p.1 v := by
          simpa [smul_eq_mul] using congrArg (fun D => D v) hder
        calc
          (c : ℂ) ^ (-(1 + 2 * s)) *
              iteratedFDeriv ℝ n
                (fun q => eisSeed F Γ σ' τ' s (ptX F q)) p.1 v =
            iteratedFDeriv ℝ n
              (fun q => (c : ℂ) ^ (-(1 + 2 * s)) •
                eisSeed F Γ σ' τ' s (ptX F q)) p.1 v := hderV.symm
          _ = iteratedFDeriv ℝ n (fun q => eisSeed F Γ σ τ s (ptX F q)) p.1 v := by
            rw [← hfun]

end ArtinPrimitiveRoots.Proofs.spec_continue_p
