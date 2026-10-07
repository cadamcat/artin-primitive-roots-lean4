import ArtinPrimitiveRoots.Hecke.Theta.RayMellinWeight

/-!
Real Mellin agreement for the ray theta. The Gaussian orbit evaluation and unit-box basis
change are AINTLIB's `CompletedZeta/MellinAgreement.lean` (Chris Birkbeck, Apache-2.0).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory MeasureTheory
open NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units NumberField.Units.dirichletUnitTheorem DedekindResidue
open scoped NumberField nonZeroDivisors Real ENNReal NNReal Classical

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

theorem rayThetaTail_eq_theta_sub_delta [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    rayThetaTail m J hcop (heckeWeights K t u) =
      rayTheta m J hcop (heckeWeights K t u) - (if m.finitePart = 0 then 1 else 0) := by
  classical
  have hne : (Finset.univ : Finset (InfinitePlace K)).Nonempty := Finset.univ_nonempty
  let a := Finset.univ.inf' hne (heckeWeights K t u)
  have ha : 0 < a := (Finset.lt_inf'_iff hne).mpr (fun w _ => heckeWeights_pos K ht u w)
  have hca : ∀ w : InfinitePlace K, a ≤ heckeWeights K t u w :=
    fun w => Finset.inf'_le _ (Finset.mem_univ w)
  have hplace : ∀ i : index K, a ≤ placeWeights K (heckeWeights K t u) i := by
    rintro (w | ⟨w, j⟩) <;> exact hca w
  rw [rayTheta_eq_delta_add_tail m J hcop (heckeWeights K t u) ha hplace]
  ring

theorem rayThetaTail_heckeWeights_periodic [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    {t : ℝ} (ht : 0 < t) (v : logSpace K) (u : (𝓞 K)ˣ) :
    rayThetaTail m J hcop (heckeWeights K t (v + logEmbedding K (Additive.ofMul u))) =
      rayThetaTail m J hcop (heckeWeights K t v) := by
  rw [rayThetaTail_eq_theta_sub_delta m J hcop ht,
    rayThetaTail_eq_theta_sub_delta m J hcop ht, rayTheta_heckeWeights_periodic]

theorem ofReal_rayG_sub_const [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (rayG m J hcop t - rayPrimalConstant m) =
      ENNReal.ofReal ((torsionOrder K : ℝ)⁻¹) *
        ∫⁻ u in ZSpan.fundamentalDomain
          ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
          ENNReal.ofReal (rayThetaTail m J hcop (heckeWeights K t u)) := by
  classical
  let B := ZSpan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)
  let d : ℝ := if m.finitePart = 0 then 1 else 0
  have hB : MeasurableSet B := ZSpan.fundamentalDomain_measurableSet _
  have hBfin : volume B < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  have hcompact : IsCompact (closure B) :=
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
  have hcont : Continuous (fun u : logSpace K =>
      rayTheta m J hcop (heckeWeights K t u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (continuousAt_rayTheta_heckeWeights m J hcop (p := (t, u)) ht).comp
      ((continuous_const.prodMk continuous_id).continuousAt)
  have hint : IntegrableOn (fun u : logSpace K =>
      rayTheta m J hcop (heckeWeights K t u)) B :=
    (hcont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure
  have htailInt : IntegrableOn (fun u : logSpace K =>
      rayThetaTail m J hcop (heckeWeights K t u)) B := by
    have hi := hint.sub (integrableOn_const (C := d) (ne_top_of_lt hBfin))
    change IntegrableOn (fun u => rayTheta m J hcop (heckeWeights K t u) - d) B at hi
    simpa only [rayThetaTail_eq_theta_sub_delta m J hcop ht] using hi
  have hvol : volume.real B = unitBoxVol K := by
    rw [DedekindResidue.unitBoxVol]
    rfl
  have hid : rayG m J hcop t - rayPrimalConstant m =
      (torsionOrder K : ℝ)⁻¹ * ∫ u in B, rayThetaTail m J hcop (heckeWeights K t u) := by
    simp_rw [rayThetaTail_eq_theta_sub_delta m J hcop ht]
    rw [integral_sub hint (integrableOn_const (C := d) (ne_top_of_lt hBfin)),
      setIntegral_const, smul_eq_mul, hvol]
    dsimp [rayG, rayPrimalConstant, B, d]
    ring
  rw [hid, ENNReal.ofReal_mul (by positivity)]
  congr 1
  apply ofReal_integral_eq_lintegral_ofReal htailInt
  refine (ae_restrict_iff' hB).mpr (Filter.Eventually.of_forall (fun u _ => ?_))
  unfold rayThetaTail
  apply tsum_nonneg
  intro x
  split_ifs
  · exact le_refl 0
  · exact (Real.exp_pos _).le

/-- Gaussian Mellin evaluation after ray-kernel unit-box unfolding. -/
theorem lintegral_mellin_rayG_dev [IsTotallyComplex K]
    (m : RayClassModulus K) (J : (Ideal (𝓞 K))⁰)
    (hcop : IsCoprimeTo m (J : Ideal (𝓞 K))) {σ : ℝ} (hσ : 0 < σ) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (σ - 1))
        * ENNReal.ofReal (rayG m (J : Ideal (𝓞 K)) hcop t
            - rayPrimalConstant m))
      = ENNReal.ofReal ((torsionOrder K : ℝ)⁻¹)
        * ((heckeJacobian K : ℝ≥0∞) * ENNReal.ofReal (∏ w : InfinitePlace K,
            π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ)))
        * ∑' a : rayConePoints m J, ENNReal.ofReal
            (((((|Algebra.norm ℚ (conePreimage K J a.1)| : ℚ) : ℝ)) ^ 2) ^ (-σ)) := by
  -- step 1: per-t rewrite to the cone-unfolded form
  have hstep1 : ∀ t ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal (t ^ (σ - 1))
        * ENNReal.ofReal (rayG m (J : Ideal (𝓞 K)) hcop t
            - rayPrimalConstant m)
      = ENNReal.ofReal ((torsionOrder K : ℝ)⁻¹) * (ENNReal.ofReal (t ^ (σ - 1))
          * ∑' a : rayConePoints m J, ∫⁻ u : logSpace K,
              ENNReal.ofReal (gaussTerm K t u
                (embeddingCoords K (conePreimage K J a.1)))) := by
    intro t ht
    rw [ofReal_rayG_sub_const m (J : Ideal (𝓞 K)) hcop ht]
    have hswap : (∫⁻ u in ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
        ENNReal.ofReal (rayThetaTail m (J : Ideal (𝓞 K)) hcop
          (heckeWeights K t u)))
        = ∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
            ENNReal.ofReal (rayThetaTail m (J : Ideal (𝓞 K)) hcop
              (heckeWeights K t u)) := by
      refine setLIntegral_box_swap K _ (fun l hl x => ?_)
      obtain ⟨b, -, hb⟩ := Submodule.mem_map.mp hl
      rw [add_comm, ← hb]
      rw [show ((logEmbedding K).toIntLinearMap b : logSpace K)
        = logEmbedding K (Additive.ofMul (Additive.toMul b)) from rfl]
      rw [rayThetaTail_heckeWeights_periodic m (J : Ideal (𝓞 K)) hcop ht x (Additive.toMul b)]
    rw [hswap, lintegral_box_rayTheta_tail m J hcop ht]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hstep1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- step 2: swap the a-sum out of the t-integral (antitone-measurability route)
  have hanti : ∀ c : EuclideanSpace ℝ (index K), AntitoneOn
      (fun t => ∫⁻ u : logSpace K, ENNReal.ofReal (gaussTerm K t u c))
      (Set.Ioi (0:ℝ)) := by
    intro c s hs t ht hst
    refine lintegral_mono (fun u => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [gaussTerm, gaussTerm]
    refine Real.exp_le_exp.mpr ?_
    have hsum : ∑ i : index K, placeWeights K (heckeWeights K s u) i * (c i) ^ 2
        ≤ ∑ i : index K, placeWeights K (heckeWeights K t u) i * (c i) ^ 2 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hw : ∀ w : InfinitePlace K, heckeWeights K s u w ≤ heckeWeights K t u w := by
        intro w
        rw [heckeWeights, heckeWeights]
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        refine Real.rpow_le_rpow (le_of_lt hs) hst ?_
        have := Module.finrank_pos (R := ℚ) (M := K)
        positivity
      rcases i with (w | ⟨w, j⟩) <;> exact hw _
    nlinarith [Real.pi_pos]
  have hmeasH : ∀ c : EuclideanSpace ℝ (index K), AEMeasurable
      (fun t => ∫⁻ u : logSpace K, ENNReal.ofReal (gaussTerm K t u c))
      (volume.restrict (Set.Ioi (0:ℝ))) :=
    fun c => aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (hanti c)
  have hmeas_rpow : AEMeasurable (fun t : ℝ => ENNReal.ofReal (t ^ (σ - 1)))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    have hcont : ContinuousOn (fun t : ℝ => t ^ (σ - 1)) (Set.Ioi (0:ℝ)) :=
      fun x hx => (Real.continuousAt_rpow_const x _
        (Or.inl (ne_of_gt hx))).continuousWithinAt
    exact (ENNReal.continuous_ofReal.comp_continuousOn hcont).aemeasurable
      measurableSet_Ioi
  have hpull : ∀ t ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal (t ^ (σ - 1)) * ∑' a : rayConePoints m J,
        ∫⁻ u : logSpace K, ENNReal.ofReal (gaussTerm K t u
          (embeddingCoords K (conePreimage K J a.1)))
      = ∑' a : rayConePoints m J, ENNReal.ofReal (t ^ (σ - 1))
          * ∫⁻ u : logSpace K, ENNReal.ofReal (gaussTerm K t u
              (embeddingCoords K (conePreimage K J a.1))) :=
    fun t _ => (ENNReal.tsum_mul_left).symm
  rw [setLIntegral_congr_fun measurableSet_Ioi hpull]
  rw [lintegral_tsum (f := fun (a : rayConePoints m J) (t : ℝ) =>
      ENNReal.ofReal (t ^ (σ - 1))
        * ∫⁻ u : logSpace K, ENNReal.ofReal (gaussTerm K t u
            (embeddingCoords K (conePreimage K J a.1))))
    (fun a => hmeas_rpow.mul (hmeasH _))]
  -- step 3: evaluate each cone-point term
  have hpera : ∀ a : rayConePoints m J,
      (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (σ - 1))
        * ∫⁻ u : logSpace K, ENNReal.ofReal (gaussTerm K t u
            (embeddingCoords K (conePreimage K J a.1))))
      = ENNReal.ofReal (((((|Algebra.norm ℚ (conePreimage K J a.1)| : ℚ) : ℝ)) ^ 2) ^ (-σ))
        * ((heckeJacobian K : ℝ≥0∞) * ENNReal.ofReal (∏ w : InfinitePlace K,
            π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ))) := by
    intro a
    have hyne := conePreimage_ne_zero K J a.1
    have hcpos : (0:ℝ) < (((|Algebra.norm ℚ (conePreimage K J a.1)| : ℚ) : ℝ)) ^ 2 := by
      have habs : ((|Algebra.norm ℚ (conePreimage K J a.1)| : ℚ) : ℝ) ≠ 0 := by
        rw [Rat.cast_ne_zero, abs_ne_zero]
        exact Algebra.norm_ne_zero_iff.mpr hyne
      positivity
    have hstep : ∀ t ∈ Set.Ioi (0:ℝ),
        (ENNReal.ofReal (t ^ (σ - 1)) * ∫⁻ u : logSpace K,
          ENNReal.ofReal (gaussTerm K t u (embeddingCoords K (conePreimage K J a.1))))
        = ENNReal.ofReal (t ^ (σ - 1)) * (fun s => ∫⁻ u : logSpace K,
            ENNReal.ofReal (gaussTerm K s u (embeddingCoords K 1)))
              ((((|Algebra.norm ℚ (conePreimage K J a.1)| : ℚ) : ℝ)) ^ 2 * t) := by
      intro t ht
      congr 1
      exact lintegral_gaussTerm_eq_norm_scaled K hyne (le_of_lt ht)
    rw [setLIntegral_congr_fun measurableSet_Ioi hstep]
    rw [lintegral_Ioi_mellin_scale hcpos σ _ (hmeasH (embeddingCoords K 1))]
    rw [lintegral_M0_eq K hσ]
  rw [tsum_congr hpera, ENNReal.tsum_mul_right]
  ring


/-- Norm scaling and torsion cancellation identify the real ray-class Mellin sum. -/
theorem lintegral_mellin_rayF_dev [IsTotallyComplex K]
    (m : RayClassModulus K) (J : (Ideal (𝓞 K))⁰)
    (hcop : IsCoprimeTo m (J : Ideal (𝓞 K))) {σ : ℝ} (hσ : 0 < σ) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (σ - 1))
        * ENNReal.ofReal (rayF m (J : Ideal (𝓞 K)) hcop t - rayPrimalConstant m))
      = ENNReal.ofReal ((heckeBeta K) ^ (-σ))
        * ((heckeJacobian K : ℝ≥0∞) * ENNReal.ofReal (∏ w : InfinitePlace K,
            π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ)))
        * ∑' b : {b : (Ideal (𝓞 K))⁰ //
            ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
              rayClass m (b : Ideal (𝓞 K)) hb = (rayClass m (J : Ideal (𝓞 K)) hcop)⁻¹},
            ENNReal.ofReal ((((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ 2)
              ^ (-σ)) := by
  have hNpos := idealNormR_pos K (idealUnit (J : Ideal (𝓞 K)) hcop.1)
  have hβ := heckeBeta_pos K
  set s_C : ℝ := (idealNormR K (idealUnit (J : Ideal (𝓞 K)) hcop.1))⁻¹ ^ 2 * heckeBeta K with hsC
  have hsCpos : 0 < s_C := by positivity
  -- the class theta is the scaled base theta
  have hshape : ∀ t : ℝ, rayF m (J : Ideal (𝓞 K)) hcop t = rayG m (J : Ideal (𝓞 K)) hcop (s_C * t) :=
    fun t => rfl
  have hdev_meas : AEMeasurable (fun t : ℝ =>
      ENNReal.ofReal (rayG m (J : Ideal (𝓞 K)) hcop t
        - rayPrimalConstant m))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    refine (ENNReal.continuous_ofReal.comp_continuousOn ?_).aemeasurable measurableSet_Ioi
    exact (continuousOn_rayG m (J : Ideal (𝓞 K)) hcop).sub continuousOn_const
  have hstep : ∀ t ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal (t ^ (σ - 1))
        * ENNReal.ofReal (rayF m (J : Ideal (𝓞 K)) hcop t - rayPrimalConstant m)
      = ENNReal.ofReal (t ^ (σ - 1)) * (fun r => ENNReal.ofReal
          (rayG m (J : Ideal (𝓞 K)) hcop r
            - rayPrimalConstant m)) (s_C * t) := by
    intro t ht
    rw [hshape]
  rw [setLIntegral_congr_fun measurableSet_Ioi hstep,
    lintegral_Ioi_mellin_scale hsCpos σ _ hdev_meas,
    lintegral_mellin_rayG_dev m J hcop hσ,
    tsum_rayCone_norm_rpow m J σ, tsum_rayPrincipal_dvd_norm_sq_rpow m J hcop σ]
  -- now pure constant algebra in ℝ≥0∞
  have hNJ : idealNormR K (idealUnit (J : Ideal (𝓞 K)) hcop.1)
      = ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)) := by
    simp [idealNormR, idealUnit, FractionalIdeal.coeIdeal_absNorm]
  have hNJpos : (0:ℝ) < ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)) := by
    rw [← hNJ]
    exact hNpos
  -- s_C^{-σ} = (NJ²)^{σ}·β^{-σ}
  have hsC_rpow : s_C ^ (-σ)
      = (((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)) ^ 2) ^ σ * (heckeBeta K) ^ (-σ) := by
    rw [hsC, hNJ, Real.mul_rpow (by positivity) hβ.le, ← Real.rpow_natCast
      ((((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)))⁻¹) 2, ← Real.rpow_natCast
      (((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ))) 2,
      ← Real.rpow_mul (by positivity), ← Real.rpow_mul hNJpos.le,
      Real.inv_rpow hNJpos.le, ← Real.rpow_neg hNJpos.le]
    push_cast
    ring_nf
  -- w-cancellation
  have hw_cancel : ENNReal.ofReal ((torsionOrder K : ℝ)⁻¹) * (torsionOrder K : ℝ≥0∞) = 1 := by
    rw [ENNReal.ofReal_inv_of_pos (by
      have := torsionOrder_pos K
      positivity), ENNReal.ofReal_natCast]
    refine ENNReal.inv_mul_cancel ?_ (ENNReal.natCast_ne_top _)
    exact_mod_cast (torsionOrder_pos K).ne'
  -- assemble
  rw [hsC_rpow, ENNReal.ofReal_mul (by positivity)]
  have hNJcancel : ENNReal.ofReal ((((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)) ^ 2) ^ σ)
      * ENNReal.ofReal ((((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ)) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by positivity)]
    simp
  calc ENNReal.ofReal ((((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)) ^ 2) ^ σ)
        * ENNReal.ofReal ((heckeBeta K) ^ (-σ))
        * (ENNReal.ofReal ((torsionOrder K : ℝ)⁻¹)
          * ((heckeJacobian K : ℝ≥0∞) * ENNReal.ofReal (∏ w : InfinitePlace K,
              π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ)))
          * ((torsionOrder K : ℝ≥0∞)
            * (ENNReal.ofReal ((((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ))
              * ∑' b : {b : (Ideal (𝓞 K))⁰ // ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
                  rayClass m (b : Ideal (𝓞 K)) hb = (rayClass m (J : Ideal (𝓞 K)) hcop)⁻¹},
                  ENNReal.ofReal ((((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) :
                    Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ)))))
      = (ENNReal.ofReal ((torsionOrder K : ℝ)⁻¹) * (torsionOrder K : ℝ≥0∞))
        * (ENNReal.ofReal ((((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)) ^ 2) ^ σ)
          * ENNReal.ofReal ((((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ)))
        * (ENNReal.ofReal ((heckeBeta K) ^ (-σ))
          * ((heckeJacobian K : ℝ≥0∞) * ENNReal.ofReal (∏ w : InfinitePlace K,
              π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ)))
          * ∑' b : {b : (Ideal (𝓞 K))⁰ // ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
                  rayClass m (b : Ideal (𝓞 K)) hb = (rayClass m (J : Ideal (𝓞 K)) hcop)⁻¹},
              ENNReal.ofReal ((((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) :
                Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ))) := by ring
    _ = _ := by
        rw [hw_cancel, hNJcancel, one_mul, one_mul]


theorem rayG_dev_nonneg [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    {t : ℝ} (ht : 0 < t) : 0 ≤ rayG m J hcop t - rayPrimalConstant m := by
  classical
  let B := ZSpan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)
  let d : ℝ := if m.finitePart = 0 then 1 else 0
  have hBfin : volume B < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  have hcont : Continuous (fun u : logSpace K => rayTheta m J hcop (heckeWeights K t u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (continuousAt_rayTheta_heckeWeights m J hcop (p := (t, u)) ht).comp
      ((continuous_const.prodMk continuous_id).continuousAt)
  have hint : IntegrableOn (fun u : logSpace K => rayTheta m J hcop (heckeWeights K t u)) B :=
    (hcont.continuousOn.integrableOn_compact
      (ZSpan.fundamentalDomain_isBounded _).isCompact_closure).mono_set subset_closure
  have hle : ∀ u : logSpace K, d ≤ rayTheta m J hcop (heckeWeights K t u) := by
    intro u
    have heq := rayThetaTail_eq_theta_sub_delta m J hcop ht u
    have hn : 0 ≤ rayThetaTail m J hcop (heckeWeights K t u) := by
      unfold rayThetaTail
      apply tsum_nonneg
      intro x
      split_ifs
      · exact le_refl 0
      · exact (Real.exp_pos _).le
    dsimp only [d]
    linarith
  have hi := integral_mono_ae (integrableOn_const (C := d) (ne_top_of_lt hBfin)) hint
    (Filter.Eventually.of_forall hle)
  have hvol : volume.real B = unitBoxVol K := by rw [DedekindResidue.unitBoxVol]; rfl
  rw [setIntegral_const, smul_eq_mul, hvol] at hi
  rw [rayG, rayPrimalConstant]
  apply sub_nonneg.mpr
  change d * (torsionOrder K : ℝ)⁻¹ * unitBoxVol K ≤
    (torsionOrder K : ℝ)⁻¹ * ∫ u in B, rayTheta m J hcop (heckeWeights K t u)
  calc
    _ = (torsionOrder K : ℝ)⁻¹ * (unitBoxVol K * d) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)

theorem rayF_dev_nonneg [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    {t : ℝ} (ht : 0 < t) : 0 ≤ rayF m J hcop t - rayPrimalConstant m := by
  have hN := idealNormR_pos K (idealUnit J hcop.1)
  have hβ := heckeBeta_pos K
  exact rayG_dev_nonneg m J hcop (by positivity)

end ArtinPrimitiveRoots.Hecke

end
