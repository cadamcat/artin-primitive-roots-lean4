import ArtinPrimitiveRoots.Hecke.Theta.WeightedCone

/-!
The ray-principal indicator on Euclidean embedding coordinates, extended by zero outside
the field embedding. This is a finite unit-invariant weight for weighted cone unfolding.
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

private theorem rayEmbeddingCoords_injective : Function.Injective (embeddingCoords K) := by
  intro x y hxy
  apply mixedEmbedding_injective K
  have h := congrArg (fun z => (euclidean.toMixed K)
    ((euclidean.stdOrthonormalBasis K).repr.symm z)) hxy
  simpa [embeddingCoords] using h

/-- The ray kernel on field coordinates, extended by zero to the ambient Euclidean space. -/
def fieldCoordinateRayWeight (m : RayClassModulus K)
    (v : EuclideanSpace ℝ (index K)) : ℝ≥0∞ :=
  if h : ∃ x : K, embeddingCoords K x = v then
    ENNReal.ofReal (rayKernelWeight m (Classical.choose h)) else 0

theorem fieldCoordinateRayWeight_ne_top (m : RayClassModulus K)
    (v : EuclideanSpace ℝ (index K)) : fieldCoordinateRayWeight m v ≠ ⊤ := by
  unfold fieldCoordinateRayWeight
  split_ifs <;> simp

@[simp] theorem fieldCoordinateRayWeight_embed (m : RayClassModulus K) (x : K) :
    fieldCoordinateRayWeight m (embeddingCoords K x) = ENNReal.ofReal (rayKernelWeight m x) := by
  have h : ∃ y : K, embeddingCoords K y = embeddingCoords K x := ⟨x, rfl⟩
  rw [fieldCoordinateRayWeight, dif_pos h]
  have heq : Classical.choose h = x := rayEmbeddingCoords_injective (Classical.choose_spec h)
  rw [heq]

theorem fieldCoordinateRayWeight_unit_cone (m : RayClassModulus K)
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) (u : (𝓞 K)ˣ) :
    fieldCoordinateRayWeight m ((euclidMixedEquiv K).symm (u • (a : mixedSpace K))) =
      fieldCoordinateRayWeight m (embeddingCoords K (conePreimage K J a)) := by
  rw [← mixedEmbedding_conePreimage K J a]
  have hcoord : (euclidMixedEquiv K).symm (u • mixedEmbedding K (conePreimage K J a)) =
      embeddingCoords K (algebraMap (𝓞 K) K (u : 𝓞 K) * conePreimage K J a) := by
    change (euclidMixedEquiv K).symm
      (mixedEmbedding K (algebraMap (𝓞 K) K (u : 𝓞 K)) *
        mixedEmbedding K (conePreimage K J a)) = _
    rw [← map_mul, euclidMixedEquiv_symm_mixedEmbedding]
  rw [hcoord, fieldCoordinateRayWeight_embed, fieldCoordinateRayWeight_embed,
    rayKernelWeight_integralUnit]

/-- The nonzero ray theta is the Gaussian lattice sum with the Euclidean ray indicator. -/
theorem ofReal_rayThetaTail_eq_weighted_tsum [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    ENNReal.ofReal (rayThetaTail m J hcop (heckeWeights K t u)) =
      ∑' v : idealZLattice K (idealUnit J hcop.1), if v = 0 then 0 else
        fieldCoordinateRayWeight m (v : EuclideanSpace ℝ (index K)) *
          ENNReal.ofReal (gaussTerm K t u (v : EuclideanSpace ℝ (index K))) := by
  classical
  have hne : (Finset.univ : Finset (InfinitePlace K)).Nonempty := Finset.univ_nonempty
  let a := Finset.univ.inf' hne (heckeWeights K t u)
  have ha : 0 < a := (Finset.lt_inf'_iff hne).mpr (fun w _ => heckeWeights_pos K ht u w)
  have hca : ∀ w : InfinitePlace K, a ≤ heckeWeights K t u w :=
    fun w => Finset.inf'_le _ (Finset.mem_univ w)
  have hplace : ∀ i : index K, a ≤ placeWeights K (heckeWeights K t u) i := by
    rintro (w | ⟨w, j⟩) <;> exact hca w
  have hs := summable_integralIdealGaussian m J hcop
    (placeWeights K (heckeWeights K t u)) ha hplace
  have htail : Summable (fun x : rayKernelPoints m J =>
      if x.1.1 = 0 then 0 else
        integralIdealGaussian (placeWeights K (heckeWeights K t u)) x.1.1) := by
    apply hs.of_nonneg_of_le
    · intro x
      split_ifs
      · exact le_refl 0
      · exact (Real.exp_pos _).le
    · intro x
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_refl _
  have hnonneg : ∀ x : rayKernelPoints m J,
      0 ≤ if x.1.1 = 0 then 0 else
        integralIdealGaussian (placeWeights K (heckeWeights K t u)) x.1.1 := by
    intro x
    split_ifs
    · exact le_refl 0
    · exact (Real.exp_pos _).le
  rw [rayThetaTail, ENNReal.ofReal_tsum_of_nonneg hnonneg htail]
  have hcast : ∀ x : rayKernelPoints m J,
      ENNReal.ofReal (if x.1.1 = 0 then 0 else
        integralIdealGaussian (placeWeights K (heckeWeights K t u)) x.1.1) =
      if x.1.1 = 0 then 0 else
        ENNReal.ofReal (integralIdealGaussian (placeWeights K (heckeWeights K t u)) x.1.1) := by
    intro x
    split_ifs <;> simp
  rw [tsum_congr hcast]
  let e := integralIdealCoordEquiv J hcop.1
  rw [← Equiv.tsum_eq e (fun v => if v = 0 then 0 else
    fieldCoordinateRayWeight m (v : EuclideanSpace ℝ (index K)) *
      ENNReal.ofReal (gaussTerm K t u (v : EuclideanSpace ℝ (index K))))]
  change (∑' x : {x : J // rayKernelWeight m (algebraMap (𝓞 K) K x.1) = 1},
    if x.1.1 = 0 then 0 else
      ENNReal.ofReal (integralIdealGaussian (placeWeights K (heckeWeights K t u)) x.1.1)) = _
  have hsub : (∑' x : {x : J // rayKernelWeight m (algebraMap (𝓞 K) K x.1) = 1},
      if x.1.1 = 0 then 0 else
        ENNReal.ofReal (integralIdealGaussian (placeWeights K (heckeWeights K t u)) x.1.1)) =
      ∑' x : J, {x : J | rayKernelWeight m (algebraMap (𝓞 K) K x.1) = 1}.indicator
        (fun x : J => if x.1 = 0 then 0 else
          ENNReal.ofReal (integralIdealGaussian (placeWeights K (heckeWeights K t u)) x.1)) x :=
    tsum_subtype (α := ℝ≥0∞) (β := J)
      {x : J | rayKernelWeight m (algebraMap (𝓞 K) K x.1) = 1}
      (fun x : J => if x.1 = 0 then 0 else
        ENNReal.ofReal (integralIdealGaussian (placeWeights K (heckeWeights K t u)) x.1))
  rw [hsub]
  apply tsum_congr
  intro x
  have hzero : e x = 0 ↔ x.1 = 0 := by
    change integralIdealCoordMap J hcop.1 x = 0 ↔ x.1 = 0
    rw [integralIdealCoordMap_eq_zero_iff]
    simp
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  simp only [hzero]
  change (if rayKernelWeight m (algebraMap (𝓞 K) K x.1) = 1 then
      (if x.1 = 0 then 0 else
        ENNReal.ofReal (integralIdealGaussian (placeWeights K (heckeWeights K t u)) x.1))
      else 0) = if x.1 = 0 then 0 else
      fieldCoordinateRayWeight m (embeddingCoords K (algebraMap (𝓞 K) K x.1)) *
        ENNReal.ofReal (integralIdealGaussian (placeWeights K (heckeWeights K t u)) x.1)
  rw [fieldCoordinateRayWeight_embed]
  rcases rayKernelWeight_mem m (algebraMap (𝓞 K) K x.1) with hw | hw <;>
    simp [hw]

/-- The ray restriction of the unit-box unfolding identity. -/
theorem lintegral_box_rayTheta_tail [IsTotallyComplex K]
    (m : RayClassModulus K) (J : (Ideal (𝓞 K))⁰)
    (hcop : IsCoprimeTo m (J : Ideal (𝓞 K))) {t : ℝ} (ht : 0 < t) :
    (∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
      ENNReal.ofReal (rayThetaTail m (J : Ideal (𝓞 K)) hcop (heckeWeights K t u))) =
      ∑' a : rayConePoints m J, ∫⁻ u : logSpace K,
        ENNReal.ofReal (gaussTerm K t u (embeddingCoords K (conePreimage K J a.1))) := by
  classical
  have hI : FractionalIdeal.mk0 K J = idealUnit (J : Ideal (𝓞 K)) hcop.1 := by
    apply Units.ext
    simp [idealUnit, FractionalIdeal.coe_mk0]
  rw [setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _)
    (fun u _ => ofReal_rayThetaTail_eq_weighted_tsum m (J : Ideal (𝓞 K)) hcop ht u)]
  rw [← hI, lintegral_box_weighted_theta_tail J t (fieldCoordinateRayWeight m)
    (fieldCoordinateRayWeight_ne_top m)
    (fun a n => fieldCoordinateRayWeight_unit_cone m J a (∏ j, fundSystem K j ^ (n j)))]
  simp_rw [fieldCoordinateRayWeight_embed]
  change (∑' a : idealSet K J, ENNReal.ofReal (rayKernelWeight m (conePreimage K J a)) *
    ∫⁻ u : logSpace K,
      ENNReal.ofReal (gaussTerm K t u (embeddingCoords K (conePreimage K J a)))) =
    ∑' a : {a : idealSet K J // rayKernelWeight m (conePreimage K J a) = 1},
      ∫⁻ u : logSpace K,
        ENNReal.ofReal (gaussTerm K t u (embeddingCoords K (conePreimage K J a.1)))
  have hsub : (∑' a : {a : idealSet K J // rayKernelWeight m (conePreimage K J a) = 1},
      ∫⁻ u : logSpace K,
        ENNReal.ofReal (gaussTerm K t u (embeddingCoords K (conePreimage K J a.1)))) =
      ∑' a : idealSet K J, {a : idealSet K J | rayKernelWeight m (conePreimage K J a) = 1}.indicator
        (fun a => ∫⁻ u : logSpace K,
          ENNReal.ofReal (gaussTerm K t u (embeddingCoords K (conePreimage K J a)))) a :=
    tsum_subtype (α := ℝ≥0∞) (β := idealSet K J)
      {a : idealSet K J | rayKernelWeight m (conePreimage K J a) = 1}
      (fun a => ∫⁻ u : logSpace K,
        ENNReal.ofReal (gaussTerm K t u (embeddingCoords K (conePreimage K J a))))
  rw [hsub]
  apply tsum_congr
  intro a
  rcases rayKernelWeight_mem m (conePreimage K J a) with hw | hw <;>
    simp [Set.indicator_apply, hw]

end ArtinPrimitiveRoots.Hecke

end
