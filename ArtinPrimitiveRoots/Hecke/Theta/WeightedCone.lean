import ArtinPrimitiveRoots.Hecke.Theta.RayMellinCone

/-!
Unit-box unfolding with a finite weight invariant under the fundamental units.
Adapted from AINTLIB's `DedekindResidue/CompletedZeta/MellinAgreement.lean`,
`lintegral_box_theta_tail` (Chris Birkbeck, Apache-2.0). The weight is carried through the
cone reindexing and log-space tiling, allowing the ray-principal restriction.
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

/-- A finite unit-invariant weight survives unfolding the unit box to the full logarithmic space. -/
theorem lintegral_box_weighted_theta_tail (J : (Ideal (𝓞 K))⁰) (t : ℝ)
    (W : EuclideanSpace ℝ (index K) → ℝ≥0∞) (hWfin : ∀ x, W x ≠ ⊤)
    (hW : ∀ (a : idealSet K J) (n : Fin (rank K) → ℤ),
      W ((euclidMixedEquiv K).symm
        ((∏ j, fundSystem K j ^ (n j)) • (a : mixedSpace K))) =
          W (embeddingCoords K (conePreimage K J a))) :
    (∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
      ∑' v : idealZLattice K (FractionalIdeal.mk0 K J),
        if v = 0 then 0 else
          W (v : EuclideanSpace ℝ (index K)) *
            ENNReal.ofReal (gaussTerm K t u (v : EuclideanSpace ℝ (index K)))) =
      ∑' a : idealSet K J, W (embeddingCoords K (conePreimage K J a)) *
        ∫⁻ u : logSpace K,
          ENNReal.ofReal (gaussTerm K t u (embeddingCoords K (conePreimage K J a))) := by
  classical
  let B := ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ)
  let G : EuclideanSpace ℝ (index K) → ℝ≥0∞ := fun x =>
    W x * ∫⁻ u in B, ENNReal.ofReal (gaussTerm K t u x)
  have hB : MeasurableSet B := ZSpan.fundamentalDomain_measurableSet _
  rw [lintegral_tsum]
  swap
  · intro v
    by_cases hv : v = 0
    · simp only [if_pos hv]
      exact aemeasurable_const
    · simp only [if_neg hv]
      exact aemeasurable_const.mul
        ((ENNReal.continuous_ofReal.comp (continuous_gaussTerm K t _)).aemeasurable.restrict)
  have hsplit : ∀ v : idealZLattice K (FractionalIdeal.mk0 K J),
      (∫⁻ u in B, if v = 0 then 0 else
        W (v : EuclideanSpace ℝ (index K)) *
          ENNReal.ofReal (gaussTerm K t u (v : EuclideanSpace ℝ (index K)))) =
      if v = 0 then 0 else G (v : EuclideanSpace ℝ (index K)) := by
    intro v
    by_cases hv : v = 0
    · simp only [if_pos hv, lintegral_zero]
    · simp only [if_neg hv]
      exact lintegral_const_mul' _ _ (hWfin _)
  rw [tsum_congr hsplit, tsum_ite_eq_tsum_coneUnfold_ennreal K J G, ENNReal.tsum_prod']
  apply tsum_congr
  intro a
  have hshift : ∀ n : Fin (rank K) → ℤ,
      G ((euclidMixedEquiv K).symm
        ((∏ j, fundSystem K j ^ (n j)) • (a : mixedSpace K))) =
      W (embeddingCoords K (conePreimage K J a)) *
        ∫⁻ u in B,
          ENNReal.ofReal (gaussTerm K t
            (u + logEmbedding K (Additive.ofMul (∏ j, fundSystem K j ^ (n j))))
            (embeddingCoords K (conePreimage K J a))) := by
    intro n
    dsimp only [G]
    rw [hW a n]
    congr 1
    apply setLIntegral_congr_fun hB
    intro u _
    apply congrArg ENNReal.ofReal
    rw [← mixedEmbedding_conePreimage K J a]
    exact gaussTerm_unit_smul K t u (∏ j, fundSystem K j ^ (n j)) (conePreimage K J a)
  rw [tsum_congr hshift, ENNReal.tsum_mul_left]
  congr 1
  exact (lintegral_eq_tsum_box_shift K
    (fun u => ENNReal.ofReal (gaussTerm K t u (embeddingCoords K (conePreimage K J a))))).symm

end ArtinPrimitiveRoots.Hecke

end
