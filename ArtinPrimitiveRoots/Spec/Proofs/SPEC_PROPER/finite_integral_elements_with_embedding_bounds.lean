import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Integral elements with uniformly bounded chosen complex embeddings form a finite set.
Uses the Mathlib canonical embedding lattice;
feeds compact_overlap_finite_SL2O, finite_denominator_elements_with_embedding_bounds,
and siegel_high_height_overlap_finite. -/
theorem finite_integral_elements_with_embedding_bounds (R : ℝ) (hR : 0 ≤ R) :
    {a : 𝓞 F | ∀ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F a)‖ ≤ R}.Finite := by
  classical
  let S : Set F := {x | IsIntegral ℤ x ∧ ∀ φ : F →+* ℂ, ‖φ x‖ ≤ R}
  have hS : S.Finite := NumberField.Embeddings.finite_of_norm_le F ℂ R
  have hpre : (fun a : 𝓞 F => (a : F)) ⁻¹' S |>.Finite := by
    apply hS.preimage
    intro a ha b hb hab
    exact RingOfIntegers.coe_injective hab
  apply hpre.subset
  intro a ha
  change (a : F) ∈ S
  refine ⟨RingOfIntegers.isIntegral_coe a, ?_⟩
  intro φ
  let w : InfinitePlace F := InfinitePlace.mk φ
  have hw := ha w
  rcases InfinitePlace.embedding_mk_eq φ with hφ | hφ
  · simpa only [w, hφ] using hw
  · have hconj : ‖φ (a : F)‖ = ‖(ComplexEmbedding.conjugate φ) (a : F)‖ := by
      simp [ComplexEmbedding.conjugate]
    change ‖(InfinitePlace.mk φ).embedding (algebraMap (𝓞 F) F a)‖ ≤ R at hw
    rw [hφ] at hw
    exact hconj.symm ▸ hw
end ArtinPrimitiveRoots.A1.Spec
