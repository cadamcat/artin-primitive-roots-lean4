import ArtinPrimitiveRoots.Spec.Stage1
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GREEN.G4
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GREEN.G5

/-! Differential-geometry nodes G4--G5. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- G4 `spec:energy` — P-SPEC.md:211. The placewise gradient pairing and total energy
are invariant under the product isometry action, and the squared norm of `∇ log N` is the number
of complex places. -/
theorem G4_energy (g : InfinitePlace F → SL(2,ℂ)) (f f' : X F → ℂ)
    (hf : IsSmoothX F f) (hf' : IsSmoothX F f') :
    (∀ w z,
      placeGradInner F w (fun x => f (actAtPlaces F g x))
        (fun x => f' (actAtPlaces F g x)) z =
        placeGradInner F w f f' (actAtPlaces F g z)) ∧
    (∀ z, totalGradNormSq F (fun x => f (actAtPlaces F g x)) z =
      totalGradNormSq F f (actAtPlaces F g z)) ∧
    ∀ z, totalGradNormSq F (logNormHeight F) z = placeCount F := by
  refine ⟨?_, ?_, greenTotalGradNormSq_logNormHeight⟩
  · intro w z
    exact greenPlaceGradInner_action g f f' hf hf' w z
  · intro z
    exact greenTotalGradNormSq_action g f hf z

/-- G5 `spec:green-x` — P-SPEC.md:212, 262–265. Coordinate integration by parts gives the
Green identity and symmetry; each partial Laplacian commutes with the product isometry action. -/
theorem G5_green_x (f φ : X F → ℂ) (hf : IsSmoothX F f) (hφ : IsSmoothX F φ)
    (hcompact : HasCompactSupportX F φ) :
    (∀ w : InfinitePlace F,
      ∫ z, partialLap F w f z * φ z ∂(volX F) =
        ∫ z, placeGradBilinear F w f φ z ∂(volX F)) ∧
    (∀ (f' φ' : X F → ℂ), IsSmoothX F f' → IsSmoothX F φ' →
      HasCompactSupportX F f' → HasCompactSupportX F φ' → ∀ w : InfinitePlace F,
        ∫ z, partialLap F w f' z * φ' z ∂(volX F) =
          ∫ z, f' z * partialLap F w φ' z ∂(volX F)) ∧
    (∀ (g : InfinitePlace F → SL(2,ℂ)) (F₀ : X F → ℂ), IsSmoothX F F₀ →
      ∀ w z, partialLap F w (fun x => F₀ (actAtPlaces F g x)) z =
        partialLap F w F₀ (actAtPlaces F g z)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    exact g5GreenFirst f φ hf hφ hcompact w
  · intro f' φ' hf' hφ' hf'compact hφ'compact w
    exact g5GreenSymmetry f' φ' hf' hφ' hf'compact hφ'compact w
  · intro g F₀ hF₀ w z
    exact g5PartialLap_action_pointwise g F₀ hF₀ w z

end ArtinPrimitiveRoots.A1.Spec
