import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Isometry equivariance for every radial kernel and function, including the Bochner integral's
nonintegrable case. Uses frozen `G2_x_action`,
`G3_volume`, `G6_ppi`; supplies the equivariance and invariance conjuncts of `S1_smoothing`. -/
theorem smoothing_isometry_equivariant (k₀ : ℝ → ℝ)
    (g : InfinitePlace F → SL(2,ℂ)) (f : X F → ℂ) (z : X F) :
    smoothingOperator F k₀ (fun x => f (actAtPlaces F g x)) z =
      smoothingOperator F k₀ f (actAtPlaces F g z) := by
  classical
  let gi : InfinitePlace F → SL(2,ℂ) := fun w => (g w)⁻¹
  have hmeas (h : InfinitePlace F → SL(2,ℂ)) :
      Measurable (actAtPlaces F h) := by
    apply measurable_pi_iff.2
    intro w
    change Measurable (fun x : X F => h w • x w)
    exact (OAI.CubicEisenstein.continuous_hyperbolic_action (h w)).measurable.comp
      (measurable_pi_apply w)
  have hcancel (x : X F) : actAtPlaces F gi (actAtPlaces F g x) = x := by
    funext v
    simp [actAtPlaces, gi]
  have hcancel' (x : X F) : actAtPlaces F g (actAtPlaces F gi x) = x := by
    funext v
    simp [actAtPlaces, gi]
  let e : X F ≃ᵐ X F :=
    { toFun := actAtPlaces F g
      invFun := actAtPlaces F gi
      left_inv := hcancel
      right_inv := hcancel'
      measurable_toFun := hmeas g
      measurable_invFun := hmeas gi }
  have hpres : MeasurePreserving e (volX F) (volX F) := by
    change MeasurePreserving (actAtPlaces F g) (volX F) (volX F)
    exact ⟨hmeas g, (G3_volume (F := F)).1 g⟩
  have hkernel (w : X F) :
      radialKernel F k₀ z (actAtPlaces F gi w) =
        radialKernel F k₀ (actAtPlaces F g z) w := by
    unfold radialKernel
    apply Finset.prod_congr rfl
    intro v hv
    have h := (G6_ppi (F := F)).1 (g v) (z v) ((g v)⁻¹ • w v)
    have hppi : ppi (z v) ((g v)⁻¹ • w v) = ppi (g v • z v) (w v) := by
      simpa using h.symm
    exact congrArg (fun t : ℝ => (k₀ t : ℂ)) hppi
  let q : X F → ℂ := fun w => radialKernel F k₀ z (actAtPlaces F gi w) * f w
  calc
    smoothingOperator F k₀ (fun x => f (actAtPlaces F g x)) z
        = ∫ x, radialKernel F k₀ z x * f (actAtPlaces F g x) ∂(volX F) := by
            rw [smoothingOperator]
    _ = ∫ x, q (actAtPlaces F g x) ∂(volX F) := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp [q, hcancel]
    _ = ∫ x, q x ∂(volX F) := hpres.integral_comp' q
    _ = smoothingOperator F k₀ f (actAtPlaces F g z) := by
          rw [smoothingOperator]
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp [q]
          rw [hkernel]

end ArtinPrimitiveRoots.A1.Spec
