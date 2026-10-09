import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

theorem product_compact (HC : EulerCorrection R η U) (C Q0 : ℝ)
    (hE : EulerHypotheses R η)
    (hb : HasPoHLocalBounds R η U C Q0)
    (hlocal : ∀ u v hv, DifferentiableOn ℂ (fun p : Triple =>
      normalizedLocal R η U u v hv (p 0) (p 1) (p 2)) {p | eulerNeighborhood p}) :
    ∀ u (K : Set Triple), IsCompact K → K ⊆ {p | eulerNeighborhood p} →
      ∀ ε : ℝ, 0 < ε → ∃ V : Finset (FinPlace F), ∀ V' : Finset (FinPlace F), V ⊆ V' →
        ∀ p ∈ K, ‖(∏ v ∈ V'.attach, if hv : v.1 ∉ S.Sf then
          normalizedLocal R η U u v.1 hv (p 0) (p 1) (p 2) else 1) - HC.H u p‖ < ε := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
