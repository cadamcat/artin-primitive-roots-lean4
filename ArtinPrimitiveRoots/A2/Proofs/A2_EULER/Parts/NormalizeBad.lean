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

theorem normalize_bad (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (p : Triple)
    (hE : EulerHypotheses R η) (hp : eulerNeighborhood p) (hQ : (2 : ℝ) ^ (2000 : ℕ) < qI v.asIdeal)
    (hdev : ‖localEuler R η U u v hv (p 0) (p 1) (p 2) - 1‖ ≤
      16 * qI v.asIdeal ^ (-1 / 4000 : ℝ)) :
    ‖normalizedLocal R η U u v hv (p 0) (p 1) (p 2) - 1‖ ≤
      128 * qI v.asIdeal ^ (-1 / 4000 : ℝ) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
