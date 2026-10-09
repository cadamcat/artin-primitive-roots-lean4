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

theorem principal_nonzero (HC : EulerCorrection R η U)
    (hs : ∀ p, eulerNeighborhood p → Summable (fun v : {v : FinPlace F // v ∉ S.Sf} =>
      ‖normalizedLocal R η U U.one v.1 v.2 (p 0) (p 1) (p 2) - 1‖))
    (hsmall : ∀ v hv p, eulerNeighborhood p →
      ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) :
    ∀ p, eulerNeighborhood p → HC.H U.one p ≠ 0 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
