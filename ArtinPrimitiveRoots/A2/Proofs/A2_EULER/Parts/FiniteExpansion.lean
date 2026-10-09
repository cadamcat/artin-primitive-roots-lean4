import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
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

theorem finite_expansion (B : PrimeTupleBridge S) (u : U.U) (ξ w z : ℂ)
    (hs : ∀ v hv, Summable (fun i : LocalIndex => ‖localEulerTerm R η U u v hv ξ w z i‖))
    (hcoeff : ∀ p : IdealTuple S, calFTerm R η U u ξ w z p =
      ∏ v ∈ (B.equiv p).support, localEulerTerm R η U u v.1 v.2 ξ w z (B.equiv p v))
    (V : Finset (ExteriorPrime S)) :
    (∏ v ∈ V, localEuler R η U u v.1 v.2 ξ w z) =
      ∑' p : IdealTuple S, if (B.equiv p).support ⊆ V then calFTerm R η U u ξ w z p else 0 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
