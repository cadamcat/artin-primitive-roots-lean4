import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.CoefficientAssembly
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.CharacterProducts
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.LocalNormalization
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.ArithmeticCore

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

theorem prime_coefficient (B : PrimeTupleBridge S) (u : U.U) (ξ w z : ℂ)
    (p : IdealTuple S) :
    calFTerm R η U u ξ w z p =
      ∏ v ∈ (B.equiv p).support,
        localEulerTerm R η U u v.1 v.2 ξ w z (B.equiv p v) := by
  apply ArtinPrimitiveRoots.Proofs.e_c.coefficient_of_core R η U B u ξ w z p
  exact ArtinPrimitiveRoots.Proofs.e_c.tuple_arithmetic_core R η U B u p

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
