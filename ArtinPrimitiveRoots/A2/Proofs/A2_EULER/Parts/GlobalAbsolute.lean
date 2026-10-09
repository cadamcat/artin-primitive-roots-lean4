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

theorem global_absolute (u : U.U) (ξ w z : ℂ)
    (hreg : initialRegion ξ w z)
    (hgamma : ∀ c : S.SqfExtIdeal, ‖gamma D S A 2 c.1 (cgen R c)‖ ≤ 1)
    (hfinite : ∀ p : IdealTuple S,
      ‖finiteFactor R p.2.2.1 (Aideal R p.1 p.2.1) (Agen R p.1 p.2.1)
        ((U.repr u : F) * (bc.gen p.2.2.2 : F) ^ 6)‖ ≤
        qI p.2.2.1.1 * qI (Aideal R p.1 p.2.1).1) :
    Summable (fun p : IdealTuple S => ‖calFTerm R η U u ξ w z p‖) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
