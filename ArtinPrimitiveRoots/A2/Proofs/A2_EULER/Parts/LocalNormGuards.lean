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

theorem local_norm_guards (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (ξ w z : ℂ)
    (hθ : ‖ϑ.primeValue v‖ ≤ 1)
    (hξ : 2 / 3 < ξ.re) (hw : 0 < w.re) (hz : 0 < z.re) :
    ‖localV v z‖ < 1 ∧ ‖localWvar η U u v w‖ < 1 ∧
      ‖localEvar (ϑ := ϑ) v ξ z‖ < 1 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
