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

theorem good_rational_error (Q : ℝ) (ξ w z : ℂ) (V W D1 E1 : ℂ)
    (hQ : (2 : ℝ) ^ (2000 : ℕ) < Q)
    (hp : eulerNeighborhood ![ξ, w, z])
    (hV : ‖V‖ ≤ Q ^ (-6 * z.re)) (hW : ‖W‖ ≤ Q ^ (-w.re))
    (hD : ‖D1‖ ≤ Q ^ (-ξ.re))
    (hE : ‖E1‖ ≤ Q ^ (4 - 6 * ξ.re - 6 * z.re)) :
    ‖(1 - V) * (1 - W) / (1 - D1) * eulerGoodClosed (Q : ℂ) V W D1 E1 - 1‖ ≤
      128 * Q ^ (-1 - 1 / 4000 : ℝ) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
