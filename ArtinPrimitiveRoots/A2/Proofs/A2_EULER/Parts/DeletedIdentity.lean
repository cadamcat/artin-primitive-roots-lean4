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

theorem deleted_identity (HC : EulerCorrection R η U) (HA : HeckeAnalysis F)
    (hE : EulerHypotheses R η)
    (hfactor : ∀ u ξ w z, initialRegion ξ w z →
      HasProd (fun v : {v : FinPlace F // v ∉ S.Sf} => localEuler R η U u v.1 v.2 ξ w z)
        (calF R η U u ξ w z))
    (hH : ∀ u p, eulerNeighborhood p → HasProd
      (fun v : {v : FinPlace F // v ∉ S.Sf} =>
        normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)) (HC.H u p)) :
    ∀ u ξ w z, initialRegion ξ w z →
      calF R η U u ξ w z = HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ,w,z] /
        HA.LS S (η * (U.kummer u)⁻¹) ξ := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
