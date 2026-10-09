import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import Mathlib.Analysis.Normed.Group.Tannery

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

theorem product_limit (B : PrimeTupleBridge S) (u : U.U) (ξ w z : ℂ)
    (hs : Summable (fun p : IdealTuple S => ‖calFTerm R η U u ξ w z p‖))
    (hfinite : ∀ V : Finset (ExteriorPrime S),
      (∏ v ∈ V, localEuler R η U u v.1 v.2 ξ w z) =
        ∑' p : IdealTuple S, if (B.equiv p).support ⊆ V then calFTerm R η U u ξ w z p else 0) :
    HasProd (fun v : ExteriorPrime S => localEuler R η U u v.1 v.2 ξ w z)
      (calF R η U u ξ w z) := by
  change Filter.Tendsto
    (fun V : Finset (ExteriorPrime S) =>
      ∏ v ∈ V, localEuler R η U u v.1 v.2 ξ w z)
    Filter.atTop (𝓝 (calF R η U u ξ w z))
  have hpoint (p : IdealTuple S) : Filter.Tendsto
      (fun V : Finset (ExteriorPrime S) =>
        if (B.equiv p).support ⊆ V then calFTerm R η U u ξ w z p else 0)
      Filter.atTop (𝓝 (calFTerm R η U u ξ w z p)) := by
    refine Filter.Tendsto.congr' ?_
      (tendsto_const_nhds (x := calFTerm R η U u ξ w z p))
    exact (Filter.eventually_ge_atTop (B.equiv p).support).mono
      (fun V hV => by simp only [if_pos hV])
  have hlim := tendsto_tsum_of_dominated_convergence
    (f := fun (V : Finset (ExteriorPrime S)) (p : IdealTuple S) =>
      if (B.equiv p).support ⊆ V then calFTerm R η U u ξ w z p else 0)
    (g := fun p : IdealTuple S => calFTerm R η U u ξ w z p) hs hpoint
    (Filter.Eventually.of_forall (fun V p => by
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (calFTerm R η U u ξ w z p)))
  simpa only [← hfinite, calF] using hlim

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
