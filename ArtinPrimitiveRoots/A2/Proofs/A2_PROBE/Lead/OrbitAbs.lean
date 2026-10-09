import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Contracts
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
variable (W : ProbeWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)

/-- IMPL: full absolute-sheet control and Gaussian order 4 give all five sums. -/
theorem orbit_abs_summable
    (hfinite : LeadFiniteContract R) (hsheets : LeadSheetsContract R sd W)
    (hequiv : LeadEquivContract (bc := bc) η U) :
    ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
      Summable (fun p => ‖leadOrbitTerm R sd W η U X Y Z p‖) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
