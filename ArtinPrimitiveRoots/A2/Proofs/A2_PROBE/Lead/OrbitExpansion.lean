import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.OrbitEquiv
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.PeriodicPoisson
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.OrbitAbs
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.OrbitSheet
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

/-- LEAD: integrate the expanded Bm rows using the independent worker parts. -/
theorem orbit_expansion
    (hspec : LeadWeightSpec R sd W) (hcoset : LeadCosetContract sd W)
    (hfinite : LeadFiniteContract R) (hsheets : LeadSheetsContract R sd W)
    (hclass : LeadClassContract (bc := bc) η U)
    (hratio : LeadRatioContract (S := S)) :
    LeadExpansionContract R sd W η U := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
