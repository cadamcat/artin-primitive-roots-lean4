import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.MellinTerm
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.MellinFubini
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

/-- LEAD: final exact triple identity from the earlier orbit target and worker inversions. -/
theorem mellin_identity
    (horbit : LeadExpansionContract R sd W η U)
    (hinv : LeadInversionsContract R sd W)
    (hdecay : LeadWeightDecay R sd W) (hcoeff : LeadCoeffBoundContract R η U)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    leadProbe R W X Y Z = leadTripleVertical 4 4 2 (fun ξ w z =>
      leadMellinWeight R sd W X Y Z ξ w z *
        ∑' u : U.U, (U.q u : ℂ) ^ (-z) * leadCalF R η U u ξ w z) := by
  rw [(mellin_sum_interchange R sd W η U hdecay hcoeff X Y Z hX hY hZ).2.2,
    (horbit X Y Z hX hY hZ).2, ← tsum_mul_left]
  exact tsum_congr fun p =>
    mellin_term_inversion R sd W η U hinv hdecay X Y Z hX hY hZ p

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
