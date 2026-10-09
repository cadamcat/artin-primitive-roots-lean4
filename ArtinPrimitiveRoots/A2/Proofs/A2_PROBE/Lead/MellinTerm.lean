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

/-- IMPL: three pointwise inversions with the Gaussian height shear. -/
theorem mellin_term_inversion
    (hinv : LeadInversionsContract R sd W)
    (hdecay : LeadWeightDecay R sd W)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal) :
    ((X ^ (1 / 2 : ℝ) / Y : ℝ) : ℂ) * leadOrbitTerm R sd W η U X Y Z p =
      leadTripleVertical 4 4 2 (fun ξ w z => leadMellinTerm R sd W η U X Y Z ξ w z p) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
