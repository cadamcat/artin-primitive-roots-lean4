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

/-- IMPL: dominate the individual terms before moving all sums through the integral. -/
theorem mellin_sum_interchange
    (hdecay : LeadWeightDecay R sd W) (hcoeff : LeadCoeffBoundContract R η U)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    (∀ p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal,
      Integrable (fun t : ℝ × ℝ × ℝ =>
        leadMellinTerm R sd W η U X Y Z (4 + t.1 * Complex.I)
          (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I) p)) ∧
    Summable (fun p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal =>
      ∫ t : ℝ × ℝ × ℝ,
        ‖leadMellinTerm R sd W η U X Y Z (4 + t.1 * Complex.I)
          (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I) p‖) ∧
    leadTripleVertical 4 4 2 (fun ξ w z =>
      leadMellinWeight R sd W X Y Z ξ w z *
        ∑' u : U.U, (U.q u : ℂ) ^ (-z) * leadCalF R η U u ξ w z) =
      ∑' p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal,
        leadTripleVertical 4 4 2 (fun ξ w z =>
          leadMellinTerm R sd W η U X Y Z ξ w z p) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
