import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Contracts
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.pr_b.PeriodicPoissonProof
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

/-- IMPL: periodize the actual residue coefficients, then apply the coset contract. -/
theorem periodic_poisson
    (hcoset : LeadCosetContract sd W) (hfinite : LeadFiniteContract R)
    (s I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1)
    (hallowed : Bd.Allowed a) (k : S.FSˣ) :
    Summable (fun m : S.R =>
      ‖(qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * leadFiniteGauss R s (-(m : F)) *
        chiIdealPow D I.1 (m : F) 1 *
          W.W0 (S.diag (m : F) * (k⁻¹ : S.FSˣ).val)‖) ∧
    Summable (fun h : S.R =>
      ‖leadFiniteFactor R s I a (h : F) *
        leadFourier sd W ((k : S.FS) *
          S.diag ((h : F) / ((bc.gen s : F) * (a : F))))‖) ∧
    (∑' m : S.R,
      (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * leadFiniteGauss R s (-(m : F)) *
        chiIdealPow D I.1 (m : F) 1 *
          W.W0 (S.diag (m : F) * (k⁻¹ : S.FSˣ).val)) =
      ((S.absS (k : S.FS) / (qI s.1 ^ (1 / 2 : ℝ) * qI I.1) : ℝ) : ℂ) *
        ∑' h : S.R, leadFiniteFactor R s I a (h : F) *
          leadFourier sd W ((k : S.FS) *
            S.diag ((h : F) / ((bc.gen s : F) * (a : F)))) := by
  exact ArtinPrimitiveRoots.Proofs.pr_b.periodicPoisson
    R sd W hcoset hfinite s I a ha hallowed k

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
