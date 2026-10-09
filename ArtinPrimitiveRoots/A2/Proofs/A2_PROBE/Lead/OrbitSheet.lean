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

/-- IMPL: exact nonzero-frequency regrouping and its full absolute unfolding. -/
theorem orbit_sheet_sum
    (hzero : leadFourier sd W 0 = 0)
    (hcoset : LeadCosetContract sd W)
    (hfinite : LeadFiniteContract R) (hsheets : LeadSheetsContract R sd W)
    (hequiv : LeadEquivContract (bc := bc) η U)
    (s I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1)
    (hallowed : Bd.Allowed a) (X : ℝ) (hX : 0 < X) :
    Summable (fun ur : U.U × S.ExtIdeal =>
      ‖leadFiniteFactor R s I a ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6) *
        leadV0 R sd W (X * U.q ur.1 * qI ur.2.1 ^ 6 / qI I.1)‖) ∧
    IntegrableOn (fun y : S.FS =>
      onUnits (fun t : S.FSˣ =>
        ∑' h : S.R, leadFiniteFactor R s I a (h : F) *
          leadFourier sd W (((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ) : S.FS) *
            S.diag ((h : F) / ((bc.gen s : F) * (a : F))))) y)
      (omegaAt R 1) (R.sheets.sheet 1) ∧
    omegaInt R 1 (fun t : S.FSˣ =>
      ∑' h : S.R, leadFiniteFactor R s I a (h : F) *
        leadFourier sd W (((t * R.sheets.ellU (qI s.1 * X) : S.FSˣ) : S.FS) *
          S.diag ((h : F) / ((bc.gen s : F) * (a : F))))) =
      ∑' ur : U.U × S.ExtIdeal,
        leadFiniteFactor R s I a ((U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6) *
          leadV0 R sd W (X * U.q ur.1 * qI ur.2.1 ^ 6 / qI I.1) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
