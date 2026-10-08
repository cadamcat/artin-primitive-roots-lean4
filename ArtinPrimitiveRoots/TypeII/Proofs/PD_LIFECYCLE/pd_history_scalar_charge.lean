import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_active_run_count
import ArtinPrimitiveRoots.TypeII.Proofs.pcr_opus.ScalarCharge

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Exact scalar charge for every valid lifespan assignment: all rho factors cancel,
nu and promotion factors pay one V inverse per active run, and the run count extracts
physicalMeasure and the N edge normalizations.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:434–449. Uses pd_active_run_count and
pd_lifecycle_parameters; feeds the ordered history assembly and the common cutoff majorant.
The statement is per assignment, so every cutoff selector can be retained. -/
theorem pd_history_scalar_charge (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ γ : EnvPath S.x K, IsEnvPathAdmissible F S γ → pathCoefficient F S γ ≠ 0 →
          ∀ H : PDLifeAssignment F S γ,
            pdRawAssignmentCharge F S ρ γ H =
              pdActiveNormalization F S * pdLifeAssignmentCharge F S γ H := by
  intro K F hF ρ hρ
  obtain ⟨x₁, hx₁, hpar⟩ := pd_lifecycle_parameters K F hF
  obtain ⟨x₂, hx₂, hruns⟩ := pd_active_run_count δ c₁ c₂ hδ hc₁ K F hF
  refine ⟨max x₁ x₂, le_trans hx₁ (le_max_left _ _), ?_⟩
  intro S hS hxS γ hγ hcoef H
  have hV : ∀ i, 0 < bandMass S.x (F.a i) := fun i =>
    ((hpar S.x (le_trans (le_max_left _ _) hxS)).1 i).1
  exact pcr_scalar_charge_of_runs F S ρ hρ.1.ne' γ H hV
    (hruns S hS (le_trans (le_max_right _ _) hxS) γ hγ hcoef)

end
end ArtinPrimitiveRoots.TypeII.PD
