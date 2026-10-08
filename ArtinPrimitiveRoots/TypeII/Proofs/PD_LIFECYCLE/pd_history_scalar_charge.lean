import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_active_run_count

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
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
