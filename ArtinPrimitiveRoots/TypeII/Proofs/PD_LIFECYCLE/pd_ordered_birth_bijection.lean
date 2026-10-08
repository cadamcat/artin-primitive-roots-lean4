import ArtinPrimitiveRoots.Proofs.pd_life_b.BoundarySupport
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_ordered_distinct_batch_sum

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Ordered distinct histories are the finite lifespan sum with the same memory cutoff.
Batch orderings cancel each local ghost factorial; unique old indices give no factorial.
Active symmetrizations and raw-minus-comparison choices give the signed pathCoefficient
before any norm is taken. The normalization is nonzero at this threshold.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:386–433,447–449,454–473. Uses finite distinct
history support, projective-line transport and ordered_distinct_batch_sum; feeds
history_path_value and pd_truncation_choice_majorant. Defs records literal raw charges;
pd_history_scalar_charge is applied by consumers, not assumed by this bijection. -/
theorem pd_ordered_birth_bijection (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        pdActiveNormalization F S ≠ 0 ∧
        ∀ w : ArchRoot, w.InRegion S → ∀ γ : EnvPath S.x K,
          IsEnvPathAdmissible F S γ → ∀ B : Option ℕ,
            memHistory F S ρ w B (some γ) distinctWeight =
              pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
                ((pdActiveNormalization F S)⁻¹ * pdRawHistorySum F S ρ γ B : ℝ) := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
