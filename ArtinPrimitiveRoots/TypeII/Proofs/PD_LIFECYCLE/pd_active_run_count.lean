import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_lifecycle_parameters

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- On a nonzero path each group has M initial runs and exactly one new run per edge.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:434–449. Uses the support of symKernel,
IsSlotTransition and disjoint bands; feeds pd_history_scalar_charge and the active count
in pd_doubled_lifespan_bound. Odd edges give the same undirected set transition. -/
theorem pd_active_run_count (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ γ : EnvPath S.x K, IsEnvPathAdmissible F S γ → pathCoefficient F S γ ≠ 0 →
          ∀ i : Fin K, (∑ p : primeBand S.x (F.a i), pdActiveRuns S γ p.1) =
            slotCount S.x + pathLength S.x := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
