import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_truncation_choice_majorant
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_doubled_lifespan_bound

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Sum the fixed-path majorant using root_budget and absorb the exponential tail at
B=ceil(L squared). Constants are uniform in the archimedean root.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:504–523. Uses
pd_truncation_choice_majorant, pd_doubled_lifespan_bound and root_budget; feeds the frozen
truncation_adjoint. Choose C_A=1 after increasing the threshold. -/
theorem pd_truncation_tail_absorb (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          ‖historyDistinct F S ρ w - historyDistinctTrunc F S ρ w‖ ≤
            C_A * Real.rpow S.L (-A * (S.N : ℝ)) := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
