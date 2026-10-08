import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_ordered_birth_bijection
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_history_scalar_charge
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_life_memory_bound

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Lifespan selectors omit only assignments with more than B-KN ghost births, yielding
the doubled finite choice majorant. The complete error decomposes over contributing paths.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:454–481. Uses
pd_ordered_birth_bijection and pd_history_scalar_charge; feeds pd_truncation_tail_absorb.
Factor the common signed path coefficient before taking the norm. -/
theorem pd_truncation_choice_majorant (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S → ∀ B : ℕ, K * pathLength S.x ≤ B →
          (memHistory F S ρ w none none distinctWeight -
              memHistory F S ρ w (some B) none distinctWeight =
            ∑' γ : EnvPath S.x K, if IsContributingPath F S γ then
              memHistory F S ρ w none (some γ) distinctWeight -
                memHistory F S ρ w (some B) (some γ) distinctWeight else 0) ∧
          (∀ γ : EnvPath S.x K, IsEnvPathAdmissible F S γ →
            ‖memHistory F S ρ w none (some γ) distinctWeight -
                memHistory F S ρ w (some B) (some γ) distinctWeight‖ ≤
              (2 : ℝ) ^ (-(B : ℤ) + (K * pathLength S.x : ℤ)) *
                ‖pathCoefficient F S γ‖ * pathArch F S w γ * doubledLifeMajorant F S γ) := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
