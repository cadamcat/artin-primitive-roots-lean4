import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_positive_choice_rows
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_chronological_model

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Fixed-system absolute bound from positive choices, with chronological pivots.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:328–397`; uses pd5_positive_choice_rows,
pd5_triangular_birth_sum_le, pd5_chronological_model and pd5_scale_facts;
feeds pd5_high_rank_tail and frozen history_rank_high. Constants precede S,w and the system. -/
theorem pd5_fixed_system_abs_estimate (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ)
    (hrows : PD5PositiveRowsAvailable δ c₁ c₂ F ρ) :
    ∃ Cabs aAtom x₀ : ℝ, 0 < Cabs ∧ 0 < aAtom ∧ 2 ≤ x₀ ∧
      ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
        ∀ C ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)),
          ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ ≤
            Real.rpow S.L (Cabs * ((S.N : ℝ) + 1)) *
              (aAtom * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))) ^ constraintRank C := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
