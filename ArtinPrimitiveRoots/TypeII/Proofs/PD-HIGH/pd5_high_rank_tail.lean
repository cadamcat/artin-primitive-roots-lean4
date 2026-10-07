import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDHigh.pd5_fixed_system_abs_estimate
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDHigh.pd5_rank_support_mass

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Finite rank grouping, geometric tail and the exact frozen exponent; the existing 3r mass
bound replaces the guide's proposed 2r decoration proof without changing the conclusion.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:456–493`; uses pd5_scale_facts,
pd5_rank_support_mass and the supplied fixed-system bound; feeds frozen history_rank_high. -/
theorem pd5_high_rank_tail (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ)
    (E₀ : ℝ) (hE₀ : 0 < E₀)
    (hfixed : ∃ Cabs aAtom x₀ : ℝ, 0 < Cabs ∧ 0 < aAtom ∧ 2 ≤ x₀ ∧
      ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
        ∀ C ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)),
          ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ ≤
            Real.rpow S.L (Cabs * ((S.N : ℝ) + 1)) *
              (aAtom * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))) ^ constraintRank C) :
    ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
      ∀ w : ArchRoot, w.InRegion S →
        (∑ C ∈ (constraintSystems (birthAddresses S.x K (memoryCutoff S))).filter
          (fun C => ⌈C' * (S.N : ℝ) * Real.log S.L / Real.rpow S.L (1 / 10 : ℝ)⌉₊ ≤
            constraintRank C),
          |(constraintCoeff C : ℝ)| *
            ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖) ≤
          Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
