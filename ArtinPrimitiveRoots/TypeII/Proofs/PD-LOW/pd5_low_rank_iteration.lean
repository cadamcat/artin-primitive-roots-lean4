import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDLow.pd5_boundary_norm_near_one
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDLow.pd5_phase_at_births
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDLow.pd5_modified_ops_symmetry_domination
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDHigh.pd5_rank_support_mass

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Iterate norms on the finite invariant state set, with at most twice the rank modified
edges. The exponent uses real N-2r even when negative. Guide
`runs/lanes/sol-thin-pd5/PROOFS.md:771–832`; uses boundary, finite model, Fourier, phase
attachment, rank support and the supplied modified bounds; feeds frozen history_rank_low. -/
theorem pd5_low_rank_iteration (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ)
    (hboundary : PD5BoundaryAvailable δ c₁ c₂ F)
    (hmodified : PD5ModifiedBoundsAvailable δ c₁ c₂ F ρ) :
    ∃ C_K Ccr x₀ : ℝ, 0 < C_K ∧ 0 < Ccr ∧ 2 ≤ x₀ ∧
      ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
        ∀ G : ℝ, 0 < G →
          (∀ j : ℕ, j < S.N →
            MemOpNormLE_sym F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
              (Real.rpow S.L (-G))) →
          ∀ C ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)),
            ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ ≤
              2 * C_K ^ (S.N + 1) *
                Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (constraintRank C : ℝ))) *
                Real.rpow S.L (2 * Ccr * (constraintRank C : ℝ)) := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
