import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_edge_position_mass_le
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_scale_facts

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Prefix-dependent prescribed coordinates cost one atom each. A prescription reads only
strictly earlier coordinates, including earlier coordinates of the same batch.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:207–243`; uses finite sum decomposition only;
feeds pd5_positive_choice_rows. LEAD. -/
theorem pd5_triangular_birth_sum_le (n : ℕ) (P : Fin n → Finset ℕ)
    (ν : Fin n → ℕ → ℝ) (R : Finset (Fin n)) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (pick : (k : Fin n) → (Fin k.val → ℕ) → ℕ)
    (hν : ∀ k p, p ∈ P k → 0 ≤ ν k p)
    (hatom : ∀ k ∈ R, ∀ p ∈ P k, ν k p ≤ Δ) :
    (∑ b : (k : Fin n) → {p : ℕ // p ∈ P k},
      if ∀ k ∈ R, (b k : ℕ) = pick k
        (fun j => (b ⟨j.val, lt_trans j.isLt k.isLt⟩ : ℕ))
      then ∏ k : Fin n, ν k (b k) else 0) ≤
      ∏ k : Fin n, if k ∈ R then Δ else ∑ p ∈ P k, ν k p := by
  sorry

/-- Uniform finite positive-choice rows with performed flags and chronological prescriptions.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:151–327`; uses pd5_scale_facts,
pd5_triangular_birth_sum_le, the deletion binomial sum and uniform geometric target count;
feeds pd5_fixed_system_abs_estimate and frozen history_rank_high. LEAD. -/
theorem pd5_positive_choice_rows (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) :
    PD5PositiveRowsAvailable δ c₁ c₂ F ρ := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
