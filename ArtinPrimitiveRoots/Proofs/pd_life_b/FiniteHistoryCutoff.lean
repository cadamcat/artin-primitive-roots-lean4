import ArtinPrimitiveRoots.Proofs.pd_life_b.FiniteHistoryTrace

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- The maximum over every state where the literal trace weight tests memory size. -/
def finiteHistoryTraceMaxMemory {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) :
    (k : ℕ) → (σ : LogPoint S.x K) → FiniteHistoryTrace F S γ k σ → ℕ
  | 0, σ, t =>
      max (memSize σ.1)
        (memSize (ghostTraceOutput F S (pathLength S.x) σ t).1)
  | k + 1, σ, t =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      max (memSize σ.1)
        (max (memSize τ.1)
          (max (memSize υ.1)
            (finiteHistoryTraceMaxMemory F S γ k υ t.2.2)))

/-- A trace survives truncation exactly when all of its tested memory sizes fit. -/
theorem finiteHistoryTraceWeight_cutoff_selector {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (γ : EnvPath S.x K) (b k : ℕ) (σ : LogPoint S.x K)
    (t : FiniteHistoryTrace F S γ k σ) :
    finiteHistoryTraceWeight F S ρ w (some b) γ k σ t =
      if finiteHistoryTraceMaxMemory F S γ k σ t ≤ b then
        finiteHistoryTraceWeight F S ρ w none γ k σ t
      else 0 := by
  classical
  induction k generalizing σ with
  | zero =>
      let τ := ghostTraceOutput F S (pathLength S.x) σ t
      by_cases hs : memSize σ.1 ≤ b <;>
        by_cases ht : memSize τ.1 ≤ b <;>
        simp [finiteHistoryTraceMaxMemory, finiteHistoryTraceWeight,
          historyCutoffFactor, hs, ht, τ]
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      have hi := ih υ t.2.2
      by_cases hs : memSize σ.1 ≤ b <;>
        by_cases ht : memSize τ.1 ≤ b <;>
        by_cases he : memSize υ.1 ≤ b <;>
        by_cases hr : finiteHistoryTraceMaxMemory F S γ k υ t.2.2 ≤ b <;>
        simp [finiteHistoryTraceMaxMemory, finiteHistoryTraceWeight,
          historyCutoffFactor, hi, hs, ht, he, hr, j, τ, z', υ]

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
