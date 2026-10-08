import ArtinPrimitiveRoots.Proofs.pd_life_b.ValidHistorySum

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- The logged state after the terminal ghost operation of a complete finite trace. -/
def finiteHistoryTraceTerminal {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) :
    (k : ℕ) → (σ : LogPoint S.x K) → FiniteHistoryTrace F S γ k σ →
      LogPoint S.x K
  | 0, σ, t => ghostTraceOutput F S (pathLength S.x) σ t
  | k + 1, σ, t =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      finiteHistoryTraceTerminal F S γ k υ t.2.2

/-- Every trace retains its source birth log as a prefix of its terminal log. -/
theorem finiteHistoryTrace_log_prefix {K : ℕ}
    (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ) :
    List.IsPrefix σ.2 (finiteHistoryTraceTerminal F S γ k σ t).2 := by
  have hGhost (j : ℕ) (τ : LogPoint S.x K) (g : GhostTraceChoice F S τ) :
      List.IsPrefix τ.2 (ghostTraceOutput F S j τ g).2 := by
    change List.IsPrefix τ.2 (τ.2 ++ _)
    exact List.prefix_append _ _
  have hEdge (j : ℕ) (z' : ℤ × ℤ) (τ : LogPoint S.x K)
      (e : EdgeTraceChoice F S τ) :
      List.IsPrefix τ.2 (edgeTraceOutput F S j z' τ e).2 := by
    change List.IsPrefix τ.2 (τ.2 ++ _)
    exact List.prefix_append _ _
  induction k generalizing σ with
  | zero => exact hGhost (pathLength S.x) σ t
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      exact (hGhost j σ t.1).trans ((hEdge j z' τ t.2.1).trans (ih υ t.2.2))

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
