import ArtinPrimitiveRoots.Proofs.pd_life_b.TraceTerminal

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- Valid traces terminate at the right boundary with a distinct global birth log. -/
theorem finiteHistoryTrace_terminal_tests {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t) :
    let τ := finiteHistoryTraceTerminal F S γ k σ t
    (τ.1.1 = (1, 0) ∧ ∀ i, τ.1.2.2 i = []) ∧
      (τ.2.map Prod.snd).Nodup := by
  induction k generalizing σ with
  | zero => exact ht.2.2
  | succ k ih => exact ih _ t.2.2 ht.2.2.2

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
