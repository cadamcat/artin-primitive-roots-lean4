import ArtinPrimitiveRoots.Proofs.pd_life_b.TerminalTests

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- A state invariant at every source, ghost output, and edge output of a trace. -/
def FiniteHistoryTraceAll {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (P : LogPoint S.x K → Prop) :
    (k : ℕ) → (σ : LogPoint S.x K) → FiniteHistoryTrace F S γ k σ → Prop
  | 0, σ, t => P σ ∧ P (ghostTraceOutput F S (pathLength S.x) σ t)
  | k + 1, σ, t =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      P σ ∧ P τ ∧ P υ ∧ FiniteHistoryTraceAll F S γ P k υ t.2.2

/-- Every intermediate birth log of a valid trace has distinct prime values. -/
theorem finiteHistoryTrace_all_log_nodup {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t) :
    FiniteHistoryTraceAll F S γ (fun υ => (υ.2.map Prod.snd).Nodup) k σ t := by
  have hSource (m : ℕ) (ω : LogPoint S.x K) (q : FiniteHistoryTrace F S γ m ω)
      (hq : FiniteHistoryTraceValid F S w γ m ω q) :
      (ω.2.map Prod.snd).Nodup := by
    have hsub := (finiteHistoryTrace_log_prefix F S γ m ω q).sublist.map Prod.snd
    exact hsub.nodup (finiteHistoryTrace_terminal_tests F S w γ m ω q hq).2
  induction k generalizing σ with
  | zero =>
      exact ⟨hSource 0 σ t ht,
        (finiteHistoryTrace_terminal_tests F S w γ 0 σ t ht).2⟩
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      have hυ := hSource k υ t.2.2 ht.2.2.2
      have hp : List.IsPrefix τ.2 υ.2 := by
        change List.IsPrefix τ.2 (τ.2 ++ _)
        exact List.prefix_append _ _
      have hτ := (hp.sublist.map Prod.snd).nodup hυ
      exact ⟨hSource (k + 1) σ t ht, hτ, hυ, ih υ t.2.2 ht.2.2.2⟩

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
