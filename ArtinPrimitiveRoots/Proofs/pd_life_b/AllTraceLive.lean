import ArtinPrimitiveRoots.Proofs.pd_life_b.AllTraceLog

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- Valid traces preserve distinct live prime values and their birth-log membership. -/
theorem finiteHistoryTrace_all_live_log_valid {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t)
    (hσ : LiveLogValid σ) :
    FiniteHistoryTraceAll F S γ LiveLogValid k σ t := by
  induction k generalizing σ with
  | zero =>
      have hn := finiteHistoryTrace_all_log_nodup F S w γ 0 σ t ht
      exact ⟨hσ, subsetGhostPoint_live_log_valid F S (pathLength S.x)
        σ t.1 t.2 hσ hn.2⟩
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      have hn := finiteHistoryTrace_all_log_nodup F S w γ (k + 1) σ t ht
      have hτ : LiveLogValid τ :=
        subsetGhostPoint_live_log_valid F S j σ t.1.1 t.1.2 hσ hn.2.1
      have hπ : LiveLogValid (permuteLogPoint t.2.1.1 τ) :=
        permuteLists_live_log_valid τ t.2.1.1 hτ
      let ω := edgeOutputPoint F S j (permuteLogPoint t.2.1.1 τ) t.2.1.2.1 z'
      have hω : LiveLogValid ω :=
        edgeOutputPoint_live_log_valid F S w j (permuteLogPoint t.2.1.1 τ)
          t.2.1.2.1 z' hπ ht.2.2.1 hn.2.2.1
      have hυ : LiveLogValid υ :=
        permuteLists_live_log_valid ω t.2.1.2.2 hω
      exact ⟨hσ, hτ, hυ, ih υ t.2.2 ht.2.2.2 hυ⟩

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
