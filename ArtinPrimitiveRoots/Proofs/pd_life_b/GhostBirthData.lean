import ArtinPrimitiveRoots.Proofs.pd_life_b.TraceGhostBirths

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- Extracted ghost births have unique fresh prime values in their recorded group bands. -/
theorem finiteHistoryTrace_ghost_birth_data {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t) :
    let G := finiteHistoryTraceGhostBirths F S γ k σ t
    (G.map (fun b => b.2.2)).Nodup ∧
      List.Disjoint (σ.2.map Prod.snd) (G.map (fun b => b.2.2)) ∧
      ∀ b ∈ G, b.2.2 ∈ primeBand S.x (F.a b.2.1) := by
  have hBlock (v : Fin (pathLength S.x + 1))
      (T : (i : Fin K) → (primeBand S.x (F.a i)).powerset)
      (b : Fin (pathLength S.x + 1) × Fin K × ℕ)
      (hb : b ∈ (List.finRange K).flatMap fun i =>
        (T i).1.toList.map fun p => (v, i, p)) :
      b.2.2 ∈ primeBand S.x (F.a b.2.1) := by
    rcases List.mem_flatMap.mp hb with ⟨i, _, hi⟩
    rcases List.mem_map.mp hi with ⟨p, hp, rfl⟩
    exact (Finset.mem_powerset.mp (T i).2) (Finset.mem_toList.mp hp)
  have hBand (m : ℕ) (ω : LogPoint S.x K) (q : FiniteHistoryTrace F S γ m ω) :
      ∀ b ∈ finiteHistoryTraceGhostBirths F S γ m ω q,
        b.2.2 ∈ primeBand S.x (F.a b.2.1) := by
    induction m generalizing ω with
    | zero =>
        intro b hb
        exact hBlock (Fin.last (pathLength S.x)) q.2 b hb
    | succ m ih =>
        intro b hb
        rw [finiteHistoryTraceGhostBirths] at hb
        rcases List.mem_append.mp hb with hb | hb
        · exact hBlock _ q.1.2 b hb
        · exact ih _ q.2.2 b hb
  have hN := (finiteHistoryTrace_ghost_birth_values_sublist F S γ k σ t).nodup
    (finiteHistoryTrace_terminal_tests F S w γ k σ t ht).2
  have hParts := List.nodup_append'.mp hN
  exact ⟨hParts.2.1, hParts.2.2, hBand k σ t⟩

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
