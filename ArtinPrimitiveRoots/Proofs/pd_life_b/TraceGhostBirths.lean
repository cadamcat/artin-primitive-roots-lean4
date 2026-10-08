import ArtinPrimitiveRoots.Proofs.pd_life_b.AllTraceMemValid

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- Ghost births of a complete trace, recorded in operation order by visit and group. -/
def finiteHistoryTraceGhostBirths {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) :
    (k : ℕ) → (σ : LogPoint S.x K) → FiniteHistoryTrace F S γ k σ →
      List (Fin (pathLength S.x + 1) × Fin K × ℕ)
  | 0, _σ, t =>
      (List.finRange K).flatMap fun i =>
        (t.2 i).1.toList.map fun p => (Fin.last (pathLength S.x), i, p)
  | k + 1, σ, t =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      ((List.finRange K).flatMap fun i =>
        (t.1.2 i).1.toList.map fun p =>
          ((⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ :
            Fin (pathLength S.x + 1)), i, p)) ++
        finiteHistoryTraceGhostBirths F S γ k υ t.2.2

/-- The source log followed by the ghost births embeds in the terminal prime log. -/
theorem finiteHistoryTrace_ghost_birth_values_sublist {K : ℕ}
    (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ) :
    List.Sublist
      (σ.2.map Prod.snd ++
        (finiteHistoryTraceGhostBirths F S γ k σ t).map (fun b => b.2.2))
      ((finiteHistoryTraceTerminal F S γ k σ t).2.map Prod.snd) := by
  have hGhost (j : ℕ) (ω : LogPoint S.x K) (g : GhostTraceChoice F S ω) :
      (ghostTraceOutput F S j ω g).2.map Prod.snd =
        ω.2.map Prod.snd ++ (List.finRange K).flatMap (fun i => (g.2 i).1.toList) := by
    simp only [ghostTraceOutput, subsetGhostPoint, List.map_append,
      List.map_flatMap, List.map_map]
    congr 1
    apply congrArg (List.finRange K).flatMap
    funext i
    change (g.2 i).1.toList.zipIdx.map Prod.fst = (g.2 i).1.toList
    exact List.zipIdx_map_fst 0 _
  have hBirthValues (v : Fin (pathLength S.x + 1))
      (T : (i : Fin K) → (primeBand S.x (F.a i)).powerset) :
      (((List.finRange K).flatMap fun i =>
        (T i).1.toList.map fun p => (v, i, p)).map fun b => b.2.2) =
        (List.finRange K).flatMap (fun i => (T i).1.toList) := by
    simp only [List.map_flatMap, List.map_map, Function.comp_def,
      List.map_id_fun', id_eq]
  induction k generalizing σ with
  | zero =>
      rw [finiteHistoryTraceGhostBirths, finiteHistoryTraceTerminal, hBirthValues,
        hGhost]
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      have hp : List.IsPrefix τ.2 υ.2 := by
        change List.IsPrefix τ.2 (τ.2 ++ _)
        exact List.prefix_append _ _
      have hf := ((hp.sublist.map Prod.snd).append_right
        ((finiteHistoryTraceGhostBirths F S γ k υ t.2.2).map fun b => b.2.2)).trans
          (ih υ t.2.2)
      have hτLog : τ.2.map Prod.snd =
          σ.2.map Prod.snd ++ (List.finRange K).flatMap
            (fun i => (t.1.2 i).1.toList) := hGhost j σ t.1
      rw [hτLog] at hf
      rw [finiteHistoryTraceGhostBirths, List.map_append, hBirthValues,
        ← List.append_assoc]
      exact hf

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
