import ArtinPrimitiveRoots.Proofs.pd_life_b.FixedHistoryEdge

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- The finite subset-batch form of the distinct-birth ghost operation. -/
def subsetGhost {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (f : LogPoint S.x K → ℂ) : LogPoint S.x K → ℂ :=
  fun σ =>
    ∑ D : (i : Fin K) → Finset (Fin (σ.1.2.2 i).length),
      ∑ T : (i : Fin K) → (primeBand S.x (F.a i)).powerset,
        if ∀ i, D i ⊆ hitIndices (σ.1.2.2 i) σ.1.1 then
          ((∏ i : Fin K,
              (-memoryEta S.x F.q_d j / ρ) ^ (D i).card *
              (memoryQ S.x F.q_d j / ρ ^ 2) ^
                (hitCount (σ.1.2.2 i) σ.1.1 - (D i).card) *
              (-memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ) ^ (T i).1.card *
              (∏ p ∈ (T i).1, memoryNu S.x K F.a F.q_d i p) : ℝ) : ℂ) *
            f (subsetGhostPoint F S j σ D T)
        else 0

def finiteHistoryFn {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : Option ℕ) (γ : EnvPath S.x K) :
    ℕ → LogPoint S.x K → ℂ
  | 0 => logTrunc B (logPathRestrict (some γ) (pathLength S.x)
      (subsetGhost F S ρ (pathLength S.x) (logTrunc B (logBoundaryOut distinctWeight))))
  | k + 1 =>
      let j := pathLength S.x - (k + 1)
      logTrunc B (logPathRestrict (some γ) j (subsetGhost F S ρ j (logTrunc B
        (edgeAtPosition F S ρ w j
          (γ ⟨pathLength S.x - k, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
          (logTrunc B (finiteHistoryFn F S ρ w B γ k))))))

theorem logHistoryFn_eq_finite {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : Option ℕ) (γ : EnvPath S.x K)
    (k : ℕ) (hk : k ≤ pathLength S.x) (σ : LogPoint S.x K) :
    logHistoryFn F S ρ w B (some γ) distinctWeight k σ =
      finiteHistoryFn F S ρ w B γ k σ := by
  classical
  have hSym (f : LogPoint S.x K → ℂ) (hf : RespectsLoggedPerm f) :
      RespectsLoggedPerm (logSym F S f) := by
    intro τ υ h
    unfold logSym
    congr 1
    apply Finset.sum_congr rfl
    intro π _
    apply hf
    exact ⟨h.1, congrArg (permuteLists π) h.2.1, h.2.2.1, h.2.2.2⟩
  have hTrunc (f : LogPoint S.x K → ℂ) (hf : RespectsLoggedPerm f) :
      RespectsLoggedPerm (logTrunc B f) := by
    intro τ υ h
    have hSize : memSize τ.1 = memSize υ.1 := by
      unfold memSize
      apply Finset.sum_congr rfl
      intro i _
      exact (h.2.2.1 i).length_eq
    cases B with
    | none => exact hf τ υ h
    | some b =>
        change (if memSize τ.1 ≤ b then f τ else 0) =
          (if memSize υ.1 ≤ b then f υ else 0)
        rw [hSize, hf τ υ h]
  have hEdge (j : ℕ) (f : LogPoint S.x K → ℂ) (hf : RespectsLoggedPerm f) :
      RespectsLoggedPerm (logEdge F S ρ w EdgeKind.full j f) := by
    change RespectsLoggedPerm (logSym F S fun τ =>
      ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w j true St Pr (logSym F S f) τ -
          logEdgePiece F S ρ w j false St Pr (logSym F S f) τ))
    apply hSym
    intro τ υ h
    apply Finset.sum_congr rfl
    intro St _
    apply Finset.sum_congr rfl
    intro Pr _
    have hPiece (raw : Bool) :=
      logEdgePiece_respects_perm F S ρ w j raw St Pr (logSym F S f)
        (hSym f hf) τ υ h
    exact congrArg₂ (fun a b : ℂ => a - b) (hPiece true) (hPiece false)
  have hBoundary :
      RespectsLoggedPerm (logBoundaryOut (x := S.x) (distinctWeight (K := K))) := by
    rintro ⟨s, L⟩ ⟨t, M⟩ ⟨hz, hp, hm, hl⟩
    change s.1 = t.1 at hz
    change ∀ i, (s.2.2 i).Perm (t.2.2 i) at hm
    change (L.map Prod.snd).Perm (M.map Prod.snd) at hl
    have hEmpty (i : Fin K) : s.2.2 i = [] ↔ t.2.2 i = [] := by
      simp only [← List.length_eq_zero_iff, (hm i).length_eq]
    have hAllEmpty : (∀ i, s.2.2 i = []) ↔ ∀ i, t.2.2 i = [] :=
      forall_congr' hEmpty
    have hb : memBoundary s = memBoundary t := by
      simp only [memBoundary, hz, hAllEmpty]
    have hd : distinctWeight L = distinctWeight M := by
      simp only [distinctWeight, hl.nodup_iff]
    change memBoundary s * distinctWeight L = memBoundary t * distinctWeight M
    rw [hb, hd]
  have hHistory (n : ℕ) :
      RespectsLoggedPerm (logHistoryFn F S ρ w B (some γ) distinctWeight n) := by
    intro τ υ h
    exact history_continuation_perm F S ρ w B (some γ) n τ.1 υ.1 τ.2 υ.2
      h.1 h.2.1 h.2.2.1 h.2.2.2
  have hTruncBad (f : LogPoint S.x K → ℂ)
      (hf : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup → f τ = 0) :
      ∀ τ, ¬ (τ.2.map Prod.snd).Nodup → logTrunc B f τ = 0 := by
    intro τ hbad
    cases B <;> simp only [logTrunc, hf τ hbad, ite_self]
  have hSymBad (f : LogPoint S.x K → ℂ)
      (hf : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup → f τ = 0) :
      ∀ τ, ¬ (τ.2.map Prod.snd).Nodup → logSym F S f τ = 0 := by
    intro τ hbad
    unfold logSym
    have hsum : (∑ π : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        f ((τ.1.1, permuteLists π τ.1.2.1, τ.1.2.2), τ.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro π _
      exact hf _ hbad
    rw [hsum, mul_zero]
  have hBoundaryBad : ∀ τ : LogPoint S.x K,
      ¬ (τ.2.map Prod.snd).Nodup → logBoundaryOut distinctWeight τ = 0 := by
    intro τ hbad
    simp only [logBoundaryOut, distinctWeight, ite_eq_right hbad, mul_zero]
  have hHistoryBad (n : ℕ) : ∀ τ : LogPoint S.x K,
      ¬ (τ.2.map Prod.snd).Nodup →
        logHistoryFn F S ρ w B (some γ) distinctWeight n τ = 0 := by
    cases B with
    | none => exact pd_life_b_logHistoryFn_zero_of_badLog F S ρ w (some γ) n
    | some b => exact pd_life_b_logHistoryFn_zero_of_badLog_cutoff F S ρ w b (some γ) n
  have hEdgeAtBad (j : ℕ) (z' : ℤ × ℤ) (f : LogPoint S.x K → ℂ)
      (hf : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup → f τ = 0) :
      ∀ τ, ¬ (τ.2.map Prod.snd).Nodup → edgeAtPosition F S ρ w j z' f τ = 0 := by
    unfold edgeAtPosition
    apply hSymBad
    intro τ hbad
    apply Finset.sum_eq_zero
    intro St _
    apply Finset.sum_eq_zero
    intro Pr _
    have hPiece (raw : Bool) :
        edgePieceAtPosition F S ρ w j raw St Pr z' (logSym F S f) τ = 0 := by
      unfold edgePieceAtPosition
      dsimp only
      apply Finset.sum_eq_zero
      intro c _
      by_cases hg : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
          EdgeAdmissible F S w τ.1 c z'
      · rw [ite_eq_left hg]
        have hOutBad : ¬ ((edgeOutputPoint F S j τ c z').2.map Prod.snd).Nodup := by
          intro hout
          apply hbad
          have hPrefix : (τ.2.map Prod.snd ++
              (edgeBirths F S j τ.1 c).map Prod.snd).Nodup := by
            simpa only [edgeOutputPoint, List.map_append] using hout
          exact (List.nodup_append.mp hPrefix).1
        have hzero : logSym F S f (edgeOutputPoint F S j τ c z') = 0 :=
          hSymBad f hf _ hOutBad
        rw [hzero, mul_zero]
      · exact ite_eq_right hg
    rw [hPiece true, hPiece false, sub_self]
  have hGhost (j : ℕ) (f : LogPoint S.x K → ℂ) (hf : RespectsLoggedPerm f)
      (hbad : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup → f τ = 0) :
      logGhost F S ρ j f = subsetGhost F S ρ j f := by
    funext τ
    exact logGhost_eq_subset_batches F S ρ j f hf hbad τ
  have hAll : ∀ n : ℕ, n ≤ pathLength S.x → ∀ τ : LogPoint S.x K,
      logHistoryFn F S ρ w B (some γ) distinctWeight n τ =
        finiteHistoryFn F S ρ w B γ n τ := by
    intro n
    induction n with
    | zero =>
        intro hn τ
        simp only [logHistoryFn, finiteHistoryFn]
        rw [hGhost (pathLength S.x) _ (hTrunc _ hBoundary)
          (hTruncBad _ hBoundaryBad)]
    | succ n ih =>
        intro hn τ
        have hn' : n ≤ pathLength S.x := by omega
        let j := pathLength S.x - (n + 1)
        let G := logTrunc B (logHistoryFn F S ρ w B (some γ) distinctWeight n)
        let E := logEdge F S ρ w EdgeKind.full j G
        have hERespects : RespectsLoggedPerm E := hEdge j G (hTrunc _ (hHistory n))
        have hEBad : ∀ υ, ¬ (υ.2.map Prod.snd).Nodup → E υ = 0 := by
          intro υ hbad
          change logEdge F S ρ w EdgeKind.full j
            (logTrunc B (logHistoryFn F S ρ w B (some γ) distinctWeight n)) υ = 0
          rw [logEdge_history_eq_at_visit F S ρ w j B γ distinctWeight n hn' υ]
          exact hEdgeAtBad j
            (γ ⟨pathLength S.x - n, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
            G (hTruncBad _ (hHistoryBad n)) υ hbad
        have hGhostEq : logGhost F S ρ j (logTrunc B E) =
            subsetGhost F S ρ j (logTrunc B E) :=
          hGhost j _ (hTrunc E hERespects) (hTruncBad E hEBad)
        have hFixedEdge : E = edgeAtPosition F S ρ w j
            (γ ⟨pathLength S.x - n, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1 G := by
          funext υ
          exact logEdge_history_eq_at_visit F S ρ w j B γ distinctWeight n hn' υ
        have hInd : logHistoryFn F S ρ w B (some γ) distinctWeight n =
            finiteHistoryFn F S ρ w B γ n := funext (ih hn')
        have hG : G = logTrunc B (finiteHistoryFn F S ρ w B γ n) :=
          congrArg (logTrunc B) hInd
        simp only [logHistoryFn, finiteHistoryFn]
        rw [hGhostEq, hFixedEdge, hG]
  exact hAll k hk σ

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
