import ArtinPrimitiveRoots.TypeII.PD.Memory
import ArtinPrimitiveRoots.TypeII.Proofs.pd5.HistoryPartition
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.ConstraintWeight

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

/-- Every value in the log belongs to one of the marked prime bands. -/
def pd5b_logValuesMarked {K : ℕ} (F : PDFix K) (S : PDScale) (log : BirthLog K) : Prop :=
  ∀ e ∈ log, e.2 ∈ markedPrimes S.x K F.a

theorem pd5b_initialLog_values_marked {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s) :
    pd5b_logValuesMarked F S (initialLog s) := by
  classical
  intro e he
  unfold initialLog at he
  simp only [List.mem_flatMap, List.mem_map] at he
  rcases he with ⟨i, hi, j, hj, heq⟩
  cases heq
  apply Finset.mem_biUnion.mpr
  exact ⟨i, Finset.mem_univ i, hs.2.1 i j⟩

theorem pd5b_edgeBirths_values_marked {K : ℕ} (F : PDFix K) (S : PDScale)
    (step : ℕ) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :
    pd5b_logValuesMarked F S (edgeBirths F S step s c) := by
  classical
  intro e he
  have hp : e.2 ∈ (edgeBirths F S step s c).map Prod.snd :=
    List.mem_map.mpr ⟨e, he, rfl⟩
  unfold edgeBirths at hp
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    List.map_nil, List.map_cons, Prod.snd] at hp
  rcases List.mem_flatMap.mp hp with ⟨i, hi, hp⟩
  cases hc : (c i).2 with
  | inl k => simp [hc] at hp
  | inr q =>
      have hEq : e.2 = (q : ℕ) := by simpa [hc] using hp
      rw [hEq]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, q.property⟩

theorem pd5b_ghostBirthLog_values_marked {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℕ) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) :
    pd5b_logValuesMarked F S (pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))) := by
  classical
  intro e he
  unfold pd5_ghostBirthLog at he
  simp only [List.mem_flatMap, List.mem_ofFn] at he
  rcases he with ⟨i, hi, k, hk, rfl⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨i, Finset.mem_univ i, (new i k).property⟩

theorem pd5b_logValuesMarked_append {K : ℕ} (F : PDFix K) (S : PDScale)
    (L₁ L₂ : BirthLog K)
    (h₁ : pd5b_logValuesMarked F S L₁)
    (h₂ : pd5b_logValuesMarked F S L₂) :
    pd5b_logValuesMarked F S (L₁ ++ L₂) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact h₁ e he
  · exact h₂ e he

private theorem pd5b_logGhost_values_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (f₁ f₂ : LogPoint S.x K → ℂ)
    (hf : ∀ σL, pd5b_logValuesMarked F S σL.2 → f₁ σL = f₂ σL)
    (s : MemPoint S.x K) (L : BirthLog K) (hL : pd5b_logValuesMarked F S L) :
    logGhost F S ρ j f₁ (s, L) = logGhost F S ρ j f₂ (s, L) := by
  classical
  unfold logGhost
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro l
  apply Finset.sum_congr rfl
  intro new hnew
  by_cases hdelete : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1
  · simp only [if_pos hdelete]
    let t : MemPoint S.x K :=
      (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
        List.ofFn fun k => anchorAt (new i k) s.1)
    let G : BirthLog K := pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))
    have hG : pd5b_logValuesMarked F S G := by
      simpa [G] using pd5b_ghostBirthLog_values_marked F S j l new
    have hTG : pd5b_logValuesMarked F S (L ++ G) :=
      pd5b_logValuesMarked_append F S L G hL hG
    have hfun := hf (t, L ++ G) hTG
    have hfun' : f₁
        ((s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
          List.ofFn fun k => anchorAt (new i k) s.1),
          L ++ (List.finRange K).flatMap fun i =>
            List.ofFn fun k : Fin (l i) => (BirthAddress.ghost j i k.val, (new i k : ℕ))) =
      f₂
        ((s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
          List.ofFn fun k => anchorAt (new i k) s.1),
          L ++ (List.finRange K).flatMap fun i =>
            List.ofFn fun k : Fin (l i) => (BirthAddress.ghost j i k.val, (new i k : ℕ))) := by
      simpa only [t, G, pd5_ghostBirthLog] using hfun
    rw [hfun']
  · simp [hdelete]

private theorem pd5b_logEdgePiece_values_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (raw : Bool) (St Pr : Finset (Fin K))
    (f₁ f₂ : LogPoint S.x K → ℂ)
    (hf : ∀ σL, pd5b_logValuesMarked F S σL.2 → f₁ σL = f₂ σL)
    (σL : LogPoint S.x K) (hL : pd5b_logValuesMarked F S σL.2) :
    logEdgePiece F S ρ w step raw St Pr f₁ σL =
      logEdgePiece F S ρ w step raw St Pr f₂ σL := by
  classical
  unfold logEdgePiece
  apply Finset.sum_congr rfl
  intro c hc
  apply tsum_congr
  intro z'
  by_cases hcond : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
      EdgeAdmissible F S w σL.1 c z'
  · simp only [if_pos hcond]
    let t : MemPoint S.x K := (z', edgeTargetLists F S σL.1 c, edgeNewMemory F S σL.1 c)
    let G : BirthLog K := edgeBirths F S step σL.1 c
    have hG : pd5b_logValuesMarked F S G :=
      pd5b_edgeBirths_values_marked F S step σL.1 c
    have hTG : pd5b_logValuesMarked F S (σL.2 ++ G) :=
      pd5b_logValuesMarked_append F S σL.2 G hL hG
    have hfun := hf (t, σL.2 ++ G) hTG
    have hfun' : f₁ ((z', edgeTargetLists F S σL.1 c, edgeNewMemory F S σL.1 c),
        σL.2 ++ edgeBirths F S step σL.1 c) =
      f₂ ((z', edgeTargetLists F S σL.1 c, edgeNewMemory F S σL.1 c),
        σL.2 ++ edgeBirths F S step σL.1 c) := by
      simpa only [t, G] using hfun
    rw [hfun']
  · simp [hcond]

private theorem pd5b_logSym_values_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (f₁ f₂ : LogPoint S.x K → ℂ)
    (hf : ∀ σL, pd5b_logValuesMarked F S σL.2 → f₁ σL = f₂ σL)
    (σL : LogPoint S.x K) (hL : pd5b_logValuesMarked F S σL.2) :
    logSym F S f₁ σL = logSym F S f₂ σL := by
  classical
  unfold logSym
  apply congrArg (fun z : ℂ => ((permCount S.x K : ℂ)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro σ hσ
  exact hf ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2) hL

private theorem pd5b_logEdge_values_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ)
    (f₁ f₂ : LogPoint S.x K → ℂ)
    (hf : ∀ σL, pd5b_logValuesMarked F S σL.2 → f₁ σL = f₂ σL)
    (σL : LogPoint S.x K) (hL : pd5b_logValuesMarked F S σL.2) :
    logEdge F S ρ w EdgeKind.full step f₁ σL =
      logEdge F S ρ w EdgeKind.full step f₂ σL := by
  classical
  have hSym (τL : LogPoint S.x K) (hτ : pd5b_logValuesMarked F S τL.2) :
      logSym F S f₁ τL = logSym F S f₂ τL :=
    pd5b_logSym_values_congr F S f₁ f₂ hf τL hτ
  have hInner (τL : LogPoint S.x K) (hτ : pd5b_logValuesMarked F S τL.2) :
      (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S f₁) τL -
          logEdgePiece F S ρ w step false St Pr (logSym F S f₁) τL)) =
      (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S f₂) τL -
          logEdgePiece F S ρ w step false St Pr (logSym F S f₂) τL)) := by
    apply Finset.sum_congr rfl
    intro St hSt
    apply Finset.sum_congr rfl
    intro Pr hPr
    rw [pd5b_logEdgePiece_values_congr F S ρ w step true St Pr
      (logSym F S f₁) (logSym F S f₂) hSym τL hτ]
    rw [pd5b_logEdgePiece_values_congr F S ρ w step false St Pr
      (logSym F S f₁) (logSym F S f₂) hSym τL hτ]
  unfold logEdge
  apply pd5b_logSym_values_congr F S _ _ hInner σL hL

private theorem pd5b_logHistoryFn_values_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : ℕ) (W₁ W₂ : BirthLog K → ℂ)
    (hW : ∀ log, pd5b_logValuesMarked F S log → W₁ log = W₂ log) :
    ∀ k, k ≤ pathLength S.x → ∀ s : MemPoint S.x K, ∀ L : BirthLog K,
      pd5b_logValuesMarked F S L →
      logHistoryFn F S ρ w (some B) none W₁ k (s, L) =
        logHistoryFn F S ρ w (some B) none W₂ k (s, L) := by
  classical
  intro k
  induction k with
  | zero =>
      intro hk s L hL
      simp only [logHistoryFn, logPathRestrict]
      change logTrunc (some B)
          (logGhost F S ρ (pathLength S.x)
            (logTrunc (some B) (logBoundaryOut W₁))) (s, L) =
        logTrunc (some B)
          (logGhost F S ρ (pathLength S.x)
            (logTrunc (some B) (logBoundaryOut W₂))) (s, L)
      by_cases hsrc : memSize s ≤ B
      · simp only [logTrunc, hsrc, if_pos]
        apply pd5b_logGhost_values_congr F S ρ (pathLength S.x)
          (logTrunc (some B) (logBoundaryOut W₁))
          (logTrunc (some B) (logBoundaryOut W₂))
        · intro τL hτ
          by_cases hsize : memSize τL.1 ≤ B
          · simp [logTrunc, hsize, logBoundaryOut, hW τL.2 hτ]
          · simp [logTrunc, hsize]
        · exact hL
      · simp [logTrunc, hsrc]
  | succ k ih =>
      intro hk s L hL
      let n : ℕ := pathLength S.x - (k + 1)
      have hkn : k ≤ pathLength S.x := Nat.le_trans (Nat.le_succ _) hk
      have hnstep : n < pathLength S.x := by
        dsimp [n]
        omega
      simp only [logHistoryFn, logPathRestrict]
      change logTrunc (some B)
          (logGhost F S ρ n
            (logTrunc (some B)
              (logEdge F S ρ w EdgeKind.full n
                (logTrunc (some B)
                  (logHistoryFn F S ρ w (some B) none W₁ k))))) (s, L) =
        logTrunc (some B)
          (logGhost F S ρ n
            (logTrunc (some B)
              (logEdge F S ρ w EdgeKind.full n
                (logTrunc (some B)
                  (logHistoryFn F S ρ w (some B) none W₂ k))))) (s, L)
      by_cases hsrc : memSize s ≤ B
      · simp only [logTrunc, hsrc, if_pos]
        let cont₁ : LogPoint S.x K → ℂ := fun τL =>
          logTrunc (some B)
            (logEdge F S ρ w EdgeKind.full n
              (logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none W₁ k))) τL
        let cont₂ : LogPoint S.x K → ℂ := fun τL =>
          logTrunc (some B)
            (logEdge F S ρ w EdgeKind.full n
              (logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none W₂ k))) τL
        have hcont : ∀ τL, pd5b_logValuesMarked F S τL.2 → cont₁ τL = cont₂ τL := by
          intro τL hτ
          by_cases hsize : memSize τL.1 ≤ B
          · simp [cont₁, cont₂, logTrunc, hsize]
            exact pd5b_logEdge_values_congr F S ρ w n
              (logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none W₁ k))
              (logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none W₂ k))
              (by
                intro ξL hξ
                by_cases hξsize : memSize ξL.1 ≤ B
                · have hrec := ih hkn ξL.1 ξL.2 hξ
                  simp [logTrunc, hξsize, hrec]
                · simp [logTrunc, hξsize]) τL hτ
          · simp [cont₁, cont₂, logTrunc, hsize]
        change logGhost F S ρ n cont₁ (s, L) = logGhost F S ρ n cont₂ (s, L)
        exact pd5b_logGhost_values_congr F S ρ n cont₁ cont₂ hcont s L hL
      · simp [logTrunc, hsrc]

theorem pd5b_memHistory_values_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : ℕ) (W₁ W₂ : BirthLog K → ℂ)
    (hW : ∀ log, pd5b_logValuesMarked F S log → W₁ log = W₂ log) :
    memHistory F S ρ w (some B) none W₁ =
      memHistory F S ρ w (some B) none W₂ := by
  classical
  unfold memHistory logInner
  apply tsum_congr
  intro σL
  by_cases hlog : σL.2 = initialLog σL.1
  · rcases σL with ⟨s, L⟩
    change L = initialLog s at hlog
    subst L
    by_cases hμ : memMeasure F S s = 0
    · simp [hμ]
    · have hsValid : MemValid F S s := by
        by_contra h
        simp [memMeasure, h] at hμ
      have hvalues : pd5b_logValuesMarked F S (initialLog s) :=
        pd5b_initialLog_values_marked F S s hsValid
      have hHist := pd5b_logHistoryFn_values_congr F S ρ w B W₁ W₂ hW
        (pathLength S.x) le_rfl s (initialLog s) hvalues
      simp [logBoundaryIn, hHist]
  · simp [logBoundaryIn, hlog]

theorem pd5b_memHistory_prefix_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : ℕ) (W₁ W₂ : BirthLog K → ℂ)
    (hW : ∀ log, (log.map Prod.fst).Nodup →
      (∀ e ∈ log, e.1 ∈ birthAddresses S.x K B) → W₁ log = W₂ log) :
    memHistory F S ρ w (some B) none W₁ =
      memHistory F S ρ w (some B) none W₂ := by
  classical
  unfold memHistory logInner
  apply tsum_congr
  intro σL
  by_cases hlog : σL.2 = initialLog σL.1
  · rcases σL with ⟨s, L⟩
    change L = initialLog s at hlog
    subst L
    have hInit := pd5_initialLog_prefixGood (B := B) s
    have hHist := pd5_logHistoryFn_prefix_congr F S ρ w B W₁ W₂ hW
      (pathLength S.x) le_rfl s (initialLog s) (by simpa using hInit)
    simp [logBoundaryIn, hHist]
  · simp [logBoundaryIn, hlog]

/-- Exact finite Fourier expansion of one constraint-weighted truncated history. -/
theorem pd5b_memHistory_constraint_fourier {K T : ℕ} [NeZero T]
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (B : ℕ)
    (A : Finset (BirthAddress K)) (C : Finset (Finset (BirthAddress K)))
    (hC : IsConstraintSystem A C)
    (hA : birthAddresses S.x K B ⊆ A)
    (hT : ∀ p ∈ markedPrimes S.x K F.a, p < T)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    memHistory F S ρ w (some B) none (constraintWeight C) =
      ((Fintype.card
        ({p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T) : ℂ)⁻¹) *
        ∑ θ : {p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T,
          memHistory F S ρ w (some B) none (pd5b_systemPairPhase A C hC · θ) := by
  classical
  let Pair := {p : A × A // p ∈ pd5_systemPairs A C hC}
  letI : DecidableEq Pair := Subtype.instDecidableEq
  let phase : (Pair → ZMod T) → BirthLog K → ℂ := fun θ log =>
    pd5b_systemPairPhase A C hC log θ
  let coeff : ℂ := (Fintype.card (Pair → ZMod T) : ℂ)⁻¹
  let avg : BirthLog K → ℂ := fun log => coeff * ∑ θ : Pair → ZMod T, phase θ log
  let mid : BirthLog K → ℂ := fun log =>
    if pd5b_logValuesMarked F S log then avg log else constraintWeight C log
  have hWprefix : ∀ log, (log.map Prod.fst).Nodup →
      (∀ e ∈ log, e.1 ∈ birthAddresses S.x K B) →
      constraintWeight C log = mid log := by
    intro log hnodup haddr
    by_cases hvalues : pd5b_logValuesMarked F S log
    · have hbound : ∀ a ∈ A, ∀ p, pd5b_label log a = some p → p < T := by
        intro a ha p hp
        have hmem : (a, p) ∈ log := (pd5b_label_spec hnodup a p).1 hp
        exact hT p (hvalues (a, p) hmem)
      have hfourier := pd5b_constraintWeight_fourier A C hC log hnodup hbound
      have havg : constraintWeight C log = avg log := by
        simpa [avg, coeff, phase, Pair] using hfourier
      simp [mid, hvalues, havg]
    · simp [mid, hvalues]
  have hWvalues : ∀ log, pd5b_logValuesMarked F S log → mid log = avg log := by
    intro log hvalues
    simp [mid, hvalues]
  have hprefix := pd5b_memHistory_prefix_congr F S ρ w B
    (constraintWeight C) mid hWprefix
  have hvalues := pd5b_memHistory_values_congr F S ρ w B mid avg hWvalues
  have hlin := pd5_memHistory_finsetSum F S ρ w B Finset.univ
    (fun _ : Pair → ZMod T => coeff) phase hbox
  have havgTerms : avg = fun log =>
      ∑ θ : Pair → ZMod T, coeff * phase θ log := by
    funext log
    simp [avg, coeff, Finset.mul_sum]
  have hcombine :
      (∑ θ : Pair → ZMod T, coeff * memHistory F S ρ w (some B) none (phase θ)) =
        coeff * ∑ θ : Pair → ZMod T,
          memHistory F S ρ w (some B) none (phase θ) := by
    rw [← Finset.mul_sum]
  calc
    _ = memHistory F S ρ w (some B) none mid := hprefix
    _ = memHistory F S ρ w (some B) none avg := hvalues
    _ = ∑ θ : Pair → ZMod T,
          coeff * memHistory F S ρ w (some B) none (phase θ) := by
          rw [havgTerms]
          exact hlin
    _ = _ := hcombine

end

end ArtinPrimitiveRoots.TypeII.PD
