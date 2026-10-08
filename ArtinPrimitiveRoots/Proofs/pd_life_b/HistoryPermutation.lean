import ArtinPrimitiveRoots.Proofs.pd_life_b.EdgePermutation

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- Distinct-birth history continuations depend only on the permutation classes of memory
particles and logged prime values, including path restrictions and every memory cutoff. -/
theorem history_continuation_perm {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : Option (EnvPath S.x K)) (k : ℕ)
    (s t : MemPoint S.x K) (l m : BirthLog K)
    (hz : s.1 = t.1) (hp : s.2.1 = t.2.1)
    (hmem : ∀ i, List.Perm (s.2.2 i) (t.2.2 i))
    (hlog : List.Perm (l.map Prod.snd) (m.map Prod.snd)) :
    logHistoryFn F S ρ w B γ distinctWeight k (s, l) =
      logHistoryFn F S ρ w B γ distinctWeight k (t, m) := by
  classical
  have hSym (g : LogPoint S.x K → ℂ) (hg : RespectsLoggedPerm g) :
      RespectsLoggedPerm (logSym F S g) := by
    intro σ τ h
    unfold logSym
    congr 1
    apply Finset.sum_congr rfl
    intro π _
    apply hg
    exact ⟨h.1, congrArg (permuteLists π) h.2.1, h.2.2.1, h.2.2.2⟩
  have hTrunc (g : LogPoint S.x K → ℂ) (hg : RespectsLoggedPerm g) :
      RespectsLoggedPerm (logTrunc B g) := by
    intro σ τ h
    have hSize : memSize σ.1 = memSize τ.1 := by
      unfold memSize
      apply Finset.sum_congr rfl
      intro i _
      exact (h.2.2.1 i).length_eq
    cases B with
    | none => exact hg σ τ h
    | some b =>
        change (if memSize σ.1 ≤ b then g σ else 0) =
          (if memSize τ.1 ≤ b then g τ else 0)
        rw [hSize, hg σ τ h]
  have hPath (j : ℕ) (g : LogPoint S.x K → ℂ) (hg : RespectsLoggedPerm g) :
      RespectsLoggedPerm (logPathRestrict γ j g) := by
    intro σ τ h
    have hPoint : (σ.1.1, σ.1.2.1) = (τ.1.1, τ.1.2.1) := Prod.ext h.1 h.2.1
    cases γ with
    | none => exact hg σ τ h
    | some path =>
        unfold logPathRestrict
        dsimp only
        by_cases hj : j < pathLength S.x + 1
        · rw [dite_eq_left hj, dite_eq_left hj, hPoint, hg σ τ h]
        · simp only [dite_eq_right hj]
  have hBoundary :
      RespectsLoggedPerm (logBoundaryOut (x := S.x) (distinctWeight (K := K))) := by
    rintro ⟨s', L⟩ ⟨t', M⟩ ⟨hz', hp', hmem', hlog'⟩
    change s'.1 = t'.1 at hz'
    change ∀ i, (s'.2.2 i).Perm (t'.2.2 i) at hmem'
    change (L.map Prod.snd).Perm (M.map Prod.snd) at hlog'
    have hEmpty (i : Fin K) : s'.2.2 i = [] ↔ t'.2.2 i = [] := by
      simp only [← List.length_eq_zero_iff, (hmem' i).length_eq]
    have hEmptyAll : (∀ i, s'.2.2 i = []) ↔ ∀ i, t'.2.2 i = [] :=
      forall_congr' hEmpty
    have hb : memBoundary s' = memBoundary t' := by
      simp only [memBoundary, hz', hEmptyAll]
    have hd : distinctWeight L = distinctWeight M := by
      simp only [distinctWeight, hlog'.nodup_iff]
    change memBoundary s' * distinctWeight L = memBoundary t' * distinctWeight M
    rw [hb, hd]
  have hEdge (j : ℕ) (g : LogPoint S.x K → ℂ) (hg : RespectsLoggedPerm g) :
      RespectsLoggedPerm (logEdge F S ρ w EdgeKind.full j g) := by
    change RespectsLoggedPerm (logSym F S fun σL =>
      ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w j true St Pr (logSym F S g) σL -
          logEdgePiece F S ρ w j false St Pr (logSym F S g) σL))
    apply hSym
    intro σ τ h
    apply Finset.sum_congr rfl
    intro St _
    apply Finset.sum_congr rfl
    intro Pr _
    have hPiece (raw : Bool) :=
      logEdgePiece_respects_perm F S ρ w j raw St Pr (logSym F S g) (hSym g hg) σ τ h
    exact congrArg₂ (fun a b : ℂ => a - b) (hPiece true) (hPiece false)
  have hHistory : ∀ n, RespectsLoggedPerm (logHistoryFn F S ρ w B γ distinctWeight n) := by
    intro n
    induction n with
    | zero =>
        exact hTrunc _ (hPath (pathLength S.x) _
          (logGhost_respects_perm F S ρ (pathLength S.x) _ (hTrunc _ hBoundary)))
    | succ n ih =>
        let j := pathLength S.x - (n + 1)
        exact hTrunc _ (hPath j _
          (logGhost_respects_perm F S ρ j _ (hTrunc _ (hEdge j _ (hTrunc _ ih)))))
  exact hHistory k (s, l) (t, m) ⟨hz, hp, hmem, hlog⟩

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
