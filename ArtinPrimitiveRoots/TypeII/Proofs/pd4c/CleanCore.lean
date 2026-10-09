import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CleanChoices
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.GroupTransfer

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- The unsymmetrized clean core draws only fresh tuples and preserves its memory. -/
theorem clean_core_fresh_formula {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) (raw : Bool)
    (f : MemPoint S.x K → ℂ) (s : MemPoint S.x K) :
    let χ : ((i : Fin K) → primeBand S.x (F.a i)) →
        ((i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :=
      fun p i => (false, Sum.inr (p i))
    plainOp (logEdgePiece F S ρ w j raw ∅ ∅) f s =
      ∑ p : (i : Fin K) → primeBand S.x (F.a i), ∑' z' : ℤ × ℤ,
        if EdgeAdmissible F S w s (χ p) z' then
          ((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
            (∏ i : Fin K, memoryNu S.x K F.a F.q_d i (p i)) *
            ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) z') : ℝ) : ℂ) *
          edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1
            (edgeTargetLists F S s (χ p)) s.1 z' *
          f (z', edgeTargetLists F S s (χ p), s.2.2)
        else 0 := by
  let χ : ((i : Fin K) → primeBand S.x (F.a i)) →
      ((i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :=
    fun p i => (false, Sum.inr (p i))
  let Φ := fun (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) =>
    ∑' z' : ℤ × ℤ, if EdgeAdmissible F S w s c z' then
      ((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
        (∏ i : Fin K, match (c i).2 with
          | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
          | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
        ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s c i) z') : ℝ) : ℂ) *
      edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1
        (edgeTargetLists F S s c) s.1 z' *
      f (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
    else 0
  have hcore : plainOp (logEdgePiece F S ρ w j raw ∅ ∅) f s =
      ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
        if edgeStoredSet (s := s) c = ∅ ∧ edgePromotedSet (s := s) c = ∅ then Φ c else 0 := by
    dsimp only [plainOp, logEdgePiece]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hpat : edgeStoredSet (s := s) c = ∅ ∧ edgePromotedSet (s := s) c = ∅
    · simp only [Φ, ← and_assoc, hpat, true_and, ite_true] <;> rfl
    · simp only [← and_assoc, hpat, false_and, if_false, tsum_zero]
  rw [hcore, clean_choice_sum_reindex]
  apply Finset.sum_congr rfl
  intro p hp
  have hmem : edgeNewMemory F S s (χ p) = s.2.2 := by
    funext i
    simp [edgeNewMemory, χ, pd4c_remove_empty]
  change Φ (χ p) = _
  dsimp only [Φ]
  rw [hmem]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
