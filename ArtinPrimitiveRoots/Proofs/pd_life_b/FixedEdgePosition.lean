import ArtinPrimitiveRoots.Proofs.pd_life_b.GhostMemoryPrime

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- A literal edge piece evaluated at its single possible target position. -/
def edgePieceAtPosition {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (raw : Bool)
    (St Pr : Finset (Fin K)) (z' : ℤ × ℤ)
    (f : LogPoint S.x K → ℂ) : LogPoint S.x K → ℂ :=
  fun σ =>
    let s := σ.1
    ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
          EdgeAdmissible F S w s c z' then
        let mem' := edgeNewMemory F S s c
        ((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
            (∏ i : Fin K,
              match (c i).2 with
              | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
              | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
            ρ ^ (∑ i : Fin K, hitCount (mem' i) z') : ℝ) : ℂ) *
          edgeMultiplier F S (decide (step % 2 = 0)) raw s.2.1
            (edgeTargetLists F S s c) s.1 z' *
          f (edgeOutputPoint F S step σ c z')
      else 0

theorem logEdgePiece_eq_at_position {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (raw : Bool)
    (St Pr : Finset (Fin K)) (z' : ℤ × ℤ)
    (f : LogPoint S.x K → ℂ)
    (hf : ∀ τ : LogPoint S.x K, τ.1.1 ≠ z' → f τ = 0)
    (σ : LogPoint S.x K) :
    logEdgePiece F S ρ w step raw St Pr f σ =
      edgePieceAtPosition F S ρ w step raw St Pr z' f σ := by
  classical
  unfold logEdgePiece edgePieceAtPosition edgeOutputPoint
  dsimp only
  apply Finset.sum_congr rfl
  intro c _
  apply tsum_eq_single z'
  intro z'' hne
  by_cases hGuard : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
      EdgeAdmissible F S w σ.1 c z''
  · rw [ite_eq_left hGuard]
    have hzero : f ((z'', edgeTargetLists F S σ.1 c, edgeNewMemory F S σ.1 c),
        σ.2 ++ edgeBirths F S step σ.1 c) = 0 := hf _ hne
    rw [hzero, mul_zero]
  · exact ite_eq_right hGuard

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
