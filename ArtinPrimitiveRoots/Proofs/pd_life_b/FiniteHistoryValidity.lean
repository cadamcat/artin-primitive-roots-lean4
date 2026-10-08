import ArtinPrimitiveRoots.Proofs.pd_life_b.FiniteHistoryCutoff

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- The literal visit, ghost, edge, and terminal distinct-boundary tests of a trace. -/
def FiniteHistoryTraceValid {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (γ : EnvPath S.x K) :
    (k : ℕ) → (σ : LogPoint S.x K) → FiniteHistoryTrace F S γ k σ → Prop
  | 0, σ, t =>
      let τ := ghostTraceOutput F S (pathLength S.x) σ t
      (σ.1.1, σ.1.2.1) = γ (Fin.last (pathLength S.x)) ∧
        (∀ i, t.1 i ⊆ hitIndices (σ.1.2.2 i) σ.1.1) ∧
        (τ.1.1 = (1, 0) ∧ ∀ i, τ.1.2.2 i = []) ∧
        (τ.2.map Prod.snd).Nodup
  | k + 1, σ, t =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      (σ.1.1, σ.1.2.1) =
          γ ⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ ∧
        (∀ i, t.1.1 i ⊆ hitIndices (σ.1.2.2 i) σ.1.1) ∧
        EdgeAdmissible F S w (permuteLogPoint t.2.1.1 τ).1 t.2.1.2.1 z' ∧
        FiniteHistoryTraceValid F S w γ k υ t.2.2

/-- Failure of any structural history test makes the trace weight zero. -/
theorem finiteHistoryTraceWeight_zero_of_not_valid {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (k : ℕ) (σ : LogPoint S.x K)
    (t : FiniteHistoryTrace F S γ k σ)
    (ht : ¬ FiniteHistoryTraceValid F S w γ k σ t) :
    finiteHistoryTraceWeight F S ρ w B γ k σ t = 0 := by
  classical
  have hVisitZero (j : ℕ) (hj : j < pathLength S.x + 1)
      (τ : LogPoint S.x K)
      (h : (τ.1.1, τ.1.2.1) ≠ γ ⟨j, hj⟩) :
      historyVisitFactor γ j τ = 0 := by
    unfold historyVisitFactor
    rw [dite_eq_left hj, ite_eq_right h]
  have hGhostZero (j : ℕ) (τ : LogPoint S.x K)
      (g : GhostTraceChoice F S τ)
      (h : ¬ ∀ i, g.1 i ⊆ hitIndices (τ.1.2.2 i) τ.1.1) :
      ghostTraceCharge F S ρ j τ g = 0 := by
    unfold ghostTraceCharge
    exact ite_eq_right h
  have hEdgeZero (j : ℕ) (z' : ℤ × ℤ) (τ : LogPoint S.x K)
      (e : EdgeTraceChoice F S τ)
      (h : ¬ EdgeAdmissible F S w (permuteLogPoint e.1 τ).1 e.2.1 z') :
      edgeTraceCharge F S ρ w j z' τ e = 0 := by
    unfold edgeTraceCharge
    dsimp only [permuteLogPoint] at h ⊢
    rw [ite_eq_right h, mul_zero]
  have hBoundaryZero (τ : LogPoint S.x K)
      (h : ¬ ((τ.1.1 = (1, 0) ∧ ∀ i, τ.1.2.2 i = []) ∧
        (τ.2.map Prod.snd).Nodup)) :
      logBoundaryOut distinctWeight τ = 0 := by
    unfold logBoundaryOut memBoundary distinctWeight
    by_cases hb : τ.1.1 = (1, 0) ∧ ∀ i, τ.1.2.2 i = []
    · have hl : ¬ (τ.2.map Prod.snd).Nodup := fun hl => h ⟨hb, hl⟩
      rw [ite_eq_left hb, ite_eq_right hl, mul_zero]
    · rw [ite_eq_right hb, zero_mul]
  induction k generalizing σ with
  | zero =>
      let τ := ghostTraceOutput F S (pathLength S.x) σ t
      by_cases hv : (σ.1.1, σ.1.2.1) = γ (Fin.last (pathLength S.x))
      · by_cases hg : ∀ i, t.1 i ⊆ hitIndices (σ.1.2.2 i) σ.1.1
        · have hb : ¬ ((τ.1.1 = (1, 0) ∧ ∀ i, τ.1.2.2 i = []) ∧
              (τ.2.map Prod.snd).Nodup) := by
            intro hb
            exact ht ⟨hv, hg, hb.1, hb.2⟩
          have hz := hBoundaryZero τ hb
          dsimp only [τ] at hz
          simp only [finiteHistoryTraceWeight, hz, mul_zero]
        · have hz := hGhostZero (pathLength S.x) σ t hg
          simp only [finiteHistoryTraceWeight, hz, mul_zero, zero_mul]
      · have hz := hVisitZero (pathLength S.x)
          (Nat.lt_succ_self _) σ hv
        simp only [finiteHistoryTraceWeight, hz, mul_zero, zero_mul]
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      have hj : j < pathLength S.x + 1 :=
        Nat.lt_succ_of_le (Nat.sub_le _ _)
      by_cases hv : (σ.1.1, σ.1.2.1) = γ ⟨j, hj⟩
      · by_cases hg : ∀ i, t.1.1 i ⊆ hitIndices (σ.1.2.2 i) σ.1.1
        · by_cases he :
              EdgeAdmissible F S w (permuteLogPoint t.2.1.1 τ).1 t.2.1.2.1 z'
          · have htail : ¬ FiniteHistoryTraceValid F S w γ k υ t.2.2 := by
              intro htail
              exact ht ⟨hv, hg, he, htail⟩
            have hz := ih υ t.2.2 htail
            dsimp only [υ, τ, j, z'] at hz
            simp only [finiteHistoryTraceWeight, hz, mul_zero]
          · have hz := hEdgeZero j z' τ t.2.1 he
            dsimp only [τ, j, z'] at hz
            simp only [finiteHistoryTraceWeight, hz, zero_mul, mul_zero]
        · have hz := hGhostZero j σ t.1 hg
          dsimp only [j] at hz
          simp only [finiteHistoryTraceWeight, hz, zero_mul, mul_zero]
      · have hz := hVisitZero j hj σ hv
        dsimp only [j] at hz
        simp only [finiteHistoryTraceWeight, hz, zero_mul, mul_zero]

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
