import ArtinPrimitiveRoots.Proofs.pd_life_b.FixedEdgePosition
import ArtinPrimitiveRoots.Proofs.pd_life_b.HistoryPaths

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- The complete signed edge with the target position fixed, retaining both symmetrizations. -/
def edgeAtPosition {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (z' : ℤ × ℤ)
    (f : LogPoint S.x K → ℂ) : LogPoint S.x K → ℂ :=
  let g := logSym F S f
  logSym F S fun σ =>
    ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      (edgePieceAtPosition F S ρ w step true St Pr z' g σ -
        edgePieceAtPosition F S ρ w step false St Pr z' g σ)

theorem logEdge_history_eq_at_visit {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (B : Option ℕ)
    (γ : EnvPath S.x K) (W : BirthLog K → ℂ)
    (k : ℕ) (hk : k ≤ pathLength S.x) (σ : LogPoint S.x K) :
    logEdge F S ρ w EdgeKind.full step
      (logTrunc B (logHistoryFn F S ρ w B (some γ) W k)) σ =
      edgeAtPosition F S ρ w step
        (γ ⟨pathLength S.x - k, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
        (logTrunc B (logHistoryFn F S ρ w B (some γ) W k)) σ := by
  classical
  let y : EnvPoint S.x K :=
    γ ⟨pathLength S.x - k, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hSupport (τ : LogPoint S.x K) (hne : τ.1.1 ≠ y.1) :
      logSym F S (logTrunc B (logHistoryFn F S ρ w B (some γ) W k)) τ = 0 := by
    unfold logSym
    suffices hsum : (∑ π : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        logTrunc B (logHistoryFn F S ρ w B (some γ) W k)
          ((τ.1.1, permuteLists π τ.1.2.1, τ.1.2.2), τ.2)) = 0 by
      rw [hsum, mul_zero]
    apply Finset.sum_eq_zero
    intro π _
    let υ : LogPoint S.x K :=
      ((τ.1.1, permuteLists π τ.1.2.1, τ.1.2.2), τ.2)
    have hOff : (υ.1.1, υ.1.2.1) ≠
        γ ⟨pathLength S.x - k, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      intro heq
      exact hne (congrArg Prod.fst heq)
    have hzero :=
      ArtinPrimitiveRoots.Proofs.pd_life_b.pd_life_b_logHistoryFn_zero_off_path_visit
        F S ρ w B γ W k hk υ hOff
    change logTrunc B (logHistoryFn F S ρ w B (some γ) W k) υ = 0
    cases B with
    | none => exact hzero
    | some b => simp only [logTrunc, hzero, ite_self]
  unfold logEdge edgeAtPosition
  dsimp only
  apply congrArg (fun g : LogPoint S.x K → ℂ => logSym F S g σ)
  funext τ
  apply Finset.sum_congr rfl
  intro St _
  apply Finset.sum_congr rfl
  intro Pr _
  rw [logEdgePiece_eq_at_position F S ρ w step true St Pr y.1 _ hSupport τ,
    logEdgePiece_eq_at_position F S ρ w step false St Pr y.1 _ hSupport τ]

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
