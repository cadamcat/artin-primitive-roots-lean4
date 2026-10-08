import ArtinPrimitiveRoots.Proofs.pd_life_b.FiniteHistory

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- The fixed-position edge as one sum over choices, with its signed geometric multiplier. -/
def edgeChoiceAtPosition {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (z' : ℤ × ℤ)
    (f : LogPoint S.x K → ℂ) : LogPoint S.x K → ℂ :=
  let g := logSym F S f
  logSym F S fun σ =>
    let s := σ.1
    ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      if EdgeAdmissible F S w s c z' then
        let mem' := edgeNewMemory F S s c
        ((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
            (∏ i : Fin K,
              match (c i).2 with
              | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
              | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
            ρ ^ (∑ i : Fin K, hitCount (mem' i) z') : ℝ) : ℂ) *
          (edgeMultiplier F S (decide (step % 2 = 0)) true s.2.1
              (edgeTargetLists F S s c) s.1 z' -
            edgeMultiplier F S (decide (step % 2 = 0)) false s.2.1
              (edgeTargetLists F S s c) s.1 z') *
          g (edgeOutputPoint F S step σ c z')
      else 0

/-- Each edge choice selects exactly one stored/promoted mask pair. -/
theorem edgeAtPosition_eq_choice_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (z' : ℤ × ℤ)
    (f : LogPoint S.x K → ℂ) (σ : LogPoint S.x K) :
    edgeAtPosition F S ρ w step z' f σ =
      edgeChoiceAtPosition F S ρ w step z' f σ := by
  classical
  unfold edgeAtPosition edgeChoiceAtPosition
  dsimp only
  apply congrArg (fun g : LogPoint S.x K → ℂ => logSym F S g σ)
  funext τ
  unfold edgePieceAtPosition
  dsimp only
  simp only [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, Pr]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single (edgeStoredSet c)]
  · rw [Finset.sum_eq_single (edgePromotedSet c)]
    · by_cases hAdm : EdgeAdmissible F S w τ.1 c z' <;>
        simp only [eq_self, true_and, hAdm, ite_true, ite_false,
          sub_self, mul_sub, sub_mul]
      rfl
    · intro Pr _ hne
      have hPr : edgePromotedSet c ≠ Pr := Ne.symm hne
      simp only [hPr, and_false, false_and, ite_false, sub_self]
    · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  · intro St _ hne
    have hSt : edgeStoredSet c ≠ St := Ne.symm hne
    apply Finset.sum_eq_zero
    intro Pr _
    simp only [hSt, false_and, ite_false, sub_self]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
