import ArtinPrimitiveRoots.Proofs.pd_life_b.FiniteEdgeTrace

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- The deletion vector and the subset of ghost births in each group. -/
abbrev GhostTraceChoice {K : ℕ} (F : PDFix K) (S : PDScale)
    (σ : LogPoint S.x K) :=
  ((i : Fin K) → Finset (Fin (σ.1.2.2 i).length)) ×
    ((i : Fin K) → (primeBand S.x (F.a i)).powerset)

/-- The logged state reached by a finite ghost trace. -/
def ghostTraceOutput {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℕ) (σ : LogPoint S.x K) (t : GhostTraceChoice F S σ) :
    LogPoint S.x K :=
  subsetGhostPoint F S j σ t.1 t.2

/-- The literal ghost charge, including its hitting guard. -/
def ghostTraceCharge {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (σ : LogPoint S.x K)
    (t : GhostTraceChoice F S σ) : ℂ :=
  if ∀ i, t.1 i ⊆ hitIndices (σ.1.2.2 i) σ.1.1 then
    ((∏ i : Fin K,
        (-memoryEta S.x F.q_d j / ρ) ^ (t.1 i).card *
        (memoryQ S.x F.q_d j / ρ ^ 2) ^
          (hitCount (σ.1.2.2 i) σ.1.1 - (t.1 i).card) *
        (-memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ) ^ (t.2 i).1.card *
        (∏ p ∈ (t.2 i).1, memoryNu S.x K F.a F.q_d i p) : ℝ) : ℂ)
  else 0

/-- Package the subset-ghost expansion as one finite trace sum. -/
theorem subsetGhost_eq_trace_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (f : LogPoint S.x K → ℂ) (σ : LogPoint S.x K) :
    subsetGhost F S ρ j f σ =
      ∑ t : GhostTraceChoice F S σ,
        ghostTraceCharge F S ρ j σ t * f (ghostTraceOutput F S j σ t) := by
  classical
  unfold subsetGhost
  simp only [Fintype.sum_prod_type]
  unfold ghostTraceCharge ghostTraceOutput
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro T _
  by_cases h : ∀ i, D i ⊆ hitIndices (σ.1.2.2 i) σ.1.1
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, zero_mul]

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
