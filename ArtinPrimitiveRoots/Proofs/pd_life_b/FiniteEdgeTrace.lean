import ArtinPrimitiveRoots.Proofs.pd_life_b.FiniteEdgeChoices

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- Apply a slot permutation, keeping position, memory, and birth log fixed. -/
def permuteLogPoint {x : ℝ} {K : ℕ}
    (π : Fin K → Equiv.Perm (Fin (slotCount x))) (σ : LogPoint x K) :
    LogPoint x K :=
  ((σ.1.1, permuteLists π σ.1.2.1, σ.1.2.2), σ.2)

/-- The source permutation, edge choice vector, and target permutation. -/
abbrev EdgeTraceChoice {K : ℕ} (F : PDFix K) (S : PDScale)
    (σ : LogPoint S.x K) :=
  (Fin K → Equiv.Perm (Fin (slotCount S.x))) ×
    ((i : Fin K) → EdgeChoice S.x F.a (σ.1.2.2 i) i) ×
    (Fin K → Equiv.Perm (Fin (slotCount S.x)))

/-- The logged state reached by a finite edge trace. -/
def edgeTraceOutput {K : ℕ} (F : PDFix K) (S : PDScale)
    (step : ℕ) (z' : ℤ × ℤ) (σ : LogPoint S.x K)
    (t : EdgeTraceChoice F S σ) : LogPoint S.x K :=
  permuteLogPoint t.2.2
    (edgeOutputPoint F S step (permuteLogPoint t.1 σ) t.2.1 z')

/-- The literal signed edge charge, including both slot-symmetrization factors. -/
def edgeTraceCharge {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (z' : ℤ × ℤ)
    (σ : LogPoint S.x K) (t : EdgeTraceChoice F S σ) : ℂ :=
  let τ := permuteLogPoint t.1 σ
  let s := τ.1
  let c := t.2.1
  ((permCount S.x K : ℂ)⁻¹) ^ 2 *
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
            (edgeTargetLists F S s c) s.1 z')
    else 0

/-- Expand both slot symmetrizations into a single finite sum of edge traces. -/
theorem edgeChoiceAtPosition_eq_trace_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (z' : ℤ × ℤ)
    (f : LogPoint S.x K → ℂ) (σ : LogPoint S.x K) :
    edgeChoiceAtPosition F S ρ w step z' f σ =
      ∑ t : EdgeTraceChoice F S σ,
        edgeTraceCharge F S ρ w step z' σ t *
          f (edgeTraceOutput F S step z' σ t) := by
  classical
  unfold edgeChoiceAtPosition
  unfold logSym
  dsimp only
  simp only [Fintype.sum_prod_type]
  unfold edgeTraceCharge edgeTraceOutput permuteLogPoint
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hAdm : EdgeAdmissible F S w
      (permuteLogPoint π σ).1 c z'
  · simp only [permuteLogPoint] at hAdm
    simp only [hAdm, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro κ _
    rw [pow_two]
    ac_nf
    rfl'
  · simp only [permuteLogPoint] at hAdm
    simp only [hAdm, ite_false, mul_zero, zero_mul, Finset.sum_const_zero]

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
