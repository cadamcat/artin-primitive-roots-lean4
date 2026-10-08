import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedEdgeStep
import ArtinPrimitiveRoots.Proofs.pd_life_b.AllTraceLog

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- The cutoff indicator of a memory size. -/
def cutF (B : Option ℕ) (n : ℕ) : ℂ :=
  match B with
  | none => 1
  | some b => if n ≤ b then 1 else 0

theorem cutF_idem (B : Option ℕ) (n : ℕ) : cutF B n * cutF B n = cutF B n := by
  cases B with
  | none => simp [cutF]
  | some b =>
    show (if n ≤ b then (1 : ℂ) else 0) * (if n ≤ b then 1 else 0) = if n ≤ b then 1 else 0
    split_ifs <;> simp

theorem historyCutoffFactor_eq {x : ℝ} {K : ℕ} (B : Option ℕ) (σ : LogPoint x K) :
    historyCutoffFactor B σ = cutF B (memSize σ.1) := by
  cases B <;> rfl

/-- Length of a life-state memory list. -/
theorem length_life {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (i : Fin K) (b : Bool) (jP : Fin (pathLength S.x + 1))
    (l : List Particle) (hnd : (l.map Prod.fst).Nodup)
    (hmem : ∀ q : Particle, q ∈ l ↔ ∃ hp : q.1 ∈ primeBand S.x (F.a i),
      pdLifePending S γ q.1 (H i ⟨q.1, hp⟩) b jP ∧
        q.2 = (lifeLine S γ q.1 (H i ⟨q.1, hp⟩).1).val) :
    l.length = (Finset.univ.filter fun p : primeBand S.x (F.a i) =>
        pdLifePending S γ p.1 (H i p) b jP).card := by
  have h : (Finset.univ.filter fun _ : Fin l.length => True).card =
      (Finset.univ.filter fun p : primeBand S.x (F.a i) =>
        pdLifePending S γ p.1 (H i p) b jP).card :=
    card_filter_get_eq (s := primeBand S.x (F.a i)) l hnd (fun _ => True)
    (fun p : primeBand S.x (F.a i) => pdLifePending S γ p.1 (H i p) b jP)
    (dR := _) (dC := _) ?_ ?_
  · simpa using h
  · intro r _
    obtain ⟨hp, hpend, -⟩ := (hmem _).mp (List.get_mem _ r)
    exact ⟨hp, hpend⟩
  · intro p hp
    have hin : ((p.1, (lifeLine S γ p.1 (H i p).1).val) : Particle) ∈ l :=
      (hmem _).mpr ⟨p.2, hp, rfl⟩
    obtain ⟨r, hr⟩ := List.mem_iff_get.mp hin
    exact ⟨r, by rw [hr], trivial⟩

theorem memSize_life {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x + 1)) (σ : LogPoint S.x K)
    (hσ : IsLifeState F S γ H j σ) :
    memSize σ.1 = pdLifeMemorySize F S γ H false j := by
  unfold memSize pdLifeMemorySize
  apply Finset.sum_congr rfl
  intro i _
  rw [length_life F S γ H i false j _ (hσ.2.1 i) (hσ.2.2.1 i), Finset.card_filter]

theorem memSize_life_after {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x + 1)) (τ : LogPoint S.x K)
    (hτ : IsLifeStateAfter F S γ H j τ) :
    memSize τ.1 = pdLifeMemorySize F S γ H true j := by
  unfold memSize pdLifeMemorySize
  apply Finset.sum_congr rfl
  intro i _
  rw [length_life F S γ H i true j _ (hτ.2.1 i) (hτ.2.2.1 i), Finset.card_filter]

/-- Every trace weight starts with the source cutoff and the visit test. -/
theorem weight_head {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (k : ℕ) (σ : LogPoint S.x K)
    (t : FiniteHistoryTrace F S γ k σ) :
    ∃ r : ℂ, finiteHistoryTraceWeight F S ρ w B γ k σ t =
      historyCutoffFactor B σ * (historyVisitFactor γ (pathLength S.x - k) σ * r) := by
  cases k with
  | zero =>
    refine ⟨ghostTraceCharge F S ρ (pathLength S.x) σ t *
      (historyCutoffFactor B (ghostTraceOutput F S (pathLength S.x) σ t) *
        logBoundaryOut distinctWeight (ghostTraceOutput F S (pathLength S.x) σ t)), ?_⟩
    rw [Nat.sub_zero]
    rfl
  | succ k => exact ⟨_, rfl⟩

/-- A non-vanishing guided sum forces the visit at its first state. -/
theorem guidedTraceSum_visit {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (H : PDLifeAssignment F S γ) (k : ℕ)
    (hk : k ≤ pathLength S.x) (σ : LogPoint S.x K)
    (h : guidedTraceSum F S ρ w B γ H k σ ≠ 0) :
    (σ.1.1, σ.1.2.1) = γ ⟨pathLength S.x - k, by omega⟩ := by
  by_contra hv
  apply h
  apply Finset.sum_eq_zero
  intro t _
  split_ifs
  · obtain ⟨r, hr⟩ := weight_head F S ρ w B γ k σ t
    rw [hr]
    unfold historyVisitFactor
    rw [dif_pos (by omega), if_neg hv]
    ring
  · rfl

/-- A non-vanishing guided sum forces a repetition-free source log. -/
theorem guidedTraceSum_nodup {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (H : PDLifeAssignment F S γ) (k : ℕ)
    (σ : LogPoint S.x K)
    (h : guidedTraceSum F S ρ w B γ H k σ ≠ 0) :
    (σ.2.map Prod.snd).Nodup := by
  by_contra hn
  apply h
  apply Finset.sum_eq_zero
  intro t _
  split_ifs
  · apply finiteHistoryTraceWeight_zero_of_not_valid
    intro hv
    have hall := finiteHistoryTrace_all_log_nodup F S w γ k σ t hv
    apply hn
    cases k with
    | zero => exact hall.1
    | succ k => exact hall.1
  · rfl

/-- One step of the guided sum: the ghost is forced, the edge sum remains. -/
theorem guidedTraceSum_succ {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (H : PDLifeAssignment F S γ) (k : ℕ)
    (hk : k + 1 ≤ pathLength S.x) (σ : LogPoint S.x K) :
    guidedTraceSum F S ρ w B γ H (k + 1) σ =
      historyCutoffFactor B σ *
        (historyVisitFactor γ (pathLength S.x - (k + 1)) σ *
          (ghostTraceCharge F S ρ (pathLength S.x - (k + 1)) σ
              (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ) *
            (historyCutoffFactor B (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ
                (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ)) *
              ∑ e : EdgeTraceChoice F S (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ
                  (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ)),
                if EdgeGuided F S γ H ⟨pathLength S.x - (k + 1), by omega⟩
                    (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ
                      (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ)) e then
                  edgeTraceCharge F S ρ w (pathLength S.x - (k + 1))
                      (γ ⟨pathLength S.x - k, by omega⟩).1
                      (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ
                        (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ)) e *
                    (historyCutoffFactor B (edgeTraceOutput F S (pathLength S.x - (k + 1))
                        (γ ⟨pathLength S.x - k, by omega⟩).1
                        (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ
                          (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ)) e) *
                      guidedTraceSum F S ρ w B γ H k (edgeTraceOutput F S (pathLength S.x - (k + 1))
                        (γ ⟨pathLength S.x - k, by omega⟩).1
                        (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ
                          (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ)) e))
                else 0))) := by
  have hjN : pathLength S.x - (k + 1) < pathLength S.x := by omega
  unfold guidedTraceSum
  simp only [Fintype.sum_sigma, TraceGuided, finiteHistoryTraceWeight]
  rw [Finset.sum_eq_single (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ)]
  · have hGG : GhostGuided F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ
        (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ) :=
      (ghostGuided_iff F S γ H _ σ _).mpr rfl
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hE : EdgeGuided F S γ H ⟨pathLength S.x - (k + 1), hjN⟩
        (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ
          (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ)) e
    · have hE' : ∀ hj : pathLength S.x - (k + 1) < pathLength S.x,
          EdgeGuided F S γ H ⟨pathLength S.x - (k + 1), hj⟩
            (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ
              (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ)) e :=
        fun _ => hE
      rw [if_pos hE]
      simp only [Finset.mul_sum, mul_ite, mul_zero]
      apply Finset.sum_congr rfl
      intro t _
      by_cases hT : TraceGuided F S γ H k _ t
      · simp only [hGG, hE', hT, true_and, implies_true, if_true, ite_true]
      · simp only [hT, and_false, if_false, ite_false]
    · rw [if_neg hE]
      simp only [mul_zero]
      apply Finset.sum_eq_zero
      intro t _
      have hE'' : ¬ ∀ hj : pathLength S.x - (k + 1) < pathLength S.x,
          EdgeGuided F S γ H ⟨pathLength S.x - (k + 1), hj⟩
            (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ
              (guidedGhostChoice F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ)) e :=
        fun h => hE (h hjN)
      simp only [hE'', false_and, and_false, if_false, ite_false]
  · intro g _ hg
    apply Finset.sum_eq_zero
    intro e _
    apply Finset.sum_eq_zero
    intro t _
    have hg' : ¬ GhostGuided F S γ H ⟨pathLength S.x - (k + 1), by omega⟩ σ g :=
      fun h => hg ((ghostGuided_iff F S γ H _ σ g).mp h)
    simp only [hg', false_and, if_false, ite_false]
  · intro h; exact absurd (Finset.mem_univ _) h

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
