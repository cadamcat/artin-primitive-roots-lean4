import ArtinPrimitiveRoots.Proofs.pd_life_b.FiniteGhostTrace

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- The complex indicator of the memory cutoff at one state. -/
def historyCutoffFactor {x : ℝ} {K : ℕ} (B : Option ℕ)
    (σ : LogPoint x K) : ℂ :=
  match B with
  | none => 1
  | some b => if memSize σ.1 ≤ b then 1 else 0

/-- The complex indicator of the prescribed external visit. -/
def historyVisitFactor {x : ℝ} {K : ℕ} (γ : EnvPath x K)
    (j : ℕ) (σ : LogPoint x K) : ℂ :=
  if hj : j < pathLength x + 1 then
    if (σ.1.1, σ.1.2.1) = γ ⟨j, hj⟩ then 1 else 0
  else 0

/-- A finite tree of ghost and edge choices, indexed by its actual source state. -/
@[reducible]
def FiniteHistoryTrace {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) : ℕ → LogPoint S.x K → Type
  | 0, σ => GhostTraceChoice F S σ
  | k + 1, σ =>
      Σ g : GhostTraceChoice F S σ,
        Σ e : EdgeTraceChoice F S
            (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ g),
          FiniteHistoryTrace F S γ k
            (edgeTraceOutput F S (pathLength S.x - (k + 1))
              (γ ⟨pathLength S.x - k,
                Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
              (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ g) e)

/-- Enumerate each finite trace by enumerating its dependent fibers recursively. -/
@[instance_reducible]
def finiteHistoryTraceFintype {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) : (k : ℕ) → (σ : LogPoint S.x K) →
      Fintype (FiniteHistoryTrace F S γ k σ)
  | 0, σ => by
      change Fintype (GhostTraceChoice F S σ)
      infer_instance
  | k + 1, σ => by
      letI : (τ : LogPoint S.x K) → Fintype (FiniteHistoryTrace F S γ k τ) :=
        finiteHistoryTraceFintype F S γ k
      change Fintype (Σ g : GhostTraceChoice F S σ,
        Σ e : EdgeTraceChoice F S
            (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ g),
          FiniteHistoryTrace F S γ k
            (edgeTraceOutput F S (pathLength S.x - (k + 1))
              (γ ⟨pathLength S.x - k,
                Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
              (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ g) e))
      infer_instance

instance instFintypeFiniteHistoryTrace {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (k : ℕ) (σ : LogPoint S.x K) :
    Fintype (FiniteHistoryTrace F S γ k σ) :=
  finiteHistoryTraceFintype F S γ k σ

/-- The literal history charge, including all cutoffs, visits, and the terminal boundary. -/
def finiteHistoryTraceWeight {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : Option ℕ) (γ : EnvPath S.x K) :
    (k : ℕ) → (σ : LogPoint S.x K) → FiniteHistoryTrace F S γ k σ → ℂ
  | 0, σ, t =>
      let τ := ghostTraceOutput F S (pathLength S.x) σ t
      historyCutoffFactor B σ *
        (historyVisitFactor γ (pathLength S.x) σ *
          (ghostTraceCharge F S ρ (pathLength S.x) σ t *
            (historyCutoffFactor B τ * logBoundaryOut distinctWeight τ)))
  | k + 1, σ, t =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      historyCutoffFactor B σ *
        (historyVisitFactor γ j σ *
          (ghostTraceCharge F S ρ j σ t.1 *
            (historyCutoffFactor B τ *
              (edgeTraceCharge F S ρ w j z' τ t.2.1 *
                (historyCutoffFactor B υ *
                  finiteHistoryTraceWeight F S ρ w B γ k υ t.2.2)))))

/-- The finite fixed-path recursion equals its complete finite trace sum. -/
theorem finiteHistoryFn_eq_trace_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : Option ℕ) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) :
    finiteHistoryFn F S ρ w B γ k σ =
      ∑ t : FiniteHistoryTrace F S γ k σ,
        finiteHistoryTraceWeight F S ρ w B γ k σ t := by
  classical
  have hTrunc (f : LogPoint S.x K → ℂ) (τ : LogPoint S.x K) :
      logTrunc B f τ = historyCutoffFactor B τ * f τ := by
    cases B with
    | none => simp only [logTrunc, historyCutoffFactor, one_mul]
    | some b =>
        by_cases h : memSize τ.1 ≤ b <;>
          simp only [logTrunc, historyCutoffFactor, h, ite_true, ite_false,
            one_mul, zero_mul]
  have hVisit (j : ℕ) (f : LogPoint S.x K → ℂ) (τ : LogPoint S.x K) :
      logPathRestrict (some γ) j f τ = historyVisitFactor γ j τ * f τ := by
    by_cases hj : j < pathLength S.x + 1
    · simp only [logPathRestrict, historyVisitFactor, dite_eq_left hj]
      by_cases h : (τ.1.1, τ.1.2.1) = γ ⟨j, hj⟩ <;>
        simp only [h, ite_true, ite_false, one_mul, zero_mul]
    · simp only [logPathRestrict, historyVisitFactor, dite_eq_right hj, zero_mul]
  induction k generalizing σ with
  | zero =>
      rw [finiteHistoryFn, hTrunc, hVisit, subsetGhost_eq_trace_sum]
      simp_rw [hTrunc]
      simp only [finiteHistoryTraceWeight, Finset.mul_sum]
  | succ k ih =>
      simp only [Fintype.sum_sigma]
      rw [finiteHistoryFn]
      rw [hTrunc, hVisit, subsetGhost_eq_trace_sum]
      simp_rw [hTrunc]
      simp_rw [edgeAtPosition_eq_choice_sum, edgeChoiceAtPosition_eq_trace_sum,
        hTrunc, ih]
      simp only [finiteHistoryTraceWeight, Finset.mul_sum]

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
