import ArtinPrimitiveRoots.Proofs.pd_life_b.FiniteHistoryValidity

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- Finite histories satisfying all literal structural tests. -/
abbrev ValidFiniteHistoryTrace {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (γ : EnvPath S.x K) (k : ℕ) (σ : LogPoint S.x K) :=
  {t : FiniteHistoryTrace F S γ k σ // FiniteHistoryTraceValid F S w γ k σ t}

/-- Only structurally valid histories contribute to the finite recursion. -/
theorem finiteHistoryFn_eq_valid_trace_sum {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (k : ℕ) (σ : LogPoint S.x K) :
    finiteHistoryFn F S ρ w B γ k σ =
      ∑ t : ValidFiniteHistoryTrace F S w γ k σ,
        finiteHistoryTraceWeight F S ρ w B γ k σ t.1 := by
  classical
  rw [finiteHistoryFn_eq_trace_sum]
  have hzero :
      (∑ t : {t : FiniteHistoryTrace F S γ k σ //
          ¬ FiniteHistoryTraceValid F S w γ k σ t},
        finiteHistoryTraceWeight F S ρ w B γ k σ t.1) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    exact finiteHistoryTraceWeight_zero_of_not_valid F S ρ w B γ k σ t.1 t.2
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (FiniteHistoryTraceValid F S w γ k σ)
    (finiteHistoryTraceWeight F S ρ w B γ k σ)
  simpa only [hzero, add_zero] using hsplit.symm

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
