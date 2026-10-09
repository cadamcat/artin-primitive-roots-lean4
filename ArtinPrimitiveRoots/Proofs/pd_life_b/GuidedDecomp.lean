import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedUnique

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- If every non-vanishing trace is guided by exactly one assignment, the trace sum splits
into guided sums. -/
theorem decomposition_of_unique {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (k : ℕ) (σ : LogPoint S.x K)
    (hu : ∀ t : FiniteHistoryTrace F S γ k σ,
      finiteHistoryTraceWeight F S ρ w B γ k σ t ≠ 0 →
        ∃! H : PDLifeAssignment F S γ, TraceGuided F S γ H k σ t) :
    finiteHistoryFn F S ρ w B γ k σ =
      ∑ H : PDLifeAssignment F S γ, guidedTraceSum F S ρ w B γ H k σ := by
  rw [finiteHistoryFn_eq_trace_sum]
  unfold guidedTraceSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hw : finiteHistoryTraceWeight F S ρ w B γ k σ t = 0
  · rw [hw]; simp
  · obtain ⟨H, hH, huniq⟩ := hu t hw
    rw [Finset.sum_eq_single H]
    · rw [if_pos hH]
    · intro H' _ hne
      rw [if_neg (fun h => hne (huniq H' h))]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **R4–R5 (open).** A non-vanishing trace from the initial state is guided by some lifespan
assignment. See NOTES.md for the planned proof. -/
theorem guided_trace_exists {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (hnd : ((initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
      MemPoint S.x K)).map Prod.snd).Nodup)
    (t : FiniteHistoryTrace F S γ (pathLength S.x)
      ((((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) : MemPoint S.x K),
        initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
          MemPoint S.x K)))
    (hw : finiteHistoryTraceWeight F S ρ w B γ (pathLength S.x) _ t ≠ 0) :
    ∃ H : PDLifeAssignment F S γ, TraceGuided F S γ H (pathLength S.x) _ t := by
  sorry

/-- **R4–R6.** A non-vanishing trace from the initial state is guided by exactly one lifespan
assignment. -/
theorem guided_trace_exists_unique {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (hnd : ((initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
      MemPoint S.x K)).map Prod.snd).Nodup)
    (t : FiniteHistoryTrace F S γ (pathLength S.x)
      ((((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) : MemPoint S.x K),
        initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
          MemPoint S.x K)))
    (hw : finiteHistoryTraceWeight F S ρ w B γ (pathLength S.x) _ t ≠ 0) :
    ∃! H : PDLifeAssignment F S γ, TraceGuided F S γ H (pathLength S.x) _ t := by
  obtain ⟨H, hH⟩ := guided_trace_exists F S ρ w B γ hγ hBands hnd t hw
  exact ⟨H, hH, fun H' hH' =>
    (guided_unique_initial F S ρ w B γ hγ hBands hnd t hw H H' hH hH').symm⟩

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
