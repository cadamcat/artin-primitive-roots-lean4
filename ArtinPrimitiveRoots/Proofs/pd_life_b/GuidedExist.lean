import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedOutputs

set_option autoImplicit false

/-! Existence of a guiding assignment: the past-record invariant `ExistRec`. -/

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- What a reachable state at visit `j` records about the past. -/
structure ExistRec {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (j : Fin (pathLength S.x + 1)) (σ : LogPoint S.x K) : Prop where
  pos : (σ.1.1, σ.1.2.1) = γ j
  memNodup : ∀ i, ((σ.1.2.2 i).map Prod.fst).Nodup
  logNodup : (σ.2.map Prod.snd).Nodup
  memBand : ∀ i, ∀ q ∈ σ.1.2.2 i, q.1 ∈ primeBand S.x (F.a i)
  memLog : ∀ i, ∀ q ∈ σ.1.2.2 i, q.1 ∈ σ.2.map Prod.snd
  logBand : ∀ p ∈ σ.2.map Prod.snd, ∃ i, p ∈ primeBand S.x (F.a i)
  actLog : ∀ p (m : Fin (pathLength S.x + 1)), m ≤ j → IsActiveAt γ p m →
    p ∈ σ.2.map Prod.snd
  actLine : ∀ p (m m' : Fin (pathLength S.x + 1)), m ≤ j → m' ≤ j →
    IsActiveAt γ p m → IsActiveAt γ p m' → projLine p (γ m).1 = projLine p (γ m').1
  memRec : ∀ i, ∀ q ∈ σ.1.2.2 i, ¬ IsActiveAt γ q.1 j ∧
    (((∃ a : Fin (pathLength S.x + 1), a < j ∧ (projLine q.1 (γ a).1).val = q.2) ∧
        ∀ m, m ≤ j → ¬ IsActiveAt γ q.1 m) ∨
      ∃ m : Fin (pathLength S.x + 1), m < j ∧ IsActiveAt γ q.1 m ∧
        (projLine q.1 (γ m).1).val = q.2)
  deadRec : ∀ i (p : ℕ), p ∈ primeBand S.x (F.a i) → p ∈ σ.2.map Prod.snd →
    (∀ q ∈ σ.1.2.2 i, q.1 ≠ p) → ¬ IsActiveAt γ p j →
    (∃ m : Fin (pathLength S.x + 1), m < j ∧ IsActiveAt γ p m) ∨
      ∃ a c : Fin (pathLength S.x + 1), a < c ∧ c < j ∧
        projLine p (γ c).1 = projLine p (γ a).1 ∧ ∀ m, m ≤ j → ¬ IsActiveAt γ p m

theorem existRec_initial {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (hγ : IsEnvPathAdmissible F S γ)
    (hnd : ((initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
      MemPoint S.x K)).map Prod.snd).Nodup) :
    ExistRec F S γ ⟨0, by omega⟩
      ((((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) : MemPoint S.x K),
        initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
          MemPoint S.x K)) := by
  have hlog : ∀ p, p ∈ (initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
      MemPoint S.x K)).map Prod.snd ↔ IsActiveAt γ p ⟨0, by omega⟩ := by
    intro p
    unfold initialLog IsActiveAt
    simp only [List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_finRange, true_and,
      List.mem_map, Function.comp_def]
  have h0 : ∀ m : Fin (pathLength S.x + 1), m ≤ ⟨0, by omega⟩ → m = ⟨0, by omega⟩ := by
    intro m hm
    apply Fin.ext
    have := Fin.le_def.mp hm
    simp only [Fin.val_mk] at this ⊢
    omega
  refine ⟨rfl, fun i => List.nodup_nil, hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i q hq; simp at hq
  · intro i q hq; simp at hq
  · intro p hp
    obtain ⟨i, jj, hij⟩ := (hlog p).mp hp
    exact ⟨i, hij ▸ ((hγ.1 ⟨0, by omega⟩).2.1 i jj).2⟩
  · intro p m hm hact
    rw [h0 m hm] at hact
    exact (hlog p).mpr hact
  · intro p m m' hm hm' _ _
    rw [h0 m hm, h0 m' hm']
  · intro i q hq; simp at hq
  · intro i p _ hp _ hna
    exact absurd ((hlog p).mp hp) hna

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
