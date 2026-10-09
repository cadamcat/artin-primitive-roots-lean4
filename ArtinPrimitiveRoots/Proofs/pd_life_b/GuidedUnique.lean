import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedAssembly

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

theorem weight_ne_zero_visit {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (k : ℕ) (hk : k ≤ pathLength S.x)
    (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (h : finiteHistoryTraceWeight F S ρ w B γ k σ t ≠ 0) :
    (σ.1.1, σ.1.2.1) = γ ⟨pathLength S.x - k, by omega⟩ := by
  by_contra hv
  apply h
  obtain ⟨r, hr⟩ := weight_head F S ρ w B γ k σ t
  rw [hr]
  unfold historyVisitFactor
  rw [dif_pos (by omega), if_neg hv]
  ring

theorem weight_ne_zero_nodup {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (k : ℕ)
    (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (h : finiteHistoryTraceWeight F S ρ w B γ k σ t ≠ 0) :
    (σ.2.map Prod.snd).Nodup := by
  by_contra hn
  apply h
  apply finiteHistoryTraceWeight_zero_of_not_valid
  intro hv
  have hall := finiteHistoryTrace_all_log_nodup F S w γ k σ t hv
  apply hn
  cases k with
  | zero => exact hall.1
  | succ k => exact hall.1

/-- A guided edge with non-vanishing charge and a visited, repetition-free output is the
forced edge, and leads to the next life state. -/
theorem edge_forced {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x)) (τ : LogPoint S.x K)
    (hτ : IsLifeStateAfter F S γ H j.castSucc τ) (e : EdgeTraceChoice F S τ)
    (hE : EdgeGuided F S γ H j τ e) (jS : Fin (pathLength S.x + 1)) (hjS : jS = j.succ)
    (hc : edgeTraceCharge F S ρ w j.val (γ jS).1 τ e ≠ 0)
    (hv : ((edgeTraceOutput F S j.val (γ jS).1 τ e).1.1,
      (edgeTraceOutput F S j.val (γ jS).1 τ e).1.2.1) = γ jS)
    (hn : ((edgeTraceOutput F S j.val (γ jS).1 τ e).2.map Prod.snd).Nodup) :
    IsLifeState F S γ H jS (edgeTraceOutput F S j.val (γ jS).1 τ e) := by
  subst hjS
  obtain ⟨π, c, π'⟩ := e
  have hl : τ.1.2.1 = (γ j.castSucc).2 := congrArg Prod.snd hτ.1
  have hQv : ValidPrimeLists S.x K F.a (permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2) :=
    guided_validPrimeLists_permute _ _ (hγ.1 j.succ).2
  let q : (i : Fin K) → primeBand S.x (F.a i) := fun i =>
    ⟨permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2 i (lastSlot S.x), (hQv.1 i _).2⟩
  have hq : ∀ i, (q i).1 =
      permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2 i (lastSlot S.x) := fun i => rfl
  have hcH : c = guidedEdgeChoice F S γ H j τ π q := by
    by_contra hne
    let G : LogPoint S.x K → ℂ := fun υ =>
      if (υ.1.1, υ.1.2.1) = γ j.succ ∧ (υ.2.map Prod.snd).Nodup then 1 else 0
    have h0 := guided_edge_other_zero F S γ H j τ hτ π π' q hq G
      (fun υ hG => by by_contra h; exact hG (by simp only [G]; rw [if_neg (fun h' => h h'.1)]))
      (fun υ hG => by by_contra h; exact hG (by simp only [G]; rw [if_neg (fun h' => h h'.2)]))
      c (fun i => hE i) hne
    simp only [G] at h0
    rw [if_pos ⟨hv, hn⟩] at h0
    exact one_ne_zero h0
  subst hcH
  have hLQ := visit_target F S γ j τ π π' _ hv
  have hST : IsSlotTransition (permuteLists π (γ j.castSucc).2)
      (permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2) := by
    by_contra hns
    apply hc
    unfold edgeTraceCharge
    dsimp only
    rw [if_neg, mul_zero]
    intro hAdm
    apply hns
    have h4 := hAdm.2.2.2.1
    rw [hLQ] at h4
    have e1 : (permuteLogPoint π τ).1.2.1 = permuteLists π (γ j.castSucc).2 := by
      show permuteLists π τ.1.2.1 = _
      rw [hl]
    rw [e1] at h4
    exact h4
  exact guided_edge_output F S γ hγ hBands H j τ hτ π π' hST q hq

/-- Two assignments guiding the same ghost from a common life state have the same events
at that visit. -/
theorem events_agree {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H H' : PDLifeAssignment F S γ) (j : Fin (pathLength S.x + 1)) (σ : LogPoint S.x K)
    (hσ : IsLifeState F S γ H j σ) (hσ' : IsLifeState F S γ H' j σ)
    (g : GhostTraceChoice F S σ) (hg : GhostGuided F S γ H j σ g)
    (hg' : GhostGuided F S γ H' j σ g) (i : Fin K) (p : primeBand S.x (F.a i)) :
    ((H i p).1.1 = some j ↔ (H' i p).1.1 = some j) ∧
      ((H i p).1.2 = some j ↔ (H' i p).1.2 = some j) := by
  have hb : ∀ (A A' : PDLifeAssignment F S γ), GhostGuided F S γ A j σ g →
      GhostGuided F S γ A' j σ g → (A i p).1.1 = some j → (A' i p).1.1 = some j := by
    intro A A' hA hA' h
    have h1 : p.1 ∈ (g.2 i).1 := by
      rw [(hA i).2]; exact Finset.mem_filter.mpr ⟨p.2, p.2, h⟩
    rw [(hA' i).2] at h1
    obtain ⟨-, hp, h2⟩ := Finset.mem_filter.mp h1
    exact h2
  have hd : ∀ (A A' : PDLifeAssignment F S γ), IsLifeState F S γ A j σ →
      GhostGuided F S γ A j σ g →
      GhostGuided F S γ A' j σ g → (A i p).1.2 = some j → (A' i p).1.2 = some j := by
    intro A A' hσA hA hA' h
    obtain ⟨hpend, -⟩ := life_delete_pending_hit S γ p.1 (A i p) j h
    obtain ⟨r, hr⟩ := List.mem_iff_get.mp
      ((hσA.2.2.1 i (p.1, (lifeLine S γ p.1 (A i p).1).val)).mpr ⟨p.2, hpend, rfl⟩)
    have h1 : r ∈ g.1 i := by
      rw [(hA i).1]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hr]
      exact ⟨p.2, h⟩
    rw [(hA' i).1] at h1
    have h2 := (Finset.mem_filter.mp h1).2
    rw [hr] at h2
    obtain ⟨hp, h3⟩ := h2
    exact h3
  exact ⟨⟨hb H H' hg hg', hb H' H hg' hg⟩, ⟨hd H H' hσ hg hg', hd H' H hσ' hg' hg⟩⟩

/-- Two assignments guiding the same non-vanishing trace from a common life state agree on
all events from that visit on. -/
theorem guided_agree {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (H H' : PDLifeAssignment F S γ) (k : ℕ) (hk : k ≤ pathLength S.x) (σ : LogPoint S.x K)
    (hσ : IsLifeState F S γ H ⟨pathLength S.x - k, by omega⟩ σ)
    (hσ' : IsLifeState F S γ H' ⟨pathLength S.x - k, by omega⟩ σ)
    (t : FiniteHistoryTrace F S γ k σ)
    (hw : finiteHistoryTraceWeight F S ρ w B γ k σ t ≠ 0)
    (ht : TraceGuided F S γ H k σ t) (ht' : TraceGuided F S γ H' k σ t) :
    ∀ i (p : primeBand S.x (F.a i)) (m : Fin (pathLength S.x + 1)),
      pathLength S.x - k ≤ m.val →
        ((H i p).1.1 = some m ↔ (H' i p).1.1 = some m) ∧
          ((H i p).1.2 = some m ↔ (H' i p).1.2 = some m) := by
  induction k generalizing σ with
  | zero =>
    have e : (⟨pathLength S.x - 0, by omega⟩ : Fin (pathLength S.x + 1)) =
        Fin.last _ := Fin.ext (by simp)
    rw [e] at hσ hσ'
    intro i p m hm
    have hmL : m = Fin.last _ := Fin.ext (by have := m.isLt; simp at hm ⊢; omega)
    subst hmL
    exact events_agree F S γ H H' _ σ hσ hσ' t ht ht' i p
  | succ k ih =>
    have hjN : pathLength S.x - (k + 1) < pathLength S.x := by omega
    set jF : Fin (pathLength S.x) := ⟨pathLength S.x - (k + 1), hjN⟩ with hjF
    have hs : jF.succ = ⟨pathLength S.x - k, by omega⟩ := Fin.ext (by simp [hjF]; omega)
    obtain ⟨hG, hE, hT⟩ := ht
    obtain ⟨hG', hE', hT'⟩ := ht'
    have hw' := hw
    simp only [finiteHistoryTraceWeight, ne_eq, mul_eq_zero, not_or] at hw'
    obtain ⟨-, -, -, -, hc, -, hW⟩ := hw'
    have hgH := (ghostGuided_iff F S γ H _ σ t.1).mp hG
    have hgH' := (ghostGuided_iff F S γ H' _ σ t.1).mp hG'
    have hτ : IsLifeStateAfter F S γ H jF.castSucc
        (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ t.1) := by
      rw [hgH]; exact guided_ghost_output F S γ H hBands _ σ hσ
    have hτ' : IsLifeStateAfter F S γ H' jF.castSucc
        (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ t.1) := by
      rw [hgH']; exact guided_ghost_output F S γ H' hBands _ σ hσ'
    have hv := weight_ne_zero_visit F S ρ w B γ k (by omega) _ t.2.2 hW
    have hn := weight_ne_zero_nodup F S ρ w B γ k _ t.2.2 hW
    have hυ := edge_forced F S ρ w γ hγ hBands H jF _ hτ t.2.1 (hE hjN) _ hs.symm hc hv hn
    have hυ' := edge_forced F S ρ w γ hγ hBands H' jF _ hτ' t.2.1 (hE' hjN) _ hs.symm hc hv hn
    intro i p m hm
    by_cases hmj : m.val = pathLength S.x - (k + 1)
    · have hmE : m = ⟨pathLength S.x - (k + 1), by omega⟩ := Fin.ext hmj
      rw [hmE]
      exact events_agree F S γ H H' _ σ hσ hσ' t.1 hG hG' i p
    · exact ih (by omega) _ hυ hυ' t.2.2 hW hT hT' i p m (by omega)

theorem option_eq_of_some_iff {α : Type*} (x y : Option α)
    (h : ∀ m, x = some m ↔ y = some m) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b => exact absurd ((h b).mpr rfl) (by simp)
  | some a => exact ((h a).mp rfl).symm

/-- **R6.** Uniqueness of the guiding assignment of a non-vanishing trace from the initial
state. -/
theorem guided_unique_initial {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (hnd : ((initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
      MemPoint S.x K)).map Prod.snd).Nodup)
    (t : FiniteHistoryTrace F S γ (pathLength S.x)
      ((((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) : MemPoint S.x K),
        initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
          MemPoint S.x K)))
    (hw : finiteHistoryTraceWeight F S ρ w B γ (pathLength S.x) _ t ≠ 0)
    (H H' : PDLifeAssignment F S γ)
    (ht : TraceGuided F S γ H (pathLength S.x) _ t)
    (ht' : TraceGuided F S γ H' (pathLength S.x) _ t) : H = H' := by
  have e0 : (⟨pathLength S.x - pathLength S.x, by omega⟩ : Fin (pathLength S.x + 1)) =
      ⟨0, by omega⟩ := Fin.ext (Nat.sub_self _)
  have hag := guided_agree F S ρ w B γ hγ hBands H H' _ le_rfl _
    (by rw [e0]; exact lifeState_initial F S γ H hnd)
    (by rw [e0]; exact lifeState_initial F S γ H' hnd) t hw ht ht'
  funext i p
  apply Subtype.ext
  apply Prod.ext
  · exact option_eq_of_some_iff _ _ (fun m => (hag i p m (by omega)).1)
  · exact option_eq_of_some_iff _ _ (fun m => (hag i p m (by omega)).2)

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
