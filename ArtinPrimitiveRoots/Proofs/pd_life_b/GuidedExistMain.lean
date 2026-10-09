import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedExistCases

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

theorem tg_cast {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (k : ℕ) (σ₁ σ₂ : LogPoint S.x K) (h : σ₁ = σ₂)
    (t : FiniteHistoryTrace F S γ k σ₁) :
    TraceGuided F S γ H k σ₂ (h ▸ t) ↔ TraceGuided F S γ H k σ₁ t := by
  subst h; rfl

theorem valid_cast {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ₁ σ₂ : LogPoint S.x K) (h : σ₁ = σ₂) (t : FiniteHistoryTrace F S γ k σ₁) :
    FiniteHistoryTraceValid F S w γ k σ₂ (h ▸ t) ↔ FiniteHistoryTraceValid F S w γ k σ₁ t := by
  subst h; rfl

theorem valid_visit {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (hk : k ≤ pathLength S.x) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t) :
    (σ.1.1, σ.1.2.1) = γ ⟨pathLength S.x - k, by omega⟩ := by
  cases k with
  | zero =>
    have e : (⟨pathLength S.x - 0, by omega⟩ : Fin (pathLength S.x + 1)) = Fin.last _ :=
      Fin.ext (by simp)
    rw [e]; exact ht.1
  | succ k => exact ht.1

theorem valid_nodup {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t) : (σ.2.map Prod.snd).Nodup := by
  have hall := finiteHistoryTrace_all_log_nodup F S w γ k σ t ht
  cases k with
  | zero => exact hall.1
  | succ k => exact hall.1

theorem existRec_index {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (j₁ j₂ : Fin (pathLength S.x + 1)) (h : j₁ = j₂) (σ : LogPoint S.x K)
    (hR : ExistRec F S γ j₁ σ) : ExistRec F S γ j₂ σ := by
  subst h; exact hR

theorem lifeState_index {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ)
    (j₁ j₂ : Fin (pathLength S.x + 1)) (h : j₁ = j₂) (σ : LogPoint S.x K)
    (hR : IsLifeState F S γ H j₁ σ) : IsLifeState F S γ H j₂ σ := by
  subst h; exact hR

theorem edge_guided_of {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (j : Fin (pathLength S.x)) (σ : LogPoint S.x K) (g : GhostTraceChoice F S σ)
    (τ : LogPoint S.x K) (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i) (H H' : PDLifeAssignment F S γ)
    (E : StepEnv F S γ j σ g τ π π' c H')
    (hF : ∀ i (p : primeBand S.x (F.a i)), FutPrime S γ j.succ p.1 (H i p) (H' i p)) :
    ∀ i, (c i).1 = decide
      (lifePendingIn F S γ H i (permuteLists π τ.1.2.1 i (lastSlot S.x)) false j.succ) := by
  intro i
  have hp₀ : permuteLists π τ.1.2.1 i (lastSlot S.x) ∈ primeBand S.x (F.a i) := E.hlast i
  have hact₀ : IsActiveAt γ (permuteLists π τ.1.2.1 i (lastSlot S.x)) j.castSucc :=
    (E.hactj _).mpr ⟨i, _, rfl⟩
  obtain ⟨hpendυ, -, -⟩ := prime_next_facts F S γ j σ g τ π π' c H' E i ⟨_, hp₀⟩
  have key : (c i).1 = true ↔
      lifePendingIn F S γ H i (permuteLists π τ.1.2.1 i (lastSlot S.x)) false j.succ := by
    constructor
    · intro hc
      have hmemυ : anchorAt (permuteLists π τ.1.2.1 i (lastSlot S.x)) τ.1.1 ∈
          (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.2 i :=
        (E.hυmem i _).mpr (Or.inr ⟨hc, rfl⟩)
      have h1 := hpendυ.mpr ⟨_, hmemυ, rfl⟩
      exact ⟨hp₀, ((hF i ⟨_, hp₀⟩) j.succ le_rfl).2.2.mpr h1⟩
    · rintro ⟨hp, hpend⟩
      have h2 := ((hF i ⟨_, hp⟩) j.succ le_rfl).2.2.mp hpend
      obtain ⟨q, hq, hq1⟩ := hpendυ.mp h2
      rcases (E.hυmem i q).mp hq with ⟨r, -, hr⟩ | ⟨hc, -⟩
      · exfalso
        have h3 := E.hτmemAct i _ (List.get_mem _ r)
        rw [hr, hq1] at h3
        exact h3 hact₀
      · exact hc
  have goal : (c i).1 = decide
      (lifePendingIn F S γ H i (permuteLists π τ.1.2.1 i (lastSlot S.x)) false j.succ) := by
    by_cases hP : lifePendingIn F S γ H i (permuteLists π τ.1.2.1 i (lastSlot S.x)) false j.succ
    · rw [decide_eq_true hP]; exact key.mpr hP
    · rw [decide_eq_false hP]
      cases hc : (c i).1
      · rfl
      · exact absurd (key.mp hc) hP
  exact goal

/-- **Existence by suffix induction.** -/
theorem exist_aux {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (k : ℕ) (hk : k ≤ pathLength S.x) (σ : LogPoint S.x K)
    (hR : ExistRec F S γ ⟨pathLength S.x - k, by omega⟩ σ)
    (t : FiniteHistoryTrace F S γ k σ) (ht : FiniteHistoryTraceValid F S w γ k σ t) :
    ∃ H : PDLifeAssignment F S γ, IsLifeState F S γ H ⟨pathLength S.x - k, by omega⟩ σ ∧
      TraceGuided F S γ H k σ t := by
  induction k generalizing σ with
  | zero =>
    have e : (⟨pathLength S.x - 0, by omega⟩ : Fin (pathLength S.x + 1)) = Fin.last _ :=
      Fin.ext (by simp)
    rw [e] at hR ⊢
    exact exist_base F S w γ hBands σ hR t ht
  | succ k ih =>
    have hjN : pathLength S.x - (k + 1) < pathLength S.x := by omega
    set jF : Fin (pathLength S.x) := ⟨pathLength S.x - (k + 1), hjN⟩ with hjF
    have hs : jF.succ = ⟨pathLength S.x - k, by omega⟩ := Fin.ext (by simp [hjF]; omega)
    rcases t with ⟨g, e, t'⟩
    obtain ⟨-, hguard, hadm, ht'⟩ := ht
    have hz' : (γ ⟨pathLength S.x - k, by omega⟩).1 = (γ jF.succ).1 := by rw [hs]
    have hυ : edgeTraceOutput F S (pathLength S.x - (k + 1)) (γ ⟨pathLength S.x - k, by omega⟩).1
        (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ g) e =
        edgeTraceOutput F S (pathLength S.x - (k + 1)) (γ jF.succ).1
        (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ g) e := by
      rw [hz']
    have ht'' := (valid_cast F S w γ k _ _ hυ t').mpr ht'
    have hvis := (valid_visit F S w γ k (by omega) _ _ ht'').trans (congrArg γ hs.symm)
    have hnd := valid_nodup F S w γ k _ _ ht''
    have hadm' : EdgeAdmissible F S w
        (permuteLogPoint e.1 (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ g)).1 e.2.1
        (γ jF.succ).1 := by
      have h0 : EdgeAdmissible F S w
          (permuteLogPoint e.1 (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ g)).1 e.2.1
          (γ ⟨pathLength S.x - k, by omega⟩).1 := hadm
      rw [hz'] at h0
      exact h0
    have hS : StepFacts F S w γ jF σ g (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ g)
        e.1 e.2.2 e.2.1 := ⟨rfl, hguard, hadm', hvis, hnd⟩
    have hR' : ExistRec F S γ ⟨pathLength S.x - k, by omega⟩
        (edgeTraceOutput F S (pathLength S.x - (k + 1)) (γ jF.succ).1
          (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ g) e) :=
      existRec_index F S γ _ _ hs _ (existRec_step F S w γ hγ hBands jF σ hR g _ _ _ _ hS)
    obtain ⟨H', hlife', htg'⟩ := ih (by omega) _ hR' _ ht''
    have hlife'' : IsLifeState F S γ H' jF.succ
        (edgeTraceOutput F S jF.val (γ jF.succ).1
          (ghostTraceOutput F S (pathLength S.x - (k + 1)) σ g) (e.1, e.2.1, e.2.2)) :=
      lifeState_index F S γ H' _ _ hs.symm _ hlife'
    have E := stepEnv_of F S w γ hγ hBands jF σ hR g _ _ _ _ hS H' hlife''
    have hex := fun i p => exist_step_prime F S w γ jF σ g _ _ _ _ H' hR hS E i p
    choose H hH using hex
    obtain ⟨hlife, hgg⟩ := lift_primeOK F S γ hBands H jF.castSucc σ hR g
      (fun i p => (hH i p).1)
    refine ⟨H, hlife, hgg, ?_, ?_⟩
    · intro hj i
      exact edge_guided_of F S γ jF σ g _ _ _ _ H H' E (fun i p => (hH i p).2) i
    · have hF : FutAgree F S γ (pathLength S.x - k) H H' := by
        intro i p m hm
        apply (hH i p).2 m
        rw [hs]; exact Fin.le_def.mpr hm
      have := traceGuided_congr F S γ H H' k (by omega) _ _ hF htg'
      exact (tg_cast F S γ H k _ _ hυ t').mp this

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
