import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedStepEnv

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- A lifespan not pending at `m0`, inactive there and born before it, has nothing from
`m0` on. -/
theorem dead_from {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) (e : PrimeLife S γ p)
    (m0 : Fin (pathLength S.x + 1)) (hnp : ¬ pdLifePending S γ p e false m0)
    (hna : ¬ IsActiveAt γ p m0)
    (hb : (∃ a, e.1.1 = some a ∧ a < m0) ∨ ∃ m, m < m0 ∧ IsActiveAt γ p m) :
    (∀ m, m0 ≤ m → ¬ IsActiveAt γ p m) ∧ (∀ c, e.1.2 = some c → c < m0) ∧
      (∀ a, e.1.1 = some a → a < m0) ∧ ∀ m, m0 ≤ m → ¬ pdLifePending S γ p e false m := by
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · obtain ⟨hAJ, hB, hC, -⟩ := life_active_facts S γ p e hA
    have hαact : IsActiveAt γ p ((pdLifeActive S γ p).min' hA) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
    have hωact : IsActiveAt γ p ((pdLifeActive S γ p).max' hA) :=
      (Finset.mem_filter.mp (Finset.max'_mem _ hA)).2
    rw [pend_active_iff S γ p e hA] at hnp
    have hborn : (∃ a, e.1.1 = some a ∧ a < m0) ∨ (pdLifeActive S γ p).min' hA < m0 := by
      rcases hb with h | ⟨m, hm, hact⟩
      · exact Or.inl h
      · exact Or.inr (lt_of_le_of_lt (hAJ m hact).1 hm)
    have hfut : ¬ ((∃ c, e.1.2 = some c ∧ m0 ≤ c) ∨ m0 < (pdLifeActive S γ p).max' hA) :=
      fun h => hnp ⟨hna, hborn, h⟩
    push_neg at hfut
    have hω : (pdLifeActive S γ p).max' hA < m0 :=
      lt_of_le_of_ne hfut.2 (fun h => hna (h ▸ hωact))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro m hm hact
      exact absurd (lt_of_le_of_lt (hAJ m hact).2 hω) (not_lt.mpr hm)
    · intro c hc
      exact not_le.mp (fun h => absurd h (not_le.mpr (by
        have := hfut.1 c hc; exact this)))
    · intro a ha
      exact lt_trans (hB a ha).1 (lt_of_le_of_lt (hAJ _ hαact).2 hω)
    · intro m hm hpm
      rw [pend_active_iff S γ p e hA] at hpm
      rcases hpm.2.2 with ⟨c, hc, hmc⟩ | hmω
      · exact absurd (lt_of_lt_of_le (hfut.1 c hc) (le_trans hm hmc)) (lt_irrefl _)
      · exact absurd (lt_trans hmω hω) (not_lt.mpr hm)
  · rcases life_inactive_facts S γ p e hA with he | ⟨a, c, he, hac, -⟩
    · rcases hb with ⟨a, ha, -⟩ | ⟨m, -, hact⟩
      · rw [he] at ha; simp at ha
      · exact absurd ⟨m, (mem_active_iff S γ p m).mpr hact⟩ hA
    · have ha0 : a < m0 := by
        rcases hb with ⟨a', ha', h⟩ | ⟨m, -, hact⟩
        · rw [he] at ha'; simp only [Option.some.injEq] at ha'; rw [ha']; exact h
        · exact absurd ⟨m, (mem_active_iff S γ p m).mpr hact⟩ hA
      rw [pend_inactive_iff S γ p e hA] at hnp
      have hc0 : c < m0 := by
        by_contra h
        exact hnp ⟨a, c, he, ha0, not_lt.mp h⟩
      refine ⟨fun m _ hact => hA ⟨m, (mem_active_iff S γ p m).mpr hact⟩, ?_, ?_, ?_⟩
      · intro c' hc'; rw [he] at hc'; simp only [Option.some.injEq] at hc'; rw [← hc']; exact hc0
      · intro a' ha'; rw [he] at ha'; simp only [Option.some.injEq] at ha'; rw [← ha']; exact ha0
      · intro m hm hpm
        rw [pend_inactive_iff S γ p e hA] at hpm
        obtain ⟨a', c', he', -, hmc⟩ := hpm
        rw [he] at he'
        simp only [Prod.mk.injEq, Option.some.injEq] at he'
        rw [← he'.2] at hmc
        exact absurd (lt_of_lt_of_le hc0 (le_trans hm hmc)) (lt_irrefl _)

/-- A lifespan pending or active at `m0` has its birth before `m0` and its deletion from
`m0` on. -/
theorem alive_at {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) (e : PrimeLife S γ p)
    (m0 : Fin (pathLength S.x + 1))
    (h : pdLifePending S γ p e false m0 ∨ IsActiveAt γ p m0) :
    (∀ a, e.1.1 = some a → a < m0) ∧ (∀ c, e.1.2 = some c → m0 ≤ c) := by
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · obtain ⟨hAJ, hB, hC, -⟩ := life_active_facts S γ p e hA
    rcases h with hp | hact
    · rw [pend_active_iff S γ p e hA] at hp
      obtain ⟨-, hb, hf⟩ := hp
      constructor
      · intro a ha
        rcases hb with ⟨a', ha', h'⟩ | hα
        · rw [ha] at ha'; simp only [Option.some.injEq] at ha'; rw [ha']; exact h'
        · exact lt_trans (hB a ha).1 hα
      · intro c hc
        rcases hf with ⟨c', hc', h'⟩ | hω
        · rw [hc] at hc'; simp only [Option.some.injEq] at hc'; rw [hc']; exact h'
        · exact le_of_lt (lt_trans hω (hC c hc))
    · exact ⟨fun a ha => lt_of_lt_of_le (hB a ha).1 (hAJ _ hact).1,
        fun c hc => le_of_lt (lt_of_le_of_lt (hAJ _ hact).2 (hC c hc))⟩
  · rcases h with hp | hact
    · rw [pend_inactive_iff S γ p e hA] at hp
      obtain ⟨a, c, he, ha, hc⟩ := hp
      constructor
      · intro a' ha'; rw [he] at ha'; simp only [Option.some.injEq] at ha'; rw [← ha']; exact ha
      · intro c' hc'; rw [he] at hc'; simp only [Option.some.injEq] at hc'; rw [← hc']; exact hc
    · exact absurd ⟨m0, (mem_active_iff S γ p m0).mpr hact⟩ hA

/-- Facts on one prime from the life state of `H'` at the next visit. -/
theorem prime_next_facts {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (j : Fin (pathLength S.x)) (σ : LogPoint S.x K) (g : GhostTraceChoice F S σ)
    (τ : LogPoint S.x K) (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i) (H' : PDLifeAssignment F S γ)
    (E : StepEnv F S γ j σ g τ π π' c H') (i : Fin K) (p : primeBand S.x (F.a i)) :
    (pdLifePending S γ p.1 (H' i p) false j.succ ↔
      ∃ q ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.2 i, q.1 = p.1) ∧
    (∀ q ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.2 i, q.1 = p.1 →
      q.2 = (lifeLine S γ p.1 (H' i p).1).val) ∧
    (p.1 ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).2.map Prod.snd ↔
      (∃ m, m ≤ j.succ ∧ IsActiveAt γ p.1 m) ∨ ∃ a, (H' i p).1.1 = some a ∧ a < j.succ) := by
  refine ⟨⟨fun h => ⟨_, (E.hH'mem i (p.1, (lifeLine S γ p.1 (H' i p).1).val)).mpr
      ⟨p.2, h, rfl⟩, rfl⟩, ?_⟩, ?_, ?_⟩
  · rintro ⟨⟨q1, q2⟩, hq, hq1⟩
    obtain ⟨hp, hpend, -⟩ := (E.hH'mem i _).mp hq
    simp only at hq1 hpend hp
    subst hq1
    exact hpend
  · rintro ⟨q1, q2⟩ hq hq1
    obtain ⟨hp, -, hanc⟩ := (E.hH'mem i _).mp hq
    simp only at hq1 hanc hp ⊢
    subst hq1
    exact hanc
  · rw [E.hH'log]
    unfold lifeBornBefore
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨i', a, ha, hp', hb⟩
      have hii := E.hgroup i' i p.1 hp' p.2
      subst hii
      exact ⟨a, hb, ha⟩
    · rintro ⟨a, hb, ha⟩
      exact ⟨i, a, ha, p.2, hb⟩

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
