import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedExistGen

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- Agreement of two lifespans on everything used by guidance from `m0` on. -/
def FutPrime {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (m0 : Fin (pathLength S.x + 1))
    (p : ℕ) (e e' : PrimeLife S γ p) : Prop :=
  ∀ m : Fin (pathLength S.x + 1), m0 ≤ m →
    (e.1.1 = some m ↔ e'.1.1 = some m) ∧ (e.1.2 = some m ↔ e'.1.2 = some m) ∧
      (pdLifePending S γ p e false m ↔ pdLifePending S γ p e' false m)

theorem life_active_death_line {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (hA : (pdLifeActive S γ p).Nonempty) (c : Fin (pathLength S.x + 1))
    (hc : e.1.2 = some c) :
    projLine p (γ c).1 = projLine p (γ ((pdLifeActive S γ p).min' hA)).1 := by
  have hv : pdLifeEndpointValid S γ p e.1 := (Finset.mem_filter.mp e.2).2
  simp only [pdLifeEndpointValid, hA, ↓reduceDIte] at hv
  have h3 := hv.2.2
  rw [hc] at h3
  exact h3.2

theorem fin_lt_succ_iff' {n : ℕ} (j : Fin n) (m : Fin (n + 1)) :
    m < j.succ ↔ m ≤ j.castSucc := by
  rw [Fin.lt_def, Fin.le_def]; simp only [Fin.val_succ, Fin.coe_castSucc]; omega

/-- Deletion part of an active-type lifespan, for the constructor. -/
theorem death_ok {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) (e : PrimeLife S γ p)
    (hA : (pdLifeActive S γ p).Nonempty) :
    ∀ c, e.1.2 = some c → (∀ m, IsActiveAt γ p m → m < c) ∧
      ∃ m, IsActiveAt γ p m ∧ projLine p (γ c).1 = projLine p (γ m).1 := by
  intro c hc
  obtain ⟨hAJ, -, hC, -⟩ := life_active_facts S γ p e hA
  have hαact : IsActiveAt γ p ((pdLifeActive S γ p).min' hA) :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
  exact ⟨fun m hm => lt_of_le_of_lt (hAJ m hm).2 (hC c hc), _, hαact,
    life_active_death_line S γ p e hA c hc⟩

theorem birth_ok {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) (e : PrimeLife S γ p)
    (hA : (pdLifeActive S γ p).Nonempty) :
    ∀ a, e.1.1 = some a → (∀ m, IsActiveAt γ p m → a < m) ∧
      ∃ m, IsActiveAt γ p m ∧ projLine p (γ a).1 = projLine p (γ m).1 := by
  intro a ha
  obtain ⟨hAJ, hB, -, -⟩ := life_active_facts S γ p e hA
  have hαact : IsActiveAt γ p ((pdLifeActive S γ p).min' hA) :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
  exact ⟨fun m hm => lt_of_lt_of_le (hB a ha).1 (hAJ m hm).1, _, hαact, (hB a ha).2⟩

variable {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
  (j : Fin (pathLength S.x)) (σ : LogPoint S.x K) (g : GhostTraceChoice F S σ)
  (τ : LogPoint S.x K) (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
  (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i) (H' : PDLifeAssignment F S γ)

theorem case_active (hR : ExistRec F S γ j.castSucc σ)
    (E : StepEnv F S γ j σ g τ π π' c H') (i : Fin K) (p : primeBand S.x (F.a i))
    (hact : IsActiveAt γ p.1 j.castSucc) :
    ∃ e : PrimeLife S γ p.1, PrimeOK F S γ j.castSucc σ g i p e ∧
      FutPrime S γ j.succ p.1 e (H' i p) := by
  have hA : (pdLifeActive S γ p.1).Nonempty := ⟨_, (mem_active_iff S γ p.1 _).mpr hact⟩
  obtain ⟨hAJ, hB, hC, -⟩ := life_active_facts S γ p.1 (H' i p) hA
  have hlog := hR.actLog p.1 _ le_rfl hact
  have hnomem : ¬ ∃ q ∈ σ.1.2.2 i, q.1 = p.1 := by
    rintro ⟨q, hq, hq1⟩
    exact (hR.memRec i q hq).1 (hq1 ▸ hact)
  refine ⟨H' i p, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun m _ => ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩⟩
  · exact ⟨fun h => absurd hact (fun h' => not_pending_of_active S γ _ _ false _ h' h),
      fun h => absurd h hnomem⟩
  · intro q hq hq1; exact absurd ⟨q, hq, hq1⟩ hnomem
  · intro _ _ _; exact hlog
  · intro _; exact Or.inl ⟨_, le_rfl, hact⟩
  · constructor
    · intro h
      exact absurd (lt_of_lt_of_le (hB _ h).1 (hAJ _ hact).1) (lt_irrefl _)
    · intro h; exact absurd hlog (E.hborn i _ h)
  · constructor
    · intro h
      exact absurd (lt_of_le_of_lt (hAJ _ hact).2 (hC _ h)) (lt_irrefl _)
    · rintro ⟨r, -, hr⟩
      exact absurd ⟨_, List.get_mem _ r, hr⟩ hnomem

theorem case_dead (hR : ExistRec F S γ j.castSucc σ)
    (E : StepEnv F S γ j σ g τ π π' c H') (i : Fin K) (p : primeBand S.x (F.a i))
    (hlog : p.1 ∈ σ.2.map Prod.snd) (hmem : ∀ q ∈ σ.1.2.2 i, q.1 ≠ p.1)
    (hna : ¬ IsActiveAt γ p.1 j.castSucc) :
    ∃ e : PrimeLife S γ p.1, PrimeOK F S γ j.castSucc σ g i p e ∧
      FutPrime S γ j.succ p.1 e (H' i p) := by
  obtain ⟨hpendυ, -, hbornυ⟩ := prime_next_facts F S γ j σ g τ π π' c H' E i p
  have hτlog : p.1 ∈ τ.2.map Prod.snd := (E.hτlog _).mpr (Or.inl hlog)
  have hτnoP : ∀ q ∈ τ.1.2.2 i, q.1 ≠ p.1 := by
    intro q hq hq1
    rcases (E.hτmem i q).mp hq with ⟨r, -, rfl⟩ | ⟨hb, -⟩
    · exact hmem _ (List.get_mem _ r) hq1
    · exact E.hborn i _ hb (hq1 ▸ hlog)
  have hnactS : ¬ IsActiveAt γ p.1 j.succ := by
    intro h
    obtain ⟨i', y, hy⟩ := (E.hactj1 _).mp h
    rw [E.hLy] at hy
    split_ifs at hy with hyJ
    · exact hna ((E.hactj _).mpr ⟨i', y, hy⟩)
    · have hii := E.hgroup i' i _ (hy ▸ E.hlabelBand i') p.2
      subst hii
      rcases E.hlabel i' _ hy with ⟨k, -, hk⟩ | ⟨q, -, -, hnl⟩
      · exact hτnoP _ (List.get_mem _ k) hk
      · exact hnl hτlog
  have hυnoP : ¬ ∃ q ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.2 i,
      q.1 = p.1 := by
    rintro ⟨q, hq, hq1⟩
    rcases (E.hυmem i q).mp hq with ⟨r, -, rfl⟩ | ⟨-, rfl⟩
    · exact hτnoP _ (List.get_mem _ r) hq1
    · exact hna (hq1 ▸ (E.hactj _).mpr ⟨i, _, rfl⟩)
  have hnp : ¬ pdLifePending S γ p.1 (H' i p) false j.succ := fun h => hυnoP (hpendυ.mp h)
  have hbυ := hbornυ.mp (E.hτsub _ hτlog)
  have hb' : (∃ a, (H' i p).1.1 = some a ∧ a < j.succ) ∨
      ∃ m, m < j.succ ∧ IsActiveAt γ p.1 m := by
    rcases hbυ with ⟨m, hm, hact⟩ | h
    · exact Or.inr ⟨m, lt_of_le_of_ne hm (fun h => hnactS (h ▸ hact)), hact⟩
    · exact Or.inl h
  have dead := dead_from S γ p.1 (H' i p) j.succ hnp hnactS hb'
  have hnoborn : p.1 ∉ (g.2 i).1 := fun h => E.hborn i _ h hlog
  have hnodeath : ¬ ∃ r ∈ g.1 i, ((σ.1.2.2 i).get r).1 = p.1 :=
    fun ⟨r, _, hr⟩ => hmem _ (List.get_mem _ r) hr
  have hnopend : ¬ ∃ q ∈ σ.1.2.2 i, q.1 = p.1 := fun ⟨q, hq, h⟩ => hmem q hq h
  have hlt : ∀ m : Fin (pathLength S.x + 1), j.succ ≤ m → j.castSucc < m :=
    fun m hm => lt_of_lt_of_le Fin.castSucc_lt_succ hm
  rcases hR.deadRec i p.1 p.2 hlog hmem hna with ⟨m₀, hm₀, hact₀⟩ | ⟨a, c', hac, hc, hl, hno⟩
  · have hA : (pdLifeActive S γ p.1).Nonempty := ⟨m₀, (mem_active_iff S γ p.1 m₀).mpr hact₀⟩
    have hωact : IsActiveAt γ p.1 ((pdLifeActive S γ p.1).max' hA) :=
      (Finset.mem_filter.mp (Finset.max'_mem _ hA)).2
    have hω : (pdLifeActive S γ p.1).max' hA < j.castSucc := by
      have h1 : (pdLifeActive S γ p.1).max' hA < j.succ :=
        not_le.mp (fun h => dead.1 _ h hωact)
      exact lt_of_le_of_ne ((fin_lt_succ_iff' j _).mp h1) (fun h => hna (h ▸ hωact))
    have hvalid := mkLife_active S γ p.1 hA (active_lines_of_life S γ p.1 (H' i p))
      (H' i p).1.1 none (birth_ok S γ p.1 (H' i p) hA) (fun c h => by simp at h)
    obtain ⟨hAJ, hB, -, -⟩ := life_active_facts S γ p.1 (H' i p) hA
    refine ⟨⟨_, hvalid⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [pend_active_iff S γ p.1 _ hA]
      refine ⟨fun h => ?_, fun h => absurd h hnopend⟩
      rcases h.2.2 with ⟨c, hc, -⟩ | hω'
      · simp at hc
      · exact absurd (lt_trans hω' hω) (lt_irrefl _)
    · intro q hq hq1; exact absurd hq1 (hmem q hq)
    · intro _ _ _; exact hlog
    · intro _; exact Or.inl ⟨m₀, le_of_lt hm₀, hact₀⟩
    · constructor
      · intro h
        exact absurd (lt_trans (lt_of_lt_of_le (hB _ h).1 (hAJ _ hact₀).1) hm₀) (lt_irrefl _)
      · intro h; exact absurd h hnoborn
    · exact ⟨fun h => by simp at h, fun h => absurd h hnodeath⟩
    · intro m hm
      refine ⟨Iff.rfl, ⟨fun h => by simp at h, fun h => absurd (dead.2.1 m h) (not_lt.mpr hm)⟩,
        ⟨fun h => ?_, fun h => absurd h (dead.2.2.2 m hm)⟩⟩
      rw [pend_active_iff S γ p.1 _ hA] at h
      rcases h.2.2 with ⟨c, hc, -⟩ | hω'
      · simp at hc
      · exact absurd (lt_trans hω' (lt_trans hω (hlt m hm))) (lt_irrefl _)
  · have hA : ¬ (pdLifeActive S γ p.1).Nonempty := by
      rintro ⟨m, hm⟩
      have hact := (mem_active_iff S γ p.1 m).mp hm
      by_cases h : m ≤ j.castSucc
      · exact hno m h hact
      · exact dead.1 m (by rw [← not_lt, fin_lt_succ_iff']; exact h) hact
    refine ⟨⟨_, mkLife_inactive_some S γ p.1 hA a c' hac hl⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [pend_inactive_iff S γ p.1 _ hA]
      constructor
      · rintro ⟨a', c'', h, -, h2⟩
        simp only [Prod.mk.injEq, Option.some.injEq] at h
        rw [← h.2] at h2
        exact absurd hc (not_lt.mpr h2)
      · intro h; exact absurd h hnopend
    · intro q hq hq1; exact absurd hq1 (hmem q hq)
    · intro _ _ _; exact hlog
    · intro _; exact Or.inr ⟨a, rfl, lt_trans hac hc⟩
    · exact ⟨fun h => absurd (Option.some.inj h) (ne_of_lt (lt_trans hac hc)),
        fun h => absurd h hnoborn⟩
    · exact ⟨fun h => absurd (Option.some.inj h) (ne_of_lt hc), fun h => absurd h hnodeath⟩
    · intro m hm
      have hcm : c' < m := lt_trans hc (hlt m hm)
      refine ⟨⟨fun h => absurd (Option.some.inj h) (ne_of_lt (lt_trans hac hcm)),
          fun h => absurd (dead.2.2.1 m h) (not_lt.mpr hm)⟩,
        ⟨fun h => absurd (Option.some.inj h) (ne_of_lt hcm),
          fun h => absurd (dead.2.1 m h) (not_lt.mpr hm)⟩,
        ⟨fun h => ?_, fun h => absurd h (dead.2.2.2 m hm)⟩⟩
      rw [pend_inactive_iff S γ p.1 _ hA] at h
      obtain ⟨a', c'', h, -, h2⟩ := h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      rw [← h.2] at h2
      exact absurd hcm (not_lt.mpr h2)

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
