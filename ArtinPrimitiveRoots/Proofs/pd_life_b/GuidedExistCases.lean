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

theorem case_deleted (hR : ExistRec F S γ j.castSucc σ)
    (hS : StepFacts F S w γ j σ g τ π π' c)
    (E : StepEnv F S γ j σ g τ π π' c H') (i : Fin K) (p : primeBand S.x (F.a i))
    (q : Particle) (hq : q ∈ σ.1.2.2 i) (hq1 : q.1 = p.1) (r : Fin (σ.1.2.2 i).length)
    (hr : (σ.1.2.2 i).get r = q) (hrD : r ∈ g.1 i) :
    ∃ e : PrimeLife S γ p.1, PrimeOK F S γ j.castSucc σ g i p e ∧
      FutPrime S γ j.succ p.1 e (H' i p) := by
  obtain ⟨hpendυ, -, hbornυ⟩ := prime_next_facts F S γ j σ g τ π π' c H' E i p
  have hlog : p.1 ∈ σ.2.map Prod.snd := hq1 ▸ hR.memLog i q hq
  have hna : ¬ IsActiveAt γ p.1 j.castSucc := hq1 ▸ (hR.memRec i q hq).1
  have huniq : ∀ q' ∈ σ.1.2.2 i, q'.1 = p.1 → q' = q := by
    intro q' hq' hq'1
    obtain ⟨r', hr'⟩ := List.mem_iff_get.mp hq'
    have : r' = r := index_inj_of_nodup _ (hR.memNodup i) r' r (by rw [hr', hr, hq'1, hq1])
    rw [← hr', ← hr, this]
  have hτlog : p.1 ∈ τ.2.map Prod.snd := (E.hτlog _).mpr (Or.inl hlog)
  have hτnoP : ∀ q' ∈ τ.1.2.2 i, q'.1 ≠ p.1 := by
    intro q' hq' hq'1
    rcases (E.hτmem i q').mp hq' with ⟨r', hr'D, hr'⟩ | ⟨hb, -⟩
    · have : q' = q := huniq q' (hr' ▸ List.get_mem _ r') hq'1
      have hrr : r' = r := index_inj_of_nodup _ (hR.memNodup i) r' r (by rw [hr', hr, this])
      exact hr'D (hrr ▸ hrD)
    · exact E.hborn i _ hb (hq'1 ▸ hlog)
  have hnactS : ¬ IsActiveAt γ p.1 j.succ := by
    intro h
    obtain ⟨i', y, hy⟩ := (E.hactj1 _).mp h
    rw [E.hLy] at hy
    split_ifs at hy with hyJ
    · exact hna ((E.hactj _).mpr ⟨i', y, hy⟩)
    · have hii := E.hgroup i' i _ (hy ▸ E.hlabelBand i') p.2
      subst hii
      rcases E.hlabel i' _ hy with ⟨k, -, hk⟩ | ⟨q', -, -, hnl⟩
      · exact hτnoP _ (List.get_mem _ k) hk
      · exact hnl hτlog
  have hυnoP : ¬ ∃ q' ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.2 i,
      q'.1 = p.1 := by
    rintro ⟨q', hq', hq'1⟩
    rcases (E.hυmem i q').mp hq' with ⟨r', -, rfl⟩ | ⟨-, rfl⟩
    · exact hτnoP _ (List.get_mem _ r') hq'1
    · exact hna (hq'1 ▸ (E.hactj _).mpr ⟨i, _, rfl⟩)
  have hnp : ¬ pdLifePending S γ p.1 (H' i p) false j.succ := fun h => hυnoP (hpendυ.mp h)
  have hbυ := hbornυ.mp (E.hτsub _ hτlog)
  have hb' : (∃ a, (H' i p).1.1 = some a ∧ a < j.succ) ∨
      ∃ m, m < j.succ ∧ IsActiveAt γ p.1 m := by
    rcases hbυ with ⟨m, hm, hact⟩ | h
    · exact Or.inr ⟨m, lt_of_le_of_ne hm (fun h => hnactS (h ▸ hact)), hact⟩
    · exact Or.inl h
  have dead := dead_from S γ p.1 (H' i p) j.succ hnp hnactS hb'
  have hlt : ∀ m : Fin (pathLength S.x + 1), j.succ ≤ m → j.castSucc < m :=
    fun m hm => lt_of_lt_of_le Fin.castSucc_lt_succ hm
  have hhit : q.2 = (projLine p.1 (γ j.castSucc).1).val := by
    have h := (Finset.mem_filter.mp (hS.guard i hrD)).2
    unfold particleHits at h
    rw [hr] at h; rw [h, E.hz, hq1]
  have hnoborn : p.1 ∉ (g.2 i).1 := fun h => E.hborn i _ h hlog
  have hdeath : ∃ r ∈ g.1 i, ((σ.1.2.2 i).get r).1 = p.1 := ⟨r, hrD, by rw [hr, hq1]⟩
  rcases (hR.memRec i q hq).2 with ⟨⟨a, ha, hla⟩, hno⟩ | ⟨m₀, hm₀, hact₀, hl₀⟩
  · rw [hq1] at hla hno
    have hA : ¬ (pdLifeActive S γ p.1).Nonempty := by
      rintro ⟨m, hm⟩
      have hact := (mem_active_iff S γ p.1 m).mp hm
      by_cases h : m ≤ j.castSucc
      · exact hno m h hact
      · exact dead.1 m (by rw [← not_lt, fin_lt_succ_iff']; exact h) hact
    have hline : projLine p.1 (γ j.castSucc).1 = projLine p.1 (γ a).1 :=
      Fin.ext (by rw [← hhit, hla])
    refine ⟨⟨_, mkLife_inactive_some S γ p.1 hA a _ ha hline⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [pend_inactive_iff S γ p.1 _ hA]
      exact ⟨fun _ => ⟨q, hq, hq1⟩, fun _ => ⟨a, _, rfl, ha, le_rfl⟩⟩
    · intro q' hq' hq'1
      rw [huniq q' hq' hq'1]
      show q.2 = (lifeLine S γ p.1 (some a, some j.castSucc)).val
      rw [lifeLine_inactive S γ p.1 a _ hA, ← hla]
    · intro _ _ _; exact hlog
    · intro _; exact Or.inr ⟨a, rfl, ha⟩
    · exact ⟨fun h => absurd (Option.some.inj h) (ne_of_lt ha), fun h => absurd h hnoborn⟩
    · exact ⟨fun _ => hdeath, fun _ => rfl⟩
    · intro m hm
      refine ⟨⟨fun h => absurd (Option.some.inj h) (ne_of_lt (lt_trans ha (hlt m hm))),
          fun h => absurd (dead.2.2.1 m h) (not_lt.mpr hm)⟩,
        ⟨fun h => absurd (Option.some.inj h) (ne_of_lt (hlt m hm)),
          fun h => absurd (dead.2.1 m h) (not_lt.mpr hm)⟩,
        ⟨fun h => ?_, fun h => absurd h (dead.2.2.2 m hm)⟩⟩
      rw [pend_inactive_iff S γ p.1 _ hA] at h
      obtain ⟨a', c'', h, -, h2⟩ := h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      rw [← h.2] at h2
      exact absurd (hlt m hm) (not_lt.mpr h2)
  · rw [hq1] at hact₀ hl₀
    have hA : (pdLifeActive S γ p.1).Nonempty := ⟨m₀, (mem_active_iff S γ p.1 m₀).mpr hact₀⟩
    have hαact : IsActiveAt γ p.1 ((pdLifeActive S γ p.1).min' hA) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
    have hωact : IsActiveAt γ p.1 ((pdLifeActive S γ p.1).max' hA) :=
      (Finset.mem_filter.mp (Finset.max'_mem _ hA)).2
    have hacts : ∀ m, IsActiveAt γ p.1 m → m < j.castSucc := by
      intro m hm
      have h1 : m < j.succ := not_le.mp (fun h => dead.1 _ h hm)
      exact lt_of_le_of_ne ((fin_lt_succ_iff' j _).mp h1) (fun h => hna (h ▸ hm))
    have hlines := active_lines_of_life S γ p.1 (H' i p)
    have hvalid := mkLife_active S γ p.1 hA hlines none (some j.castSucc)
      (fun a h => by simp at h)
      (fun c' hc' => by
        cases hc'
        exact ⟨hacts, m₀, hact₀, Fin.ext (by rw [← hhit, hl₀])⟩)
    refine ⟨⟨_, hvalid⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [pend_active_iff S γ p.1 _ hA]
      refine ⟨fun _ => ⟨q, hq, hq1⟩, fun _ => ⟨hna, Or.inr ?_, Or.inl ⟨_, rfl, le_rfl⟩⟩⟩
      exact lt_of_le_of_lt (Finset.min'_le _ _ ((mem_active_iff S γ p.1 m₀).mpr hact₀)) hm₀
    · intro q' hq' hq'1
      rw [huniq q' hq' hq'1]
      show q.2 = (lifeLine S γ p.1 (none, some j.castSucc)).val
      rw [lifeLine_active S γ p.1 _ hA, ← hl₀, hlines m₀ _ hact₀ hαact]
    · intro a h; simp at h
    · intro _; exact Or.inl ⟨m₀, le_of_lt hm₀, hact₀⟩
    · exact ⟨fun h => by simp at h, fun h => absurd h hnoborn⟩
    · exact ⟨fun _ => hdeath, fun _ => rfl⟩
    · intro m hm
      refine ⟨⟨fun h => by simp at h, fun h => absurd (dead.2.2.1 m h) (not_lt.mpr hm)⟩,
        ⟨fun h => absurd (Option.some.inj h) (ne_of_lt (hlt m hm)),
          fun h => absurd (dead.2.1 m h) (not_lt.mpr hm)⟩,
        ⟨fun h => ?_, fun h => absurd h (dead.2.2.2 m hm)⟩⟩
      rw [pend_active_iff S γ p.1 _ hA] at h
      rcases h.2.2 with ⟨c', hc', hmc⟩ | hω'
      · simp only [Option.some.injEq] at hc'
        rw [← hc'] at hmc
        exact absurd (hlt m hm) (not_lt.mpr hmc)
      · exact absurd (lt_trans hω' (lt_trans (hacts _ hωact) (hlt m hm))) (lt_irrefl _)

theorem case_unborn (hR : ExistRec F S γ j.castSucc σ)
    (E : StepEnv F S γ j σ g τ π π' c H') (i : Fin K) (p : primeBand S.x (F.a i))
    (hlog : p.1 ∉ σ.2.map Prod.snd) (hnb : p.1 ∉ (g.2 i).1) :
    ∃ e : PrimeLife S γ p.1, PrimeOK F S γ j.castSucc σ g i p e ∧
      FutPrime S γ j.succ p.1 e (H' i p) := by
  obtain ⟨-, -, hbornυ⟩ := prime_next_facts F S γ j σ g τ π π' c H' E i p
  have hτlog : p.1 ∉ τ.2.map Prod.snd := by
    intro h
    rcases (E.hτlog _).mp h with h | ⟨i', hb⟩
    · exact hlog h
    · have hii := E.hgroup i' i _ (E.hbornBand i' _ hb) p.2
      subst hii
      exact hnb hb
  have hnoEarly : ∀ m, m ≤ j.castSucc → ¬ IsActiveAt γ p.1 m :=
    fun m hm hact => hlog (hR.actLog _ m hm hact)
  have hnopend : ¬ ∃ q ∈ σ.1.2.2 i, q.1 = p.1 :=
    fun ⟨q, hq, hq1⟩ => hlog (hq1 ▸ hR.memLog i q hq)
  have hnodeath : ¬ ∃ r ∈ g.1 i, ((σ.1.2.2 i).get r).1 = p.1 :=
    fun ⟨r, _, hr⟩ => hnopend ⟨_, List.get_mem _ r, hr⟩
  have hlt : ∀ m : Fin (pathLength S.x + 1), j.succ ≤ m → j.castSucc < m :=
    fun m hm => lt_of_lt_of_le Fin.castSucc_lt_succ hm
  have hlateAct : ∀ m, IsActiveAt γ p.1 m → j.castSucc < m := by
    intro m hm
    by_contra h
    exact hnoEarly m (not_lt.mp h) hm
  -- an early birth forces a fresh entry at `j+1`
  have hfresh : (∃ x, (H' i p).1.1 = some x ∧ x ≤ j.castSucc) → IsActiveAt γ p.1 j.succ := by
    rintro ⟨x, hx, hxj⟩
    have hυ := hbornυ.mpr (Or.inr ⟨x, hx, (fin_lt_succ_iff' j x).mpr hxj⟩)
    rcases (E.hυlog _).mp hυ with h | ⟨i', q', hc', hq'⟩
    · exact absurd h hτlog
    · have hii := E.hgroup i' i _ (hq' ▸ q'.2) p.2
      subst hii
      refine (E.hactj1 _).mpr ⟨i', lastSlot S.x, ?_⟩
      rw [E.hLy, if_neg (by simp [lastSlot])]
      unfold edgeNewLabel; rw [hc']; exact hq'
  -- generic facts for the conditions at `j`
  have hpendC : ∀ e : PrimeLife S γ p.1,
      (∀ x, e.1.1 = some x → j.castSucc < x) → ¬ pdLifePending S γ p.1 e false j.castSucc := by
    intro e he hp
    by_cases hA : (pdLifeActive S γ p.1).Nonempty
    · rw [pend_active_iff S γ p.1 e hA] at hp
      rcases hp.2.1 with ⟨x, hx, hxj⟩ | hα
      · exact absurd (lt_trans hxj (he x hx)) (lt_irrefl _)
      · exact absurd (hlateAct _ (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2) (not_lt.mpr
          (le_of_lt hα))
    · rw [pend_inactive_iff S γ p.1 e hA] at hp
      obtain ⟨x, y, hxy, hx, -⟩ := hp
      have := he x (by rw [hxy])
      exact absurd (lt_trans hx this) (lt_irrefl _)
  by_cases h : ∃ x, (H' i p).1.1 = some x ∧ x ≤ j.castSucc
  · have hact1 := hfresh h
    have hA : (pdLifeActive S γ p.1).Nonempty :=
      ⟨_, (mem_active_iff S γ p.1 _).mpr hact1⟩
    have hαact : IsActiveAt γ p.1 ((pdLifeActive S γ p.1).min' hA) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
    have hα : (pdLifeActive S γ p.1).min' hA ≤ j.succ :=
      Finset.min'_le _ _ ((mem_active_iff S γ p.1 _).mpr hact1)
    have hvalid := mkLife_active S γ p.1 hA (active_lines_of_life S γ p.1 (H' i p))
      none (H' i p).1.2 (fun a h => by simp at h) (death_ok S γ p.1 (H' i p) hA)
    obtain ⟨hAJ, hB, hC, -⟩ := life_active_facts S γ p.1 (H' i p) hA
    obtain ⟨x, hx, hxj⟩ := h
    refine ⟨⟨_, hvalid⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact ⟨fun hp => absurd hp (hpendC ⟨_, hvalid⟩ (fun x h => by simp at h)),
        fun h => absurd h hnopend⟩
    · intro q hq hq1; exact absurd ⟨q, hq, hq1⟩ hnopend
    · intro a h; simp at h
    · intro h; exact absurd h hlog
    · exact ⟨fun h => by simp at h, fun h => absurd h hnb⟩
    · constructor
      · intro hc
        exact absurd (lt_trans (hlateAct _ hαact) (lt_of_le_of_lt (hAJ _ hαact).2 (hC _ hc)))
          (lt_irrefl _)
      · intro h; exact absurd h hnodeath
    · intro m hm
      refine ⟨⟨fun h => by simp at h, fun h' => ?_⟩, Iff.rfl, ?_⟩
      · rw [hx] at h'
        simp only [Option.some.injEq] at h'
        rw [← h'] at hm
        exact absurd (hlt _ hm) (not_lt.mpr hxj)
      · rw [pend_active_iff S γ p.1 _ hA, pend_active_iff S γ p.1 _ hA]
        constructor
        · rintro ⟨h1, -, h3⟩
          exact ⟨h1, Or.inl ⟨x, hx, lt_of_le_of_lt hxj (hlt m hm)⟩, h3⟩
        · rintro ⟨h1, -, h3⟩
          refine ⟨h1, Or.inr ?_, h3⟩
          exact lt_of_le_of_lt hα (lt_of_le_of_ne hm (fun h => h1 (h ▸ hact1)))
  · push_neg at h
    have hlate : ∀ x, (H' i p).1.1 = some x → j.castSucc < x := h
    refine ⟨H' i p, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun m _ => ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩⟩
    · exact ⟨fun hp => absurd hp (hpendC _ hlate), fun h => absurd h hnopend⟩
    · intro q hq hq1; exact absurd ⟨q, hq, hq1⟩ hnopend
    · intro a ha hlt'; exact absurd (lt_trans hlt' (hlate a ha)) (lt_irrefl _)
    · intro h; exact absurd h hlog
    · exact ⟨fun h' => absurd (hlate _ h') (lt_irrefl _), fun h' => absurd h' hnb⟩
    · constructor
      · intro hc
        by_cases hA : (pdLifeActive S γ p.1).Nonempty
        · obtain ⟨hAJ, -, hC, -⟩ := life_active_facts S γ p.1 (H' i p) hA
          have hαact : IsActiveAt γ p.1 ((pdLifeActive S γ p.1).min' hA) :=
            (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
          exact absurd (lt_trans (hlateAct _ hαact) (lt_of_le_of_lt (hAJ _ hαact).2 (hC _ hc)))
            (lt_irrefl _)
        · rcases life_inactive_facts S γ p.1 (H' i p) hA with he | ⟨a, c', he, hac, -⟩
          · rw [he] at hc; simp at hc
          · have ha := hlate a (by rw [he])
            rw [he] at hc
            simp only [Option.some.injEq] at hc
            rw [hc] at hac
            exact absurd (lt_trans ha hac) (lt_irrefl _)
      · intro h; exact absurd h hnodeath

/-- The surviving particle of `p` after the ghost of visit `j`: either promoted at the edge or
kept in memory. -/
theorem survivor_alive (E : StepEnv F S γ j σ g τ π π' c H') (i : Fin K)
    (p : primeBand S.x (F.a i)) (q : Particle) (hq : q ∈ τ.1.2.2 i) (hq1 : q.1 = p.1) :
    (IsActiveAt γ p.1 j.succ ∧ q.2 = (projLine p.1 (γ j.succ).1).val) ∨
      q ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.2 i := by
  obtain ⟨r, hr⟩ := List.mem_iff_get.mp hq
  by_cases hprom : (c i).2 = Sum.inl r
  · left
    refine ⟨(E.hactj1 _).mpr ⟨i, lastSlot S.x, ?_⟩, ?_⟩
    · rw [E.hLy, if_neg (by simp [lastSlot])]
      unfold edgeNewLabel; rw [hprom]; exact (congrArg Prod.fst hr).trans hq1
    · have := E.hprom i r hprom
      rw [hr] at this; rw [this, hq1]
  · right
    exact (E.hυmem i q).mpr (Or.inl ⟨r, hprom, hr⟩)

/-- Ghost-born-type construction for a surviving particle anchored at a visit `a ≤ j`. -/
theorem alive_ghost (E : StepEnv F S γ j σ g τ π π' c H') (i : Fin K)
    (p : primeBand S.x (F.a i)) (q : Particle) (hq : q ∈ τ.1.2.2 i) (hq1 : q.1 = p.1)
    (a : Fin (pathLength S.x + 1)) (ha : a ≤ j.castSucc)
    (hla : (projLine p.1 (γ a).1).val = q.2)
    (hno : ∀ m, m ≤ j.castSucc → ¬ IsActiveAt γ p.1 m) :
    ∃ e : PrimeLife S γ p.1, e.1 = (some a, (H' i p).1.2) ∧
      (pdLifePending S γ p.1 e false j.castSucc ↔ a < j.castSucc) ∧
      (lifeLine S γ p.1 e.1).val = q.2 ∧ e.1.2 ≠ some j.castSucc ∧
      FutPrime S γ j.succ p.1 e (H' i p) := by
  obtain ⟨hpendυ, hanchυ, -⟩ := prime_next_facts F S γ j σ g τ π π' c H' E i p
  have hlt : ∀ m : Fin (pathLength S.x + 1), j.succ ≤ m → j.castSucc < m :=
    fun m hm => lt_of_lt_of_le Fin.castSucc_lt_succ hm
  have hlate : ∀ m, IsActiveAt γ p.1 m → j.castSucc < m := by
    intro m hm; by_contra h; exact hno m (not_lt.mp h) hm
  have hsurv := survivor_alive F S γ j σ g τ π π' c H' E i p q hq hq1
  have halive' : pdLifePending S γ p.1 (H' i p) false j.succ ∨ IsActiveAt γ p.1 j.succ := by
    rcases hsurv with ⟨h, -⟩ | h
    · exact Or.inr h
    · exact Or.inl (hpendυ.mpr ⟨q, h, hq1⟩)
  have alive := alive_at S γ p.1 (H' i p) j.succ halive'
  by_cases hA : (pdLifeActive S γ p.1).Nonempty
  · have hαact : IsActiveAt γ p.1 ((pdLifeActive S γ p.1).min' hA) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
    have hωact : IsActiveAt γ p.1 ((pdLifeActive S γ p.1).max' hA) :=
      (Finset.mem_filter.mp (Finset.max'_mem _ hA)).2
    have hlines := active_lines_of_life S γ p.1 (H' i p)
    -- the anchor is the active line
    have hlineα : (projLine p.1 (γ ((pdLifeActive S γ p.1).min' hA)).1).val = q.2 := by
      rcases hsurv with ⟨h1, h2⟩ | h
      · rw [h2, hlines _ _ hαact h1]
      · rw [hanchυ q h hq1, lifeLine_active S γ p.1 _ hA]
    have hvalid := mkLife_active S γ p.1 hA hlines (some a) (H' i p).1.2
      (fun a' h => by
        cases h
        exact ⟨fun m hm => lt_of_le_of_lt ha (hlate m hm), _, hαact,
          Fin.ext (by rw [hla, hlineα])⟩)
      (death_ok S γ p.1 (H' i p) hA)
    have hjω : j.castSucc < (pdLifeActive S γ p.1).max' hA := hlate _ hωact
    refine ⟨⟨_, hvalid⟩, rfl, ?_, ?_, ?_, ?_⟩
    · rw [pend_active_iff S γ p.1 _ hA]
      constructor
      · rintro ⟨-, hb, -⟩
        rcases hb with ⟨a', ha', h'⟩ | hα
        · simp only [Option.some.injEq] at ha'; rw [ha']; exact h'
        · exact absurd (hlate _ hαact) (not_lt.mpr (le_of_lt hα))
      · intro h
        exact ⟨hno _ le_rfl, Or.inl ⟨a, rfl, h⟩, Or.inr hjω⟩
    · show (lifeLine S γ p.1 (some a, (H' i p).1.2)).val = q.2
      rw [lifeLine_active S γ p.1 _ hA]; exact hlineα
    · intro h
      exact absurd (alive.2 _ h) (not_le.mpr Fin.castSucc_lt_succ)
    · intro m hm
      refine ⟨⟨fun h => ?_, fun h => absurd (alive.1 m h) (not_lt.mpr hm)⟩, Iff.rfl, ?_⟩
      · simp only [Option.some.injEq] at h
        rw [← h] at hm
        exact absurd (lt_of_le_of_lt ha (hlt _ hm)) (lt_irrefl _)
      · rw [pend_active_iff S γ p.1 _ hA, pend_active_iff S γ p.1 _ hA]
        have hborn' : ¬ IsActiveAt γ p.1 m →
            (∃ x, (H' i p).1.1 = some x ∧ x < m) ∨ (pdLifeActive S γ p.1).min' hA < m := by
          intro hnm
          cases hb : (H' i p).1.1 with
          | some x => exact Or.inl ⟨x, rfl, lt_of_lt_of_le (alive.1 x hb) hm⟩
          | none =>
            right
            rcases halive' with hp | hact
            · rw [pend_active_iff S γ p.1 _ hA] at hp
              rcases hp.2.1 with ⟨x, hx, -⟩ | hα
              · rw [hb] at hx; simp at hx
              · exact lt_of_lt_of_le hα hm
            · exact lt_of_le_of_lt (Finset.min'_le _ _ ((mem_active_iff S γ p.1 _).mpr hact))
                (lt_of_le_of_ne hm (fun h => hnm (h ▸ hact)))
        constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨h1, hborn' h1, h3⟩
        · rintro ⟨h1, -, h3⟩
          exact ⟨h1, Or.inl ⟨a, rfl, lt_of_le_of_lt ha (hlt m hm)⟩, h3⟩
  · -- no active visit: the particle stays in memory and is deleted later
    have hkept : q ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.2 i := by
      rcases hsurv with ⟨h1, -⟩ | h
      · exact absurd ⟨_, (mem_active_iff S γ p.1 _).mpr h1⟩ hA
      · exact h
    have hpS := hpendυ.mpr ⟨q, hkept, hq1⟩
    rw [pend_inactive_iff S γ p.1 _ hA] at hpS
    obtain ⟨a', c', he', ha', hc'⟩ := hpS
    have hanc := hanchυ q hkept hq1
    rw [he', lifeLine_inactive S γ p.1 a' _ hA] at hanc
    have hlc : projLine p.1 (γ c').1 = projLine p.1 (γ a').1 := by
      rcases life_inactive_facts S γ p.1 (H' i p) hA with h | ⟨a'', c'', h, -, hl⟩
      · rw [h] at he'; simp at he'
      · rw [h] at he'
        simp only [Prod.mk.injEq, Option.some.injEq] at he'
        rw [← he'.1, ← he'.2]; exact hl
    have hac : a < c' := lt_of_le_of_lt ha (lt_of_lt_of_le Fin.castSucc_lt_succ hc')
    have hvalid := mkLife_inactive_some S γ p.1 hA a c' hac
      (Fin.ext (by rw [hlc, ← hanc]; exact hla.symm))
    have he2 : (H' i p).1.2 = some c' := by rw [he']
    refine ⟨⟨_, hvalid⟩, by rw [he2], ?_, ?_, ?_, ?_⟩
    · rw [pend_inactive_iff S γ p.1 _ hA]
      constructor
      · rintro ⟨x, y, h, hx, -⟩
        simp only [Prod.mk.injEq, Option.some.injEq] at h
        rw [h.1]; exact hx
      · intro h
        exact ⟨a, c', rfl, h, le_of_lt (lt_of_lt_of_le Fin.castSucc_lt_succ hc')⟩
    · show (lifeLine S γ p.1 (some a, some c')).val = q.2
      rw [lifeLine_inactive S γ p.1 a _ hA, hla]
    · intro h
      simp only [Option.some.injEq] at h
      rw [h] at hc'
      exact absurd hc' (not_le.mpr Fin.castSucc_lt_succ)
    · intro m hm
      refine ⟨⟨fun h => ?_, fun h => absurd (alive.1 m h) (not_lt.mpr hm)⟩, ?_, ?_⟩
      · simp only [Option.some.injEq] at h
        rw [← h] at hm
        exact absurd (lt_of_le_of_lt ha (hlt _ hm)) (lt_irrefl _)
      · rw [he2]
      · rw [pend_inactive_iff S γ p.1 _ hA, pend_inactive_iff S γ p.1 _ hA, he']
        constructor
        · rintro ⟨x, y, h, -, h2⟩
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          exact ⟨a', c', rfl, lt_of_lt_of_le ha' hm, h.2 ▸ h2⟩
        · rintro ⟨x, y, h, -, h2⟩
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          exact ⟨a, c', rfl, lt_of_le_of_lt ha (hlt m hm), h.2 ▸ h2⟩

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
