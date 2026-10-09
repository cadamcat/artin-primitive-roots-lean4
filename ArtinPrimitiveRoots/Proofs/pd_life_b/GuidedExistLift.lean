import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedLifeChar

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- The per-prime conditions at visit `j` that make `H` a guiding life assignment there. -/
structure PrimeOK {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (j : Fin (pathLength S.x + 1)) (σ : LogPoint S.x K) (g : GhostTraceChoice F S σ)
    (i : Fin K) (p : primeBand S.x (F.a i)) (e : PrimeLife S γ p.1) : Prop where
  pend : pdLifePending S γ p.1 e false j ↔ ∃ q ∈ σ.1.2.2 i, q.1 = p.1
  anchor : ∀ q ∈ σ.1.2.2 i, q.1 = p.1 → q.2 = (lifeLine S γ p.1 e.1).val
  bornLog : ∀ a, e.1.1 = some a → a < j → p.1 ∈ σ.2.map Prod.snd
  logBorn : p.1 ∈ σ.2.map Prod.snd →
    (∃ m, m ≤ j ∧ IsActiveAt γ p.1 m) ∨ ∃ a, e.1.1 = some a ∧ a < j
  birthAt : e.1.1 = some j ↔ p.1 ∈ (g.2 i).1
  deathAt : e.1.2 = some j ↔ ∃ r ∈ g.1 i, ((σ.1.2.2 i).get r).1 = p.1

theorem lift_primeOK {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x + 1)) (σ : LogPoint S.x K)
    (hR : ExistRec F S γ j σ) (g : GhostTraceChoice F S σ)
    (hok : ∀ i p, PrimeOK F S γ j σ g i p (H i p)) :
    IsLifeState F S γ H j σ ∧ GhostGuided F S γ H j σ g := by
  have hgroup : ∀ i i' p, p ∈ primeBand S.x (F.a i) → p ∈ primeBand S.x (F.a i') → i = i' := by
    intro i i' p h1 h2
    by_contra hne
    exact Finset.disjoint_left.mp (hBands i i' hne) h1 h2
  refine ⟨⟨hR.pos, hR.memNodup, ?_, hR.logNodup, ?_⟩, ?_⟩
  · intro i q
    constructor
    · intro hq
      have hp := hR.memBand i q hq
      exact ⟨hp, (hok i ⟨q.1, hp⟩).pend.mpr ⟨q, hq, rfl⟩,
        (hok i ⟨q.1, hp⟩).anchor q hq rfl⟩
    · rintro ⟨hp, hpend, hanc⟩
      obtain ⟨q', hq', hq'1⟩ := (hok i ⟨q.1, hp⟩).pend.mp hpend
      have h2 := (hok i ⟨q.1, hp⟩).anchor q' hq' hq'1
      have : q' = q := Prod.ext hq'1 (h2.trans hanc.symm)
      rw [← this]; exact hq'
  · intro p
    constructor
    · intro hp
      obtain ⟨i, hpi⟩ := hR.logBand p hp
      rcases (hok i ⟨p, hpi⟩).logBorn hp with ⟨m, hm, hact⟩ | ⟨a, ha, hlt⟩
      · exact Or.inl ⟨m, hm, hact⟩
      · exact Or.inr ⟨i, a, hlt, hpi, ha⟩
    · rintro (⟨m, hm, hact⟩ | ⟨i, a, ha, hpi, hb⟩)
      · exact hR.actLog p m hm hact
      · exact (hok i ⟨p, hpi⟩).bornLog a hb ha
  · intro i
    constructor
    · ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hr
        have hp := hR.memBand i _ (List.get_mem _ r)
        exact ⟨hp, (hok i ⟨_, hp⟩).deathAt.mpr ⟨r, hr, rfl⟩⟩
      · rintro ⟨hp, hd⟩
        obtain ⟨r', hr', hr'1⟩ := (hok i ⟨_, hp⟩).deathAt.mp hd
        have : r' = r := index_inj_of_nodup _ (hR.memNodup i) r' r hr'1
        rw [← this]; exact hr'
    · ext p
      simp only [Finset.mem_filter]
      constructor
      · intro hp
        have hpb : p ∈ primeBand S.x (F.a i) := Finset.mem_powerset.mp (g.2 i).2 hp
        exact ⟨hpb, hpb, (hok i ⟨p, hpb⟩).birthAt.mpr hp⟩
      · rintro ⟨-, hpb, hb⟩
        exact (hok i ⟨p, hpb⟩).birthAt.mp hb

/-- Agreement of two assignments on all data used by guidance from visit `m0` on. -/
def FutAgree {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) (m0 : ℕ)
    (H H' : PDLifeAssignment F S γ) : Prop :=
  ∀ i (p : primeBand S.x (F.a i)) (m : Fin (pathLength S.x + 1)), m0 ≤ m.val →
    ((H i p).1.1 = some m ↔ (H' i p).1.1 = some m) ∧
      ((H i p).1.2 = some m ↔ (H' i p).1.2 = some m) ∧
      (pdLifePending S γ p.1 (H i p) false m ↔ pdLifePending S γ p.1 (H' i p) false m)

theorem ghostGuided_congr {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H H' : PDLifeAssignment F S γ) (j : Fin (pathLength S.x + 1)) (σ : LogPoint S.x K)
    (g : GhostTraceChoice F S σ) (hF : FutAgree F S γ j.val H H')
    (h : GhostGuided F S γ H' j σ g) : GhostGuided F S γ H j σ g := by
  have hdel : ∀ i p, lifeDeletedAt F S γ H i p j ↔ lifeDeletedAt F S γ H' i p j := by
    intro i p
    exact ⟨fun ⟨hp, h⟩ => ⟨hp, (hF i ⟨p, hp⟩ j le_rfl).2.1.mp h⟩,
      fun ⟨hp, h⟩ => ⟨hp, (hF i ⟨p, hp⟩ j le_rfl).2.1.mpr h⟩⟩
  have hborn : ∀ i p, lifeBornAt F S γ H i p j ↔ lifeBornAt F S γ H' i p j := by
    intro i p
    exact ⟨fun ⟨hp, h⟩ => ⟨hp, (hF i ⟨p, hp⟩ j le_rfl).1.mp h⟩,
      fun ⟨hp, h⟩ => ⟨hp, (hF i ⟨p, hp⟩ j le_rfl).1.mpr h⟩⟩
  intro i
  refine ⟨?_, ?_⟩
  · rw [(h i).1]; exact Finset.filter_congr (fun r _ => (hdel i _).symm)
  · rw [(h i).2]; exact Finset.filter_congr (fun p _ => (hborn i p).symm)

theorem traceGuided_congr {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H H' : PDLifeAssignment F S γ) (k : ℕ) (hk : k ≤ pathLength S.x)
    (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (hF : FutAgree F S γ (pathLength S.x - k) H H')
    (h : TraceGuided F S γ H' k σ t) : TraceGuided F S γ H k σ t := by
  induction k generalizing σ with
  | zero =>
    exact ghostGuided_congr F S γ H H' _ σ t (fun i p m hm => hF i p m (by simp at hm ⊢; omega)) h
  | succ k ih =>
    obtain ⟨hG, hE, hT⟩ := h
    refine ⟨ghostGuided_congr F S γ H H' _ σ t.1 hF hG, ?_,
      ih (by omega) _ t.2.2 (fun i p m hm => hF i p m (by omega)) hT⟩
    intro hj i
    rw [hE hj i]
    apply decide_eq_decide.mpr
    exact ⟨fun ⟨hp, h⟩ => ⟨hp, (hF i ⟨_, hp⟩ _ (by simp)).2.2.mpr h⟩,
      fun ⟨hp, h⟩ => ⟨hp, (hF i ⟨_, hp⟩ _ (by simp)).2.2.mp h⟩⟩

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
