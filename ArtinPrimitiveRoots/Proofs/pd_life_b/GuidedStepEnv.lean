import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedExistBase

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- Derived facts of a valid step with a life state of `H'` at the next visit. -/
structure StepEnv {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (j : Fin (pathLength S.x)) (σ : LogPoint S.x K) (g : GhostTraceChoice F S σ)
    (τ : LogPoint S.x K) (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i) (H' : PDLifeAssignment F S γ) :
    Prop where
  hz : σ.1.1 = (γ j.castSucc).1
  hτz : τ.1.1 = (γ j.castSucc).1
  hτlog : ∀ x, x ∈ τ.2.map Prod.snd ↔ x ∈ σ.2.map Prod.snd ∨ ∃ i, x ∈ (g.2 i).1
  hτsub : ∀ x, x ∈ τ.2.map Prod.snd →
    x ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).2.map Prod.snd
  hborn : ∀ i x, x ∈ (g.2 i).1 → x ∉ σ.2.map Prod.snd
  hbornBand : ∀ i x, x ∈ (g.2 i).1 → x ∈ primeBand S.x (F.a i)
  hactj : ∀ x, IsActiveAt γ x j.castSucc ↔ ∃ i y, permuteLists π τ.1.2.1 i y = x
  hactj1 : ∀ x, IsActiveAt γ x j.succ ↔
    ∃ i y, edgeTargetLists F S (permuteLogPoint π τ).1 c i y = x
  hLy : ∀ i y, edgeTargetLists F S (permuteLogPoint π τ).1 c i y =
    if y.val < momentJ S.x then permuteLists π τ.1.2.1 i y else edgeNewLabel (c i)
  hτmem : ∀ i q, q ∈ τ.1.2.2 i ↔
    (∃ r : Fin (σ.1.2.2 i).length, r ∉ g.1 i ∧ (σ.1.2.2 i).get r = q) ∨
      (q.1 ∈ (g.2 i).1 ∧ q = anchorAt q.1 σ.1.1)
  hτmemAct : ∀ i, ∀ q ∈ τ.1.2.2 i, ¬ IsActiveAt γ q.1 j.castSucc
  hτmemLog : ∀ i, ∀ q ∈ τ.1.2.2 i, q.1 ∈ τ.2.map Prod.snd
  hτnodup : ∀ i, ((τ.1.2.2 i).map Prod.fst).Nodup
  hlabel : ∀ i x, edgeNewLabel (c i) = x →
    (∃ k, (c i).2 = Sum.inl k ∧ ((τ.1.2.2 i).get k).1 = x) ∨
      (∃ q : primeBand S.x (F.a i), (c i).2 = Sum.inr q ∧ q.1 = x ∧ x ∉ τ.2.map Prod.snd)
  hlabelBand : ∀ i, edgeNewLabel (c i) ∈ primeBand S.x (F.a i)
  hυmem : ∀ i q, q ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.2 i ↔
    (∃ r : Fin (τ.1.2.2 i).length, (c i).2 ≠ Sum.inl r ∧ (τ.1.2.2 i).get r = q) ∨
      ((c i).1 = true ∧ q = anchorAt (permuteLists π τ.1.2.1 i (lastSlot S.x)) τ.1.1)
  hυmemNotAct : ∀ i,
    ∀ q ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.2 i,
      ¬ IsActiveAt γ q.1 j.succ
  hυlog : ∀ x, x ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).2.map Prod.snd ↔
    x ∈ τ.2.map Prod.snd ∨ ∃ i, ∃ q : primeBand S.x (F.a i), (c i).2 = Sum.inr q ∧ q.1 = x
  hprom : ∀ i k, (c i).2 = Sum.inl k →
    ((τ.1.2.2 i).get k).2 = (projLine ((τ.1.2.2 i).get k).1 (γ j.succ).1).val
  hgroup : ∀ i i' x, x ∈ primeBand S.x (F.a i) → x ∈ primeBand S.x (F.a i') → i = i'
  hH'mem : ∀ i q, q ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.2 i ↔
    ∃ hp : q.1 ∈ primeBand S.x (F.a i),
      pdLifePending S γ q.1 (H' i ⟨q.1, hp⟩) false j.succ ∧
        q.2 = (lifeLine S γ q.1 (H' i ⟨q.1, hp⟩).1).val
  hH'log : ∀ x, x ∈ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).2.map Prod.snd ↔
    lifeBornBefore F S γ H' x j.succ
  hlast : ∀ i, permuteLists π τ.1.2.1 i (lastSlot S.x) ∈ primeBand S.x (F.a i)
  hlastNot : ∀ i, ¬ IsActiveAt γ (permuteLists π τ.1.2.1 i (lastSlot S.x)) j.succ

theorem stepEnv_of {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (j : Fin (pathLength S.x)) (σ : LogPoint S.x K) (hR : ExistRec F S γ j.castSucc σ)
    (g : GhostTraceChoice F S σ) (τ : LogPoint S.x K)
    (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i)
    (hS : StepFacts F S w γ j σ g τ π π' c) (H' : PDLifeAssignment F S γ)
    (hH' : IsLifeState F S γ H' j.succ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π'))) :
    StepEnv F S γ j σ g τ π π' c H' := by
  have hτdef := hS.ghost
  set υ := edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π') with hυdef
  have hz : σ.1.1 = (γ j.castSucc).1 := congrArg Prod.fst hR.pos
  have hl : σ.1.2.1 = (γ j.castSucc).2 := congrArg Prod.snd hR.pos
  have hτz : τ.1.1 = (γ j.castSucc).1 := by rw [hτdef]; exact hz
  have hτl : τ.1.2.1 = (γ j.castSucc).2 := by rw [hτdef]; exact hl
  set P := permuteLists π τ.1.2.1 with hPdef
  set L := edgeTargetLists F S (permuteLogPoint π τ).1 c with hLdef
  have hPv : ValidPrimeLists S.x K F.a P := hS.adm.2.1
  have hLv : ValidPrimeLists S.x K F.a L := hS.adm.2.2.1
  have hST : IsSlotTransition P L := hS.adm.2.2.2.1
  have hLy : ∀ i y, L i y = if y.val < momentJ S.x then P i y else edgeNewLabel (c i) :=
    fun _ _ => rfl
  have hτsub : ∀ p, p ∈ τ.2.map Prod.snd → p ∈ υ.2.map Prod.snd :=
    fun p hp => (edge_log_iff F S j.val _ τ π π' c p).mpr (Or.inl hp)
  have hτnd : (τ.2.map Prod.snd).Nodup := by
    have hsub : List.Sublist (τ.2.map Prod.snd) (υ.2.map Prod.snd) :=
      (List.sublist_append_left τ.2 _).map Prod.snd
    exact hsub.nodup hS.nodup
  have hτlog : ∀ p, p ∈ τ.2.map Prod.snd ↔ p ∈ σ.2.map Prod.snd ∨ ∃ i, p ∈ (g.2 i).1 := by
    intro p; rw [hτdef]; exact ghost_log_iff F S j.val σ g p
  have hborn : ∀ i p, p ∈ (g.2 i).1 → p ∉ σ.2.map Prod.snd := by
    intro i p hp
    have h := hτnd
    rw [hτdef] at h
    exact ghost_born_not_logged F S j.val σ g h i p hp
  have hbornBand : ∀ i p, p ∈ (g.2 i).1 → p ∈ primeBand S.x (F.a i) :=
    fun i p hp => Finset.mem_powerset.mp (g.2 i).2 hp
  have hactj : ∀ p, IsActiveAt γ p j.castSucc ↔ ∃ i y, P i y = p := by
    intro p
    have := active_iff_permute S γ π j.castSucc p
    rw [this, hPdef, hτl]
  have hactj1 : ∀ p, IsActiveAt γ p j.succ ↔ ∃ i y, L i y = p := by
    intro p
    have h2 : (γ j.succ).2 = υ.1.2.1 := (congrArg Prod.snd hS.visit).symm
    unfold IsActiveAt
    rw [h2]
    constructor
    · rintro ⟨i, jj, h⟩; exact ⟨i, π' i jj, h⟩
    · rintro ⟨i, y, h⟩
      refine ⟨i, (π' i).symm y, ?_⟩
      show L i (π' i ((π' i).symm y)) = p
      rw [Equiv.apply_symm_apply]; exact h
  have hτmem : ∀ i q, q ∈ τ.1.2.2 i ↔
      (∃ r : Fin (σ.1.2.2 i).length, r ∉ g.1 i ∧ (σ.1.2.2 i).get r = q) ∨
        (q.1 ∈ (g.2 i).1 ∧ q = anchorAt q.1 σ.1.1) := by
    intro i q; rw [hτdef]; exact ghost_mem_iff F S j.val σ g i q
  have hτmemBand : ∀ i, ∀ q ∈ τ.1.2.2 i, q.1 ∈ primeBand S.x (F.a i) := by
    intro i q hq
    rcases (hτmem i q).mp hq with ⟨r, -, rfl⟩ | ⟨hb, -⟩
    · exact hR.memBand i _ (List.get_mem _ r)
    · exact hbornBand i _ hb
  have hτmemLog : ∀ i, ∀ q ∈ τ.1.2.2 i, q.1 ∈ τ.2.map Prod.snd := by
    intro i q hq
    rcases (hτmem i q).mp hq with ⟨r, -, rfl⟩ | ⟨hb, -⟩
    · exact (hτlog _).mpr (Or.inl (hR.memLog i _ (List.get_mem _ r)))
    · exact (hτlog _).mpr (Or.inr ⟨i, hb⟩)
  have hτmemAct : ∀ i, ∀ q ∈ τ.1.2.2 i, ¬ IsActiveAt γ q.1 j.castSucc := by
    intro i q hq
    rcases (hτmem i q).mp hq with ⟨r, -, rfl⟩ | ⟨hb, -⟩
    · exact (hR.memRec i _ (List.get_mem _ r)).1
    · exact fun hact => hborn i _ hb (hR.actLog _ _ le_rfl hact)
  have hτnodup : ∀ i, ((τ.1.2.2 i).map Prod.fst).Nodup := by
    intro i
    rw [hτdef]
    show ((removeIndices (σ.1.2.2 i) (g.1 i) ++
      ((g.2 i).1.toList.map fun p => anchorAt p σ.1.1)).map Prod.fst).Nodup
    rw [List.map_append, List.map_map]
    have hfst : (Prod.fst ∘ fun p => anchorAt p σ.1.1) = id := by funext p; rfl
    rw [hfst, List.map_id]
    refine List.Nodup.append (((removeIndices_sublist' _ _).map Prod.fst).nodup
      (hR.memNodup i)) (Finset.nodup_toList _) ?_
    intro a ha hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    exact hborn i _ (Finset.mem_toList.mp hb)
      (hR.memLog i q ((removeIndices_sublist' _ _).subset hq))
  have hlabel : ∀ i p, edgeNewLabel (c i) = p →
      (∃ k, (c i).2 = Sum.inl k ∧ ((τ.1.2.2 i).get k).1 = p) ∨
        (∃ q : primeBand S.x (F.a i), (c i).2 = Sum.inr q ∧ q.1 = p ∧
          p ∉ τ.2.map Prod.snd) := by
    intro i p hp
    unfold edgeNewLabel at hp
    cases hc : (c i).2 with
    | inl k => rw [hc] at hp; exact Or.inl ⟨k, rfl, hp⟩
    | inr q =>
      rw [hc] at hp
      exact Or.inr ⟨q, rfl, hp, hp ▸ edge_fresh_not_logged F S j.val _ τ π π' c hS.nodup i q hc⟩
  have hlabelBand : ∀ i, edgeNewLabel (c i) ∈ primeBand S.x (F.a i) := by
    intro i
    rcases hlabel i _ rfl with ⟨k, -, hk⟩ | ⟨q, -, hq, -⟩
    · rw [← hk]; exact hτmemBand i _ (List.get_mem _ k)
    · rw [← hq]; exact q.2
  have hgroup : ∀ i i' p, p ∈ primeBand S.x (F.a i) → p ∈ primeBand S.x (F.a i') → i = i' := by
    intro i i' p h1 h2
    by_contra hne
    exact Finset.disjoint_left.mp (hBands i i' hne) h1 h2
  have hfacts := fun i p hp => edge_slot_facts F S hBands P L hPv hLv hST i p hp
  have hυmem : ∀ i q, q ∈ υ.1.2.2 i ↔
      (∃ r : Fin (τ.1.2.2 i).length, (c i).2 ≠ Sum.inl r ∧ (τ.1.2.2 i).get r = q) ∨
        ((c i).1 = true ∧ q = anchorAt (P i (lastSlot S.x)) τ.1.1) :=
    edge_mem_iff F S j.val _ τ π π' c
  have hυmemNotAct : ∀ i, ∀ q ∈ υ.1.2.2 i, ¬ IsActiveAt γ q.1 j.succ := by
    intro i q hq hact
    have hL' := (hactj1 _).mp hact
    revert hL'
    rcases (hυmem i q).mp hq with ⟨r, hr, rfl⟩ | ⟨-, rfl⟩
    · rintro ⟨i', y, hy⟩
      rw [hLy] at hy
      split_ifs at hy with hyJ
      · exact hτmemAct i _ (List.get_mem _ r) ((hactj _).mpr ⟨i', y, hy⟩)
      · have hb := hτmemBand i _ (List.get_mem _ r)
        have hii := hgroup i' i _ (hy ▸ hlabelBand i') hb
        subst hii
        rcases hlabel i' _ hy with ⟨k, hk, hk'⟩ | ⟨q', -, -, hnl⟩
        · apply hr
          rw [hk]
          congr 1
          exact (index_inj_of_nodup _ (hτnodup i') r k hk'.symm).symm
        · exact hnl (hτmemLog i' _ (List.get_mem _ r))
    · exact (hfacts i _ (hPv.1 i (lastSlot S.x)).2).2.2.2
  refine ⟨hz, hτz, hτlog, hτsub, hborn, hbornBand, hactj, hactj1, hLy, hτmem, hτmemAct,
    hτmemLog, hτnodup, hlabel, hlabelBand, hυmem, hυmemNotAct,
    edge_log_iff F S j.val _ τ π π' c, ?_, hgroup, hH'.2.2.1, hH'.2.2.2.2,
    fun i => (hPv.1 i _).2, ?_⟩
  · intro i k hk
    exact hS.adm.1 i k hk
  · intro i hact
    exact (hfacts i _ (hPv.1 i (lastSlot S.x)).2).2.2.2 ((hactj1 _).mp hact)

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
