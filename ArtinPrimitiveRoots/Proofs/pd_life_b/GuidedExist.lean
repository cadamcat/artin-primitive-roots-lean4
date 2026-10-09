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

/-- Shared slots keep their line along an admissible edge. -/
theorem shared_line {x : ℝ} {K : ℕ} (a : Fin K → ℝ) (d₀ : ℕ) (P : PrimeLists x K)
    (z z' : ℤ × ℤ) (hP : ValidPrimeLists x K a P)
    (hpad : IsPadAdmissible d₀ (sharedProduct P) (det2 z z'))
    (hz : Int.gcd z.1 z.2 = 1) (hz' : Int.gcd z'.1 z'.2 = 1)
    (i : Fin K) (y : Fin (slotCount x)) (hy : y.val < momentJ x) :
    projLine (P i y) z = projLine (P i y) z' := by
  apply pd_life_b_projLine_eq_of_det_dvd _ (hP.1 i y).1 z z' hz hz'
  have h1 : P i y ∣ sharedProduct P := by
    unfold sharedProduct
    have hin : P i y ∣ ∏ y' : Fin (slotCount x), if y'.val < momentJ x then P i y' else 1 := by
      have := Finset.dvd_prod_of_mem (fun y' : Fin (slotCount x) =>
        if y'.val < momentJ x then P i y' else 1) (Finset.mem_univ y)
      simpa [hy] using this
    exact dvd_trans hin (Finset.dvd_prod_of_mem (fun i' : Fin K =>
      ∏ y' : Fin (slotCount x), if y'.val < momentJ x then P i' y' else 1) (Finset.mem_univ i))
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h1) hpad.2.2

theorem fin_le_succ_cases {n : ℕ} (j : Fin n) (m : Fin (n + 1)) (h : m ≤ j.succ) :
    m ≤ j.castSucc ∨ m = j.succ := by
  by_cases hm : m = j.succ
  · exact Or.inr hm
  · left
    have h1 := Fin.le_def.mp h
    have h2 : m.val ≠ j.val + 1 := fun h' => hm (Fin.ext (by simpa using h'))
    simp only [Fin.val_succ] at h1
    exact Fin.le_def.mpr (by simp only [Fin.coe_castSucc]; omega)

/-- Common facts about one valid step `σ → τ → υ` from visit `j` to `j+1`. -/
structure StepFacts {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (j : Fin (pathLength S.x)) (σ : LogPoint S.x K) (g : GhostTraceChoice F S σ)
    (τ : LogPoint S.x K) (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i) : Prop where
  ghost : τ = ghostTraceOutput F S j.val σ g
  guard : ∀ i, g.1 i ⊆ hitIndices (σ.1.2.2 i) σ.1.1
  adm : EdgeAdmissible F S w (permuteLogPoint π τ).1 c (γ j.succ).1
  visit : ((edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.1,
    (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.1) = γ j.succ
  nodup : ((edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).2.map Prod.snd).Nodup

/-- **Preservation of the past record** along a valid step. -/
theorem existRec_step {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (j : Fin (pathLength S.x)) (σ : LogPoint S.x K) (hR : ExistRec F S γ j.castSucc σ)
    (g : GhostTraceChoice F S σ) (τ : LogPoint S.x K)
    (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i)
    (hS : StepFacts F S w γ j σ g τ π π' c) :
    ExistRec F S γ j.succ (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')) := by
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
  have hgcd : Int.gcd (γ j.castSucc).1.1 (γ j.castSucc).1.2 = 1 := (hγ.1 j.castSucc).1
  have hgcd' : Int.gcd (γ j.succ).1.1 (γ j.succ).1.2 = 1 := hS.adm.2.2.2.2.2.1
  have hLy : ∀ i y, L i y = if y.val < momentJ S.x then P i y else edgeNewLabel (c i) :=
    fun _ _ => rfl
  -- logs
  have hτsub : ∀ p, p ∈ τ.2.map Prod.snd → p ∈ υ.2.map Prod.snd :=
    fun p hp => (edge_log_iff F S j.val _ τ π π' c p).mpr (Or.inl hp)
  have hτnd : (τ.2.map Prod.snd).Nodup := by
    have hsub : List.Sublist (τ.2.map Prod.snd) (υ.2.map Prod.snd) :=
      (List.sublist_append_left τ.2 _).map Prod.snd
    exact hsub.nodup hS.nodup
  have hτlog : ∀ p, p ∈ τ.2.map Prod.snd ↔ p ∈ σ.2.map Prod.snd ∨ ∃ i, p ∈ (g.2 i).1 := by
    intro p; rw [hτdef]; exact ghost_log_iff F S j.val σ g p
  have hσsub : ∀ p, p ∈ σ.2.map Prod.snd → p ∈ τ.2.map Prod.snd :=
    fun p hp => (hτlog p).mpr (Or.inl hp)
  have hborn : ∀ i p, p ∈ (g.2 i).1 → p ∉ σ.2.map Prod.snd := by
    intro i p hp
    rw [hτdef] at hτnd
    exact ghost_born_not_logged F S j.val σ g hτnd i p hp
  have hbornBand : ∀ i p, p ∈ (g.2 i).1 → p ∈ primeBand S.x (F.a i) :=
    fun i p hp => Finset.mem_powerset.mp (g.2 i).2 hp
  -- activity
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
  have hnotactLog : ∀ p, p ∉ σ.2.map Prod.snd → ∀ m, m ≤ j.castSucc → ¬ IsActiveAt γ p m :=
    fun p hp m hm hact => hp (hR.actLog p m hm hact)
  -- τ memory
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
    · exact hσsub _ (hR.memLog i _ (List.get_mem _ r))
    · exact (hτlog _).mpr (Or.inr ⟨i, hb⟩)
  have hτmemAct : ∀ i, ∀ q ∈ τ.1.2.2 i, ¬ IsActiveAt γ q.1 j.castSucc := by
    intro i q hq
    rcases (hτmem i q).mp hq with ⟨r, -, rfl⟩ | ⟨hb, -⟩
    · exact (hR.memRec i _ (List.get_mem _ r)).1
    · exact hnotactLog _ (hborn i _ hb) _ le_rfl
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
  -- labels
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
  -- υ memory
  have hυmem : ∀ i q, q ∈ υ.1.2.2 i ↔
      (∃ r : Fin (τ.1.2.2 i).length, (c i).2 ≠ Sum.inl r ∧ (τ.1.2.2 i).get r = q) ∨
        ((c i).1 = true ∧ q = anchorAt (P i (lastSlot S.x)) τ.1.1) :=
    edge_mem_iff F S j.val _ τ π π' c
  have hυmemNotAct : ∀ i, ∀ q ∈ υ.1.2.2 i, ¬ ∃ i' y, L i' y = q.1 := by
    intro i q hq
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
  refine ⟨hS.visit, ?_, hS.nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- memNodup
    intro i
    show ((edgeNewMemory F S (permuteLogPoint π τ).1 c i).map Prod.fst).Nodup
    unfold edgeNewMemory
    rw [List.map_append]
    refine List.Nodup.append (((removeIndices_sublist' _ _).map Prod.fst).nodup
      (hτnodup i)) ?_ ?_
    · split_ifs <;> simp
    · intro a ha hb
      split_ifs at hb
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        apply hτmemAct i q ((removeIndices_sublist' _ _).subset hq)
        rw [hb]
        exact (hactj _).mpr ⟨i, _, rfl⟩
      · simp at hb
  · -- memBand
    intro i q hq
    rcases (hυmem i q).mp hq with ⟨r, -, rfl⟩ | ⟨-, rfl⟩
    · exact hτmemBand i _ (List.get_mem _ r)
    · exact (hPv.1 i _).2
  · -- memLog
    intro i q hq
    rcases (hυmem i q).mp hq with ⟨r, -, rfl⟩ | ⟨-, rfl⟩
    · exact hτsub _ (hτmemLog i _ (List.get_mem _ r))
    · exact hτsub _ (hσsub _ (hR.actLog _ _ le_rfl ((hactj _).mpr ⟨i, _, rfl⟩)))
  · -- logBand
    intro p hp
    rcases (edge_log_iff F S j.val _ τ π π' c p).mp hp with hp | ⟨i, q, -, rfl⟩
    · rcases (hτlog p).mp hp with hp | ⟨i, hb⟩
      · exact hR.logBand p hp
      · exact ⟨i, hbornBand i p hb⟩
    · exact ⟨i, q.2⟩
  · -- actLog
    intro p m hm hact
    rcases fin_le_succ_cases j m hm with hm | rfl
    · exact hτsub _ (hσsub _ (hR.actLog p m hm hact))
    · obtain ⟨i, y, hy⟩ := (hactj1 p).mp hact
      rw [hLy] at hy
      split_ifs at hy with hyJ
      · exact hτsub _ (hσsub _ (hR.actLog p _ le_rfl ((hactj _).mpr ⟨i, y, hy⟩)))
      · rcases hlabel i p hy with ⟨k, -, hk⟩ | ⟨q, hc, hq, -⟩
        · rw [← hk]; exact hτsub _ (hτmemLog i _ (List.get_mem _ k))
        · exact (edge_log_iff F S j.val _ τ π π' c p).mpr (Or.inr ⟨i, q, hc, hq⟩)
  · -- actLine
    have hnew : ∀ p (m : Fin (pathLength S.x + 1)), m ≤ j.castSucc → IsActiveAt γ p m →
        IsActiveAt γ p j.succ → projLine p (γ m).1 = projLine p (γ j.succ).1 := by
      intro p m hm hactm hact1
      obtain ⟨i, y, hy⟩ := (hactj1 p).mp hact1
      rw [hLy] at hy
      split_ifs at hy with hyJ
      · subst hy
        rw [hR.actLine _ m j.castSucc hm le_rfl hactm ((hactj _).mpr ⟨i, y, rfl⟩), ← hτz]
        exact shared_line F.a S.d₀ P τ.1.1 (γ j.succ).1 hPv hS.adm.2.2.2.2.1
          (hτz ▸ hgcd) hgcd' i y hyJ
      · rcases hlabel i p hy with ⟨k, hk, hk'⟩ | ⟨q, -, -, hnl⟩
        · have hkm := List.get_mem (τ.1.2.2 i) k
          rcases (hτmem i _).mp hkm with ⟨r, -, hr⟩ | ⟨hb, -⟩
          · have hrec := (hR.memRec i _ (List.get_mem _ r)).2
            rw [hr, hk'] at hrec
            rcases hrec with ⟨-, hno⟩ | ⟨m₀, hm₀, hact₀, hline⟩
            · exact absurd hactm (hno m hm)
            · rw [hR.actLine p m m₀ hm (le_of_lt hm₀) hactm hact₀]
              have hhit : ((τ.1.2.2 i).get k).2 =
                  (projLine ((τ.1.2.2 i).get k).1 (γ j.succ).1).val := hS.adm.1 i k hk
              apply Fin.ext
              rw [hline, hhit, hk']
          · rw [hk'] at hb
            exact absurd hactm (hnotactLog p (hborn i p hb) m hm)
        · exact absurd (hσsub _ (hR.actLog p m hm hactm)) hnl
    intro p m m' hm hm' hact hact'
    rcases fin_le_succ_cases j m hm with hm | rfl <;>
      rcases fin_le_succ_cases j m' hm' with hm' | rfl
    · exact hR.actLine p m m' hm hm' hact hact'
    · exact hnew p m hm hact hact'
    · exact (hnew p m' hm' hact' hact).symm
    · rfl
  · -- memRec
    intro i q hq
    have hna : ¬ IsActiveAt γ q.1 j.succ := fun h =>
      hυmemNotAct i q hq ((hactj1 _).mp h)
    refine ⟨hna, ?_⟩
    rcases (hυmem i q).mp hq with ⟨r, -, rfl⟩ | ⟨-, rfl⟩
    · rcases (hτmem i _).mp (List.get_mem _ r) with ⟨r', -, hr'⟩ | ⟨hb, hanc⟩
      · have hrec := (hR.memRec i _ (List.get_mem _ r')).2
        rw [hr'] at hrec
        rcases hrec with ⟨⟨a, ha, hla⟩, hno⟩ | ⟨m, hm, hact, hline⟩
        · refine Or.inl ⟨⟨a, lt_trans ha (Fin.castSucc_lt_succ), hla⟩, ?_⟩
          intro m hm
          rcases fin_le_succ_cases j m hm with hm | rfl
          · exact hno m hm
          · exact hna
        · exact Or.inr ⟨m, lt_trans hm (Fin.castSucc_lt_succ), hact, hline⟩
      · refine Or.inl ⟨⟨j.castSucc, Fin.castSucc_lt_succ, ?_⟩, ?_⟩
        · rw [hanc]; show _ = (projLine _ σ.1.1).val; rw [hz]; rfl
        · intro m hm
          rcases fin_le_succ_cases j m hm with hm | rfl
          · exact hnotactLog _ (hborn i _ hb) m hm
          · exact hna
    · refine Or.inr ⟨j.castSucc, Fin.castSucc_lt_succ, (hactj _).mpr ⟨i, _, rfl⟩, ?_⟩
      show _ = (projLine _ τ.1.1).val
      rw [hτz]; rfl
  · -- deadRec
    intro i p hp hlog hnot hna
    have hshift : ∀ m : Fin (pathLength S.x + 1), m < j.castSucc → m < j.succ :=
      fun m hm => lt_trans hm Fin.castSucc_lt_succ
    have hextend : (∀ m, m ≤ j.castSucc → ¬ IsActiveAt γ p m) →
        ∀ m, m ≤ j.succ → ¬ IsActiveAt γ p m := by
      intro h m hm
      rcases fin_le_succ_cases j m hm with hm | rfl
      · exact h m hm
      · exact hna
    by_cases hσlog : p ∈ σ.2.map Prod.snd
    · by_cases hact0 : IsActiveAt γ p j.castSucc
      · exact Or.inl ⟨j.castSucc, Fin.castSucc_lt_succ, hact0⟩
      by_cases hmem : ∃ q ∈ σ.1.2.2 i, q.1 = p
      · obtain ⟨q, hq, rfl⟩ := hmem
        obtain ⟨r, hr⟩ := List.mem_iff_get.mp hq
        by_cases hrD : r ∈ g.1 i
        · have hhit := Finset.mem_filter.mp (hS.guard i hrD)
          have hhit' : q.2 = (projLine q.1 (γ j.castSucc).1).val := by
            rw [← hz, ← hr]; exact hhit.2
          rcases (hR.memRec i q hq).2 with ⟨⟨a, ha, hla⟩, hno⟩ | ⟨m, hm, hact, -⟩
          · refine Or.inr ⟨a, j.castSucc, ha, Fin.castSucc_lt_succ, ?_, hextend hno⟩
            apply Fin.ext; rw [← hhit', hla]
          · exact Or.inl ⟨m, hshift m hm, hact⟩
        · exfalso
          have hτq : q ∈ τ.1.2.2 i := (hτmem i q).mpr (Or.inl ⟨r, hrD, hr⟩)
          obtain ⟨r', hr'⟩ := List.mem_iff_get.mp hτq
          by_cases hprom : (c i).2 = Sum.inl r'
          · apply hna
            refine (hactj1 _).mpr ⟨i, lastSlot S.x, ?_⟩
            rw [hLy, if_neg (by simp [lastSlot])]
            unfold edgeNewLabel; rw [hprom]; exact congrArg Prod.fst hr'
          · exact hnot q ((hυmem i q).mpr (Or.inl ⟨r', hprom, hr'⟩)) rfl
      · push_neg at hmem
        rcases hR.deadRec i p hp hσlog hmem hact0 with ⟨m, hm, hact⟩ | ⟨a, c', hac, hc, hl', hno⟩
        · exact Or.inl ⟨m, hshift m hm, hact⟩
        · exact Or.inr ⟨a, c', hac, hshift c' hc, hl', hextend hno⟩
    · exfalso
      rcases (edge_log_iff F S j.val _ τ π π' c p).mp hlog with hτp | ⟨i', q, hc, hq⟩
      · rcases (hτlog p).mp hτp with h | ⟨i', hb⟩
        · exact hσlog h
        · have hii := hgroup i' i p (hbornBand i' p hb) hp
          subst hii
          have hτq : anchorAt p σ.1.1 ∈ τ.1.2.2 i' := (hτmem i' _).mpr (Or.inr ⟨hb, rfl⟩)
          obtain ⟨r', hr'⟩ := List.mem_iff_get.mp hτq
          by_cases hprom : (c i').2 = Sum.inl r'
          · apply hna
            refine (hactj1 _).mpr ⟨i', lastSlot S.x, ?_⟩
            rw [hLy, if_neg (by simp [lastSlot])]
            unfold edgeNewLabel; rw [hprom]; exact congrArg Prod.fst hr'
          · exact hnot _ ((hυmem i' _).mpr (Or.inl ⟨r', hprom, hr'⟩)) rfl
      · apply hna
        refine (hactj1 _).mpr ⟨i', lastSlot S.x, ?_⟩
        rw [hLy, if_neg (by simp [lastSlot])]
        unfold edgeNewLabel; rw [hc]; exact hq

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
