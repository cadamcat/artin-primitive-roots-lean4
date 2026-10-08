import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_positive_choice_rows
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_chronological_model
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».Defs
import ArtinPrimitiveRoots.Proofs.pd5_low_b.MemoryPermutation

/-! Column (reverse-transition) support for `pd5_twisted_edge_schur`.
The first block is copied from the lane helpers in `PD-LOW/pd5_twisted_edge_schur.lean`
(reverse choice, memory permutation and group-weight facts), renamed `pd5c_`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

private theorem pd5c_get_append_singleton {α : Type*} (l : List α) (a : α) :
    (l ++ [a]).get ⟨l.length, by simp⟩ = a := by
  rw [List.get_eq_getElem]
  rw [List.getElem_append_right (as := l) (bs := [a])
    (i := l.length) (Nat.le_refl _)]
  simp

private theorem pd5c_get_append_last_cast {α : Type*} (l : List α) (a : α)
    (hlen : l.length + 1 = (l ++ [a]).length) :
    (l ++ [a]).get (Fin.cast hlen (Fin.last l.length)) = a := by
  rw [List.get_eq_getElem]
  have hval : (Fin.cast hlen (Fin.last l.length)).val = l.length := by
    simp [Fin.cast, Fin.last]
  simp [hval, List.getElem_append_right]

private theorem pd5c_list_get_eq_of_eq {α : Type*} {l₁ l₂ : List α}
    (h : l₁ = l₂) (i : Fin l₁.length) :
    l₁.get i = l₂.get (Fin.cast (congrArg List.length h) i) := by
  cases h
  rfl

private def pd5c_edgeRemovedIndices {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
    Finset (Fin (s.2.2 i).length) :=
  match (c i).2 with
  | Sum.inl k => {k}
  | Sum.inr _ => ∅

private def pd5c_edgeReverseChoice {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
    EdgeChoice S.x F.a (edgeNewMemory F S s c i) i :=
  ((c i).2.isLeft,
    if hstore : (c i).1 then
      let pre := removeIndices (s.2.2 i) (pd5c_edgeRemovedIndices F S s c i)
      let hlen : pre.length + 1 = (edgeNewMemory F S s c i).length := by
        simp [pre, edgeNewMemory, pd5c_edgeRemovedIndices, hstore] <;> rfl
      Sum.inl (Fin.cast hlen (Fin.last pre.length))
    else
      Sum.inr ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩)

private theorem pd5c_edgeNewMemory_inl {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K)
    (stored : Bool) (k : Fin (s.2.2 i).length)
    (hchoice : c i = (stored, Sum.inl k)) :
    edgeNewMemory F S s c i = removeIndices (s.2.2 i) {k} ++
      (if stored then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else []) := by
  rw [edgeNewMemory, hchoice]

private theorem pd5c_removeIndices_empty (l : List Particle) :
    removeIndices l ∅ = l := by
  simp [removeIndices]

private theorem pd5c_edgeNewMemory_inr {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K)
    (stored : Bool) (p : {p : ℕ // p ∈ primeBand S.x (F.a i)})
    (hchoice : c i = (stored, Sum.inr p)) :
    edgeNewMemory F S s c i = s.2.2 i ++
      (if stored then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else []) := by
  rw [edgeNewMemory, hchoice]
  simp [pd5c_removeIndices_empty]

private def pd5c_selectIndices (l : List Particle) (D : Finset (Fin l.length)) :
    List Particle :=
  (List.finRange l.length).filterMap fun k => if k ∈ D then some (l.get k) else none

private theorem pd5c_filterMap_complement_perm {α β : Type*} (l : List α)
    (P : α → Prop) [DecidablePred P] (f : α → β) :
    List.Perm
      ((l.filterMap fun a => if P a then none else some (f a)) ++
        l.filterMap (fun a => if P a then some (f a) else none)) (l.map f) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases ha : P a
      · let A := l.filterMap (fun a => if P a then none else some (f a))
        let B := l.filterMap (fun a => if P a then some (f a) else none)
        have hmove : List.Perm (A ++ [f a] ++ B) ([f a] ++ A ++ B) := by
          exact List.Perm.append_right B
            (List.perm_append_comm (l₁ := A) (l₂ := [f a]))
        have hcons : ([f a] ++ A ++ B).Perm (f a :: List.map f l) := by
          simpa [A, B, List.append_assoc] using (List.Perm.cons (f a) ih)
        simpa [A, B, ha, List.append_assoc] using hmove.trans hcons
      · simp [ha, ih]

private theorem pd5c_remove_select_perm (l : List Particle)
    (D : Finset (Fin l.length)) :
    List.Perm (removeIndices l D ++ pd5c_selectIndices l D) l := by
  classical
  unfold removeIndices pd5c_selectIndices
  simpa [List.map_get_finRange] using
    (pd5c_filterMap_complement_perm (List.finRange l.length) (fun k => k ∈ D)
      (fun k => l.get k))

private theorem pd5c_select_singleton (l : List Particle) (k : Fin l.length) :
    pd5c_selectIndices l {k} = [l.get k] := by
  induction l with
  | nil => exact Fin.elim0 k
  | cons a l ih =>
      refine Fin.cases ?_ ?_ k
      · simp [pd5c_selectIndices, List.finRange]
      · intro j
        unfold pd5c_selectIndices
        simp only [Finset.mem_singleton, List.length_cons]
        change (List.finRange (l.length + 1)).filterMap
          (fun x => if x = j.succ then some ((a :: l).get x) else none) =
            [(a :: l).get j.succ]
        rw [← List.ofFn_id (l.length + 1), List.ofFn_succ]
        simp only [id_eq]
        rw [List.filterMap_cons]
        have hzero : (0 : Fin (l.length + 1)) ≠ j.succ :=
          (Fin.succ_ne_zero j).symm
        simp only [hzero, if_false]
        have hOfFn : List.ofFn (fun i : Fin l.length => i.succ) =
            (List.finRange l.length).map Fin.succ := List.ofFn_eq_map
        rw [hOfFn, List.filterMap_map]
        have hfun : (fun i : Fin l.length =>
            if Fin.succ i = Fin.succ j then some ((a :: l).get (Fin.succ i)) else none) =
            (fun i => if i ∈ ({j} : Finset (Fin l.length)) then
              some (l.get i) else none) := by
          funext i
          simp
        change List.filterMap (fun i : Fin l.length =>
          if Fin.succ i = Fin.succ j then some ((a :: l).get (Fin.succ i)) else none)
          (List.finRange l.length) = [(a :: l).get j.succ]
        rw [hfun]
        change pd5c_selectIndices l {j} = [l.get j]
        exact ih j

private theorem pd5c_remove_singleton_append_perm (l : List Particle) (k : Fin l.length) :
    List.Perm (removeIndices l {k} ++ [l.get k]) l := by
  rw [← pd5c_select_singleton l k]
  exact pd5c_remove_select_perm l {k}

private theorem pd5c_remove_append_last_perm (l : List Particle) (a : Particle) :
    List.Perm (removeIndices (l ++ [a]) {⟨l.length, by simp⟩}) l := by
  let k : Fin (l ++ [a]).length := ⟨l.length, by simp⟩
  have hp := pd5c_remove_singleton_append_perm (l ++ [a]) k
  have hget : (l ++ [a]).get k = a := by
    simpa [k] using pd5c_get_append_singleton l a
  rw [hget] at hp
  apply List.perm_iff_count.mpr
  intro e
  have hc := (List.perm_iff_count.mp hp) e
  simp only [List.count_append, List.count_singleton] at hc
  exact Nat.add_right_cancel hc

private theorem pd5c_remove_last_perm_of_eq {m l : List Particle} (a : Particle)
    (hm : m = l ++ [a]) (k : Fin m.length)
    (hk : k = Fin.cast (congrArg List.length hm).symm ⟨l.length, by simp⟩) :
    List.Perm (removeIndices m {k}) l := by
  cases hm
  have hk' : k = ⟨l.length, by simp⟩ := by simpa using hk
  rw [hk']
  exact pd5c_remove_append_last_perm l a

private def pd5c_activeNuGroup {K : ℕ} (F : PDFix K) (S : PDScale)
    (p : PrimeLists S.x K) (i : Fin K) : ℝ :=
  ∏ j : Fin (slotCount S.x), memoryNu S.x K F.a F.q_d i (p i j)

private theorem pd5c_activeNuGroup_edge {K : ℕ} (F : PDFix K) (S : PDScale)
    (p q : PrimeLists S.x K) (i : Fin K)
    (hshared : ∀ j : Fin (slotCount S.x), j.val < momentJ S.x → p i j = q i j) :
    pd5c_activeNuGroup F S p i *
        memoryNu S.x K F.a F.q_d i (q i (lastSlot S.x)) =
      pd5c_activeNuGroup F S q i *
        memoryNu S.x K F.a F.q_d i (p i (lastSlot S.x)) := by
  classical
  let E : Finset (Fin (slotCount S.x)) :=
    Finset.univ.erase (lastSlot S.x)
  have hlast : lastSlot S.x ∈ (Finset.univ : Finset (Fin (slotCount S.x))) :=
    Finset.mem_univ _
  have hsplitP : pd5c_activeNuGroup F S p i =
      (∏ j ∈ E, memoryNu S.x K F.a F.q_d i (p i j)) *
        memoryNu S.x K F.a F.q_d i (p i (lastSlot S.x)) := by
    dsimp [pd5c_activeNuGroup, E]
    rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin (slotCount S.x)))
      (fun j => memoryNu S.x K F.a F.q_d i (p i j)) hlast]
  have hsplitQ : pd5c_activeNuGroup F S q i =
      (∏ j ∈ E, memoryNu S.x K F.a F.q_d i (q i j)) *
        memoryNu S.x K F.a F.q_d i (q i (lastSlot S.x)) := by
    dsimp [pd5c_activeNuGroup, E]
    rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin (slotCount S.x)))
      (fun j => memoryNu S.x K F.a F.q_d i (q i j)) hlast]
  have hprod :
      (∏ j ∈ E, memoryNu S.x K F.a F.q_d i (p i j)) =
        ∏ j ∈ E, memoryNu S.x K F.a F.q_d i (q i j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjne : j ≠ lastSlot S.x := (Finset.mem_erase.mp hj).1
    have hvalNe : j.val ≠ momentJ S.x := by
      intro heq
      apply hjne
      apply Fin.ext
      exact heq
    have hjlt : j.val < momentJ S.x := by
      have hlt : j.val < momentJ S.x + 1 := by simpa [slotCount] using j.isLt
      omega
    rw [hshared j hjlt]
  rw [hsplitP, hsplitQ, hprod]
  ring

private def pd5c_memoryNuListProd {K : ℕ} (F : PDFix K) (S : PDScale)
    (i : Fin K) (l : List Particle) : ℝ :=
  (l.map fun e => memoryNu S.x K F.a F.q_d i e.1).prod

private def pd5c_memoryNuListMass {K : ℕ} (F : PDFix K) (S : PDScale)
    (i : Fin K) (l : List Particle) : ℝ :=
  pd5c_memoryNuListProd F S i l / (l.length.factorial : ℝ)

private theorem pd5c_memoryNuListProd_perm {K : ℕ} (F : PDFix K) (S : PDScale)
    (i : Fin K) (l₁ l₂ : List Particle) (h : List.Perm l₁ l₂) :
    pd5c_memoryNuListProd F S i l₁ = pd5c_memoryNuListProd F S i l₂ := by
  unfold pd5c_memoryNuListProd
  exact (h.map fun e => memoryNu S.x K F.a F.q_d i e.1).prod_eq

private def pd5c_memGroupWeight {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (i : Fin K) : ℝ :=
  pd5c_activeNuGroup F S s.2.1 i * pd5c_memoryNuListMass F S i (s.2.2 i)

private theorem pd5c_memMeasure_eq_groupProd {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s) :
    memMeasure F S s = ∏ i : Fin K, pd5c_memGroupWeight F S s i := by
  simp [memMeasure, hs, pd5c_memGroupWeight, pd5c_activeNuGroup,
    pd5c_memoryNuListMass, pd5c_memoryNuListProd, Finset.prod_mul_distrib]

private theorem pd5c_active_balance_algebra (A At νsrc νt P den C r : ℝ)
    (hAct : A * νt = At * νsrc)
    (hbase : 0 ≤ At * (P / den) * νsrc) (hfac : 1 ≤ C * r) :
    A * (P / den) * νt ≤ C * r * (At * (P / den) * νsrc) := by
  have hbase' : 0 ≤ (P / den) * (At * νsrc) := by nlinarith [hbase]
  calc
    A * (P / den) * νt = (P / den) * (A * νt) := by ring
    _ = (P / den) * (At * νsrc) := by rw [hAct]
    _ ≤ C * r * ((P / den) * (At * νsrc)) := by
      simpa using (mul_le_mul_of_nonneg_right hfac hbase')
    _ = C * r * (At * (P / den) * νsrc) := by ring

private theorem pd5c_edgeChoiceMass_inl {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (i : Fin K) (k : Fin (s.2.2 i).length) (stored : Bool)
    (hchoice : c i = (stored, Sum.inl k)) :
    pd5_edgeChoiceMass F S s c i = (bandMass S.x (F.a i))⁻¹ := by
  simp [pd5_edgeChoiceMass, hchoice]

private theorem pd5c_edgeChoiceMass_inr {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (i : Fin K) (p : {p : ℕ // p ∈ primeBand S.x (F.a i)}) (stored : Bool)
    (hchoice : c i = (stored, Sum.inr p)) :
    pd5_edgeChoiceMass F S s c i = memoryNu S.x K F.a F.q_d i p := by
  simp [pd5_edgeChoiceMass, hchoice]

private theorem pd5c_edgeGroupWeight_fresh_noStore {K : ℕ} (F : PDFix K)
    (S : PDScale) (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (z' : ℤ × ℤ) (i : Fin K) (p : {p : ℕ // p ∈ primeBand S.x (F.a i)})
    (hchoice : c i = (false, Sum.inr p))
    (hVlow : Real.log 2 / 2 ≤ bandMass S.x (F.a i))
    (hVhigh : bandMass S.x (F.a i) ≤ 2 * Real.log 2)
    (hbase : 0 ≤ pd5c_memGroupWeight F S
      (z', edgeTargetLists F S s c, edgeNewMemory F S s c) i *
        pd5_edgeChoiceMass F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
          (pd5c_edgeReverseChoice F S s hs c) i) :
    pd5c_memGroupWeight F S s i * pd5_edgeChoiceMass F S s c i ≤
      (1 + 2 / Real.log 2 + 2 * Real.log 2) *
        ((s.2.2 i).length + 1 : ℕ) *
        pd5c_memGroupWeight F S
          (z', edgeTargetLists F S s c, edgeNewMemory F S s c) i *
          pd5_edgeChoiceMass F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
            (pd5c_edgeReverseChoice F S s hs c) i := by
  classical
  let t : MemPoint S.x K :=
    (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
  let rc := pd5c_edgeReverseChoice F S s hs c
  let A := pd5c_activeNuGroup F S s.2.1 i
  let At := pd5c_activeNuGroup F S t.2.1 i
  let l := s.2.2 i
  let P := pd5c_memoryNuListProd F S i l
  let den := (l.length.factorial : ℝ)
  let νs := memoryNu S.x K F.a F.q_d i (s.2.1 i (lastSlot S.x))
  let νt := memoryNu S.x K F.a F.q_d i (edgeNewLabel (c i))
  have hlast : ¬ (lastSlot S.x).val < momentJ S.x := by
    dsimp [lastSlot]
    omega
  have hshared : ∀ j : Fin (slotCount S.x), j.val < momentJ S.x →
      s.2.1 i j = t.2.1 i j := by
    intro j hj
    simp [t, edgeTargetLists, hj]
  have hactiveRaw := pd5c_activeNuGroup_edge F S s.2.1 t.2.1 i hshared
  have hactive : A * νt = At * νs := by
    simpa [A, At, νs, νt, t, hlast, edgeTargetLists] using hactiveRaw
  have htargetLast : edgeTargetLists F S s c i (lastSlot S.x) = edgeNewLabel (c i) := by
    simp [edgeTargetLists, hlast]
  have hmem : t.2.2 i = l := by
    simp [t, edgeNewMemory, hchoice, l, pd5c_removeIndices_empty]
  have hgroupS : pd5c_memGroupWeight F S s i = A * (P / den) := by
    simp [pd5c_memGroupWeight, pd5c_memoryNuListMass, A, P, den, l]
  have hgroupT : pd5c_memGroupWeight F S t i = At * (P / den) := by
    change pd5c_activeNuGroup F S t.2.1 i *
      (pd5c_memoryNuListProd F S i (t.2.2 i) / ((t.2.2 i).length.factorial : ℝ)) = _
    rw [hmem]
  have hmassS : pd5_edgeChoiceMass F S s c i = νt := by
    have hlabel : edgeNewLabel (c i) = p.1 := by
      simp [edgeNewLabel, hchoice]
    simpa [νt, hlabel] using pd5c_edgeChoiceMass_inr F S s c i p false hchoice
  have hrc : rc i =
      (false, Sum.inr ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩) := by
    simp [rc, pd5c_edgeReverseChoice, hchoice]
  have hmassT : pd5_edgeChoiceMass F S t rc i = νs := by
    simpa [νs] using pd5c_edgeChoiceMass_inr F S t rc i
      ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩ false hrc
  have hbase' : 0 ≤ At * (P / den) * νs := by
    simpa [hgroupT, hmassT, t, rc] using hbase
  let C0 : ℝ := 1 + 2 / Real.log 2 + 2 * Real.log 2
  let r : ℝ := ((l.length + 1 : ℕ) : ℝ)
  have hC0 : 1 ≤ C0 := by
    dsimp [C0]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hdiv : 0 < 2 / Real.log 2 := div_pos (by norm_num) hlog
    have hmul : 0 < 2 * Real.log 2 := mul_pos (by norm_num) hlog
    linarith
  have hr : 1 ≤ r := by
    dsimp [r]
    push_cast
    have hlen : 1 ≤ l.length + 1 := by omega
    exact_mod_cast hlen
  have hfac : 1 ≤ C0 * r := by
    have hC0nonneg : 0 ≤ C0 := by linarith [hC0]
    exact (le_trans hC0 (le_mul_of_one_le_right hC0nonneg hr))
  rw [hgroupS, hmassS, hgroupT, hmassT]
  simpa [C0, r, mul_assoc, mul_left_comm, mul_comm] using
    pd5c_active_balance_algebra A At νs νt P den C0 r hactive hbase' hfac

private theorem pd5c_edgeReverseChoice_label {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
    edgeNewLabel (pd5c_edgeReverseChoice F S s hs c i) = s.2.1 i (lastSlot S.x) := by
  by_cases hb : (c i).1 = true
  · let pre := removeIndices (s.2.2 i) (pd5c_edgeRemovedIndices F S s c i)
    have happend : pre.length + 1 = (pre ++ [anchorAt (s.2.1 i (lastSlot S.x)) s.1]).length := by
      simp
    have hget := pd5c_get_append_last_cast pre (anchorAt (s.2.1 i (lastSlot S.x)) s.1) happend
    have hlen : pre.length + 1 = (edgeNewMemory F S s c i).length := by
      simp [pre, edgeNewMemory, pd5c_edgeRemovedIndices, hb] <;> rfl
    have hnew : edgeNewMemory F S s c i =
        pre ++ [anchorAt (s.2.1 i (lastSlot S.x)) s.1] := by
      simp [pre, edgeNewMemory, pd5c_edgeRemovedIndices, hb] <;> rfl
    simp only [pd5c_edgeReverseChoice, hb, dite_true, edgeNewLabel]
    have hindex :
        Fin.cast hlen (Fin.last pre.length) =
          (⟨pre.length, by rw [hnew]; simp⟩ : Fin (edgeNewMemory F S s c i).length) := by
      apply Fin.ext
      simp [Fin.cast, Fin.last]
    rw [hindex]
    let iPre : Fin (edgeNewMemory F S s c i).length :=
      ⟨pre.length, by rw [hnew]; simp⟩
    have hcast :
        Fin.cast (congrArg List.length hnew) iPre =
          Fin.cast happend (Fin.last pre.length) := by
      apply Fin.ext
      simp [iPre, Fin.cast, Fin.last]
    have hget' := pd5c_list_get_eq_of_eq hnew (Fin.cast hlen (Fin.last pre.length))
    rw [hindex] at hget'
    rw [hcast] at hget'
    rw [hget', hget]
    rfl
  · have hb' : (c i).1 = false := Bool.eq_false_of_not_eq_true hb
    simp [pd5c_edgeReverseChoice, edgeNewLabel, hb']

private theorem pd5c_edgeReverse_targetLists {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) :
    edgeTargetLists F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
      (pd5c_edgeReverseChoice F S s hs c) = s.2.1 := by
  funext i jj
  by_cases hshared : jj.val < momentJ S.x
  · simp [edgeTargetLists, hshared]
  · have hjlast : jj = lastSlot S.x := by
      apply Fin.ext
      have hlt : jj.val < momentJ S.x + 1 := by simpa [slotCount] using jj.isLt
      have hge : momentJ S.x ≤ jj.val := by omega
      have hle : jj.val ≤ momentJ S.x := by omega
      exact Nat.le_antisymm hle hge
    subst jj
    have hlast : ¬ (lastSlot S.x).val < momentJ S.x := by
      dsimp [lastSlot]
      omega
    simp [edgeTargetLists, hlast, pd5c_edgeReverseChoice_label]

private theorem pd5c_removeIndices_mem_of_mem {l : List Particle}
    (D : Finset (Fin l.length)) {e : Particle}
    (he : e ∈ removeIndices l D) : e ∈ l := by
  unfold removeIndices at he
  obtain ⟨k, hk, heq⟩ := List.mem_filterMap.mp he
  by_cases hD : k ∈ D
  · simp [hD] at heq
  · have hEq : l.get k = e := by
      simpa [hD] using heq
    rw [← hEq]
    exact List.get_mem l k

private theorem pd5c_anchorAt_le_prime (p : ℕ) (z : ℤ × ℤ) :
    (anchorAt p z).2 ≤ p := by
  dsimp [anchorAt]
  exact Nat.le_of_lt_succ (projLine p z).isLt

private theorem pd5c_edge_output_valid {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ)
    (hc : EdgeAdmissible F S w s c z') :
    MemValid F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c) := by
  rcases hc with ⟨_, _, htarget, _, _, hgcd, _, _, _, _⟩
  refine ⟨hgcd, fun i j => (htarget.1 i j).2, ?_⟩
  intro i e he
  change e ∈ removeIndices (s.2.2 i)
      (match (c i).2 with | .inl k => {k} | .inr _ => ∅) ++
    (if (c i).1 then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else []) at he
  rcases List.mem_append.mp he with hrem | hstore
  · exact hs.2.2 i e (pd5c_removeIndices_mem_of_mem _ hrem)
  · cases hflag : (c i).1 with
    | false => simp [hflag] at hstore
    | true =>
        have heq : e = anchorAt (s.2.1 i (lastSlot S.x)) s.1 := by
          simpa [hflag] using hstore
        rw [heq]
        exact ⟨hs.2.1 i (lastSlot S.x),
          pd5c_anchorAt_le_prime (s.2.1 i (lastSlot S.x)) s.1⟩

private theorem pd5c_edge_output_region {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (B : ℕ) (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ)
    (hc : EdgeAdmissible F S w s c z')
    (hsize : memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ B) :
    pd5_stateRegion F S w B (z', edgeTargetLists F S s c, edgeNewMemory F S s c) := by
  have hEdge := hc
  rcases hc with ⟨_, _, _, _, _, _, _, hboxTarget, _, _⟩
  exact ⟨pd5c_edge_output_valid F S w s hs c z' hEdge, hsize, Or.inr hboxTarget⟩

private theorem pd5c_removeIndices_length {l : List Particle}
    (D : Finset (Fin l.length)) :
    (removeIndices l D).length = l.length - D.card := by
  classical
  unfold removeIndices
  rw [List.length_filterMap_eq_countP]
  have hp :
      (fun a : Fin l.length => (if a ∈ D then none else some (l.get a)).isSome) =
        fun a => a ∉ D := by
    funext a
    by_cases h : a ∈ D <;> simp [h]
  rw [hp]
  have hfin : (List.finRange l.length).toFinset = (Finset.univ : Finset (Fin l.length)) := by
    ext a
    simp
  have hcount :
      (List.finRange l.length).countP (fun a => a ∉ D) =
        ((List.finRange l.length).toFinset.filter (fun a => a ∉ D)).card :=
    (List.nodup_finRange _).card_eq_countP.symm
  rw [hcount, hfin]
  have hfilter :
      (Finset.univ : Finset (Fin l.length)).filter (fun a => a ∉ D) =
        Finset.univ \ D := by
    ext a
    simp
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ D)]
  simp

private theorem pd5c_memoryNuListProd_append {K : ℕ} (F : PDFix K) (S : PDScale)
    (i : Fin K) (l : List Particle) (a : Particle) :
    pd5c_memoryNuListProd F S i (l ++ [a]) =
      pd5c_memoryNuListProd F S i l * memoryNu S.x K F.a F.q_d i a.1 := by
  simp [pd5c_memoryNuListProd, List.map_append]

private theorem pd5c_memoryNuListProd_remove_singleton {K : ℕ} (F : PDFix K)
    (S : PDScale) (i : Fin K) (l : List Particle) (k : Fin l.length) :
    pd5c_memoryNuListProd F S i l =
      pd5c_memoryNuListProd F S i (removeIndices l {k}) *
        memoryNu S.x K F.a F.q_d i (l.get k).1 := by
  have hp := pd5c_remove_singleton_append_perm l k
  have hprod := pd5c_memoryNuListProd_perm F S i _ _ hp
  rw [pd5c_memoryNuListProd_append] at hprod
  exact hprod.symm

private theorem pd5c_remove_singleton_length {l : List Particle} (k : Fin l.length) :
    (removeIndices l {k}).length + 1 = l.length := by
  have hlen := pd5c_removeIndices_length (l := l) ({k} : Finset (Fin l.length))
  have hcard : ({k} : Finset (Fin l.length)).card = 1 := by simp
  rw [hcard] at hlen
  have hk : 0 < l.length := Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  omega

private theorem pd5c_memoryNuListMass_remove_singleton_le {K : ℕ}
    (F : PDFix K) (S : PDScale) (i : Fin K) (l : List Particle)
    (k : Fin l.length)
    (hP : 0 ≤ pd5c_memoryNuListProd F S i (removeIndices l {k}))
    (hν : 0 ≤ memoryNu S.x K F.a F.q_d i (l.get k).1) :
    pd5c_memoryNuListMass F S i l ≤
      pd5c_memoryNuListMass F S i (removeIndices l {k}) *
        memoryNu S.x K F.a F.q_d i (l.get k).1 := by
  let pre := removeIndices l {k}
  have hprod := pd5c_memoryNuListProd_remove_singleton F S i l k
  have hlen : pre.length + 1 = l.length := pd5c_remove_singleton_length k
  have hfact : (l.length.factorial : ℝ) =
      (l.length : ℝ) * (pre.length.factorial : ℝ) := by
    rw [← hlen, Nat.factorial_succ]
    simp [Nat.cast_mul]
  have hfactPos : 0 < (pre.length.factorial : ℝ) := by positivity
  have hlenPos : 1 ≤ (l.length : ℝ) := by
    have hpos : 0 < l.length := by omega
    exact_mod_cast (Nat.succ_le_iff.mpr hpos)
  rw [pd5c_memoryNuListMass, pd5c_memoryNuListMass, hprod, hfact]
  have hnum : 0 ≤ pd5c_memoryNuListProd F S i pre *
      memoryNu S.x K F.a F.q_d i (l.get k).1 := mul_nonneg hP hν
  calc
    (pd5c_memoryNuListProd F S i pre * memoryNu S.x K F.a F.q_d i (l.get k).1) /
        ((l.length : ℝ) * (pre.length.factorial : ℝ))
        = ((pd5c_memoryNuListProd F S i pre * memoryNu S.x K F.a F.q_d i (l.get k).1) /
            (pre.length.factorial : ℝ)) / (l.length : ℝ) := by
              rw [div_div]; ring
    _ ≤ (pd5c_memoryNuListProd F S i pre * memoryNu S.x K F.a F.q_d i (l.get k).1) /
          (pre.length.factorial : ℝ) := by
          exact div_le_self (div_nonneg hnum hfactPos.le) hlenPos
    _ = pd5c_memoryNuListMass F S i pre *
          memoryNu S.x K F.a F.q_d i (l.get k).1 := by
          unfold pd5c_memoryNuListMass
          ring

private theorem pd5c_edgeReverse_memory_perm {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ)
    (hhit : ∀ i, ∀ k, (c i).2 = Sum.inl k →
      particleHits ((s.2.2 i).get k) z') :
    ∀ i, List.Perm
      (edgeNewMemory F S
        (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
        (pd5c_edgeReverseChoice F S s hs c) i) (s.2.2 i) := by
  intro i
  let t : MemPoint S.x K :=
    (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
  let rc := pd5c_edgeReverseChoice F S s hs c
  have hlast : ¬ (lastSlot S.x).val < momentJ S.x := by
    dsimp [lastSlot]
    omega
  have htargetLast :
      edgeTargetLists F S s c i (lastSlot S.x) = edgeNewLabel (c i) := by
    simp [edgeTargetLists, hlast]
  cases hchoice : c i with
  | mk stored choice =>
      cases choice with
      | inl k =>
          have hsecond : (c i).2 = Sum.inl k := by rw [hchoice]
          have hremoved : pd5c_edgeRemovedIndices F S s c i = {k} := by
            simp [pd5c_edgeRemovedIndices, hchoice]
          have hhit' := hhit i k hsecond
          let l := s.2.2 i
          let old := l.get k
          let pre := removeIndices l {k}
          have hlabel : edgeNewLabel (c i) = old.1 := by
            simp [edgeNewLabel, hchoice, old, l]
          have hanchor : anchorAt (edgeTargetLists F S s c i (lastSlot S.x)) z' = old := by
            apply Prod.ext
            · rw [htargetLast]
              exact hlabel
            · change (projLine (edgeTargetLists F S s c i (lastSlot S.x)) z').val = old.2
              rw [htargetLast, hlabel]
              exact hhit'.symm
          have hforward : edgeNewMemory F S s c i = pre ++
              (if stored then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else []) :=
            pd5c_edgeNewMemory_inl F S s c i stored k hchoice
          cases stored with
          | false =>
              have hrc : rc i =
                  (true, Sum.inr ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩) := by
                simp [rc, pd5c_edgeReverseChoice, hchoice]
              have hout := pd5c_edgeNewMemory_inr F S t rc i true
                ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩ hrc
              rw [hout]
              simpa [t, hforward, hanchor, pre, old, l] using
                pd5c_remove_singleton_append_perm l k
          | true =>
              let anchorSrc := anchorAt (s.2.1 i (lastSlot S.x)) s.1
              have hmem : edgeNewMemory F S s c i = pre ++ [anchorSrc] := by
                simpa [anchorSrc] using hforward
              have htMem : t.2.2 i = pre ++ [anchorSrc] := by
                simpa [t] using hmem
              let kBase : Fin (pre ++ [anchorSrc]).length :=
                ⟨pre.length, by simp⟩
              let kLast : Fin (t.2.2 i).length :=
                Fin.cast (congrArg List.length htMem).symm kBase
              have hrc : rc i = (true, Sum.inl kLast) := by
                apply Prod.ext
                · simp [rc, pd5c_edgeReverseChoice, hchoice]
                · change (rc i).2 = Sum.inl kLast
                  simp [rc, pd5c_edgeReverseChoice, hchoice, hremoved,
                    pre, kLast, kBase, htMem, Fin.cast, Fin.last]
                  rfl
              have hout := pd5c_edgeNewMemory_inl F S t rc i true kLast hrc
              rw [hout]
              have hp : List.Perm (removeIndices (t.2.2 i) {kLast}) pre :=
                pd5c_remove_last_perm_of_eq anchorSrc htMem kLast rfl
              have hsource : List.Perm (pre ++ [old]) l := by
                simpa [pre, old, l] using pd5c_remove_singleton_append_perm l k
              have hanchorT : anchorAt (t.2.1 i (lastSlot S.x)) t.1 = old := by
                simpa [t] using hanchor
              simpa [hanchorT] using (hp.append_right [old]).trans hsource
      | inr p =>
          let l := s.2.2 i
          have hremoved : pd5c_edgeRemovedIndices F S s c i = ∅ := by
            simp [pd5c_edgeRemovedIndices, hchoice]
          have hforward : edgeNewMemory F S s c i = l ++
              (if stored then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else []) :=
            pd5c_edgeNewMemory_inr F S s c i stored p hchoice
          cases stored with
          | false =>
              have hrc : rc i =
                  (false, Sum.inr ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩) := by
                simp [rc, pd5c_edgeReverseChoice, hchoice]
              have hout := pd5c_edgeNewMemory_inr F S t rc i false
                ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩ hrc
              rw [hout]
              have he : removeIndices l ∅ = l := pd5c_removeIndices_empty l
              simpa [t, hforward, l] using List.Perm.of_eq he
          | true =>
              let anchorSrc := anchorAt (s.2.1 i (lastSlot S.x)) s.1
              have hmem : edgeNewMemory F S s c i = l ++ [anchorSrc] := by
                simpa [anchorSrc] using hforward
              have htMem : t.2.2 i = l ++ [anchorSrc] := by
                simpa [t] using hmem
              let kBase : Fin (l ++ [anchorSrc]).length := ⟨l.length, by simp⟩
              let kLast : Fin (t.2.2 i).length :=
                Fin.cast (congrArg List.length htMem).symm kBase
              have hrc : rc i = (false, Sum.inl kLast) := by
                apply Prod.ext
                · simp [rc, pd5c_edgeReverseChoice, hchoice]
                · change (rc i).2 = Sum.inl kLast
                  simp [rc, pd5c_edgeReverseChoice, hchoice, hremoved,
                    l, kLast, kBase, htMem, Fin.cast, Fin.last,
                    pd5c_removeIndices_empty]
              have hout := pd5c_edgeNewMemory_inl F S t rc i false kLast hrc
              rw [hout]
              simpa [t] using pd5c_remove_last_perm_of_eq anchorSrc htMem kLast rfl



/-! ### New column helpers -/

theorem pd5c_removeIndices_singleton (l : List Particle) (k : Fin l.length) :
    removeIndices l {k} = l.eraseIdx k.val := by
  induction l with
  | nil => exact k.elim0
  | cons a l ih =>
      refine Fin.cases ?_ (fun j => ?_) k
      · unfold removeIndices
        change List.filterMap _ (List.finRange (l.length + 1)) = _
        rw [List.finRange_succ, List.filterMap_cons, List.filterMap_map]
        have hfun : ((fun k : Fin (l.length + 1) =>
            if k ∈ ({0} : Finset (Fin (l.length + 1))) then none
            else some ((a :: l).get k)) ∘ Fin.succ) = fun j => some (l.get j) := by
          funext j
          simp [Fin.succ_ne_zero]
        simp only [Finset.mem_singleton, if_true]
        change List.filterMap ((fun k : Fin (l.length + 1) =>
            if k ∈ ({0} : Finset (Fin (l.length + 1))) then none
            else some ((a :: l).get k)) ∘ Fin.succ) (List.finRange l.length) = _
        rw [hfun]
        simp [List.filterMap_eq_map, List.map_get_finRange]
      · have hrec : removeIndices (a :: l) {Fin.succ j} = a :: removeIndices l {j} := by
          unfold removeIndices
          change List.filterMap _ (List.finRange (l.length + 1)) = _
          rw [List.finRange_succ, List.filterMap_cons, List.filterMap_map]
          have hfun : ((fun k : Fin (l.length + 1) =>
              if k ∈ ({Fin.succ j} : Finset (Fin (l.length + 1))) then none
              else some ((a :: l).get k)) ∘ Fin.succ) =
              fun i => if i ∈ ({j} : Finset (Fin l.length)) then none else some (l.get i) := by
            funext i
            simp
          have h0 : ¬ ((0 : Fin (l.length + 1)) ∈ ({Fin.succ j} : Finset (Fin (l.length + 1)))) := by
            simp [eq_comm, Fin.succ_ne_zero]
          simp only [h0, if_false]
          change (a :: List.filterMap ((fun k : Fin (l.length + 1) =>
              if k ∈ ({Fin.succ j} : Finset (Fin (l.length + 1))) then none
              else some ((a :: l).get k)) ∘ Fin.succ) (List.finRange l.length)) = _
          rw [hfun]
        rw [hrec, ih j]
        rfl

theorem pd5c_list_eq_of_remove {l₁ l₂ : List Particle} (k₁ : Fin l₁.length)
    (k₂ : Fin l₂.length) (hk : k₁.val = k₂.val)
    (hrem : removeIndices l₁ {k₁} = removeIndices l₂ {k₂})
    (hget : l₁.get k₁ = l₂.get k₂) : l₁ = l₂ := by
  rw [pd5c_removeIndices_singleton, pd5c_removeIndices_singleton] at hrem
  have e1 := List.insertIdx_eraseIdx_getElem (l := l₁) k₁.isLt
  have e2 := List.insertIdx_eraseIdx_getElem (l := l₂) k₂.isLt
  have hget' : l₁[k₁.val] = l₂[k₂.val] := by
    simpa [List.get_eq_getElem] using hget
  calc
    l₁ = (l₁.eraseIdx k₁.val).insertIdx k₁.val l₁[k₁.val] := e1.symm
    _ = (l₂.eraseIdx k₂.val).insertIdx k₂.val l₂[k₂.val] := by
      rw [hget', hrem, hk]
    _ = l₂ := e2

theorem pd5c_sharedProduct_eq {x : ℝ} {K : ℕ} (p q : PrimeLists x K)
    (h : ∀ i (j : Fin (slotCount x)), j.val < momentJ x → p i j = q i j) :
    sharedProduct p = sharedProduct q := by
  unfold sharedProduct
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs with hj
  · exact h i j hj
  · rfl

theorem pd5c_edgeMult_norm_swap {K : ℕ} (F : PDFix K) (S : PDScale) (b raw : Bool)
    (p q : PrimeLists S.x K) (z z' : ℤ × ℤ) (hD : sharedProduct p = sharedProduct q) :
    ‖edgeMultiplier F S b raw p q z z'‖ = ‖edgeMultiplier F S (!b) raw q p z' z‖ := by
  cases b <;> cases raw <;>
    simp only [edgeMultiplier, hD, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, norm_star]

private theorem pd5c_mass_append {K : ℕ} (F : PDFix K) (S : PDScale) (i : Fin K)
    (l : List Particle) (a : Particle) :
    pd5c_memoryNuListMass F S i (l ++ [a]) * ((l.length : ℝ) + 1) =
      pd5c_memoryNuListMass F S i l * memoryNu S.x K F.a F.q_d i a.1 := by
  unfold pd5c_memoryNuListMass
  rw [pd5c_memoryNuListProd_append, List.length_append, List.length_singleton,
    Nat.factorial_succ]
  push_cast
  have h1 : (l.length.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((l.length : ℝ) + 1) ≠ 0 := by positivity
  field_simp

private theorem pd5c_listProd_nonneg {K : ℕ} (F : PDFix K) (S : PDScale) (i : Fin K)
    (l : List Particle) (h : ∀ e ∈ l, 0 ≤ memoryNu S.x K F.a F.q_d i e.1) :
    0 ≤ pd5c_memoryNuListProd F S i l := by
  unfold pd5c_memoryNuListProd
  apply List.prod_nonneg
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact h e he

private theorem pd5c_listMass_nonneg {K : ℕ} (F : PDFix K) (S : PDScale) (i : Fin K)
    (l : List Particle) (h : ∀ e ∈ l, 0 ≤ memoryNu S.x K F.a F.q_d i e.1) :
    0 ≤ pd5c_memoryNuListMass F S i l := by
  unfold pd5c_memoryNuListMass
  exact div_nonneg (pd5c_listProd_nonneg F S i l h) (by positivity)

private theorem pd5c_activeNuGroup_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (p : PrimeLists S.x K) (i : Fin K)
    (h : ∀ j, 0 ≤ memoryNu S.x K F.a F.q_d i (p i j)) :
    0 ≤ pd5c_activeNuGroup F S p i :=
  Finset.prod_nonneg fun j _ => h j

private theorem pd5c_groupWeight_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (hν : ∀ i, ∀ p ∈ primeBand S.x (F.a i), 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (s : MemPoint S.x K) (hs : MemValid F S s) (i : Fin K) :
    0 ≤ pd5c_memGroupWeight F S s i := by
  unfold pd5c_memGroupWeight
  apply mul_nonneg
  · exact pd5c_activeNuGroup_nonneg F S s.2.1 i fun j => hν i _ (hs.2.1 i j)
  · exact pd5c_listMass_nonneg F S i (s.2.2 i) fun e he => hν i _ (hs.2.2 i e he).1

theorem pd5c_memMeasure_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (hν : ∀ i, ∀ p ∈ primeBand S.x (F.a i), 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (s : MemPoint S.x K) : 0 ≤ memMeasure F S s := by
  by_cases hs : MemValid F S s
  · rw [pd5c_memMeasure_eq_groupProd F S s hs]
    exact Finset.prod_nonneg fun i _ => pd5c_groupWeight_nonneg F S hν s hs i
  · simp [memMeasure, hs]

/-- Reverse choice at a target state `t`: promoted groups store, stored groups promote the
last memory particle, other groups fill the source slot freshly with the source label. -/
def pd5c_revChoice {K : ℕ} (F : PDFix K) (S : PDScale) (t : MemPoint S.x K)
    (p : PrimeLists S.x K) (st pr : Fin K → Bool)
    (dflt : (i : Fin K) → EdgeChoice S.x F.a (t.2.2 i) i) (i : Fin K) :
    EdgeChoice S.x F.a (t.2.2 i) i :=
  (pr i,
    if h : st i = true ∧ 0 < (t.2.2 i).length then
      Sum.inl ⟨(t.2.2 i).length - 1, by omega⟩
    else if hp : p i (lastSlot S.x) ∈ primeBand S.x (F.a i) then
      Sum.inr ⟨p i (lastSlot S.x), hp⟩
    else (dflt i).2)

private theorem pd5c_edgeNewMemory_stored_length {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K)
    (hst : (c i).1 = true) :
    (edgeNewMemory F S s c i).length =
      (removeIndices (s.2.2 i) (pd5c_edgeRemovedIndices F S s c i)).length + 1 := by
  cases hk : (c i).2 with
  | inl k =>
      have hci : c i = (true, Sum.inl k) := by
        rw [← hst, ← hk]
      rw [pd5c_edgeNewMemory_inl F S s c i true k hci]
      simp [pd5c_edgeRemovedIndices, hk]
  | inr p =>
      have hci : c i = (true, Sum.inr p) := by
        rw [← hst, ← hk]
      rw [pd5c_edgeNewMemory_inr F S s c i true p hci]
      simp [pd5c_edgeRemovedIndices, hk, pd5c_removeIndices_empty]

private theorem pd5c_revChoice_eq {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ)
    (dflt : (i : Fin K) → EdgeChoice S.x F.a (edgeNewMemory F S s c i) i) :
    pd5c_revChoice F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c) s.2.1
        (fun i => (c i).1) (fun i => (c i).2.isLeft) dflt =
      pd5c_edgeReverseChoice F S s hs c := by
  funext i
  apply Prod.ext
  · rfl
  · cases hst : (c i).1 with
    | false =>
        have hn : ¬ ((c i).1 = true ∧
            0 < (edgeNewMemory F S s c i).length) := by
          rw [hst]; simp
        change (if h : (c i).1 = true ∧ 0 < (edgeNewMemory F S s c i).length then _
            else if hp : s.2.1 i (lastSlot S.x) ∈ primeBand S.x (F.a i) then
              Sum.inr ⟨s.2.1 i (lastSlot S.x), hp⟩ else (dflt i).2) =
          (pd5c_edgeReverseChoice F S s hs c i).2
        rw [dif_neg hn, dif_pos (hs.2.1 i (lastSlot S.x))]
        unfold pd5c_edgeReverseChoice
        simp [hst]
    | true =>
        have hlen := pd5c_edgeNewMemory_stored_length F S s c i hst
        have hy : (c i).1 = true ∧ 0 < (edgeNewMemory F S s c i).length := by
          refine ⟨hst, ?_⟩
          omega
        change (if h : (c i).1 = true ∧ 0 < (edgeNewMemory F S s c i).length then
              Sum.inl ⟨(edgeNewMemory F S s c i).length - 1, by omega⟩
            else _) = (pd5c_edgeReverseChoice F S s hs c i).2
        rw [dif_pos hy]
        unfold pd5c_edgeReverseChoice
        simp only [hst, dite_true]
        congr 1
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_last]
        omega



/-! ### Group weights of the reverse transition -/

private theorem pd5c_alg_FN (A At νq νp M C0 n : ℝ) (hact : A * νq = At * νp)
    (hY : 0 ≤ At * M * νp) (hC : 1 ≤ C0 * (n + 1)) :
    A * M * νq ≤ C0 * (n + 1) * (At * M) * νp := by
  have heq : A * M * νq = At * M * νp := by linear_combination M * hact
  rw [heq]
  calc At * M * νp = 1 * (At * M * νp) := by ring
    _ ≤ (C0 * (n + 1)) * (At * M * νp) := mul_le_mul_of_nonneg_right hC hY
    _ = _ := by ring

private theorem pd5c_alg_FS (A At νq νp Ms Mt V C0 n : ℝ) (hact : A * νq = At * νp)
    (hM : Mt * (n + 1) = Ms * νp) (hX : 0 ≤ A * Ms * νq) (hk : 1 ≤ C0 * V⁻¹) :
    A * Ms * νq ≤ C0 * (n + 1) * (At * Mt) * V⁻¹ := by
  have heq : C0 * (n + 1) * (At * Mt) * V⁻¹ = (C0 * V⁻¹) * (A * Ms * νq) := by
    linear_combination (C0 * V⁻¹ * At) * hM - (C0 * V⁻¹ * Ms) * hact
  rw [heq]
  calc A * Ms * νq = 1 * (A * Ms * νq) := by ring
    _ ≤ (C0 * V⁻¹) * (A * Ms * νq) := mul_le_mul_of_nonneg_right hk hX

private theorem pd5c_alg_PN (A At νq νp Ms Ml V C0 n : ℝ) (hact : A * νq = At * νp)
    (hMs : Ms ≤ Ml * νq) (hA : 0 ≤ A) (hVi : 0 ≤ V⁻¹) (hY : 0 ≤ At * Ml * νp)
    (hC : V⁻¹ ≤ C0 * (n + 1)) :
    A * Ms * V⁻¹ ≤ C0 * (n + 1) * (At * Ml) * νp := by
  calc A * Ms * V⁻¹ ≤ A * (Ml * νq) * V⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hVi
        exact mul_le_mul_of_nonneg_left hMs hA
    _ = V⁻¹ * (At * Ml * νp) := by linear_combination (Ml * V⁻¹) * hact
    _ ≤ (C0 * (n + 1)) * (At * Ml * νp) := mul_le_mul_of_nonneg_right hC hY
    _ = _ := by ring

private theorem pd5c_alg_PS (A At νq νp Ms Ml Mt V C0 m : ℝ) (hact : A * νq = At * νp)
    (hMs : Ms ≤ Ml * νq) (hM : Mt * (m + 1) = Ml * νp) (hA : 0 ≤ A) (hVi : 0 ≤ V⁻¹)
    (hY : 0 ≤ At * Mt * V⁻¹) (hC : m + 1 ≤ C0 * (m + 1 + 1)) :
    A * Ms * V⁻¹ ≤ C0 * (m + 1 + 1) * (At * Mt) * V⁻¹ := by
  calc A * Ms * V⁻¹ ≤ A * (Ml * νq) * V⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hVi
        exact mul_le_mul_of_nonneg_left hMs hA
    _ = (m + 1) * (At * Mt * V⁻¹) := by
        linear_combination (V⁻¹ * Ml) * hact - (V⁻¹ * At) * hM
    _ ≤ (C0 * (m + 1 + 1)) * (At * Mt * V⁻¹) := mul_le_mul_of_nonneg_right hC hY
    _ = _ := by ring

private theorem pd5c_revMass {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) (i : Fin K) :
    pd5_edgeChoiceMass F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
        (pd5c_edgeReverseChoice F S s hs c) i =
      if (c i).1 = true then (bandMass S.x (F.a i))⁻¹
      else memoryNu S.x K F.a F.q_d i (s.2.1 i (lastSlot S.x)) := by
  cases h : (c i).1 <;> simp [pd5_edgeChoiceMass, pd5c_edgeReverseChoice, h]

private theorem pd5c_get_last_of_eq (L X : List Particle) (a : Particle) (h : L = X ++ [a])
    (k : Fin L.length) (hk : k.val + 1 = L.length) : L.get k = a := by
  subst h
  have hkv : k.val = X.length := by simp at hk; omega
  rw [List.get_eq_getElem]
  rw [List.getElem_append_right (by omega)]
  simp [hkv]

private theorem pd5c_rev_get {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K)
    (k : Fin (edgeNewMemory F S s c i).length)
    (hk : (pd5c_edgeReverseChoice F S s hs c i).2 = Sum.inl k) :
    (edgeNewMemory F S s c i).get k = anchorAt (s.2.1 i (lastSlot S.x)) s.1 := by
  have hst : (c i).1 = true := by
    by_contra h
    have h' : (c i).1 = false := Bool.eq_false_of_not_eq_true h
    simp [pd5c_edgeReverseChoice, h'] at hk
  have hlen := pd5c_edgeNewMemory_stored_length F S s c i hst
  have hkval : k.val + 1 = (edgeNewMemory F S s c i).length := by
    unfold pd5c_edgeReverseChoice at hk
    simp only [hst, dite_true] at hk
    have hk' := Sum.inl.inj hk
    rw [← hk']
    simp only [Fin.val_cast, Fin.val_last]
    omega
  cases hc : (c i).2 with
  | inl k₀ =>
      have hci : c i = (true, Sum.inl k₀) := by rw [← hst, ← hc]
      have hmem := pd5c_edgeNewMemory_inl F S s c i true k₀ hci
      simp only [if_true] at hmem
      exact pd5c_get_last_of_eq _ _ _ hmem k hkval
  | inr p =>
      have hci : c i = (true, Sum.inr p) := by rw [← hst, ← hc]
      have hmem := pd5c_edgeNewMemory_inr F S s c i true p hci
      simp only [if_true] at hmem
      exact pd5c_get_last_of_eq _ _ _ hmem k hkval

private theorem pd5c_group_weight {K : ℕ} (F : PDFix K) (S : PDScale)
    (hν : ∀ i, ∀ p ∈ primeBand S.x (F.a i), 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ)
    (hvalidT : MemValid F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c))
    (hhit : ∀ i, ∀ k, (c i).2 = Sum.inl k → particleHits ((s.2.2 i).get k) z')
    (i : Fin K)
    (hVlow : Real.log 2 / 2 ≤ bandMass S.x (F.a i))
    (hVhigh : bandMass S.x (F.a i) ≤ 2 * Real.log 2) :
    pd5c_memGroupWeight F S s i * pd5_edgeChoiceMass F S s c i ≤
      (1 + 2 / Real.log 2 + 2 * Real.log 2) * ((s.2.2 i).length + 1 : ℕ) *
        pd5c_memGroupWeight F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c) i *
          pd5_edgeChoiceMass F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
            (pd5c_edgeReverseChoice F S s hs c) i := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hVpos : 0 < bandMass S.x (F.a i) := by linarith
  have hC0 : 1 ≤ 1 + 2 / Real.log 2 + 2 * Real.log 2 := by
    have h1 : 0 < 2 / Real.log 2 := div_pos (by norm_num) hlog
    linarith
  have hVC : bandMass S.x (F.a i) ≤ 1 + 2 / Real.log 2 + 2 * Real.log 2 := by
    have h1 : 0 < 2 / Real.log 2 := div_pos (by norm_num) hlog
    linarith
  have hVinvC : (bandMass S.x (F.a i))⁻¹ ≤ 1 + 2 / Real.log 2 + 2 * Real.log 2 := by
    have hinv : (bandMass S.x (F.a i))⁻¹ ≤ 2 / Real.log 2 := by
      rw [inv_le_comm₀ hVpos (div_pos (by norm_num) hlog)]
      rw [inv_div]
      linarith
    linarith
  have hVi : 0 ≤ (bandMass S.x (F.a i))⁻¹ := inv_nonneg.mpr hVpos.le
  have hlast : ¬ (lastSlot S.x).val < momentJ S.x := by
    dsimp [lastSlot]
    omega
  have hshared : ∀ j : Fin (slotCount S.x), j.val < momentJ S.x →
      s.2.1 i j = edgeTargetLists F S s c i j := by
    intro j hj
    simp [edgeTargetLists, hj]
  have hactRaw := pd5c_activeNuGroup_edge F S s.2.1 (edgeTargetLists F S s c) i hshared
  have htargetLast : edgeTargetLists F S s c i (lastSlot S.x) = edgeNewLabel (c i) := by
    simp [edgeTargetLists, hlast]
  rw [htargetLast] at hactRaw
  have hA : 0 ≤ pd5c_activeNuGroup F S s.2.1 i :=
    pd5c_activeNuGroup_nonneg F S s.2.1 i fun j => hν i _ (hs.2.1 i j)
  have hAt : 0 ≤ pd5c_activeNuGroup F S (edgeTargetLists F S s c) i :=
    pd5c_activeNuGroup_nonneg F S _ i fun j => hν i _ (hvalidT.2.1 i j)
  have hνp : 0 ≤ memoryNu S.x K F.a F.q_d i (s.2.1 i (lastSlot S.x)) :=
    hν i _ (hs.2.1 i (lastSlot S.x))
  have hνq : 0 ≤ memoryNu S.x K F.a F.q_d i (edgeNewLabel (c i)) := by
    rw [← htargetLast]
    exact hν i _ (hvalidT.2.1 i (lastSlot S.x))
  have hMs : 0 ≤ pd5c_memoryNuListMass F S i (s.2.2 i) :=
    pd5c_listMass_nonneg F S i _ fun e he => hν i _ (hs.2.2 i e he).1
  have hMt : 0 ≤ pd5c_memoryNuListMass F S i (edgeNewMemory F S s c i) :=
    pd5c_listMass_nonneg F S i _ fun e he => hν i _ (hvalidT.2.2 i e he).1
  have hrm := pd5c_revMass F S s hs c z' i
  change pd5c_activeNuGroup F S s.2.1 i * pd5c_memoryNuListMass F S i (s.2.2 i) *
      pd5_edgeChoiceMass F S s c i ≤
    (1 + 2 / Real.log 2 + 2 * Real.log 2) * ((s.2.2 i).length + 1 : ℕ) *
      (pd5c_activeNuGroup F S (edgeTargetLists F S s c) i *
        pd5c_memoryNuListMass F S i (edgeNewMemory F S s c i)) *
      pd5_edgeChoiceMass F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
        (pd5c_edgeReverseChoice F S s hs c) i
  rw [hrm]
  push_cast
  cases hci : c i with
  | mk stored choice =>
      have hst : (c i).1 = stored := by rw [hci]
      cases choice with
      | inr p =>
          have hms := pd5c_edgeChoiceMass_inr F S s c i p stored hci
          have hlab : edgeNewLabel (c i) = p.1 := by simp [edgeNewLabel, hci]
          rw [hms]
          rw [hlab] at hactRaw hνq
          have hmem := pd5c_edgeNewMemory_inr F S s c i stored p hci
          cases stored with
          | false =>
              simp only [hst, Bool.false_eq_true, if_false] at hmem ⊢
              simp only [List.append_nil] at hmem
              rw [hmem] at hMt ⊢
              have hY : 0 ≤ pd5c_activeNuGroup F S (edgeTargetLists F S s c) i *
                  pd5c_memoryNuListMass F S i (s.2.2 i) *
                    memoryNu S.x K F.a F.q_d i (s.2.1 i (lastSlot S.x)) := by positivity
              have hCn : 1 ≤ (1 + 2 / Real.log 2 + 2 * Real.log 2) *
                  (((s.2.2 i).length : ℝ) + 1) := by
                have : (1 : ℝ) ≤ ((s.2.2 i).length : ℝ) + 1 := by
                  have := Nat.cast_nonneg (α := ℝ) (s.2.2 i).length; linarith
                nlinarith
              exact pd5c_alg_FN _ _ _ _ _ _ _ hactRaw hY hCn
          | true =>
              simp only [hst, if_true] at hmem ⊢
              rw [hmem]
              have hM := pd5c_mass_append F S i (s.2.2 i)
                (anchorAt (s.2.1 i (lastSlot S.x)) s.1)
              have hX : 0 ≤ pd5c_activeNuGroup F S s.2.1 i *
                  pd5c_memoryNuListMass F S i (s.2.2 i) *
                    memoryNu S.x K F.a F.q_d i p.1 := by positivity
              have hk : 1 ≤ (1 + 2 / Real.log 2 + 2 * Real.log 2) *
                  (bandMass S.x (F.a i))⁻¹ := by
                rw [← div_eq_mul_inv]
                exact (one_le_div hVpos).mpr hVC
              exact pd5c_alg_FS _ _ _ _ _ _ _ _ _ hactRaw hM hX hk
      | inl k =>
          have hms := pd5c_edgeChoiceMass_inl F S s c i k stored hci
          have hlab : edgeNewLabel (c i) = ((s.2.2 i).get k).1 := by
            simp [edgeNewLabel, hci]
          rw [hms]
          rw [hlab] at hactRaw hνq
          have hmem := pd5c_edgeNewMemory_inl F S s c i stored k hci
          have hPl : 0 ≤ pd5c_memoryNuListProd F S i (removeIndices (s.2.2 i) {k}) :=
            pd5c_listProd_nonneg F S i _ fun e he =>
              hν i _ (hs.2.2 i e (pd5c_removeIndices_mem_of_mem _ he)).1
          have hMsl := pd5c_memoryNuListMass_remove_singleton_le F S i (s.2.2 i) k hPl hνq
          have hMl : 0 ≤ pd5c_memoryNuListMass F S i (removeIndices (s.2.2 i) {k}) :=
            pd5c_listMass_nonneg F S i _ fun e he =>
              hν i _ (hs.2.2 i e (pd5c_removeIndices_mem_of_mem _ he)).1
          have hlenR := pd5c_remove_singleton_length k
          cases stored with
          | false =>
              simp only [hst, Bool.false_eq_true, if_false] at hmem ⊢
              simp only [List.append_nil] at hmem
              rw [hmem]
              have hY : 0 ≤ pd5c_activeNuGroup F S (edgeTargetLists F S s c) i *
                  pd5c_memoryNuListMass F S i (removeIndices (s.2.2 i) {k}) *
                    memoryNu S.x K F.a F.q_d i (s.2.1 i (lastSlot S.x)) := by positivity
              have hCn : (bandMass S.x (F.a i))⁻¹ ≤ (1 + 2 / Real.log 2 + 2 * Real.log 2) *
                  (((s.2.2 i).length : ℝ) + 1) := by
                have h1 : (1 : ℝ) ≤ ((s.2.2 i).length : ℝ) + 1 := by
                  have := Nat.cast_nonneg (α := ℝ) (s.2.2 i).length; linarith
                calc (bandMass S.x (F.a i))⁻¹ ≤ 1 + 2 / Real.log 2 + 2 * Real.log 2 := hVinvC
                  _ = (1 + 2 / Real.log 2 + 2 * Real.log 2) * 1 := by ring
                  _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by linarith)
              exact pd5c_alg_PN _ _ _ _ _ _ _ _ _ hactRaw hMsl hA hVi hY hCn
          | true =>
              simp only [hst, if_true] at hmem ⊢
              rw [hmem]
              have hM := pd5c_mass_append F S i (removeIndices (s.2.2 i) {k})
                (anchorAt (s.2.1 i (lastSlot S.x)) s.1)
              have hMt' : 0 ≤ pd5c_memoryNuListMass F S i (removeIndices (s.2.2 i) {k} ++
                  [anchorAt (s.2.1 i (lastSlot S.x)) s.1]) := by
                rw [← hmem]; exact hMt
              have hY : 0 ≤ pd5c_activeNuGroup F S (edgeTargetLists F S s c) i *
                  pd5c_memoryNuListMass F S i (removeIndices (s.2.2 i) {k} ++
                    [anchorAt (s.2.1 i (lastSlot S.x)) s.1]) *
                    (bandMass S.x (F.a i))⁻¹ := by positivity
              have hlenC : (((removeIndices (s.2.2 i) {k}).length : ℝ) + 1 + 1) =
                  ((s.2.2 i).length : ℝ) + 1 := by
                have h : ((removeIndices (s.2.2 i) {k}).length : ℝ) + 1 =
                    ((s.2.2 i).length : ℝ) := by exact_mod_cast hlenR
                linarith
              have hCn : ((removeIndices (s.2.2 i) {k}).length : ℝ) + 1 ≤
                  (1 + 2 / Real.log 2 + 2 * Real.log 2) *
                    (((removeIndices (s.2.2 i) {k}).length : ℝ) + 1 + 1) := by
                have h0 := Nat.cast_nonneg (α := ℝ) (removeIndices (s.2.2 i) {k}).length
                nlinarith
              have hres := pd5c_alg_PS _ _ _ _ _ _ _ _ _ _ hactRaw hMsl hM hA hVi hY hCn
              rw [hlenC] at hres
              exact hres



/-! ### Reverse admissibility and the per-transition comparison -/

private theorem pd5c_rev_admissible {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (hdisj : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ)
    (hadm : EdgeAdmissible F S w s c z') :
    EdgeAdmissible F S w (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
      (pd5c_edgeReverseChoice F S s hs c) s.1 := by
  have hlists := pd5c_edgeReverse_targetLists F S s hs c z'
  rcases hadm with ⟨hhitF, hvalS, hvalT, hslot, hpad, hgcd', hboxS, hbox', hgoodS, hgoodT⟩
  unfold EdgeAdmissible
  rw [hlists]
  refine ⟨?_, hvalT, hvalS, ?_, ?_, hs.1, hbox', hboxS, hgoodT, hgoodS⟩
  · intro i k hk
    have hget := pd5c_rev_get F S s hs c i k hk
    change ((edgeNewMemory F S s c i).get k).2 =
      (projLine ((edgeNewMemory F S s c i).get k).1 s.1).val
    rw [hget]
    rfl
  · refine ⟨fun i j hj => (hslot.1 i j hj).symm, ?_⟩
    intro i i' j
    by_cases hj : j.val < momentJ S.x
    · change s.2.1 i (lastSlot S.x) ≠ edgeTargetLists F S s c i' j
      rw [hslot.1 i' j hj]
      by_cases hii : i = i'
      · subst hii
        apply hvalS.2 i (lastSlot S.x) j
        intro h
        have hne : ¬ (lastSlot S.x).val < momentJ S.x := by dsimp [lastSlot]; omega
        apply hne
        rw [h]
        exact hj
      · intro heq
        have h1 : s.2.1 i (lastSlot S.x) ∈ primeBand S.x (F.a i) :=
          (hvalS.1 i (lastSlot S.x)).2
        have h2 : s.2.1 i' j ∈ primeBand S.x (F.a i') := (hvalS.1 i' j).2
        rw [heq] at h1
        exact Finset.disjoint_left.mp (hdisj i i' hii) h1 h2
    · have hjl : j = lastSlot S.x := by
        apply Fin.ext
        have hlt : j.val < momentJ S.x + 1 := by simpa [slotCount] using j.isLt
        dsimp [lastSlot]
        omega
      subst hjl
      exact fun h => hslot.2 i' i (lastSlot S.x) h.symm
  · rcases hpad with ⟨h1, h2, hdvd⟩
    have hD : sharedProduct (edgeTargetLists F S s c) = sharedProduct s.2.1 :=
      pd5c_sharedProduct_eq _ _ fun i j hj => hslot.1 i j hj
    have hdet : det2 z' s.1 = -det2 s.1 z' := by unfold det2; ring
    refine ⟨?_, ?_, ?_⟩
    · change (S.d₀ : ℝ) ≤ (sharedProduct (edgeTargetLists F S s c) : ℝ)
      rw [hD]; exact h1
    · change (sharedProduct (edgeTargetLists F S s c) : ℝ) < 2 * (S.d₀ : ℝ)
      rw [hD]; exact h2
    · change ((sharedProduct (edgeTargetLists F S s c) : ℕ) : ℤ) ∣ det2 z' s.1
      rw [hD, hdet]
      exact (dvd_neg).mpr hdvd

/-- Positive raw-plus-comparison weight of one edge choice (as in the row proof). -/
def pd5c_edgeBase {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (j B : ℕ)
    (s : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (z' : ℤ × ℤ) : ℝ :=
  if EdgeAdmissible F S w s c z' ∧
      memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ B then
    |ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
      (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
        ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s c i) z')| *
      (‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
          (edgeTargetLists F S s c) s.1 z'‖ +
        ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
          (edgeTargetLists F S s c) s.1 z'‖)
  else 0

theorem pd5c_edgeBase_nonneg {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j B : ℕ) (s : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (z' : ℤ × ℤ) : 0 ≤ pd5c_edgeBase F S ρ w j B s c z' := by
  unfold pd5c_edgeBase
  split_ifs <;> positivity

private theorem pd5c_choiceMass_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (hν : ∀ i, ∀ p ∈ primeBand S.x (F.a i), 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hVpos : ∀ i, 0 < bandMass S.x (F.a i))
    (s : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
    0 ≤ pd5_edgeChoiceMass F S s c i := by
  cases hci : c i with
  | mk b ch =>
      cases ch with
      | inl k =>
          rw [pd5c_edgeChoiceMass_inl F S s c i k b hci]
          exact inv_nonneg.mpr (hVpos i).le
      | inr p =>
          rw [pd5c_edgeChoiceMass_inr F S s c i p b hci]
          exact hν i p.1 p.2

private theorem pd5c_measure_mass_le {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (B : ℕ)
    (hν : ∀ i, ∀ p ∈ primeBand S.x (F.a i), 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hV : ∀ i, Real.log 2 / 2 ≤ bandMass S.x (F.a i) ∧
      bandMass S.x (F.a i) ≤ 2 * Real.log 2)
    (s : MemPoint S.x K) (hs : MemValid F S s) (hsB : memSize s ≤ B)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ)
    (hadm : EdgeAdmissible F S w s c z') :
    memMeasure F S s * ∏ i : Fin K, pd5_edgeChoiceMass F S s c i ≤
      ((1 + 2 / Real.log 2 + 2 * Real.log 2) * ((B : ℝ) + 1)) ^ K *
        (memMeasure F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c) *
          ∏ i : Fin K, pd5_edgeChoiceMass F S
            (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
            (pd5c_edgeReverseChoice F S s hs c) i) := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hVpos : ∀ i, 0 < bandMass S.x (F.a i) := fun i => by linarith [(hV i).1]
  have hC0 : 0 ≤ 1 + 2 / Real.log 2 + 2 * Real.log 2 := by
    have h1 : 0 < 2 / Real.log 2 := div_pos (by norm_num) hlog
    linarith
  have hvalidT := pd5c_edge_output_valid F S w s hs c z' hadm
  rw [pd5c_memMeasure_eq_groupProd F S s hs, pd5c_memMeasure_eq_groupProd F S _ hvalidT,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  calc
    (∏ i : Fin K, pd5c_memGroupWeight F S s i * pd5_edgeChoiceMass F S s c i) ≤
        ∏ i : Fin K, ((1 + 2 / Real.log 2 + 2 * Real.log 2) * ((B : ℝ) + 1)) *
          (pd5c_memGroupWeight F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c) i *
            pd5_edgeChoiceMass F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
              (pd5c_edgeReverseChoice F S s hs c) i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (pd5c_groupWeight_nonneg F S hν s hs i)
          (pd5c_choiceMass_nonneg F S hν hVpos s c i)
      · intro i _
        have hg := pd5c_group_weight F S hν s hs c z' hvalidT hadm.1 i (hV i).1 (hV i).2
        have hlen : (s.2.2 i).length ≤ B := by
          have h1 : (s.2.2 i).length ≤ memSize s := by
            unfold memSize
            exact Finset.single_le_sum (f := fun j => (s.2.2 j).length)
              (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
          omega
        have hn : (((s.2.2 i).length + 1 : ℕ) : ℝ) ≤ (B : ℝ) + 1 := by
          have : ((s.2.2 i).length : ℝ) ≤ (B : ℝ) := by exact_mod_cast hlen
          push_cast
          linarith
        have hY : 0 ≤ pd5c_memGroupWeight F S
            (z', edgeTargetLists F S s c, edgeNewMemory F S s c) i *
            pd5_edgeChoiceMass F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
              (pd5c_edgeReverseChoice F S s hs c) i :=
          mul_nonneg (pd5c_groupWeight_nonneg F S hν _ hvalidT i)
            (pd5c_choiceMass_nonneg F S hν hVpos _ _ i)
        calc pd5c_memGroupWeight F S s i * pd5_edgeChoiceMass F S s c i ≤ _ := hg
          _ = ((1 + 2 / Real.log 2 + 2 * Real.log 2) *
                (((s.2.2 i).length + 1 : ℕ) : ℝ)) *
              (pd5c_memGroupWeight F S
                (z', edgeTargetLists F S s c, edgeNewMemory F S s c) i *
                pd5_edgeChoiceMass F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
                  (pd5c_edgeReverseChoice F S s hs c) i) := by ring
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ hY
            exact mul_le_mul_of_nonneg_left hn hC0
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem pd5c_term_le {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j j' B : ℕ) (hpar : decide (j' % 2 = 0) = !decide (j % 2 = 0))
    (hdisj : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (hν : ∀ i, ∀ p ∈ primeBand S.x (F.a i), 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hV : ∀ i, Real.log 2 / 2 ≤ bandMass S.x (F.a i) ∧
      bandMass S.x (F.a i) ≤ 2 * Real.log 2)
    (s : MemPoint S.x K) (hs : MemValid F S s) (hsB : memSize s ≤ B)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) :
    memMeasure F S s * pd5c_edgeBase F S ρ w j B s c z' ≤
      ((1 + 2 / Real.log 2 + 2 * Real.log 2) * ((B : ℝ) + 1)) ^ K *
        (memMeasure F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c) *
          pd5c_edgeBase F S ρ w j' B (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
            (pd5c_edgeReverseChoice F S s hs c) s.1) := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ 1 + 2 / Real.log 2 + 2 * Real.log 2 := by
    have h1 : 0 < 2 / Real.log 2 := div_pos (by norm_num) hlog
    linarith
  have hVpos : ∀ i, 0 < bandMass S.x (F.a i) := fun i => by linarith [(hV i).1]
  have hCK : 0 ≤ ((1 + 2 / Real.log 2 + 2 * Real.log 2) * ((B : ℝ) + 1)) ^ K := by
    positivity
  by_cases hfw : EdgeAdmissible F S w s c z' ∧
      memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ B
  · obtain ⟨hadm, htB⟩ := hfw
    have hrevAdm := pd5c_rev_admissible F S w hdisj s hs c z' hadm
    have hperm := pd5c_edgeReverse_memory_perm F S s hs c z' hadm.1
    have hlists := pd5c_edgeReverse_targetLists F S s hs c z'
    have hrsize : memSize (s.1,
        edgeTargetLists F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
          (pd5c_edgeReverseChoice F S s hs c),
        edgeNewMemory F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
          (pd5c_edgeReverseChoice F S s hs c)) = memSize s := by
      unfold memSize
      apply Finset.sum_congr rfl
      intro i _
      exact (hperm i).length_eq
    have hhits : (∑ i : Fin K, hitCount (edgeNewMemory F S
        (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
        (pd5c_edgeReverseChoice F S s hs c) i) s.1) =
        ∑ i : Fin K, hitCount (s.2.2 i) s.1 :=
      Finset.sum_congr rfl fun i _ => (hitCount_perm (hperm i) s.1).symm
    have hD : sharedProduct (edgeTargetLists F S s c) = sharedProduct s.2.1 :=
      pd5c_sharedProduct_eq _ _ fun i j hj => hadm.2.2.2.1.1 i j hj
    have hmult (raw : Bool) :
        ‖edgeMultiplier F S (decide (j' % 2 = 0)) raw (edgeTargetLists F S s c) s.2.1
            z' s.1‖ =
          ‖edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1 (edgeTargetLists F S s c)
            s.1 z'‖ := by
      rw [pd5c_edgeMult_norm_swap F S (decide (j' % 2 = 0)) raw _ _ z' s.1 hD, hpar,
        Bool.not_not]
    have hguard : EdgeAdmissible F S w (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
        (pd5c_edgeReverseChoice F S s hs c) s.1 ∧
        memSize (s.1,
          edgeTargetLists F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
            (pd5c_edgeReverseChoice F S s hs c),
          edgeNewMemory F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
            (pd5c_edgeReverseChoice F S s hs c)) ≤ B := ⟨hrevAdm, by rw [hrsize]; exact hsB⟩
    have hmass := pd5c_measure_mass_le F S w B hν hV s hs hsB c z' hadm
    unfold pd5c_edgeBase
    rw [if_pos ⟨hadm, htB⟩, if_pos hguard]
    dsimp only
    rw [hhits, hlists, hmult true, hmult false]
    set P := ∏ i : Fin K, pd5_edgeChoiceMass F S s c i with hP
    set P' := ∏ i : Fin K, pd5_edgeChoiceMass F S
      (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
      (pd5c_edgeReverseChoice F S s hs c) i with hP'
    set G := ‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
        (edgeTargetLists F S s c) s.1 z'‖ +
      ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
        (edgeTargetLists F S s c) s.1 z'‖ with hG
    set a := ∑ i : Fin K, hitCount (s.2.2 i) s.1 with ha
    set b := ∑ i : Fin K, hitCount (edgeNewMemory F S s c i) z' with hb
    have hPn : 0 ≤ P := Finset.prod_nonneg fun i _ => pd5c_choiceMass_nonneg F S hν hVpos s c i
    have hP'n : 0 ≤ P' := Finset.prod_nonneg fun i _ =>
      pd5c_choiceMass_nonneg F S hν hVpos _ _ i
    have hGn : 0 ≤ G := by positivity
    have hab1 : |ρ ^ a * P * ρ ^ b| = (|ρ ^ a| * |ρ ^ b|) * P := by
      rw [abs_mul, abs_mul, abs_of_nonneg hPn]; ring
    have hab2 : |ρ ^ b * P' * ρ ^ a| = (|ρ ^ a| * |ρ ^ b|) * P' := by
      rw [abs_mul, abs_mul, abs_of_nonneg hP'n]; ring
    rw [hab1, hab2]
    have hR : 0 ≤ (|ρ ^ a| * |ρ ^ b|) * G := by positivity
    calc memMeasure F S s * (|ρ ^ a| * |ρ ^ b| * P * G) =
          (memMeasure F S s * P) * ((|ρ ^ a| * |ρ ^ b|) * G) := by ring
      _ ≤ (((1 + 2 / Real.log 2 + 2 * Real.log 2) * ((B : ℝ) + 1)) ^ K *
            (memMeasure F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c) * P')) *
            ((|ρ ^ a| * |ρ ^ b|) * G) := mul_le_mul_of_nonneg_right hmass hR
      _ = _ := by ring
  · have hzero : pd5c_edgeBase F S ρ w j B s c z' = 0 := by
      unfold pd5c_edgeBase
      rw [if_neg hfw]
    rw [hzero, mul_zero]
    exact mul_nonneg hCK (mul_nonneg (pd5c_memMeasure_nonneg F S hν _)
      (pd5c_edgeBase_nonneg F S ρ w j' B _ _ _))

/-- Promotion indices of an edge choice (zero for fresh groups). -/
def pd5c_kvec {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {s : MemPoint x K}
    (c : (i : Fin K) → EdgeChoice x a (s.2.2 i) i) : Fin K → ℕ :=
  fun i => Sum.elim (fun k => k.val) (fun _ => 0) (c i).2

private theorem pd5c_term_le_at {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j j' B : ℕ) (hpar : decide (j' % 2 = 0) = !decide (j % 2 = 0))
    (hdisj : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (hν : ∀ i, ∀ p ∈ primeBand S.x (F.a i), 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hV : ∀ i, Real.log 2 / 2 ≤ bandMass S.x (F.a i) ∧
      bandMass S.x (F.a i) ≤ 2 * Real.log 2)
    (v : ℝ) (hv : 0 ≤ v) (z' : ℤ × ℤ) (q : PrimeLists S.x K) (M : Fin K → List Particle)
    (dflt : (i : Fin K) → EdgeChoice S.x F.a (M i) i)
    (s : MemPoint S.x K) (hs : MemValid F S s) (hsB : memSize s ≤ B)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (hq : edgeTargetLists F S s c = q) (hM : edgeNewMemory F S s c = M) :
    memMeasure F S s * pd5c_edgeBase F S ρ w j B s c z' * v ^ memSize s ≤
      ((1 + 2 / Real.log 2 + 2 * Real.log 2) * ((B : ℝ) + 1)) ^ K *
        memMeasure F S (z', q, M) *
        (pd5c_edgeBase F S ρ w j' B (z', q, M)
            (pd5c_revChoice F S (z', q, M) s.2.1 (fun i => (c i).1)
              (fun i => (c i).2.isLeft) dflt) s.1 *
          v ^ memSize (s.1, edgeTargetLists F S (z', q, M)
              (pd5c_revChoice F S (z', q, M) s.2.1 (fun i => (c i).1)
                (fun i => (c i).2.isLeft) dflt),
            edgeNewMemory F S (z', q, M)
              (pd5c_revChoice F S (z', q, M) s.2.1 (fun i => (c i).1)
                (fun i => (c i).2.isLeft) dflt))) := by
  subst hq hM
  rw [pd5c_revChoice_eq F S s hs c z' dflt]
  have hterm := pd5c_term_le F S ρ w j j' B hpar hdisj hν hV s hs hsB c z'
  by_cases hadm : EdgeAdmissible F S w s c z'
  · have hperm := pd5c_edgeReverse_memory_perm F S s hs c z' hadm.1
    have hrsize : memSize (s.1,
        edgeTargetLists F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
          (pd5c_edgeReverseChoice F S s hs c),
        edgeNewMemory F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
          (pd5c_edgeReverseChoice F S s hs c)) = memSize s := by
      unfold memSize
      apply Finset.sum_congr rfl
      intro i _
      exact (hperm i).length_eq
    rw [hrsize]
    have hvn : 0 ≤ v ^ memSize s := pow_nonneg hv _
    calc memMeasure F S s * pd5c_edgeBase F S ρ w j B s c z' * v ^ memSize s ≤
          (((1 + 2 / Real.log 2 + 2 * Real.log 2) * ((B : ℝ) + 1)) ^ K *
            (memMeasure F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c) *
              pd5c_edgeBase F S ρ w j' B (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
                (pd5c_edgeReverseChoice F S s hs c) s.1)) * v ^ memSize s :=
        mul_le_mul_of_nonneg_right hterm hvn
      _ = _ := by ring
  · have hzero : pd5c_edgeBase F S ρ w j B s c z' = 0 := by
      unfold pd5c_edgeBase
      rw [if_neg (fun h => hadm h.1)]
    rw [hzero, mul_zero, zero_mul]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hC0 : 0 ≤ 1 + 2 / Real.log 2 + 2 * Real.log 2 := by
      have h1 : 0 < 2 / Real.log 2 := div_pos (by norm_num) hlog
      linarith
    have hCK : 0 ≤ ((1 + 2 / Real.log 2 + 2 * Real.log 2) * ((B : ℝ) + 1)) ^ K := by
      positivity
    exact mul_nonneg (mul_nonneg hCK (pd5c_memMeasure_nonneg F S hν _))
      (mul_nonneg (pd5c_edgeBase_nonneg F S ρ w j' B _ _ _) (pow_nonneg hv _))



/-! ### Injectivity of the reverse parametrization -/

private theorem pd5c_stored_mem {K : ℕ} (F : PDFix K) (S : PDScale) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) (h : (c i).1 = true) :
    ∃ X : List Particle, edgeNewMemory F S s c i =
      X ++ [anchorAt (s.2.1 i (lastSlot S.x)) s.1] := by
  cases hk : (c i).2 with
  | inl k =>
      have hci : c i = (true, Sum.inl k) := by rw [← h, ← hk]
      refine ⟨removeIndices (s.2.2 i) {k}, ?_⟩
      rw [pd5c_edgeNewMemory_inl F S s c i true k hci]
      simp
  | inr p =>
      have hci : c i = (true, Sum.inr p) := by rw [← h, ← hk]
      refine ⟨s.2.2 i, ?_⟩
      rw [pd5c_edgeNewMemory_inr F S s c i true p hci]
      simp

private theorem pd5c_promoted_anchor {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ)
    (i : Fin K) (k : Fin (s.2.2 i).length) (hc : (c i).2 = Sum.inl k)
    (hhit : particleHits ((s.2.2 i).get k) z') :
    (s.2.2 i).get k = anchorAt (edgeTargetLists F S s c i (lastSlot S.x)) z' := by
  have hlastn : ¬ (lastSlot S.x).val < momentJ S.x := by dsimp [lastSlot]; omega
  have hl : edgeTargetLists F S s c i (lastSlot S.x) = ((s.2.2 i).get k).1 := by
    simp [edgeTargetLists, hlastn, edgeNewLabel, hc]
  rw [hl]
  apply Prod.ext
  · rfl
  · exact hhit

private theorem pd5c_inj {K : ℕ} (F : PDFix K) (S : PDScale)
    (z' : ℤ × ℤ) (q : PrimeLists S.x K) (M : Fin K → List Particle)
    (dflt : (i : Fin K) → EdgeChoice S.x F.a (M i) i)
    (s₁ s₂ : MemPoint S.x K) (hs₁ : MemValid F S s₁) (hs₂ : MemValid F S s₂)
    (c₁ : (i : Fin K) → EdgeChoice S.x F.a (s₁.2.2 i) i)
    (c₂ : (i : Fin K) → EdgeChoice S.x F.a (s₂.2.2 i) i)
    (hhit₁ : ∀ i, ∀ k, (c₁ i).2 = Sum.inl k → particleHits ((s₁.2.2 i).get k) z')
    (hhit₂ : ∀ i, ∀ k, (c₂ i).2 = Sum.inl k → particleHits ((s₂.2.2 i).get k) z')
    (hq₁ : edgeTargetLists F S s₁ c₁ = q) (hq₂ : edgeTargetLists F S s₂ c₂ = q)
    (hM₁ : edgeNewMemory F S s₁ c₁ = M) (hM₂ : edgeNewMemory F S s₂ c₂ = M)
    (hrc : pd5c_revChoice F S (z', q, M) s₁.2.1 (fun i => (c₁ i).1)
        (fun i => (c₁ i).2.isLeft) dflt =
      pd5c_revChoice F S (z', q, M) s₂.2.1 (fun i => (c₂ i).1)
        (fun i => (c₂ i).2.isLeft) dflt)
    (hz : s₁.1 = s₂.1) (hk : pd5c_kvec c₁ = pd5c_kvec c₂) :
    (⟨s₁, c₁⟩ : (s : MemPoint S.x K) × ((i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)) =
      ⟨s₂, c₂⟩ := by
  classical
  have hlastn : ¬ (lastSlot S.x).val < momentJ S.x := by dsimp [lastSlot]; omega
  have hpr : ∀ i, (c₁ i).2.isLeft = (c₂ i).2.isLeft := fun i =>
    congrArg Prod.fst (congrFun hrc i)
  have hsnd := fun i => congrArg Prod.snd (congrFun hrc i)
  have hlenpos₁ : ∀ i, (c₁ i).1 = true → 0 < (M i).length := by
    intro i h
    rw [← hM₁]
    have := pd5c_edgeNewMemory_stored_length F S s₁ c₁ i h
    omega
  have hlenpos₂ : ∀ i, (c₂ i).1 = true → 0 < (M i).length := by
    intro i h
    rw [← hM₂]
    have := pd5c_edgeNewMemory_stored_length F S s₂ c₂ i h
    omega
  have hst : ∀ i, (c₁ i).1 = (c₂ i).1 := by
    intro i
    have h := hsnd i
    unfold pd5c_revChoice at h
    cases h₁ : (c₁ i).1 <;> cases h₂ : (c₂ i).1
    · rfl
    · exfalso
      have hl := hlenpos₂ i h₂
      simp [h₁, h₂, hl, hs₁.2.1 i (lastSlot S.x)] at h
    · exfalso
      have hl := hlenpos₁ i h₁
      simp [h₁, h₂, hl, hs₂.2.1 i (lastSlot S.x)] at h
    · rfl
  have hlast : ∀ i, s₁.2.1 i (lastSlot S.x) = s₂.2.1 i (lastSlot S.x) := by
    intro i
    cases h₁ : (c₁ i).1
    · have h₂ : (c₂ i).1 = false := by rw [← hst i]; exact h₁
      have h := hsnd i
      unfold pd5c_revChoice at h
      simp [h₁, h₂, hs₁.2.1 i (lastSlot S.x), hs₂.2.1 i (lastSlot S.x)] at h
      exact h
    · have h₂ : (c₂ i).1 = true := by rw [← hst i]; exact h₁
      obtain ⟨X₁, e₁⟩ := pd5c_stored_mem F S s₁ c₁ i h₁
      obtain ⟨X₂, e₂⟩ := pd5c_stored_mem F S s₂ c₂ i h₂
      rw [hM₁] at e₁
      rw [hM₂] at e₂
      have h12 := e₁.symm.trans e₂
      have hsing := (List.append_inj' h12 rfl).2
      have ha := List.singleton_inj.mp hsing
      have := congrArg Prod.fst ha
      simpa [anchorAt] using this
  have hact : s₁.2.1 = s₂.2.1 := by
    funext i j
    by_cases hj : j.val < momentJ S.x
    · have e1 := congrFun (congrFun hq₁ i) j
      have e2 := congrFun (congrFun hq₂ i) j
      simp only [edgeTargetLists, hj, if_true] at e1 e2
      rw [e1, e2]
    · have hjl : j = lastSlot S.x := by
        apply Fin.ext
        have hlt : j.val < momentJ S.x + 1 := by simpa [slotCount] using j.isLt
        dsimp [lastSlot]
        omega
      subst hjl
      exact hlast i
  have hmem : s₁.2.2 = s₂.2.2 := by
    funext i
    have hX : (if (c₁ i).1 then [anchorAt (s₁.2.1 i (lastSlot S.x)) s₁.1] else []) =
        (if (c₂ i).1 then [anchorAt (s₂.2.1 i (lastSlot S.x)) s₂.1] else []) := by
      rw [hst i, hlast i, hz]
    cases hc₁ : (c₁ i).2 with
    | inr p₁ =>
        cases hc₂ : (c₂ i).2 with
        | inl k₂ =>
            exfalso
            have := hpr i
            rw [hc₁, hc₂] at this
            simp at this
        | inr p₂ =>
            have e₁ := pd5c_edgeNewMemory_inr F S s₁ c₁ i (c₁ i).1 p₁ (Prod.ext rfl hc₁)
            have e₂ := pd5c_edgeNewMemory_inr F S s₂ c₂ i (c₂ i).1 p₂ (Prod.ext rfl hc₂)
            rw [hM₁] at e₁
            rw [hM₂] at e₂
            rw [hX] at e₁
            exact List.append_cancel_right (e₁.symm.trans e₂)
    | inl k₁ =>
        cases hc₂ : (c₂ i).2 with
        | inr p₂ =>
            exfalso
            have := hpr i
            rw [hc₁, hc₂] at this
            simp at this
        | inl k₂ =>
            have hkv : k₁.val = k₂.val := by
              have := congrFun hk i
              simp only [pd5c_kvec, hc₁, hc₂, Sum.elim_inl] at this
              exact this
            have e₁ := pd5c_edgeNewMemory_inl F S s₁ c₁ i (c₁ i).1 k₁ (Prod.ext rfl hc₁)
            have e₂ := pd5c_edgeNewMemory_inl F S s₂ c₂ i (c₂ i).1 k₂ (Prod.ext rfl hc₂)
            rw [hM₁] at e₁
            rw [hM₂] at e₂
            rw [hX] at e₁
            have hrem := List.append_cancel_right (e₁.symm.trans e₂)
            have hg₁ := pd5c_promoted_anchor F S s₁ c₁ z' i k₁ hc₁ (hhit₁ i k₁ hc₁)
            have hg₂ := pd5c_promoted_anchor F S s₂ c₂ z' i k₂ hc₂ (hhit₂ i k₂ hc₂)
            rw [hq₁] at hg₁
            rw [hq₂] at hg₂
            exact pd5c_list_eq_of_remove k₁ k₂ hkv hrem (hg₁.trans hg₂.symm)
  have hs : s₁ = s₂ := Prod.ext hz (Prod.ext hact hmem)
  subst hs
  have hc : c₁ = c₂ := by
    funext i
    apply Prod.ext (hst i)
    cases hc₁ : (c₁ i).2 with
    | inl k₁ =>
        cases hc₂ : (c₂ i).2 with
        | inl k₂ =>
            congr 1
            apply Fin.ext
            have := congrFun hk i
            simp only [pd5c_kvec, hc₁, hc₂, Sum.elim_inl] at this
            exact this
        | inr p₂ =>
            exfalso
            have := hpr i
            rw [hc₁, hc₂] at this
            simp at this
    | inr p₁ =>
        cases hc₂ : (c₂ i).2 with
        | inl k₂ =>
            exfalso
            have := hpr i
            rw [hc₁, hc₂] at this
            simp at this
        | inr p₂ =>
            congr 1
            apply Subtype.ext
            have e1 := congrFun (congrFun hq₁ i) (lastSlot S.x)
            have e2 := congrFun (congrFun hq₂ i) (lastSlot S.x)
            simp [edgeTargetLists, hlastn, edgeNewLabel, hc₁, hc₂] at e1 e2
            rw [e1, e2]
  subst hc
  rfl

/-! ### The column comparison with the reverse row -/

private theorem pd5c_sum_single_le {α : Type*} [DecidableEq α] (Z : Finset α) (z₀ : α)
    (f : α → ℝ) (hf : ∀ z, 0 ≤ f z) (hzero : ∀ z, z ≠ z₀ → f z = 0) :
    ∑ z ∈ Z, f z ≤ f z₀ := by
  by_cases hz : z₀ ∈ Z
  · rw [Finset.sum_eq_single z₀ (fun b _ hb => hzero b hb) (fun h => (h hz).elim)]
  · rw [Finset.sum_eq_zero (fun b hb => hzero b (fun h => hz (h ▸ hb)))]
    exact hf z₀

theorem pd5c_column_core {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j j' B : ℕ) (hpar : decide (j' % 2 = 0) = !decide (j % 2 = 0))
    (hdisj : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (hν : ∀ i, ∀ p ∈ primeBand S.x (F.a i), 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hV : ∀ i, Real.log 2 / 2 ≤ bandMass S.x (F.a i) ∧
      bandMass S.x (F.a i) ≤ 2 * Real.log 2)
    (v : ℝ) (hv : 0 ≤ v) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z, envBox S w z → z ∈ Z)
    (T : Finset (MemPoint S.x K)) (hT : ∀ s ∈ T, memSize s ≤ B)
    (u : MemPoint S.x K) :
    (∑ s ∈ T, memMeasure F S s *
      (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i, ∑ z' ∈ Z,
        pd5c_edgeBase F S ρ w j B s c z' *
          (if (z', edgeTargetLists F S s c, edgeNewMemory F S s c) = u then (1 : ℝ) else 0)) *
      v ^ memSize s) ≤
    ((1 + 2 / Real.log 2 + 2 * Real.log 2) * ((B : ℝ) + 1)) ^ K * ((B : ℝ) + 1) ^ K *
      memMeasure F S u *
      ∑ rc : (i : Fin K) → EdgeChoice S.x F.a (u.2.2 i) i, ∑ z ∈ Z,
        pd5c_edgeBase F S ρ w j' B u rc z *
          v ^ memSize (z, edgeTargetLists F S u rc, edgeNewMemory F S u rc) := by
  classical
  obtain ⟨zu, q, M⟩ := u
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ 1 + 2 / Real.log 2 + 2 * Real.log 2 := by
    have h1 : 0 < 2 / Real.log 2 := div_pos (by norm_num) hlog
    linarith
  set C : ℝ := ((1 + 2 / Real.log 2 + 2 * Real.log 2) * ((B : ℝ) + 1)) ^ K with hCdef
  have hCn : 0 ≤ C := by positivity
  let Ch := fun s : MemPoint S.x K => (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i
  let Fx : (Σ s : MemPoint S.x K, Ch s) → ℝ := fun x =>
    memMeasure F S x.1 *
      (pd5c_edgeBase F S ρ w j B x.1 x.2 zu *
        (if (zu, edgeTargetLists F S x.1 x.2, edgeNewMemory F S x.1 x.2) = (zu, q, M)
          then (1 : ℝ) else 0)) * v ^ memSize x.1
  have hFx_nonneg : ∀ x, 0 ≤ Fx x := by
    intro x
    have h1 := pd5c_memMeasure_nonneg F S hν x.1
    have h2 := pd5c_edgeBase_nonneg F S ρ w j B x.1 x.2 zu
    have h3 : (0 : ℝ) ≤ (if (zu, edgeTargetLists F S x.1 x.2, edgeNewMemory F S x.1 x.2) =
        (zu, q, M) then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    exact mul_nonneg (mul_nonneg h1 (mul_nonneg h2 h3)) (pow_nonneg hv _)
  -- Step 1: collapse the position sum.
  have hstep1 : (∑ s ∈ T, memMeasure F S s *
      (∑ c : Ch s, ∑ z' ∈ Z,
        pd5c_edgeBase F S ρ w j B s c z' *
          (if (z', edgeTargetLists F S s c, edgeNewMemory F S s c) = (zu, q, M)
            then (1 : ℝ) else 0)) * v ^ memSize s) ≤
      ∑ x ∈ T.sigma (fun s => (Finset.univ : Finset (Ch s))), Fx x := by
    rw [Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro s hs
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro c _
    have hcol : (∑ z' ∈ Z, pd5c_edgeBase F S ρ w j B s c z' *
        (if (z', edgeTargetLists F S s c, edgeNewMemory F S s c) = (zu, q, M)
          then (1 : ℝ) else 0)) ≤
        pd5c_edgeBase F S ρ w j B s c zu *
          (if (zu, edgeTargetLists F S s c, edgeNewMemory F S s c) = (zu, q, M)
            then (1 : ℝ) else 0) := by
      apply pd5c_sum_single_le Z zu
        (fun z' => pd5c_edgeBase F S ρ w j B s c z' *
          (if (z', edgeTargetLists F S s c, edgeNewMemory F S s c) = (zu, q, M)
            then (1 : ℝ) else 0))
      · intro z'
        apply mul_nonneg (pd5c_edgeBase_nonneg F S ρ w j B s c z')
        split_ifs <;> norm_num
      · intro z' hz'
        have hne : (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≠ (zu, q, M) := by
          intro h
          exact hz' (congrArg Prod.fst h)
        simp [hne]
    have hμ := pd5c_memMeasure_nonneg F S hν s
    calc memMeasure F S s * (∑ z' ∈ Z, pd5c_edgeBase F S ρ w j B s c z' *
          (if (z', edgeTargetLists F S s c, edgeNewMemory F S s c) = (zu, q, M)
            then (1 : ℝ) else 0)) * v ^ memSize s ≤
        memMeasure F S s * (pd5c_edgeBase F S ρ w j B s c zu *
          (if (zu, edgeTargetLists F S s c, edgeNewMemory F S s c) = (zu, q, M)
            then (1 : ℝ) else 0)) * v ^ memSize s := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hv _)
          exact mul_le_mul_of_nonneg_left hcol hμ
      _ = Fx ⟨s, c⟩ := rfl
  refine hstep1.trans ?_
  -- Step 2: restrict to the support.
  let A := (T.sigma (fun s => (Finset.univ : Finset (Ch s)))).filter
    (fun x => MemValid F S x.1 ∧ EdgeAdmissible F S w x.1 x.2 zu ∧
      edgeTargetLists F S x.1 x.2 = q ∧ edgeNewMemory F S x.1 x.2 = M)
  have hsupp : ∀ x ∈ T.sigma (fun s => (Finset.univ : Finset (Ch s))), Fx x ≠ 0 →
      (MemValid F S x.1 ∧ EdgeAdmissible F S w x.1 x.2 zu ∧
        edgeTargetLists F S x.1 x.2 = q ∧ edgeNewMemory F S x.1 x.2 = M) := by
    intro x _ hx
    by_contra hnot
    apply hx
    by_cases hval : MemValid F S x.1
    · by_cases hadm : EdgeAdmissible F S w x.1 x.2 zu
      · by_cases htar : edgeTargetLists F S x.1 x.2 = q ∧ edgeNewMemory F S x.1 x.2 = M
        · exact (hnot ⟨hval, hadm, htar⟩).elim
        · have hne : (zu, edgeTargetLists F S x.1 x.2, edgeNewMemory F S x.1 x.2) ≠
              (zu, q, M) := by
            intro h
            apply htar
            have h2 := congrArg Prod.snd h
            exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
          simp only [Fx, hne, if_false, mul_zero, zero_mul]
      · have hb : pd5c_edgeBase F S ρ w j B x.1 x.2 zu = 0 := by
          unfold pd5c_edgeBase
          rw [if_neg (fun h => hadm h.1)]
        simp only [Fx, hb, zero_mul, mul_zero]
    · have hm : memMeasure F S x.1 = 0 := by simp [memMeasure, hval]
      simp only [Fx, hm, zero_mul]
  rw [← Finset.sum_filter_of_ne hsupp]
  change ∑ x ∈ A, Fx x ≤ _
  -- Step 3: an empty reverse choice space forces an empty support.
  rcases isEmpty_or_nonempty ((i : Fin K) → EdgeChoice S.x F.a (M i) i) with hE | hNE
  · have hA : A = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨_, hval, _, _, hM⟩ := Finset.mem_filter.mp hx
      have rc := pd5c_edgeReverseChoice F S x.1 hval x.2
      rw [hM] at rc
      exact hE.false rc
    rw [hA, Finset.sum_empty]
    apply mul_nonneg (mul_nonneg (mul_nonneg hCn (by positivity))
      (pd5c_memMeasure_nonneg F S hν _))
    apply Finset.sum_nonneg
    intro rc _
    apply Finset.sum_nonneg
    intro z _
    exact mul_nonneg (pd5c_edgeBase_nonneg F S ρ w j' B _ _ _) (pow_nonneg hv _)
  · let dflt : (i : Fin K) → EdgeChoice S.x F.a (M i) i := Classical.arbitrary _
    let Rc := (i : Fin K) → EdgeChoice S.x F.a (((zu, q, M) : MemPoint S.x K).2.2 i) i
    let φ : (Σ s : MemPoint S.x K, Ch s) → Rc × (ℤ × ℤ) × (Fin K → ℕ) := fun x =>
      (pd5c_revChoice F S (zu, q, M) x.1.2.1 (fun i => (x.2 i).1)
        (fun i => (x.2 i).2.isLeft) dflt, x.1.1, pd5c_kvec x.2)
    let g : Rc × (ℤ × ℤ) × (Fin K → ℕ) → ℝ := fun y =>
      C * memMeasure F S (zu, q, M) *
        (pd5c_edgeBase F S ρ w j' B (zu, q, M) y.1 y.2.1 *
          v ^ memSize (y.2.1, edgeTargetLists F S (zu, q, M) y.1,
            edgeNewMemory F S (zu, q, M) y.1))
    let Y : Finset (Rc × (ℤ × ℤ) × (Fin K → ℕ)) :=
      (Finset.univ : Finset Rc) ×ˢ (Z ×ˢ Fintype.piFinset (fun _ : Fin K => Finset.range (B + 1)))
    have hg_nonneg : ∀ y, 0 ≤ g y := by
      intro y
      exact mul_nonneg (mul_nonneg hCn (pd5c_memMeasure_nonneg F S hν _))
        (mul_nonneg (pd5c_edgeBase_nonneg F S ρ w j' B _ _ _) (pow_nonneg hv _))
    have hInj : Set.InjOn φ A := by
      intro x₁ hx₁ x₂ hx₂ hφ
      obtain ⟨_, hval₁, hadm₁, hq₁, hM₁⟩ := Finset.mem_filter.mp hx₁
      obtain ⟨_, hval₂, hadm₂, hq₂, hM₂⟩ := Finset.mem_filter.mp hx₂
      obtain ⟨s₁, c₁⟩ := x₁
      obtain ⟨s₂, c₂⟩ := x₂
      have h1 := congrArg Prod.fst hφ
      have h2 := congrArg (fun y => y.2.1) hφ
      have h3 := congrArg (fun y => y.2.2) hφ
      exact pd5c_inj F S zu q M dflt s₁ s₂ hval₁ hval₂ c₁ c₂ hadm₁.1 hadm₂.1 hq₁ hq₂ hM₁ hM₂
        h1 h2 h3
    have hImg : A.image φ ⊆ Y := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxT, hval, hadm, hq, hM⟩ := Finset.mem_filter.mp hx
      have hsB : memSize x.1 ≤ B := hT x.1 (Finset.mem_sigma.mp hxT).1
      refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact hZ _ hadm.2.2.2.2.2.2.1
      · rw [Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_range]
        change Sum.elim (fun k => k.val) (fun _ => 0) (x.2 i).2 < B + 1
        cases hci : (x.2 i).2 with
        | inl k =>
            have hlen : (x.1.2.2 i).length ≤ memSize x.1 := by
              unfold memSize
              exact Finset.single_le_sum (f := fun j => (x.1.2.2 j).length)
                (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
            simp only [Sum.elim_inl]
            have := k.isLt
            omega
        | inr p =>
            simp only [Sum.elim_inr]
            omega
    have hle : ∀ x ∈ A, Fx x ≤ g (φ x) := by
      intro x hx
      obtain ⟨hxT, hval, hadm, hq, hM⟩ := Finset.mem_filter.mp hx
      have hsB : memSize x.1 ≤ B := hT x.1 (Finset.mem_sigma.mp hxT).1
      have hind : (zu, edgeTargetLists F S x.1 x.2, edgeNewMemory F S x.1 x.2) =
          ((zu, q, M) : MemPoint S.x K) := by rw [hq, hM]
      have hterm := pd5c_term_le_at F S ρ w j j' B hpar hdisj hν hV v hv zu q M dflt
        x.1 hval hsB x.2 hq hM
      change memMeasure F S x.1 *
          (pd5c_edgeBase F S ρ w j B x.1 x.2 zu *
            (if (zu, edgeTargetLists F S x.1 x.2, edgeNewMemory F S x.1 x.2) = (zu, q, M)
              then (1 : ℝ) else 0)) * v ^ memSize x.1 ≤ _
      rw [if_pos hind, mul_one]
      exact hterm
    have hmain := Finset.sum_le_sum_of_injOn φ hInj hImg hle
      (fun y _ _ => hg_nonneg y)
    refine hmain.trans (le_of_eq ?_)
    rw [Finset.sum_product]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rc _
    rw [Finset.sum_product]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    simp only [g]
    rw [Finset.sum_const, Fintype.card_piFinset]
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring



/-! ### Memory-permutation facts used by the column assembly -/

private theorem pd5c_list_perm_inv (l l' : List Particle) (σ : Equiv.Perm (Fin l.length))
    (c : Fin l.length ≃ Fin l'.length) (hc : ∀ k, (c k).val = k.val)
    (h : List.ofFn (fun j => l.get (σ j)) = l') :
    List.ofFn (fun k => l'.get (((c.symm.trans σ.symm).trans c) k)) = l := by
  subst h
  have hcs : ∀ k, (c.symm k).val = k.val := by
    intro k
    have := hc (c.symm k)
    simp only [Equiv.apply_symm_apply] at this
    omega
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [List.getElem_ofFn, hc, hcs]

theorem pd5c_memorySym_delta_symm {x : ℝ} {K : ℕ} (u t : MemPoint x K) :
    memorySym (fun g => if g = t then (1 : ℂ) else 0) u =
      memorySym (fun g => if g = u then (1 : ℂ) else 0) t := by
  classical
  unfold memorySym
  by_cases hl : ∀ i, (u.2.2 i).length = (t.2.2 i).length
  · let c : ∀ i, Fin (u.2.2 i).length ≃ Fin (t.2.2 i).length := fun i => finCastEquiv (hl i)
    have hc : ∀ i k, ((c i) k).val = k.val := fun i k => rfl
    have hcs : ∀ i k, ((c i).symm k).val = k.val := fun i k => rfl
    let E : MemoryPermutation u ≃ MemoryPermutation t := Equiv.piCongrRight fun i =>
      { toFun := fun σ => ((c i).symm.trans σ.symm).trans (c i)
        invFun := fun τ => ((c i).trans τ.symm).trans (c i).symm
        left_inv := by intro σ; ext k; simp
        right_inv := by intro τ; ext k; simp }
    have hE : ∀ σ i, E σ i = ((c i).symm.trans (σ i).symm).trans (c i) := fun σ i => rfl
    have hcard : Fintype.card (MemoryPermutation u) = Fintype.card (MemoryPermutation t) :=
      Fintype.card_congr E
    rw [hcard]
    congr 1
    apply Fintype.sum_equiv E
    intro σ
    have hiff : memoryPermute u σ = t ↔ memoryPermute t (E σ) = u := by
      constructor
      · intro h
        have h1 : (memoryPermute u σ).1 = t.1 := congrArg Prod.fst h
        have h2 : (memoryPermute u σ).2.1 = t.2.1 := congrArg (fun p => p.2.1) h
        have h3 : ∀ i, (memoryPermute u σ).2.2 i = t.2.2 i :=
          fun i => congrFun (congrArg (fun p => p.2.2) h) i
        refine Prod.ext h1.symm (Prod.ext h2.symm (funext fun i => ?_))
        change List.ofFn (fun k => (t.2.2 i).get (E σ i k)) = u.2.2 i
        rw [hE]
        exact pd5c_list_perm_inv (u.2.2 i) (t.2.2 i) (σ i) (c i) (hc i) (h3 i)
      · intro h
        have h1 : (memoryPermute t (E σ)).1 = u.1 := congrArg Prod.fst h
        have h2 : (memoryPermute t (E σ)).2.1 = u.2.1 := congrArg (fun p => p.2.1) h
        have h3 : ∀ i, (memoryPermute t (E σ)).2.2 i = u.2.2 i :=
          fun i => congrFun (congrArg (fun p => p.2.2) h) i
        refine Prod.ext h1.symm (Prod.ext h2.symm (funext fun i => ?_))
        have hinv := pd5c_list_perm_inv (t.2.2 i) (u.2.2 i) (E σ i) (c i).symm (hcs i) (h3 i)
        have heq : (((c i).symm.symm.trans (E σ i).symm).trans (c i).symm) = σ i := by
          rw [hE]
          ext k
          simp
        rw [heq] at hinv
        exact hinv
    dsimp only
    by_cases h : memoryPermute u σ = t
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  · have h1 : ∀ σ : MemoryPermutation u, memoryPermute u σ ≠ t := by
      intro σ h
      apply hl
      intro i
      rw [← h]
      simp [memoryPermute]
    have h2 : ∀ τ : MemoryPermutation t, memoryPermute t τ ≠ u := by
      intro τ h
      apply hl
      intro i
      rw [← h]
      simp [memoryPermute]
    simp [h1, h2]

theorem pd5c_memSize_memoryPermute' {x : ℝ} {K : ℕ} (u : MemPoint x K)
    (σ : MemoryPermutation u) : memSize (memoryPermute u σ) = memSize u := by
  simp [memSize, memoryPermute]

theorem pd5c_memMeasure_memoryPermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (u : MemPoint S.x K) (σ : MemoryPermutation u) :
    memMeasure F S (memoryPermute u σ) = memMeasure F S u := by
  classical
  have hperm : ∀ i, List.Perm ((memoryPermute u σ).2.2 i) (u.2.2 i) :=
    fun i => listPermute_perm (u.2.2 i) (σ i)
  have hvalid : MemValid F S (memoryPermute u σ) ↔ MemValid F S u := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun i e he => h3 i e ((hperm i).mem_iff.mpr he)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun i e he => h3 i e ((hperm i).mem_iff.mp he)⟩
  unfold memMeasure
  by_cases hv : MemValid F S u
  · rw [if_pos (hvalid.mpr hv), if_pos hv]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [((hperm i).map fun e => memoryNu S.x K F.a F.q_d i e.1).prod_eq, (hperm i).length_eq]
  · rw [if_neg (fun h => hv (hvalid.mp h)), if_neg hv]

theorem pd5c_permuteLists_eq_iff {x : ℝ} {K : ℕ}
    (τ : Fin K → Equiv.Perm (Fin (slotCount x))) (p q : PrimeLists x K) :
    permuteLists τ p = q ↔ p = permuteLists (fun i => (τ i).symm) q := by
  constructor
  · intro h
    subst h
    funext i j
    simp [permuteLists]
  · intro h
    subst h
    funext i j
    simp [permuteLists]

theorem pd5c_memMeasure_activePermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (u : MemPoint S.x K) (τ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
    memMeasure F S (u.1, permuteLists τ u.2.1, u.2.2) = memMeasure F S u := by
  classical
  have hvalid : MemValid F S (u.1, permuteLists τ u.2.1, u.2.2) ↔ MemValid F S u := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun i j => ?_, h3⟩
      have := h2 i ((τ i).symm j)
      simpa [permuteLists] using this
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun i j => h2 i (τ i j), h3⟩
  unfold memMeasure
  by_cases hv : MemValid F S u
  · rw [if_pos (hvalid.mpr hv), if_pos hv]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact Equiv.prod_comp (τ i) (fun j => memoryNu S.x K F.a F.q_d i (u.2.1 i j))
  · rw [if_neg (fun h => hv (hvalid.mp h)), if_neg hv]


end
end ArtinPrimitiveRoots.TypeII.PD
