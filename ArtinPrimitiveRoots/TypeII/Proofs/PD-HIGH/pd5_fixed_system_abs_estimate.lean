import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_positive_choice_rows
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_chronological_model

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

private def pd5_birthLayer {K : ℕ} : BirthAddress K → ℕ
  | .initial _ _ => 0
  | .ghost j _ _ => 2 * j + 1
  | .edge j _ => 2 * j + 2

private def pd5_birthGroup {K : ℕ} : BirthAddress K → ℕ
  | .initial i _ => i.val
  | .ghost _ i _ => i.val
  | .edge _ i => i.val

private def pd5_birthOffset {K : ℕ} : BirthAddress K → ℕ
  | .initial _ k => k
  | .ghost _ _ k => k
  | .edge _ _ => 0

private theorem pd5_mul_add_injective (q r q' r' d : ℕ) (hd : 0 < d)
    (hr : r < d) (hr' : r' < d) (h : q * d + r = q' * d + r') :
    q = q' ∧ r = r' := by
  have hq : q = q' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt' : q + 1 ≤ q' := Nat.succ_le_of_lt hlt
      have hmul : (q + 1) * d ≤ q' * d := Nat.mul_le_mul_right d hlt'
      have hupper : q * d + r < (q + 1) * d := by
        rw [Nat.add_mul, one_mul]
        exact Nat.add_lt_add_left hr (q * d)
      have hle : q' * d ≤ q' * d + r' := Nat.le_add_right _ _
      exact (Nat.ne_of_lt (lt_of_lt_of_le hupper (le_trans hmul hle))) h
    · have hlt' : q' + 1 ≤ q := Nat.succ_le_of_lt hgt
      have hmul : (q' + 1) * d ≤ q * d := Nat.mul_le_mul_right d hlt'
      have hupper : q' * d + r' < (q' + 1) * d := by
        rw [Nat.add_mul, one_mul]
        exact Nat.add_lt_add_left hr' (q' * d)
      have hle : q * d ≤ q * d + r := Nat.le_add_right _ _
      exact (Nat.ne_of_lt (lt_of_lt_of_le hupper (le_trans hmul hle))) h.symm
  constructor
  · exact hq
  · rw [hq] at h
    exact Nat.add_left_cancel h

private theorem pd5_birthIndex_eq_row (K : ℕ) (S : PDScale) (B : ℕ)
    (a : BirthAddress K) :
    pd5_birthIndex S B a =
      (pd5_birthLayer a * K + pd5_birthGroup a) * (max (slotCount S.x) B + 1) +
        pd5_birthOffset a := by
  cases a <;> simp [pd5_birthIndex, pd5_birthLayer, pd5_birthGroup, pd5_birthOffset]

private theorem pd5_birthIndex_injective_on {K : ℕ} (S : PDScale) (B : ℕ)
    {a b : BirthAddress K}
    (ha : a ∈ birthAddresses S.x K B) (hb : b ∈ birthAddresses S.x K B)
    (h : pd5_birthIndex S B a = pd5_birthIndex S B b) : a = b := by
  have hradix : 0 < max (slotCount S.x) B + 1 := by omega
  have hoff (a : BirthAddress K) (ha : a ∈ birthAddresses S.x K B) :
      pd5_birthOffset a < max (slotCount S.x) B + 1 := by
    cases a with
    | initial i k =>
        have hk : k < slotCount S.x := by
          simpa [birthAddresses] using ha
        dsimp [pd5_birthOffset]
        have hm : slotCount S.x ≤ max (slotCount S.x) B := Nat.le_max_left _ _
        omega
    | ghost j i k =>
        have hk : k < B := by
          have hh : j ≤ pathLength S.x ∧ k < B := by
            simpa [birthAddresses] using ha
          exact hh.2
        dsimp [pd5_birthOffset]
        have hm : B ≤ max (slotCount S.x) B := Nat.le_max_right _ _
        omega
    | edge j i =>
        dsimp [pd5_birthOffset]
        omega
  have hdecomp := pd5_mul_add_injective
    ((pd5_birthLayer a * K + pd5_birthGroup a)) (pd5_birthOffset a)
    ((pd5_birthLayer b * K + pd5_birthGroup b)) (pd5_birthOffset b)
    (max (slotCount S.x) B + 1) hradix (hoff a ha) (hoff b hb) (by
      simpa only [pd5_birthIndex_eq_row] using h)
  have hK : 0 < K := by
    cases a with
    | initial i k => have hi := i.isLt; omega
    | ghost j i k => have hi := i.isLt; omega
    | edge j i => have hi := i.isLt; omega
  have hgroupA : pd5_birthGroup a < K := by
    cases a <;> exact Fin.isLt _
  have hgroupB : pd5_birthGroup b < K := by
    cases b <;> exact Fin.isLt _
  have hrow := pd5_mul_add_injective (pd5_birthLayer a) (pd5_birthGroup a)
    (pd5_birthLayer b) (pd5_birthGroup b) K hK hgroupA hgroupB
    hdecomp.1
  have hlayer : pd5_birthLayer a = pd5_birthLayer b := hrow.1
  have hgroup : pd5_birthGroup a = pd5_birthGroup b := hrow.2
  have hoffset : pd5_birthOffset a = pd5_birthOffset b := hdecomp.2
  cases a with
  | initial ia ka =>
      cases b with
      | initial ib kb =>
          have hi : ia.val = ib.val := by simpa [pd5_birthGroup] using hgroup
          have hk : ka = kb := by simpa [pd5_birthOffset] using hoffset
          cases Fin.ext hi
          cases hk
          rfl
      | ghost jb ib kb =>
          have hbad : 0 = 2 * jb + 1 := by simpa [pd5_birthLayer] using hlayer
          omega
      | edge jb ib =>
          have hbad : 0 = 2 * jb + 2 := by simpa [pd5_birthLayer] using hlayer
          omega
  | ghost ja ia ka =>
      cases b with
      | initial ib kb =>
          have hbad : 2 * ja + 1 = 0 := by simpa [pd5_birthLayer] using hlayer
          omega
      | ghost jb ib kb =>
          have hj : ja = jb := by
            have := hlayer
            simp [pd5_birthLayer] at this
            omega
          have hi : ia.val = ib.val := by simpa [pd5_birthGroup] using hgroup
          have hk : ka = kb := by simpa [pd5_birthOffset] using hoffset
          cases hj
          cases Fin.ext hi
          cases hk
          rfl
      | edge jb ib =>
          have hbad : 2 * ja + 1 = 2 * jb + 2 := by
            simpa [pd5_birthLayer] using hlayer
          omega
  | edge ja ia =>
      cases b with
      | initial ib kb =>
          have hbad : 2 * ja + 2 = 0 := by simpa [pd5_birthLayer] using hlayer
          omega
      | ghost jb ib kb =>
          have hbad : 2 * ja + 2 = 2 * jb + 1 := by
            simpa [pd5_birthLayer] using hlayer
          omega
      | edge jb ib =>
          have hj : ja = jb := by
            have := hlayer
            simp [pd5_birthLayer] at this
            omega
          have hi : ia.val = ib.val := by simpa [pd5_birthGroup] using hgroup
          cases hj
          cases Fin.ext hi
          rfl

private theorem pd5_birthIndex_lt_of_layer_lt {K : ℕ} (S : PDScale) (B : ℕ)
    {a b : BirthAddress K}
    (ha : a ∈ birthAddresses S.x K B) (hb : b ∈ birthAddresses S.x K B)
    (hlab : pd5_birthLayer a < pd5_birthLayer b) :
    pd5_birthIndex S B a < pd5_birthIndex S B b := by
  have hradix : 0 < max (slotCount S.x) B + 1 := by omega
  have hgroup (a : BirthAddress K) : pd5_birthGroup a < K := by
    cases a <;> exact Fin.isLt _
  have hoff (a : BirthAddress K) (ha : a ∈ birthAddresses S.x K B) :
      pd5_birthOffset a < max (slotCount S.x) B + 1 := by
    cases a with
    | initial i k =>
        have hk : k < slotCount S.x := by simpa [birthAddresses] using ha
        dsimp [pd5_birthOffset]
        have hm : slotCount S.x ≤ max (slotCount S.x) B := Nat.le_max_left _ _
        omega
    | ghost j i k =>
        have hk : k < B := by
          have hparts : j ≤ pathLength S.x ∧ k < B := by
            simpa [birthAddresses] using ha
          exact hparts.2
        dsimp [pd5_birthOffset]
        have hm : B ≤ max (slotCount S.x) B := Nat.le_max_right _ _
        omega
    | edge j i =>
        dsimp [pd5_birthOffset]
        omega
  have hquot :
      pd5_birthLayer a * K + pd5_birthGroup a <
        pd5_birthLayer b * K + pd5_birthGroup b := by
    have hstep : pd5_birthLayer a + 1 ≤ pd5_birthLayer b :=
      Nat.succ_le_of_lt hlab
    have hmul : (pd5_birthLayer a + 1) * K ≤ pd5_birthLayer b * K :=
      Nat.mul_le_mul_right K hstep
    have hupper :
        pd5_birthLayer a * K + pd5_birthGroup a <
          (pd5_birthLayer a + 1) * K := by
      rw [Nat.add_mul, one_mul]
      exact Nat.add_lt_add_left (hgroup a) (pd5_birthLayer a * K)
    have hlower :
        pd5_birthLayer b * K ≤ pd5_birthLayer b * K + pd5_birthGroup b :=
      Nat.le_add_right _ _
    exact lt_of_lt_of_le hupper (le_trans hmul hlower)
  rw [pd5_birthIndex_eq_row, pd5_birthIndex_eq_row]
  have hqsucc :
      pd5_birthLayer a * K + pd5_birthGroup a + 1 ≤
        pd5_birthLayer b * K + pd5_birthGroup b := Nat.succ_le_of_lt hquot
  have hmul :
      (pd5_birthLayer a * K + pd5_birthGroup a + 1) *
          (max (slotCount S.x) B + 1) ≤
        (pd5_birthLayer b * K + pd5_birthGroup b) *
          (max (slotCount S.x) B + 1) :=
    Nat.mul_le_mul_right (max (slotCount S.x) B + 1) hqsucc
  have hupper0 :
      (pd5_birthLayer a * K + pd5_birthGroup a) *
          (max (slotCount S.x) B + 1) +
          pd5_birthOffset a <
        (pd5_birthLayer a * K + pd5_birthGroup a + 1) *
          (max (slotCount S.x) B + 1) := by
    calc
      _ < (pd5_birthLayer a * K + pd5_birthGroup a) *
            (max (slotCount S.x) B + 1) + (max (slotCount S.x) B + 1) :=
        Nat.add_lt_add_left (hoff a ha) _
      _ = (pd5_birthLayer a * K + pd5_birthGroup a + 1) *
            (max (slotCount S.x) B + 1) := by
        simp [Nat.add_mul]
  have hupper :
      (pd5_birthLayer a * K + pd5_birthGroup a) *
          (max (slotCount S.x) B + 1) +
          pd5_birthOffset a <
        (pd5_birthLayer a * K + pd5_birthGroup a + 1) *
          (max (slotCount S.x) B + 1) := by
    simpa [Nat.add_mul] using hupper0
  have hlower :
      (pd5_birthLayer b * K + pd5_birthGroup b) *
          (max (slotCount S.x) B + 1) ≤
        (pd5_birthLayer b * K + pd5_birthGroup b) *
          (max (slotCount S.x) B + 1) +
          pd5_birthOffset b :=
    Nat.le_add_right _ _
  exact lt_of_lt_of_le hupper (le_trans hmul hlower)

private theorem pd5_exists_min_birth_index {K : ℕ} (S : PDScale) (B : ℕ)
    {D : Finset (BirthAddress K)} (hD : 2 ≤ D.card) :
    ∃ p ∈ D, ∀ a ∈ D, pd5_birthIndex S B p ≤ pd5_birthIndex S B a := by
  classical
  let I := D.image (pd5_birthIndex S B)
  have hDne : D.Nonempty := Finset.card_pos.mp (by omega)
  have hIne : I.Nonempty := Finset.image_nonempty.mpr hDne
  have hmem : I.min' hIne ∈ I := Finset.min'_mem I hIne
  rcases Finset.mem_image.mp hmem with ⟨p, hp, hmin⟩
  refine ⟨p, hp, ?_⟩
  intro a ha
  have hle := Finset.min'_le I (pd5_birthIndex S B a)
    (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  simpa [I, hmin] using hle

private theorem pd5_min_birth_index_strict {K : ℕ} (S : PDScale) (B : ℕ)
    {D : Finset (BirthAddress K)} (hD : 2 ≤ D.card)
    (hsub : D ⊆ birthAddresses S.x K B)
    {p a : BirthAddress K} (hp : p ∈ D) (ha : a ∈ D)
    (hmin : ∀ b ∈ D, pd5_birthIndex S B p ≤ pd5_birthIndex S B b)
    (hne : a ≠ p) : pd5_birthIndex S B p < pd5_birthIndex S B a := by
  have hle := hmin a ha
  by_contra hnot
  have heq : pd5_birthIndex S B p = pd5_birthIndex S B a := by omega
  exact hne (pd5_birthIndex_injective_on S B (hsub ha) (hsub hp) heq.symm)

private theorem pd5_prefixGood_layers_lt_ghost {K : ℕ} {x : ℝ} {B j : ℕ}
    {L : BirthLog K} (hL : pd5_logPrefixGood x B j j L) :
    ∀ e ∈ L, pd5_birthLayer e.1 < 2 * j + 1 := by
  intro e he
  rcases e with ⟨a, v⟩
  have hpref := (hL.2 (a, v) he).1
  cases a with
  | initial i k => simp [pd5_birthLayer]
  | edge n i =>
      have hn : n < j := by simpa [pd5_prefixAddress] using hpref
      simp [pd5_birthLayer]
      omega
  | ghost n i k =>
      have hn : n < j := by
        have hp : n < j ∧ k < B := by simpa [pd5_prefixAddress] using hpref
        exact hp.1
      simp [pd5_birthLayer]
      omega

private theorem pd5_prefixGood_layers_lt_edge {K : ℕ} {x : ℝ} {B j : ℕ}
    {L : BirthLog K} (hL : pd5_logPrefixGood x B j (j + 1) L) :
    ∀ e ∈ L, pd5_birthLayer e.1 < 2 * j + 2 := by
  intro e he
  rcases e with ⟨a, v⟩
  have hpref := (hL.2 (a, v) he).1
  cases a with
  | initial i k => simp [pd5_birthLayer]
  | edge n i =>
      have hn : n < j := by simpa [pd5_prefixAddress] using hpref
      simp [pd5_birthLayer]
      omega
  | ghost n i k =>
      have hn : n < j + 1 := by
        have hp : n < j + 1 ∧ k < B := by simpa [pd5_prefixAddress] using hpref
        exact hp.1
      simp [pd5_birthLayer]
      omega

private theorem pd5_ghost_not_in_prefix {K : ℕ} {x : ℝ} {B j : ℕ}
    {L : BirthLog K} (hL : pd5_logPrefixGood x B j j L)
    (i : Fin K) (k v : ℕ) :
    (BirthAddress.ghost j i k, v) ∉ L := by
  intro hmem
  have hpref := (hL.2 (BirthAddress.ghost j i k, v) hmem).1
  simp [pd5_prefixAddress] at hpref

private theorem pd5_edge_not_in_prefix {K : ℕ} {x : ℝ} {B j : ℕ}
    {L : BirthLog K} (hL : pd5_logPrefixGood x B j (j + 1) L)
    (i : Fin K) (v : ℕ) :
    (BirthAddress.edge j i, v) ∉ L := by
  intro hmem
  have hpref := (hL.2 (BirthAddress.edge j i, v) hmem).1
  simp [pd5_prefixAddress] at hpref

private theorem pd5_pastPair_mem_filter {K : ℕ} (S : PDScale) (B : ℕ)
    (pastLog newLog : BirthLog K) (a : BirthAddress K)
    (hPastLayer : ∀ e ∈ pastLog, pd5_birthLayer e.1 < pd5_birthLayer a)
    (hA : a ∈ birthAddresses S.x K B) {e : BirthAddress K × ℕ}
    (heA : e.1 ∈ birthAddresses S.x K B) (he : e ∈ pastLog) :
    e ∈ ((pastLog ++ newLog).filter fun t =>
      pd5_birthIndex S B t.1 < pd5_birthIndex S B a) := by
  have hindex := pd5_birthIndex_lt_of_layer_lt S B heA hA (hPastLayer e he)
  apply List.mem_filter.mpr
  exact ⟨List.mem_append_left _ he, by simp [hindex]⟩

private theorem pd5_ghostBirthLog_layer {K : ℕ} (j : ℕ) (l : Fin K → ℕ)
    (p : (i : Fin K) → Fin (l i) → ℕ) (e : BirthAddress K × ℕ)
    (he : e ∈ pd5_ghostBirthLog j l p) :
    pd5_birthLayer e.1 = 2 * j + 1 := by
  have haddr : e.1 ∈ pd5_ghostAddressList j l := by
    have hmap : e.1 ∈ (pd5_ghostBirthLog j l p).map Prod.fst :=
      List.mem_map.mpr ⟨e, he, rfl⟩
    rw [pd5_ghostBirthLog_map_fst] at hmap
    exact hmap
  simp only [pd5_ghostAddressList, List.mem_flatMap] at haddr
  rcases haddr with ⟨i, hi, hk⟩
  rcases List.mem_ofFn.mp hk with ⟨k, hEq⟩
  have hEq' : e.1 = BirthAddress.ghost j i k.val := hEq.symm
  rw [hEq']
  rfl

private theorem pd5_edgeBirths_layer {K : ℕ} (F : PDFix K) (S : PDScale)
    (step : ℕ) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    {a : BirthAddress K} (ha : a ∈ (edgeBirths F S step s c).map Prod.fst) :
    pd5_birthLayer a = 2 * step + 2 := by
  unfold edgeBirths at ha
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    List.map_nil, List.map_cons, Prod.fst] at ha
  rcases List.mem_flatMap.mp ha with ⟨i, hi, ha⟩
  cases h : (c i).2 with
  | inl k => simp [h] at ha
  | inr p =>
      have hEq : a = BirthAddress.edge step i := by simpa [h] using ha
      rw [hEq]
      rfl

private noncomputable def pd5_chosenBlockPivot {K : ℕ} (S : PDScale) (B : ℕ)
    (D : Finset (BirthAddress K)) (hD : 2 ≤ D.card) : BirthAddress K :=
  Classical.choose (pd5_exists_min_birth_index S B hD)

private theorem pd5_chosenBlockPivot_spec {K : ℕ} (S : PDScale) (B : ℕ)
    (D : Finset (BirthAddress K)) (hD : 2 ≤ D.card) :
    pd5_chosenBlockPivot S B D hD ∈ D ∧
      ∀ a ∈ D, pd5_birthIndex S B (pd5_chosenBlockPivot S B D hD) ≤ pd5_birthIndex S B a :=
  Classical.choose_spec (pd5_exists_min_birth_index S B hD)

private theorem pd5_chosenBlockPivot_erase_card {K : ℕ} (S : PDScale) (B : ℕ)
    (D : Finset (BirthAddress K)) (hD : 2 ≤ D.card) :
    (D.erase (pd5_chosenBlockPivot S B D hD)).card = D.card - 1 := by
  have hp := (pd5_chosenBlockPivot_spec S B D hD).1
  simp [hp]

private noncomputable def pd5_blockNonpivots {K : ℕ} (S : PDScale) (B : ℕ)
    (D : Finset (BirthAddress K)) : Finset (BirthAddress K) :=
  if hD : 2 ≤ D.card then D.erase (pd5_chosenBlockPivot S B D hD) else ∅

private theorem pd5_constraintRank_eq_erased_card_sum {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) :
    constraintRank C = ∑ D ∈ C, (pd5_blockNonpivots S B D).card := by
  classical
  unfold constraintRank
  apply Finset.sum_congr rfl
  intro D hD
  have hDsize : 2 ≤ D.card := ((Finset.mem_filter.mp hC).2.1 D hD).2
  simp [pd5_blockNonpivots, hDsize, pd5_chosenBlockPivot_erase_card]

private theorem pd5_blockNonpivots_subset {K : ℕ} (S : PDScale) (B : ℕ)
    (D : Finset (BirthAddress K)) : pd5_blockNonpivots S B D ⊆ D := by
  classical
  by_cases hD : 2 ≤ D.card
  · simpa [pd5_blockNonpivots, hD] using
      (Finset.erase_subset (pd5_chosenBlockPivot S B D hD) D)
  · simp [pd5_blockNonpivots, hD]

private def pd5_allNonpivots {K : ℕ} (S : PDScale) (B : ℕ)
    (C : Finset (Finset (BirthAddress K))) : Finset (BirthAddress K) :=
  C.biUnion (pd5_blockNonpivots S B)

private theorem pd5_allNonpivots_card {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) :
    (pd5_allNonpivots S B C).card = constraintRank C := by
  classical
  have hSys : IsConstraintSystem A C := (Finset.mem_filter.mp hC).2
  have hdisj : (C : Set (Finset (BirthAddress K))).PairwiseDisjoint
      (pd5_blockNonpivots S B) := by
    intro D hD E hE hne
    exact (hSys.2 D hD E hE hne).mono
      (pd5_blockNonpivots_subset S B D) (pd5_blockNonpivots_subset S B E)
  rw [pd5_allNonpivots, Finset.card_biUnion hdisj,
    pd5_constraintRank_eq_erased_card_sum S B hC]

private def pd5_isGhostAt {K : ℕ} (j : ℕ) : BirthAddress K → Prop
  | .ghost j' _ _ => j' = j
  | _ => False

private def pd5_isEdgeAt {K : ℕ} (j : ℕ) : BirthAddress K → Prop
  | .edge j' _ => j' = j
  | _ => False

private def pd5_isInitial {K : ℕ} : BirthAddress K → Prop
  | .initial _ _ => True
  | _ => False

private noncomputable def pd5_addressBlock {K : ℕ}
    (C : Finset (Finset (BirthAddress K))) (a : BirthAddress K)
    (ha : a ∈ C.biUnion id) : Finset (BirthAddress K) :=
  Classical.choose (Finset.mem_biUnion.mp ha)

private theorem pd5_addressBlock_spec {K : ℕ}
    (C : Finset (Finset (BirthAddress K))) (a : BirthAddress K)
    (ha : a ∈ C.biUnion id) :
    pd5_addressBlock C a ha ∈ C ∧ a ∈ pd5_addressBlock C a ha :=
  Classical.choose_spec (Finset.mem_biUnion.mp ha)

private theorem pd5_addressBlock_eq_of_mem {K : ℕ}
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hSys : IsConstraintSystem A C) (a : BirthAddress K)
    (ha : a ∈ C.biUnion id) (D : Finset (BirthAddress K))
    (hD : D ∈ C) (haD : a ∈ D) :
    pd5_addressBlock C a ha = D := by
  classical
  have hchosen := pd5_addressBlock_spec C a ha
  by_contra hne
  have hdisj := hSys.2 (pd5_addressBlock C a ha) hchosen.1 D hD hne
  exact (Finset.disjoint_left.mp hdisj) hchosen.2 haD

private noncomputable def pd5_addressPivot {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : IsConstraintSystem A C) (a : BirthAddress K) : BirthAddress K := by
  classical
  exact if ha : a ∈ C.biUnion id then
    let D := pd5_addressBlock C a ha
    pd5_chosenBlockPivot S B D ((hC.1 D (pd5_addressBlock_spec C a ha).1).2)
  else a

private theorem pd5_addressPivot_eq_blockPivot {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hSys : IsConstraintSystem A C) (a : BirthAddress K)
    (ha : a ∈ C.biUnion id) (D : Finset (BirthAddress K))
    (hD : D ∈ C) (haD : a ∈ D) :
    pd5_addressPivot S B hSys a =
      pd5_chosenBlockPivot S B D ((hSys.1 D hD).2) := by
  have hblock : pd5_addressBlock C a ha = D :=
    pd5_addressBlock_eq_of_mem hSys a ha D hD haD
  simp [pd5_addressPivot, ha, hblock]

private theorem pd5_addressPivot_spec {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : IsConstraintSystem A C) (a : BirthAddress K) (ha : a ∈ C.biUnion id) :
    pd5_addressPivot S B hC a ∈ pd5_addressBlock C a ha ∧
      a ∈ pd5_addressBlock C a ha ∧
      ∀ b ∈ pd5_addressBlock C a ha,
        pd5_birthIndex S B (pd5_addressPivot S B hC a) ≤ pd5_birthIndex S B b := by
  let D := pd5_addressBlock C a ha
  have hDsys := pd5_addressBlock_spec C a ha
  have hDsize : 2 ≤ D.card := (hC.1 D hDsys.1).2
  have hspec := pd5_chosenBlockPivot_spec S B D hDsize
  have hP : pd5_addressPivot S B hC a = pd5_chosenBlockPivot S B D hDsize := by
    simp [pd5_addressPivot, ha, D, hDsys]
  rw [hP]
  exact ⟨hspec.1, hDsys.2, hspec.2⟩

private theorem pd5_allNonpivots_eq_filter {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) :
    pd5_allNonpivots S B C =
      (C.biUnion id).filter fun a =>
        a ≠ pd5_addressPivot S B (Finset.mem_filter.mp hC).2 a := by
  classical
  let hSys : IsConstraintSystem A C := (Finset.mem_filter.mp hC).2
  ext a
  constructor
  · intro ha
    rcases Finset.mem_biUnion.mp ha with ⟨D, hD, haD⟩
    have hDsize : 2 ≤ D.card := (hSys.1 D hD).2
    have haErase : a ∈ D.erase (pd5_chosenBlockPivot S B D hDsize) := by
      simpa [pd5_blockNonpivots, hDsize] using haD
    rcases Finset.mem_erase.mp haErase with ⟨hne, haDmem⟩
    have haSupport : a ∈ C.biUnion id :=
      Finset.mem_biUnion.mpr ⟨D, hD, haDmem⟩
    have hpivotEq := pd5_addressPivot_eq_blockPivot S B hSys a haSupport D hD haDmem
    exact Finset.mem_filter.mpr ⟨haSupport, by rw [hpivotEq]; exact hne⟩
  · intro ha
    rw [pd5_allNonpivots]
    rcases Finset.mem_filter.mp ha with ⟨haSupport, hne⟩
    rcases Finset.mem_biUnion.mp haSupport with ⟨D, hD, haDmem⟩
    have hDsize : 2 ≤ D.card := (hSys.1 D hD).2
    have hpivotEq := pd5_addressPivot_eq_blockPivot S B hSys a haSupport D hD haDmem
    have haErase : a ∈ D.erase (pd5_chosenBlockPivot S B D hDsize) := by
      apply Finset.mem_erase.mpr
      refine ⟨?_, haDmem⟩
      rw [← hpivotEq]
      exact hne
    have haNonpivot : a ∈ pd5_blockNonpivots S B D := by
      simpa [pd5_blockNonpivots, hDsize] using haErase
    exact Finset.mem_biUnion.mpr ⟨D, hD, haNonpivot⟩

private def pd5_layerAddresses {K : ℕ}
    (C : Finset (Finset (BirthAddress K))) (P : BirthAddress K → Prop) :
    Finset (BirthAddress K) := (C.biUnion id).filter P

private noncomputable def pd5_layerNonpivots {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : IsConstraintSystem A C) (P : BirthAddress K → Prop) :
    Finset (BirthAddress K) :=
  (pd5_layerAddresses C P).filter fun a =>
    a ≠ pd5_addressPivot S B hC a

private noncomputable def pd5_addressPick {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : IsConstraintSystem A C) : BirthAddress K → BirthLog K → ℕ :=
  fun a pre =>
    if ha : a ∈ C.biUnion id then
      (pd5b_label pre (pd5_addressPivot S B hC a)).getD 0
    else 0

private theorem pd5_layerNonpivots_eq_all_filter {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) (P : BirthAddress K → Prop) :
    pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2 P =
      (pd5_allNonpivots S B C).filter P := by
  classical
  ext a
  simp [pd5_layerNonpivots, pd5_layerAddresses,
    pd5_allNonpivots_eq_filter S B hC]
  tauto

private theorem pd5_sum_layers (f : ℕ → ℕ) (N : ℕ) :
    (∑ l ∈ Finset.range (2 * N + 2), f l) =
      f 0 + (∑ j ∈ Finset.range (N + 1), f (2 * j + 1)) +
        (∑ j ∈ Finset.range N, f (2 * j + 2)) := by
  induction N with
  | zero => simp [Finset.sum_range_succ]
  | succ N ih =>
      have hL :
          (∑ l ∈ Finset.range (2 * (N + 1) + 2), f l) =
            (∑ l ∈ Finset.range (2 * N + 2), f l) +
              f (2 * N + 2) + f (2 * N + 3) := by
        have hidx : 2 * (N + 1) + 2 = (2 * N + 2) + 2 := by omega
        rw [hidx, Finset.sum_range_succ, Finset.sum_range_succ]
      have hG :
          (∑ j ∈ Finset.range (N + 1 + 1), f (2 * j + 1)) =
            (∑ j ∈ Finset.range (N + 1), f (2 * j + 1)) + f (2 * N + 3) := by
        rw [Finset.sum_range_succ]
        rw [show 2 * (N + 1) + 1 = 2 * N + 3 by omega]
      have hE :
          (∑ j ∈ Finset.range (N + 1), f (2 * j + 2)) =
            (∑ j ∈ Finset.range N, f (2 * j + 2)) + f (2 * N + 2) := by
        rw [Finset.sum_range_succ]
      rw [hL, hG, hE, ih]
      omega

private theorem pd5_birthLayer_eq_zero_iff {K : ℕ} (a : BirthAddress K) :
    pd5_birthLayer a = 0 ↔ pd5_isInitial a := by
  cases a <;> simp [pd5_birthLayer, pd5_isInitial]

private theorem pd5_birthLayer_eq_ghost_iff {K : ℕ} (j : ℕ) (a : BirthAddress K) :
    pd5_birthLayer a = 2 * j + 1 ↔ pd5_isGhostAt j a := by
  cases a <;> simp [pd5_birthLayer, pd5_isGhostAt] <;> omega

private theorem pd5_birthLayer_eq_edge_iff {K : ℕ} (j : ℕ) (a : BirthAddress K) :
    pd5_birthLayer a = 2 * j + 2 ↔ pd5_isEdgeAt j a := by
  cases a <;> simp [pd5_birthLayer, pd5_isEdgeAt] <;> omega

private theorem pd5_rank_eq_layer_card_sum {K : ℕ} (S : PDScale) (B : ℕ)
    {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems (birthAddresses S.x K B)) :
    constraintRank C =
      (pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2 pd5_isInitial).card +
        (∑ j ∈ Finset.range (S.N + 1),
          (pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2
            (pd5_isGhostAt j)).card) +
        (∑ j ∈ Finset.range S.N,
          (pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2
            (pd5_isEdgeAt j)).card) := by
  classical
  let R := pd5_allNonpivots S B C
  let f : ℕ → ℕ := fun layer => (R.filter fun a =>
    pd5_birthLayer a = layer).card
  have hMaps : (R : Set (BirthAddress K)).MapsTo pd5_birthLayer
      (Finset.range (2 * S.N + 2)) := by
    intro a ha
    rcases Finset.mem_biUnion.mp ha with ⟨D, hD, haD⟩
    have hblock : pd5_blockNonpivots S B D ⊆ D :=
      pd5_blockNonpivots_subset S B D
    have haD' : a ∈ D := hblock haD
    have haddr : a ∈ birthAddresses S.x K B :=
      pd5_constraint_support_subset hC
        (Finset.mem_biUnion.mpr ⟨D, hD, haD'⟩)
    cases a with
    | initial i k =>
        simp [pd5_birthLayer]
    | ghost j i k =>
        have hparts : j ≤ pathLength S.x ∧ k < B := by
          simpa [birthAddresses] using haddr
        have hj : j ≤ S.N := by simpa [PDScale.N] using hparts.1
        simp [pd5_birthLayer]
        omega
    | edge j i =>
        have hj : j < pathLength S.x := by
          simpa [birthAddresses] using haddr
        have hj' : j < S.N := by simpa [PDScale.N] using hj
        simp [pd5_birthLayer]
        omega
  have hFiber :
      R.card = ∑ layer ∈ Finset.range (2 * S.N + 2), f layer := by
    have h := Finset.card_eq_sum_card_fiberwise hMaps
    simpa [f] using h
  have hRanks : R.card = constraintRank C :=
    pd5_allNonpivots_card S B hC
  have hLayerSum := pd5_sum_layers f S.N
  have hInit :
      f 0 = (pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2
        pd5_isInitial).card := by
    have hfilter : R.filter (fun a => pd5_birthLayer a = 0) =
        R.filter pd5_isInitial := by
      ext a
      simp [pd5_birthLayer_eq_zero_iff]
    change (R.filter (fun a => pd5_birthLayer a = 0)).card = _
    rw [hfilter, ← pd5_layerNonpivots_eq_all_filter S B hC pd5_isInitial]
  have hGhost (j : ℕ) :
      f (2 * j + 1) =
        (pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2
          (pd5_isGhostAt j)).card := by
    have hfilter : R.filter (fun a => pd5_birthLayer a = 2 * j + 1) =
        R.filter (pd5_isGhostAt j) := by
      ext a
      simp [pd5_birthLayer_eq_ghost_iff]
    change (R.filter (fun a => pd5_birthLayer a = 2 * j + 1)).card = _
    rw [hfilter, ← pd5_layerNonpivots_eq_all_filter S B hC (pd5_isGhostAt j)]
  have hEdge (j : ℕ) :
      f (2 * j + 2) =
        (pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2
          (pd5_isEdgeAt j)).card := by
    have hfilter : R.filter (fun a => pd5_birthLayer a = 2 * j + 2) =
        R.filter (pd5_isEdgeAt j) := by
      ext a
      simp [pd5_birthLayer_eq_edge_iff]
    change (R.filter (fun a => pd5_birthLayer a = 2 * j + 2)).card = _
    rw [hfilter, ← pd5_layerNonpivots_eq_all_filter S B hC (pd5_isEdgeAt j)]
  calc
    constraintRank C = R.card := hRanks.symm
    _ = ∑ layer ∈ Finset.range (2 * S.N + 2), f layer := hFiber
    _ = f 0 + (∑ j ∈ Finset.range (S.N + 1), f (2 * j + 1)) +
          (∑ j ∈ Finset.range S.N, f (2 * j + 2)) := hLayerSum
    _ = _ := by simp_rw [hInit, hGhost, hEdge]

private theorem pd5_absorb_fixed_factors (K M N B : ℕ)
    (A₀ Cghost Cedge L : ℝ)
    (hA₀ : 0 ≤ A₀) (hL : 2 ≤ L) (hM : M ≤ N)
    (hB : ((B + 1 : ℕ) : ℝ) ≤ 3 * L ^ 2)
    (hghost : 0 < Cghost) (hghostL : Cghost ≤ L)
    (hedge : 0 < Cedge) (hedgeL : Cedge * (3 : ℝ) ^ K ≤ L) :
    (2 : ℝ) ^ (K * M) * Cghost ^ (N + 1) *
        (Cedge * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow L (3 * A₀)) ^ N ≤
      Real.rpow L ((3 * (K : ℝ) + 3 * A₀ + 3) * ((N : ℝ) + 1)) := by
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hKM : K * M ≤ K * N := Nat.mul_le_mul_left K hM
  have hInitPow : (2 : ℝ) ^ (K * M) ≤ L ^ (K * N) := by
    calc
      (2 : ℝ) ^ (K * M) ≤ L ^ (K * M) :=
        pow_le_pow_left₀ (by norm_num) hL _
      _ ≤ L ^ (K * N) := pow_le_pow_right₀ hLone hKM
  have hInit :
      (2 : ℝ) ^ (K * M) ≤ Real.rpow L ((K * N : ℕ) : ℝ) := by
    calc
      _ ≤ L ^ (K * N) := hInitPow
      _ = Real.rpow L ((K * N : ℕ) : ℝ) := (Real.rpow_natCast L (K * N)).symm
  have hGhostPow : Cghost ^ (N + 1) ≤ L ^ (N + 1) :=
    pow_le_pow_left₀ (le_of_lt hghost) hghostL _
  have hGhost : Cghost ^ (N + 1) ≤ Real.rpow L ((N + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ L ^ (N + 1) := hGhostPow
      _ = Real.rpow L ((N + 1 : ℕ) : ℝ) :=
        (Real.rpow_natCast L (N + 1)).symm
  have hBpow : ((B + 1 : ℕ) : ℝ) ^ K ≤ (3 * L ^ 2) ^ K :=
    pow_le_pow_left₀ (by positivity) hB _
  have hCube : (3 * L ^ 2) ^ K = (3 : ℝ) ^ K * L ^ (2 * K) := by
    calc
      (3 * L ^ 2) ^ K = (3 : ℝ) ^ K * (L ^ 2) ^ K := by rw [mul_pow]
      _ = (3 : ℝ) ^ K * L ^ (2 * K) := by rw [pow_mul]
  have hEdgeBase :
      Cedge * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow L (3 * A₀) ≤
        Real.rpow L ((2 * (K : ℝ) + 1) + 3 * A₀) := by
    have hmul1 := mul_le_mul_of_nonneg_left hBpow hedge.le
    have hmul2 := mul_le_mul_of_nonneg_right hmul1
      (Real.rpow_nonneg hLpos.le (3 * A₀))
    have hCoarse :
        Cedge * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow L (3 * A₀) ≤
          L ^ (2 * K + 1) * Real.rpow L (3 * A₀) := by
      calc
        _ ≤ Cedge * ((3 : ℝ) ^ K * L ^ (2 * K)) * Real.rpow L (3 * A₀) := by
          calc
            _ ≤ Cedge * ((3 * L ^ 2) ^ K) * Real.rpow L (3 * A₀) :=
              mul_le_mul_of_nonneg_right hmul1 (Real.rpow_nonneg hLpos.le _)
            _ = _ := by rw [hCube]
        _ ≤ L * L ^ (2 * K) * Real.rpow L (3 * A₀) := by
          have hbase := mul_le_mul_of_nonneg_right hedgeL
            (pow_nonneg hLpos.le (2 * K))
          have hbase' := mul_le_mul_of_nonneg_right hbase
            (Real.rpow_nonneg hLpos.le (3 * A₀))
          calc
            _ = (Cedge * (3 : ℝ) ^ K) * L ^ (2 * K) *
                Real.rpow L (3 * A₀) := by ring
            _ ≤ L * L ^ (2 * K) * Real.rpow L (3 * A₀) := hbase'
        _ = L ^ (2 * K + 1) * Real.rpow L (3 * A₀) := by
          rw [pow_succ]
          ring
    calc
      _ ≤ L ^ (2 * K + 1) * Real.rpow L (3 * A₀) := hCoarse
      _ = Real.rpow L ((2 * (K : ℝ) + 1) + 3 * A₀) := by
        calc
          _ = Real.rpow L ((2 * K + 1 : ℕ) : ℝ) * Real.rpow L (3 * A₀) := by
            rw [(Real.rpow_natCast L (2 * K + 1)).symm]
            rfl
          _ = Real.rpow L (((2 * K + 1 : ℕ) : ℝ) + 3 * A₀) :=
            (Real.rpow_add hLpos _ _).symm
          _ = Real.rpow L ((2 * (K : ℝ) + 1) + 3 * A₀) := by
            congr 1
            push_cast
            ring
  have hEdgeNonneg :
      0 ≤ Cedge * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow L (3 * A₀) :=
    mul_nonneg (mul_nonneg hedge.le (pow_nonneg (by positivity) _))
      (Real.rpow_nonneg hLpos.le _)
  have hEdgePow :
      (Cedge * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow L (3 * A₀)) ^ N ≤
        Real.rpow L (((2 * (K : ℝ) + 1) + 3 * A₀) * (N : ℝ)) := by
    calc
      _ ≤ (Real.rpow L ((2 * (K : ℝ) + 1) + 3 * A₀)) ^ N :=
        pow_le_pow_left₀ hEdgeNonneg hEdgeBase _
      _ = Real.rpow L (((2 * (K : ℝ) + 1) + 3 * A₀) * (N : ℝ)) := by
        rw [← Real.rpow_natCast (Real.rpow L
          ((2 * (K : ℝ) + 1) + 3 * A₀)) N]
        exact (Real.rpow_mul hLpos.le
          ((2 * (K : ℝ) + 1) + 3 * A₀) (N : ℝ)).symm
  have hPartial :
      (2 : ℝ) ^ (K * M) * Cghost ^ (N + 1) ≤
        Real.rpow L (((K * N : ℕ) : ℝ) + ((N + 1 : ℕ) : ℝ)) := by
    calc
      _ ≤ Real.rpow L ((K * N : ℕ) : ℝ) *
          Real.rpow L ((N + 1 : ℕ) : ℝ) :=
        mul_le_mul hInit hGhost
          (pow_nonneg (le_of_lt hghost) _)
          (Real.rpow_nonneg hLpos.le _)
      _ = _ := (Real.rpow_add hLpos _ _).symm
  have hAll :
      (2 : ℝ) ^ (K * M) * Cghost ^ (N + 1) *
          (Cedge * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow L (3 * A₀)) ^ N ≤
        Real.rpow L
          (((K * N : ℕ) : ℝ) + ((N + 1 : ℕ) : ℝ) +
            ((2 * (K : ℝ) + 1) + 3 * A₀) * (N : ℝ)) := by
    calc
      _ ≤ Real.rpow L (((K * N : ℕ) : ℝ) + ((N + 1 : ℕ) : ℝ)) *
          (Cedge * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow L (3 * A₀)) ^ N := by
        exact mul_le_mul_of_nonneg_right hPartial (pow_nonneg hEdgeNonneg _)
      _ ≤ Real.rpow L (((K * N : ℕ) : ℝ) + ((N + 1 : ℕ) : ℝ)) *
          Real.rpow L (((2 * (K : ℝ) + 1) + 3 * A₀) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hEdgePow (Real.rpow_nonneg hLpos.le _)
      _ = _ := (Real.rpow_add hLpos _ _).symm
  have hExponent :
      ((K * N : ℕ) : ℝ) + ((N + 1 : ℕ) : ℝ) +
          ((2 * (K : ℝ) + 1) + 3 * A₀) * (N : ℝ) ≤
        (3 * (K : ℝ) + 3 * A₀ + 3) * ((N : ℝ) + 1) := by
    push_cast
    nlinarith [sq_nonneg (N : ℝ), mul_nonneg (show 0 ≤ (K : ℝ) by positivity) hA₀]
  exact hAll.trans
    (Real.rpow_le_rpow_of_exponent_le hLone hExponent)

private theorem pd5_ghostLayer_subset {K : ℕ} (x : ℝ) (B j : ℕ)
    {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems (birthAddresses x K B)) :
    pd5_layerAddresses C (pd5_isGhostAt j) ⊆ pd5_ghostAddresses K j B := by
  intro a ha
  rcases Finset.mem_filter.mp ha with ⟨haSupport, hlayer⟩
  have haA := pd5_constraint_support_subset hC haSupport
  cases a with
  | initial i k => simp [pd5_isGhostAt] at hlayer
  | edge j' i => simp [pd5_isGhostAt] at hlayer
  | ghost j' i k =>
      simp [pd5_isGhostAt] at hlayer
      subst j'
      have hmem : BirthAddress.ghost j i k ∈ birthAddresses x K B := haA
      have hk : k < B := by
        have hparts : j ≤ pathLength x ∧ k < B := by
          simpa [birthAddresses] using hmem
        exact hparts.2
      simpa [pd5_ghostAddresses, hk]

private theorem pd5_edgeLayer_subset {K : ℕ} (x : ℝ) (B j : ℕ)
    {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems (birthAddresses x K B)) :
    pd5_layerAddresses C (pd5_isEdgeAt j) ⊆ pd5_edgeAddresses K j := by
  intro a ha
  rcases Finset.mem_filter.mp ha with ⟨haSupport, hlayer⟩
  have haA := pd5_constraint_support_subset hC haSupport
  cases a with
  | initial i k => simp [pd5_isEdgeAt] at hlayer
  | ghost j' i k => simp [pd5_isEdgeAt] at hlayer
  | edge j' i =>
      simp [pd5_isEdgeAt] at hlayer
      subst j'
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private theorem pd5_layerNonpivot_strict {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) (hA : A ⊆ birthAddresses S.x K B)
    (P : BirthAddress K → Prop) {a : BirthAddress K}
    (ha : a ∈ pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2 P) :
    pd5_birthIndex S B
        (pd5_addressPivot S B (Finset.mem_filter.mp hC).2 a) <
      pd5_birthIndex S B a := by
  let hSys : IsConstraintSystem A C := (Finset.mem_filter.mp hC).2
  have haOuter := Finset.mem_filter.mp ha
  have haLayer := Finset.mem_filter.mp haOuter.1
  have haSupport : a ∈ C.biUnion id := haLayer.1
  have hneq : a ≠ pd5_addressPivot S B hSys a := haOuter.2
  let D := pd5_addressBlock C a haSupport
  have hDsys := pd5_addressBlock_spec C a haSupport
  have hDsize : 2 ≤ D.card := (hSys.1 D hDsys.1).2
  have hDsub : D ⊆ birthAddresses S.x K B :=
    (hSys.1 D hDsys.1).1.trans hA
  have hpivot := pd5_addressPivot_spec S B hSys a haSupport
  exact pd5_min_birth_index_strict S B hDsize hDsub hpivot.1 hpivot.2.1
    hpivot.2.2 hneq

private theorem pd5_prescribedWeight_eq_one_of_labels {K : ℕ} (S : PDScale) (B : ℕ)
    (U R : Finset (BirthAddress K)) (pick : BirthAddress K → BirthLog K → ℕ)
    (pastLog newLog : BirthLog K)
    (hlabels : ∀ a ∈ U, ∃ p, pd5b_label newLog a = some p)
    (hties : ∀ a ∈ R, ∀ p, pd5b_label newLog a = some p →
      p = pick a ((pastLog ++ newLog).filter fun e =>
        pd5_birthIndex S B e.1 < pd5_birthIndex S B a)) :
    pd5_prescribedWeight S B U R pick pastLog newLog = 1 := by
  have hcond : ∀ a ∈ U, ∃ p, pd5b_label newLog a = some p ∧
      (a ∈ R → p = pick a ((pastLog ++ newLog).filter fun e =>
        pd5_birthIndex S B e.1 < pd5_birthIndex S B a)) := by
    intro a ha
    rcases hlabels a ha with ⟨p, hp⟩
    refine ⟨p, hp, ?_⟩
    intro haR
    exact hties a haR p hp
  unfold pd5_prescribedWeight
  rw [if_pos hcond]

private theorem pd5_constraintWeight_one_blocks {K : ℕ}
    (C : Finset (Finset (BirthAddress K))) (log : BirthLog K)
    (hW : constraintWeight C log = 1) :
    ∀ D ∈ C, ∃ v, ∀ a ∈ D, (a, v) ∈ log := by
  intro D hD
  have hnonzero : constraintWeight C log ≠ 0 := by rw [hW]; norm_num
  have hfactor := (Finset.prod_ne_zero_iff.mp hnonzero) D hD
  by_contra hn
  exact hfactor (by simp [constraintWeight, hn])

private def pd5_prefixConstraintOK {K : ℕ}
    (C : Finset (Finset (BirthAddress K))) (stage : ℕ) (L : BirthLog K) : Prop :=
  ∀ D ∈ C, ∃ p, ∀ a ∈ D, pd5_birthLayer a < stage → (a, p) ∈ L

private theorem pd5_prefixConstraintOK_extend {K : ℕ}
    (C : Finset (Finset (BirthAddress K))) (stage : ℕ)
    (L suffix : BirthLog K)
    (hSuffix : ∀ e ∈ suffix, stage ≤ pd5_birthLayer e.1)
    (hOK : pd5_prefixConstraintOK C stage (L ++ suffix)) :
    pd5_prefixConstraintOK C stage L := by
  intro D hD
  obtain ⟨p, hp⟩ := hOK D hD
  refine ⟨p, ?_⟩
  intro a ha hstage
  have hpair := hp a ha hstage
  rcases List.mem_append.mp hpair with hL | hS
  · exact hL
  · have hfuture := hSuffix (a, p) hS
    change stage ≤ pd5_birthLayer a at hfuture
    omega

private theorem pd5_prefixConstraintOK_bad_extend {K : ℕ}
    (C : Finset (Finset (BirthAddress K))) (stage : ℕ)
    (L suffix : BirthLog K)
    (hBad : ¬ pd5_prefixConstraintOK C stage L)
    (hSuffix : ∀ e ∈ suffix, stage ≤ pd5_birthLayer e.1) :
    ¬ pd5_prefixConstraintOK C stage (L ++ suffix) := by
  intro hOK
  exact hBad (pd5_prefixConstraintOK_extend C stage L suffix hSuffix hOK)

private theorem pd5_prefixConstraintOK_mono {K : ℕ}
    {C : Finset (Finset (BirthAddress K))} {stage₀ stage₁ : ℕ}
    {L : BirthLog K} (hstage : stage₀ ≤ stage₁)
    (hOK : pd5_prefixConstraintOK C stage₁ L) :
    pd5_prefixConstraintOK C stage₀ L := by
  intro D hD
  obtain ⟨p, hp⟩ := hOK D hD
  refine ⟨p, ?_⟩
  intro a ha hlt
  exact hp a ha (lt_of_lt_of_le hlt hstage)

private theorem pd5_constraintWeight_zero_of_bad_prefix {K : ℕ}
    (C : Finset (Finset (BirthAddress K))) (stage : ℕ)
    (L suffix : BirthLog K) (hbad : ¬ pd5_prefixConstraintOK C stage L)
    (hsuffix : ∀ e ∈ suffix, stage ≤ pd5_birthLayer e.1) :
    constraintWeight C (L ++ suffix) = 0 := by
  classical
  let fullLog := L ++ suffix
  by_contra hnonzero
  have hblocks : ∀ D ∈ C, ∃ v, ∀ a ∈ D, (a, v) ∈ fullLog := by
    intro D hD
    have hfactor := (Finset.prod_ne_zero_iff.mp hnonzero) D hD
    by_contra hmissing
    have hzero : (if ∃ v, ∀ a ∈ D, (a, v) ∈ fullLog then (1 : ℂ) else 0) = 0 :=
      if_neg hmissing
    exact hfactor hzero
  rcases not_forall.mp hbad with ⟨D, hDnot⟩
  have hD : D ∈ C := by
    by_contra hD
    exact hDnot (fun h => (hD h).elim)
  have hDbad : ¬ ∃ p, ∀ a ∈ D, pd5_birthLayer a < stage → (a, p) ∈ L := by
    intro hp
    exact hDnot (fun _ => hp)
  push_neg at hDbad
  obtain ⟨p, hp⟩ := hblocks D hD
  obtain ⟨a, ha, hstage, hnotL⟩ := hDbad p
  have hpair := hp a ha
  rcases List.mem_append.mp hpair with hL | hS
  · exact hnotL hL
  · have hfuture := hsuffix (a, p) hS
    change stage ≤ pd5_birthLayer a at hfuture
    omega

private theorem pd5_tsum_zero_of_pointwise_zero {α : Type*} (f : α → ℂ)
    (hf : ∀ a, f a = 0) : (∑' a, f a) = 0 := by
  simp [hf]

private theorem pd5_logGhost_zero_of_badPredicate {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (j : ℕ)
    (P : BirthLog K → Prop)
    (hAppend : ∀ L l p, P L → P (L ++ pd5_ghostBirthLog j l p))
    (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, P σL.2 → f σL = 0)
    (σL : LogPoint S.x K) (hσ : P σL.2) :
    logGhost F S ρ j f σL = 0 := by
  classical
  unfold logGhost
  apply Finset.sum_eq_zero
  intro D hD
  apply pd5_tsum_zero_of_pointwise_zero
  intro l
  apply Finset.sum_eq_zero
  intro new hnew
  by_cases hDsub : ∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1
  · let out := pd5_ghostOutput F S σL D l new j
    have hPout := hAppend σL.2 l (fun i k => (new i k : ℕ)) hσ
    have hfout : f out = 0 :=
      hf out (by simpa [out, pd5_ghostOutput, pd5_ghostBirthLog] using hPout)
    simp only [if_pos hDsub]
    change (((∏ i : Fin K, ghostGroupCoeff F S ρ j i
        (hitCount (σL.1.2.2 i) σL.1.1) (D i).card (l i)
        (List.ofFn fun k => (new i k : ℕ)) : ℝ) : ℂ) * f out) = 0
    rw [hfout]
    simp
  · simp [hDsub]

private theorem pd5_logEdgePiece_zero_of_badPredicate {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step : ℕ)
    (raw : Bool) (St Pr : Finset (Fin K))
    (P : BirthLog K → Prop)
    (hAppend : ∀ L s c, P L → P (L ++ edgeBirths F S step s c))
    (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, P σL.2 → f σL = 0)
    (σL : LogPoint S.x K) (hσ : P σL.2) :
    logEdgePiece F S ρ w step raw St Pr f σL = 0 := by
  classical
  unfold logEdgePiece
  apply Finset.sum_eq_zero
  intro c hc
  apply pd5_tsum_zero_of_pointwise_zero
  intro z'
  by_cases hcond : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
      EdgeAdmissible F S w σL.1 c z'
  · let out : LogPoint S.x K :=
      ((z', edgeTargetLists F S σL.1 c, edgeNewMemory F S σL.1 c),
        σL.2 ++ edgeBirths F S step σL.1 c)
    have hPout := hAppend σL.2 σL.1 c hσ
    have hfout : f out = 0 := hf out (by simp [out, hPout])
    simp [hcond, out, hfout]
  · simp [hcond]

private theorem pd5_logSym_zero_of_badPredicate {K : ℕ}
    (F : PDFix K) (S : PDScale) (P : BirthLog K → Prop)
    (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, P σL.2 → f σL = 0)
    (σL : LogPoint S.x K) (hσ : P σL.2) :
    logSym F S f σL = 0 := by
  classical
  unfold logSym
  have hsum : (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      f ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2)) = 0 := by
    apply Finset.sum_eq_zero
    intro σ hσ'
    exact hf ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2) hσ
  rw [hsum]
  simp

private theorem pd5_logEdge_zero_of_badPredicate {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step : ℕ)
    (P : BirthLog K → Prop)
    (hAppend : ∀ L s c, P L → P (L ++ edgeBirths F S step s c))
    (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, P σL.2 → f σL = 0)
    (σL : LogPoint S.x K) (hσ : P σL.2) :
    logEdge F S ρ w EdgeKind.full step f σL = 0 := by
  classical
  have hSym : ∀ τL, P τL.2 → logSym F S f τL = 0 :=
    fun τL hτ => pd5_logSym_zero_of_badPredicate F S P f hf τL hτ
  have hInside : ∀ τL, P τL.2 →
      (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S f) τL -
          logEdgePiece F S ρ w step false St Pr (logSym F S f) τL)) = 0 := by
    intro τL hτ
    apply Finset.sum_eq_zero
    intro St hSt
    apply Finset.sum_eq_zero
    intro Pr hPr
    rw [pd5_logEdgePiece_zero_of_badPredicate F S ρ w step true St Pr P hAppend
          (logSym F S f) hSym τL hτ,
        pd5_logEdgePiece_zero_of_badPredicate F S ρ w step false St Pr P hAppend
          (logSym F S f) hSym τL hτ]
    ring
  have hOuter : ∀ τL, P τL.2 →
      logSym F S (fun τ =>
        ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          (logEdgePiece F S ρ w step true St Pr (logSym F S f) τ -
            logEdgePiece F S ρ w step false St Pr (logSym F S f) τ)) τL = 0 := by
    intro τL hτ
    exact pd5_logSym_zero_of_badPredicate F S P
      (fun τ =>
        ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          (logEdgePiece F S ρ w step true St Pr (logSym F S f) τ -
            logEdgePiece F S ρ w step false St Pr (logSym F S f) τ))
      hInside τL hτ
  unfold logEdge
  simp only [EdgeKind.full]
  exact hOuter σL hσ

private theorem pd5_layer_weight_gives_prescription {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hSys : IsConstraintSystem A C)
    (U R : Finset (BirthAddress K)) (hRU : R ⊆ U)
    (hUsupport : U ⊆ C.biUnion id)
    (fullLog pastLog newLog : BirthLog K) (hW : constraintWeight C fullLog = 1)
    (hNewNodup : (newLog.map Prod.fst).Nodup)
    (hPrefixNodup : ∀ (a : BirthAddress K),
      (((pastLog ++ newLog).filter fun e =>
        pd5_birthIndex S B e.1 < pd5_birthIndex S B a).map Prod.fst).Nodup)
    (hCurrent : ∀ (a : BirthAddress K), a ∈ U → ∀ v,
      (a, v) ∈ fullLog → (a, v) ∈ newLog)
    (hPivotEarlier : ∀ (a : BirthAddress K), a ∈ R → ∀ v,
      (pd5_addressPivot S B hSys a, v) ∈ fullLog →
        (pd5_addressPivot S B hSys a, v) ∈
          ((pastLog ++ newLog).filter fun e =>
            pd5_birthIndex S B e.1 < pd5_birthIndex S B a)) :
    pd5_prescribedWeight S B U R (pd5_addressPick S B hSys) pastLog newLog = 1 := by
  have hblocks : ∀ D ∈ C, ∃ v, ∀ a ∈ D, (a, v) ∈ fullLog :=
    pd5_constraintWeight_one_blocks C fullLog hW
  have hlabels : ∀ a ∈ U, ∃ p, pd5b_label newLog a = some p := by
    intro a ha
    have haSupport : a ∈ C.biUnion id := hUsupport ha
    rcases Finset.mem_biUnion.mp haSupport with ⟨D, hD, haD⟩
    obtain ⟨v, hv⟩ := hblocks D hD
    have hnew : (a, v) ∈ newLog := hCurrent a ha v (hv a haD)
    exact ⟨v, (pd5b_label_spec hNewNodup a v).2 hnew⟩
  have hties : ∀ a ∈ R, ∀ p, pd5b_label newLog a = some p →
      p = pd5_addressPick S B hSys a ((pastLog ++ newLog).filter fun e =>
        pd5_birthIndex S B e.1 < pd5_birthIndex S B a) := by
    intro a haR p hp
    have haU := hRU haR
    have haSupport : a ∈ C.biUnion id := hUsupport haU
    let D := pd5_addressBlock C a haSupport
    have hDsys := pd5_addressBlock_spec C a haSupport
    obtain ⟨v, hv⟩ := hblocks D hDsys.1
    have haNew : (a, v) ∈ newLog := hCurrent a haU v (hv a hDsys.2)
    have hpNew : (a, p) ∈ newLog := (pd5b_label_spec hNewNodup a p).1 hp
    have hlabelV : pd5b_label newLog a = some v :=
      (pd5b_label_spec hNewNodup a v).2 haNew
    have hpv : p = v := Option.some.inj (hp.symm.trans hlabelV)
    have hpivotD := pd5_addressPivot_spec S B hSys a haSupport
    have hpivotFull : (pd5_addressPivot S B hSys a, v) ∈ fullLog :=
      hv (pd5_addressPivot S B hSys a) hpivotD.1
    have hpivotPrefix := hPivotEarlier a haR v hpivotFull
    have hpivotLabel := (pd5b_label_spec (hPrefixNodup a)
      (pd5_addressPivot S B hSys a) v).2 hpivotPrefix
    have hpick : pd5_addressPick S B hSys a
        ((pastLog ++ newLog).filter fun e =>
          pd5_birthIndex S B e.1 < pd5_birthIndex S B a) = v := by
      unfold pd5_addressPick
      rw [dif_pos haSupport]
      exact congrArg (fun o : Option ℕ => o.getD 0) hpivotLabel
    rw [hpick]
    exact hpv
  exact pd5_prescribedWeight_eq_one_of_labels S B U R
    (pd5_addressPick S B hSys) pastLog newLog hlabels hties

private theorem pd5_layer_gate_of_log_parts {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hSys : IsConstraintSystem A C)
    (U R : Finset (BirthAddress K)) (hRU : R ⊆ U)
    (hUsupport : U ⊆ C.biUnion id)
    (fullLog pastLog newLog futureLog : BirthLog K)
    (hFull : fullLog = pastLog ++ newLog ++ futureLog)
    (hW : constraintWeight C fullLog = 1)
    (hNewNodup : (newLog.map Prod.fst).Nodup)
    (hPrefixNodup : ∀ (a : BirthAddress K),
      (((pastLog ++ newLog).filter fun e =>
        pd5_birthIndex S B e.1 < pd5_birthIndex S B a).map Prod.fst).Nodup)
    (hPastCurrent : ∀ a ∈ U, ∀ v, (a, v) ∉ pastLog)
    (hFutureCurrent : ∀ a ∈ U, ∀ v, (a, v) ∉ futureLog)
    (hStrict : ∀ a ∈ R,
      pd5_birthIndex S B (pd5_addressPivot S B hSys a) < pd5_birthIndex S B a)
    (hPastPivot : ∀ a ∈ R, ∀ v, (pd5_addressPivot S B hSys a, v) ∈ pastLog →
      (pd5_addressPivot S B hSys a, v) ∈
        ((pastLog ++ newLog).filter fun e =>
          pd5_birthIndex S B e.1 < pd5_birthIndex S B a))
    (hFuturePivot : ∀ a ∈ R, ∀ v, (pd5_addressPivot S B hSys a, v) ∉ futureLog) :
    pd5_prescribedWeight S B U R (pd5_addressPick S B hSys) pastLog newLog = 1 := by
  have hCurrent : ∀ a ∈ U, ∀ v, (a, v) ∈ fullLog → (a, v) ∈ newLog := by
    intro a ha v hmem
    have hparts : (a, v) ∈ pastLog ∨ (a, v) ∈ newLog ∨ (a, v) ∈ futureLog := by
      rw [hFull] at hmem
      simpa [List.mem_append] using hmem
    rcases hparts with hpast | hnew | hfuture
    · exact (hPastCurrent a ha v hpast).elim
    · exact hnew
    · exact (hFutureCurrent a ha v hfuture).elim
  have hPivotEarlier : ∀ a ∈ R, ∀ v,
      (pd5_addressPivot S B hSys a, v) ∈ fullLog →
        (pd5_addressPivot S B hSys a, v) ∈
          ((pastLog ++ newLog).filter fun e =>
            pd5_birthIndex S B e.1 < pd5_birthIndex S B a) := by
    intro a ha v hmem
    have hparts :
        (pd5_addressPivot S B hSys a, v) ∈ pastLog ∨
          (pd5_addressPivot S B hSys a, v) ∈ newLog ∨
            (pd5_addressPivot S B hSys a, v) ∈ futureLog := by
      rw [hFull] at hmem
      simpa [List.mem_append] using hmem
    rcases hparts with hpast | hnew | hfuture
    · exact hPastPivot a ha v hpast
    · apply List.mem_filter.mpr
      exact ⟨List.mem_append_right _ hnew, by simp [hStrict a ha]⟩
    · exact (hFuturePivot a ha v hfuture).elim
  exact pd5_layer_weight_gives_prescription S B hSys U R hRU hUsupport
    fullLog pastLog newLog hW hNewNodup hPrefixNodup hCurrent hPivotEarlier

private theorem pd5_stage_gate_of_future {K : ℕ} (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) (hA : A ⊆ birthAddresses S.x K B)
    (U R : Finset (BirthAddress K)) (hRU : R ⊆ U)
    (hUsupport : U ⊆ C.biUnion id) (stage : ℕ)
    (hULayer : ∀ a ∈ U, pd5_birthLayer a = stage)
    (hStrict : ∀ a ∈ R,
      pd5_birthIndex S B (pd5_addressPivot S B (Finset.mem_filter.mp hC).2 a) <
        pd5_birthIndex S B a)
    (fullLog pastLog newLog futureLog : BirthLog K)
    (hFull : fullLog = pastLog ++ newLog ++ futureLog)
    (hW : constraintWeight C fullLog = 1)
    (hNewNodup : (newLog.map Prod.fst).Nodup)
    (hPrefixNodup : ∀ (a : BirthAddress K),
      (((pastLog ++ newLog).filter fun e =>
        pd5_birthIndex S B e.1 < pd5_birthIndex S B a).map Prod.fst).Nodup)
    (hPastLayer : ∀ e ∈ pastLog, pd5_birthLayer e.1 < stage)
    (hFutureLayer : ∀ e ∈ futureLog, stage < pd5_birthLayer e.1) :
    pd5_prescribedWeight S B U R
      (pd5_addressPick S B (Finset.mem_filter.mp hC).2) pastLog newLog = 1 := by
  let hSys : IsConstraintSystem A C := (Finset.mem_filter.mp hC).2
  have hPastCurrent : ∀ a ∈ U, ∀ v, (a, v) ∉ pastLog := by
    intro a ha v hmem
    have hsmall := hPastLayer (a, v) hmem
    rw [hULayer a ha] at hsmall
    exact (Nat.lt_irrefl stage hsmall).elim
  have hFutureCurrent : ∀ a ∈ U, ∀ v, (a, v) ∉ futureLog := by
    intro a ha v hmem
    have hlarge := hFutureLayer (a, v) hmem
    rw [hULayer a ha] at hlarge
    exact (Nat.lt_irrefl stage hlarge).elim
  have hPastPivot : ∀ a ∈ R, ∀ v,
      (pd5_addressPivot S B hSys a, v) ∈ pastLog →
        (pd5_addressPivot S B hSys a, v) ∈
          ((pastLog ++ newLog).filter fun e =>
            pd5_birthIndex S B e.1 < pd5_birthIndex S B a) := by
    intro a ha v hmem
    have haU := hRU ha
    have haSupport := hUsupport haU
    have haA : a ∈ birthAddresses S.x K B :=
      hA (pd5_constraint_support_subset hC haSupport)
    have hpivotD := pd5_addressPivot_spec S B hSys a haSupport
    let D := pd5_addressBlock C a haSupport
    have hDsys := pd5_addressBlock_spec C a haSupport
    have hpivotA : pd5_addressPivot S B hSys a ∈ A :=
      pd5_constraint_support_subset hC
        (Finset.mem_biUnion.mpr ⟨D, hDsys.1, hpivotD.1⟩)
    have hpivotBirth : pd5_addressPivot S B hSys a ∈ birthAddresses S.x K B :=
      hA hpivotA
    exact pd5_pastPair_mem_filter S B pastLog newLog a
      (by
        intro e he
        rw [hULayer a haU]
        exact hPastLayer e he)
      haA hpivotBirth hmem
  have hFuturePivot : ∀ a ∈ R, ∀ v,
      (pd5_addressPivot S B hSys a, v) ∉ futureLog := by
    intro a ha v hmem
    have haU := hRU ha
    have hcur := hULayer a haU
    have hfuture := hFutureLayer (pd5_addressPivot S B hSys a, v) hmem
    have haSupport := hUsupport haU
    have haA : a ∈ birthAddresses S.x K B :=
      hA (pd5_constraint_support_subset hC haSupport)
    have hpivotD := pd5_addressPivot_spec S B hSys a haSupport
    let D := pd5_addressBlock C a haSupport
    have hDsys := pd5_addressBlock_spec C a haSupport
    have hpivotA : pd5_addressPivot S B hSys a ∈ A :=
      pd5_constraint_support_subset hC
        (Finset.mem_biUnion.mpr ⟨D, hDsys.1, hpivotD.1⟩)
    have hpivotBirth : pd5_addressPivot S B hSys a ∈ birthAddresses S.x K B :=
      hA hpivotA
    have hLayerLt : pd5_birthLayer a <
        pd5_birthLayer (pd5_addressPivot S B hSys a) := by
      rw [hcur]
      exact hfuture
    have hidx := pd5_birthIndex_lt_of_layer_lt S B haA hpivotBirth hLayerLt
    exact (Nat.lt_asymm (hStrict a ha) hidx).elim
  exact pd5_layer_gate_of_log_parts S B hSys U R hRU hUsupport
    fullLog pastLog newLog futureLog hFull hW hNewNodup hPrefixNodup
    hPastCurrent hFutureCurrent hStrict hPastPivot hFuturePivot

private theorem pd5_sum_boundedLengths_eq_univ {K B : ℕ}
    (f : (Fin K → ℕ) → ℝ) :
    (∑ l ∈ pd5_boundedLengths K B, f l) =
      ∑ l : Fin K → Fin (B + 1), f (fun i => (l i).val) := by
  classical
  unfold pd5_boundedLengths
  apply Finset.sum_bij (fun l hl => fun i =>
    ⟨l i, Nat.lt_succ_of_le ((pd5_mem_boundedLengths).mp hl i)⟩)
  · intro l hl
    exact Finset.mem_univ _
  · intro l hl l' hl' heq
    funext i
    exact congrArg (fun q : Fin K → Fin (B + 1) => (q i).val) heq
  · intro l hl
    refine ⟨fun i => (l i).val, ?_, ?_⟩
    · apply (pd5_mem_boundedLengths).2
      intro i
      exact Nat.le_of_lt_succ (l i).isLt
    · funext i
      exact Fin.ext rfl
  · intro l hl
    rfl

private theorem pd5_mem_removeIndices {l : List Particle}
    {D : Finset (Fin l.length)} {a : Particle}
    (ha : a ∈ removeIndices l D) : a ∈ l := by
  unfold removeIndices at ha
  simp only [List.mem_filterMap] at ha
  rcases ha with ⟨k, hk, hsome⟩
  by_cases hD : k ∈ D
  · simp [hD] at hsome
  · simp [hD] at hsome
    exact hsome ▸ List.get_mem l k

private theorem pd5_log_append_nodup_of_layer_separation {K : ℕ}
    (past newLog : BirthLog K) (stage : ℕ)
    (hPast : (past.map Prod.fst).Nodup)
    (hNew : (newLog.map Prod.fst).Nodup)
    (hPastLayer : ∀ e ∈ past, pd5_birthLayer e.1 < stage)
    (hNewLayer : ∀ e ∈ newLog, pd5_birthLayer e.1 = stage) :
    ((past ++ newLog).map Prod.fst).Nodup := by
  rw [List.map_append]
  apply List.nodup_append'.2
  refine ⟨hPast, hNew, ?_⟩
  apply List.disjoint_left.mpr
  intro a ha hb
  rcases List.mem_map.mp ha with ⟨e, he, rfl⟩
  rcases List.mem_map.mp hb with ⟨f, hf, hEq⟩
  have h1 := hPastLayer e he
  have h2 := hNewLayer f hf
  rw [hEq] at h2
  omega

private theorem pd5_filtered_projection_nodup {K : ℕ}
    (L : BirthLog K) (P : BirthAddress K → Prop) [DecidablePred P]
    [DecidablePred (fun e : BirthAddress K × ℕ => P e.1)]
    (hL : (L.map Prod.fst).Nodup) :
    ((L.filter fun e => P e.1).map Prod.fst).Nodup := by
  have hmap : (L.filter fun e => P e.1).map Prod.fst =
      (L.map Prod.fst).filter P := by
    induction L with
    | nil => rfl
    | cons e L ih =>
        have hTail := (List.nodup_cons.mp hL).2
        by_cases hP : P e.1 <;> simp [List.filter_cons, hP, ih hTail]
  rw [hmap]
  exact hL.filter P

private theorem pd5_ghost_output_region {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (B : ℕ)
    (sL : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length))
    (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
    (j : ℕ) (hState : pd5_stateRegion F S w B sL.1)
    (hDel : ∀ i, D i ⊆ hitIndices (sL.1.2.2 i) sL.1.1)
    (hCut : memSize (pd5_ghostOutput F S sL D l new j).1 ≤ B) :
    pd5_stateRegion F S w B (pd5_ghostOutput F S sL D l new j).1 := by
  rcases hState with ⟨hvalid, _, hpos⟩
  have hvalid' : MemValid F S (pd5_ghostOutput F S sL D l new j).1 := by
    refine ⟨hvalid.1, hvalid.2.1, ?_⟩
    intro i e he
    change e ∈ removeIndices (sL.1.2.2 i) (D i) ++
      List.ofFn fun k => anchorAt (new i k) sL.1.1 at he
    rcases List.mem_append.mp he with hrem | hnew
    · exact hvalid.2.2 i e (pd5_mem_removeIndices hrem)
    · rcases List.mem_ofFn.mp hnew with ⟨k, hEq⟩
      rw [← hEq]
      constructor
      · exact (new i k).property
      · have hproj := (projLine (new i k) sL.1.1).isLt
        simp [anchorAt]
        omega
  refine ⟨hvalid', hCut, ?_⟩
  simpa [pd5_ghostOutput] using hpos

private theorem pd5_edge_output_region {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (B : ℕ)
    (s : MemPoint S.x K)
    (choice : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (z' : ℤ × ℤ) (hState : pd5_stateRegion F S w B s)
    (hAdm : EdgeAdmissible F S w s choice z')
    (hCut : memSize (z', edgeTargetLists F S s choice,
      edgeNewMemory F S s choice) ≤ B) :
    pd5_stateRegion F S w B
      (z', edgeTargetLists F S s choice, edgeNewMemory F S s choice) := by
  rcases hState with ⟨hvalid, _, _⟩
  rcases hAdm with ⟨_, _, htarget, _, _, hgcd, _, htargetBox, _, _⟩
  have hvalid' : MemValid F S
      (z', edgeTargetLists F S s choice, edgeNewMemory F S s choice) := by
    refine ⟨hgcd, (fun i j => (htarget.1 i j).2), ?_⟩
    intro i e he
    change e ∈ removeIndices (s.2.2 i)
        (match (choice i).2 with
          | Sum.inl k => {k}
          | Sum.inr _ => ∅) ++
        (if (choice i).1 then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else []) at he
    rcases List.mem_append.mp he with hrem | hstored
    · exact hvalid.2.2 i e (pd5_mem_removeIndices hrem)
    · by_cases hstore : (choice i).1
      · simp [hstore] at hstored
        have heq : e = anchorAt (s.2.1 i (lastSlot S.x)) s.1 :=
          hstored
        subst e
        constructor
        · exact hvalid.2.1 i (lastSlot S.x)
        · have hline := (projLine (s.2.1 i (lastSlot S.x)) s.1).isLt
          simp [anchorAt]
          omega
      · simp [hstore] at hstored
  refine ⟨hvalid', hCut, Or.inr htargetBox⟩

private theorem pd5_prescribedWeight_bounds {K : ℕ} (S : PDScale) (B : ℕ)
    (U R : Finset (BirthAddress K)) (pick : BirthAddress K → BirthLog K → ℕ)
    (pastLog newLog : BirthLog K) :
    0 ≤ pd5_prescribedWeight S B U R pick pastLog newLog ∧
      pd5_prescribedWeight S B U R pick pastLog newLog ≤ 1 := by
  unfold pd5_prescribedWeight
  split_ifs <;> norm_num

private theorem pd5_constraintWeight_norm_le_one {K : ℕ}
    (C : Finset (Finset (BirthAddress K))) (L : BirthLog K) :
    ‖constraintWeight C L‖ ≤ 1 := by
  classical
  unfold constraintWeight
  induction C using Finset.induction_on with
  | empty => simp
  | @insert D C hD ih =>
      rw [Finset.prod_insert hD]
      have hfac :
          ‖(if ∃ v, ∀ a ∈ D, (a, v) ∈ L then (1 : ℂ) else 0)‖ ≤ 1 := by
        split_ifs <;> norm_num
      calc
        ‖(if ∃ v, ∀ a ∈ D, (a, v) ∈ L then (1 : ℂ) else 0) *
            ∏ D' ∈ C, if ∃ v, ∀ a ∈ D', (a, v) ∈ L then (1 : ℂ) else 0‖ =
          ‖(if ∃ v, ∀ a ∈ D, (a, v) ∈ L then (1 : ℂ) else 0)‖ *
            ‖∏ D' ∈ C, if ∃ v, ∀ a ∈ D', (a, v) ∈ L then (1 : ℂ) else 0‖ :=
              norm_mul _ _
        _ ≤ 1 * 1 := mul_le_mul hfac ih (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num

private theorem pd5_logBoundaryOut_constraint_norm_le_one {K : ℕ} {x : ℝ}
    (C : Finset (Finset (BirthAddress K))) (σL : LogPoint x K) :
    ‖logBoundaryOut (constraintWeight C) σL‖ ≤ 1 := by
  by_cases h : σL.1.1 = (1, 0) ∧ ∀ i, σL.1.2.2 i = []
  · have hweight := pd5_constraintWeight_norm_le_one C σL.2
    simpa [logBoundaryOut, memBoundary, h] using hweight
  · simp [logBoundaryOut, memBoundary, h]

private theorem pd5_logGhost_norm_le_absChoice {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (j B : ℕ)
    (W : BirthLog K → ℝ) (f : LogPoint S.x K → ℂ)
    (c v : ℝ) (sL : LogPoint S.x K)
    (hsource : memSize sL.1 ≤ B)
    (hc : 0 ≤ c) (hv : 0 ≤ v) (hW : ∀ L, 0 ≤ W L)
    (hBound : ∀ (D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length))
        (l : Fin K → ℕ)
        (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)),
        (∀ i, D i ⊆ hitIndices (sL.1.2.2 i) sL.1.1) →
        memSize (pd5_ghostOutput F S sL D l new j).1 ≤ B →
        ‖logTrunc (some B) f (pd5_ghostOutput F S sL D l new j)‖ ≤
          c * W (pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))) *
            v ^ memSize (pd5_ghostOutput F S sL D l new j).1) :
    ‖logGhost F S ρ j (logTrunc (some B) f) sL‖ ≤
      c * pd5_ghostAbsChoice F S ρ j B W (fun s => v ^ memSize s) sL.1 := by
  classical
  rw [pd5_logGhost_truncated_finite F S ρ j B f sL]
  have hterm (D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length))
      (l : Fin K → ℕ) :
      ‖pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) f)‖ ≤
        ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
          if (∀ i, D i ⊆ hitIndices (sL.1.2.2 i) sL.1.1) ∧
              memSize (pd5_ghostOutput F S sL D l new j).1 ≤ B then
            |∏ i : Fin K, ghostGroupCoeff F S ρ j i
                (hitCount (sL.1.2.2 i) sL.1.1) (D i).card (l i)
                (List.ofFn fun k => (new i k : ℕ))| *
              c * W (pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))) *
                v ^ memSize (pd5_ghostOutput F S sL D l new j).1
          else 0 := by
    unfold pd5_ghostLengthTerm
    calc
      _ ≤ ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
            ‖if ∀ i, D i ⊆ hitIndices (sL.1.2.2 i) sL.1.1 then
              pd5_ghostWeight F S ρ j sL D l new *
                logTrunc (some B) f (pd5_ghostOutput F S sL D l new j)
            else 0‖ := norm_sum_le _ _
      _ ≤ ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
            if (∀ i, D i ⊆ hitIndices (sL.1.2.2 i) sL.1.1) ∧
                memSize (pd5_ghostOutput F S sL D l new j).1 ≤ B then
              |∏ i : Fin K, ghostGroupCoeff F S ρ j i
                  (hitCount (sL.1.2.2 i) sL.1.1) (D i).card (l i)
                  (List.ofFn fun k => (new i k : ℕ))| *
                c * W (pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))) *
                  v ^ memSize (pd5_ghostOutput F S sL D l new j).1
            else 0 := by
          apply Finset.sum_le_sum
          intro new hnew
          by_cases hdel : ∀ i, D i ⊆ hitIndices (sL.1.2.2 i) sL.1.1
          · by_cases hcut : memSize (pd5_ghostOutput F S sL D l new j).1 ≤ B
            · have hfun := hBound D l new hdel hcut
              have hweight :
                  ‖pd5_ghostWeight F S ρ j sL D l new‖ =
                    |∏ i : Fin K, ghostGroupCoeff F S ρ j i
                      (hitCount (sL.1.2.2 i) sL.1.1) (D i).card (l i)
                        (List.ofFn fun k => (new i k : ℕ))| := by
                simp [pd5_ghostWeight, Finset.abs_prod]
              simp only [if_pos hdel, if_pos (And.intro hdel hcut)]
              rw [norm_mul, hweight]
              have hnonneg : 0 ≤ c * W
                  (pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))) *
                    v ^ memSize (pd5_ghostOutput F S sL D l new j).1 :=
                mul_nonneg (mul_nonneg hc (hW _)) (pow_nonneg hv _)
              calc
                _ ≤ |∏ i : Fin K, ghostGroupCoeff F S ρ j i
                      (hitCount (sL.1.2.2 i) sL.1.1) (D i).card (l i)
                      (List.ofFn fun k => (new i k : ℕ))| *
                    (c * W (pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))) *
                      v ^ memSize (pd5_ghostOutput F S sL D l new j).1) :=
                  mul_le_mul_of_nonneg_left hfun (abs_nonneg _)
                _ = _ := by ring
            · simp [hdel, hcut, logTrunc]
          · simp [hdel]
  calc
    ‖∑ D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length),
        ∑ l ∈ pd5_boundedLengths K B,
          pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) f)‖ ≤
      ∑ D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length),
        ∑ l ∈ pd5_boundedLengths K B,
          ‖pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) f)‖ := by
        calc
          _ ≤ ∑ D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length),
              ‖∑ l ∈ pd5_boundedLengths K B,
                pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) f)‖ :=
            norm_sum_le _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro D hD
            exact norm_sum_le _ _
    _ ≤ ∑ D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length),
        ∑ l ∈ pd5_boundedLengths K B,
          ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
            if (∀ i, D i ⊆ hitIndices (sL.1.2.2 i) sL.1.1) ∧
                memSize (pd5_ghostOutput F S sL D l new j).1 ≤ B then
              |∏ i : Fin K, ghostGroupCoeff F S ρ j i
                  (hitCount (sL.1.2.2 i) sL.1.1) (D i).card (l i)
                  (List.ofFn fun k => (new i k : ℕ))| *
                c * W (pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))) *
                  v ^ memSize (pd5_ghostOutput F S sL D l new j).1
            else 0 := by
        apply Finset.sum_le_sum
        intro D hD
        apply Finset.sum_le_sum
        intro l hl
        exact hterm D l
    _ = c * pd5_ghostAbsChoice F S ρ j B W
        (fun s => v ^ memSize s) sL.1 := by
        unfold pd5_ghostAbsChoice
        simp only [if_pos hsource]
        simp_rw [pd5_sum_boundedLengths_eq_univ]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D hD
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro new hnew
        by_cases hguard :
            (∀ i, D i ⊆ hitIndices (sL.1.2.2 i) sL.1.1) ∧
              memSize (pd5_ghostOutput F S sL D (fun i => (l i).val) new j).1 ≤ B
        · dsimp [pd5_ghostOutput] at hguard ⊢
          simp [hguard]
          ring_nf
        · dsimp [pd5_ghostOutput] at hguard ⊢
          simp [hguard]

private theorem pd5_logSym_norm_le_uniform {K : ℕ}
    (F : PDFix K) (S : PDScale) (f : LogPoint S.x K → ℂ)
    (sL : LogPoint S.x K) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      ‖f ((sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2), sL.2)‖ ≤ A) :
    ‖logSym F S f sL‖ ≤ A := by
  classical
  have hnNat : 0 < permCount S.x K := by
    unfold permCount
    exact Fintype.card_pos_iff.mpr ⟨1⟩
  have hn : 0 < (permCount S.x K : ℝ) := by exact_mod_cast hnNat
  have hinv : ‖(permCount S.x K : ℂ)⁻¹‖ = (permCount S.x K : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  have hsum :
      ‖∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        f ((sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2), sL.2)‖ ≤
        (permCount S.x K : ℝ) * A := by
    calc
      _ ≤ ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ‖f ((sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2), sL.2)‖ := norm_sum_le _ _
      _ ≤ ∑ _σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), A := by
        apply Finset.sum_le_sum
        intro σ hσ
        exact hbound σ
      _ = (permCount S.x K : ℝ) * A := by simp [permCount]
  unfold logSym
  calc
    _ ≤ ‖(permCount S.x K : ℂ)⁻¹‖ *
        ‖∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          f ((sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2), sL.2)‖ := norm_mul_le _ _
    _ ≤ (permCount S.x K : ℝ)⁻¹ * ((permCount S.x K : ℝ) * A) := by
      rw [hinv]
      exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = A := by field_simp [ne_of_gt hn]

private theorem pd5_logSym_norm_le_average {K : ℕ}
    (F : PDFix K) (S : PDScale) (f : LogPoint S.x K → ℂ)
    (sL : LogPoint S.x K) :
    ‖logSym F S f sL‖ ≤
      (permCount S.x K : ℝ)⁻¹ *
        ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ‖f ((sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2), sL.2)‖ := by
  classical
  have hnNat : 0 < permCount S.x K := by
    unfold permCount
    exact Fintype.card_pos_iff.mpr ⟨1⟩
  have hn : 0 < (permCount S.x K : ℝ) := by exact_mod_cast hnNat
  have hinv : ‖(permCount S.x K : ℂ)⁻¹‖ = (permCount S.x K : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  unfold logSym
  calc
    _ ≤ ‖(permCount S.x K : ℂ)⁻¹‖ *
        ‖∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          f ((sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2), sL.2)‖ := norm_mul_le _ _
    _ ≤ (permCount S.x K : ℝ)⁻¹ *
        ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ‖f ((sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2), sL.2)‖ := by
      rw [hinv]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)

private theorem pd5_stateRegion_permute {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (B : ℕ)
    (s : MemPoint S.x K) (σ : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (hState : pd5_stateRegion F S w B s) :
    pd5_stateRegion F S w B (s.1, permuteLists σ s.2.1, s.2.2) := by
  rcases hState with ⟨⟨hgcd, hactive, hmemory⟩, hcut, hpos⟩
  refine ⟨⟨hgcd, ?_, hmemory⟩, ?_, ?_⟩
  · intro i j
    exact hactive i (σ i j)
  · simpa [memSize] using hcut
  · exact hpos

private theorem pd5_logEdgePiece_norm_le_absChoice {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step B : ℕ)
    (raw : Bool) (St Pr : Finset (Fin K))
    (g : LogPoint S.x K → ℂ) (sL : LogPoint S.x K)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite)
    (W : BirthLog K → ℝ) (c v : ℝ)
    (hc : 0 ≤ c) (hv : 0 ≤ v) (hW : ∀ L, 0 ≤ W L)
    (hBound : ∀ (choice : (i : Fin K) → EdgeChoice S.x F.a (sL.1.2.2 i) i)
        (z' : ℤ × ℤ), EdgeAdmissible F S w sL.1 choice z' →
        memSize (z', edgeTargetLists F S sL.1 choice,
          edgeNewMemory F S sL.1 choice) ≤ B →
        ‖g ((z', edgeTargetLists F S sL.1 choice,
              edgeNewMemory F S sL.1 choice),
            sL.2 ++ edgeBirths F S step sL.1 choice)‖ ≤
          c * W (edgeBirths F S step sL.1 choice) *
            v ^ memSize (z', edgeTargetLists F S sL.1 choice,
              edgeNewMemory F S sL.1 choice))
    (hzero : ∀ (choice : (i : Fin K) → EdgeChoice S.x F.a (sL.1.2.2 i) i)
      (z' : ℤ × ℤ), EdgeAdmissible F S w sL.1 choice z' →
        ¬ memSize (z', edgeTargetLists F S sL.1 choice,
          edgeNewMemory F S sL.1 choice) ≤ B →
        g ((z', edgeTargetLists F S sL.1 choice,
              edgeNewMemory F S sL.1 choice),
            sL.2 ++ edgeBirths F S step sL.1 choice) = 0) :
    ‖logEdgePiece F S ρ w step raw St Pr g sL‖ ≤
      ∑ choice : (i : Fin K) → EdgeChoice S.x F.a (sL.1.2.2 i) i,
        ∑ z' ∈ hbox.toFinset,
          if edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
              EdgeAdmissible F S w sL.1 choice z' ∧
                memSize (z', edgeTargetLists F S sL.1 choice,
                  edgeNewMemory F S sL.1 choice) ≤ B then
            |ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1) *
              (∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i) *
                ρ ^ (∑ i : Fin K,
                  hitCount (edgeNewMemory F S sL.1 choice i) z')| *
              ‖edgeMultiplier F S (decide (step % 2 = 0)) raw
                sL.1.2.1 (edgeTargetLists F S sL.1 choice) sL.1.1 z'‖ *
              c * W (edgeBirths F S step sL.1 choice) *
                v ^ memSize (z', edgeTargetLists F S sL.1 choice,
                  edgeNewMemory F S sL.1 choice)
          else 0 := by
  classical
  rw [pd5_logEdgePiece_finite F S ρ w step raw St Pr g sL hbox]
  calc
    _ ≤ ∑ choice : (i : Fin K) → EdgeChoice S.x F.a (sL.1.2.2 i) i,
        ‖∑ z' ∈ hbox.toFinset,
          if edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
              EdgeAdmissible F S w sL.1 choice z' then
            ((ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1) *
              (∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i) *
                ρ ^ (∑ i : Fin K, hitCount
                  (edgeNewMemory F S sL.1 choice i) z') : ℝ) : ℂ) *
              edgeMultiplier F S (decide (step % 2 = 0)) raw sL.1.2.1
                (edgeTargetLists F S sL.1 choice) sL.1.1 z' *
              (g ((z', edgeTargetLists F S sL.1 choice,
                edgeNewMemory F S sL.1 choice),
                sL.2 ++ edgeBirths F S step sL.1 choice))
          else 0‖ := norm_sum_le _ _
    _ ≤ ∑ choice : (i : Fin K) → EdgeChoice S.x F.a (sL.1.2.2 i) i,
        ∑ z' ∈ hbox.toFinset,
          ‖if edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
              EdgeAdmissible F S w sL.1 choice z' then
            ((ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1) *
              (∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i) *
                ρ ^ (∑ i : Fin K, hitCount
                  (edgeNewMemory F S sL.1 choice i) z') : ℝ) : ℂ) *
              edgeMultiplier F S (decide (step % 2 = 0)) raw sL.1.2.1
                (edgeTargetLists F S sL.1 choice) sL.1.1 z' *
              (g ((z', edgeTargetLists F S sL.1 choice,
                edgeNewMemory F S sL.1 choice),
                sL.2 ++ edgeBirths F S step sL.1 choice))
          else 0‖ := by
          apply Finset.sum_le_sum
          intro choice hchoice
          exact norm_sum_le _ _
    _ ≤ _ := by
          apply Finset.sum_le_sum
          intro choice hchoice
          apply Finset.sum_le_sum
          intro z' hz'
          by_cases hset : edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr
          · by_cases hAdm : EdgeAdmissible F S w sL.1 choice z'
            · by_cases hcut : memSize
                  (z', edgeTargetLists F S sL.1 choice,
                    edgeNewMemory F S sL.1 choice) ≤ B
              · have hfun := hBound choice z' hAdm hcut
                have hcoeff :
                    ‖((ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1) *
                      (∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i) *
                        ρ ^ (∑ i : Fin K, hitCount
                          (edgeNewMemory F S sL.1 choice i) z') : ℝ) : ℂ)‖ =
                    |ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1) *
                      (∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i) *
                        ρ ^ (∑ i : Fin K, hitCount
                          (edgeNewMemory F S sL.1 choice i) z')| := by
                  simp only [Complex.norm_real, Real.norm_eq_abs]
                have hterm : edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
                    EdgeAdmissible F S w sL.1 choice z' :=
                  ⟨hset.1, hset.2, hAdm⟩
                have hrow : edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
                    EdgeAdmissible F S w sL.1 choice z' ∧
                      memSize (z', edgeTargetLists F S sL.1 choice,
                        edgeNewMemory F S sL.1 choice) ≤ B :=
                  ⟨hset.1, hset.2, hAdm, hcut⟩
                simp only [if_pos hterm, if_pos hrow]
                simp only [norm_mul, hcoeff]
                have hnonneg :
                    0 ≤ c * W (edgeBirths F S step sL.1 choice) *
                      v ^ memSize (z', edgeTargetLists F S sL.1 choice,
                        edgeNewMemory F S sL.1 choice) :=
                  mul_nonneg (mul_nonneg hc (hW _)) (pow_nonneg hv _)
                calc
                  _ ≤ |ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1) *
                        (∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i) *
                          ρ ^ (∑ i : Fin K, hitCount
                            (edgeNewMemory F S sL.1 choice i) z')| *
                      ‖edgeMultiplier F S (decide (step % 2 = 0)) raw
                        sL.1.2.1 (edgeTargetLists F S sL.1 choice) sL.1.1 z'‖ *
                      (c * W (edgeBirths F S step sL.1 choice) *
                        v ^ memSize (z', edgeTargetLists F S sL.1 choice,
                          edgeNewMemory F S sL.1 choice)) := by
                    exact mul_le_mul_of_nonneg_left hfun (by positivity)
                  _ = _ := by ring
              · have hz := hzero choice z' hAdm hcut
                have hrow : ¬(edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
                    EdgeAdmissible F S w sL.1 choice z' ∧
                      memSize (z', edgeTargetLists F S sL.1 choice,
                        edgeNewMemory F S sL.1 choice) ≤ B) := by
                  rintro ⟨hs, hp, hA, hc'⟩
                  exact hcut hc'
                simp [hset.1, hset.2, hAdm, hcut, hz]
            · have hcond : ¬(edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
                  EdgeAdmissible F S w sL.1 choice z') := by
                rintro ⟨hs, hp, hA⟩
                exact hAdm hA
              have hrow : ¬(edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
                  EdgeAdmissible F S w sL.1 choice z' ∧
                    memSize (z', edgeTargetLists F S sL.1 choice,
                      edgeNewMemory F S sL.1 choice) ≤ B) := by
                rintro ⟨hs, hp, hA, hc'⟩
                exact hAdm hA
              simp [hcond, hrow]
          · have hcond : ¬(edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
                EdgeAdmissible F S w sL.1 choice z') := by
              rintro ⟨hs, hp, hA⟩
              exact hset ⟨hs, hp⟩
            have hrow : ¬(edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
                EdgeAdmissible F S w sL.1 choice z' ∧
                  memSize (z', edgeTargetLists F S sL.1 choice,
                    edgeNewMemory F S sL.1 choice) ≤ B) := by
              rintro ⟨hs, hp, hA, hc'⟩
              exact hset ⟨hs, hp⟩
            simp [hcond, hrow]

private def pd5_edgePositiveTotal {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (step B : ℕ) (Z : Finset (ℤ × ℤ)) (W : BirthLog K → ℝ)
    (v : ℝ) (s : MemPoint S.x K) : ℝ :=
  ∑ choice : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
    ∑ z' ∈ Z,
      let t : MemPoint S.x K :=
        (z', edgeTargetLists F S s choice, edgeNewMemory F S s choice)
      if EdgeAdmissible F S w s choice z' ∧ memSize t ≤ B then
        |ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
          (∏ i : Fin K, pd5_edgeChoiceMass F S s choice i) *
            ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s choice i) z')| *
          (‖edgeMultiplier F S (decide (step % 2 = 0)) true s.2.1
              (edgeTargetLists F S s choice) s.1 z'‖ +
            ‖edgeMultiplier F S (decide (step % 2 = 0)) false s.2.1
              (edgeTargetLists F S s choice) s.1 z'‖) *
          W (edgeBirths F S step s choice) * v ^ memSize t
      else 0

private theorem pd5_activeAverage_memSize_pow {K : ℕ}
    (S : PDScale) (v : ℝ) (s : MemPoint S.x K) :
    pd5_activeAverage S (fun t => v ^ memSize t) s = v ^ memSize s := by
  classical
  have hsize (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      memSize (s.1, permuteLists σ s.2.1, s.2.2) = memSize s := by
    simp [memSize]
  have hn : 0 < permCount S.x K := by
    unfold permCount
    exact Fintype.card_pos_iff.mpr ⟨1⟩
  unfold pd5_activeAverage
  simp_rw [hsize]
  simp [permCount, hn.ne']

private theorem pd5_logEdgePiece_le_edgePositiveTotal {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step B : ℕ)
    (raw : Bool) (St Pr : Finset (Fin K))
    (g : LogPoint S.x K → ℂ) (sL : LogPoint S.x K)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite)
    (W : BirthLog K → ℝ) (c v : ℝ)
    (hc : 0 ≤ c) (hv : 0 ≤ v) (hW : ∀ L, 0 ≤ W L)
    (hBound : ∀ (choice : (i : Fin K) → EdgeChoice S.x F.a (sL.1.2.2 i) i)
        (z' : ℤ × ℤ), EdgeAdmissible F S w sL.1 choice z' →
        memSize (z', edgeTargetLists F S sL.1 choice,
          edgeNewMemory F S sL.1 choice) ≤ B →
        ‖g ((z', edgeTargetLists F S sL.1 choice,
              edgeNewMemory F S sL.1 choice),
            sL.2 ++ edgeBirths F S step sL.1 choice)‖ ≤
          c * W (edgeBirths F S step sL.1 choice) *
            v ^ memSize (z', edgeTargetLists F S sL.1 choice,
              edgeNewMemory F S sL.1 choice))
    (hzero : ∀ (choice : (i : Fin K) → EdgeChoice S.x F.a (sL.1.2.2 i) i)
      (z' : ℤ × ℤ), EdgeAdmissible F S w sL.1 choice z' →
        ¬ memSize (z', edgeTargetLists F S sL.1 choice,
          edgeNewMemory F S sL.1 choice) ≤ B →
        g ((z', edgeTargetLists F S sL.1 choice,
              edgeNewMemory F S sL.1 choice),
            sL.2 ++ edgeBirths F S step sL.1 choice) = 0) :
    ‖logEdgePiece F S ρ w step raw St Pr g sL‖ ≤
      c * pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v sL.1 := by
  classical
  have hpiece := pd5_logEdgePiece_norm_le_absChoice F S ρ w step B raw St Pr
    g sL hbox W c v hc hv hW hBound hzero
  unfold pd5_edgePositiveTotal
  calc
    _ ≤ ∑ choice : (i : Fin K) → EdgeChoice S.x F.a (sL.1.2.2 i) i,
        ∑ z' ∈ hbox.toFinset,
          if edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
              EdgeAdmissible F S w sL.1 choice z' ∧
                memSize (z', edgeTargetLists F S sL.1 choice,
                  edgeNewMemory F S sL.1 choice) ≤ B then
            |ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1) *
              (∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i) *
                ρ ^ (∑ i : Fin K, hitCount
                  (edgeNewMemory F S sL.1 choice i) z')| *
              ‖edgeMultiplier F S (decide (step % 2 = 0)) raw
                sL.1.2.1 (edgeTargetLists F S sL.1 choice) sL.1.1 z'‖ *
              c * W (edgeBirths F S step sL.1 choice) *
                v ^ memSize (z', edgeTargetLists F S sL.1 choice,
                  edgeNewMemory F S sL.1 choice)
          else 0 := hpiece
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro choice hchoice
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z' hz'
      by_cases hPiece : edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
          EdgeAdmissible F S w sL.1 choice z' ∧
            memSize (z', edgeTargetLists F S sL.1 choice,
              edgeNewMemory F S sL.1 choice) ≤ B
      · rcases hPiece with ⟨hs, hp, hAdm, hcut⟩
        have hmult :
            ‖edgeMultiplier F S (decide (step % 2 = 0)) raw sL.1.2.1
                (edgeTargetLists F S sL.1 choice) sL.1.1 z'‖ ≤
              ‖edgeMultiplier F S (decide (step % 2 = 0)) true sL.1.2.1
                  (edgeTargetLists F S sL.1 choice) sL.1.1 z'‖ +
                ‖edgeMultiplier F S (decide (step % 2 = 0)) false sL.1.2.1
                  (edgeTargetLists F S sL.1 choice) sL.1.1 z'‖ := by
          cases raw <;> simp
        have hnonneg : 0 ≤ c * W (edgeBirths F S step sL.1 choice) *
            v ^ memSize (z', edgeTargetLists F S sL.1 choice,
              edgeNewMemory F S sL.1 choice) :=
          mul_nonneg (mul_nonneg hc (hW _)) (pow_nonneg hv _)
        have hcoeff : 0 ≤ |ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1) *
            (∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i) *
              ρ ^ (∑ i : Fin K, hitCount
                (edgeNewMemory F S sL.1 choice i) z')| := abs_nonneg _
        let ca := ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1)
        let cb := ∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i
        let cd := ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S sL.1 choice i) z')
        have hcoeffEq : |(ca * cb) * cd| = |(ca * cd) * cb| := by
          congr 1
          ring
        have hterm : edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
            EdgeAdmissible F S w sL.1 choice z' := ⟨hs, hp, hAdm⟩
        have hrow : edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
            EdgeAdmissible F S w sL.1 choice z' ∧
              memSize (z', edgeTargetLists F S sL.1 choice,
                edgeNewMemory F S sL.1 choice) ≤ B := ⟨hs, hp, hAdm, hcut⟩
        have hrowCut : EdgeAdmissible F S w sL.1 choice z' ∧
            memSize (z', edgeTargetLists F S sL.1 choice,
              edgeNewMemory F S sL.1 choice) ≤ B := ⟨hAdm, hcut⟩
        simp only [if_pos hterm, if_pos hrow, if_pos hrowCut]
        calc
          _ = (|ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1) *
                  (∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i) *
                    ρ ^ (∑ i : Fin K, hitCount
                      (edgeNewMemory F S sL.1 choice i) z')| *
                ‖edgeMultiplier F S (decide (step % 2 = 0)) raw
                  sL.1.2.1 (edgeTargetLists F S sL.1 choice) sL.1.1 z'‖) *
              (c * W (edgeBirths F S step sL.1 choice) *
                v ^ memSize (z', edgeTargetLists F S sL.1 choice,
                  edgeNewMemory F S sL.1 choice)) := by ring
          _ ≤ |ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1) *
                (∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i) *
                  ρ ^ (∑ i : Fin K, hitCount
                    (edgeNewMemory F S sL.1 choice i) z')| *
              (‖edgeMultiplier F S (decide (step % 2 = 0)) true
                  sL.1.2.1 (edgeTargetLists F S sL.1 choice) sL.1.1 z'‖ +
                ‖edgeMultiplier F S (decide (step % 2 = 0)) false
                  sL.1.2.1 (edgeTargetLists F S sL.1 choice) sL.1.1 z'‖) *
              (c * W (edgeBirths F S step sL.1 choice) *
                v ^ memSize (z', edgeTargetLists F S sL.1 choice,
                  edgeNewMemory F S sL.1 choice)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hmult hcoeff) hnonneg
          _ = _ := by rw [hcoeffEq]; ring
      · by_cases hRow : EdgeAdmissible F S w sL.1 choice z' ∧
            memSize (z', edgeTargetLists F S sL.1 choice,
              edgeNewMemory F S sL.1 choice) ≤ B
        · have hcoef0 : 0 ≤ |ρ ^ (∑ i : Fin K, hitCount (sL.1.2.2 i) sL.1.1) *
              (∏ i : Fin K, pd5_edgeChoiceMass F S sL.1 choice i) *
                ρ ^ (∑ i : Fin K, hitCount
                  (edgeNewMemory F S sL.1 choice i) z')| := abs_nonneg _
          have hmult0 : 0 ≤ ‖edgeMultiplier F S (decide (step % 2 = 0)) true
              sL.1.2.1 (edgeTargetLists F S sL.1 choice) sL.1.1 z'‖ +
              ‖edgeMultiplier F S (decide (step % 2 = 0)) false
                sL.1.2.1 (edgeTargetLists F S sL.1 choice) sL.1.1 z'‖ := by positivity
          simp only [if_neg hPiece, if_pos hRow]
          have hW' : 0 ≤ W (edgeBirths F S step sL.1 choice) := hW _
          have hv' : 0 ≤ v ^ memSize
              (z', edgeTargetLists F S sL.1 choice,
                edgeNewMemory F S sL.1 choice) := pow_nonneg hv _
          positivity
        · simp [hPiece, hRow]

private theorem pd5_logEdge_norm_le_positiveAverage {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step B : ℕ)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite)
    (W : BirthLog K → ℝ) (f : LogPoint S.x K → ℂ)
    (c v : ℝ) (sL : LogPoint S.x K)
    (hState : pd5_stateRegion F S w B sL.1)
    (hc : 0 ≤ c) (hv : 0 ≤ v) (hW : ∀ L, 0 ≤ W L)
    (hBound : ∀ (r : MemPoint S.x K), pd5_stateRegion F S w B r →
        ∀ (choice : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i)
          (z' : ℤ × ℤ), EdgeAdmissible F S w r choice z' →
          memSize (z', edgeTargetLists F S r choice,
            edgeNewMemory F S r choice) ≤ B →
          ∀ τ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ‖logTrunc (some B) f
              ((z', permuteLists τ (edgeTargetLists F S r choice),
                  edgeNewMemory F S r choice),
                sL.2 ++ edgeBirths F S step r choice)‖ ≤
              c * W (edgeBirths F S step r choice) *
                v ^ memSize (z', edgeTargetLists F S r choice,
                  edgeNewMemory F S r choice)) :
    ‖logEdge F S ρ w EdgeKind.full step (logTrunc (some B) f) sL‖ ≤
      2 * (Fintype.card (Finset (Fin K)) : ℝ) ^ 2 * c *
        pd5_activeAverage S
          (fun r => pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v r) sL.1 := by
  classical
  let g : LogPoint S.x K → ℂ := logSym F S (logTrunc (some B) f)
  let edgeInner : LogPoint S.x K → ℂ := fun τL =>
    ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      (logEdgePiece F S ρ w step true St Pr g τL -
        logEdgePiece F S ρ w step false St Pr g τL)
  let nsets : ℝ := (Fintype.card (Finset (Fin K)) : ℝ) ^ 2
  have hInner (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      ‖edgeInner ((sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2), sL.2)‖ ≤
        2 * nsets * c *
          pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v
            (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) := by
    let r : MemPoint S.x K :=
      (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2)
    let rL : LogPoint S.x K := (r, sL.2)
    have hRState : pd5_stateRegion F S w B r := by
      simpa [r] using pd5_stateRegion_permute F S w B sL.1 σ hState
    have hgBound : ∀ (choice : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i)
        (z' : ℤ × ℤ), EdgeAdmissible F S w r choice z' →
        memSize (z', edgeTargetLists F S r choice,
          edgeNewMemory F S r choice) ≤ B →
        ‖g ((z', edgeTargetLists F S r choice,
              edgeNewMemory F S r choice),
            rL.2 ++ edgeBirths F S step r choice)‖ ≤
          c * W (edgeBirths F S step r choice) *
            v ^ memSize (z', edgeTargetLists F S r choice,
              edgeNewMemory F S r choice) := by
      intro choice z' hAdm hcut
      have hA : 0 ≤ c * W (edgeBirths F S step r choice) *
          v ^ memSize (z', edgeTargetLists F S r choice,
            edgeNewMemory F S r choice) :=
        mul_nonneg (mul_nonneg hc (hW _)) (pow_nonneg hv _)
      exact pd5_logSym_norm_le_uniform F S (logTrunc (some B) f)
        ((z', edgeTargetLists F S r choice, edgeNewMemory F S r choice),
          rL.2 ++ edgeBirths F S step r choice)
        (c * W (edgeBirths F S step r choice) *
          v ^ memSize (z', edgeTargetLists F S r choice,
            edgeNewMemory F S r choice)) hA
        (by
          intro τ
          have hcut' : memSize (z', permuteLists τ (edgeTargetLists F S r choice),
              edgeNewMemory F S r choice) ≤ B := by
            simpa [memSize] using hcut
          simpa [rL] using hBound r hRState choice z' hAdm hcut τ)
    have hgZero : ∀ (choice : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i)
        (z' : ℤ × ℤ), EdgeAdmissible F S w r choice z' →
        ¬ memSize (z', edgeTargetLists F S r choice,
          edgeNewMemory F S r choice) ≤ B →
        g ((z', edgeTargetLists F S r choice, edgeNewMemory F S r choice),
          rL.2 ++ edgeBirths F S step r choice) = 0 := by
      intro choice z' hAdm hcut
      have hcutPerm : ∀ τ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ¬ memSize (z', permuteLists τ (edgeTargetLists F S r choice),
            edgeNewMemory F S r choice) ≤ B := by
        intro τ
        simpa [memSize] using hcut
      have hsum :
          (∑ τ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            logTrunc (some B) f
              ((z', permuteLists τ (edgeTargetLists F S r choice),
                edgeNewMemory F S r choice),
                rL.2 ++ edgeBirths F S step r choice)) = 0 := by
        apply Finset.sum_eq_zero
        intro τ hτ
        simp [logTrunc, hcutPerm τ]
      unfold g logSym
      simp [hsum]
    have hRaw (St Pr : Finset (Fin K)) :
        ‖logEdgePiece F S ρ w step true St Pr g rL‖ ≤
          c * pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v r :=
      pd5_logEdgePiece_le_edgePositiveTotal F S ρ w step B true St Pr
        g rL hbox W c v hc hv hW hgBound hgZero
    have hCmp (St Pr : Finset (Fin K)) :
        ‖logEdgePiece F S ρ w step false St Pr g rL‖ ≤
          c * pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v r :=
      pd5_logEdgePiece_le_edgePositiveTotal F S ρ w step B false St Pr
        g rL hbox W c v hc hv hW hgBound hgZero
    have hSumBound :
        (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          (‖logEdgePiece F S ρ w step true St Pr g rL‖ +
            ‖logEdgePiece F S ρ w step false St Pr g rL‖)) ≤
          2 * nsets * c *
            pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v r := by
      calc
        _ ≤ ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
            (c * pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v r +
              c * pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v r) := by
              apply Finset.sum_le_sum
              intro St hSt
              apply Finset.sum_le_sum
              intro Pr hPr
              exact add_le_add (hRaw St Pr) (hCmp St Pr)
        _ = _ := by
              simp [nsets]
              ring
    change ‖∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      (logEdgePiece F S ρ w step true St Pr g rL -
        logEdgePiece F S ρ w step false St Pr g rL)‖ ≤ _
    calc
      _ ≤ ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          (‖logEdgePiece F S ρ w step true St Pr g rL‖ +
            ‖logEdgePiece F S ρ w step false St Pr g rL‖) := by
        calc
          _ ≤ ∑ St : Finset (Fin K),
              ‖∑ Pr : Finset (Fin K),
                (logEdgePiece F S ρ w step true St Pr g rL -
                  logEdgePiece F S ρ w step false St Pr g rL)‖ := norm_sum_le _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro St hSt
            calc
              _ ≤ ∑ Pr : Finset (Fin K),
                  ‖logEdgePiece F S ρ w step true St Pr g rL -
                    logEdgePiece F S ρ w step false St Pr g rL‖ := norm_sum_le _ _
              _ ≤ _ := by
                apply Finset.sum_le_sum
                intro Pr hPr
                exact norm_sub_le _ _
      _ ≤ 2 * nsets * c *
          pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v r := hSumBound
  unfold logEdge
  simp only [EdgeKind.full]
  change ‖logSym F S edgeInner sL‖ ≤
    2 * nsets * c * pd5_activeAverage S
      (fun r => pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v r) sL.1
  calc
    _ ≤ (permCount S.x K : ℝ)⁻¹ *
        ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ‖edgeInner ((sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2), sL.2)‖ :=
      pd5_logSym_norm_le_average F S edgeInner sL
    _ ≤ (permCount S.x K : ℝ)⁻¹ *
        ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          2 * nsets * c * pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v
            (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
      apply Finset.sum_le_sum
      intro σ hσ
      exact hInner σ
    _ = _ := by
      unfold pd5_activeAverage
      have hsum :
          (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            2 * nsets * c * pd5_edgePositiveTotal F S ρ w step B
              hbox.toFinset W v (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2)) =
            (2 * nsets * c) *
              ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                pd5_edgePositiveTotal F S ρ w step B hbox.toFinset W v
                  (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) := by
        rw [← Finset.mul_sum]
      rw [hsum]
      ring

private theorem pd5_edgeSet_sum_collapse {K : ℕ}
    (st pr : Finset (Fin K)) (P : Prop) [Decidable P] (f : ℝ) :
    (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      if st = St ∧ pr = Pr ∧ P then f else 0) = if P then f else 0 := by
  classical
  by_cases hP : P
  · simp only [if_pos hP]
    have hinner (St : Finset (Fin K)) :
        (∑ Pr : Finset (Fin K), if st = St ∧ pr = Pr ∧ P then f else 0) =
          if st = St then f else 0 := by
      by_cases hSt : st = St
      · subst St
        simp [hP]
      · simp [hSt, hP]
    calc
      _ = ∑ St : Finset (Fin K), if st = St then f else 0 := by
        apply Finset.sum_congr rfl
        intro St hSt
        exact hinner St
      _ = f := by simp
  · simp [hP]

private theorem pd5_card_filter_ge_split {α : Type*} [DecidableEq α]
    (T : Finset α) (layer : α → ℕ) (stage : ℕ) :
    (T.filter fun a => stage ≤ layer a).card =
      (T.filter fun a => layer a = stage).card +
        (T.filter fun a => layer a = stage + 1).card +
          (T.filter fun a => stage + 2 ≤ layer a).card := by
  classical
  calc
    (T.filter fun a => stage ≤ layer a).card =
        ∑ a ∈ T, if stage ≤ layer a then 1 else 0 := by simp
    _ = ∑ a ∈ T,
          ((if layer a = stage then 1 else 0) +
            (if layer a = stage + 1 then 1 else 0) +
              (if stage + 2 ≤ layer a then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h0 : layer a = stage
        · simp [h0]
        · by_cases h1 : layer a = stage + 1
          · have hle : stage ≤ layer a := by omega
            simp [h0, h1, hle]
          · by_cases h2 : stage + 2 ≤ layer a
            · have hle : stage ≤ layer a := by omega
              simp [h0, h1, h2, hle]
            · have hnot : ¬ stage ≤ layer a := by omega
              simp [h0, h1, h2, hnot]
    _ = (T.filter fun a => layer a = stage).card +
          (T.filter fun a => layer a = stage + 1).card +
            (T.filter fun a => stage + 2 ≤ layer a).card := by
        simp_rw [Finset.card_filter]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

private noncomputable def pd5_futureRank {K : ℕ} (S : PDScale) (B : ℕ)
    (C : Finset (Finset (BirthAddress K))) (stage : ℕ) : ℕ :=
  ((pd5_allNonpivots S B C).filter fun a => stage ≤ pd5_birthLayer a).card

private noncomputable def pd5_edgeRowFactor {K : ℕ}
    (F : PDFix K) (S : PDScale) (Cedge : ℝ) : ℝ :=
  2 * (Fintype.card (Finset (Fin K)) : ℝ) ^ 2 * Cedge *
    ((memoryCutoff S + 1 : ℕ) : ℝ) ^ K * Real.rpow S.L (3 * F.A₀)

private noncomputable def pd5_fixedAtom {K : ℕ}
    (S : PDScale) (cmax aAtom : ℝ) : ℝ :=
  cmax * (aAtom * Real.exp (-Real.rpow S.L (1 / 10 : ℝ)))

private theorem pd5_futureRank_split {K : ℕ} (S : PDScale) (B : ℕ)
    {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems (birthAddresses S.x K B)) (j : ℕ) :
    pd5_futureRank S B C (2 * j + 1) =
      (pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2
        (pd5_isGhostAt j)).card +
        (pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2
          (pd5_isEdgeAt j)).card +
          pd5_futureRank S B C (2 * j + 3) := by
  classical
  let R := pd5_allNonpivots S B C
  have hsplit := pd5_card_filter_ge_split R pd5_birthLayer (2 * j + 1)
  have hGhost : R.filter (fun a => pd5_birthLayer a = 2 * j + 1) =
      pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2 (pd5_isGhostAt j) := by
    calc
      R.filter (fun a => pd5_birthLayer a = 2 * j + 1) =
          R.filter (pd5_isGhostAt j) := by
            ext a
            simp [pd5_birthLayer_eq_ghost_iff]
      _ = _ := by
        change (pd5_allNonpivots S B C).filter (pd5_isGhostAt j) = _
        rw [← pd5_layerNonpivots_eq_all_filter S B hC (pd5_isGhostAt j)]
  have hEdge : R.filter (fun a => pd5_birthLayer a = 2 * j + 2) =
      pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2 (pd5_isEdgeAt j) := by
    calc
      R.filter (fun a => pd5_birthLayer a = 2 * j + 2) =
          R.filter (pd5_isEdgeAt j) := by
            ext a
            simp [pd5_birthLayer_eq_edge_iff]
      _ = _ := by
        change (pd5_allNonpivots S B C).filter (pd5_isEdgeAt j) = _
        rw [← pd5_layerNonpivots_eq_all_filter S B hC (pd5_isEdgeAt j)]
  dsimp [pd5_futureRank] at *
  rw [hGhost, hEdge] at hsplit
  simpa [R] using hsplit

private theorem pd5_futureRank_final {K : ℕ} (S : PDScale) (B : ℕ)
    {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems (birthAddresses S.x K B)) :
    pd5_futureRank S B C (2 * S.N + 1) =
      (pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2
        (pd5_isGhostAt S.N)).card := by
  classical
  let R := pd5_allNonpivots S B C
  have hLayer : ∀ a ∈ R, pd5_birthLayer a < 2 * S.N + 2 := by
    intro a ha
    rcases Finset.mem_biUnion.mp ha with ⟨D, hD, haD⟩
    have haD' : a ∈ D := pd5_blockNonpivots_subset S B D haD
    have haA : a ∈ birthAddresses S.x K B :=
      pd5_constraint_support_subset hC (Finset.mem_biUnion.mpr ⟨D, hD, haD'⟩)
    cases a with
    | initial i k => simp [pd5_birthLayer]
    | ghost j i k =>
        have hj : j ≤ S.N := by
          have hparts : j ≤ pathLength S.x ∧ k < B := by
            simpa [birthAddresses] using haA
          simpa [PDScale.N] using hparts.1
        simp [pd5_birthLayer]
        omega
    | edge j i =>
        have hj : j < S.N := by
          have hle : j < pathLength S.x := by simpa [birthAddresses] using haA
          simpa [PDScale.N] using hle
        simp [pd5_birthLayer]
        omega
  have hfilter : R.filter (fun a => 2 * S.N + 1 ≤ pd5_birthLayer a) =
      R.filter (pd5_isGhostAt S.N) := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, hge⟩
      have heq : pd5_birthLayer a = 2 * S.N + 1 := by
        have hlt := hLayer a ha
        omega
      exact ⟨ha, (pd5_birthLayer_eq_ghost_iff S.N a).mp heq⟩
    · rintro ⟨ha, hghost⟩
      have heq := (pd5_birthLayer_eq_ghost_iff S.N a).mpr hghost
      exact ⟨ha, by omega⟩
  rw [pd5_futureRank, hfilter,
    ← pd5_layerNonpivots_eq_all_filter S B hC (pd5_isGhostAt S.N)]

private theorem pd5_good_prefix_gives_stage_gate {K : ℕ}
    (S : PDScale) (B : ℕ)
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) (hA : A ⊆ birthAddresses S.x K B)
    (U R : Finset (BirthAddress K)) (hRU : R ⊆ U)
    (hUsupport : U ⊆ C.biUnion id) (stage : ℕ)
    (hULayer : ∀ a ∈ U, pd5_birthLayer a = stage)
    (hStrict : ∀ a ∈ R,
      pd5_birthIndex S B (pd5_addressPivot S B (Finset.mem_filter.mp hC).2 a) <
        pd5_birthIndex S B a)
    (pastLog newLog : BirthLog K)
    (hNewNodup : (newLog.map Prod.fst).Nodup)
    (hPrefixNodup : ∀ (a : BirthAddress K),
      (((pastLog ++ newLog).filter fun e =>
        pd5_birthIndex S B e.1 < pd5_birthIndex S B a).map Prod.fst).Nodup)
    (hPastLayer : ∀ e ∈ pastLog, pd5_birthLayer e.1 < stage)
    (hGood : pd5_prefixConstraintOK C (stage + 1) (pastLog ++ newLog)) :
    pd5_prescribedWeight S B U R
      (pd5_addressPick S B (Finset.mem_filter.mp hC).2) pastLog newLog = 1 := by
  classical
  let hSys : IsConstraintSystem A C := (Finset.mem_filter.mp hC).2
  let lbl : Finset (BirthAddress K) → ℕ := fun D =>
    if hD : D ∈ C then Classical.choose (hGood D hD) else 0
  have hlabel (D : Finset (BirthAddress K)) (hD : D ∈ C) :
      ∀ a ∈ D, pd5_birthLayer a < stage + 1 →
        (a, lbl D) ∈ pastLog ++ newLog := by
    intro a ha hstage
    dsimp [lbl]
    rw [dif_pos hD]
    exact Classical.choose_spec (hGood D hD) a ha hstage
  let futureLog : BirthLog K := C.toList.flatMap fun D =>
    (D.filter fun a => stage + 1 ≤ pd5_birthLayer a).toList.map
      fun a => (a, lbl D)
  have hfuturePair (D : Finset (BirthAddress K)) (hD : D ∈ C)
      (a : BirthAddress K) (ha : a ∈ D) (hstage : stage + 1 ≤ pd5_birthLayer a) :
      (a, lbl D) ∈ futureLog := by
    apply List.mem_flatMap.mpr
    refine ⟨D, Finset.mem_toList.mpr hD, ?_⟩
    apply List.mem_map.mpr
    refine ⟨a, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨ha, hstage⟩), rfl⟩
  have hfutureLayer : ∀ e ∈ futureLog, stage < pd5_birthLayer e.1 := by
    intro e he
    rcases List.mem_flatMap.mp he with ⟨D, hD, he⟩
    rcases List.mem_map.mp he with ⟨a, ha, hEq⟩
    have hfilter := Finset.mem_toList.mp ha
    have hstage := (Finset.mem_filter.mp hfilter).2
    have hEq' : e.1 = a := by simpa using (congrArg Prod.fst hEq).symm
    rw [hEq']
    omega
  let fullLog := pastLog ++ newLog ++ futureLog
  have hblocks : ∀ D ∈ C, ∃ p, ∀ a ∈ D, (a, p) ∈ fullLog := by
    intro D hD
    refine ⟨lbl D, ?_⟩
    intro a ha
    by_cases hf : stage + 1 ≤ pd5_birthLayer a
    · have hmem := hfuturePair D hD a ha hf
      exact List.mem_append_right _ hmem
    · have hmem := hlabel D hD a ha (by omega)
      exact List.mem_append_left _ hmem
  have hW : constraintWeight C fullLog = 1 := by
    unfold constraintWeight
    rw [Finset.prod_eq_one]
    intro D hD
    simp [hblocks D hD]
  exact pd5_stage_gate_of_future S B hC hA U R hRU hUsupport stage hULayer hStrict
    fullLog pastLog newLog futureLog rfl hW hNewNodup hPrefixNodup hPastLayer
    hfutureLayer

private theorem pd5_logHistoryFn_zero_of_bad_prefix {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (B : ℕ)
    (C : Finset (Finset (BirthAddress K))) (k : ℕ) (hk : k ≤ S.N)
    (σL : LogPoint S.x K)
    (hbad : ¬ pd5_prefixConstraintOK C (2 * (S.N - k) + 1) σL.2) :
    logHistoryFn F S ρ w (some B) none (constraintWeight C) k σL = 0 := by
  revert σL
  induction k with
  | zero =>
      intro σL hbad
      have hbad0 :
          ¬ pd5_prefixConstraintOK C (2 * S.N + 1) σL.2 := by
        simpa using hbad
      have hGhostAppend : ∀ L l p,
          (¬ pd5_prefixConstraintOK C (2 * S.N + 1) L) →
            ¬ pd5_prefixConstraintOK C (2 * S.N + 1)
              (L ++ pd5_ghostBirthLog S.N l p) := by
        intro L l p hL
        apply pd5_prefixConstraintOK_bad_extend C (2 * S.N + 1)
          L (pd5_ghostBirthLog S.N l p) hL
        intro e he
        rw [pd5_ghostBirthLog_layer S.N l p e he]
      have hBoundary : ∀ τL : LogPoint S.x K,
          (¬ pd5_prefixConstraintOK C (2 * S.N + 1) τL.2) →
            logBoundaryOut (constraintWeight C) τL = 0 := by
        intro τL hτ
        have hw0 := pd5_constraintWeight_zero_of_bad_prefix C (2 * S.N + 1)
          τL.2 ([] : BirthLog K) hτ (by intro e he; cases he)
        have hw : constraintWeight C τL.2 = 0 := by simpa using hw0
        simp [logBoundaryOut, hw]
      have hBoundaryTrunc : ∀ τL : LogPoint S.x K,
          (¬ pd5_prefixConstraintOK C (2 * S.N + 1) τL.2) →
            logTrunc (some B) (logBoundaryOut (constraintWeight C)) τL = 0 := by
        intro τL hτ
        by_cases hsize : memSize τL.1 ≤ B
        · simpa [logTrunc, hsize] using hBoundary τL hτ
        · simp [logTrunc, hsize]
      have hghost := pd5_logGhost_zero_of_badPredicate F S ρ S.N
        (fun L => ¬ pd5_prefixConstraintOK C (2 * S.N + 1) L)
        hGhostAppend (logTrunc (some B) (logBoundaryOut (constraintWeight C)))
        hBoundaryTrunc σL hbad0
      have hghost' : logGhost F S ρ (pathLength S.x)
          (logTrunc (some B) (logBoundaryOut (constraintWeight C))) σL = 0 := by
        simpa [PDScale.N] using hghost
      simp [logHistoryFn, logPathRestrict, logTrunc, hghost']
  | succ k ih =>
      intro σL hbad
      have hk' : k + 1 ≤ S.N := by simpa using hk
      let j := S.N - (k + 1)
      have hjStage : 2 * (S.N - (k + 1)) + 1 = 2 * j + 1 := by rfl
      have hNextStage : 2 * (S.N - k) + 1 = 2 * j + 3 := by
        dsimp [j]
        omega
      have hbadCurrent :
          ¬ pd5_prefixConstraintOK C (2 * j + 1) σL.2 := by
        simpa [j] using hbad
      have hGhostAppend : ∀ L l p,
          (¬ pd5_prefixConstraintOK C (2 * j + 1) L) →
            ¬ pd5_prefixConstraintOK C (2 * j + 1)
              (L ++ pd5_ghostBirthLog j l p) := by
        intro L l p hL
        apply pd5_prefixConstraintOK_bad_extend C (2 * j + 1)
          L (pd5_ghostBirthLog j l p) hL
        intro e he
        rw [pd5_ghostBirthLog_layer j l p e he]
      have hEdgeAppend : ∀ L s c,
          (¬ pd5_prefixConstraintOK C (2 * j + 1) L) →
            ¬ pd5_prefixConstraintOK C (2 * j + 1)
              (L ++ edgeBirths F S j s c) := by
        intro L s c hL
        apply pd5_prefixConstraintOK_bad_extend C (2 * j + 1)
          L (edgeBirths F S j s c) hL
        intro e he
        have hfst : e.1 ∈ (edgeBirths F S j s c).map Prod.fst :=
          List.mem_map.mpr ⟨e, he, rfl⟩
        rw [pd5_edgeBirths_layer F S j s c hfst]
        omega
      have hEdgeZero : ∀ τL : LogPoint S.x K,
          (¬ pd5_prefixConstraintOK C (2 * j + 1) τL.2) →
            logEdge F S ρ w EdgeKind.full j
              (logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none (constraintWeight C) k)) τL = 0 := by
        intro τL hτ
        have hfn : ∀ υL : LogPoint S.x K,
            (¬ pd5_prefixConstraintOK C (2 * j + 1) υL.2) →
              logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none (constraintWeight C) k) υL = 0 := by
          intro υL hυ
          by_cases hsize : memSize υL.1 ≤ B
          · have hbadIH :
                ¬ pd5_prefixConstraintOK C (2 * (S.N - k) + 1) υL.2 := by
              intro hgood
              have hgood' := hgood
              rw [hNextStage] at hgood'
              exact hυ (pd5_prefixConstraintOK_mono (by omega) hgood')
            have hzero := ih (by omega : k ≤ S.N) υL hbadIH
            simp [logTrunc, hsize, hzero]
          · simp [logTrunc, hsize]
        exact pd5_logEdge_zero_of_badPredicate F S ρ w j
          (fun L => ¬ pd5_prefixConstraintOK C (2 * j + 1) L)
          hEdgeAppend
          (logTrunc (some B)
            (logHistoryFn F S ρ w (some B) none (constraintWeight C) k))
          hfn τL hτ
      have hGhostZero :
          logGhost F S ρ j
            (fun υL => logTrunc (some B)
              (logEdge F S ρ w EdgeKind.full j
                (logTrunc (some B)
                  (logHistoryFn F S ρ w (some B) none (constraintWeight C) k))) υL) σL = 0 := by
        exact pd5_logGhost_zero_of_badPredicate F S ρ j
          (fun L => ¬ pd5_prefixConstraintOK C (2 * j + 1) L)
          hGhostAppend
          (fun υL => logTrunc (some B)
            (logEdge F S ρ w EdgeKind.full j
              (logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none (constraintWeight C) k))) υL)
          (by
            intro υL hυ
            have hedge := hEdgeZero υL hυ
            simp [logTrunc, hedge])
          σL hbadCurrent
      have hzero :
          (logTrunc (some B) (logPathRestrict none j
            (logGhost F S ρ j (logTrunc (some B)
              (logEdge F S ρ w EdgeKind.full j (logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none (constraintWeight C) k)))))) σL) = 0 := by
        by_cases hsize : memSize σL.1 ≤ B
        · simpa [logTrunc, hsize, logPathRestrict, hGhostZero]
        · simp [logTrunc, hsize]
      simpa [logHistoryFn, j, PDScale.N] using hzero

private theorem pd5_logHistoryFn_base_bound {K : ℕ}
    (δ c₁ c₂ : ℝ) (F : PDFix K) (ρ : ℝ)
    (v Cghost Cedge cmax aAtom x₀ : ℝ)
    (hV : 1 < v) (hCghost : 0 < Cghost) (hCedge : 0 < Cedge)
    (hCmax : 1 ≤ cmax) (hAtom : 0 < aAtom) (hRows :
      PD5PositiveRows δ c₁ c₂ F ρ v Cghost Cedge cmax aAtom x₀)
    (S : PDScale) (hS : S.Valid K δ c₁ c₂) (hx : x₀ ≤ S.x)
    (w : ArchRoot) (hw : w.InRegion S)
    (C : Finset (Finset (BirthAddress K)))
    (hC : C ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)))
    (σL : LogPoint S.x K)
    (hState : pd5_stateRegion F S w (memoryCutoff S) σL.1)
    (hLog : pd5_logPrefixGood S.x (memoryCutoff S) S.N S.N σL.2)
    (hPrefix : pd5_prefixConstraintOK C (2 * S.N + 1) σL.2) :
    ‖logHistoryFn F S ρ w (some (memoryCutoff S)) none
      (constraintWeight C) 0 σL‖ ≤
      Cghost * (cmax * (aAtom * Real.exp
        (-Real.rpow S.L (1 / 10 : ℝ)))) ^
          (pd5_layerNonpivots S (memoryCutoff S)
            (Finset.mem_filter.mp hC).2 (pd5_isGhostAt S.N)).card *
        v ^ memSize σL.1 := by
  classical
  let B := memoryCutoff S
  let Δ := aAtom * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))
  let atom := cmax * Δ
  have hΔ : 0 ≤ Δ := by dsimp [Δ]; positivity
  have hatom : 0 ≤ atom := by dsimp [atom]; positivity
  have hv : 0 ≤ v := (lt_trans zero_lt_one hV).le
  have hRowsNow := hRows S hS hx w hw σL.1 hState
  rcases hRowsNow with ⟨hghostRows, _hedgeRows⟩
  let hSys : IsConstraintSystem (birthAddresses S.x K B) C :=
    (Finset.mem_filter.mp hC).2
  let U := pd5_layerAddresses C (pd5_isGhostAt S.N)
  let R := pd5_layerNonpivots S B hSys (pd5_isGhostAt S.N)
  let pick := pd5_addressPick S B hSys
  have hRU : R ⊆ U := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hUsupport : U ⊆ C.biUnion id := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hU : U ⊆ pd5_ghostAddresses K S.N B := by
    simpa [U, pd5_layerAddresses] using pd5_ghostLayer_subset S.x B S.N hC
  have hULayer : ∀ a ∈ U, pd5_birthLayer a = 2 * S.N + 1 := by
    intro a ha
    exact (pd5_birthLayer_eq_ghost_iff S.N a).mpr
      (Finset.mem_filter.mp ha).2
  have hA : birthAddresses S.x K B ⊆ birthAddresses S.x K B := fun _ ha => ha
  have hStrict : ∀ a ∈ R,
      pd5_birthIndex S B (pd5_addressPivot S B hSys a) < pd5_birthIndex S B a := by
    intro a ha
    exact pd5_layerNonpivot_strict S B hC hA (pd5_isGhostAt S.N) ha
  have hPastLayer : ∀ e ∈ σL.2, pd5_birthLayer e.1 < 2 * S.N + 1 :=
    pd5_prefixGood_layers_lt_ghost hLog
  let W : BirthLog K → ℝ := fun batch =>
    pd5_prescribedWeight S B U R pick σL.2 batch
  have hW : ∀ batch, 0 ≤ W batch := by
    intro batch
    exact (pd5_prescribedWeight_bounds S B U R pick σL.2 batch).1
  have hBound : ∀ (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length))
      (l : Fin K → ℕ)
      (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)),
      (∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1) →
      memSize (pd5_ghostOutput F S σL D l new S.N).1 ≤ B →
      ‖logTrunc (some B) (logBoundaryOut (constraintWeight C))
        (pd5_ghostOutput F S σL D l new S.N)‖ ≤
        W (pd5_ghostBirthLog S.N l (fun i k => (new i k : ℕ))) *
          v ^ memSize (pd5_ghostOutput F S σL D l new S.N).1 := by
    intro D l new hDel hCut
    let batch := pd5_ghostBirthLog S.N l (fun i k => (new i k : ℕ))
    let out := pd5_ghostOutput F S σL D l new S.N
    have hlBound : ∀ i, l i ≤ B := by
      intro i
      have hlen := pd5_ghost_length_le_memSize σL.1 D l
        (fun i k => (new i k : ℕ)) i
      have hsize : memSize
          (σL.1.1, σL.1.2.1, fun j =>
            removeIndices (σL.1.2.2 j) (D j) ++
              List.ofFn fun k => anchorAt (new j k) σL.1.1) ≤ B := by
        simpa [out, pd5_ghostOutput] using hCut
      exact hlen.trans hsize
    have hLogOut : pd5_logPrefixGood S.x B S.N (S.N + 1)
        (σL.2 ++ batch) := by
      exact pd5_logPrefixGood_append_ghostBatch hLog (by simp [PDScale.N])
        l hlBound (fun i k => (new i k : ℕ))
    have hNewNodup : (batch.map Prod.fst).Nodup := by
      dsimp [batch]
      rw [pd5_ghostBirthLog_map_fst]
      exact pd5_ghostAddressList_nodup S.N l
    have hPrefixNodup : ∀ a : BirthAddress K,
        (((σL.2 ++ batch).filter fun e =>
          pd5_birthIndex S B e.1 < pd5_birthIndex S B a).map Prod.fst).Nodup := by
      intro a
      let P : BirthAddress K → Prop := fun b =>
        pd5_birthIndex S B b < pd5_birthIndex S B a
      letI : DecidablePred P := fun b => Nat.decLt _ _
      letI : DecidablePred (fun e : BirthAddress K × ℕ => P e.1) :=
        fun e => Nat.decLt _ _
      exact pd5_filtered_projection_nodup (σL.2 ++ batch) P hLogOut.1
    have hAfterLayer :
        ∀ e ∈ σL.2 ++ batch,
          pd5_birthLayer e.1 < 2 * S.N + 2 := by
      intro e he
      rcases List.mem_append.mp he with hePast | heBatch
      · have hlt := hPastLayer e hePast
        omega
      · have hlayer := pd5_ghostBirthLog_layer S.N l
          (fun i k => (new i k : ℕ)) e heBatch
        omega
    let stageGate := W batch
    by_cases hgood : pd5_prefixConstraintOK C (2 * S.N + 2) (σL.2 ++ batch)
    · have hgate : stageGate = 1 := by
        dsimp [stageGate, W]
        exact pd5_good_prefix_gives_stage_gate S B hC hA U R hRU hUsupport
          (2 * S.N + 1) hULayer hStrict σL.2 batch hNewNodup hPrefixNodup
          hPastLayer hgood
      have hgateW : W batch = 1 := by simpa [stageGate] using hgate
      have hboundary :
          ‖logBoundaryOut (constraintWeight C) out‖ ≤ 1 := by
        exact pd5_logBoundaryOut_constraint_norm_le_one C out
      have hvPow : 1 ≤ v ^ memSize out.1 := one_le_pow₀ (le_of_lt hV)
      have hgate' :
          W (pd5_ghostBirthLog S.N l (fun i k => (new i k : ℕ))) = 1 := by
        simpa [batch] using hgateW
      have htruncEq :
          logTrunc (some B) (logBoundaryOut (constraintWeight C))
            (pd5_ghostOutput F S σL D l new S.N) =
          logBoundaryOut (constraintWeight C) out := by
        simp only [logTrunc, if_pos hCut]
        rfl
      calc
        ‖logTrunc (some B) (logBoundaryOut (constraintWeight C))
            (pd5_ghostOutput F S σL D l new S.N)‖ =
            ‖logBoundaryOut (constraintWeight C) out‖ :=
              congrArg norm htruncEq
        _ ≤ 1 := hboundary
        _ ≤ W (pd5_ghostBirthLog S.N l (fun i k => (new i k : ℕ))) *
            v ^ memSize (pd5_ghostOutput F S σL D l new S.N).1 := by
              rw [hgate']
              simpa using hvPow
    · have hweight0 : constraintWeight C (out.2) = 0 := by
        have hz := pd5_constraintWeight_zero_of_bad_prefix C (2 * S.N + 2)
          out.2 ([] : BirthLog K) hgood (by intro e he; cases he)
        simpa using hz
      have hboundary0 : logBoundaryOut (constraintWeight C) out = 0 := by
        simp [logBoundaryOut, hweight0]
      have hWpow : 0 ≤ W batch *
          v ^ memSize (pd5_ghostOutput F S σL D l new S.N).1 :=
        mul_nonneg (hW batch) (pow_nonneg hv _)
      have htrunc0 : logTrunc (some B)
          (logBoundaryOut (constraintWeight C))
          (pd5_ghostOutput F S σL D l new S.N) = 0 := by
        simp [logTrunc, hCut, hboundary0, out]
      rw [htrunc0]
      simpa [batch] using hWpow
  have hBound' : ∀ (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length))
      (l : Fin K → ℕ)
      (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)),
      (∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1) →
      memSize (pd5_ghostOutput F S σL D l new S.N).1 ≤ B →
      ‖logTrunc (some B) (logBoundaryOut (constraintWeight C))
        (pd5_ghostOutput F S σL D l new S.N)‖ ≤
        1 * W (pd5_ghostBirthLog S.N l (fun i k => (new i k : ℕ))) *
          v ^ memSize (pd5_ghostOutput F S σL D l new S.N).1 := by
    intro D l new hDel hCut
    simpa [one_mul] using hBound D l new hDel hCut
  have hGhostOp := pd5_logGhost_norm_le_absChoice F S ρ S.N B W
    (logBoundaryOut (constraintWeight C)) 1 v σL
    (by simpa [B] using (show memSize σL.1 ≤ memoryCutoff S from hState.2.1))
    (by norm_num) hv hW hBound'
  have hRow := hghostRows S.N (by simp [PDScale.N]) U R hRU hU pick σL.2
  have hRank := pd5_futureRank_final S B hC
  have hGateNorm :
      ‖logGhost F S ρ S.N (logTrunc (some B)
        (logBoundaryOut (constraintWeight C))) σL‖ ≤
        Cghost * atom ^ (pd5_layerNonpivots S B hSys
          (pd5_isGhostAt S.N)).card * v ^ memSize σL.1 := by
    calc
      _ ≤ 1 * pd5_ghostAbsChoice F S ρ S.N B W
          (fun s => v ^ memSize s) σL.1 := by simpa using hGhostOp
      _ ≤ 1 * (Cghost * atom ^ R.card * v ^ memSize σL.1) := by
        exact mul_le_mul_of_nonneg_left hRow (by norm_num)
      _ = Cghost * atom ^ R.card * v ^ memSize σL.1 := by ring
  have hH0 : logHistoryFn F S ρ w (some B) none (constraintWeight C) 0 σL =
      logGhost F S ρ (pathLength S.x)
        (logTrunc (some B) (logBoundaryOut (constraintWeight C))) σL := by
    simp [logHistoryFn, logPathRestrict, logTrunc, B, PDScale.N, hState.2.1]
  rw [hH0]
  have hRank' :
      pd5_futureRank S B C (2 * S.N + 1) =
        (pd5_layerNonpivots S B hSys (pd5_isGhostAt S.N)).card := by
    simpa [hSys] using hRank
  simpa [atom, Δ, hRank', PDScale.N] using hGateNorm

private theorem pd5_logHistoryFn_edge_step_bound {K : ℕ}
    (δ c₁ c₂ : ℝ) (F : PDFix K) (ρ : ℝ)
    (v Cghost Cedge cmax aAtom x₀ : ℝ)
    (hV : 1 < v) (hCghost : 0 < Cghost) (hCedge : 0 < Cedge)
    (hCmax : 1 ≤ cmax) (hAtom : 0 < aAtom)
    (hRows : PD5PositiveRows δ c₁ c₂ F ρ v Cghost Cedge cmax aAtom x₀)
    (S : PDScale) (hS : S.Valid K δ c₁ c₂) (hx : x₀ ≤ S.x)
    (w : ArchRoot) (hw : w.InRegion S)
    (C : Finset (Finset (BirthAddress K)))
    (hC : C ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)))
    (k : ℕ) (hk : k ≤ S.N) (j : ℕ) (hN : S.N - k = j + 1)
    (hStep : j < S.N)
    (hIH : ∀ τL : LogPoint S.x K,
      pd5_stateRegion F S w (memoryCutoff S) τL.1 →
      pd5_logPrefixGood S.x (memoryCutoff S) (S.N - k) (S.N - k) τL.2 →
      pd5_prefixConstraintOK C (2 * (S.N - k) + 1) τL.2 →
      ‖logHistoryFn F S ρ w (some (memoryCutoff S)) none
          (constraintWeight C) k τL‖ ≤
        Cghost ^ (k + 1) * (pd5_edgeRowFactor F S Cedge) ^ k *
          (pd5_fixedAtom (K := K) S cmax aAtom) ^
            pd5_futureRank S (memoryCutoff S) C (2 * (S.N - k) + 1) *
          v ^ memSize τL.1)
    (τL : LogPoint S.x K)
    (hState : pd5_stateRegion F S w (memoryCutoff S) τL.1)
    (hLog : pd5_logPrefixGood S.x (memoryCutoff S) j (j + 1) τL.2)
    (hPrefix : pd5_prefixConstraintOK C (2 * j + 2) τL.2) :
    ‖logTrunc (some (memoryCutoff S))
      (logEdge F S ρ w EdgeKind.full j
        (logTrunc (some (memoryCutoff S))
          (logHistoryFn F S ρ w (some (memoryCutoff S)) none
            (constraintWeight C) k))) τL‖ ≤
      (Cghost ^ (k + 1) * (pd5_edgeRowFactor F S Cedge) ^ k *
        (pd5_fixedAtom (K := K) S cmax aAtom) ^
          pd5_futureRank S (memoryCutoff S) C (2 * j + 3)) *
        pd5_edgeRowFactor F S Cedge *
          (pd5_fixedAtom (K := K) S cmax aAtom) ^
            (pd5_layerNonpivots S (memoryCutoff S)
              (Finset.mem_filter.mp hC).2 (pd5_isEdgeAt j)).card *
        v ^ memSize τL.1 := by
  classical
  let B := memoryCutoff S
  let Δ := aAtom * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))
  let atom := pd5_fixedAtom (K := K) S cmax aAtom
  let edgeFactor := pd5_edgeRowFactor F S Cedge
  let nsets := (Fintype.card (Finset (Fin K)) : ℝ) ^ 2
  let hSys : IsConstraintSystem (birthAddresses S.x K B) C :=
    (Finset.mem_filter.mp hC).2
  let U := pd5_layerAddresses C (pd5_isEdgeAt j)
  let R := pd5_layerNonpivots S B hSys (pd5_isEdgeAt j)
  let pick := pd5_addressPick S B hSys
  let hbox := pd5_envBox_finite_of_valid hS hw
  have hΔ : 0 ≤ Δ := by dsimp [Δ]; positivity
  have hatom : 0 ≤ atom := by dsimp [atom, pd5_fixedAtom]; positivity
  have hRU : R ⊆ U := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hUsupport : U ⊆ C.biUnion id := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hU : U ⊆ pd5_edgeAddresses K j := by
    simpa [U, pd5_layerAddresses] using pd5_edgeLayer_subset S.x B j hC
  have hULayer : ∀ a ∈ U, pd5_birthLayer a = 2 * j + 2 := by
    intro a ha
    exact (pd5_birthLayer_eq_edge_iff j a).mpr (Finset.mem_filter.mp ha).2
  have hA : birthAddresses S.x K B ⊆ birthAddresses S.x K B := fun _ ha => ha
  have hStrict : ∀ a ∈ R,
      pd5_birthIndex S B (pd5_addressPivot S B hSys a) < pd5_birthIndex S B a := by
    intro a ha
    exact pd5_layerNonpivot_strict S B hC hA (pd5_isEdgeAt j) ha
  have hPastLayer : ∀ e ∈ τL.2, pd5_birthLayer e.1 < 2 * j + 2 :=
    pd5_prefixGood_layers_lt_edge hLog
  let Wedge : BirthLog K → ℝ := fun batch =>
    pd5_prescribedWeight S B U R pick τL.2 batch
  have hWedge : ∀ batch, 0 ≤ Wedge batch := by
    intro batch
    exact (pd5_prescribedWeight_bounds S B U R pick τL.2 batch).1
  have hZ : ∀ z, envBox S w z → z ∈ hbox.toFinset := by
    intro z hz
    exact hbox.mem_toFinset.mpr hz
  have hRowsNow := hRows S hS hx w hw τL.1 hState
  rcases hRowsNow with ⟨_, hEdgeRows⟩
  let futureCoeff := Cghost ^ (k + 1) * edgeFactor ^ k * atom ^
    pd5_futureRank S B C (2 * j + 3)
  have hLpos : 0 < S.L := by
    dsimp [PDScale.L]
    exact Real.log_pos (by linarith [hS.1])
  have hv : 0 ≤ v := (lt_trans zero_lt_one hV).le
  have hfutureCoeff : 0 ≤ futureCoeff := by
    dsimp [futureCoeff, edgeFactor, pd5_edgeRowFactor, atom, pd5_fixedAtom]
    positivity [hLpos]
  have hBoundEdge : ∀ (r : MemPoint S.x K),
      pd5_stateRegion F S w B r →
      ∀ (choice : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i)
        (z' : ℤ × ℤ), EdgeAdmissible F S w r choice z' →
        memSize (z', edgeTargetLists F S r choice,
          edgeNewMemory F S r choice) ≤ B →
        ∀ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ‖logTrunc (some B) (logHistoryFn F S ρ w (some B) none
              (constraintWeight C) k)
            ((z', permuteLists σ (edgeTargetLists F S r choice),
                edgeNewMemory F S r choice),
              τL.2 ++ edgeBirths F S j r choice)‖ ≤
            futureCoeff * Wedge (edgeBirths F S j r choice) *
              v ^ memSize (z', edgeTargetLists F S r choice,
                edgeNewMemory F S r choice) := by
    intro r hR choice z' hAdm hcut σ
    let outLog := τL.2 ++ edgeBirths F S j r choice
    have hLogOut : pd5_logPrefixGood S.x B (j + 1) (j + 1) outLog := by
      exact pd5_logPrefixGood_append_edge hLog F S r choice rfl
        (by simpa [PDScale.N] using hStep)
    have hNewNodup : (edgeBirths F S j r choice).map Prod.fst |>.Nodup :=
      pd5_edgeBirths_addresses_nodup F S j r choice
    have hPrefixNodup : ∀ a : BirthAddress K,
        ((outLog.filter fun e =>
          pd5_birthIndex S B e.1 < pd5_birthIndex S B a).map Prod.fst).Nodup := by
      intro a
      let P : BirthAddress K → Prop := fun b =>
        pd5_birthIndex S B b < pd5_birthIndex S B a
      letI : DecidablePred P := fun b => Nat.decLt _ _
      letI : DecidablePred (fun e : BirthAddress K × ℕ => P e.1) :=
        fun e => Nat.decLt _ _
      exact pd5_filtered_projection_nodup outLog P hLogOut.1
    have hStrict : ∀ a ∈ R,
        pd5_birthIndex S B (pd5_addressPivot S B hSys a) < pd5_birthIndex S B a := by
      intro a ha
      exact pd5_layerNonpivot_strict S B hC hA (pd5_isEdgeAt j) ha
    let target : MemPoint S.x K :=
      (z', permuteLists σ (edgeTargetLists F S r choice),
        edgeNewMemory F S r choice)
    let targetLog : LogPoint S.x K := (target, outLog)
    have hcutTarget : memSize target ≤ B := by
      simpa [target, memSize] using hcut
    have hcutTargetLog : memSize targetLog.1 ≤ B := by
      simpa [targetLog] using hcutTarget
    have hStateOut : pd5_stateRegion F S w B
        (z', edgeTargetLists F S r choice, edgeNewMemory F S r choice) :=
      pd5_edge_output_region F S w B r choice z' hR hAdm hcut
    have hStateTarget : pd5_stateRegion F S w B target := by
      simpa [target] using pd5_stateRegion_permute F S w B
        (z', edgeTargetLists F S r choice, edgeNewMemory F S r choice) σ hStateOut
    by_cases hGood : pd5_prefixConstraintOK C (2 * j + 3) outLog
    · have hGateEq : Wedge (edgeBirths F S j r choice) = 1 := by
        have hGate := pd5_good_prefix_gives_stage_gate S B hC hA U R hRU hUsupport
          (2 * j + 2) hULayer hStrict τL.2 (edgeBirths F S j r choice)
          hNewNodup hPrefixNodup hPastLayer hGood
        simpa [Wedge] using hGate
      have hLogIH : pd5_logPrefixGood S.x B (S.N - k) (S.N - k) outLog := by
        simpa [hN] using hLogOut
      have hGoodIH :
          pd5_prefixConstraintOK C (2 * (S.N - k) + 1) outLog := by
        rw [hN]
        convert hGood using 1 <;> omega
      have hIHbound := hIH targetLog hStateTarget hLogIH hGoodIH
      have hRankEq : 2 * (S.N - k) + 1 = 2 * j + 3 := by omega
      have hIHbound' :
          ‖logHistoryFn F S ρ w (some B) none (constraintWeight C) k targetLog‖ ≤
            futureCoeff * v ^ memSize target := by
        simpa [futureCoeff, edgeFactor, atom, targetLog, target, hRankEq] using hIHbound
      have htrunc : logTrunc (some B)
          (logHistoryFn F S ρ w (some B) none (constraintWeight C) k) targetLog =
            logHistoryFn F S ρ w (some B) none (constraintWeight C) k targetLog := by
        simp [logTrunc, hcutTargetLog]
      calc
        _ = ‖logHistoryFn F S ρ w (some B) none (constraintWeight C) k targetLog‖ :=
          congrArg norm htrunc
        _ ≤ futureCoeff * v ^ memSize target := hIHbound'
        _ = futureCoeff * Wedge (edgeBirths F S j r choice) *
              v ^ memSize (z', edgeTargetLists F S r choice,
                edgeNewMemory F S r choice) := by
          rw [hGateEq]
          simp [target, memSize]
    · have hZeroIH :
          logHistoryFn F S ρ w (some B) none (constraintWeight C) k targetLog = 0 := by
        apply pd5_logHistoryFn_zero_of_bad_prefix F S ρ w B C k (by omega) targetLog
        rw [hN]
        convert hGood using 1 <;> omega
      have hcutPerm :
          memSize (z', permuteLists σ (edgeTargetLists F S r choice),
            edgeNewMemory F S r choice) ≤ B := by
        simpa [memSize] using hcut
      have hrhs : 0 ≤ futureCoeff * Wedge (edgeBirths F S j r choice) *
          v ^ memSize (z', edgeTargetLists F S r choice,
            edgeNewMemory F S r choice) :=
        mul_nonneg (mul_nonneg hfutureCoeff (hWedge _)) (pow_nonneg hv _)
      have hhistoryZero :
          logHistoryFn F S ρ w (some B) none (constraintWeight C) k
            ((z', permuteLists σ (edgeTargetLists F S r choice),
              edgeNewMemory F S r choice),
              τL.2 ++ edgeBirths F S j r choice) = 0 := by
        simpa [targetLog, target, outLog] using hZeroIH
      calc
        _ = 0 := by
          simp [logTrunc, hcutPerm, hhistoryZero]
        _ ≤ futureCoeff * Wedge (edgeBirths F S j r choice) *
            v ^ memSize (z', edgeTargetLists F S r choice,
              edgeNewMemory F S r choice) := hrhs
  have hEdgeOp := pd5_logEdge_norm_le_positiveAverage F S ρ w j B hbox Wedge
    (logHistoryFn F S ρ w (some B) none (constraintWeight C) k)
    futureCoeff v τL hState hfutureCoeff hv hWedge hBoundEdge
  have hEdgeRow := hEdgeRows j (by simpa [PDScale.N] using hStep)
    U R hRU hU pick τL.2 hbox.toFinset hZ
  have hAbsEq :
      pd5_edgeAbsChoice F S ρ w j B hbox.toFinset Wedge
          (fun s => v ^ memSize s) τL.1 =
      pd5_activeAverage S
          (fun r => pd5_edgePositiveTotal F S ρ w j B hbox.toFinset Wedge v r)
          τL.1 := by
    simp [pd5_edgeAbsChoice, pd5_edgePositiveTotal,
      pd5_activeAverage_memSize_pow, B, hState.2.1]
  rw [hAbsEq] at hEdgeRow
  have hRowΔ :
      Cedge * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow S.L (3 * F.A₀) *
          Δ ^ R.card * v ^ memSize τL.1 ≤
        Cedge * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow S.L (3 * F.A₀) *
          atom ^ R.card * v ^ memSize τL.1 := by
    have hAtomLe : Δ ≤ atom := by
      simpa [atom, pd5_fixedAtom, Δ] using
        (mul_le_mul_of_nonneg_right hCmax hΔ)
    have hpow : Δ ^ R.card ≤ atom ^ R.card :=
      pow_le_pow_left₀ hΔ hAtomLe _
    have hleft : 0 ≤ Cedge * ((B + 1 : ℕ) : ℝ) ^ K *
        Real.rpow S.L (3 * F.A₀) := by
      exact mul_nonneg
        (mul_nonneg (le_of_lt hCedge)
          (pow_nonneg (Nat.cast_nonneg (B + 1)) K))
        (Real.rpow_nonneg hLpos.le _)
    calc
      _ = (Cedge * ((B + 1 : ℕ) : ℝ) ^ K *
            Real.rpow S.L (3 * F.A₀) * Δ ^ R.card) *
            v ^ memSize τL.1 := by ring
      _ ≤ (Cedge * ((B + 1 : ℕ) : ℝ) ^ K *
            Real.rpow S.L (3 * F.A₀) * atom ^ R.card) *
            v ^ memSize τL.1 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hleft)
            (pow_nonneg hv _)
      _ = _ := by ring
  have hEdgeBound :
      ‖logTrunc (some B)
        (logEdge F S ρ w EdgeKind.full j
          (logTrunc (some B)
            (logHistoryFn F S ρ w (some B) none (constraintWeight C) k))) τL‖ ≤
        futureCoeff * edgeFactor * atom ^ R.card * v ^ memSize τL.1 := by
    have hsize : memSize τL.1 ≤ B := hState.2.1
    calc
      _ = ‖logEdge F S ρ w EdgeKind.full j
          (logTrunc (some B)
            (logHistoryFn F S ρ w (some B) none (constraintWeight C) k)) τL‖ := by
              simp [logTrunc, hsize]
      _ ≤ 2 * nsets * futureCoeff *
          pd5_activeAverage S
            (fun r => pd5_edgePositiveTotal F S ρ w j B hbox.toFinset Wedge v r)
            τL.1 := hEdgeOp
      _ ≤ 2 * nsets * futureCoeff *
          (Cedge * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow S.L (3 * F.A₀) *
            Δ ^ R.card * v ^ memSize τL.1) := by
              apply mul_le_mul_of_nonneg_left hEdgeRow
              positivity
      _ ≤ futureCoeff * edgeFactor * atom ^ R.card * v ^ memSize τL.1 := by
              have hfactor : 0 ≤ 2 * nsets * futureCoeff := by positivity
              calc
                _ ≤ 2 * nsets * futureCoeff *
                    (Cedge * ((B + 1 : ℕ) : ℝ) ^ K *
                      Real.rpow S.L (3 * F.A₀) * atom ^ R.card *
                        v ^ memSize τL.1) := by
                          exact mul_le_mul_of_nonneg_left hRowΔ
                            (show 0 ≤ 2 * nsets * futureCoeff by positivity)
                _ = _ := by
                          simp [edgeFactor, pd5_edgeRowFactor, nsets]
                          ring
  exact hEdgeBound

private theorem pd5_logHistoryFn_ghost_step_bound {K : ℕ}
    (δ c₁ c₂ : ℝ) (F : PDFix K) (ρ : ℝ)
    (v Cghost Cedge cmax aAtom x₀ : ℝ)
    (hV : 1 < v) (hCghost : 0 < Cghost) (hCedge : 0 < Cedge)
    (hCmax : 1 ≤ cmax) (hAtom : 0 < aAtom)
    (hRows : PD5PositiveRows δ c₁ c₂ F ρ v Cghost Cedge cmax aAtom x₀)
    (S : PDScale) (hS : S.Valid K δ c₁ c₂) (hx : x₀ ≤ S.x)
    (w : ArchRoot) (hw : w.InRegion S)
    (C : Finset (Finset (BirthAddress K)))
    (hC : C ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)))
    (k j : ℕ) (hk : k ≤ S.N) (hN : S.N - k = j + 1)
    (hStep : j < S.N)
    (hIH : ∀ τL : LogPoint S.x K,
      pd5_stateRegion F S w (memoryCutoff S) τL.1 →
      pd5_logPrefixGood S.x (memoryCutoff S) (S.N - k) (S.N - k) τL.2 →
      pd5_prefixConstraintOK C (2 * (S.N - k) + 1) τL.2 →
      ‖logHistoryFn F S ρ w (some (memoryCutoff S)) none
          (constraintWeight C) k τL‖ ≤
        Cghost ^ (k + 1) * (pd5_edgeRowFactor F S Cedge) ^ k *
          (pd5_fixedAtom (K := K) S cmax aAtom) ^
            pd5_futureRank S (memoryCutoff S) C (2 * (S.N - k) + 1) *
          v ^ memSize τL.1)
    (τL : LogPoint S.x K)
    (hState : pd5_stateRegion F S w (memoryCutoff S) τL.1)
    (hLog : pd5_logPrefixGood S.x (memoryCutoff S) j j τL.2)
    (hPrefix : pd5_prefixConstraintOK C (2 * j + 1) τL.2) :
    ‖logHistoryFn F S ρ w (some (memoryCutoff S)) none
        (constraintWeight C) (k + 1) τL‖ ≤
      Cghost ^ (k + 2) * (pd5_edgeRowFactor F S Cedge) ^ (k + 1) *
        (pd5_fixedAtom (K := K) S cmax aAtom) ^
          pd5_futureRank S (memoryCutoff S) C (2 * (S.N - (k + 1)) + 1) *
        v ^ memSize τL.1 := by
  classical
  let B := memoryCutoff S
  let Δ := aAtom * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))
  let atom := pd5_fixedAtom (K := K) S cmax aAtom
  let edgeFactor := pd5_edgeRowFactor F S Cedge
  let hSys : IsConstraintSystem (birthAddresses S.x K B) C :=
    (Finset.mem_filter.mp hC).2
  let U := pd5_layerAddresses C pd5_isInitial
  let Ughost := pd5_layerAddresses C (pd5_isGhostAt j)
  let Rghost := pd5_layerNonpivots S B hSys (pd5_isGhostAt j)
  let Redge := pd5_layerNonpivots S B hSys (pd5_isEdgeAt j)
  let pick := pd5_addressPick S B hSys
  let Wghost : BirthLog K → ℝ := fun batch =>
    pd5_prescribedWeight S B Ughost Rghost pick τL.2 batch
  let futureCoeff := Cghost ^ (k + 1) * edgeFactor ^ k *
    atom ^ pd5_futureRank S B C (2 * j + 3)
  let edgeStepCoeff := futureCoeff * edgeFactor * atom ^ Redge.card
  have hΔ : 0 ≤ Δ := by dsimp [Δ]; positivity
  have hatom : 0 ≤ atom := by dsimp [atom, pd5_fixedAtom]; positivity
  have hv : 0 ≤ v := (lt_trans zero_lt_one hV).le
  have hLpos : 0 < S.L := by
    dsimp [PDScale.L]
    exact Real.log_pos (by linarith [hS.1])
  have hEdgeFactor : 0 ≤ edgeFactor := by
    dsimp [edgeFactor, pd5_edgeRowFactor]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hCedge.le)
        (pow_nonneg (Nat.cast_nonneg (memoryCutoff S + 1)) K))
      (Real.rpow_nonneg hLpos.le _)
  have hfutureCoeff : 0 ≤ futureCoeff := by
    dsimp [futureCoeff]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hCghost.le _) (pow_nonneg hEdgeFactor _))
      (pow_nonneg hatom _)
  have hedgeStepCoeff : 0 ≤ edgeStepCoeff := by
    dsimp [edgeStepCoeff]
    exact mul_nonneg (mul_nonneg hfutureCoeff hEdgeFactor) (pow_nonneg hatom _)
  have hRU : Rghost ⊆ Ughost := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hUsupport : Ughost ⊆ C.biUnion id := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hU : Ughost ⊆ pd5_ghostAddresses K j B := by
    simpa [Ughost, pd5_layerAddresses] using pd5_ghostLayer_subset S.x B j hC
  have hULayer : ∀ a ∈ Ughost, pd5_birthLayer a = 2 * j + 1 := by
    intro a ha
    exact (pd5_birthLayer_eq_ghost_iff j a).mpr (Finset.mem_filter.mp ha).2
  have hA : birthAddresses S.x K B ⊆ birthAddresses S.x K B := fun _ ha => ha
  have hStrict : ∀ a ∈ Rghost,
      pd5_birthIndex S B (pd5_addressPivot S B hSys a) < pd5_birthIndex S B a := by
    intro a ha
    exact pd5_layerNonpivot_strict S B hC hA (pd5_isGhostAt j) ha
  have hPastLayer : ∀ e ∈ τL.2, pd5_birthLayer e.1 < 2 * j + 1 :=
    pd5_prefixGood_layers_lt_ghost hLog
  have hWghost : ∀ batch, 0 ≤ Wghost batch := by
    intro batch
    exact (pd5_prescribedWeight_bounds S B Ughost Rghost pick τL.2 batch).1
  have hRowsNow := hRows S hS hx w hw τL.1 hState
  rcases hRowsNow with ⟨hghostRows, _hEdgeRows⟩
  have hGhostRow := hghostRows j (by omega) Ughost Rghost hRU hU pick τL.2
  have hBoundGhost : ∀ (D : (i : Fin K) → Finset (Fin (τL.1.2.2 i).length))
      (l : Fin K → ℕ)
      (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)),
      (∀ i, D i ⊆ hitIndices (τL.1.2.2 i) τL.1.1) →
      memSize (pd5_ghostOutput F S τL D l new j).1 ≤ B →
      ‖logTrunc (some B)
          (logEdge F S ρ w EdgeKind.full j
            (logTrunc (some B)
              (logHistoryFn F S ρ w (some B) none (constraintWeight C) k)))
          (pd5_ghostOutput F S τL D l new j)‖ ≤
        edgeStepCoeff * Wghost
            (pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))) *
          v ^ memSize (pd5_ghostOutput F S τL D l new j).1 := by
    intro D l new hDel hCut
    let batch := pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))
    let out := pd5_ghostOutput F S τL D l new j
    have hlBound : ∀ i, l i ≤ B := by
      intro i
      have hlen := pd5_ghost_length_le_memSize τL.1 D l
        (fun i k => (new i k : ℕ)) i
      have hsize : memSize
          (τL.1.1, τL.1.2.1, fun i =>
            removeIndices (τL.1.2.2 i) (D i) ++
              List.ofFn fun k => anchorAt (new i k) τL.1.1) ≤ B := by
        simpa [out, pd5_ghostOutput] using hCut
      exact hlen.trans hsize
    have hLogOut : pd5_logPrefixGood S.x B j (j + 1)
        (τL.2 ++ batch) := by
      exact pd5_logPrefixGood_append_ghostBatch hLog
        (by simpa [PDScale.N] using (Nat.le_of_lt hStep))
        l hlBound (fun i k => (new i k : ℕ))
    have hNewNodup : (batch.map Prod.fst).Nodup := by
      dsimp [batch]
      rw [pd5_ghostBirthLog_map_fst]
      exact pd5_ghostAddressList_nodup j l
    have hPrefixNodup : ∀ a : BirthAddress K,
        (((τL.2 ++ batch).filter fun e =>
          pd5_birthIndex S B e.1 < pd5_birthIndex S B a).map Prod.fst).Nodup := by
      intro a
      let P : BirthAddress K → Prop := fun b =>
        pd5_birthIndex S B b < pd5_birthIndex S B a
      letI : DecidablePred P := fun b => Nat.decLt _ _
      letI : DecidablePred (fun e : BirthAddress K × ℕ => P e.1) :=
        fun e => Nat.decLt _ _
      exact pd5_filtered_projection_nodup (τL.2 ++ batch) P hLogOut.1
    have hGoodOut : pd5_logPrefixGood S.x B j (j + 1) out.2 := by
      simpa [out, batch, pd5_ghostOutput, pd5_ghostBirthLog] using hLogOut
    have hStateOut : pd5_stateRegion F S w B out.1 :=
      pd5_ghost_output_region F S w B τL D l new j hState hDel hCut
    by_cases hgood : pd5_prefixConstraintOK C (2 * j + 2) out.2
    · have hGate : Wghost batch = 1 := by
        dsimp [Wghost]
        have hgood' : pd5_prefixConstraintOK C (2 * j + 1 + 1)
            (τL.2 ++ batch) := by
          convert hgood using 1 <;> simp [out, batch, pd5_ghostOutput,
            pd5_ghostBirthLog] <;> omega
        exact pd5_good_prefix_gives_stage_gate S B hC hA Ughost Rghost hRU
          hUsupport (2 * j + 1) hULayer hStrict τL.2 batch hNewNodup
          hPrefixNodup hPastLayer hgood'
      have hEdge := pd5_logHistoryFn_edge_step_bound δ c₁ c₂ F ρ
        v Cghost Cedge cmax aAtom x₀ hV hCghost hCedge hCmax hAtom hRows
        S hS hx w hw C hC k hk j hN hStep hIH out hStateOut hGoodOut hgood
      have hEdge' :
          ‖logTrunc (some B)
              (logEdge F S ρ w EdgeKind.full j
                (logTrunc (some B)
                  (logHistoryFn F S ρ w (some B) none (constraintWeight C) k))) out‖ ≤
            edgeStepCoeff * v ^ memSize out.1 := by
        simpa [edgeStepCoeff, futureCoeff, edgeFactor, atom, Redge] using hEdge
      calc
        _ ≤ edgeStepCoeff * v ^ memSize out.1 := hEdge'
        _ = edgeStepCoeff * Wghost batch * v ^ memSize out.1 := by
          rw [hGate]
          ring
    · have hEdgeAppend : ∀ L s choice,
          (¬ pd5_prefixConstraintOK C (2 * j + 2) L) →
          ¬ pd5_prefixConstraintOK C (2 * j + 2)
            (L ++ edgeBirths F S j s choice) := by
        intro L s choice hBad
        apply pd5_prefixConstraintOK_bad_extend C (2 * j + 2)
          L (edgeBirths F S j s choice) hBad
        intro e he
        have hfst : e.1 ∈ (edgeBirths F S j s choice).map Prod.fst :=
          List.mem_map.mpr ⟨e, he, rfl⟩
        rw [pd5_edgeBirths_layer F S j s choice hfst]
      have hFnZero : ∀ τG : LogPoint S.x K,
          (¬ pd5_prefixConstraintOK C (2 * j + 2) τG.2) →
          logTrunc (some B)
            (logHistoryFn F S ρ w (some B) none (constraintWeight C) k) τG = 0 := by
        intro τG hBad
        by_cases hsize : memSize τG.1 ≤ B
        · have hbadIH :
              ¬ pd5_prefixConstraintOK C (2 * (S.N - k) + 1) τG.2 := by
            intro hgoodIH
            have hgood' : pd5_prefixConstraintOK C (2 * j + 2) τG.2 := by
              have hstage : 2 * j + 2 ≤ 2 * (S.N - k) + 1 := by
                rw [hN]
                omega
              exact pd5_prefixConstraintOK_mono hstage hgoodIH
            exact hBad hgood'
          have hzero := pd5_logHistoryFn_zero_of_bad_prefix F S ρ w B C k hk τG hbadIH
          simp [logTrunc, hsize, hzero]
        · simp [logTrunc, hsize]
      have hEdgeZero := pd5_logEdge_zero_of_badPredicate F S ρ w j
        (fun L => ¬ pd5_prefixConstraintOK C (2 * j + 2) L)
        hEdgeAppend
        (logTrunc (some B)
          (logHistoryFn F S ρ w (some B) none (constraintWeight C) k))
        hFnZero out hgood
      have htruncZero :
          logTrunc (some B)
            (logEdge F S ρ w EdgeKind.full j
              (logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none (constraintWeight C) k))) out = 0 := by
        simp [logTrunc, hEdgeZero]
      have hrhs : 0 ≤ edgeStepCoeff * Wghost batch *
          v ^ memSize out.1 :=
        mul_nonneg (mul_nonneg hedgeStepCoeff (hWghost batch)) (pow_nonneg hv _)
      rw [htruncZero]
      simpa using hrhs
  have hGhostOp := pd5_logGhost_norm_le_absChoice F S ρ j B Wghost
    (logEdge F S ρ w EdgeKind.full j
      (logTrunc (some B)
        (logHistoryFn F S ρ w (some B) none (constraintWeight C) k)))
    edgeStepCoeff v τL
    (by simpa [B] using (show memSize τL.1 ≤ memoryCutoff S from hState.2.1))
    hedgeStepCoeff hv hWghost hBoundGhost
  have hRow := hGhostRow
  have hGhostBound :
      ‖logGhost F S ρ j
          (logTrunc (some B)
            (logEdge F S ρ w EdgeKind.full j
              (logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none (constraintWeight C) k)))) τL‖ ≤
        edgeStepCoeff * (Cghost * atom ^ Rghost.card * v ^ memSize τL.1) := by
    calc
      _ ≤ edgeStepCoeff *
          pd5_ghostAbsChoice F S ρ j B Wghost (fun s => v ^ memSize s) τL.1 := hGhostOp
      _ ≤ edgeStepCoeff * (Cghost * atom ^ Rghost.card * v ^ memSize τL.1) :=
        mul_le_mul_of_nonneg_left
          (by simpa [atom, pd5_fixedAtom] using hRow) hedgeStepCoeff
  have hRankSplit := pd5_futureRank_split S B hC j
  have hCoeffEq :
      Cghost ^ (k + 2) * edgeFactor ^ (k + 1) *
          atom ^ pd5_futureRank S B C (2 * j + 1) =
        edgeStepCoeff * (Cghost * atom ^ Rghost.card) := by
    have hpowC : Cghost ^ (k + 2) = Cghost ^ (k + 1) * Cghost := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    have hpowE : edgeFactor ^ (k + 1) = edgeFactor ^ k * edgeFactor := by
      rw [pow_succ]
    have hpowAtom :
        atom ^ (Rghost.card + Redge.card +
          pd5_futureRank S B C (2 * j + 3)) =
          atom ^ Rghost.card * atom ^ Redge.card *
            atom ^ pd5_futureRank S B C (2 * j + 3) := by
      rw [Nat.add_assoc, pow_add, pow_add]
      ring
    calc
      _ = Cghost ^ (k + 1) * Cghost *
          (edgeFactor ^ k * edgeFactor) *
          atom ^ (Rghost.card + Redge.card +
            pd5_futureRank S B C (2 * j + 3)) := by
              rw [hpowC, hpowE, hRankSplit]
      _ = edgeStepCoeff * (Cghost * atom ^ Rghost.card) := by
        rw [hpowAtom]
        dsimp [edgeStepCoeff, futureCoeff]
        ring
  have hUnfold :
      logHistoryFn F S ρ w (some B) none (constraintWeight C) (k + 1) τL =
        logGhost F S ρ j
          (logTrunc (some B)
            (logEdge F S ρ w EdgeKind.full j
              (logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none (constraintWeight C) k)))) τL := by
    have hJ : pathLength S.x - (k + 1) = j := by
      simpa [PDScale.N] using (show S.N - (k + 1) = j by omega)
    have hcut : memSize τL.1 ≤ B := by simpa [B] using hState.2.1
    change logTrunc (some B)
        (logPathRestrict none (pathLength S.x - (k + 1))
          (logGhost F S ρ (pathLength S.x - (k + 1))
            (logTrunc (some B)
              (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
                (logTrunc (some B)
                (logHistoryFn F S ρ w (some B) none (constraintWeight C) k)))))) τL =
      logGhost F S ρ j
        (logTrunc (some B)
          (logEdge F S ρ w EdgeKind.full j
            (logTrunc (some B)
              (logHistoryFn F S ρ w (some B) none (constraintWeight C) k)))) τL
    rw [hJ]
    simp [logPathRestrict, logTrunc, hcut]
  have hBound :
      ‖logHistoryFn F S ρ w (some B) none (constraintWeight C) (k + 1) τL‖ ≤
        Cghost ^ (k + 2) * edgeFactor ^ (k + 1) *
          atom ^ pd5_futureRank S B C (2 * j + 1) * v ^ memSize τL.1 := by
    rw [hUnfold]
    calc
      _ ≤ edgeStepCoeff *
          (Cghost * atom ^ Rghost.card * v ^ memSize τL.1) := hGhostBound
      _ = (edgeStepCoeff * (Cghost * atom ^ Rghost.card)) *
          v ^ memSize τL.1 := by ring
      _ = (Cghost ^ (k + 2) * edgeFactor ^ (k + 1) *
          atom ^ pd5_futureRank S B C (2 * j + 1)) *
          v ^ memSize τL.1 := by rw [← hCoeffEq]
      _ = Cghost ^ (k + 2) * edgeFactor ^ (k + 1) *
          atom ^ pd5_futureRank S B C (2 * j + 1) * v ^ memSize τL.1 := by ring
  have hStage : 2 * (S.N - (k + 1)) + 1 = 2 * j + 1 := by omega
  simpa [edgeFactor, atom, B, hStage] using hBound

private theorem pd5_logHistoryFn_uniform_bound {K : ℕ}
    (δ c₁ c₂ : ℝ) (F : PDFix K) (ρ : ℝ)
    (v Cghost Cedge cmax aAtom x₀ : ℝ)
    (hV : 1 < v) (hCghost : 0 < Cghost) (hCedge : 0 < Cedge)
    (hCmax : 1 ≤ cmax) (hAtom : 0 < aAtom)
    (hRows : PD5PositiveRows δ c₁ c₂ F ρ v Cghost Cedge cmax aAtom x₀)
    (S : PDScale) (hS : S.Valid K δ c₁ c₂) (hx : x₀ ≤ S.x)
    (w : ArchRoot) (hw : w.InRegion S)
    (C : Finset (Finset (BirthAddress K)))
    (hC : C ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S))) :
    ∀ k, k ≤ S.N → ∀ τL : LogPoint S.x K,
      pd5_stateRegion F S w (memoryCutoff S) τL.1 →
      pd5_logPrefixGood S.x (memoryCutoff S) (S.N - k) (S.N - k) τL.2 →
      pd5_prefixConstraintOK C (2 * (S.N - k) + 1) τL.2 →
      ‖logHistoryFn F S ρ w (some (memoryCutoff S)) none
          (constraintWeight C) k τL‖ ≤
        Cghost ^ (k + 1) * (pd5_edgeRowFactor F S Cedge) ^ k *
          (pd5_fixedAtom (K := K) S cmax aAtom) ^
            pd5_futureRank S (memoryCutoff S) C (2 * (S.N - k) + 1) *
          v ^ memSize τL.1 := by
  intro k
  induction k with
  | zero =>
      intro hk τL hState hLog hPrefix
      have hBase := pd5_logHistoryFn_base_bound δ c₁ c₂ F ρ
        v Cghost Cedge cmax aAtom x₀ hV hCghost hCedge hCmax hAtom hRows
        S hS hx w hw C hC τL hState hLog hPrefix
      have hFinal := pd5_futureRank_final S (memoryCutoff S) hC
      simpa [pd5_fixedAtom, pd5_edgeRowFactor, hFinal] using hBase
  | succ k ih =>
      intro hk τL hState hLog hPrefix
      have hk' : k ≤ S.N := by omega
      let j := S.N - (k + 1)
      have hN : S.N - k = j + 1 := by dsimp [j]; omega
      have hStep : j < S.N := by dsimp [j]; omega
      have hPrevIH : ∀ τG : LogPoint S.x K,
          pd5_stateRegion F S w (memoryCutoff S) τG.1 →
          pd5_logPrefixGood S.x (memoryCutoff S) (S.N - k) (S.N - k) τG.2 →
          pd5_prefixConstraintOK C (2 * (S.N - k) + 1) τG.2 →
          ‖logHistoryFn F S ρ w (some (memoryCutoff S)) none
              (constraintWeight C) k τG‖ ≤
            Cghost ^ (k + 1) * (pd5_edgeRowFactor F S Cedge) ^ k *
              (pd5_fixedAtom (K := K) S cmax aAtom) ^
                pd5_futureRank S (memoryCutoff S) C (2 * (S.N - k) + 1) *
              v ^ memSize τG.1 := by
        intro τG hStateG hLogG hPrefixG
        exact ih hk' τG hStateG hLogG hPrefixG
      exact pd5_logHistoryFn_ghost_step_bound δ c₁ c₂ F ρ
        v Cghost Cedge cmax aAtom x₀ hV hCghost hCedge hCmax hAtom hRows
        S hS hx w hw C hC k j hk' hN hStep hPrevIH τL hState
        (by simpa [j] using hLog) (by simpa [j] using hPrefix)

private theorem pd5_initial_serial_lt_of_birthIndex_lt {K : ℕ}
    (S : PDScale) (B : ℕ)
    (i i' : Fin K) (j j' : Fin (slotCount S.x))
    (h : pd5_birthIndex S B (.initial i j.val) <
      pd5_birthIndex S B (.initial i' j'.val)) :
    (finProdFinEquiv (i, j)).val < (finProdFinEquiv (i', j')).val := by
  let R := max (slotCount S.x) B + 1
  have hR : 0 < R := by dsimp [R]; omega
  have hIndex : i.val * R + j.val < i'.val * R + j'.val := by
    simpa [R, pd5_birthIndex] using h
  by_cases hGroup : i.val < i'.val
  · have hUpper : j.val + slotCount S.x * i.val < (i.val + 1) * slotCount S.x := by
      calc
        _ < slotCount S.x + slotCount S.x * i.val :=
          Nat.add_lt_add_right j.isLt _
        _ = (i.val + 1) * slotCount S.x := by
          rw [Nat.add_mul, one_mul]
          simp [Nat.mul_comm, Nat.add_comm]
    have hBase : (i.val + 1) * slotCount S.x ≤ i'.val * slotCount S.x :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hGroup)
    have hLower : i'.val * slotCount S.x ≤
        j'.val + slotCount S.x * i'.val := by
      simpa [Nat.mul_comm, Nat.add_comm] using
        (Nat.le_add_right (slotCount S.x * i'.val) j'.val)
    change j.val + slotCount S.x * i.val <
      j'.val + slotCount S.x * i'.val
    exact lt_of_lt_of_le hUpper (le_trans hBase hLower)
  · have hReverse : ¬ i'.val < i.val := by
      intro hRev
      have hRevUpper : i'.val * R + j'.val <
          (i'.val + 1) * R := by
        have hjR : j'.val < R := by
          dsimp [R]
          have hM : slotCount S.x ≤ max (slotCount S.x) B := Nat.le_max_left _ _
          omega
        calc
          _ < i'.val * R + R := Nat.add_lt_add_left hjR _
          _ = (i'.val + 1) * R := by
            rw [Nat.add_mul, one_mul]
      have hRevBase : (i'.val + 1) * R ≤ i.val * R :=
        Nat.mul_le_mul_right R (Nat.succ_le_of_lt hRev)
      have hRevLower : i.val * R ≤ i.val * R + j.val := Nat.le_add_right _ _
      have hRevIndex : i'.val * R + j'.val < i.val * R + j.val := by
        exact lt_of_lt_of_le hRevUpper (le_trans hRevBase hRevLower)
      omega
    have hSame : i.val = i'.val := by omega
    have hSlot : j.val < j'.val := by
      rw [hSame] at hIndex
      omega
    change j.val + slotCount S.x * i.val <
      j'.val + slotCount S.x * i'.val
    rw [hSame]
    exact Nat.add_lt_add_right hSlot _

private theorem pd5_initialLog_entry {K : ℕ} {x : ℝ}
    (s : MemPoint x K) (i : Fin K) (j : Fin (slotCount x)) :
    (BirthAddress.initial i j.val, s.2.1 i j) ∈ initialLog s := by
  unfold initialLog
  apply List.mem_flatMap.mpr
  refine ⟨i, by simp, ?_⟩
  apply List.mem_map.mpr
  exact ⟨j, by simp, rfl⟩

private theorem pd5_constraintRank_initial_future {K : ℕ} (S : PDScale) (B : ℕ)
    {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems (birthAddresses S.x K B)) :
    constraintRank C =
      (pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2 pd5_isInitial).card +
        pd5_futureRank S B C 1 := by
  classical
  let R := pd5_allNonpivots S B C
  have hzero : R.filter (fun a => pd5_birthLayer a = 0) =
      pd5_layerNonpivots S B (Finset.mem_filter.mp hC).2 pd5_isInitial := by
    have hfilter : R.filter (fun a => pd5_birthLayer a = 0) = R.filter pd5_isInitial := by
      ext a
      simp [pd5_birthLayer_eq_zero_iff]
    rw [hfilter, ← pd5_layerNonpivots_eq_all_filter S B hC pd5_isInitial]
  have hunion : R.filter (fun a => pd5_birthLayer a = 0) ∪
      R.filter (fun a => 1 ≤ pd5_birthLayer a) = R := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨ha, h0⟩ | ⟨ha, hge⟩)
      · exact ha
      · exact ha
    · intro ha
      by_cases h0 : pd5_birthLayer a = 0
      · exact Or.inl ⟨ha, h0⟩
      · exact Or.inr ⟨ha, by omega⟩
  have hdisj : Disjoint (R.filter (fun a => pd5_birthLayer a = 0))
      (R.filter (fun a => 1 ≤ pd5_birthLayer a)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have h0 := (Finset.mem_filter.mp ha).2
    have hge := (Finset.mem_filter.mp hb).2
    omega
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcard
  have hRank : R.card = constraintRank C := pd5_allNonpivots_card S B hC
  have hfuture : (R.filter (fun a => 1 ≤ pd5_birthLayer a)).card =
      pd5_futureRank S B C 1 := by
    rfl
  rw [hRank, hzero, hfuture] at hcard
  exact hcard

/-- Fixed-system absolute bound from positive choices, with chronological pivots.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:328–397`; uses pd5_positive_choice_rows,
pd5_triangular_birth_sum_le, pd5_chronological_model and pd5_scale_facts;
feeds pd5_high_rank_tail and frozen history_rank_high. Constants precede S,w and the system. -/
theorem pd5_fixed_system_abs_estimate (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ)
    (hrows : PD5PositiveRowsAvailable δ c₁ c₂ F ρ) :
    ∃ Cabs aAtom x₀ : ℝ, 0 < Cabs ∧ 0 < aAtom ∧ 2 ≤ x₀ ∧
      ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
        ∀ C ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)),
          ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ ≤
            Real.rpow S.L (Cabs * ((S.N : ℝ) + 1)) *
              (aAtom * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))) ^ constraintRank C := by
  classical
  rcases hrows with ⟨v, Cghost, Cedge, cmax, aRows, xRows,
    hV, hCghost, hCedge, hCmax, hRowsAtom, hxRows, hRows⟩
  obtain ⟨xScale, hxScale, hScaleFacts⟩ := pd5_scale_facts K F hF
  let aBase := max aRows (4 / Real.log 2)
  let aOut := cmax * aBase
  let edgeInflation := (1 + 2 * (Fintype.card (Finset (Fin K)) : ℝ) ^ 2) * Cedge
  let thresholdL := max Cghost (max 2 (edgeInflation * (3 : ℝ) ^ K))
  let x₀ := max xRows (max xScale (Real.exp thresholdL))
  let Cabs := 3 * (K : ℝ) + 3 * F.A₀ + 3
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have haBase : 0 < aBase := lt_of_lt_of_le hRowsAtom (le_max_left _ _)
  have haOut : 0 < aOut := mul_pos (lt_of_lt_of_le (by norm_num) hCmax) haBase
  have hEdgeInflation : 0 < edgeInflation := by
    dsimp [edgeInflation]
    positivity
  have hCabs : 0 < Cabs := by
    have hA₀ : 0 < F.A₀ := hF.2.2.2.1
    dsimp [Cabs]
    positivity
  have hx₀ : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxRows (le_max_left _ _)
  refine ⟨Cabs, aOut, x₀, hCabs, haOut, hx₀, ?_⟩
  intro S hS hx₀S w hw C hC
  have hxRowsS : xRows ≤ S.x := le_trans (le_max_left _ _) hx₀S
  have hxScaleS : xScale ≤ S.x := le_trans
    (le_trans (le_max_left _ _) (le_max_right _ _)) hx₀S
  have hscale := hScaleFacts S hxScaleS
  rcases hscale with ⟨hL1, hN2, hNlower, hNupper, hMupper, hBupper, hMN, hBands⟩
  let B := memoryCutoff S
  let M := slotCount S.x
  let n := K * M
  let Δbase := aBase * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))
  let atomRows := cmax * (aRows * Real.exp (-Real.rpow S.L (1 / 10 : ℝ)))
  let atomTarget := aOut * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))
  have hLpos : 0 < S.L := by
    dsimp [PDScale.L]
    exact Real.log_pos (by linarith [hS.1])
  have hΔbase : 0 ≤ Δbase := by dsimp [Δbase]; positivity
  have hAtomRows : 0 ≤ atomRows := by dsimp [atomRows]; positivity
  have hAtomTarget : 0 ≤ atomTarget := by dsimp [atomTarget]; positivity
  have haRowsBase : aRows ≤ aBase := le_max_left _ _
  have hAtomRowsLe : atomRows ≤ atomTarget := by
    dsimp [atomRows, atomTarget, aOut]
    calc
      cmax * (aRows * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))) =
          (cmax * aRows) * Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) := by ring
      _ ≤ (cmax * aBase) * Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left haRowsBase (le_trans (by norm_num) hCmax))
          (Real.exp_nonneg _)
      _ = cmax * aBase * Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) := by ring
  have hDeltaLeTarget : Δbase ≤ atomTarget := by
    dsimp [Δbase, atomTarget, aOut]
    calc
      aBase * Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) =
          1 * (aBase * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))) := by ring
      _ ≤ cmax * (aBase * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))) :=
        mul_le_mul_of_nonneg_right hCmax
          (mul_nonneg (le_of_lt haBase) (Real.exp_nonneg _))
      _ = cmax * aBase * Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) := by ring
  let edgeAbs := pd5_edgeRowFactor F S Cedge
  have hedgeAbsNonneg : 0 ≤ edgeAbs := by
    dsimp [edgeAbs, pd5_edgeRowFactor]
    positivity
  have hEdgeBase : edgeAbs ≤
      edgeInflation * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow S.L (3 * F.A₀) := by
    have hBaseEq : edgeAbs =
        (2 * (Fintype.card (Finset (Fin K)) : ℝ) ^ 2 * Cedge) *
          ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow S.L (3 * F.A₀) := by
      dsimp [edgeAbs, pd5_edgeRowFactor, B]
    have hq : 0 ≤ 2 * (Fintype.card (Finset (Fin K)) : ℝ) ^ 2 := by positivity
    have hpow : 0 ≤ ((B + 1 : ℕ) : ℝ) ^ K := by positivity
    have hrpow : 0 ≤ Real.rpow S.L (3 * F.A₀) := Real.rpow_nonneg hLpos.le _
    rw [hBaseEq]
    calc
      _ = (2 * (Fintype.card (Finset (Fin K)) : ℝ) ^ 2 * Cedge) *
          (((B + 1 : ℕ) : ℝ) ^ K * Real.rpow S.L (3 * F.A₀)) := by ring
      _ ≤ edgeInflation *
          (((B + 1 : ℕ) : ℝ) ^ K * Real.rpow S.L (3 * F.A₀)) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hpow hrpow)
            dsimp [edgeInflation]
            nlinarith [hCedge, hq]
      _ = _ := by ring
  have hBAbsorb : ((B + 1 : ℕ) : ℝ) ≤ 3 * S.L ^ 2 := by
    calc
      _ = (B : ℝ) + 1 := by norm_num
      _ ≤ 2 * S.L ^ 2 + 1 := by simpa [add_comm] using add_le_add_right hBupper 1
      _ ≤ 3 * S.L ^ 2 := by nlinarith [hL1]
  have hCghostL : Cghost ≤ S.L := by
    have hT : Cghost ≤ thresholdL := le_max_left _ _
    have hxExp : Real.exp thresholdL ≤ S.x := by
      have hx0exp : Real.exp thresholdL ≤ x₀ := le_trans
        (le_max_right xScale (Real.exp thresholdL))
        (le_max_right xRows (max xScale (Real.exp thresholdL)))
      exact hx0exp.trans hx₀S
    have hlog : thresholdL ≤ S.L := by
      have h := Real.log_le_log (Real.exp_pos thresholdL) hxExp
      simpa [PDScale.L] using h
    exact hT.trans hlog
  have hEdgeLarge : edgeInflation * (3 : ℝ) ^ K ≤ S.L := by
    have hT : edgeInflation * (3 : ℝ) ^ K ≤ thresholdL := le_trans
      (le_max_right 2 _) (le_max_right Cghost _)
    have hxExp : Real.exp thresholdL ≤ S.x := by
      have hx0exp : Real.exp thresholdL ≤ x₀ := le_trans
        (le_max_right xScale (Real.exp thresholdL))
        (le_max_right xRows (max xScale (Real.exp thresholdL)))
      exact hx0exp.trans hx₀S
    have hlog : thresholdL ≤ S.L := by
      have h := Real.log_le_log (Real.exp_pos thresholdL) hxExp
      simpa [PDScale.L] using h
    exact hT.trans hlog
  let e : Fin K × Fin M ≃ Fin n := finProdFinEquiv
  let coord : Fin n → Fin K × Fin M := fun q => e.symm q
  let P : Fin n → Finset ℕ := fun q => primeBand S.x (F.a (coord q).1)
  let nu : Fin n → ℕ → ℝ := fun q p =>
    memoryNu S.x K F.a F.q_d (coord q).1 p
  let Choice := (q : Fin n) → {p : ℕ // p ∈ P q}
  let Active := (i : Fin K) → Fin M → {p : ℕ // p ∈ primeBand S.x (F.a i)}
  letI : Fintype Choice := inferInstance
  letI : Fintype Active := inferInstance
  let choiceEquiv : Active ≃ Choice := {
    toFun := fun l q =>
      ⟨(l (coord q).1 (coord q).2).val, by
        simpa [P] using (l (coord q).1 (coord q).2).property⟩
    invFun := fun b i j =>
      ⟨(b (e (i, j))).val, by
        have hcoord : coord (e (i, j)) = (i, j) := by
          dsimp [coord]
          exact Equiv.symm_apply_apply e (i, j)
        simpa [P, hcoord] using (b (e (i, j))).property⟩
    left_inv := by
      intro l
      funext i
      funext j
      apply Subtype.ext
      have hcoord : coord (e (i, j)) = (i, j) := by
        dsimp [coord]
        exact Equiv.symm_apply_apply e (i, j)
      change (l (coord (e (i, j))).1 (coord (e (i, j))).2).val = (l i j).val
      rw [hcoord]
    right_inv := by
      intro b
      funext q
      apply Subtype.ext
      have hcoord : e (coord q) = q := by
        dsimp [coord]
        exact Equiv.apply_symm_apply e q
      change (b (e (coord q))).val = (b q).val
      rw [hcoord]
  }
  let stateOf : Active → MemPoint S.x K := fun l =>
    ((1, 0), (fun i j => (l i j : ℕ)), fun _ => ([] : List Particle))
  let addr : Fin n → BirthAddress K := fun q =>
    BirthAddress.initial (coord q).1 (coord q).2.val
  let hSys : IsConstraintSystem (birthAddresses S.x K B) C :=
    (Finset.mem_filter.mp hC).2
  let Rinit := pd5_layerNonpivots S B hSys pd5_isInitial
  let Rfin := (Finset.univ : Finset (Fin n)).filter fun q => addr q ∈ Rinit
  have haddrInj : Function.Injective addr := by
    intro q q' hq
    have hi : (coord q).1.val = (coord q').1.val := by
      simpa [addr, pd5_birthGroup] using congrArg pd5_birthGroup hq
    have hj : (coord q).2.val = (coord q').2.val := by
      simpa [addr, pd5_birthOffset] using congrArg pd5_birthOffset hq
    have hcoord : coord q = coord q' := by
      apply Prod.ext
      · exact Fin.ext hi
      · exact Fin.ext hj
    exact e.symm.injective hcoord
  have hRinitSupport : Rinit ⊆ C.biUnion id := by
    intro a ha
    have hLayer : a ∈ pd5_layerAddresses C pd5_isInitial :=
      (Finset.mem_filter.mp ha).1
    exact (Finset.mem_filter.mp hLayer).1
  have hRinitBirth : Rinit ⊆ birthAddresses S.x K B :=
    fun a ha => pd5_constraint_support_subset hC (hRinitSupport ha)
  have hRcard : Rfin.card = Rinit.card := by
    have hImage : Rfin.image addr = Rinit := by
      ext a
      constructor
      · intro ha
        rcases Finset.mem_image.mp ha with ⟨q, hq, rfl⟩
        exact (Finset.mem_filter.mp hq).2
      · intro ha
        have haBirth := hRinitBirth ha
        cases a with
        | initial i j =>
            have hj : j < M := by simpa [birthAddresses, M] using haBirth
            let q := e (i, ⟨j, hj⟩)
            have hcoord : coord q = (i, ⟨j, hj⟩) := by simp [q, coord, e]
            refine Finset.mem_image.mpr ⟨q,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · simpa [addr, hcoord] using ha
            · simp [addr, hcoord]
        | ghost j i k =>
            simp [Rinit, pd5_layerNonpivots, pd5_layerAddresses,
              pd5_isInitial] at ha
        | edge j i =>
            simp [Rinit, pd5_layerNonpivots, pd5_layerAddresses,
              pd5_isInitial] at ha
    calc
      Rfin.card = (Rfin.image addr).card :=
        (Finset.card_image_of_injective Rfin haddrInj).symm
      _ = Rinit.card := congrArg Finset.card hImage
  let initLogOf : Active → BirthLog K := fun l => initialLog (stateOf l)
  let boundaryPoint : Active → LogPoint S.x K := fun l => (stateOf l, initLogOf l)
  let boundarySupport : Finset (LogPoint S.x K) :=
    (Finset.univ : Finset Active).image boundaryPoint
  have hboundaryPointInj : Function.Injective boundaryPoint := by
    intro l l' h
    have hs : stateOf l = stateOf l' := congrArg Prod.fst h
    have hLists : (fun i j => (l i j : ℕ)) = fun i j => (l' i j : ℕ) :=
      congrArg (fun s : MemPoint S.x K => s.2.1) hs
    funext i
    funext j
    apply Subtype.ext
    exact congrFun (congrFun hLists i) j
  have hboundaryPointInjOn : Set.InjOn boundaryPoint
      (↑(Finset.univ : Finset Active)) := by
    intro l hl l' hl' heq
    exact hboundaryPointInj heq
  have hValidState : ∀ l : Active, MemValid F S (stateOf l) := by
    intro l
    constructor
    · norm_num [stateOf]
    constructor
    · intro i j
      exact (l i j).property
    · intro i p hp
      simp [stateOf] at hp
  have hStateRegion : ∀ l : Active,
      pd5_stateRegion F S w B (stateOf l) := by
    intro l
    refine ⟨hValidState l, ?_, Or.inl rfl⟩
    simp [memSize, stateOf, B]
  have hInitLogGood : ∀ l : Active,
      pd5_logPrefixGood S.x B 0 0 (initLogOf l) := by
    intro l
    simpa [initLogOf] using pd5_initialLog_prefixGood (B := B) (stateOf l)
  have hNuNonneg : ∀ q p, p ∈ P q → 0 ≤ nu q p := by
    intro q p hp
    exact ((hBands (coord q).1).2.2.2 p (by simpa [P] using hp)).1
  have hNuSum : ∀ q, (∑ p ∈ P q, nu q p) ≤ 2 := by
    intro q
    simpa [P, nu] using (hBands (coord q).1).2.2.1
  have hNuSmall : ∀ q p, p ∈ P q →
      nu q p ≤ (4 / Real.log 2) * Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) := by
    intro q p hp
    exact ((hBands (coord q).1).2.2.2 p (by simpa [P] using hp)).2
  have hFourLe : 4 / Real.log 2 ≤ aBase := le_max_right _ _
  have hNuBase : ∀ q p, p ∈ P q → nu q p ≤ Δbase := by
    intro q p hp
    calc
      nu q p ≤ (4 / Real.log 2) * Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) := hNuSmall q p hp
      _ ≤ Δbase := by
        dsimp [Δbase]
        exact mul_le_mul_of_nonneg_right hFourLe (Real.exp_nonneg _)
  let pick : (q : Fin n) → (Fin q.val → ℕ) → ℕ := fun q prev =>
    match pd5_addressPivot S B hSys (addr q) with
    | .initial i j =>
        if hj : j < M then
          let q₀ := e (i, ⟨j, hj⟩)
          if hq : q₀ < q then
            prev ⟨q₀.val, Fin.lt_iff_val_lt_val.mp hq⟩ else 0
        else 0
    | .ghost _ _ _ => 0
    | .edge _ _ => 0
  let prevValues : Choice → (q : Fin n) → Fin q.val → ℕ := fun b q r =>
    (b ⟨r.val, r.isLt.trans q.isLt⟩).val
  let triCond : Choice → Prop := fun b =>
    ∀ q ∈ Rfin, (b q).val = pick q (prevValues b q)
  have hPrefixTri : ∀ b : Choice,
      pd5_prefixConstraintOK C 1 (initialLog (stateOf (choiceEquiv.symm b))) →
      triCond b := by
    intro b hPrefix q hqR
    let s := stateOf (choiceEquiv.symm b)
    let a := addr q
    have hAddrR : a ∈ Rinit := (Finset.mem_filter.mp hqR).2
    have hSupport : a ∈ C.biUnion id := hRinitSupport hAddrR
    have hAddrBirth : a ∈ birthAddresses S.x K B := hRinitBirth hAddrR
    have hPivotStrict : pd5_birthIndex S B
        (pd5_addressPivot S B hSys a) < pd5_birthIndex S B a :=
      pd5_layerNonpivot_strict S B hC (fun _ ha => ha) pd5_isInitial hAddrR
    let D := pd5_addressBlock C a hSupport
    have hD := pd5_addressBlock_spec C a hSupport
    have hPivotSpec := pd5_addressPivot_spec S B hSys a hSupport
    have hPivotInSupport : pd5_addressPivot S B hSys a ∈ C.biUnion id :=
      Finset.mem_biUnion.mpr ⟨D, hD.1, hPivotSpec.1⟩
    have hPivotBirth : pd5_addressPivot S B hSys a ∈ birthAddresses S.x K B :=
      pd5_constraint_support_subset hC hPivotInSupport
    have hPivotInitial : ∃ i₀ j₀,
        pd5_addressPivot S B hSys a = BirthAddress.initial i₀ j₀ := by
      cases hp : pd5_addressPivot S B hSys a with
      | initial i₀ j₀ => exact ⟨i₀, j₀, rfl⟩
      | ghost j₀ i₀ k₀ =>
          have hPivotBirth' : BirthAddress.ghost j₀ i₀ k₀ ∈ birthAddresses S.x K B := by
            simpa [hp] using hPivotBirth
          have hLayer : pd5_birthLayer a < pd5_birthLayer (.ghost j₀ i₀ k₀) := by
            simp [a, addr, pd5_birthLayer]
          have hBack := pd5_birthIndex_lt_of_layer_lt S B hAddrBirth hPivotBirth' hLayer
          have hStrict' : pd5_birthIndex S B (.ghost j₀ i₀ k₀) <
              pd5_birthIndex S B a := by simpa [hp] using hPivotStrict
          omega
      | edge j₀ i₀ =>
          have hPivotBirth' : BirthAddress.edge j₀ i₀ ∈ birthAddresses S.x K B := by
            simpa [hp] using hPivotBirth
          have hLayer : pd5_birthLayer a < pd5_birthLayer (.edge j₀ i₀) := by
            simp [a, addr, pd5_birthLayer]
          have hBack := pd5_birthIndex_lt_of_layer_lt S B hAddrBirth hPivotBirth' hLayer
          have hStrict' : pd5_birthIndex S B (.edge j₀ i₀) <
              pd5_birthIndex S B a := by simpa [hp] using hPivotStrict
          omega
    rcases hPivotInitial with ⟨i₀, j₀, hpivot⟩
    have hj₀ : j₀ < M := by
      have hPivotBirth' : BirthAddress.initial i₀ j₀ ∈ birthAddresses S.x K B := by
        simpa [hpivot] using hPivotBirth
      simpa [birthAddresses, M] using hPivotBirth'
    let j₀f : Fin M := ⟨j₀, hj₀⟩
    let q₀ : Fin n := e (i₀, j₀f)
    have hInitialOrder :
        pd5_birthIndex S B (.initial i₀ j₀) <
          pd5_birthIndex S B (.initial (coord q).1 (coord q).2.val) := by
      simpa [hpivot, a, addr] using hPivotStrict
    have hser := pd5_initial_serial_lt_of_birthIndex_lt S B i₀ (coord q).1 j₀f
      (coord q).2 hInitialOrder
    have hq₀val : q₀.val < q.val := by
      have hser' : q₀.val < q.val % M + M * (q.val / M) := by
        simpa [q₀, j₀f, coord, e, finProdFinEquiv, M] using hser
      exact lt_of_lt_of_eq hser' (Nat.mod_add_div _ _)
    have hq₀ : q₀ < q := Fin.lt_iff_val_lt_val.mpr hq₀val
    obtain ⟨p, hp⟩ := hPrefix D hD.1
    have hCurrPair : (a, p) ∈ initialLog s := by
      apply hp a hD.2
      simp [a, addr, pd5_birthLayer]
    have hPivotPair : (BirthAddress.initial i₀ j₀, p) ∈ initialLog s := by
      have hpair := hp (pd5_addressPivot S B hSys a) hPivotSpec.1 (by
        simp [hpivot, pd5_birthLayer])
      simpa [hpivot] using hpair
    have hCurrentEntry := pd5_initialLog_entry s (coord q).1 (coord q).2
    have hCurrentEntry' : (a, s.2.1 (coord q).1 (coord q).2) ∈ initialLog s := by
      simpa [a, addr] using hCurrentEntry
    have hPivotEntry := pd5_initialLog_entry s i₀ j₀f
    have hPivotEntry' :
        (BirthAddress.initial i₀ j₀, s.2.1 i₀ j₀f) ∈ initialLog s := by
      simpa [j₀f] using hPivotEntry
    have hNodup := pd5_initialLog_addresses_nodup s
    have hCurrentValue : p = (b q).val := by
      have hpair := List.inj_on_of_nodup_map (f := Prod.fst) hNodup
        hCurrPair hCurrentEntry' rfl
      have hsnd := congrArg Prod.snd hpair
      have hcoordq : e (coord q) = q := by
        dsimp [coord]
        exact Equiv.apply_symm_apply e q
      have hvalue : s.2.1 (coord q).1 (coord q).2 = (b q).val := by
        change (b (e (coord q))).val = (b q).val
        rw [hcoordq]
      simpa [hvalue] using hsnd
    have hPivotValue : p = (b q₀).val := by
      have hpair := List.inj_on_of_nodup_map (f := Prod.fst) hNodup
        hPivotPair hPivotEntry' rfl
      have hsnd := congrArg Prod.snd hpair
      have hvalue : s.2.1 i₀ j₀f = (b q₀).val := by
        change (b (e (i₀, j₀f))).val = (b q₀).val
        rfl
      simpa [hvalue] using hsnd
    have hPick : pick q (prevValues b q) = (b q₀).val := by
      have hpivot' : pd5_addressPivot S B hSys (addr q) =
          BirthAddress.initial i₀ j₀ := by simpa [a] using hpivot
      simp [pick, prevValues, addr, q₀, j₀f, hpivot', hq₀, hj₀]
    calc
      (b q).val = p := hCurrentValue.symm
      _ = (b q₀).val := hPivotValue
      _ = pick q (prevValues b q) := hPick.symm
  let nuProd : Choice → ℝ := fun b => ∏ q : Fin n, nu q (b q).val
  let weight : LogPoint S.x K → ℂ := fun σL =>
    (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)
  have hMeasureActive (l : Active) :
      memMeasure F S (stateOf l) = nuProd (choiceEquiv l) := by
    have hmem : memMeasure F S (stateOf l) =
        ∏ i : Fin K, ∏ j : Fin M,
          memoryNu S.x K F.a F.q_d i (l i j).val := by
      simp [memMeasure, stateOf, hValidState l] <;> rfl
    have hpair :
        (∏ i : Fin K, ∏ j : Fin M,
          memoryNu S.x K F.a F.q_d i (l i j).val) =
          ∏ ij : Fin K × Fin M,
            memoryNu S.x K F.a F.q_d ij.1 (l ij.1 ij.2).val := by
      exact (Fintype.prod_prod_type'
        (fun i j => memoryNu S.x K F.a F.q_d i (l i j).val)).symm
    have hequiv :
        (∏ ij : Fin K × Fin M,
            memoryNu S.x K F.a F.q_d ij.1 (l ij.1 ij.2).val) =
          ∏ q : Fin n, nu q (choiceEquiv l q).val := by
      exact Fintype.prod_equiv e _ _ (by
        intro ij
        change memoryNu S.x K F.a F.q_d ij.1 (l ij.1 ij.2).val =
          memoryNu S.x K F.a F.q_d (coord (e ij)).1
            (l (coord (e ij)).1 (coord (e ij)).2).val
        have hcoord : coord (e ij) = ij := by
          dsimp [coord]
          exact Equiv.symm_apply_apply e ij
        rw [hcoord])
    calc
      _ = ∏ i : Fin K, ∏ j : Fin M,
          memoryNu S.x K F.a F.q_d i (l i j).val := hmem
      _ = ∏ ij : Fin K × Fin M,
          memoryNu S.x K F.a F.q_d ij.1 (l ij.1 ij.2).val := hpair
      _ = nuProd (choiceEquiv l) := by simpa [nuProd] using hequiv
  have hBoundaryLog (l : Active) : logBoundaryIn (boundaryPoint l) = 1 := by
    simp [boundaryPoint, initLogOf, logBoundaryIn, memBoundary, stateOf]
  have hWeightActive (l : Active) :
      weight (boundaryPoint l) = (nuProd (choiceEquiv l) : ℂ) := by
    simp [weight, boundaryPoint, hMeasureActive l, hBoundaryLog l]
  have hWeightSupport :
      {σL : LogPoint S.x K | weight σL ≠ 0}.Finite := by
    simpa [weight] using pd5_logBoundaryIn_weight_support_finite F S
  have hWeightSupportSubset : ∀ σL, weight σL ≠ 0 → σL ∈ boundarySupport := by
    intro σL hW
    rcases σL with ⟨s, L⟩
    have hmuC : (memMeasure F S s : ℂ) ≠ 0 := by
      intro hzero
      apply hW
      simp [weight, hzero]
    have hmu : memMeasure F S s ≠ 0 := by exact_mod_cast hmuC
    have hbin : logBoundaryIn (s, L) ≠ 0 := by
      intro hzero
      apply hW
      simp [weight, hzero]
    have hvalid : MemValid F S s := by
      by_contra hnot
      apply hmu
      simp [memMeasure, hnot]
    have hlog : L = initialLog s := by
      by_cases heq : L = initialLog s
      · exact heq
      · have hz : logBoundaryIn (s, L) = 0 := by simp [logBoundaryIn, heq]
        exact (hbin hz).elim
    have hmemBoundary : memBoundary s ≠ 0 := by
      simpa [logBoundaryIn, hlog] using hbin
    have hs : s.1 = (1, 0) ∧ ∀ i, s.2.2 i = [] := by
      unfold memBoundary at hmemBoundary
      by_cases h : s.1 = (1, 0) ∧ ∀ i, s.2.2 i = []
      · exact h
      · simp [h] at hmemBoundary
    let l : Active := fun i j => ⟨s.2.1 i j, hvalid.2.1 i j⟩
    have hstate : stateOf l = s := by
      apply Prod.ext
      · exact hs.1.symm
      · apply Prod.ext
        · funext i j
          rfl
        · funext i
          exact (hs.2 i).symm
    have hL : L = initLogOf l := by
      simpa [initLogOf, hstate] using hlog
    have hpoint : boundaryPoint l = (s, L) := by
      apply Prod.ext
      · exact hstate
      · exact hL.symm
    exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, hpoint⟩
  have hZeroOutside : ∀ σL, σL ∉ boundarySupport →
      weight σL * logHistoryFn F S ρ w (some B) none
        (constraintWeight C) S.N σL = 0 := by
    intro σL hnot
    by_cases hW : weight σL = 0
    · simp [hW]
    · exact False.elim (hnot (hWeightSupportSubset σL hW))
  have hMemHistorySum :
      memHistory F S ρ w (some B) none (constraintWeight C) =
        ∑ l : Active, (nuProd (choiceEquiv l) : ℂ) *
          logHistoryFn F S ρ w (some B) none (constraintWeight C) S.N
            (boundaryPoint l) := by
    unfold memHistory logInner
    calc
      _ = ∑ σL ∈ boundarySupport,
          weight σL * logHistoryFn F S ρ w (some B) none
            (constraintWeight C) S.N σL :=
        tsum_eq_sum (L := SummationFilter.unconditional (LogPoint S.x K))
          (s := boundarySupport) hZeroOutside
      _ = ∑ l : Active, weight (boundaryPoint l) *
          logHistoryFn F S ρ w (some B) none (constraintWeight C) S.N
            (boundaryPoint l) := by
        dsimp [boundarySupport]
        rw [Finset.sum_image hboundaryPointInjOn]
      _ = _ := by simp_rw [hWeightActive]
  let H := Cghost ^ (S.N + 1) * edgeAbs ^ S.N *
    atomRows ^ pd5_futureRank S B C 1
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hCghost.le _) (pow_nonneg hedgeAbsNonneg _))
      (pow_nonneg hAtomRows _)
  have hInd := pd5_logHistoryFn_uniform_bound δ c₁ c₂ F ρ
    v Cghost Cedge cmax aRows xRows hV hCghost hCedge hCmax hRowsAtom hRows
    S hS hxRowsS w hw C hC
  have hHistoryLeH : ∀ l : Active,
      ‖logHistoryFn F S ρ w (some B) none (constraintWeight C) S.N
        (boundaryPoint l)‖ ≤ H := by
    intro l
    by_cases hgood : pd5_prefixConstraintOK C 1 (initLogOf l)
    · have h := hInd S.N (by omega) (boundaryPoint l) (hStateRegion l)
        (by simpa [boundaryPoint, initLogOf] using hInitLogGood l)
        (by simpa using hgood)
      simpa [H, edgeAbs, atomRows, pd5_fixedAtom, B, boundaryPoint,
        memSize, stateOf] using h
    · have hbad : ¬ pd5_prefixConstraintOK C
          (2 * (S.N - S.N) + 1) (boundaryPoint l).2 := by
        simpa [boundaryPoint, initLogOf] using hgood
      have hzero := pd5_logHistoryFn_zero_of_bad_prefix F S ρ w B C S.N
        (by omega) (boundaryPoint l) hbad
      rw [hzero]
      simpa using hHnonneg
  have hHistoryTri : ∀ l : Active,
      ‖logHistoryFn F S ρ w (some B) none (constraintWeight C) S.N
        (boundaryPoint l)‖ ≤
        H * (if triCond (choiceEquiv l) then 1 else 0) := by
    intro l
    by_cases htri : triCond (choiceEquiv l)
    · simpa [htri] using hHistoryLeH l
    · have hgoodFalse : ¬ pd5_prefixConstraintOK C 1 (initLogOf l) := by
        intro hgood
        have hgood' : pd5_prefixConstraintOK C 1
            (initialLog (stateOf (choiceEquiv.symm (choiceEquiv l)))) := by
          simpa [initLogOf] using hgood
        exact htri (hPrefixTri (choiceEquiv l) hgood')
      have hzero := pd5_logHistoryFn_zero_of_bad_prefix F S ρ w B C S.N
        (by omega) (boundaryPoint l)
        (by simpa [boundaryPoint, initLogOf] using hgoodFalse)
      simp [htri, hzero]
  have hNuProdNonneg : ∀ b : Choice, 0 ≤ nuProd b := by
    intro b
    apply Finset.prod_nonneg
    intro q hq
    exact hNuNonneg q (b q).val (b q).property
  have hWeightedTerm : ∀ l : Active,
      nuProd (choiceEquiv l) *
          ‖logHistoryFn F S ρ w (some B) none (constraintWeight C) S.N
            (boundaryPoint l)‖ ≤
        H * (if triCond (choiceEquiv l) then nuProd (choiceEquiv l) else 0) := by
    intro l
    have hμ := hNuProdNonneg (choiceEquiv l)
    by_cases htri : triCond (choiceEquiv l)
    · have hhist := hHistoryTri l
      simp [htri] at hhist
      calc
        _ ≤ nuProd (choiceEquiv l) * H :=
          mul_le_mul_of_nonneg_left hhist hμ
        _ = H * nuProd (choiceEquiv l) := by ring
        _ = H * (if triCond (choiceEquiv l) then nuProd (choiceEquiv l) else 0) := by
          simp [htri]
    · have hhist := hHistoryTri l
      have hnormzero :
          ‖logHistoryFn F S ρ w (some B) none (constraintWeight C) S.N
            (boundaryPoint l)‖ = 0 := by
        apply le_antisymm
        · simpa [htri] using hhist
        · exact norm_nonneg _
      simp [htri, hnormzero]
  have hNormInitialTri :
      ‖memHistory F S ρ w (some B) none (constraintWeight C)‖ ≤
        H * ∑ l : Active,
          if triCond (choiceEquiv l) then nuProd (choiceEquiv l) else 0 := by
    rw [hMemHistorySum]
    calc
      _ ≤ ∑ l : Active,
          ‖(nuProd (choiceEquiv l) : ℂ) *
            logHistoryFn F S ρ w (some B) none (constraintWeight C) S.N
              (boundaryPoint l)‖ := norm_sum_le _ _
      _ = ∑ l : Active,
          nuProd (choiceEquiv l) *
            ‖logHistoryFn F S ρ w (some B) none (constraintWeight C) S.N
              (boundaryPoint l)‖ := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [norm_mul]
            simp [Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (hNuProdNonneg (choiceEquiv l))]
      _ ≤ ∑ l : Active,
          H * (if triCond (choiceEquiv l) then nuProd (choiceEquiv l) else 0) :=
            Finset.sum_le_sum (by intro l hl; exact hWeightedTerm l)
      _ = H * ∑ l : Active,
          if triCond (choiceEquiv l) then nuProd (choiceEquiv l) else 0 := by
            rw [Finset.mul_sum]
  have hTriSumEquiv :
      (∑ l : Active,
        if triCond (choiceEquiv l) then nuProd (choiceEquiv l) else 0) =
        ∑ b : Choice, if triCond b then nuProd b else 0 := by
    apply Fintype.sum_equiv choiceEquiv
    intro l
    rfl
  have hTriangular := pd5_triangular_birth_sum_le n P nu Rfin Δbase hΔbase pick
    hNuNonneg (by intro q hq p hp; exact hNuBase q p hp)
  have hProductRows :
      (∏ q : Fin n, if q ∈ Rfin then Δbase else ∑ p ∈ P q, nu q p) ≤
        ∏ q : Fin n, if q ∈ Rfin then (2 : ℝ) * Δbase else 2 := by
    apply Finset.prod_le_prod₀
    · intro q hq
      by_cases hqR : q ∈ Rfin
      · simp [hqR, hΔbase]
      · simp [hqR]
        exact Finset.sum_nonneg (fun p hp => hNuNonneg q p hp)
    · intro q hq
      by_cases hqR : q ∈ Rfin
      · simp [hqR]
        nlinarith [hΔbase]
      · simp [hqR]
        exact hNuSum q
  have hProductExact :
      (∏ q : Fin n, if q ∈ Rfin then (2 : ℝ) * Δbase else 2) =
        (2 : ℝ) ^ n * Δbase ^ Rfin.card := by
    have hFilteredProd :
        (∏ q : Fin n, if q ∈ Rfin then Δbase else 1) = Δbase ^ Rfin.card := by
      rw [← Finset.prod_filter]
      simp
    calc
      _ = ∏ q : Fin n, (2 : ℝ) *
          (if q ∈ Rfin then Δbase else 1) := by
            apply Finset.prod_congr rfl
            intro q hq
            by_cases hqR : q ∈ Rfin <;> simp [hqR] <;> ring
      _ = (∏ q : Fin n, (2 : ℝ)) *
          ∏ q : Fin n, (if q ∈ Rfin then Δbase else 1) := Finset.prod_mul_distrib
      _ = _ := by simp [hFilteredProd]
  have hTriSum :
      (∑ b : Choice, if triCond b then nuProd b else 0) ≤
        (2 : ℝ) ^ n * Δbase ^ Rfin.card := by
    calc
      _ ≤ ∏ q : Fin n, if q ∈ Rfin then Δbase else ∑ p ∈ P q, nu q p := by
        simpa [triCond, prevValues, nuProd] using hTriangular
      _ ≤ ∏ q : Fin n, if q ∈ Rfin then (2 : ℝ) * Δbase else 2 := hProductRows
      _ = (2 : ℝ) ^ n * Δbase ^ Rfin.card := hProductExact
  have hTriInitialNorm :
      ‖memHistory F S ρ w (some B) none (constraintWeight C)‖ ≤
        H * ((2 : ℝ) ^ n * Δbase ^ Rfin.card) := by
    have hTriSumActive :
        (∑ l : Active,
          if triCond (choiceEquiv l) then nuProd (choiceEquiv l) else 0) ≤
        (2 : ℝ) ^ n * Δbase ^ Rfin.card := by
      rw [hTriSumEquiv]
      exact hTriSum
    exact le_trans hNormInitialTri
      (mul_le_mul_of_nonneg_left hTriSumActive hHnonneg)
  have hRankInit := pd5_constraintRank_initial_future S B hC
  have hRankExp : pd5_futureRank S B C 1 + Rfin.card = constraintRank C := by
    rw [hRcard, Nat.add_comm]
    exact hRankInit.symm
  have hAtomPowers :
      atomRows ^ pd5_futureRank S B C 1 * Δbase ^ Rfin.card ≤
        atomTarget ^ constraintRank C := by
    calc
      _ ≤ atomTarget ^ pd5_futureRank S B C 1 * atomTarget ^ Rfin.card :=
        mul_le_mul
          (pow_le_pow_left₀ hAtomRows hAtomRowsLe _)
          (pow_le_pow_left₀ hΔbase hDeltaLeTarget _)
          (pow_nonneg hΔbase _) (pow_nonneg hAtomTarget _)
      _ = atomTarget ^ (pd5_futureRank S B C 1 + Rfin.card) :=
        (pow_add atomTarget _ _).symm
      _ = atomTarget ^ constraintRank C := by rw [hRankExp]
  have hFrontNonneg :
      0 ≤ (2 : ℝ) ^ n * Cghost ^ (S.N + 1) * edgeAbs ^ S.N := by
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hCghost.le _))
      (pow_nonneg hedgeAbsNonneg _)
  have hFixedBase :
      ‖memHistory F S ρ w (some B) none (constraintWeight C)‖ ≤
        (2 : ℝ) ^ n * Cghost ^ (S.N + 1) * edgeAbs ^ S.N *
          atomTarget ^ constraintRank C := by
    calc
      _ ≤ H * ((2 : ℝ) ^ n * Δbase ^ Rfin.card) := hTriInitialNorm
      _ = ((2 : ℝ) ^ n * Cghost ^ (S.N + 1) * edgeAbs ^ S.N) *
          (atomRows ^ pd5_futureRank S B C 1 * Δbase ^ Rfin.card) := by
            dsimp [H]
            ring
      _ ≤ ((2 : ℝ) ^ n * Cghost ^ (S.N + 1) * edgeAbs ^ S.N) *
          atomTarget ^ constraintRank C :=
            mul_le_mul_of_nonneg_left hAtomPowers hFrontNonneg
      _ = _ := by ring
  have hL2 : 2 ≤ S.L := by
    have hT2 : 2 ≤ thresholdL :=
      le_trans (le_max_left 2 (edgeInflation * (3 : ℝ) ^ K))
        (le_max_right Cghost _)
    have hx0exp : Real.exp thresholdL ≤ x₀ := le_trans
      (le_max_right xScale (Real.exp thresholdL))
      (le_max_right xRows (max xScale (Real.exp thresholdL)))
    have hxExp : Real.exp thresholdL ≤ S.x := hx0exp.trans hx₀S
    have hlog : thresholdL ≤ S.L := by
      have h := Real.log_le_log (Real.exp_pos thresholdL) hxExp
      simpa [PDScale.L] using h
    exact hT2.trans hlog
  have hA₀ : 0 ≤ F.A₀ := le_of_lt hF.2.2.2.1
  have hAbsorb := pd5_absorb_fixed_factors K M S.N B F.A₀ Cghost edgeInflation S.L
    hA₀ hL2 hMN hBAbsorb hCghost hCghostL hEdgeInflation hEdgeLarge
  have hEdgePow : edgeAbs ^ S.N ≤
      (edgeInflation * ((B + 1 : ℕ) : ℝ) ^ K *
        Real.rpow S.L (3 * F.A₀)) ^ S.N :=
    pow_le_pow_left₀ hedgeAbsNonneg hEdgeBase _
  have hBeforeAbsorb :
      (2 : ℝ) ^ n * Cghost ^ (S.N + 1) * edgeAbs ^ S.N ≤
        (2 : ℝ) ^ (K * M) * Cghost ^ (S.N + 1) *
          (edgeInflation * ((B + 1 : ℕ) : ℝ) ^ K *
            Real.rpow S.L (3 * F.A₀)) ^ S.N := by
    calc
      _ ≤ (2 : ℝ) ^ n * Cghost ^ (S.N + 1) *
          (edgeInflation * ((B + 1 : ℕ) : ℝ) ^ K *
            Real.rpow S.L (3 * F.A₀)) ^ S.N := by
              exact mul_le_mul_of_nonneg_left hEdgePow
                (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hCghost.le _))
      _ = _ := by simp [n]
  calc
    _ ≤ (2 : ℝ) ^ n * Cghost ^ (S.N + 1) * edgeAbs ^ S.N *
        atomTarget ^ constraintRank C := hFixedBase
    _ ≤ (2 : ℝ) ^ (K * M) * Cghost ^ (S.N + 1) *
        (edgeInflation * ((B + 1 : ℕ) : ℝ) ^ K *
          Real.rpow S.L (3 * F.A₀)) ^ S.N *
        atomTarget ^ constraintRank C := by
          exact mul_le_mul_of_nonneg_right hBeforeAbsorb
            (pow_nonneg hAtomTarget _)
    _ ≤ Real.rpow S.L (Cabs * ((S.N : ℝ) + 1)) *
        atomTarget ^ constraintRank C := by
          have hAbsorb' := hAbsorb
          simpa [Cabs] using
            (mul_le_mul_of_nonneg_right hAbsorb' (pow_nonneg hAtomTarget _))
    _ = Real.rpow S.L (Cabs * ((S.N : ℝ) + 1)) *
        (aOut * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))) ^ constraintRank C := by
          simp [atomTarget]

end
end ArtinPrimitiveRoots.TypeII.PD
