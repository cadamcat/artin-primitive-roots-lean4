import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

private theorem mem_constraintSystems_iff {K : ℕ} (A : Finset (BirthAddress K))
    (C : Finset (Finset (BirthAddress K))) :
    C ∈ constraintSystems A ↔ IsConstraintSystem A C := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      intro D hD
      apply Finset.mem_powerset.mpr
      exact (h.1 D hD).1
    · exact h

private abbrev PD5System {K : ℕ} (A : Finset (BirthAddress K)) :=
  {C : Finset (Finset (BirthAddress K)) // C ∈ constraintSystems A}

private theorem pd5_system_val_cast {K : ℕ} {A B : Finset (BirthAddress K)}
    (h : A = B) (C : PD5System A) :
    (cast (congrArg PD5System h) C).1 = C.1 := by
  cases h
  rfl

private abbrev pd5_blocks {K : ℕ} (A : Finset (BirthAddress K)) (a : BirthAddress K) :=
  A.powerset.filter fun D => a ∈ D ∧ 2 ≤ D.card

private abbrev PD5Block {K : ℕ} (A : Finset (BirthAddress K)) (a : BirthAddress K) :=
  {D : Finset (BirthAddress K) // D ∈ pd5_blocks A a}

private theorem pd5_block_props {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} (D : PD5Block A a) :
    D.1 ⊆ A ∧ a ∈ D.1 ∧ 2 ≤ D.1.card := by
  have h := Finset.mem_filter.mp D.2
  exact ⟨Finset.mem_powerset.mp h.1, h.2.1, h.2.2⟩

private abbrev PD5SystemDecomp {K : ℕ} (A : Finset (BirthAddress K)) (a : BirthAddress K) :=
  PD5System (A.erase a) ⊕ Σ D : PD5Block A a, PD5System (A \ D.1)

private theorem pd5_eraseBlock_system {K : ℕ} {A : Finset (BirthAddress K)}
    {D : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) (hD : D ∈ C) :
    C.erase D ∈ constraintSystems (A \ D) := by
  apply Iff.mpr (mem_constraintSystems_iff (A \ D) (C.erase D))
  have hs := Iff.mp (mem_constraintSystems_iff A C) hC
  refine ⟨?_, ?_⟩
  · intro E hE
    have hE' := Finset.mem_erase.mp hE
    have hEC : E ∈ C := hE'.2
    have hdisj := hs.2 E hEC D hD hE'.1
    refine ⟨?_, (hs.1 E hEC).2⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨(hs.1 E hEC).1 hx,
      (Finset.disjoint_left.mp hdisj) hx⟩
  · intro E hE F hF hEF
    exact hs.2 E (Finset.mem_erase.mp hE).2 F (Finset.mem_erase.mp hF).2 hEF

private theorem pd5_noBlock_system {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) (hNo : ∀ D ∈ C, a ∉ D) :
    C ∈ constraintSystems (A.erase a) := by
  apply Iff.mpr (mem_constraintSystems_iff (A.erase a) C)
  have hs := Iff.mp (mem_constraintSystems_iff A C) hC
  refine ⟨?_, hs.2⟩
  intro D hD
  refine ⟨?_, (hs.1 D hD).2⟩
  intro x hx
  refine Finset.mem_erase.mpr ⟨?_, (hs.1 D hD).1 hx⟩
  intro hxa
  subst x
  exact hNo D hD hx

private theorem pd5_eraseLift_system {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems (A.erase a)) : C ∈ constraintSystems A := by
  apply Iff.mpr (mem_constraintSystems_iff A C)
  have hs := Iff.mp (mem_constraintSystems_iff (A.erase a) C) hC
  refine ⟨?_, hs.2⟩
  intro D hD
  have hprops := hs.1 D hD
  exact ⟨Finset.Subset.trans hprops.1 (Finset.erase_subset _ _), hprops.2⟩

private theorem pd5_insertBlock_system {K : ℕ} {A : Finset (BirthAddress K)}
    {D : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hDsub : D ⊆ A) (hDcard : 2 ≤ D.card)
    (hC : C ∈ constraintSystems (A \ D)) :
    insert D C ∈ constraintSystems A := by
  apply Iff.mpr (mem_constraintSystems_iff A (insert D C))
  have hs := Iff.mp (mem_constraintSystems_iff (A \ D) C) hC
  have hDne : D ∉ C := by
    intro hDC
    have hDsub' := (hs.1 D hDC).1
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
    exact (Finset.mem_sdiff.mp (hDsub' hx)).2 hx
  have hdisj (E : Finset (BirthAddress K)) (hE : E ∈ C) : Disjoint D E := by
    apply Finset.disjoint_left.mpr
    intro x hxD hxE
    exact (Finset.mem_sdiff.mp ((hs.1 E hE).1 hxE)).2 hxD
  refine ⟨?_, ?_⟩
  · intro E hE
    rcases Finset.mem_insert.mp hE with hE | hE
    · subst E
      exact ⟨hDsub, hDcard⟩
    · have hprops := hs.1 E hE
      exact ⟨Finset.Subset.trans hprops.1 (Finset.sdiff_subset), hprops.2⟩
  · intro E hE F hF hEF
    rcases Finset.mem_insert.mp hE with hE | hE
    · subst E
      rcases Finset.mem_insert.mp hF with hF | hF
      · subst F
        exact (hEF rfl).elim
      · exact hdisj F hF
    · rcases Finset.mem_insert.mp hF with hF | hF
      · subst F
        exact (hdisj E hE).symm
      · exact hs.2 E hE F hF hEF

private theorem pd5_block_unique {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} {C : Finset (Finset (BirthAddress K))}
    (hs : IsConstraintSystem A C) {D E : Finset (BirthAddress K)}
    (hD : D ∈ C) (hE : E ∈ C) (hDa : a ∈ D) (hEa : a ∈ E) : D = E := by
  by_contra hne
  exact (Finset.disjoint_left.mp (hs.2 D hD E hE hne)) hDa hEa

private noncomputable def pd5_chooseBlock {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} (C : PD5System A)
    (h : ∃ D, D ∈ C.1 ∧ a ∈ D) : PD5Block A a := by
  classical
  let D := Classical.choose h
  have hD := Classical.choose_spec h
  have hs := Iff.mp (mem_constraintSystems_iff A C.1) C.2
  refine ⟨D, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_powerset.mpr (hs.1 D hD.1).1,
    ⟨hD.2, (hs.1 D hD.1).2⟩⟩

private theorem pd5_chooseBlock_mem {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} (C : PD5System A)
    (h : ∃ D, D ∈ C.1 ∧ a ∈ D) : (pd5_chooseBlock C h).1 ∈ C.1 := by
  change Classical.choose h ∈ C.1
  exact (Classical.choose_spec h).1

private noncomputable def pd5_encode_pos {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} (C : PD5System A)
    (h : ∃ D, D ∈ C.1 ∧ a ∈ D) : PD5SystemDecomp A a := by
  refine Sum.inr ⟨pd5_chooseBlock C h, ⟨C.1.erase (pd5_chooseBlock C h).1, ?_⟩⟩
  exact pd5_eraseBlock_system C.2 (pd5_chooseBlock_mem C h)

private def pd5_encode_neg {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} (C : PD5System A)
    (h : ¬ ∃ D, D ∈ C.1 ∧ a ∈ D) : PD5SystemDecomp A a := by
  apply Sum.inl
  refine ⟨C.1, pd5_noBlock_system C.2 ?_⟩
  intro D hD hDa
  exact h ⟨D, hD, hDa⟩

private noncomputable def pd5_encode {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} (C : PD5System A) : PD5SystemDecomp A a := by
  classical
  by_cases h : ∃ D, D ∈ C.1 ∧ a ∈ D
  · exact pd5_encode_pos C h
  · exact pd5_encode_neg C h

private def pd5_decode {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} : PD5SystemDecomp A a → PD5System A
  | Sum.inl C => ⟨C.1, pd5_eraseLift_system C.2⟩
  | Sum.inr ⟨D, C⟩ =>
      ⟨insert D.1 C.1,
        pd5_insertBlock_system (pd5_block_props D).1 (pd5_block_props D).2.2 C.2⟩

private theorem pd5_decode_encode {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} (C : PD5System A) :
    pd5_decode (a := a) (pd5_encode (a := a) C) = C := by
  classical
  apply Subtype.ext
  dsimp [pd5_decode]
  by_cases h : ∃ D, D ∈ C.1 ∧ a ∈ D
  · let D := Classical.choose h
    have hD := Classical.choose_spec h
    simp [pd5_encode, pd5_encode_pos, pd5_encode_neg, pd5_chooseBlock_mem,
      h, D, hD.1, Finset.insert_erase]
  · simp [pd5_encode, pd5_encode_neg, h]

private theorem pd5_encode_decode {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} (x : PD5SystemDecomp A a) : pd5_encode (pd5_decode x) = x := by
  classical
  cases x with
  | inl C =>
    have hNo : ¬ ∃ D, D ∈ C.1 ∧ a ∈ D := by
      rintro ⟨D, hD, hDa⟩
      have hs := Iff.mp (mem_constraintSystems_iff (A.erase a) C.1) C.2
      have ha : a ∈ A.erase a := (hs.1 D hD).1 hDa
      exact (Finset.mem_erase.mp ha).1 rfl
    simp [pd5_encode, pd5_encode_neg, pd5_decode, hNo]
  | inr y =>
    rcases y with ⟨D, C⟩
    let C' := insert D.1 C.1
    have hsys : C' ∈ constraintSystems A :=
      pd5_insertBlock_system (pd5_block_props D).1 (pd5_block_props D).2.2 C.2
    have hNoOther : ∀ E ∈ C.1, a ∉ E := by
      intro E hE hEa
      have hs := Iff.mp (mem_constraintSystems_iff (A \ D.1) C.1) C.2
      have hEsub := (hs.1 E hE).1
      have haE : a ∈ A \ D.1 := hEsub hEa
      exact (Finset.mem_sdiff.mp haE).2 (pd5_block_props D).2.1
    have hBlock : ∃ E, E ∈ C' ∧ a ∈ E :=
      ⟨D.1, Finset.mem_insert_self _ _, (pd5_block_props D).2.1⟩
    have hUnique : ∀ E, E ∈ C' → a ∈ E → E = D.1 := by
      intro E hE hEa
      rcases Finset.mem_insert.mp hE with hED | hE
      · exact hED
      · exact (hNoOther E hE hEa).elim
    have hChoiceAll : ∀ h : ∃ E, E ∈ C' ∧ a ∈ E, Classical.choose h = D.1 := by
      intro h
      apply hUnique
      · exact (Classical.choose_spec h).1
      · exact (Classical.choose_spec h).2
    have hDnot : D.1 ∉ C.1 := by
      intro hD
      have hs := Iff.mp (mem_constraintSystems_iff (A \ D.1) C.1) C.2
      have hsub := (hs.1 D.1 hD).1
      have hpos : 0 < D.1.card := Nat.zero_lt_two.trans_le (pd5_block_props D).2.2
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
      exact (Finset.mem_sdiff.mp (hsub hz)).2 hz
    change pd5_encode (pd5_decode (Sum.inr ⟨D, C⟩)) = Sum.inr ⟨D, C⟩
    dsimp only [pd5_decode]
    unfold pd5_encode
    by_cases h : ∃ E, E ∈ C' ∧ a ∈ E
    · have hChoice := hChoiceAll h
      rw [dif_pos h]
      have hval : (pd5_chooseBlock ⟨C', hsys⟩ h).1 = Classical.choose h := rfl
      have hChosen : pd5_chooseBlock ⟨C', hsys⟩ h = D :=
        Subtype.ext (hval.trans hChoice)
      change pd5_encode_pos ⟨C', hsys⟩ h = Sum.inr ⟨D, C⟩
      dsimp only [pd5_encode_pos]
      apply congrArg Sum.inr
      apply Sigma.ext
      · exact hChosen
      · have hval : (pd5_chooseBlock ⟨C', hsys⟩ h).1 = D.1 :=
          congrArg Subtype.val hChosen
        have hidx : A \ D.1 = A \ (pd5_chooseBlock ⟨C', hsys⟩ h).1 := by
          rw [← hval]
        have htype : PD5System (A \ D.1) =
            PD5System (A \ (pd5_chooseBlock ⟨C', hsys⟩ h).1) :=
          congrArg PD5System hidx
        apply heq_of_eq_cast htype
        apply Subtype.ext
        simp only [pd5_system_val_cast hidx C]
        rw [hval]
        simp [C', hDnot]
    · exact False.elim (h ⟨D.1, Finset.mem_insert_self _ _, (pd5_block_props D).2.1⟩)

private noncomputable def pd5_systemDecompEquiv {K : ℕ}
    (A : Finset (BirthAddress K)) (a : BirthAddress K) :
    PD5System A ≃ PD5SystemDecomp A a where
  toFun := pd5_encode
  invFun := pd5_decode
  left_inv := pd5_decode_encode
  right_inv := pd5_encode_decode

private def pd5_systemProd {K : ℕ} (w : Finset (BirthAddress K) → ℂ)
    (C : Finset (Finset (BirthAddress K))) : ℂ := ∏ D ∈ C, w D

private noncomputable def pd5_systemSum {K : ℕ} (A : Finset (BirthAddress K))
    (w : Finset (BirthAddress K) → ℂ) : ℂ :=
  ∑ C : PD5System A, pd5_systemProd w C.1

private theorem pd5_block_notmem_system {K : ℕ} {A : Finset (BirthAddress K)}
    {a : BirthAddress K} (D : PD5Block A a) (C : PD5System (A \ D.1)) :
    D.1 ∉ C.1 := by
  intro hD
  have hs := Iff.mp (mem_constraintSystems_iff (A \ D.1) C.1) C.2
  have hsub := (hs.1 D.1 hD).1
  have hpos : 0 < D.1.card := Nat.zero_lt_two.trans_le (pd5_block_props D).2.2
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  exact (Finset.mem_sdiff.mp (hsub hx)).2 hx

private theorem pd5_systemProd_insert {K : ℕ} (w : Finset (BirthAddress K) → ℂ)
    (D : Finset (BirthAddress K)) (C : Finset (Finset (BirthAddress K)))
    (hD : D ∉ C) :
    pd5_systemProd w (insert D C) = w D * pd5_systemProd w C := by
  simp [pd5_systemProd, hD]

private theorem pd5_systemSum_recurrence {K : ℕ} (A : Finset (BirthAddress K))
    (a : BirthAddress K) (w : Finset (BirthAddress K) → ℂ) :
    pd5_systemSum A w = pd5_systemSum (A.erase a) w +
      ∑ D : PD5Block A a, ∑ C : PD5System (A \ D.1),
        w D.1 * pd5_systemProd w C.1 := by
  classical
  calc
    pd5_systemSum A w =
        ∑ C : PD5SystemDecomp A a, pd5_systemProd w (pd5_decode C).1 := by
      unfold pd5_systemSum
      apply Fintype.sum_equiv (pd5_systemDecompEquiv A a)
      intro C
      simp [pd5_systemDecompEquiv, pd5_systemProd, pd5_decode_encode]
    _ = pd5_systemSum (A.erase a) w +
        ∑ D : PD5Block A a, ∑ C : PD5System (A \ D.1),
          w D.1 * pd5_systemProd w C.1 := by
      simp only [Fintype.sum_sum_type, Fintype.sum_sigma]
      simp only [pd5_systemSum, pd5_systemProd, pd5_decode]
      congr 1
      apply Fintype.sum_congr
      intro D
      apply Fintype.sum_congr
      intro C
      exact pd5_systemProd_insert w D.1 C.1 (pd5_block_notmem_system D C)

private noncomputable def pd5_label {K : ℕ} (log : BirthLog K)
    (a : BirthAddress K) : Option ℕ :=
  if h : ∃ v, (a, v) ∈ log then some (Classical.choose h) else none

private theorem pd5_label_spec {K : ℕ} {log : BirthLog K}
    (hnodup : (log.map Prod.fst).Nodup) (a : BirthAddress K) (v : ℕ) :
    pd5_label log a = some v ↔ (a, v) ∈ log := by
  classical
  have hunique {v w : ℕ} (hv : (a, v) ∈ log) (hw : (a, w) ∈ log) : v = w := by
    have hp : (a, v) = (a, w) :=
      List.inj_on_of_nodup_map (f := Prod.fst) hnodup hv hw rfl
    exact congrArg Prod.snd hp
  unfold pd5_label
  by_cases h : ∃ u, (a, u) ∈ log
  · simp only [dif_pos h, Option.some.injEq]
    constructor
    · intro hv
      subst v
      exact Classical.choose_spec h
    · intro hv
      exact hunique (Classical.choose_spec h) hv
  · simp only [dif_neg h]
    constructor
    · intro hv
      cases hv
    · intro hv
      exact (h ⟨v, hv⟩).elim

private def pd5_cycleCoeff (r : ℕ) : ℂ :=
  ((((-1 : ℤ) ^ r * (r.factorial : ℤ) : ℤ) : ℂ))

private theorem pd5_cycleCoeff_cancel (r : ℕ) :
    (r + 1 : ℂ) * pd5_cycleCoeff r + pd5_cycleCoeff (r + 1) = 0 := by
  unfold pd5_cycleCoeff
  rw [pow_succ, Nat.factorial_succ]
  norm_cast
  push_cast
  ring

private theorem pd5_cycleCoeff_ne_zero (r : ℕ) : pd5_cycleCoeff r ≠ 0 := by
  unfold pd5_cycleCoeff
  have h : ((-1 : ℤ) ^ r * (r.factorial : ℤ)) ≠ 0 := by
    have hf : (r.factorial : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero r)
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hf
  exact_mod_cast h

private def pd5_labelNoCollision {K : ℕ} (label : BirthAddress K → Option ℕ)
    (A : Finset (BirthAddress K)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → label a = label b → label a = none

private theorem pd5_exists_label_collision {K : ℕ}
    (label : BirthAddress K → Option ℕ) (A : Finset (BirthAddress K))
    (hN : ¬ pd5_labelNoCollision label A) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ label a = label b ∧ label a ≠ none := by
  classical
  unfold pd5_labelNoCollision at hN
  push_neg at hN
  exact hN

private def pd5_labelBlockFactor {K : ℕ} (label : BirthAddress K → Option ℕ)
    (D : Finset (BirthAddress K)) : ℂ :=
  pd5_cycleCoeff (D.card - 1) * (if ∃ v, ∀ a ∈ D, label a = some v then 1 else 0)

private def pd5_fiber {K : ℕ} (label : BirthAddress K → Option ℕ) (v : ℕ)
    (A : Finset (BirthAddress K)) : Finset (BirthAddress K) :=
  A.filter fun a => label a = some v

private theorem pd5_labelNoCollision_subset {K : ℕ}
    (label : BirthAddress K → Option ℕ) {A B : Finset (BirthAddress K)}
    (hBA : B ⊆ A) (hN : pd5_labelNoCollision label A) :
    pd5_labelNoCollision label B := by
  intro a ha b hb hab heq
  exact hN a (hBA ha) b (hBA hb) hab heq

private theorem pd5_labelNoCollision_split {K : ℕ}
    (label : BirthAddress K → Option ℕ) (A : Finset (BirthAddress K)) (v : ℕ) :
    pd5_labelNoCollision label A ↔
      pd5_labelNoCollision label (A \ pd5_fiber label v A) ∧
        (pd5_fiber label v A).card ≤ 1 := by
  classical
  let F := pd5_fiber label v A
  constructor
  · intro hN
    constructor
    · apply pd5_labelNoCollision_subset label (Finset.sdiff_subset) hN
    · rw [Finset.card_le_one]
      intro x hx y hy
      have hxA := (Finset.mem_filter.mp hx).1
      have hyA := (Finset.mem_filter.mp hy).1
      have hxv := (Finset.mem_filter.mp hx).2
      have hyv := (Finset.mem_filter.mp hy).2
      by_contra hxy
      have hn : label x = none := hN x hxA y hyA hxy (hxv.trans hyv.symm)
      cases hn.symm.trans hxv
  · rintro ⟨hOut, hcard⟩ x hx y hy hxy hlabels
    by_cases hxF : x ∈ F
    · have hxv := (Finset.mem_filter.mp hxF).2
      by_cases hyF : y ∈ F
      · have hxy' := (Finset.card_le_one.mp hcard) x hxF y hyF
        exact (hxy hxy').elim
      · have hyv : label y = some v := hlabels.symm.trans hxv
        have hyFmem : y ∈ F := by
          change y ∈ pd5_fiber label v A
          exact Finset.mem_filter.mpr ⟨hy, hyv⟩
        exact False.elim (hyF hyFmem)
    · by_cases hyF : y ∈ F
      · have hyF' : y ∈ pd5_fiber label v A := by simpa [F] using hyF
        have hyv := (Finset.mem_filter.mp hyF').2
        have hxv : label x = some v := hlabels.trans hyv
        have hxF' : x ∈ pd5_fiber label v A := Finset.mem_filter.mpr ⟨hx, hxv⟩
        have hxFmem : x ∈ F := by change x ∈ pd5_fiber label v A; exact hxF'
        exact False.elim (hxF hxFmem)
      · exact hOut x (Finset.mem_sdiff.mpr ⟨hx, hxF⟩) y
          (Finset.mem_sdiff.mpr ⟨hy, hyF⟩) hxy hlabels

private theorem pd5_fiber_erase {K : ℕ} (label : BirthAddress K → Option ℕ)
    (A : Finset (BirthAddress K)) (a : BirthAddress K) (v : ℕ)
    (ha : a ∈ A) (hav : label a = some v) :
    pd5_fiber label v (A.erase a) = (pd5_fiber label v A).erase a := by
  classical
  ext x
  simp [pd5_fiber, and_assoc, and_left_comm, and_comm]

private theorem pd5_fiber_sdiff {K : ℕ} (label : BirthAddress K → Option ℕ)
    (A D : Finset (BirthAddress K)) (v : ℕ)
    (hD : D ⊆ pd5_fiber label v A) :
    pd5_fiber label v (A \ D) = (pd5_fiber label v A) \ D := by
  classical
  ext x
  simp [pd5_fiber, and_assoc, and_left_comm, and_comm]

private theorem pd5_labelNoCollision_iff_nodup {K : ℕ} (log : BirthLog K)
    (hnodup : (log.map Prod.fst).Nodup) (A : Finset (BirthAddress K))
    (hA : ∀ e ∈ log, e.1 ∈ A) :
    pd5_labelNoCollision (pd5_label log) A ↔ (log.map Prod.snd).Nodup := by
  classical
  have hlog : log.Nodup := List.Nodup.of_map Prod.fst hnodup
  constructor
  · intro hN
    rw [List.nodup_map_iff_inj_on hlog]
    intro e he f hf hev
    by_cases haddr : e.1 = f.1
    · exact Prod.ext haddr hev
    · have heA := hA e he
      have hfA := hA f hf
      have heLab := (pd5_label_spec hnodup e.1 e.2).2 he
      have hfLab := (pd5_label_spec hnodup f.1 f.2).2 hf
      have hfLab' : pd5_label log f.1 = some e.2 := by rw [hev]; exact hfLab
      have heqLab : pd5_label log e.1 = pd5_label log f.1 := heLab.trans hfLab'.symm
      have hnone := hN e.1 heA f.1 hfA haddr heqLab
      cases hnone.symm.trans heLab
  · intro hN
    intro a ha b hb hab hEq
    cases hla : pd5_label log a with
    | none => rfl
    | some v =>
      have hla' : (a, v) ∈ log := (pd5_label_spec hnodup a v).1 hla
      have hlb : pd5_label log b = some v := hEq.symm.trans hla
      have hlb' : (b, v) ∈ log := (pd5_label_spec hnodup b v).1 hlb
      have hp : (a, v) = (b, v) :=
        List.inj_on_of_nodup_map (f := Prod.snd) hN hla' hlb' rfl
      exact False.elim (hab (congrArg Prod.fst hp))

private def pd5_blockFactor {K : ℕ} (log : BirthLog K)
    (D : Finset (BirthAddress K)) : ℂ :=
  (((-1 : ℤ) ^ (D.card - 1) * ((D.card - 1).factorial : ℤ) : ℤ) : ℂ) *
    (if ∃ v, ∀ a ∈ D, (a, v) ∈ log then 1 else 0)

private theorem pd5_labelBlockFactor_log {K : ℕ} (log : BirthLog K)
    (hnodup : (log.map Prod.fst).Nodup) (D : Finset (BirthAddress K)) :
    pd5_labelBlockFactor (pd5_label log) D = pd5_blockFactor log D := by
  have hblock :
      (∃ v, ∀ a ∈ D, pd5_label log a = some v) ↔
        ∃ v, ∀ a ∈ D, (a, v) ∈ log := by
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v, fun a ha => (pd5_label_spec hnodup a v).1 (hv a ha)⟩
    · rintro ⟨v, hv⟩
      exact ⟨v, fun a ha => (pd5_label_spec hnodup a v).2 (hv a ha)⟩
  simp [pd5_labelBlockFactor, pd5_blockFactor, pd5_cycleCoeff, hblock]

private theorem pd5_systemWeight {K : ℕ} (log : BirthLog K)
    (C : Finset (Finset (BirthAddress K))) :
    (constraintCoeff C : ℂ) * constraintWeight C log =
      pd5_systemProd (pd5_blockFactor log) C := by
  simp only [constraintCoeff, constraintWeight, pd5_systemProd, pd5_blockFactor,
    Int.cast_prod]
  rw [← Finset.prod_mul_distrib]

private theorem pd5_systemSum_partitionRhs {K : ℕ} (A : Finset (BirthAddress K))
    (log : BirthLog K) :
    pd5_systemSum A (pd5_blockFactor log) =
      ∑ C ∈ constraintSystems A,
        (constraintCoeff C : ℂ) * constraintWeight C log := by
  classical
  calc
    pd5_systemSum A (pd5_blockFactor log) =
        ∑ C ∈ constraintSystems A, pd5_systemProd (pd5_blockFactor log) C := by
      unfold pd5_systemSum
      exact (Finset.sum_subtype (constraintSystems A) (fun _ => Iff.rfl)
        (fun C => pd5_systemProd (pd5_blockFactor log) C)).symm
    _ = ∑ C ∈ constraintSystems A,
          (constraintCoeff C : ℂ) * constraintWeight C log := by
      apply Finset.sum_congr rfl
      intro C hC
      exact (pd5_systemWeight log C).symm

private theorem pd5_labelBlockFactor_zero_of_noCollision {K : ℕ}
    {A : Finset (BirthAddress K)} {a : BirthAddress K}
    (label : BirthAddress K → Option ℕ) (D : PD5Block A a)
    (hN : pd5_labelNoCollision label A) :
    pd5_labelBlockFactor label D.1 = 0 := by
  classical
  by_cases h : ∃ v, ∀ b ∈ D.1, label b = some v
  · obtain ⟨v, hv⟩ := h
    have hDcard : 2 ≤ D.1.card := (pd5_block_props D).2.2
    obtain ⟨b, hb, c, hc, hbc⟩ :=
      Finset.one_lt_card.mp (lt_of_lt_of_le Nat.one_lt_two hDcard)
    have hbcLab := hN b ((pd5_block_props D).1 hb) c ((pd5_block_props D).1 hc)
      hbc ((hv b hb).trans (hv c hc).symm)
    cases hbcLab.symm.trans (hv b hb)
  · simp [pd5_labelBlockFactor, h]

private theorem pd5_label_partition_of_noCollision {K : ℕ}
    (A : Finset (BirthAddress K)) (label : BirthAddress K → Option ℕ)
    (hN : pd5_labelNoCollision label A) :
    pd5_systemSum A (pd5_labelBlockFactor label) = 1 := by
  classical
  induction A using Finset.induction with
  | empty =>
      have hCS : constraintSystems (∅ : Finset (BirthAddress K)) = {∅} := by
        ext C
        constructor
        · intro hC
          by_contra hne
          have hne' : C ≠ ∅ := by simpa using hne
          have hs := Iff.mp (mem_constraintSystems_iff ∅ C) hC
          obtain ⟨B, hB⟩ := Finset.nonempty_iff_ne_empty.mpr hne'
          have hBsub := (hs.1 B hB).1
          have hBempty : B = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro b hb
            exact (by simpa using hBsub hb)
          have hBcard := (hs.1 B hB).2
          simp [hBempty] at hBcard
        · intro hC
          have hC' : C = ∅ := Finset.mem_singleton.mp hC
          subst C
          apply Iff.mpr (mem_constraintSystems_iff (∅ : Finset (BirthAddress K)) ∅)
          constructor <;> simp [IsConstraintSystem]
      calc
        pd5_systemSum ∅ (pd5_labelBlockFactor label) =
            ∑ C ∈ constraintSystems (∅ : Finset (BirthAddress K)),
              pd5_systemProd (pd5_labelBlockFactor label) C := by
          unfold pd5_systemSum
          exact (Finset.sum_subtype (constraintSystems ∅) (fun _ => Iff.rfl)
            (fun C => pd5_systemProd (pd5_labelBlockFactor label) C)).symm
        _ = 1 := by rw [hCS]; simp [pd5_systemProd]
  | @insert a s ha ih =>
      have hNs := pd5_labelNoCollision_subset label (Finset.subset_insert _ _) hN
      have hrec := pd5_systemSum_recurrence (insert a s) a (pd5_labelBlockFactor label)
      rw [hrec]
      have hbase : pd5_systemSum ((insert a s).erase a) (pd5_labelBlockFactor label) = 1 := by
        simpa [Finset.erase_insert ha] using ih hNs
      have hterms :
          (∑ D : PD5Block (insert a s) a,
            ∑ C : PD5System ((insert a s) \ D.1),
              pd5_labelBlockFactor label D.1 * pd5_systemProd (pd5_labelBlockFactor label) C.1) = 0 := by
        simp [pd5_labelBlockFactor_zero_of_noCollision label, hN]
      rw [hbase, hterms]
      simp

private def pd5_smallBlocks {K : ℕ} (F : Finset (BirthAddress K))
    (a : BirthAddress K) : Finset (Finset (BirthAddress K)) :=
  (pd5_blocks F a).filter fun D => (F \ D).card ≤ 1

private theorem pd5_smallBlocks_eq {K : ℕ} (F : Finset (BirthAddress K))
    (a : BirthAddress K) (ha : a ∈ F) (hcard : 3 ≤ F.card) :
    pd5_smallBlocks F a =
      insert F ((F.erase a).image fun b => F.erase b) := by
  classical
  ext D
  constructor
  · intro hD
    have hD' := Finset.mem_filter.mp hD
    have hblk := Finset.mem_filter.mp hD'.1
    have hsub : D ⊆ F := Finset.mem_powerset.mp hblk.1
    have haD := hblk.2.1
    have hcardD := hblk.2.2
    have hcomp := hD'.2
    by_cases hEq : D = F
    · exact Finset.mem_insert.mpr (Or.inl hEq)
    · have hne : (F \ D).Nonempty := by
        by_contra hne
        have hEmpty : F \ D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hFD : F ⊆ D := Finset.sdiff_eq_empty_iff_subset.mp hEmpty
        exact hEq (Finset.Subset.antisymm hsub hFD)
      have hcompPos : 0 < (F \ D).card := Finset.card_pos.mpr hne
      have hcompEq : (F \ D).card = 1 := by omega
      obtain ⟨b, hbComp⟩ := Finset.card_eq_one.mp hcompEq
      have hbF : b ∈ F := by
        have : b ∈ F \ D := by rw [hbComp]; simp
        exact (Finset.mem_sdiff.mp this).1
      have hbNotD : b ∉ D := by
        have : b ∈ F \ D := by rw [hbComp]; simp
        exact (Finset.mem_sdiff.mp this).2
      have hba : b ≠ a := by
        intro hba
        subst b
        exact hbNotD haD
      have hbErase : b ∈ F.erase a := Finset.mem_erase.mpr ⟨hba, hbF⟩
      have hDE : D = F.erase b := by
        apply Finset.ext
        intro x
        constructor
        · intro hx
          refine Finset.mem_erase.mpr ⟨?_, hsub hx⟩
          intro hxb
          subst x
          exact hbNotD hx
        · intro hx
          have hx' := Finset.mem_erase.mp hx
          have hxF : x ∈ F := hx'.2
          by_contra hxD
          have hxComp : x ∈ F \ D := Finset.mem_sdiff.mpr ⟨hxF, hxD⟩
          rw [hbComp] at hxComp
          have hxb : x = b := by simpa using hxComp
          exact hx'.1 hxb
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨b, hbErase, hDE.symm⟩))
  · intro hD
    rcases Finset.mem_insert.mp hD with hEq | hD
    · subst D
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (fun _ hx => hx), ⟨ha, by omega⟩⟩
      · simp
    · rcases Finset.mem_image.mp hD with ⟨b, hb, hEq⟩
      subst D
      have hbF := (Finset.mem_erase.mp hb).2
      have hba := (Finset.mem_erase.mp hb).1
      have hcardErase : 2 ≤ (F.erase b).card := by
        rw [Finset.card_erase_of_mem hbF]
        omega
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.erase_subset _ _),
            ⟨Finset.mem_erase.mpr ⟨hba.symm, ha⟩, hcardErase⟩⟩
      · simp [Finset.sdiff_erase_self hbF]

private theorem pd5_smallBlockCoeff_sum {K : ℕ} (F : Finset (BirthAddress K))
    (a : BirthAddress K) (ha : a ∈ F) (hcard : 3 ≤ F.card) :
    (∑ D ∈ pd5_smallBlocks F a, pd5_cycleCoeff (D.card - 1)) = 0 := by
  classical
  have hnot : F ∉ (F.erase a).image (fun b => F.erase b) := by
    intro hF
    rcases Finset.mem_image.mp hF with ⟨b, hb, hEq⟩
    have hbF := (Finset.mem_erase.mp hb).2
    have hbNot : b ∉ F.erase b := by simp
    have hb' : b ∈ F.erase b := by rw [hEq]; exact hbF
    exact hbNot hb'
  have hinj : Set.InjOn (fun b : BirthAddress K => F.erase b) (F.erase a) := by
    intro b hb c hc hEq
    by_contra hne
    have hcF := (Finset.mem_erase.mp hc).2
    have hcNeB : c ≠ b := Ne.symm hne
    have hcIn : c ∈ F.erase b := Finset.mem_erase.mpr ⟨hcNeB, hcF⟩
    change F.erase b = F.erase c at hEq
    rw [hEq] at hcIn
    simpa using hcIn
  have hsum :
      (∑ D ∈ pd5_smallBlocks F a, pd5_cycleCoeff (D.card - 1)) =
        pd5_cycleCoeff (F.card - 1) +
          ∑ b ∈ F.erase a, pd5_cycleCoeff ((F.erase b).card - 1) := by
    rw [pd5_smallBlocks_eq F a ha hcard, Finset.sum_insert hnot, Finset.sum_image hinj]
  rw [hsum]
  have hcardErase : (F.erase a).card = F.card - 1 := Finset.card_erase_of_mem ha
  have hrankSum :
      (∑ b ∈ F.erase a, pd5_cycleCoeff ((F.erase b).card - 1)) =
        ∑ b ∈ F.erase a, pd5_cycleCoeff (F.card - 2) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mp hb).2]
    congr 1
  rw [hrankSum]
  rw [Finset.sum_const, nsmul_eq_mul, hcardErase]
  have hcancel := pd5_cycleCoeff_cancel (F.card - 2)
  have hr : F.card - 2 + 1 = F.card - 1 := by omega
  rw [hr] at hcancel
  have hrCast : ((F.card - 1 : ℕ) : ℂ) = ((F.card - 2 : ℕ) : ℂ) + 1 := by
    exact_mod_cast hr.symm
  simpa [add_comm, hrCast] using hcancel

private theorem pd5_smallBlockCoeff_sum_two {K : ℕ} (F : Finset (BirthAddress K))
    (a : BirthAddress K) (ha : a ∈ F) (hcard : F.card = 2) :
    (∑ D ∈ pd5_smallBlocks F a, pd5_cycleCoeff (D.card - 1)) =
      pd5_cycleCoeff 1 := by
  have hsmall : pd5_smallBlocks F a = {F} := by
    ext D
    constructor
    · intro hD
      have hblk := (Finset.mem_filter.mp hD).1
      have hprops := Finset.mem_filter.mp hblk
      have hsub := Finset.mem_powerset.mp hprops.1
      have hcardD := hprops.2.2
      apply Finset.mem_singleton.mpr
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hcard]
      exact hcardD
    · intro hD
      have hEq : D = F := Finset.mem_singleton.mp hD
      subst D
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (fun _ hx => hx), ⟨ha, by omega⟩⟩
      · simp
  rw [hsmall]
  simp [pd5_cycleCoeff, hcard]

private theorem pd5_sdiff_card_lt {K : ℕ} {A D : Finset (BirthAddress K)}
    {a : BirthAddress K} (ha : a ∈ A) (hD : a ∈ D) : (A \ D).card < A.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · exact Finset.sdiff_subset
  · intro hEq
    have ha' : a ∈ A \ D := by rw [hEq]; exact ha
    exact (Finset.mem_sdiff.mp ha').2 hD

private theorem pd5_fiber_subset {K : ℕ} (label : BirthAddress K → Option ℕ)
    (A : Finset (BirthAddress K)) (v : ℕ) : pd5_fiber label v A ⊆ A :=
  Finset.filter_subset _ _

private theorem pd5_fiberBlockSum_reindex {K : ℕ} (A F : Finset (BirthAddress K))
    (a : BirthAddress K) (hFA : F ⊆ A) :
    (∑ D : PD5Block A a,
      if D.1 ⊆ F ∧ (F \ D.1).card ≤ 1 then pd5_cycleCoeff (D.1.card - 1) else 0) =
      ∑ D ∈ pd5_smallBlocks F a, pd5_cycleCoeff (D.card - 1) := by
  classical
  let T := (pd5_blocks A a).filter fun D => D ⊆ F ∧ (F \ D).card ≤ 1
  have hT : T = pd5_smallBlocks F a := by
    ext D
    constructor
    · intro hD
      have hD' := Finset.mem_filter.mp hD
      have hblk := Finset.mem_filter.mp hD'.1
      have hprops := hD'.2
      apply Finset.mem_filter.mpr
      refine ⟨?_, hprops.2⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hprops.1, ⟨hblk.2.1, hblk.2.2⟩⟩
    · intro hD
      have hD' := Finset.mem_filter.mp hD
      have hblk := Finset.mem_filter.mp hD'.1
      have hsubA : D ⊆ A :=
        Finset.Subset.trans (Finset.mem_powerset.mp hblk.1) hFA
      have hsubF : D ⊆ F := Finset.mem_powerset.mp hblk.1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsubA, ⟨hblk.2.1, hblk.2.2⟩⟩, ⟨hsubF, hD'.2⟩⟩
  calc
    (∑ D : PD5Block A a,
        if D.1 ⊆ F ∧ (F \ D.1).card ≤ 1 then pd5_cycleCoeff (D.1.card - 1) else 0) =
      ∑ D ∈ pd5_blocks A a,
        if D ⊆ F ∧ (F \ D).card ≤ 1 then pd5_cycleCoeff (D.card - 1) else 0 := by
          unfold PD5Block
          exact (Finset.sum_subtype (pd5_blocks A a) (fun _ => Iff.rfl)
            (fun D => if D ⊆ F ∧ (F \ D).card ≤ 1 then
              pd5_cycleCoeff (D.card - 1) else 0)).symm
    _ = ∑ D ∈ T, pd5_cycleCoeff (D.card - 1) := by
          simp [T, Finset.sum_filter]
    _ = ∑ D ∈ pd5_smallBlocks F a, pd5_cycleCoeff (D.card - 1) := by rw [hT]

private theorem pd5_labelBlockFactor_zero_or_subsetFiber {K : ℕ}
    {A : Finset (BirthAddress K)} {a : BirthAddress K}
    (label : BirthAddress K → Option ℕ) (v : ℕ) (hav : label a = some v)
    (D : PD5Block A a) :
    pd5_labelBlockFactor label D.1 = 0 ∨ D.1 ⊆ pd5_fiber label v A := by
  classical
  by_cases hmono : ∃ w, ∀ x ∈ D.1, label x = some w
  · obtain ⟨w, hw⟩ := hmono
    have hwv : w = v := Option.some.inj ((hw a (pd5_block_props D).2.1).symm.trans hav)
    right
    intro x hx
    apply Finset.mem_filter.mpr
    constructor
    · exact (pd5_block_props D).1 hx
    · rw [← hwv]
      exact hw x hx
  · left
    simp [pd5_labelBlockFactor, hmono]

private theorem pd5_labelBlockFactor_of_subsetFiber {K : ℕ}
    {A : Finset (BirthAddress K)} (label : BirthAddress K → Option ℕ) (v : ℕ)
    (D : Finset (BirthAddress K))
    (hD : D ⊆ pd5_fiber label v A) :
    pd5_labelBlockFactor label D = pd5_cycleCoeff (D.card - 1) := by
  have hmono : ∀ x ∈ D, label x = some v := by
    intro x hx
    exact (Finset.mem_filter.mp (hD hx)).2
  unfold pd5_labelBlockFactor
  rw [if_pos ⟨v, hmono⟩]
  simp

private theorem pd5_outside_fiber_sdiff {K : ℕ}
    (label : BirthAddress K → Option ℕ) (A D : Finset (BirthAddress K)) (v : ℕ)
    (hD : D ⊆ pd5_fiber label v A) :
    (A \ D) \ (pd5_fiber label v A \ D) = A \ pd5_fiber label v A := by
  classical
  ext x
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hxA, hxD⟩, hnot⟩
    refine ⟨hxA, ?_⟩
    intro hxF
    exact hnot ⟨hxF, hxD⟩
  · rintro ⟨hxA, hxF⟩
    refine ⟨⟨hxA, ?_⟩, ?_⟩
    · intro hxD
      exact hxF (hD hxD)
    · intro hxDiff
      exact hxF hxDiff.1

private theorem pd5_outside_fiber_erase {K : ℕ}
    (label : BirthAddress K → Option ℕ) (A : Finset (BirthAddress K)) (a : BirthAddress K)
    (v : ℕ) (ha : a ∈ A) (hav : label a = some v) :
    (A.erase a) \ ((pd5_fiber label v A).erase a) = A \ pd5_fiber label v A := by
  classical
  ext x
  have haF : a ∈ pd5_fiber label v A := Finset.mem_filter.mpr ⟨ha, hav⟩
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hxa, hxA⟩, hnot⟩
    refine ⟨hxA, ?_⟩
    intro hxF
    by_cases hEq : x = a
    · exact hxa hEq
    · exact hnot ⟨hEq, hxF⟩
  · rintro ⟨hxA, hxF⟩
    refine ⟨⟨?_, hxA⟩, ?_⟩
    · intro hxa
      subst x
      exact hxF haF
    · intro hxDiff
      exact hxF hxDiff.2

private theorem pd5_labelNoCollision_erase_iff {K : ℕ}
    (label : BirthAddress K → Option ℕ) (A : Finset (BirthAddress K))
    (a : BirthAddress K) (v : ℕ) (ha : a ∈ A) (hav : label a = some v)
    (hOut : pd5_labelNoCollision label (A \ pd5_fiber label v A)) :
    pd5_labelNoCollision label (A.erase a) ↔
    ((pd5_fiber label v A).erase a).card ≤ 1 := by
  have hsplit := pd5_labelNoCollision_split label (A.erase a) v
  rw [pd5_fiber_erase label A a v ha hav,
    pd5_outside_fiber_erase label A a v ha hav] at hsplit
  simpa [hOut] using hsplit

private theorem pd5_labelNoCollision_sdiff_iff {K : ℕ}
    (label : BirthAddress K → Option ℕ) (A D : Finset (BirthAddress K))
    (v : ℕ) (hD : D ⊆ pd5_fiber label v A)
    (hOut : pd5_labelNoCollision label (A \ pd5_fiber label v A)) :
    pd5_labelNoCollision label (A \ D) ↔
      (pd5_fiber label v A \ D).card ≤ 1 := by
  have hsplit := pd5_labelNoCollision_split label (A \ D) v
  rw [pd5_fiber_sdiff label A D v hD,
    pd5_outside_fiber_sdiff label A D v hD] at hsplit
  simpa [hOut] using hsplit

private theorem pd5_label_partition_full {K : ℕ} (A : Finset (BirthAddress K))
    (label : BirthAddress K → Option ℕ) :
    pd5_systemSum A (pd5_labelBlockFactor label) =
      if pd5_labelNoCollision label A then 1 else 0 := by
  classical
  have main : ∀ n : ℕ, ∀ B : Finset (BirthAddress K), B.card = n →
      pd5_systemSum B (pd5_labelBlockFactor label) =
        if pd5_labelNoCollision label B then 1 else 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hcard
      by_cases hN : pd5_labelNoCollision label B
      · rw [if_pos hN]
        exact pd5_label_partition_of_noCollision B label hN
      · rw [if_neg hN]
        obtain ⟨a, ha, b, hb, hab, hEq, hne⟩ :=
          pd5_exists_label_collision label B hN
        cases hla : label a with
        | none => exact (hne hla).elim
        | some v =>
          have hlb : label b = some v := hEq.symm.trans hla
          let F := pd5_fiber label v B
          let O := B \ F
          have haF : a ∈ F := Finset.mem_filter.mpr ⟨ha, hla⟩
          have hbF : b ∈ F := Finset.mem_filter.mpr ⟨hb, hlb⟩
          have hFlarge : 2 ≤ F.card := by
            have hlt : 1 < F.card := Finset.one_lt_card.mpr ⟨a, haF, b, hbF, hab⟩
            omega
          have hn : 0 < n := by
            rw [← hcard]
            exact Finset.card_pos.mpr ⟨a, ha⟩
          have hrec := pd5_systemSum_recurrence B a (pd5_labelBlockFactor label)
          by_cases hOut : pd5_labelNoCollision label O
          · have hbaseIff : pd5_labelNoCollision label (B.erase a) ↔ F.card ≤ 2 := by
              rw [pd5_labelNoCollision_erase_iff label B a v ha hla (by simpa [O, F] using hOut)]
              rw [show (pd5_fiber label v B).erase a = F.erase a by rfl]
              rw [Finset.card_erase_of_mem haF]
              omega
            have hltBase : (B.erase a).card < n := by
              rw [Finset.card_erase_of_mem ha, hcard]
              omega
            have hbaseIH := ih (B.erase a).card hltBase (B.erase a) rfl
            have hbaseVal : pd5_systemSum (B.erase a) (pd5_labelBlockFactor label) =
                if F.card ≤ 2 then 1 else 0 := by
              simpa only [hbaseIff] using hbaseIH
            have hterms :
                (∑ D : PD5Block B a, ∑ C : PD5System (B \ D.1),
                  pd5_labelBlockFactor label D.1 *
                    pd5_systemProd (pd5_labelBlockFactor label) C.1) =
                  ∑ D : PD5Block B a,
                    if D.1 ⊆ F ∧ (F \ D.1).card ≤ 1 then
                      pd5_cycleCoeff (D.1.card - 1) else 0 := by
              apply Fintype.sum_congr
              intro D
              have hltD : (B \ D.1).card < n := by
                rw [← hcard]
                exact pd5_sdiff_card_lt ha (pd5_block_props D).2.1
              have hcompIH := ih (B \ D.1).card hltD (B \ D.1) rfl
              rw [← Finset.mul_sum]
              change pd5_labelBlockFactor label D.1 *
                pd5_systemSum (B \ D.1) (pd5_labelBlockFactor label) = _
              rw [hcompIH]
              rcases pd5_labelBlockFactor_zero_or_subsetFiber label v hla D with hzero | hsubset
              · by_cases hcond : D.1 ⊆ F ∧ (F \ D.1).card ≤ 1
                · have hDfiber : D.1 ⊆ pd5_fiber label v B := by
                    simpa [F] using hcond.1
                  have hfactor := pd5_labelBlockFactor_of_subsetFiber label v D.1 hDfiber
                  rw [hfactor] at hzero
                  exfalso
                  exact (pd5_cycleCoeff_ne_zero _) hzero
                · simp [hzero, hcond]
              · have hDfiber : D.1 ⊆ pd5_fiber label v B := by simpa [F] using hsubset
                have hDsubF : D.1 ⊆ F := hsubset
                have hfactor := pd5_labelBlockFactor_of_subsetFiber label v D.1 hDfiber
                have hOut' : pd5_labelNoCollision label
                    (B \ pd5_fiber label v B) := by simpa [O, F] using hOut
                have hNCiff := pd5_labelNoCollision_sdiff_iff label B D.1 v hDfiber hOut'
                rw [hfactor, hNCiff]
                simp [F, hDsubF]
            have hblockSum := pd5_fiberBlockSum_reindex B F a (by
              intro x hx
              exact (Finset.mem_filter.mp hx).1)
            rw [hrec, hbaseVal, hterms, hblockSum]
            by_cases hFtwo : F.card = 2
            · rw [if_pos (by omega : F.card ≤ 2)]
              rw [pd5_smallBlockCoeff_sum_two F a haF hFtwo]
              have hcoeff : pd5_cycleCoeff 1 = -1 := by
                norm_num [pd5_cycleCoeff]
              rw [hcoeff]
              norm_num
            · have hFlarge : 3 ≤ F.card := by omega
              rw [if_neg (by omega : ¬ F.card ≤ 2)]
              rw [pd5_smallBlockCoeff_sum F a haF hFlarge]
              simp
          · have hOutPair := pd5_exists_label_collision label O hOut
            rcases hOutPair with ⟨c, hcO, d, hdO, hcd, hcdLab, hcnone⟩
            have hcB := (Finset.mem_sdiff.mp hcO).1
            have hcNotF := (Finset.mem_sdiff.mp hcO).2
            have hdB := (Finset.mem_sdiff.mp hdO).1
            have hdNotF := (Finset.mem_sdiff.mp hdO).2
            have hcNeA : c ≠ a := by
              intro hca
              subst c
              exact hcNotF haF
            have hdNeA : d ≠ a := by
              intro hda
              subst d
              exact hdNotF haF
            have hBaseFalse : ¬ pd5_labelNoCollision label (B.erase a) := by
              intro hBase
              have hn := hBase c (Finset.mem_erase.mpr ⟨hcNeA, hcB⟩)
                d (Finset.mem_erase.mpr ⟨hdNeA, hdB⟩) hcd hcdLab
              exact hcnone hn
            have hltBase : (B.erase a).card < n := by
              rw [Finset.card_erase_of_mem ha, hcard]
              omega
            have hbaseIH := ih (B.erase a).card hltBase (B.erase a) rfl
            rw [if_neg hBaseFalse] at hbaseIH
            have hterms :
                (∑ D : PD5Block B a, ∑ C : PD5System (B \ D.1),
                  pd5_labelBlockFactor label D.1 *
                    pd5_systemProd (pd5_labelBlockFactor label) C.1) = 0 := by
              apply Fintype.sum_eq_zero
              intro D
              rcases pd5_labelBlockFactor_zero_or_subsetFiber label v hla D with hzero | hsubset
              · simp [hzero]
              · have hPairFalse : ¬ pd5_labelNoCollision label (B \ D.1) := by
                  intro hPair
                  have hcD : c ∉ D.1 := by intro hc; exact hcNotF (hsubset hc)
                  have hdD : d ∉ D.1 := by intro hd; exact hdNotF (hsubset hd)
                  exact hcnone (hPair c (Finset.mem_sdiff.mpr ⟨hcB, hcD⟩)
                    d (Finset.mem_sdiff.mpr ⟨hdB, hdD⟩) hcd hcdLab)
                have hltD : (B \ D.1).card < n := by
                  rw [← hcard]
                  exact pd5_sdiff_card_lt ha (pd5_block_props D).2.1
                have hcompIH := ih (B \ D.1).card hltD (B \ D.1) rfl
                rw [if_neg hPairFalse] at hcompIH
                unfold pd5_systemSum at hcompIH
                rw [← Finset.mul_sum, hcompIH]
                simp
            rw [hrec, hbaseIH, hterms]
            simp
  exact main A.card A rfl

theorem birth_partition_from_labels {K : ℕ} (A : Finset (BirthAddress K))
    (log : BirthLog K) (hnodup : (log.map Prod.fst).Nodup)
    (hA : ∀ e ∈ log, e.1 ∈ A) :
    distinctWeight log =
      ∑ C ∈ constraintSystems A,
        (constraintCoeff C : ℂ) * constraintWeight C log := by
  classical
  have hNC := pd5_labelNoCollision_iff_nodup log hnodup A hA
  have hfull := pd5_label_partition_full A (pd5_label log)
  have hlabelSum : distinctWeight log =
      pd5_systemSum A (pd5_labelBlockFactor (pd5_label log)) := by
    by_cases hN : pd5_labelNoCollision (pd5_label log) A
    · have hn := hNC.mp hN
      simpa [distinctWeight, hn, hN] using hfull.symm
    · have hn : ¬ (log.map Prod.snd).Nodup := by
        intro hh
        exact hN (hNC.mpr hh)
      simpa [distinctWeight, hn, hN] using hfull.symm
  have htransfer :
      pd5_systemSum A (pd5_labelBlockFactor (pd5_label log)) =
        pd5_systemSum A (pd5_blockFactor log) := by
    unfold pd5_systemSum pd5_systemProd
    apply Fintype.sum_congr
    intro C
    apply Finset.prod_congr rfl
    intro D hD
    exact pd5_labelBlockFactor_log log hnodup D
  calc
    distinctWeight log = pd5_systemSum A (pd5_labelBlockFactor (pd5_label log)) := hlabelSum
    _ = pd5_systemSum A (pd5_blockFactor log) := htransfer
    _ = ∑ C ∈ constraintSystems A,
          (constraintCoeff C : ℂ) * constraintWeight C log :=
        pd5_systemSum_partitionRhs A log



end

end ArtinPrimitiveRoots.TypeII.PD
