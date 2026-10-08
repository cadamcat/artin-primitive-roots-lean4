import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

noncomputable def pd5_blockPivot {K : ℕ} (D : Finset (BirthAddress K))
    (hD : 2 ≤ D.card) : {a // a ∈ D} := by
  classical
  have hpos : 0 < D.card := by omega
  exact Classical.choice (show Nonempty {a // a ∈ D} from by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    exact ⟨⟨a, ha⟩⟩)

def pd5_toA {K : ℕ} (A D : Finset (BirthAddress K)) (hsub : D ⊆ A)
    (a : {a // a ∈ D}) : A := ⟨a.1, hsub a.2⟩

noncomputable def pd5_blockPairs {K : ℕ} (A D : Finset (BirthAddress K))
    (hsub : D ⊆ A) (hD : 2 ≤ D.card) : Finset (A × A) := by
  classical
  let p := pd5_blockPivot D hD
  exact (D.attach.erase p).image fun b =>
    (pd5_toA A D hsub p, pd5_toA A D hsub b)

theorem pd5_blockPairs_card {K : ℕ} (A D : Finset (BirthAddress K))
    (hsub : D ⊆ A) (hD : 2 ≤ D.card) :
    (pd5_blockPairs A D hsub hD).card = D.card - 1 := by
  classical
  unfold pd5_blockPairs
  let p := pd5_blockPivot D hD
  have hinj : Function.Injective
      (fun b : {a // a ∈ D} => (pd5_toA A D hsub p, pd5_toA A D hsub b)) := by
    intro b c h
    apply Subtype.ext
    simpa [pd5_toA] using congrArg (fun z : A × A => z.2.1) h
  rw [Finset.card_image_of_injective _ hinj]
  rw [Finset.card_erase_of_mem]
  · simp
  · exact Finset.mem_attach _ _

theorem pd5_blockPairs_mem_iff {K : ℕ} (A D : Finset (BirthAddress K))
    (hsub : D ⊆ A) (hD : 2 ≤ D.card) (p : A × A) :
    p ∈ pd5_blockPairs A D hsub hD ↔
      ∃ b : {b // b ∈ D}, b ∈ D.attach.erase (pd5_blockPivot D hD) ∧
        p = (pd5_toA A D hsub (pd5_blockPivot D hD), pd5_toA A D hsub b) := by
  classical
  unfold pd5_blockPairs
  rw [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, hEq⟩
    exact ⟨b, hb, hEq.symm⟩
  · rintro ⟨b, hb, hEq⟩
    exact ⟨b, hb, hEq.symm⟩

noncomputable def pd5_systemPairs {K : ℕ} (A : Finset (BirthAddress K))
    (C : Finset (Finset (BirthAddress K))) (hC : IsConstraintSystem A C) :
    Finset (A × A) := by
  classical
  rcases hC with ⟨hblocks, hdisjoint⟩
  exact C.biUnion fun D => if hD : D ∈ C then
    pd5_blockPairs A D (hblocks D hD).1 (hblocks D hD).2 else ∅

theorem pd5_systemPairs_card {K : ℕ} (A : Finset (BirthAddress K))
    (C : Finset (Finset (BirthAddress K))) (hC : IsConstraintSystem A C) :
    (pd5_systemPairs A C hC).card = constraintRank C := by
  classical
  rcases hC with ⟨hblocks, hdisjoint⟩
  have hdisj : (C : Set (Finset (BirthAddress K))).PairwiseDisjoint
      (fun D => if hD : D ∈ C then
        pd5_blockPairs A D (hblocks D hD).1 (hblocks D hD).2 else ∅) := by
    intro D hD E hE hne
    have hDfin : D ∈ C := by simpa using hD
    have hEfin : E ∈ C := by simpa using hE
    change Disjoint
      (if hD' : D ∈ C then pd5_blockPairs A D (hblocks D hD').1 (hblocks D hD').2 else ∅)
      (if hE' : E ∈ C then pd5_blockPairs A E (hblocks E hE').1 (hblocks E hE').2 else ∅)
    rw [dif_pos hDfin, dif_pos hEfin]
    apply Finset.disjoint_left.mpr
    intro p hpD hpE
    rcases Finset.mem_image.mp hpD with ⟨b, hb, rfl⟩
    rcases Finset.mem_image.mp hpE with ⟨e, he, heq⟩
    have hpivEq : (pd5_blockPivot E (hblocks E hE).2).1 =
        (pd5_blockPivot D (hblocks D hD).2).1 := by
      have heqA := congrArg Prod.fst heq
      have hval := congrArg Subtype.val heqA
      simpa [pd5_toA] using hval
    have hshared : (pd5_blockPivot D (hblocks D hD).2).1 ∈ E := by
      rw [← hpivEq]
      exact (pd5_blockPivot E (hblocks E hE).2).2
    exact (Finset.disjoint_left.mp (hdisjoint D hD E hE hne))
      (pd5_blockPivot D (hblocks D hD).2).2 hshared
  change (C.biUnion (fun D => if hD : D ∈ C then
    pd5_blockPairs A D (hblocks D hD).1 (hblocks D hD).2 else ∅)).card = _
  rw [Finset.card_biUnion hdisj]
  unfold constraintRank
  apply Finset.sum_congr rfl
  intro D hD
  rw [dif_pos hD]
  exact pd5_blockPairs_card A D (hblocks D hD).1 (hblocks D hD).2

theorem pd5_systemPairs_mem_iff {K : ℕ} (A : Finset (BirthAddress K))
    (C : Finset (Finset (BirthAddress K))) (hC : IsConstraintSystem A C)
    (p : A × A) :
    p ∈ pd5_systemPairs A C hC ↔
      ∃ D : Finset (BirthAddress K), ∃ hD : D ∈ C,
        p ∈ pd5_blockPairs A D (hC.1 D hD).1 (hC.1 D hD).2 := by
  classical
  rcases hC with ⟨hblocks, hdisjoint⟩
  change p ∈ C.biUnion (fun D => if hD : D ∈ C then
    pd5_blockPairs A D (hblocks D hD).1 (hblocks D hD).2 else ∅) ↔
    ∃ D : Finset (BirthAddress K), ∃ hD : D ∈ C,
      p ∈ pd5_blockPairs A D (hblocks D hD).1 (hblocks D hD).2
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨D, hD, hp⟩
    exact ⟨D, hD, by simpa [hD] using hp⟩
  · rintro ⟨D, hD, hp⟩
    exact ⟨D, hD, by simpa [hD] using hp⟩

theorem pd5_systemPairs_subset {K : ℕ} (A : Finset (BirthAddress K))
    (C C' : Finset (Finset (BirthAddress K)))
    (hC : IsConstraintSystem A C) (hC' : IsConstraintSystem A C')
    (hPairs : pd5_systemPairs A C hC = pd5_systemPairs A C' hC') : C ⊆ C' := by
  classical
  rcases hC with ⟨hblocks, hdisjoint⟩
  rcases hC' with ⟨hblocks', hdisjoint'⟩
  intro D hD
  have hDprops := hblocks D hD
  let p := pd5_blockPivot D hDprops.2
  have hnp : ∃ b ∈ D, b ≠ p.1 := by
    by_contra h
    push_neg at h
    have hsub : D ⊆ {p.1} := by
      intro a ha
      simp only [Finset.mem_singleton]
      exact h a ha
    have hcard := Finset.card_le_card hsub
    simp at hcard
    omega
  obtain ⟨b, hbD, hbp⟩ := hnp
  let bsub : {a // a ∈ D} := ⟨b, hbD⟩
  have hbErase : bsub ∈ D.attach.erase p := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_attach _ _⟩
    intro heq
    exact hbp (congrArg Subtype.val heq)
  let pairD : A × A :=
    (pd5_toA A D hDprops.1 p, pd5_toA A D hDprops.1 bsub)
  have hpairBlockD : pairD ∈ pd5_blockPairs A D hDprops.1 hDprops.2 := by
    apply (pd5_blockPairs_mem_iff A D hDprops.1 hDprops.2 pairD).2
    exact ⟨bsub, hbErase, rfl⟩
  have hpairD : pairD ∈ pd5_systemPairs A C ⟨hblocks, hdisjoint⟩ :=
    (pd5_systemPairs_mem_iff A C ⟨hblocks, hdisjoint⟩ pairD).2 ⟨D, hD, hpairBlockD⟩
  have hpairD' : pairD ∈ pd5_systemPairs A C' ⟨hblocks', hdisjoint'⟩ := by
    rw [← hPairs]
    exact hpairD
  rcases (pd5_systemPairs_mem_iff A C' ⟨hblocks', hdisjoint'⟩ pairD).1 hpairD'
      with ⟨E, hE, hpairBlockE⟩
  have hEprops := hblocks' E hE
  rcases (pd5_blockPairs_mem_iff A E hEprops.1 hEprops.2 pairD).1 hpairBlockE
      with ⟨e, heErase, heq⟩
  let pe := pd5_blockPivot E hEprops.2
  have hpEq : pe.1 = p.1 := by
    have heqA : pd5_toA A E hEprops.1 pe = pd5_toA A D hDprops.1 p := by
      simpa [pairD] using (congrArg Prod.fst heq).symm
    have hval := congrArg Subtype.val heqA
    simpa [pd5_toA] using hval
  have hpE : p.1 ∈ E := by
    rw [← hpEq]
    exact pe.2
  have hDE : D ⊆ E := by
    intro x hx
    by_cases hxp : x = p.1
    · simpa [hxp] using hpE
    · let xsub : {a // a ∈ D} := ⟨x, hx⟩
      have hxErase : xsub ∈ D.attach.erase p := by
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_attach _ _⟩
        intro heq
        exact hxp (congrArg Subtype.val heq)
      let pairX : A × A :=
        (pd5_toA A D hDprops.1 p, pd5_toA A D hDprops.1 xsub)
      have hpairBlockX : pairX ∈ pd5_blockPairs A D hDprops.1 hDprops.2 := by
        apply (pd5_blockPairs_mem_iff A D hDprops.1 hDprops.2 pairX).2
        exact ⟨xsub, hxErase, rfl⟩
      have hpairX : pairX ∈ pd5_systemPairs A C ⟨hblocks, hdisjoint⟩ :=
        (pd5_systemPairs_mem_iff A C ⟨hblocks, hdisjoint⟩ pairX).2 ⟨D, hD, hpairBlockX⟩
      have hpairX' : pairX ∈ pd5_systemPairs A C' ⟨hblocks', hdisjoint'⟩ := by
        rw [← hPairs]
        exact hpairX
      rcases (pd5_systemPairs_mem_iff A C' ⟨hblocks', hdisjoint'⟩ pairX).1 hpairX'
          with ⟨E', hE', hpairBlockE'⟩
      have hE'props := hblocks' E' hE'
      rcases (pd5_blockPairs_mem_iff A E' hE'props.1 hE'props.2 pairX).1 hpairBlockE'
          with ⟨e', he'Erase, heq'⟩
      let pe' := pd5_blockPivot E' hE'props.2
      have hpEq' : pe'.1 = p.1 := by
        have heqA : pd5_toA A E' hE'props.1 pe' = pd5_toA A D hDprops.1 p := by
          simpa [pairX] using (congrArg Prod.fst heq').symm
        have hval := congrArg Subtype.val heqA
        simpa [pd5_toA] using hval
      have hpE' : p.1 ∈ E' := by
        rw [← hpEq']
        exact pe'.2
      have hEE' : E' = E := by
        by_contra hne
        exact (Finset.disjoint_left.mp (hdisjoint' E' hE' E hE hne)) hpE' hpE
      have hxE' : x ∈ E' := by
        have hval : x = e'.1 := by
          have hsecond := congrArg (fun z : A × A => z.2.1) heq'
          simpa [pairX, pd5_toA] using hsecond
        rw [hval]
        exact e'.2
      simpa [hEE'] using hxE'
  have hED : E ⊆ D := by
    intro y hy
    by_cases hyp : y = p.1
    · simpa [hyp] using p.2
    · let ysub : {a // a ∈ E} := ⟨y, hy⟩
      have hyErase : ysub ∈ E.attach.erase pe := by
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_attach _ _⟩
        intro heq
        apply hyp
        calc
          y = ysub.1 := rfl
          _ = pe.1 := congrArg Subtype.val heq
          _ = p.1 := hpEq
      let pairY : A × A :=
        (pd5_toA A E hEprops.1 pe, pd5_toA A E hEprops.1 ysub)
      have hpairBlockY : pairY ∈ pd5_blockPairs A E hEprops.1 hEprops.2 := by
        apply (pd5_blockPairs_mem_iff A E hEprops.1 hEprops.2 pairY).2
        exact ⟨ysub, hyErase, rfl⟩
      have hpairY : pairY ∈ pd5_systemPairs A C' ⟨hblocks', hdisjoint'⟩ :=
        (pd5_systemPairs_mem_iff A C' ⟨hblocks', hdisjoint'⟩ pairY).2 ⟨E, hE, hpairBlockY⟩
      have hpairY' : pairY ∈ pd5_systemPairs A C ⟨hblocks, hdisjoint⟩ := by
        rw [hPairs]
        exact hpairY
      rcases (pd5_systemPairs_mem_iff A C ⟨hblocks, hdisjoint⟩ pairY).1 hpairY'
          with ⟨D', hD', hpairBlockD'⟩
      have hD'props := hblocks D' hD'
      rcases (pd5_blockPairs_mem_iff A D' hD'props.1 hD'props.2 pairY).1 hpairBlockD'
          with ⟨d', hd'Erase, hdEq⟩
      let pd' := pd5_blockPivot D' hD'props.2
      have hpEq'' : pd'.1 = p.1 := by
        have heqA : pd5_toA A D' hD'props.1 pd' = pd5_toA A E hEprops.1 pe := by
          simpa [pairY] using (congrArg Prod.fst hdEq).symm
        have hval := congrArg Subtype.val heqA
        simpa [pd5_toA] using hval.trans hpEq
      have hpD' : p.1 ∈ D' := by
        rw [← hpEq'']
        exact pd'.2
      have hDD' : D' = D := by
        by_contra hne
        exact (Finset.disjoint_left.mp (hdisjoint D' hD' D hD hne)) hpD' p.2
      have hyD' : y ∈ D' := by
        have hval : y = d'.1 := by
          have hsecond := congrArg (fun z : A × A => z.2.1) hdEq
          simpa [pairY, pd5_toA] using hsecond
        rw [hval]
        exact d'.2
      simpa [hDD'] using hyD'
  have hDEq : D = E := Finset.Subset.antisymm hDE hED
  rw [hDEq]
  exact hE

noncomputable def pd5_pairVector {α : Type*} [DecidableEq α] (P : Finset α)
    {r : ℕ} (hP : P.card = r) : Fin r → α :=
  fun i => ((P.equivFinOfCardEq hP).symm i).1

theorem pd5_pairVector_injective_on_sets {α : Type*} [DecidableEq α] {r : ℕ}
    {P Q : Finset α} (hP : P.card = r) (hQ : Q.card = r)
    (h : pd5_pairVector P hP = pd5_pairVector Q hQ) : P = Q := by
  classical
  apply Finset.ext
  intro a
  constructor
  · intro ha
    let i := P.equivFinOfCardEq hP ⟨a, ha⟩
    have hleft : pd5_pairVector P hP i = a := by
      simp [pd5_pairVector, i]
    have hright : pd5_pairVector Q hQ i = a := by
      rw [← congrFun h i]
      exact hleft
    rw [← hright]
    exact ((Q.equivFinOfCardEq hQ).symm i).2
  · intro ha
    let i := Q.equivFinOfCardEq hQ ⟨a, ha⟩
    have hright : pd5_pairVector Q hQ i = a := by
      simp [pd5_pairVector, i]
    have hleft : pd5_pairVector P hP i = a := by
      rw [congrFun h i]
      exact hright
    rw [← hleft]
    exact ((P.equivFinOfCardEq hP).symm i).2

theorem pd5_systemPairs_injective {K : ℕ} (A : Finset (BirthAddress K))
    {C C' : Finset (Finset (BirthAddress K))}
    (hC : IsConstraintSystem A C) (hC' : IsConstraintSystem A C')
    (hPairs : pd5_systemPairs A C hC = pd5_systemPairs A C' hC') : C = C' := by
  apply Finset.Subset.antisymm
  · exact pd5_systemPairs_subset A C C' hC hC' hPairs
  · exact pd5_systemPairs_subset A C' C hC' hC hPairs.symm

theorem pd5_constraint_system_rank_card_le {K : ℕ} (A : Finset (BirthAddress K))
    (r : ℕ) :
    ((constraintSystems A).filter (fun C => constraintRank C = r)).card ≤
      (max 1 A.card) ^ (2 * r) := by
  classical
  let Sys := (constraintSystems A).filter (fun C => constraintRank C = r)
  let encode : {C : Finset (Finset (BirthAddress K)) // C ∈ Sys} →
      (Fin r → A × A) := fun C =>
    let hsys := (Finset.mem_filter.mp C.2).1
    let hrank := (Finset.mem_filter.mp C.2).2
    pd5_pairVector (pd5_systemPairs A C.1 ((Finset.mem_filter.mp hsys).2)) (by
      rw [pd5_systemPairs_card]
      exact hrank)
  have hencode : Function.Injective encode := by
    intro C D h
    apply Subtype.ext
    have hsysC := (Finset.mem_filter.mp C.2).1
    have hsysD := (Finset.mem_filter.mp D.2).1
    apply pd5_systemPairs_injective A ((Finset.mem_filter.mp hsysC).2)
      ((Finset.mem_filter.mp hsysD).2)
    exact pd5_pairVector_injective_on_sets
      (by rw [pd5_systemPairs_card]; exact (Finset.mem_filter.mp C.2).2)
      (by rw [pd5_systemPairs_card]; exact (Finset.mem_filter.mp D.2).2) h
  calc
    Sys.card ≤ Fintype.card (Fin r → A × A) := by
      have h := Fintype.card_le_of_injective encode hencode
      simpa [Sys] using h
    _ = A.card ^ (2 * r) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_coe]
      rw [← pow_two, pow_mul]
    _ ≤ (max 1 A.card) ^ (2 * r) :=
      Nat.pow_le_pow_left (Nat.le_max_right 1 A.card) _

/-- The addresses used by a constraint system are at most twice its rank. -/
theorem pd5_constraint_support_card_le_twice_rank {K : ℕ}
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) :
    (C.biUnion id).card ≤ 2 * constraintRank C := by
  classical
  have hsystem : IsConstraintSystem A C := (Finset.mem_filter.mp hC).2
  calc
    (C.biUnion id).card ≤ ∑ D ∈ C, D.card := Finset.card_biUnion_le
    _ ≤ ∑ D ∈ C, 2 * (D.card - 1) := by
      apply Finset.sum_le_sum
      intro D hD
      have hsize : 2 ≤ D.card := (hsystem.1 D hD).2
      omega
    _ = 2 * constraintRank C := by
      simp [constraintRank, Finset.mul_sum]

/-- Disjoint blocks imply that the system rank is at most the number of used addresses. -/
theorem pd5_constraint_rank_le_support_card {K : ℕ}
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) :
    constraintRank C ≤ (C.biUnion id).card := by
  classical
  have hsystem : IsConstraintSystem A C := (Finset.mem_filter.mp hC).2
  have hdisj : (C : Set (Finset (BirthAddress K))).PairwiseDisjoint id := by
    intro D hD E hE hne
    exact hsystem.2 D hD E hE hne
  rw [Finset.card_biUnion hdisj]
  unfold constraintRank
  apply Finset.sum_le_sum
  intro D hD
  change D.card - 1 ≤ D.card
  exact Nat.sub_le _ _

/-- Every address used by a constraint system belongs to its ambient address set. -/
theorem pd5_constraint_support_subset {K : ℕ}
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) :
    C.biUnion id ⊆ A := by
  classical
  have hsystem : IsConstraintSystem A C := (Finset.mem_filter.mp hC).2
  intro a ha
  rcases Finset.mem_biUnion.mp ha with ⟨D, hD, haD⟩
  exact (hsystem.1 D hD).1 haD

/-- The rank of a system is bounded by the size of its address set. -/
theorem pd5_constraint_rank_le_address_card {K : ℕ}
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) : constraintRank C ≤ A.card := by
  exact (pd5_constraint_rank_le_support_card hC).trans
    (Finset.card_le_card (pd5_constraint_support_subset hC))

/-- A single system's coefficient grows at most exponentially in its rank and `|A|`. -/
theorem pd5_constraint_coeff_norm_le {K : ℕ}
    {A : Finset (BirthAddress K)} {C : Finset (Finset (BirthAddress K))}
    (hC : C ∈ constraintSystems A) :
    |(constraintCoeff C : ℝ)| ≤ (max 1 A.card : ℝ) ^ constraintRank C := by
  classical
  have hsystem : IsConstraintSystem A C := (Finset.mem_filter.mp hC).2
  let Q : ℕ := max 1 A.card
  have hQ : 1 ≤ Q := by simp [Q]
  have hfactor (D : Finset (BirthAddress K)) (hD : D ∈ C) :
      ((D.card - 1).factorial : ℝ) ≤ (Q : ℝ) ^ (D.card - 1) := by
    have hsub : D ⊆ A := (hsystem.1 D hD).1
    have hsize : D.card ≤ A.card := Finset.card_le_card hsub
    have hn : D.card - 1 ≤ Q := by
      dsimp [Q]
      omega
    have hfac := Nat.factorial_le_pow (D.card - 1)
    have hpow : (D.card - 1) ^ (D.card - 1) ≤ Q ^ (D.card - 1) :=
      Nat.pow_le_pow_left hn _
    exact_mod_cast hfac.trans hpow
  have hcoeff : |(constraintCoeff C : ℝ)| =
      ∏ D ∈ C, ((D.card - 1).factorial : ℝ) := by
    simp [constraintCoeff, Finset.abs_prod, abs_mul, abs_pow]
  calc
    |(constraintCoeff C : ℝ)| = ∏ D ∈ C, ((D.card - 1).factorial : ℝ) := hcoeff
    _ ≤ ∏ D ∈ C, (Q : ℝ) ^ (D.card - 1) := by
      apply Finset.prod_le_prod₀
      · intro D hD
        exact Nat.cast_nonneg _
      · intro D hD
        exact hfactor D hD
    _ = (max 1 A.card : ℝ) ^ constraintRank C := by
      rw [Finset.prod_pow_eq_pow_sum]
      simp [constraintRank, Q]

theorem pd5_constraint_coeff_mass_le {K : ℕ} (A : Finset (BirthAddress K))
    (r : ℕ) :
    (∑ C ∈ (constraintSystems A).filter (fun C => constraintRank C = r),
      |(constraintCoeff C : ℝ)|) ≤ (max 1 A.card : ℝ) ^ (3 * r) := by
  classical
  let Sys := (constraintSystems A).filter (fun C => constraintRank C = r)
  let Q : ℕ := max 1 A.card
  have hterm {C : Finset (Finset (BirthAddress K))} (hC : C ∈ Sys) :
      |(constraintCoeff C : ℝ)| ≤ (Q : ℝ) ^ r := by
    have hsys : C ∈ constraintSystems A := (Finset.mem_filter.mp hC).1
    have hrank : constraintRank C = r := (Finset.mem_filter.mp hC).2
    calc
      |(constraintCoeff C : ℝ)| ≤ (max 1 A.card : ℝ) ^ constraintRank C :=
        pd5_constraint_coeff_norm_le hsys
      _ = (Q : ℝ) ^ r := by simp [Q, hrank]
  have hcard : Sys.card ≤ Q ^ (2 * r) := by
    simpa [Sys, Q] using pd5_constraint_system_rank_card_le A r
  calc
    (∑ C ∈ Sys, |(constraintCoeff C : ℝ)|) ≤ ∑ C ∈ Sys, (Q : ℝ) ^ r := by
      apply Finset.sum_le_sum
      intro C hC
      exact hterm hC
    _ = (Sys.card : ℝ) * (Q : ℝ) ^ r := by simp [Sys]
    _ ≤ ((Q ^ (2 * r) : ℕ) : ℝ) * (Q : ℝ) ^ r := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg (by positivity) _)
    _ = (Q : ℝ) ^ (3 * r) := by
      rw [Nat.cast_pow]
      rw [← pow_add]
      congr 1
      omega
    _ = (max 1 A.card : ℝ) ^ (3 * r) := by simp [Q]

theorem pd5_constraint_sum_group_by_rank {K : ℕ} (A : Finset (BirthAddress K))
    (r₀ : ℕ) (f : Finset (Finset (BirthAddress K)) → ℝ) :
    (∑ C ∈ (constraintSystems A).filter (fun C => constraintRank C < r₀), f C) =
      ∑ r ∈ Finset.range r₀,
        ∑ C ∈ (constraintSystems A).filter (fun C => constraintRank C = r), f C := by
  classical
  let systems := constraintSystems A
  let low := systems.filter (fun C => constraintRank C < r₀)
  have hmaps : ∀ C ∈ low, constraintRank C ∈ Finset.range r₀ := by
    intro C hC
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hC).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun C => f C)]
  apply Finset.sum_congr rfl
  intro r hr
  have hfilter : low.filter (fun C => constraintRank C = r) =
      systems.filter (fun C => constraintRank C = r) := by
    change ((constraintSystems A).filter (fun C => constraintRank C < r₀)).filter
        (fun C => constraintRank C = r) =
      (constraintSystems A).filter (fun C => constraintRank C = r)
    ext C
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hC, hlow⟩, hrank⟩
      exact ⟨hC, hrank⟩
    · rintro ⟨hC, hrank⟩
      refine ⟨⟨hC, ?_⟩, hrank⟩
      rw [hrank]
      exact Finset.mem_range.mp hr
  rw [hfilter]

end

end ArtinPrimitiveRoots.TypeII.PD
