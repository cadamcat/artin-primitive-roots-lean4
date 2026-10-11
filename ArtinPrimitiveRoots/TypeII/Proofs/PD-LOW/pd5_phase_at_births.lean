import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».pd5_fourier_birth_constraints

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

private theorem pd5_low_a_stdAddChar_sum {T : ℕ} [NeZero T] {α : Type*}
    [DecidableEq α] (s : Finset α) (f : α → ZMod T) :
    ZMod.stdAddChar (∑ a ∈ s, f a) = ∏ a ∈ s, ZMod.stdAddChar (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha,
        AddChar.map_add_eq_mul, ih]

private theorem pd5_low_a_fintype_mul_sum {α : Type*} [Fintype α]
    (c : ℂ) (f : α → ℂ) : c * (∑ a, f a) = ∑ a, c * f a := by
  simpa using (Finset.mul_sum (s := (Finset.univ : Finset α)) f c)

private theorem pd5_low_a_label_append_left {K : ℕ} (L₁ L₂ : BirthLog K)
    (hN₁ : (L₁.map Prod.fst).Nodup)
    (hN : ((L₁ ++ L₂).map Prod.fst).Nodup)
    (P : Finset (BirthAddress K)) (a : BirthAddress K) (ha : a ∈ P)
    (h₂ : ∀ e ∈ L₂, e.1 ∉ P) :
    pd5b_label (L₁ ++ L₂) a = pd5b_label L₁ a := by
  classical
  cases h₁ : pd5b_label L₁ a with
  | some p =>
      have hp₁ : (a, p) ∈ L₁ := (pd5b_label_spec hN₁ a p).1 h₁
      have hp : (a, p) ∈ L₁ ++ L₂ := List.mem_append.mpr (Or.inl hp₁)
      exact (pd5b_label_spec hN a p).2 hp
  | none =>
      have hnone₁ : ∀ p, (a, p) ∉ L₁ := by
        intro p hp
        have heq := (pd5b_label_spec hN₁ a p).2 hp
        rw [h₁] at heq
        cases heq
      have hnone₂ : ∀ p, (a, p) ∉ L₂ := by
        intro p hp
        have he := h₂ (a, p) hp
        exact he ha
      have hnone : ∀ p, (a, p) ∉ L₁ ++ L₂ := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hnone₁ p hp
        · exact hnone₂ p hp
      cases h : pd5b_label (L₁ ++ L₂) a with
      | none => rfl
      | some p => exact (hnone p ((pd5b_label_spec hN a p).1 h)).elim

private theorem pd5_low_a_label_append_right {K : ℕ} (L₁ L₂ : BirthLog K)
    (hN₂ : (L₂.map Prod.fst).Nodup)
    (hN : ((L₁ ++ L₂).map Prod.fst).Nodup)
    (P : Finset (BirthAddress K)) (a : BirthAddress K) (ha : a ∈ P)
    (h₁ : ∀ e ∈ L₁, e.1 ∉ P) :
    pd5b_label (L₁ ++ L₂) a = pd5b_label L₂ a := by
  classical
  cases h₂ : pd5b_label L₂ a with
  | some p =>
      have hp₂ : (a, p) ∈ L₂ := (pd5b_label_spec hN₂ a p).1 h₂
      have hp : (a, p) ∈ L₁ ++ L₂ := List.mem_append.mpr (Or.inr hp₂)
      exact (pd5b_label_spec hN a p).2 hp
  | none =>
      have hnone₂ : ∀ p, (a, p) ∉ L₂ := by
        intro p hp
        have heq := (pd5b_label_spec hN₂ a p).2 hp
        rw [h₂] at heq
        cases heq
      have hnone₁ : ∀ p, (a, p) ∉ L₁ := by
        intro p hp
        have he := h₁ (a, p) hp
        exact he ha
      have hnone : ∀ p, (a, p) ∉ L₁ ++ L₂ := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hnone₁ p hp
        · exact hnone₂ p hp
      cases h : pd5b_label (L₁ ++ L₂) a with
      | none => rfl
      | some p => exact (hnone p ((pd5b_label_spec hN a p).1 h)).elim

private theorem pd5_low_a_birthPhaseWeight_append_split {K : ℕ}
    (Q R : Finset (BirthAddress K)) (φ : BirthAddress K → ℕ → ℂ)
    (L₁ L₂ : BirthLog K)
    (hQR : Disjoint Q R)
    (hN₁ : (L₁.map Prod.fst).Nodup) (hN₂ : (L₂.map Prod.fst).Nodup)
    (hN : ((L₁ ++ L₂).map Prod.fst).Nodup)
    (hL₂ : ∀ e ∈ L₂, e.1 ∉ Q) (hL₁ : ∀ e ∈ L₁, e.1 ∉ R) :
    pd5_birthPhaseWeight (Q ∪ R) φ (L₁ ++ L₂) =
      pd5_birthPhaseWeight Q φ L₁ * pd5_birthPhaseWeight R φ L₂ := by
  classical
  unfold pd5_birthPhaseWeight
  unfold pd5_addressPhase
  rw [Finset.prod_union hQR]
  congr 1
  · apply Finset.prod_congr rfl
    intro a ha
    rw [pd5_low_a_label_append_left L₁ L₂ hN₁ hN Q a ha hL₂]
  · apply Finset.prod_congr rfl
    intro a ha
    rw [pd5_low_a_label_append_right L₁ L₂ hN₂ hN R a ha hL₁]

private def pd5_phasePastAddresses {K : ℕ} (x : ℝ) (B m : ℕ) :
    Finset (BirthAddress K) :=
  pd5_initialAddresses x K ∪
    (Finset.range m).biUnion (fun j => pd5_edgeAddresses K j ∩ birthAddresses x K B) ∪
      (Finset.range m).biUnion (fun j => pd5_ghostAddresses K j B ∩ birthAddresses x K B)

private theorem pd5_phasePastAddresses_zero {K : ℕ} (x : ℝ) (B : ℕ) :
    pd5_phasePastAddresses x B 0 = pd5_initialAddresses x K := by
  simp [pd5_phasePastAddresses]

private theorem pd5_phasePastAddresses_succ {K : ℕ} (x : ℝ) (B m : ℕ) :
    pd5_phasePastAddresses x B (m + 1) =
    pd5_phasePastAddresses x B m ∪
      (pd5_edgeAddresses K m ∩ birthAddresses x K B) ∪
        (pd5_ghostAddresses K m B ∩ birthAddresses x K B) := by
  classical
  have hrange : Finset.range (m + 1) = insert m (Finset.range m) := by
    ext j
    simp
    omega
  rw [pd5_phasePastAddresses, pd5_phasePastAddresses, hrange,
    Finset.biUnion_insert, Finset.biUnion_insert]
  simp [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]

private theorem pd5_phasePastAddresses_all {K : ℕ} (x : ℝ) (B N : ℕ)
    (hN : N = pathLength x) :
    birthAddresses x K B =
      pd5_phasePastAddresses x B N ∪ pd5_ghostAddresses K N B := by
  classical
  ext a
  cases a with
  | initial i j =>
      simp [pd5_phasePastAddresses, birthAddresses, pd5_initialAddresses,
        pd5_edgeAddresses, pd5_ghostAddresses]
  | edge j i =>
      subst hN
      simp [pd5_phasePastAddresses, birthAddresses, pd5_initialAddresses,
        pd5_edgeAddresses, pd5_ghostAddresses]
  | ghost j i k =>
      subst hN
      simp [pd5_phasePastAddresses, birthAddresses, pd5_initialAddresses,
        pd5_edgeAddresses, pd5_ghostAddresses]
      omega

private def pd5_phaseGhostPrefixAddresses {K : ℕ} (x : ℝ) (B m : ℕ) :
    Finset (BirthAddress K) :=
  pd5_phasePastAddresses x B m ∪
    (pd5_ghostAddresses K m B ∩ birthAddresses x K B)

private theorem pd5_phasePastAddresses_succ_ghost_edge {K : ℕ}
    (x : ℝ) (B m : ℕ) :
    pd5_phasePastAddresses x B (m + 1) =
      pd5_phaseGhostPrefixAddresses x B m ∪
        (pd5_edgeAddresses K m ∩ birthAddresses x K B) := by
  rw [pd5_phasePastAddresses_succ]
  simp [pd5_phaseGhostPrefixAddresses, Finset.union_assoc,
    Finset.union_left_comm, Finset.union_comm]

private theorem pd5_phasePast_disjoint_ghost {K : ℕ} (x : ℝ) (B m : ℕ) :
    Disjoint (pd5_phasePastAddresses x B m)
      (pd5_ghostAddresses K m B ∩ birthAddresses x K B) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  cases a with
  | initial i j =>
      simp [pd5_phasePastAddresses, pd5_initialAddresses,
        pd5_ghostAddresses] at hb
  | edge j i =>
      simp [pd5_phasePastAddresses, pd5_ghostAddresses] at hb
  | ghost j i k =>
      simp [pd5_phasePastAddresses, pd5_initialAddresses, pd5_edgeAddresses,
        pd5_ghostAddresses] at ha hb
      omega

private theorem pd5_phasePast_disjoint_edge {K : ℕ} (x : ℝ) (B m : ℕ) :
    Disjoint (pd5_phasePastAddresses x B m)
      (pd5_edgeAddresses K m ∩ birthAddresses x K B) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  cases a with
  | initial i j =>
      simp [pd5_phasePastAddresses, pd5_initialAddresses, pd5_edgeAddresses] at hb
  | edge j i =>
      simp [pd5_phasePastAddresses, pd5_initialAddresses, pd5_edgeAddresses,
        pd5_ghostAddresses] at ha hb
      omega
  | ghost j i k =>
      simp [pd5_phasePastAddresses, pd5_edgeAddresses] at hb

private theorem pd5_phaseGhost_disjoint_edge {K : ℕ} (x : ℝ) (B m : ℕ) :
    Disjoint (pd5_ghostAddresses K m B ∩ birthAddresses x K B)
      (pd5_edgeAddresses K m ∩ birthAddresses x K B) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  cases a <;> simp [pd5_ghostAddresses, pd5_edgeAddresses] at ha hb

private def pd5_phasePastWeight {K : ℕ} (U Past : Finset (BirthAddress K))
    (φ : BirthAddress K → ℕ → ℂ) (L : BirthLog K) : ℂ :=
  pd5_birthPhaseWeight (U ∩ Past) φ L

private theorem pd5_low_a_ghostLog_nodup {K : ℕ} {x : ℝ} {B m : ℕ}
    {L : BirthLog K} (hL : pd5_logPrefixGood x B m m L)
    (F : PDFix K) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand x (F.a i)) :
    ((L ++ pd5_ghostBirthLog m l (fun i k => (new i k : ℕ))).map Prod.fst).Nodup := by
  have hG : (pd5_ghostBirthLog m l (fun i k => (new i k : ℕ))).map Prod.fst |>.Nodup := by
    rw [pd5_ghostBirthLog_map_fst]
    exact pd5_ghostAddressList_nodup m l
  have hdis : List.Disjoint (L.map Prod.fst)
      ((pd5_ghostBirthLog m l (fun i k => (new i k : ℕ))).map Prod.fst) := by
    rw [pd5_ghostBirthLog_map_fst]
    apply List.disjoint_left.mpr
    intro a ha hb
    exact (pd5_logPrefixGood_disjoint_ghost hL a ha a hb) rfl
  rw [List.map_append]
  exact List.Nodup.append hL.1 hG hdis

private theorem pd5_low_a_ghostLog_address_step {K : ℕ} (m : ℕ)
    (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → ℕ)
    {e : BirthAddress K × ℕ}
    (he : e ∈ pd5_ghostBirthLog m l new) :
    ∃ i k, e.1 = BirthAddress.ghost m i k := by
  unfold pd5_ghostBirthLog at he
  simp only [List.mem_flatMap, List.mem_ofFn] at he
  rcases he with ⟨i, hi, k, hk, heq⟩
  exact ⟨i, k.val, by simpa using congrArg Prod.fst heq⟩

private theorem pd5_low_a_edgeLog_address_step {K : ℕ} (F : PDFix K) (S : PDScale)
    (m : ℕ) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    {e : BirthAddress K × ℕ} (he : e ∈ edgeBirths F S m s c) :
    ∃ i, e.1 = BirthAddress.edge m i := by
  have ha : e.1 ∈ (edgeBirths F S m s c).map Prod.fst :=
    List.mem_map.mpr ⟨e, he, rfl⟩
  unfold edgeBirths at ha
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    List.map_nil, List.map_cons, Prod.fst] at ha
  rcases List.mem_flatMap.mp ha with ⟨i, hi, ha⟩
  cases h : (c i).2 with
  | inl k => simp [h] at ha
  | inr p =>
      have heq : e.1 = BirthAddress.edge m i := by simpa [h] using ha
      exact ⟨i, heq⟩

private theorem pd5_low_a_prefixGood_memPast {K : ℕ} {x : ℝ} {B m : ℕ}
    {L : BirthLog K} (hL : pd5_logPrefixGood x B m m L) :
    ∀ e ∈ L, e.1 ∈ pd5_phasePastAddresses x B m := by
  intro e he
  rcases hL.2 e he with ⟨hpre, hbirth⟩
  cases ha : e.1 with
  | initial i j =>
      have hbirth' : BirthAddress.initial i j ∈ birthAddresses x K B := by
        simpa [ha] using hbirth
      have hj : j < slotCount x := by
        simpa [birthAddresses] using hbirth'
      have hinit : BirthAddress.initial i j ∈ pd5_initialAddresses x K := by
        simp [pd5_initialAddresses, hj]
      simp [pd5_phasePastAddresses, hinit]
  | edge j i =>
      have hpre' : pd5_prefixAddress B m m (BirthAddress.edge j i) := by
        simpa [ha] using hpre
      have hbirth' : BirthAddress.edge j i ∈ birthAddresses x K B := by
        simpa [ha] using hbirth
      have hstep : j < m := by simpa [pd5_prefixAddress] using hpre'
      have hed : BirthAddress.edge j i ∈ pd5_edgeAddresses K j := by
        simp [pd5_edgeAddresses]
      have hpast : BirthAddress.edge j i ∈
          (Finset.range m).biUnion (fun n =>
            pd5_edgeAddresses K n ∩ birthAddresses x K B) :=
        Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hstep,
          Finset.mem_inter.mpr ⟨hed, hbirth'⟩⟩
      simp [pd5_phasePastAddresses, hpast]
  | ghost j i k =>
      have hpre' : pd5_prefixAddress B m m (BirthAddress.ghost j i k) := by
        simpa [ha] using hpre
      have hbirth' : BirthAddress.ghost j i k ∈ birthAddresses x K B := by
        simpa [ha] using hbirth
      have hstep : j < m ∧ k < B := by simpa [pd5_prefixAddress] using hpre'
      have hghost : BirthAddress.ghost j i k ∈ pd5_ghostAddresses K j B := by
        simp [pd5_ghostAddresses, hstep.2]
      have hpast : BirthAddress.ghost j i k ∈
          (Finset.range m).biUnion (fun n =>
            pd5_ghostAddresses K n B ∩ birthAddresses x K B) :=
        Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hstep.1,
          Finset.mem_inter.mpr ⟨hghost, hbirth'⟩⟩
      simp [pd5_phasePastAddresses, hpast]

private theorem pd5_low_a_prefixGood_memGhostPrefix {K : ℕ} {x : ℝ} {B m : ℕ}
    {L : BirthLog K} (hL : pd5_logPrefixGood x B m (m + 1) L) :
    ∀ e ∈ L, e.1 ∈ pd5_phaseGhostPrefixAddresses x B m := by
  intro e he
  rcases hL.2 e he with ⟨hpre, hbirth⟩
  cases ha : e.1 with
  | initial i j =>
      have hbirth' : BirthAddress.initial i j ∈ birthAddresses x K B := by
        simpa [ha] using hbirth
      have hj : j < slotCount x := by simpa [birthAddresses] using hbirth'
      have hinit : BirthAddress.initial i j ∈ pd5_initialAddresses x K := by
        simp [pd5_initialAddresses, hj]
      simp [pd5_phaseGhostPrefixAddresses, pd5_phasePastAddresses, hinit]
  | edge j i =>
      have hpre' : pd5_prefixAddress B m (m + 1) (BirthAddress.edge j i) := by
        simpa [ha] using hpre
      have hbirth' : BirthAddress.edge j i ∈ birthAddresses x K B := by
        simpa [ha] using hbirth
      have hj : j < m := by simpa [pd5_prefixAddress] using hpre'
      have hed : BirthAddress.edge j i ∈ pd5_edgeAddresses K j := by
        simp [pd5_edgeAddresses]
      have hpast : BirthAddress.edge j i ∈
          (Finset.range m).biUnion (fun n =>
            pd5_edgeAddresses K n ∩ birthAddresses x K B) :=
        Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
          Finset.mem_inter.mpr ⟨hed, hbirth'⟩⟩
      simp [pd5_phaseGhostPrefixAddresses, pd5_phasePastAddresses, hpast]
  | ghost j i k =>
      have hpre' : pd5_prefixAddress B m (m + 1) (BirthAddress.ghost j i k) := by
        simpa [ha] using hpre
      have hbirth' : BirthAddress.ghost j i k ∈ birthAddresses x K B := by
        simpa [ha] using hbirth
      have hstep : j < m + 1 ∧ k < B := by simpa [pd5_prefixAddress] using hpre'
      by_cases hj : j < m
      · have hghost : BirthAddress.ghost j i k ∈ pd5_ghostAddresses K j B := by
          simp [pd5_ghostAddresses, hstep.2]
        have hpast : BirthAddress.ghost j i k ∈
            (Finset.range m).biUnion (fun n =>
              pd5_ghostAddresses K n B ∩ birthAddresses x K B) :=
          Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
            Finset.mem_inter.mpr ⟨hghost, hbirth'⟩⟩
        simp [pd5_phaseGhostPrefixAddresses, pd5_phasePastAddresses, hpast]
      · have hjeq : j = m := by omega
        subst j
        have hghost : BirthAddress.ghost m i k ∈ pd5_ghostAddresses K m B := by
          simp [pd5_ghostAddresses, hstep.2]
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hghost, hbirth'⟩)

private theorem pd5_low_a_phaseGhostAppend {K : ℕ} (F : PDFix K) (S : PDScale)
    (B m : ℕ) (U : Finset (BirthAddress K))
    (hU : U ⊆ birthAddresses S.x K B) (φ : BirthAddress K → ℕ → ℂ)
    (L : BirthLog K) (hL : pd5_logPrefixGood S.x B m m L)
    (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) :
    pd5_phasePastWeight U (pd5_phaseGhostPrefixAddresses S.x B m) φ
        (L ++ pd5_ghostBirthLog m l (fun i k => (new i k : ℕ))) =
      pd5_phasePastWeight U (pd5_phasePastAddresses S.x B m) φ L *
        pd5_operationPhase U (pd5_ghostAddresses K m B) φ
          (pd5_ghostBirthLog m l (fun i k => (new i k : ℕ))) := by
  classical
  let G : BirthLog K := pd5_ghostBirthLog m l (fun i k => (new i k : ℕ))
  let Past : Finset (BirthAddress K) := pd5_phasePastAddresses S.x B m
  let Ghost : Finset (BirthAddress K) := pd5_ghostAddresses K m B
  have hQR : Disjoint (U ∩ Past) (U ∩ Ghost) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hdis := Finset.disjoint_left.mp
      (pd5_phasePast_disjoint_ghost (K := K) S.x B m)
    apply hdis (Finset.mem_inter.mp ha).2
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hb).2, hU (Finset.mem_inter.mp hb).1⟩
  have hN₁ := hL.1
  have hN₂ : (G.map Prod.fst).Nodup := by
    dsimp [G]
    rw [pd5_ghostBirthLog_map_fst]
    exact pd5_ghostAddressList_nodup m l
  have hN : ((L ++ G).map Prod.fst).Nodup :=
    pd5_low_a_ghostLog_nodup hL F l new
  have hL₂ : ∀ e ∈ G, e.1 ∉ U ∩ Past := by
    intro e he hmem
    obtain ⟨i, k, heq⟩ :=
      pd5_low_a_ghostLog_address_step m l (fun i k => (new i k : ℕ))
        (by simpa [G] using he)
    have hnot : BirthAddress.ghost m i k ∉ Past := by
      dsimp [Past]
      simp [pd5_phasePastAddresses, pd5_initialAddresses,
        pd5_edgeAddresses, pd5_ghostAddresses]
    rw [heq] at hmem
    exact hnot (Finset.mem_inter.mp hmem).2
  have hL₁ : ∀ e ∈ L, e.1 ∉ U ∩ Ghost := by
    intro e he hmem
    have hpast := pd5_low_a_prefixGood_memPast hL e he
    have hdis := Finset.disjoint_left.mp
      (pd5_phasePast_disjoint_ghost (K := K) S.x B m)
    have hmem' := Finset.mem_inter.mp hmem
    have hghost : e.1 ∈ Ghost ∩ birthAddresses S.x K B :=
      Finset.mem_inter.mpr ⟨hmem'.2, hU hmem'.1⟩
    exact hdis hpast hghost
  have hUdecomp : U ∩ pd5_phaseGhostPrefixAddresses S.x B m =
      (U ∩ Past) ∪ (U ∩ Ghost) := by
    ext a
    by_cases ha : a ∈ U
    · have hbirth := hU ha
      simp [ha, hbirth, pd5_phaseGhostPrefixAddresses, Past, Ghost]
    · simp [ha, pd5_phaseGhostPrefixAddresses, Past, Ghost]
  have hphase := pd5_low_a_birthPhaseWeight_append_split
    (U ∩ Past) (U ∩ Ghost) φ L G hQR hN₁ hN₂ hN hL₂ hL₁
  calc
    _ = pd5_birthPhaseWeight (U ∩ pd5_phaseGhostPrefixAddresses S.x B m) φ
          (L ++ G) := rfl
    _ = pd5_birthPhaseWeight ((U ∩ Past) ∪ (U ∩ Ghost)) φ (L ++ G) := by
          rw [hUdecomp]
    _ = _ := hphase

private theorem pd5_low_a_phaseGhostPrefix_disjoint_edge {K : ℕ}
    (x : ℝ) (B m : ℕ) :
    Disjoint (pd5_phaseGhostPrefixAddresses x B m)
      (pd5_edgeAddresses K m ∩ birthAddresses x K B) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  rcases Finset.mem_union.mp ha with hp | hg
  · exact (Finset.disjoint_left.mp
      (pd5_phasePast_disjoint_edge (K := K) x B m)) hp hb
  · exact (Finset.disjoint_left.mp
      (pd5_phaseGhost_disjoint_edge (K := K) x B m)) hg hb

private theorem pd5_low_a_phaseEdgeAppend {K : ℕ} (F : PDFix K) (S : PDScale)
    (B m : ℕ) (U : Finset (BirthAddress K))
    (hU : U ⊆ birthAddresses S.x K B) (φ : BirthAddress K → ℕ → ℂ)
    (L : BirthLog K) (hL : pd5_logPrefixGood S.x B m (m + 1) L)
    (s : MemPoint S.x K)
    (choice : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (hm : m < pathLength S.x) :
    pd5_phasePastWeight U (pd5_phasePastAddresses S.x B (m + 1)) φ
        (L ++ edgeBirths F S m s choice) =
      pd5_phasePastWeight U (pd5_phaseGhostPrefixAddresses S.x B m) φ L *
        pd5_operationPhase U (pd5_edgeAddresses K m) φ (edgeBirths F S m s choice) := by
  classical
  let E : BirthLog K := edgeBirths F S m s choice
  let Prefix : Finset (BirthAddress K) := pd5_phaseGhostPrefixAddresses S.x B m
  let Edge : Finset (BirthAddress K) := pd5_edgeAddresses K m
  have hQR : Disjoint (U ∩ Prefix) (U ∩ Edge) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hdis := Finset.disjoint_left.mp
      (pd5_low_a_phaseGhostPrefix_disjoint_edge (K := K) S.x B m)
    apply hdis (Finset.mem_inter.mp ha).2
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hb).2, hU (Finset.mem_inter.mp hb).1⟩
  have hN₁ := hL.1
  have hN₂ : (E.map Prod.fst).Nodup := by
    dsimp [E]
    exact pd5_edgeBirths_addresses_nodup F S m s choice
  have hGoodAppend := pd5_logPrefixGood_append_edge hL F S s choice rfl hm
  have hN : ((L ++ E).map Prod.fst).Nodup := by
    simpa [E] using hGoodAppend.1
  have hL₂ : ∀ e ∈ E, e.1 ∉ U ∩ Prefix := by
    intro e he hmem
    obtain ⟨i, heq⟩ := by simpa [E] using
      (pd5_low_a_edgeLog_address_step F S m s choice he)
    have hnot : BirthAddress.edge m i ∉ Prefix := by
      dsimp [Prefix, pd5_phaseGhostPrefixAddresses]
      simp [pd5_phasePastAddresses, pd5_initialAddresses,
        pd5_edgeAddresses, pd5_ghostAddresses]
    rw [heq] at hmem
    exact hnot (Finset.mem_inter.mp hmem).2
  have hL₁ : ∀ e ∈ L, e.1 ∉ U ∩ Edge := by
    intro e he hmem
    have hprefix := pd5_low_a_prefixGood_memGhostPrefix hL e he
    have hdis := Finset.disjoint_left.mp
      (pd5_low_a_phaseGhostPrefix_disjoint_edge (K := K) S.x B m)
    have hmem' := Finset.mem_inter.mp hmem
    exact hdis hprefix (Finset.mem_inter.mpr ⟨hmem'.2, hU hmem'.1⟩)
  have hSupport : U ∩ pd5_phasePastAddresses S.x B (m + 1) =
      (U ∩ Prefix) ∪ (U ∩ Edge) := by
    rw [pd5_phasePastAddresses_succ_ghost_edge]
    ext a
    by_cases ha : a ∈ U
    · have hb := hU ha
      simp [ha, hb, Prefix, Edge]
    · simp [ha, Prefix, Edge]
  have hphase := pd5_low_a_birthPhaseWeight_append_split
    (U ∩ Prefix) (U ∩ Edge) φ L E hQR hN₁ hN₂ hN hL₂ hL₁
  have hresult :
      pd5_birthPhaseWeight (U ∩ pd5_phasePastAddresses S.x B (m + 1)) φ (L ++ E) =
        pd5_birthPhaseWeight (U ∩ Prefix) φ L * pd5_birthPhaseWeight (U ∩ Edge) φ E := by
    calc
      _ = pd5_birthPhaseWeight ((U ∩ Prefix) ∪ (U ∩ Edge)) φ (L ++ E) := by
        exact congrArg (fun T => pd5_birthPhaseWeight T φ (L ++ E)) hSupport
      _ = _ := hphase
  simpa [E, Prefix, Edge, pd5_phasePastWeight, pd5_operationPhase] using hresult
private theorem pd5_low_a_phasePastGhost_append {K : ℕ}
    (U : Finset (BirthAddress K)) (x : ℝ) (B m : ℕ)
    (hU : U ⊆ birthAddresses x K B) (φ : BirthAddress K → ℕ → ℂ)
    (L G : BirthLog K)
    (hQR : Disjoint (U ∩ pd5_phasePastAddresses x B m)
      (U ∩ pd5_ghostAddresses K m B))
    (hN₁ : (L.map Prod.fst).Nodup) (hN₂ : (G.map Prod.fst).Nodup)
    (hN : ((L ++ G).map Prod.fst).Nodup)
    (hL₂ : ∀ e ∈ G, e.1 ∉ U ∩ pd5_phasePastAddresses x B m)
    (hL₁ : ∀ e ∈ L, e.1 ∉ U ∩ pd5_ghostAddresses K m B) :
    pd5_phasePastWeight U (pd5_phaseGhostPrefixAddresses x B m) φ (L ++ G) =
      pd5_phasePastWeight U (pd5_phasePastAddresses x B m) φ L *
        pd5_operationPhase U (pd5_ghostAddresses K m B) φ G := by
  have hsupport : U ∩ pd5_phaseGhostPrefixAddresses x B m =
      (U ∩ pd5_phasePastAddresses x B m) ∪
        (U ∩ pd5_ghostAddresses K m B) := by
    ext a
    by_cases ha : a ∈ U
    · have hbirth := hU ha
      simp [pd5_phaseGhostPrefixAddresses, ha, hbirth]
    · simp [pd5_phaseGhostPrefixAddresses, ha]
  unfold pd5_phasePastWeight pd5_operationPhase
  rw [hsupport]
  exact pd5_low_a_birthPhaseWeight_append_split _ _ φ L G hQR hN₁ hN₂ hN hL₂ hL₁

private theorem pd5_low_a_phasePastEdge_append {K : ℕ}
    (U : Finset (BirthAddress K)) (x : ℝ) (B m : ℕ)
    (hU : U ⊆ birthAddresses x K B) (φ : BirthAddress K → ℕ → ℂ)
    (L G : BirthLog K)
    (hQR : Disjoint (U ∩ pd5_phaseGhostPrefixAddresses x B m)
      (U ∩ pd5_edgeAddresses K m))
    (hN₁ : (L.map Prod.fst).Nodup) (hN₂ : (G.map Prod.fst).Nodup)
    (hN : ((L ++ G).map Prod.fst).Nodup)
    (hL₂ : ∀ e ∈ G, e.1 ∉ U ∩ pd5_phaseGhostPrefixAddresses x B m)
    (hL₁ : ∀ e ∈ L, e.1 ∉ U ∩ pd5_edgeAddresses K m) :
    pd5_phasePastWeight U (pd5_phasePastAddresses x B (m + 1)) φ (L ++ G) =
      pd5_phasePastWeight U (pd5_phaseGhostPrefixAddresses x B m) φ L *
        pd5_operationPhase U (pd5_edgeAddresses K m) φ G := by
  have hsupport : U ∩ pd5_phasePastAddresses x B (m + 1) =
      (U ∩ pd5_phaseGhostPrefixAddresses x B m) ∪
        (U ∩ pd5_edgeAddresses K m) := by
    rw [pd5_phasePastAddresses_succ_ghost_edge]
    ext a
    by_cases ha : a ∈ U
    · have hbirth := hU ha
      simp [ha, hbirth, pd5_phaseGhostPrefixAddresses]
      tauto
    · simp [ha]
  unfold pd5_phasePastWeight pd5_operationPhase
  rw [hsupport]
  exact pd5_low_a_birthPhaseWeight_append_split _ _ φ L G hQR hN₁ hN₂ hN hL₂ hL₁

private theorem pd5_low_a_logGhost_phaseTransfer {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (W V : BirthLog K → ℂ) (c : ℂ)
    (f : MemPoint S.x K → ℂ) (s : MemPoint S.x K) (L : BirthLog K)
    (hSplit : ∀ (l : Fin K → ℕ)
      (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)),
      W (L ++ pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))) =
        c * V (pd5_ghostBirthLog j l (fun i k => (new i k : ℕ)))) :
    logGhost F S ρ j (fun tL => W tL.2 * f tL.1) (s, L) =
      c * pd5_ghostBirthTwist F S ρ j V f s := by
  classical
  dsimp only [pd5_ghostBirthTwist, logGhost]
  change (Finset.univ.sum fun D => _) = c * (Finset.univ.sum fun D => _)
  rw [pd5_low_a_fintype_mul_sum c]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← tsum_mul_left]
  apply tsum_congr
  intro l
  rw [pd5_low_a_fintype_mul_sum
    (α := (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) c]
  apply Finset.sum_congr rfl
  intro new hnew
  by_cases hdel : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1
  · simp only [if_pos hdel]
    have hsplit := hSplit l new
    have hsplit' :
        W (L ++ (List.finRange K).flatMap (fun i =>
          List.ofFn fun k : Fin (l i) =>
            (BirthAddress.ghost j i k.val, (new i k : ℕ)))) =
          c * V ((List.finRange K).flatMap (fun i =>
            List.ofFn fun k : Fin (l i) =>
              (BirthAddress.ghost j i k.val, (new i k : ℕ)))) := by
      simpa [pd5_ghostBirthLog] using hsplit
    rw [hsplit']
    simp only [List.nil_append]
    ring
  · simp [hdel]

private theorem pd5_low_a_logSym_phaseTransfer {K : ℕ} (F : PDFix K) (S : PDScale)
    (c : ℂ) (g₁ g₂ : LogPoint S.x K → ℂ)
    (s : MemPoint S.x K) (L₁ L₂ : BirthLog K)
    (h : ∀ t : MemPoint S.x K, g₁ (t, L₁) = c * g₂ (t, L₂)) :
    logSym F S g₁ (s, L₁) = c * logSym F S g₂ (s, L₂) := by
  classical
  unfold logSym
  calc
    _ = (((permCount S.x K : ℂ))⁻¹) *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            c * g₂ ((s.1, permuteLists σ s.2.1, s.2.2), L₂) := by
          congr 1
          apply Finset.sum_congr rfl
          intro σ hσ
          exact h (s.1, permuteLists σ s.2.1, s.2.2)
    _ = c * ((((permCount S.x K : ℂ))⁻¹) *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            g₂ ((s.1, permuteLists σ s.2.1, s.2.2), L₂)) := by
          rw [(pd5_low_a_fintype_mul_sum c _).symm]
          ring

private theorem pd5_low_a_logEdgePiece_phaseTransfer {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step : ℕ) (raw : Bool)
    (St Pr : Finset (Fin K)) (hbox : {z : ℤ × ℤ | envBox S w z}.Finite)
    (g₁ g₂ : LogPoint S.x K → ℂ) (c : ℂ) (L : BirthLog K)
    (h : ∀ r : MemPoint S.x K, ∀ choice : (i : Fin K) →
        EdgeChoice S.x F.a (r.2.2 i) i, ∀ t : MemPoint S.x K,
          g₁ (t, L ++ edgeBirths F S step r choice) =
            c * g₂ (t, edgeBirths F S step r choice))
    (s : MemPoint S.x K) :
    logEdgePiece F S ρ w step raw St Pr (logSym F S g₁) (s, L) =
      c * logEdgePiece F S ρ w step raw St Pr (logSym F S g₂) (s, []) := by
  classical
  rw [pd5_logEdgePiece_finite F S ρ w step raw St Pr (logSym F S g₁) (s, L) hbox]
  rw [pd5_logEdgePiece_finite F S ρ w step raw St Pr (logSym F S g₂) (s, []) hbox]
  rw [pd5_low_a_fintype_mul_sum c]
  apply Finset.sum_congr rfl
  intro choice hchoice
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hcond : edgeStoredSet choice = St ∧ edgePromotedSet choice = Pr ∧
      EdgeAdmissible F S w (s, L).1 choice z
  · simp only [if_pos hcond]
    let target : MemPoint S.x K :=
      (z, edgeTargetLists F S (s, L).1 choice,
        edgeNewMemory F S (s, L).1 choice)
    have hsym := pd5_low_a_logSym_phaseTransfer F S c g₁ g₂ target
      (L ++ edgeBirths F S step (s, L).1 choice)
      (edgeBirths F S step (s, L).1 choice)
      (fun t => h (s, L).1 choice t)
    rw [hsym]
    simp only [List.nil_append]
    ring
  · simp [hcond]

private theorem pd5_low_a_logEdge_phaseTransfer {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step : ℕ)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite)
    (g₁ g₂ : LogPoint S.x K → ℂ) (c : ℂ) (L : BirthLog K)
    (h : ∀ r : MemPoint S.x K, ∀ choice : (i : Fin K) →
        EdgeChoice S.x F.a (r.2.2 i) i, ∀ t : MemPoint S.x K,
          g₁ (t, L ++ edgeBirths F S step r choice) =
            c * g₂ (t, edgeBirths F S step r choice))
    (s : MemPoint S.x K) :
    logEdge F S ρ w EdgeKind.full step g₁ (s, L) =
      c * logEdge F S ρ w EdgeKind.full step g₂ (s, []) := by
  classical
  have hInner (r : MemPoint S.x K) :
      (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S g₁) (r, L) -
          logEdgePiece F S ρ w step false St Pr (logSym F S g₁) (r, L))) =
        c * ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          (logEdgePiece F S ρ w step true St Pr (logSym F S g₂) (r, []) -
            logEdgePiece F S ρ w step false St Pr (logSym F S g₂) (r, [])) := by
    calc
      _ = ∑ St : Finset (Fin K), c *
            ∑ Pr : Finset (Fin K),
              (logEdgePiece F S ρ w step true St Pr (logSym F S g₂) (r, []) -
                logEdgePiece F S ρ w step false St Pr (logSym F S g₂) (r, [])) := by
              apply Finset.sum_congr rfl
              intro St hSt
              rw [pd5_low_a_fintype_mul_sum c]
              apply Finset.sum_congr rfl
              intro Pr hPr
              rw [pd5_low_a_logEdgePiece_phaseTransfer F S ρ w step true St Pr hbox
                g₁ g₂ c L h r]
              rw [pd5_low_a_logEdgePiece_phaseTransfer F S ρ w step false St Pr hbox
                g₁ g₂ c L h r]
              ring
      _ = _ := (pd5_low_a_fintype_mul_sum c _).symm
  unfold logEdge
  change logSym F S (fun σL =>
      ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S g₁) σL -
          logEdgePiece F S ρ w step false St Pr (logSym F S g₁) σL)) (s, L) = _
  refine pd5_low_a_logSym_phaseTransfer F S c _ _ s L [] ?_
  intro r
  exact hInner r

private theorem pd5_low_a_phaseHistoryFn_log {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : ℕ) (U : Finset (BirthAddress K))
    (φ : BirthAddress K → ℕ → ℂ) (hU : U ⊆ birthAddresses S.x K B)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    ∀ k : ℕ, k ≤ pathLength S.x → ∀ s : MemPoint S.x K, ∀ L : BirthLog K,
      pd5_logPrefixGood S.x B (pathLength S.x - k) (pathLength S.x - k) L →
        logHistoryFn F S ρ w (some B) none (pd5_birthPhaseWeight U φ) k (s, L) =
          pd5_phasePastWeight U
            (pd5_phasePastAddresses S.x B (pathLength S.x - k)) φ L *
            pd5_phaseHistoryFn F S ρ w B U φ k s := by
  classical
  intro k
  induction k with
  | zero =>
      intro hk s L hL
      have hL' : pd5_logPrefixGood S.x B (pathLength S.x) (pathLength S.x) L := by
        simpa using hL
      let N := pathLength S.x
      let Past : Finset (BirthAddress K) := pd5_phasePastAddresses S.x B N
      let Ghost : Finset (BirthAddress K) := pd5_ghostAddresses K N B
      let W : BirthLog K → ℂ := pd5_birthPhaseWeight U φ
      let V : BirthLog K → ℂ := pd5_operationPhase U Ghost φ
      let c : ℂ := pd5_phasePastWeight U Past φ L
      have hAll := pd5_phasePastAddresses_all (K := K) S.x B N (by rfl)
      have hGhostBirth : Ghost ⊆ birthAddresses S.x K B := by
        intro a ha
        rw [hAll]
        exact Finset.mem_union_right _ ha
      have hUdecomp : U = (U ∩ Past) ∪ (U ∩ Ghost) := by
        ext a
        constructor
        · intro ha
          have hb := hU ha
          rw [hAll] at hb
          rcases Finset.mem_union.mp hb with hp | hg
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, hp⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ha, hg⟩)
        · intro ha
          rcases Finset.mem_union.mp ha with ha | ha
          · exact (Finset.mem_inter.mp ha).1
          · exact (Finset.mem_inter.mp ha).1
      have hQR : Disjoint (U ∩ Past) (U ∩ Ghost) := by
        apply Finset.disjoint_left.mpr
        intro a ha hb
        have hdis := Finset.disjoint_left.mp
          (pd5_phasePast_disjoint_ghost (K := K) S.x B N)
        apply hdis (Finset.mem_inter.mp ha).2
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hb).2, hU (Finset.mem_inter.mp hb).1⟩
      have hSplit : ∀ (l : Fin K → ℕ)
          (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)),
          W (L ++ pd5_ghostBirthLog N l (fun i k => (new i k : ℕ))) =
            c * V (pd5_ghostBirthLog N l (fun i k => (new i k : ℕ))) := by
        intro l new
        let G : BirthLog K := pd5_ghostBirthLog N l (fun i k => (new i k : ℕ))
        have hN₁ := hL'.1
        have hN₂ : (G.map Prod.fst).Nodup := by
          dsimp [G]
          rw [pd5_ghostBirthLog_map_fst]
          exact pd5_ghostAddressList_nodup N l
        have hN : ((L ++ G).map Prod.fst).Nodup :=
          pd5_low_a_ghostLog_nodup hL' F l new
        have hL₂ : ∀ e ∈ G, e.1 ∉ U ∩ Past := by
          intro e he hmem
          obtain ⟨i, k, heq⟩ :=
            pd5_low_a_ghostLog_address_step N l
              (fun i k => (new i k : ℕ)) (by simpa [G] using he)
          have hnot : BirthAddress.ghost N i k ∉ Past := by
            dsimp [Past, N]
            simp [pd5_phasePastAddresses, pd5_initialAddresses,
              pd5_edgeAddresses, pd5_ghostAddresses]
          rw [heq] at hmem
          exact hnot (Finset.mem_inter.mp hmem).2
        have hL₁ : ∀ e ∈ L, e.1 ∉ U ∩ Ghost := by
          intro e he hmem
          have hpast := pd5_low_a_prefixGood_memPast hL' e he
          have hdis := Finset.disjoint_left.mp
            (pd5_phasePast_disjoint_ghost (K := K) S.x B N)
          have hmem' := Finset.mem_inter.mp hmem
          have hghost : e.1 ∈ Ghost ∩ birthAddresses S.x K B := by
            exact Finset.mem_inter.mpr ⟨hmem'.2, hU hmem'.1⟩
          exact hdis hpast hghost
        have hphase := pd5_low_a_birthPhaseWeight_append_split
          (U ∩ Past) (U ∩ Ghost) φ L G hQR hN₁ hN₂ hN hL₂ hL₁
        have hglobal : W (L ++ G) = c * V G := by
          change pd5_birthPhaseWeight U φ (L ++ G) =
            pd5_birthPhaseWeight (U ∩ Past) φ L *
              pd5_birthPhaseWeight (U ∩ Ghost) φ G
          calc
            _ = pd5_birthPhaseWeight ((U ∩ Past) ∪ (U ∩ Ghost)) φ (L ++ G) := by
              exact congrArg (fun T => pd5_birthPhaseWeight T φ (L ++ G)) hUdecomp
            _ = _ := hphase
        simpa [W, V, c, G, pd5_phasePastWeight, pd5_operationPhase] using hglobal
      simp only [logHistoryFn, logPathRestrict]
      change logTrunc (some B)
          (logGhost F S ρ N (logTrunc (some B) (logBoundaryOut W))) (s, L) =
        c * pd5_plainTrunc B
          (pd5_ghostBirthTwist F S ρ N V (pd5_plainTrunc B memBoundary)) s
      have hBoundaryOut :
          logTrunc (x := S.x) (K := K) (some B)
              (logBoundaryOut (x := S.x) (K := K) W) =
            fun (σL : LogPoint S.x K) =>
              W σL.2 * pd5_plainTrunc (x := S.x) (K := K) B memBoundary σL.1 := by
        funext σL
        by_cases hs : memSize σL.1 ≤ B <;>
          simp [logTrunc, logBoundaryOut, pd5_plainTrunc, hs, mul_comm]
      calc
        _ = logTrunc (some B)
              (logGhost F S ρ N
                (fun σL => W σL.2 * pd5_plainTrunc B memBoundary σL.1)) (s, L) := by
                exact congrArg (fun g =>
                  logTrunc (some B) (logGhost F S ρ N g) (s, L)) hBoundaryOut
        _ = _ := by
              have hghost := pd5_low_a_logGhost_phaseTransfer F S ρ N W V c
                (pd5_plainTrunc B memBoundary) s L hSplit
              by_cases hs : memSize s ≤ B
              · simp only [logTrunc, hs, if_pos]
                rw [hghost]
                simp [pd5_plainTrunc, hs]
              · simp [logTrunc, pd5_plainTrunc, hs]
  | succ k ih =>
      intro hk s L hL
      let n : ℕ := pathLength S.x - (k + 1)
      let Past : Finset (BirthAddress K) := pd5_phasePastAddresses S.x B n
      let PastGhost : Finset (BirthAddress K) :=
        pd5_phaseGhostPrefixAddresses S.x B n
      let PastNext : Finset (BirthAddress K) :=
        pd5_phasePastAddresses S.x B (n + 1)
      let GhostOps : Finset (BirthAddress K) := pd5_ghostAddresses K n B
      let EdgeOps : Finset (BirthAddress K) := pd5_edgeAddresses K n
      let ghostPhase : BirthLog K → ℂ := pd5_operationPhase U GhostOps φ
      let edgePhase : BirthLog K → ℂ := pd5_operationPhase U EdgeOps φ
      let phaseFn : MemPoint S.x K → ℂ := pd5_phaseHistoryFn F S ρ w B U φ k
      let oldK : LogPoint S.x K → ℂ := fun ξL =>
        logTrunc (some B) (logHistoryFn F S ρ w (some B) none
          (pd5_birthPhaseWeight U φ) k) ξL
      let newK : LogPoint S.x K → ℂ := fun ξL =>
        logTrunc (some B) (fun ηL =>
          pd5_phasePastWeight U PastNext φ ηL.2 * phaseFn ηL.1) ξL
      let edgeCont : LogPoint S.x K → ℂ := fun ξL =>
        edgePhase ξL.2 * pd5_plainTrunc B phaseFn ξL.1
      let cont₁ : LogPoint S.x K → ℂ := fun ξL =>
        logEdge F S ρ w EdgeKind.full n oldK ξL
      let cont₂ : LogPoint S.x K → ℂ := fun ξL =>
        pd5_phasePastWeight U PastGhost φ ξL.2 *
          pd5_edgeBirthTwist F S ρ w n edgePhase (pd5_plainTrunc B phaseFn) ξL.1
      have hkn : k ≤ pathLength S.x := by omega
      have hn : n < pathLength S.x := by
        dsimp [n]
        omega
      have hshift : pathLength S.x - k = n + 1 := by
        dsimp [n]
        omega
      have hL' : pd5_logPrefixGood S.x B n n L := by
        simpa [n] using hL
      have hOldNew : ∀ ξL : LogPoint S.x K,
          pd5_logPrefixGood S.x B (n + 1) (n + 1) ξL.2 →
            oldK ξL = newK ξL := by
        intro ξL hξ
        have hξ' : pd5_logPrefixGood S.x B (pathLength S.x - k)
            (pathLength S.x - k) ξL.2 := by rw [hshift]; exact hξ
        have hrec := ih hkn ξL.1 ξL.2 hξ'
        have hrec' : logHistoryFn F S ρ w (some B) none
              (pd5_birthPhaseWeight U φ) k ξL =
            pd5_phasePastWeight U PastNext φ ξL.2 * phaseFn ξL.1 := by
          simpa [PastNext, hshift, phaseFn] using hrec
        by_cases hs : memSize ξL.1 ≤ B
        · simp [oldK, newK, logTrunc, hs, hrec']
        · simp [oldK, newK, logTrunc, hs]
      have hcont : ∀ ξL : LogPoint S.x K,
          pd5_logPrefixGood S.x B n (n + 1) ξL.2 → cont₁ ξL = cont₂ ξL := by
        intro ξL hξ
        have hEdgePrefix := pd5_logEdge_prefix_congr F S ρ w n n B
          oldK newK hOldNew rfl hn ξL hξ
        have hSplitEdge : ∀ r : MemPoint S.x K,
              ∀ choice : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i,
              ∀ t : MemPoint S.x K,
                newK (t, ξL.2 ++ edgeBirths F S n r choice) =
                  (pd5_phasePastWeight U PastGhost φ ξL.2) *
                    edgeCont (t, edgeBirths F S n r choice) := by
            intro r choice t
            have hphase := pd5_low_a_phaseEdgeAppend F S B n U hU φ
              ξL.2 hξ r choice hn
            by_cases ht : memSize t ≤ B
            · simp [newK, edgeCont, logTrunc, pd5_plainTrunc, ht,
                PastNext, PastGhost, EdgeOps, edgePhase, hphase]
              ring
            · simp [newK, edgeCont, logTrunc, pd5_plainTrunc, ht]
        have hEdge := pd5_low_a_logEdge_phaseTransfer F S ρ w n hbox
            newK edgeCont (pd5_phasePastWeight U PastGhost φ ξL.2)
            ξL.2 hSplitEdge ξL.1
        calc
          cont₁ ξL = logEdge F S ρ w EdgeKind.full n oldK ξL := rfl
          _ = logEdge F S ρ w EdgeKind.full n newK ξL := hEdgePrefix
          _ = (pd5_phasePastWeight U PastGhost φ ξL.2) *
                pd5_edgeBirthTwist F S ρ w n edgePhase
                  (pd5_plainTrunc B phaseFn) ξL.1 := by
                simpa [edgeCont, pd5_edgeBirthTwist] using hEdge
          _ = cont₂ ξL := rfl
      have hGhostCong := pd5_logGhost_prefix_congr F S ρ n B s L hL'
        (Nat.le_of_lt hn) cont₁ cont₂ hcont
      have hSplitGhost : ∀ (l : Fin K → ℕ)
          (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)),
          pd5_phasePastWeight U PastGhost φ
              (L ++ pd5_ghostBirthLog n l (fun i k => (new i k : ℕ))) =
            (pd5_phasePastWeight U Past φ L) *
              ghostPhase (pd5_ghostBirthLog n l (fun i k => (new i k : ℕ))) := by
        intro l new
        exact pd5_low_a_phaseGhostAppend F S B n U hU φ L hL' l new
      have hGhost := pd5_low_a_logGhost_phaseTransfer F S ρ n
        (fun L => pd5_phasePastWeight U PastGhost φ L) ghostPhase
        (pd5_phasePastWeight U Past φ L)
        (pd5_plainTrunc B
          (pd5_edgeBirthTwist F S ρ w n edgePhase (pd5_plainTrunc B phaseFn)))
        s L hSplitGhost
      simp only [logHistoryFn, logPathRestrict]
      change logTrunc (some B)
          (logGhost F S ρ n (logTrunc (some B) cont₁)) (s, L) =
        (pd5_phasePastWeight U Past φ L) *
          pd5_plainTrunc B (pd5_ghostBirthTwist F S ρ n ghostPhase
            (pd5_plainTrunc B
              (pd5_edgeBirthTwist F S ρ w n edgePhase (pd5_plainTrunc B phaseFn)))) s
      have hCont₂Trunc :
          logTrunc (some B) cont₂ =
            fun ξL => pd5_phasePastWeight U PastGhost φ ξL.2 *
              pd5_plainTrunc B
                (pd5_edgeBirthTwist F S ρ w n edgePhase
                  (pd5_plainTrunc B phaseFn)) ξL.1 := by
        funext ξL
        by_cases hs : memSize ξL.1 ≤ B <;>
          simp [logTrunc, cont₂, pd5_plainTrunc, hs]
      calc
        _ = logTrunc (some B)
              (logGhost F S ρ n (logTrunc (some B) cont₂)) (s, L) := by
          by_cases hs : memSize s ≤ B <;>
            simp [logTrunc, hs, hGhostCong]
        _ = logTrunc (some B)
              (logGhost F S ρ n
                (fun ξL => pd5_phasePastWeight U PastGhost φ ξL.2 *
                  pd5_plainTrunc B
                    (pd5_edgeBirthTwist F S ρ w n edgePhase
                      (pd5_plainTrunc B phaseFn)) ξL.1)) (s, L) := by
          rw [hCont₂Trunc]
        _ = _ := by
          by_cases hs : memSize s ≤ B
          · simp only [logTrunc, hs, if_pos]
            calc
              logGhost F S ρ n
                  (fun ξL => pd5_phasePastWeight U PastGhost φ ξL.2 *
                    pd5_plainTrunc B
                      (pd5_edgeBirthTwist F S ρ w n edgePhase
                        (pd5_plainTrunc B phaseFn)) ξL.1) (s, L) =
                  (pd5_phasePastWeight U Past φ L) *
                    pd5_ghostBirthTwist F S ρ n ghostPhase
                      (pd5_plainTrunc B
                        (pd5_edgeBirthTwist F S ρ w n edgePhase
                          (pd5_plainTrunc B phaseFn))) s := hGhost
              _ = (pd5_phasePastWeight U Past φ L) *
                    pd5_plainTrunc B (pd5_ghostBirthTwist F S ρ n ghostPhase
                      (pd5_plainTrunc B
                        (pd5_edgeBirthTwist F S ρ w n edgePhase
                          (pd5_plainTrunc B phaseFn)))) s := by
                    simp [pd5_plainTrunc, hs]
          · simp [logTrunc, pd5_plainTrunc, hs]

private theorem pd5_low_a_logBoundaryIn_eq {x : ℝ} {K : ℕ}
    {s : MemPoint x K} {L : BirthLog K}
    (h : logBoundaryIn (s, L) ≠ 0) : L = initialLog s := by
  by_cases hEq : L = initialLog s
  · exact hEq
  · simp [logBoundaryIn, hEq] at h

private theorem pd5_low_a_logInner_initialLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (g : LogPoint S.x K → ℂ) :
    logInner F S logBoundaryIn g =
      ∑' s : MemPoint S.x K,
        (memMeasure F S s : ℂ) * star (memBoundary s) * g (s, initialLog s) := by
  classical
  let weight : LogPoint S.x K → ℂ := fun σL =>
    (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)
  let support : Finset (LogPoint S.x K) :=
    (pd5_logBoundaryIn_weight_support_finite F S).toFinset
  let states : Finset (MemPoint S.x K) := support.image Prod.fst
  have hweight_zero (σL : LogPoint S.x K) (hσ : σL ∉ support) : weight σL = 0 := by
    by_contra hw
    apply hσ
    change σL ∈ (pd5_logBoundaryIn_weight_support_finite F S).toFinset
    exact (pd5_logBoundaryIn_weight_support_finite F S).mem_toFinset.mpr
      (by simpa [weight] using hw)
  have hterm_zero (σL : LogPoint S.x K) (hσ : σL ∉ support) :
      weight σL * g σL = 0 := by simp [hweight_zero σL hσ]
  have hsumLogs :
      (∑' σL : LogPoint S.x K, weight σL * g σL) =
        ∑ σL ∈ support, weight σL * g σL :=
    tsum_eq_sum (L := SummationFilter.unconditional (LogPoint S.x K))
      (s := support) hterm_zero
  have hlog (σL : LogPoint S.x K) (hσ : σL ∈ support) :
      σL.2 = initialLog σL.1 := by
    have hw : weight σL ≠ 0 := by
      change σL ∈ (pd5_logBoundaryIn_weight_support_finite F S).toFinset at hσ
      exact (pd5_logBoundaryIn_weight_support_finite F S).mem_toFinset.mp hσ
    have hb : logBoundaryIn σL ≠ 0 := by
      intro hz
      apply hw
      simp [weight, hz]
    exact pd5_low_a_logBoundaryIn_eq hb
  have hinj : ∀ σL ∈ support, ∀ τL ∈ support, σL.1 = τL.1 → σL = τL := by
    intro σL hσ τL hτ hst
    rcases σL with ⟨s, L⟩
    rcases τL with ⟨t, M⟩
    have hL := hlog (s, L) hσ
    have hM := hlog (t, M) hτ
    change s = t at hst
    subst t
    have : L = M := hL.trans hM.symm
    subst M
    rfl
  let stateWeight : MemPoint S.x K → ℂ := fun s =>
    (memMeasure F S s : ℂ) * star (memBoundary s) * g (s, initialLog s)
  have hstate_zero (s : MemPoint S.x K) (hs : s ∉ states) : stateWeight s = 0 := by
    by_contra hnonzero
    have hμ : memMeasure F S s ≠ 0 := by
      intro hz
      apply hnonzero
      simp [stateWeight, hz]
    have hstar : star (memBoundary s) ≠ 0 := by
      intro hz
      have hbzero : memBoundary s = 0 := by
        have hstarStar := congrArg star hz
        simpa using hstarStar
      apply hnonzero
      simp [stateWeight, hbzero]
    have hμC : (memMeasure F S s : ℂ) ≠ 0 := by exact_mod_cast hμ
    have hwt : weight (s, initialLog s) ≠ 0 := by
      have heq : weight (s, initialLog s) =
          (memMeasure F S s : ℂ) * star (memBoundary s) := by
        simp [weight, logBoundaryIn]
      rw [heq]
      exact mul_ne_zero hμC hstar
    have hmem : (s, initialLog s) ∈ support := by
      change (s, initialLog s) ∈
        (pd5_logBoundaryIn_weight_support_finite F S).toFinset
      apply (pd5_logBoundaryIn_weight_support_finite F S).mem_toFinset.mpr
      simpa [weight] using hwt
    apply hs
    change s ∈ support.image Prod.fst
    exact Finset.mem_image.mpr ⟨(s, initialLog s), hmem, rfl⟩
  have hsumStates :
      (∑' s : MemPoint S.x K, stateWeight s) =
        ∑ s ∈ states, stateWeight s :=
    tsum_eq_sum (L := SummationFilter.unconditional (MemPoint S.x K))
      (s := states) hstate_zero
  unfold logInner
  change (∑' σL : LogPoint S.x K,
      (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) * g σL) = _
  rw [show (fun σL : LogPoint S.x K =>
      (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) * g σL) =
      (fun σL => weight σL * g σL) from rfl, hsumLogs]
  calc
    (∑ σL ∈ support, weight σL * g σL) =
        ∑ σL ∈ support, stateWeight σL.1 := by
          apply Finset.sum_congr rfl
          intro σL hσ
          have hEq : σL = (σL.1, initialLog σL.1) := by
            cases σL with
            | mk s L => exact congrArg (fun L => (s, L)) (hlog (s, L) hσ)
          rw [hEq]
          simp [stateWeight, weight, logBoundaryIn]
    _ = ∑ s ∈ states, stateWeight s := by
          symm
          rw [Finset.sum_image hinj]
    _ = ∑' s : MemPoint S.x K, stateWeight s := hsumStates.symm

/-- Attach bounded address phases at their unique births, eliminating the log exactly.
Uses pd5 prefix uniqueness and finite
cutoff expansions; feeds low-rank norm iteration. -/
theorem pd5_phase_at_births {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : ℕ) (U : Finset (BirthAddress K)) (hU : U ⊆ birthAddresses S.x K B)
    (φ : BirthAddress K → ℕ → ℂ) (hφ : ∀ a p, ‖φ a p‖ ≤ 1)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    memHistory F S ρ w (some B) none (pd5_birthPhaseWeight U φ) =
      pd5_phaseHistory F S ρ w B U φ := by
  classical
  let hist : LogPoint S.x K → ℂ :=
    logHistoryFn F S ρ w (some B) none (pd5_birthPhaseWeight U φ) (pathLength S.x)
  let Past₀ : Finset (BirthAddress K) := pd5_phasePastAddresses S.x B 0
  have hPast₀ : Past₀ = pd5_initialAddresses S.x K := by
    exact pd5_phasePastAddresses_zero (K := K) S.x B
  have hAttach (s : MemPoint S.x K) :
      hist (s, initialLog s) =
        pd5_phasePastWeight U Past₀ φ (initialLog s) *
          pd5_phaseHistoryFn F S ρ w B U φ (pathLength S.x) s := by
    simpa [hist, Past₀] using
      (pd5_low_a_phaseHistoryFn_log F S ρ w B U φ hU hbox
        (pathLength S.x) le_rfl s (initialLog s)
        (by simpa using pd5_initialLog_prefixGood (B := B) s))
  have hInitialWeight (s : MemPoint S.x K) :
      pd5_phasePastWeight U Past₀ φ (initialLog s) =
        pd5_operationPhase U (pd5_initialAddresses S.x K) φ (initialLog s) := by
    simp [pd5_phasePastWeight, pd5_operationPhase, hPast₀]
  unfold memHistory
  rw [pd5_low_a_logInner_initialLog F S hist]
  unfold pd5_phaseHistory
  apply tsum_congr
  intro s
  calc
    (memMeasure F S s : ℂ) * star (memBoundary s) *
        logHistoryFn F S ρ w (some B) none (pd5_birthPhaseWeight U φ)
          (pathLength S.x) (s, initialLog s) =
      (memMeasure F S s : ℂ) * star (memBoundary s) * hist (s, initialLog s) := rfl
    _ =
      (memMeasure F S s : ℂ) * star (memBoundary s) *
        (pd5_phasePastWeight U Past₀ φ (initialLog s) *
          pd5_phaseHistoryFn F S ρ w B U φ (pathLength S.x) s) := by rw [hAttach s]
    _ = (memMeasure F S s : ℂ) * star (memBoundary s) *
          pd5_operationPhase U (pd5_initialAddresses S.x K) φ (initialLog s) *
            pd5_phaseHistoryFn F S ρ w B U φ (pathLength S.x) s := by
      rw [hInitialWeight s]
      ring

/-- Pair phases regroup into the product of their per-address coefficients, including absent
performed flags. Uses pd5b_pairAddressCoeff;
feeds pd5_phase_at_births and low-rank norm iteration. -/
theorem pd5_pairPhase_eq_birthPhase {K T : ℕ} [NeZero T]
    (A : Finset (BirthAddress K)) (C : Finset (Finset (BirthAddress K)))
    (hC : IsConstraintSystem A C)
    (θ : {p : A × A // p ∈ pd5_systemPairs A C hC} → ZMod T) (log : BirthLog K) :
    pd5b_systemPairPhase A C hC log θ =
      pd5_birthPhaseWeight (C.biUnion id)
        (fun a p => ZMod.stdAddChar (pd5b_pairAddressCoeff A C hC θ a * (p : ZMod T))) log := by
  classical
  let Pair := {p : A × A // p ∈ pd5_systemPairs A C hC}
  let U := C.biUnion id
  have hincident (a : BirthAddress K) (ha : a ∈ U) :
      ∃ p : Pair, p.1.1.1 = a ∨ p.1.2.1 = a := by
    rcases Finset.mem_biUnion.mp ha with ⟨D, hD, haD⟩
    have hprops := hC.1 D hD
    let pivot := pd5_blockPivot D hprops.2
    by_cases hap : pivot.1 = a
    · have hex : ∃ b ∈ D, b ≠ pivot.1 := by
        by_contra hn
        have hsub : D ⊆ {pivot.1} := by
          intro b hb
          simp only [Finset.mem_singleton]
          by_contra hne
          exact hn ⟨b, hb, hne⟩
        have hcard := Finset.card_le_card hsub
        simp at hcard
        omega
      obtain ⟨b, hb, hbne⟩ := hex
      let b' : {b // b ∈ D} := ⟨b, hb⟩
      have hbneq : b' ≠ pivot := by
        intro h
        apply hbne
        exact congrArg Subtype.val h
      have hb' : b' ∈ D.attach.erase pivot := by
        simp [b', hbneq]
      let raw : A × A :=
        (pd5_toA A D hprops.1 pivot, pd5_toA A D hprops.1 b')
      have hraw : raw ∈ pd5_systemPairs A C hC :=
        (pd5_systemPairs_mem_iff A C hC raw).2 ⟨D, hD,
          (pd5_blockPairs_mem_iff A D hprops.1 hprops.2 raw).2 ⟨b', hb', rfl⟩⟩
      refine ⟨⟨raw, hraw⟩, Or.inl ?_⟩
      simp [raw, pd5_toA, hap]
    · let b' : {b // b ∈ D} := ⟨a, haD⟩
      have hbne : b' ≠ pivot := by
        intro h
        exact hap (congrArg Subtype.val h).symm
      have hb' : b' ∈ D.attach.erase pivot := by
        simp [b', hbne]
      let raw : A × A :=
        (pd5_toA A D hprops.1 pivot, pd5_toA A D hprops.1 b')
      have hraw : raw ∈ pd5_systemPairs A C hC :=
        (pd5_systemPairs_mem_iff A C hC raw).2 ⟨D, hD,
          (pd5_blockPairs_mem_iff A D hprops.1 hprops.2 raw).2 ⟨b', hb', rfl⟩⟩
      refine ⟨⟨raw, hraw⟩, Or.inr ?_⟩
      simp [raw, pd5_toA, b']
  have hpairSupport (p : Pair) : p.1.1.1 ∈ U ∧ p.1.2.1 ∈ U := by
    rcases (pd5_systemPairs_mem_iff A C hC p.1).mp p.2 with ⟨D, hD, hpD⟩
    have hprops := hC.1 D hD
    rcases (pd5_blockPairs_mem_iff A D hprops.1 hprops.2 p.1).mp hpD with
      ⟨b, hb, hpEq⟩
    have hpivot : (pd5_blockPivot D hprops.2).1 ∈ D :=
      (pd5_blockPivot D hprops.2).2
    have hleft : p.1.1.1 = (pd5_blockPivot D hprops.2).1 := by
      have := congrArg (fun q : A × A => q.1.1) hpEq
      simpa [pd5_toA] using this
    have hright : p.1.2.1 = b.1 := by
      have := congrArg (fun q : A × A => q.2.1) hpEq
      simpa [pd5_toA] using this
    constructor
    · exact Finset.mem_biUnion.mpr ⟨D, hD, hleft ▸ hpivot⟩
    · exact Finset.mem_biUnion.mpr ⟨D, hD, hright ▸ b.2⟩
  by_cases hAll : ∀ a ∈ U, ∃ p, pd5b_label log a = some p
  · let value : BirthAddress K → ℕ := fun a =>
      if ha : a ∈ U then Classical.choose (hAll a ha) else 0
    have hvalue (a : BirthAddress K) (ha : a ∈ U) :
        pd5b_label log a = some (value a) := by
      dsimp [value]
      rw [dif_pos ha]
      exact Classical.choose_spec (hAll a ha)
    have hfactor (a : BirthAddress K) (ha : a ∈ U) :
        pd5_addressPhase (fun a p =>
          ZMod.stdAddChar (pd5b_pairAddressCoeff A C hC θ a * (p : ZMod T))) log a =
          ZMod.stdAddChar
            (pd5b_pairAddressCoeff A C hC θ a * (value a : ZMod T)) := by
      change (match pd5b_label log a with
        | none => 0
        | some p => ZMod.stdAddChar
            (pd5b_pairAddressCoeff A C hC θ a * (p : ZMod T))) = _
      rw [hvalue a ha]
    have hexponent :
        (∑ a ∈ U, pd5b_pairAddressCoeff A C hC θ a * (value a : ZMod T)) =
          ∑ p : Pair, θ p *
            ((value p.1.1.1 : ZMod T) - (value p.1.2.1 : ZMod T)) := by
      classical
      have hleftInner (p : Pair) :
          (∑ a ∈ U, (if p.1.1.1 = a then θ p else 0) * (value a : ZMod T)) =
            θ p * (value p.1.1.1 : ZMod T) := by
        have hends := hpairSupport p
        have h := Finset.sum_ite_eq U p.1.1.1
          (fun a => θ p * (value a : ZMod T))
        simpa [ite_mul, hends.1] using h
      have hrightInner (p : Pair) :
          (∑ a ∈ U, (if p.1.2.1 = a then θ p else 0) * (value a : ZMod T)) =
            θ p * (value p.1.2.1 : ZMod T) := by
        have hends := hpairSupport p
        have h := Finset.sum_ite_eq U p.1.2.1
          (fun a => θ p * (value a : ZMod T))
        simpa [ite_mul, hends.2] using h
      have hleftTotal :
          (∑ a ∈ U, ∑ p : Pair,
            (if p.1.1.1 = a then θ p else 0) * (value a : ZMod T)) =
          ∑ p : Pair, θ p * (value p.1.1.1 : ZMod T) := by
        calc
          _ = ∑ a ∈ U, ∑ p ∈ (Finset.univ : Finset Pair),
                (if p.1.1.1 = a then θ p else 0) * (value a : ZMod T) := rfl
          _ = ∑ p ∈ (Finset.univ : Finset Pair), ∑ a ∈ U,
                (if p.1.1.1 = a then θ p else 0) * (value a : ZMod T) :=
              Finset.sum_comm
          _ = _ := by
              apply Finset.sum_congr rfl
              intro p hp
              exact hleftInner p
      have hrightTotal :
          (∑ a ∈ U, ∑ p : Pair,
            (if p.1.2.1 = a then θ p else 0) * (value a : ZMod T)) =
          ∑ p : Pair, θ p * (value p.1.2.1 : ZMod T) := by
        calc
          _ = ∑ a ∈ U, ∑ p ∈ (Finset.univ : Finset Pair),
                (if p.1.2.1 = a then θ p else 0) * (value a : ZMod T) := rfl
          _ = ∑ p ∈ (Finset.univ : Finset Pair), ∑ a ∈ U,
                (if p.1.2.1 = a then θ p else 0) * (value a : ZMod T) :=
              Finset.sum_comm
          _ = _ := by
              apply Finset.sum_congr rfl
              intro p hp
              exact hrightInner p
      calc
        _ = (∑ a ∈ U, ∑ p : Pair,
              (if p.1.1.1 = a then θ p else 0) * (value a : ZMod T)) -
            (∑ a ∈ U, ∑ p : Pair,
              (if p.1.2.1 = a then θ p else 0) * (value a : ZMod T)) := by
              simp only [pd5b_pairAddressCoeff, Finset.sum_sub_distrib,
                sub_mul, Finset.sum_mul]
              rfl
        _ = (∑ p : Pair, θ p * (value p.1.1.1 : ZMod T)) -
            (∑ p : Pair, θ p * (value p.1.2.1 : ZMod T)) := by
              rw [hleftTotal, hrightTotal]
        _ = ∑ p : Pair, θ p *
              ((value p.1.1.1 : ZMod T) - (value p.1.2.1 : ZMod T)) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro p hp
              ring
    have hcharProduct :
        (∏ a ∈ U, ZMod.stdAddChar
          (pd5b_pairAddressCoeff A C hC θ a * (value a : ZMod T))) =
          ∏ p : Pair, ZMod.stdAddChar
            (θ p * ((value p.1.1.1 : ZMod T) - (value p.1.2.1 : ZMod T))) := by
      calc
        _ = ZMod.stdAddChar
              (∑ a ∈ U, pd5b_pairAddressCoeff A C hC θ a * (value a : ZMod T)) := by
              symm
              exact pd5_low_a_stdAddChar_sum U
                (fun a => pd5b_pairAddressCoeff A C hC θ a * (value a : ZMod T))
        _ = ZMod.stdAddChar
              (∑ p : Pair, θ p *
                ((value p.1.1.1 : ZMod T) - (value p.1.2.1 : ZMod T))) :=
              congrArg ZMod.stdAddChar hexponent
        _ = _ := pd5_low_a_stdAddChar_sum Finset.univ
          (fun p : Pair => θ p *
            ((value p.1.1.1 : ZMod T) - (value p.1.2.1 : ZMod T)))
    have hsys : pd5b_systemPairPhase A C hC log θ =
        ∏ p : Pair, ZMod.stdAddChar
          (θ p * ((value p.1.1.1 : ZMod T) - (value p.1.2.1 : ZMod T))) := by
      unfold pd5b_systemPairPhase
      apply Finset.prod_congr rfl
      intro p hp
      have hends := hpairSupport p
      change (match pd5b_pairDifference log (p.1.1.1, p.1.2.1) with
        | some t => ZMod.stdAddChar (θ p * t)
        | none => 0) = _
      have hdiff : pd5b_pairDifference log (p.1.1.1, p.1.2.1) =
          some ((value p.1.1.1 : ZMod T) - (value p.1.2.1 : ZMod T)) := by
        simp [pd5b_pairDifference, hvalue, hends]
      rw [hdiff]
    unfold pd5_birthPhaseWeight
    rw [hsys]
    rw [hcharProduct.symm]
    apply Finset.prod_congr rfl
    intro a ha
    exact (hfactor a ha).symm
  · push_neg at hAll
    obtain ⟨a, ha, hnone⟩ := hAll
    have hlabelNone : pd5b_label log a = none := by
      cases h : pd5b_label log a with
      | none => rfl
      | some p => exact (hnone p h).elim
    obtain ⟨p, hpIncident⟩ := hincident a ha
    have hpMissing :
        pd5b_pairDifference (T := T) log (p.1.1.1, p.1.2.1) =
          (none : Option (ZMod T)) := by
      rcases hpIncident with hp | hp
      · simp [pd5b_pairDifference, hp, hlabelNone]
      · simp [pd5b_pairDifference, hp, hlabelNone]
    have hsysZero : pd5b_systemPairPhase A C hC log θ = 0 := by
      unfold pd5b_systemPairPhase
      apply Finset.prod_eq_zero (Finset.mem_univ p)
      simp [hpMissing]
    have hbirthZero : pd5_birthPhaseWeight U
        (fun a p => ZMod.stdAddChar
          (pd5b_pairAddressCoeff A C hC θ a * (p : ZMod T))) log = 0 := by
      unfold pd5_birthPhaseWeight
      apply Finset.prod_eq_zero ha
      simp [pd5_addressPhase, hlabelNone]
    exact hsysZero.trans hbirthZero.symm

end
end ArtinPrimitiveRoots.TypeII.PD
