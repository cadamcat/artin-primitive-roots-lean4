import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedGhostOut
import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedEdgeGeo

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- Hits of a life-state memory list, counted by band primes. -/
theorem hitCount_life {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (i : Fin K) (b : Bool) (jP jz : Fin (pathLength S.x + 1))
    (l : List Particle) (hnd : (l.map Prod.fst).Nodup)
    (hmem : ∀ q : Particle, q ∈ l ↔ ∃ hp : q.1 ∈ primeBand S.x (F.a i),
      pdLifePending S γ q.1 (H i ⟨q.1, hp⟩) b jP ∧
        q.2 = (lifeLine S γ q.1 (H i ⟨q.1, hp⟩).1).val) :
    hitCount l (γ jz).1 =
      (Finset.univ.filter fun p : primeBand S.x (F.a i) =>
        pdLifePending S γ p.1 (H i p) b jP ∧ lifeHit S γ p.1 (H i p).1 jz).card := by
  unfold hitCount hitIndices
  refine card_filter_get_eq (s := primeBand S.x (F.a i)) _ hnd
    (fun q => particleHits q (γ jz).1) _ (dR := _) (dC := _) ?_ ?_
  · intro r hr
    obtain ⟨hp, hpend, hanc⟩ := (hmem _).mp (List.get_mem _ _)
    refine ⟨hp, hpend, ?_⟩
    unfold particleHits at hr
    unfold lifeHit
    apply Fin.ext
    rw [← hr, hanc]
  · intro p hp
    obtain ⟨hpend, hhit⟩ := hp
    have hin : ((p.1, (lifeLine S γ p.1 (H i p).1).val) : Particle) ∈ l :=
      (hmem _).mpr ⟨p.2, hpend, rfl⟩
    obtain ⟨r, hr⟩ := List.mem_iff_get.mp hin
    refine ⟨r, by rw [hr], ?_⟩
    unfold particleHits
    rw [hr]
    exact congrArg Fin.val hhit.symm

theorem not_pending_of_active {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (b : Bool) (j : Fin (pathLength S.x + 1))
    (hj : IsActiveAt γ p j) : ¬ pdLifePending S γ p e b j := by
  have hA : (pdLifeActive S γ p).Nonempty := ⟨j, by simp [pdLifeActive, hj]⟩
  simp only [pdLifePending, hA, ↓reduceDIte]
  exact fun h => h.1 hj

theorem lifeLine_of_active {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (j : Fin (pathLength S.x + 1))
    (hj : IsActiveAt γ p j) : lifeLine S γ p e.1 = projLine p (γ j).1 := by
  have hA : (pdLifeActive S γ p).Nonempty := ⟨j, by simp [pdLifeActive, hj]⟩
  simp only [lifeLine, hA, ↓reduceDIte]
  exact ((life_active_facts S γ p e hA).2.2.2 j hj).symm

/-- Across an edge, a prime inactive at both ends keeps its pending status. -/
theorem pending_edge_iff {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (j : Fin (pathLength S.x))
    (hj : ¬ IsActiveAt γ p j.castSucc) (hj1 : ¬ IsActiveAt γ p j.succ) :
    pdLifePending S γ p e false j.succ ↔ pdLifePending S γ p e true j.castSucc := by
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · obtain ⟨-, hB, hC, -⟩ := life_active_facts S γ p e hA
    have hαact : IsActiveAt γ p ((pdLifeActive S γ p).min' hA) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
    have hωact : IsActiveAt γ p ((pdLifeActive S γ p).max' hA) :=
      (Finset.mem_filter.mp (Finset.max'_mem _ hA)).2
    have hα1 : ((pdLifeActive S γ p).min' hA).val ≠ j.val + 1 := by
      intro h; apply hj1
      have : (pdLifeActive S γ p).min' hA = j.succ := Fin.ext (by simp [h])
      rwa [← this]
    have hω0 : ((pdLifeActive S γ p).max' hA).val ≠ j.val := by
      intro h; apply hj
      have : (pdLifeActive S γ p).max' hA = j.castSucc := Fin.ext (by simp [h])
      rwa [← this]
    have hαω := Finset.min'_le_max' _ hA
    simp only [pdLifePending, hA, ↓reduceDIte, hj, hj1, not_false_eq_true, true_and]
    rcases e with ⟨⟨_ | a, _ | c⟩, he⟩ <;>
      split_ifs <;>
      simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff, Fin.val_succ, Fin.coe_castSucc, not_lt,
        Bool.false_eq_true, ↓reduceIte, true_and, false_and, true_iff, false_iff, and_true,
        and_false, or_false, false_or, iff_true, iff_false, not_false_eq_true,
        Option.some.injEq, reduceCtorEq, imp_false, forall_eq'] at * <;>
      (first | omega | simp)
  · simp only [pdLifePending, hA, ↓reduceDIte]
    rcases life_inactive_facts S γ p e hA with h | ⟨a, c, h, hac, -⟩
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      simp only [Fin.lt_def, Fin.le_def, Fin.val_succ, Fin.coe_castSucc]
      omega

/-- A prime pending after the ghost of visit `j` is logged by then. -/
theorem logged_of_pending_true {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (i : Fin K) (p : primeBand S.x (F.a i))
    (j : Fin (pathLength S.x + 1)) (h : pdLifePending S γ p.1 (H i p) true j) :
    lifeBornBefore F S γ H p.1 j ∨ ∃ i', lifeBornAt F S γ H i' p.1 j := by
  by_cases hA : (pdLifeActive S γ p.1).Nonempty
  · have hαact : IsActiveAt γ p.1 ((pdLifeActive S γ p.1).min' hA) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
    simp only [pdLifePending, hA, ↓reduceDIte] at h
    obtain ⟨-, h⟩ := h
    by_cases h1 : j < (pdLifeActive S γ p.1).min' hA
    · rw [if_pos h1] at h
      cases ha : (H i p).1.1 with
      | none => rw [ha] at h; exact h.elim
      | some a =>
        rw [ha] at h
        simp only [↓reduceIte] at h
        rcases lt_or_eq_of_le h with h | h
        · exact Or.inl (Or.inr ⟨i, a, h, p.2, ha⟩)
        · subst h; exact Or.inr ⟨i, p.2, ha⟩
    · exact Or.inl (Or.inl ⟨_, not_lt.mp h1, hαact⟩)
  · simp only [pdLifePending, hA, ↓reduceDIte] at h
    rcases life_inactive_facts S γ p.1 (H i p) hA with he | ⟨a, c, he, -, -⟩
    · rw [he] at h; exact h.elim
    · rw [he] at h
      simp only [↓reduceIte] at h
      have ha : (H i p).1.1 = some a := by rw [he]
      rcases lt_or_eq_of_le h.1 with h' | h'
      · exact Or.inl (Or.inr ⟨i, a, h', p.2, ha⟩)
      · subst h'; exact Or.inr ⟨i, p.2, ha⟩

/-- An entering prime that is already logged is pending after the previous ghost. -/
theorem pending_of_entering_logged {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (i : Fin K) (p : primeBand S.x (F.a i)) (j : Fin (pathLength S.x))
    (h1 : IsActiveAt γ p.1 j.succ) (h0 : ¬ IsActiveAt γ p.1 j.castSucc)
    (hlog : lifeBornBefore F S γ H p.1 j.castSucc ∨
      ∃ i', lifeBornAt F S γ H i' p.1 j.castSucc) :
    pdLifePending S γ p.1 (H i p) true j.castSucc := by
  have hA : (pdLifeActive S γ p.1).Nonempty := ⟨j.succ, by simp [pdLifeActive, h1]⟩
  obtain ⟨hAJ, hB, -, -⟩ := life_active_facts S γ p.1 (H i p) hA
  have hα := (hAJ _ h1).1
  have hbirth : ∀ i' a, lifeBornAt F S γ H i' p.1 a → (H i p).1.1 = some a := by
    rintro i' a ⟨hp', hb⟩
    by_cases hii : i' = i
    · subst hii; exact hb
    · exact absurd p.2 (Finset.disjoint_left.mp (hBands i' i hii) hp')
  simp only [pdLifePending, hA, ↓reduceDIte, h0, not_false_eq_true, true_and]
  by_cases hlt : j.castSucc < (pdLifeActive S γ p.1).min' hA
  · rw [if_pos hlt]
    rcases hlog with (⟨j', hj', hact⟩ | ⟨i', a, ha, hb⟩) | ⟨i', hb⟩
    · exact absurd (lt_of_le_of_lt hj' hlt) (not_lt.mpr (hAJ _ hact).1)
    · rw [hbirth i' a hb]; simp only [↓reduceIte]; exact le_of_lt ha
    · rw [hbirth i' _ hb]; simp
  · rw [if_neg hlt]
    have hle : j.castSucc ≤ (pdLifeActive S γ p.1).max' hA := by
      have := (hAJ _ h1).2
      simp only [Fin.le_def, Fin.val_succ, Fin.coe_castSucc] at this ⊢
      omega
    rw [if_neg (not_lt.mpr hle)]
    trivial

/-- Target fill of group `i` with label `q`: promote its memory particle if there is one,
otherwise a fresh birth. -/
def guidedFill {K : ℕ} (F : PDFix K) (S : PDScale) (τ : LogPoint S.x K) (i : Fin K)
    (q : primeBand S.x (F.a i)) : Fin (τ.1.2.2 i).length ⊕ primeBand S.x (F.a i) :=
  if h : ∃ r : Fin (τ.1.2.2 i).length, ((τ.1.2.2 i).get r).1 = q.1 then
    Sum.inl (Classical.choose h) else Sum.inr q

/-- The edge choice forced by `H` and the target labels `q`. -/
def guidedEdgeChoice {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x)) (τ : LogPoint S.x K)
    (π : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (q : (i : Fin K) → primeBand S.x (F.a i)) :
    (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i :=
  fun i => (decide (lifePendingIn F S γ H i (permuteLists π τ.1.2.1 i (lastSlot S.x))
      false j.succ), guidedFill F S τ i (q i))

theorem guidedFill_inl {K : ℕ} (F : PDFix K) (S : PDScale) (τ : LogPoint S.x K) (i : Fin K)
    (q : primeBand S.x (F.a i)) (k : Fin (τ.1.2.2 i).length)
    (h : guidedFill F S τ i q = Sum.inl k) : ((τ.1.2.2 i).get k).1 = q.1 := by
  unfold guidedFill at h
  split_ifs at h with hex
  · cases h
    exact Classical.choose_spec hex

theorem guidedFill_inr {K : ℕ} (F : PDFix K) (S : PDScale) (τ : LogPoint S.x K) (i : Fin K)
    (q q' : primeBand S.x (F.a i))
    (h : guidedFill F S τ i q = Sum.inr q') :
    q' = q ∧ ¬ ∃ r : Fin (τ.1.2.2 i).length, ((τ.1.2.2 i).get r).1 = q.1 := by
  unfold guidedFill at h
  split_ifs at h with hex
  cases h
  exact ⟨rfl, hex⟩

theorem guidedFill_label {K : ℕ} (F : PDFix K) (S : PDScale) (τ : LogPoint S.x K) (i : Fin K)
    (q : primeBand S.x (F.a i)) (b : Bool) :
    edgeNewLabel (x := S.x) (a := F.a) (l := τ.1.2.2 i) (i := i) (b, guidedFill F S τ i q) =
      q.1 := by
  unfold edgeNewLabel
  cases hf : guidedFill F S τ i q with
  | inl k => exact guidedFill_inl F S τ i q k hf
  | inr q' => rw [(guidedFill_inr F S τ i q q' hf).1]

theorem index_inj_of_nodup (l : List Particle) (hnd : (l.map Prod.fst).Nodup)
    (r r' : Fin l.length) (h : (l.get r).1 = (l.get r').1) : r = r' := by
  have h' : (l.map Prod.fst).get ⟨r.val, by simp⟩ = (l.map Prod.fst).get ⟨r'.val, by simp⟩ := by
    simpa using h
  exact Fin.ext (by simpa using (hnd.get_inj_iff).mp h')

theorem slot_eq_last {x : ℝ} (jj : Fin (slotCount x)) (h : ¬ jj.val < momentJ x) :
    jj = lastSlot x := by
  apply Fin.ext
  have := jj.isLt
  simp only [slotCount] at this
  simp only [lastSlot]
  omega

/-- Activity at both ends of an edge in terms of the permuted source and target lists. -/
theorem active_iff_permute {K : ℕ} (S : PDScale) (γ : EnvPath S.x K)
    (π : Fin K → Equiv.Perm (Fin (slotCount S.x))) (j : Fin (pathLength S.x + 1)) (p : ℕ) :
    IsActiveAt γ p j ↔ ∃ i jj, permuteLists π (γ j).2 i jj = p := by
  constructor
  · rintro ⟨i, jj, h⟩
    exact ⟨i, (π i).symm jj, by simpa [permuteLists] using h⟩
  · rintro ⟨i, jj, h⟩
    exact ⟨i, π i jj, h⟩

/-- The slot facts of a guided edge with source lists `P` and target lists `Q`. -/
theorem edge_slot_facts {K : ℕ} (F : PDFix K) (S : PDScale)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (P Q : PrimeLists S.x K) (hP : ValidPrimeLists S.x K F.a P)
    (hQ : ValidPrimeLists S.x K F.a Q) (hST : IsSlotTransition P Q)
    (i : Fin K) (p : ℕ) (hp : p ∈ primeBand S.x (F.a i)) :
    ((∃ i' jj, Q i' jj = p) ∧ ¬ (∃ i' jj, P i' jj = p) → p = Q i (lastSlot S.x)) ∧
      ((∃ i' jj, P i' jj = p) ∧ ¬ (∃ i' jj, Q i' jj = p) → p = P i (lastSlot S.x)) ∧
      (¬ ∃ i' jj, P i' jj = Q i (lastSlot S.x)) ∧
      (¬ ∃ i' jj, Q i' jj = P i (lastSlot S.x)) := by
  have hgroupP : ∀ i' jj, P i' jj = p → i' = i := by
    intro i' jj h
    by_contra hne
    exact Finset.disjoint_left.mp (hBands i' i hne) (h ▸ (hP.1 i' jj).2) hp
  have hgroupQ : ∀ i' jj, Q i' jj = p → i' = i := by
    intro i' jj h
    by_contra hne
    exact Finset.disjoint_left.mp (hBands i' i hne) (h ▸ (hQ.1 i' jj).2) hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨i', jj, h⟩, hn⟩
    have hi := hgroupQ i' jj h
    subst hi
    by_cases hjj : jj.val < momentJ S.x
    · exact absurd ⟨i', jj, (hST.1 i' jj hjj).symm.trans h⟩ hn
    · rw [← slot_eq_last jj hjj]; exact h.symm
  · rintro ⟨⟨i', jj, h⟩, hn⟩
    have hi := hgroupP i' jj h
    subst hi
    by_cases hjj : jj.val < momentJ S.x
    · exact absurd ⟨i', jj, (hST.1 i' jj hjj).trans h⟩ hn
    · rw [← slot_eq_last jj hjj]; exact h.symm
  · rintro ⟨i', jj, h⟩
    exact hST.2 i i' jj h.symm
  · rintro ⟨i', jj, h⟩
    by_cases hjj : jj.val < momentJ S.x
    · rw [hST.1 i' jj hjj] at h
      have hP' : P i (lastSlot S.x) ∈ primeBand S.x (F.a i') := h ▸ (hP.1 i' jj).2
      by_cases hii : i' = i
      · subst hii
        have hne : jj ≠ lastSlot S.x := by
          intro he; rw [he] at hjj; simp [lastSlot] at hjj
        exact hP.2 i' jj (lastSlot S.x) hne h
      · exact Finset.disjoint_left.mp (hBands i i' (Ne.symm hii)) (hP.1 i _).2 hP'
    · rw [slot_eq_last jj hjj] at h
      exact hST.2 i' i (lastSlot S.x) h

theorem bornBefore_succ {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (p : ℕ) (j : Fin (pathLength S.x)) :
    lifeBornBefore F S γ H p j.succ ↔
      (lifeBornBefore F S γ H p j.castSucc ∨ ∃ i, lifeBornAt F S γ H i p j.castSucc) ∨
        IsActiveAt γ p j.succ := by
  unfold lifeBornBefore
  constructor
  · rintro (⟨j', hj', hact⟩ | ⟨i, a, ha, hb⟩)
    · by_cases h : j' = j.succ
      · subst h; right; exact hact
      · left; left; left
        refine ⟨j', ?_, hact⟩
        simp only [Fin.le_def, Fin.val_succ, Fin.coe_castSucc, Fin.ext_iff] at *
        omega
    · by_cases h : a = j.castSucc
      · subst h; left; right; exact ⟨i, hb⟩
      · left; left; right
        refine ⟨i, a, ?_, hb⟩
        simp only [Fin.lt_def, Fin.val_succ, Fin.coe_castSucc, Fin.ext_iff] at *
        omega
  · rintro (((⟨j', hj', hact⟩ | ⟨i, a, ha, hb⟩) | ⟨i, hb⟩) | hact)
    · exact Or.inl ⟨j', le_trans hj' (le_of_lt (Fin.castSucc_lt_succ)), hact⟩
    · exact Or.inr ⟨i, a, lt_trans ha (Fin.castSucc_lt_succ), hb⟩
    · exact Or.inr ⟨i, _, Fin.castSucc_lt_succ, hb⟩
    · exact Or.inl ⟨j.succ, le_rfl, hact⟩

/-- The forced edge choice leads from the after-ghost life state at `j` to the life state
at `j+1`. -/
theorem guided_edge_output {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x)) (τ : LogPoint S.x K)
    (hτ : IsLifeStateAfter F S γ H j.castSucc τ)
    (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (hST : IsSlotTransition (permuteLists π (γ j.castSucc).2)
      (permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2))
    (q : (i : Fin K) → primeBand S.x (F.a i))
    (hq : ∀ i, (q i).1 =
      permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2 i (lastSlot S.x)) :
    IsLifeState F S γ H j.succ
      (edgeTraceOutput F S j.val (γ j.succ).1 τ
        (π, guidedEdgeChoice F S γ H j τ π q, π')) := by
  obtain ⟨hpos, hnd, hmem, hlnd, hlmem⟩ := hτ
  have hz : τ.1.1 = (γ j.castSucc).1 := congrArg Prod.fst hpos
  have hl : τ.1.2.1 = (γ j.castSucc).2 := congrArg Prod.snd hpos
  set P := permuteLists π (γ j.castSucc).2 with hPdef
  set Q := permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2 with hQdef
  have hPv : ValidPrimeLists S.x K F.a P :=
    guided_validPrimeLists_permute π _ (hγ.1 j.castSucc).2
  have hQv : ValidPrimeLists S.x K F.a Q :=
    guided_validPrimeLists_permute _ _ (hγ.1 j.succ).2
  have hactj : ∀ p, IsActiveAt γ p j.castSucc ↔ ∃ i jj, P i jj = p :=
    active_iff_permute S γ π _
  have hactj1 : ∀ p, IsActiveAt γ p j.succ ↔ ∃ i jj, Q i jj = p :=
    active_iff_permute S γ (fun i => (π' i)⁻¹) _
  have hfacts := edge_slot_facts F S hBands P Q hPv hQv hST
  set c := guidedEdgeChoice F S γ H j τ π q with hcdef
  have hc1 : ∀ i, (c i).1 =
      decide (lifePendingIn F S γ H i (P i (lastSlot S.x)) false j.succ) := by
    intro i
    show decide (lifePendingIn F S γ H i (permuteLists π τ.1.2.1 i (lastSlot S.x))
      false j.succ) = _
    rw [hl]
  have hc2 : ∀ i, (c i).2 = guidedFill F S τ i (q i) := fun i => rfl
  have hL : edgeTargetLists F S (permuteLogPoint π τ).1 c = Q := by
    funext i jj
    unfold edgeTargetLists
    split_ifs with hjj
    · show permuteLists π τ.1.2.1 i jj = Q i jj
      rw [hl]
      exact (hST.1 i jj hjj).symm
    · rw [slot_eq_last jj hjj, ← hq i]
      exact guidedFill_label F S τ i (q i) _
  have hmemOut : ∀ i, (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.2 i =
      removeIndices (τ.1.2.2 i) (match guidedFill F S τ i (q i) with
          | Sum.inl k => {k}
          | Sum.inr _ => ∅) ++
        (if (c i).1 then
          [anchorAt (P i (lastSlot S.x)) (γ j.castSucc).1] else []) := by
    intro i
    show edgeNewMemory F S (permuteLogPoint π τ).1 c i = _
    unfold edgeNewMemory
    rw [hc2 i]
    simp only [permuteLogPoint, hl, hz, hPdef]
    cases guidedFill F S τ i (q i) <;> rfl
  have hlogOut : (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).2.map Prod.snd =
      τ.2.map Prod.snd ++ (List.finRange K).flatMap (fun i =>
        match guidedFill F S τ i (q i) with
        | Sum.inl _ => []
        | Sum.inr p => [p.1]) := by
    show (τ.2 ++ edgeBirths F S j.val (permuteLogPoint π τ).1 c).map Prod.snd = _
    rw [List.map_append]
    unfold edgeBirths
    rw [List.map_flatMap]
    congr 1
    apply congrArg (fun f => (List.finRange K).flatMap f)
    funext i
    rw [hc2 i]
    cases guidedFill F S τ i (q i) <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show ((γ j.succ).1, permuteLists π' (edgeTargetLists F S (permuteLogPoint π τ).1 c)) =
      γ j.succ
    rw [hL]
    refine Prod.ext ?_ ?_
    · rfl
    funext i jj
    simp [hQdef, permuteLists]
  · intro i
    rw [hmemOut i, List.map_append]
    refine List.Nodup.append (((removeIndices_sublist' _ _).map Prod.fst).nodup (hnd i)) ?_ ?_
    · split_ifs <;> simp
    · intro a ha hb
      split_ifs at hb with hbit
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
        obtain ⟨hp, hpend, -⟩ := (hmem i y).mp ((removeIndices_sublist' _ _).subset hy)
        apply not_pending_of_active S γ _ _ true _ _ hpend
        rw [hb]
        exact (hactj _).mpr ⟨i, _, rfl⟩
      · simp at hb
  · intro i x
    rw [hmemOut i, List.mem_append, mem_removeIndices_iff]
    constructor
    · rintro (⟨r, hrD, rfl⟩ | hx)
      · obtain ⟨hp, hpend, hanc⟩ := (hmem i _).mp (List.get_mem _ r)
        have hnact0 : ¬ IsActiveAt γ ((τ.1.2.2 i).get r).1 j.castSucc :=
          fun h => not_pending_of_active S γ _ _ true _ h hpend
        have hnact1 : ¬ IsActiveAt γ ((τ.1.2.2 i).get r).1 j.succ := by
          intro h1
          have hqi := (hfacts i _ hp).1 ⟨(hactj1 _).mp h1, fun h => hnact0 ((hactj _).mpr h)⟩
          apply hrD
          rcases hf : guidedFill F S τ i (q i) with k | q'
          · have hk := guidedFill_inl F S τ i (q i) k hf
            simp only [Finset.mem_singleton]
            apply index_inj_of_nodup _ (hnd i)
            rw [hk, hq i, hqi]
          · exact absurd ⟨r, by rw [hq i, hqi]⟩ (guidedFill_inr F S τ i (q i) q' hf).2
        exact ⟨hp, (pending_edge_iff S γ _ _ j hnact0 hnact1).mpr hpend, hanc⟩
      · split_ifs at hx with hbit
        · rw [List.mem_singleton] at hx
          subst hx
          rw [hc1 i] at hbit
          obtain ⟨hp, hpend⟩ := of_decide_eq_true hbit
          have hact : IsActiveAt γ (P i (lastSlot S.x)) j.castSucc :=
            (hactj _).mpr ⟨i, _, rfl⟩
          refine ⟨hp, hpend, ?_⟩
          show (projLine (P i (lastSlot S.x)) (γ j.castSucc).1).val =
            (lifeLine S γ (P i (lastSlot S.x)) (H i ⟨P i (lastSlot S.x), hp⟩).1).val
          rw [lifeLine_of_active S γ _ _ _ hact]
        · simp at hx
    · rintro ⟨hp, hpend, hanc⟩
      have hn1 : ¬ IsActiveAt γ x.1 j.succ :=
        fun h => not_pending_of_active S γ _ _ false _ h hpend
      by_cases h0 : IsActiveAt γ x.1 j.castSucc
      · right
        have hx1 := (hfacts i x.1 hp).2.1 ⟨(hactj _).mp h0, fun h => hn1 ((hactj1 _).mpr h)⟩
        have hbit : (c i).1 = true := by
          rw [hc1 i, ← hx1]
          exact decide_eq_true ⟨hp, hpend⟩
        rw [if_pos hbit, List.mem_singleton]
        apply Prod.ext
        · exact hx1
        · show x.2 = (projLine (P i (lastSlot S.x)) (γ j.castSucc).1).val
          rw [hanc, lifeLine_of_active S γ _ _ _ h0, hx1]
      · left
        have hpt := (pending_edge_iff S γ _ _ j h0 hn1).mp hpend
        obtain ⟨r, hr⟩ := List.mem_iff_get.mp ((hmem i x).mpr ⟨hp, hpt, hanc⟩)
        refine ⟨r, ?_, hr⟩
        rcases hf : guidedFill F S τ i (q i) with k | q'
        · simp only [Finset.mem_singleton]
          intro hrk
          subst hrk
          have hk := guidedFill_inl F S τ i (q i) r hf
          rw [hr] at hk
          apply hn1
          rw [hk, hq i]
          exact (hactj1 _).mpr ⟨i, _, rfl⟩
        · simp
  · rw [hlogOut]
    refine List.Nodup.append hlnd ?_ ?_
    · rw [List.nodup_flatMap]
      constructor
      · intro i _
        cases guidedFill F S τ i (q i) <;> simp
      · refine (List.nodup_finRange K).imp ?_
        intro i i' hii a ha ha'
        rcases hf : guidedFill F S τ i (q i) with k | q1 <;> simp only [hf] at ha <;>
          simp at ha
        rcases hf' : guidedFill F S τ i' (q i') with k' | q2 <;> simp only [hf'] at ha' <;>
          simp at ha'
        exact Finset.disjoint_left.mp (hBands i i' hii) (ha ▸ q1.2) (ha' ▸ q2.2)
    · intro a ha hb
      obtain ⟨i, -, hai⟩ := List.mem_flatMap.mp hb
      rcases hf : guidedFill F S τ i (q i) with k | q1 <;> simp only [hf] at hai <;>
        simp at hai
      obtain ⟨hq1, hnone⟩ := guidedFill_inr F S τ i (q i) q1 hf
      subst hq1
      have hlog := (hlmem a).mp ha
      have h1 : IsActiveAt γ (q i).1 j.succ :=
        (hactj1 _).mpr ⟨i, lastSlot S.x, (hq i).symm⟩
      have h0 : ¬ IsActiveAt γ (q i).1 j.castSucc := by
        intro h
        apply (hfacts i _ (q i).2).2.2.1
        rw [← hq i]
        exact (hactj _).mp h
      rw [hai] at hlog
      have hpt := pending_of_entering_logged F S γ H hBands i (q i) j h1 h0 hlog
      apply hnone
      obtain ⟨r, hr⟩ := List.mem_iff_get.mp
        ((hmem i ((q i).1, (lifeLine S γ (q i).1 (H i (q i)).1).val)).mpr ⟨(q i).2, hpt, rfl⟩)
      exact ⟨r, by rw [hr]⟩
  · intro a
    rw [hlogOut, List.mem_append, hlmem, bornBefore_succ]
    constructor
    · rintro (hX | hB)
      · exact Or.inl hX
      · right
        obtain ⟨i, -, hai⟩ := List.mem_flatMap.mp hB
        rcases hf : guidedFill F S τ i (q i) with k | q1 <;> simp only [hf] at hai <;>
          simp at hai
        obtain ⟨hq1, -⟩ := guidedFill_inr F S τ i (q i) q1 hf
        subst hq1
        rw [hai]
        exact (hactj1 _).mpr ⟨i, lastSlot S.x, (hq i).symm⟩
    · rintro (hX | hA)
      · exact Or.inl hX
      by_cases h0 : IsActiveAt γ a j.castSucc
      · exact Or.inl (Or.inl (Or.inl ⟨j.castSucc, le_rfl, h0⟩))
      obtain ⟨i, jj, hij⟩ := (hactj1 a).mp hA
      have hp : a ∈ primeBand S.x (F.a i) := hij ▸ (hQv.1 i jj).2
      have ha := (hfacts i a hp).1 ⟨⟨i, jj, hij⟩, fun h => h0 ((hactj _).mpr h)⟩
      rcases hf : guidedFill F S τ i (q i) with k | q1
      · left
        have hk := guidedFill_inl F S τ i (q i) k hf
        obtain ⟨hpk, hpend, -⟩ := (hmem i _).mp (List.get_mem _ k)
        have hlog : lifeBornBefore F S γ H ((τ.1.2.2 i).get k).1 j.castSucc ∨
            ∃ i', lifeBornAt F S γ H i' ((τ.1.2.2 i).get k).1 j.castSucc :=
          logged_of_pending_true F S γ H i ⟨_, hpk⟩ j.castSucc hpend
        rw [hk, hq i, ← ha] at hlog
        exact hlog
      · right
        obtain ⟨hq1, -⟩ := guidedFill_inr F S τ i (q i) q1 hf
        subst hq1
        refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
        rw [hf]
        simp [ha, hq i]

/-- A visited edge output has target lists `Q`. -/
theorem visit_target {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (j : Fin (pathLength S.x)) (τ : LogPoint S.x K)
    (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i)
    (hv : ((edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.1,
      (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')).1.2.1) = γ j.succ) :
    edgeTargetLists F S (permuteLogPoint π τ).1 c =
      permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2 := by
  have h2 : permuteLists π' (edgeTargetLists F S (permuteLogPoint π τ).1 c) =
      (γ j.succ).2 := congrArg Prod.snd hv
  funext i jj
  have := congrFun (congrFun h2 i) ((π' i)⁻¹ jj)
  simpa [permuteLists] using this

/-- Every guided edge choice other than the forced one has a vanishing continuation. -/
theorem guided_edge_other_zero {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x)) (τ : LogPoint S.x K)
    (hτ : IsLifeStateAfter F S γ H j.castSucc τ)
    (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (q : (i : Fin K) → primeBand S.x (F.a i))
    (hq : ∀ i, (q i).1 =
      permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2 i (lastSlot S.x))
    (G : LogPoint S.x K → ℂ)
    (hGv : ∀ υ, G υ ≠ 0 → (υ.1.1, υ.1.2.1) = γ j.succ)
    (hGn : ∀ υ, G υ ≠ 0 → (υ.2.map Prod.snd).Nodup)
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i)
    (hc : ∀ i, (c i).1 = (guidedEdgeChoice F S γ H j τ π q i).1)
    (hne : c ≠ guidedEdgeChoice F S γ H j τ π q) :
    G (edgeTraceOutput F S j.val (γ j.succ).1 τ (π, c, π')) = 0 := by
  obtain ⟨-, hnd, hmem, -, hlmem⟩ := hτ
  by_contra hG0
  have hL := visit_target F S γ j τ π π' c (hGv _ hG0)
  have hlogNd := hGn _ hG0
  apply hne
  funext i
  have hlab : edgeNewLabel (c i) = (q i).1 := by
    have := congrFun (congrFun hL i) (lastSlot S.x)
    simp only [edgeTargetLists, lastSlot, lt_irrefl, ↓reduceIte] at this
    rw [hq i]
    exact this
  refine Prod.ext (hc i) ?_
  show (c i).2 = guidedFill F S τ i (q i)
  rcases hci : (c i).2 with k | p
  · have hk : ((τ.1.2.2 i).get k).1 = (q i).1 := by
      rw [← hlab]; unfold edgeNewLabel; rw [hci]
    have hex : ∃ r : Fin (τ.1.2.2 i).length, ((τ.1.2.2 i).get r).1 = (q i).1 := ⟨k, hk⟩
    unfold guidedFill
    rw [dif_pos hex]
    congr 1
    apply index_inj_of_nodup _ (hnd i)
    rw [hk, Classical.choose_spec hex]
  · have hp : p = q i := by
      apply Subtype.ext
      rw [← hlab]; unfold edgeNewLabel; rw [hci]
    subst hp
    unfold guidedFill
    split_ifs with hex
    · exfalso
      obtain ⟨r, hr⟩ := hex
      obtain ⟨hpr, hpend, -⟩ := (hmem i _).mp (List.get_mem _ r)
      have hlog : lifeBornBefore F S γ H ((τ.1.2.2 i).get r).1 j.castSucc ∨
          ∃ i', lifeBornAt F S γ H i' ((τ.1.2.2 i).get r).1 j.castSucc :=
        logged_of_pending_true F S γ H i ⟨_, hpr⟩ j.castSucc hpend
      rw [hr] at hlog
      have h1 : ((q i : ℕ)) ∈ τ.2.map Prod.snd := (hlmem _).mpr hlog
      have h2 : ((q i : ℕ)) ∈ (edgeBirths F S j.val (permuteLogPoint π τ).1 c).map Prod.snd := by
        refine List.mem_map.mpr ⟨(BirthAddress.edge j.val i, (q i : ℕ)), ?_, rfl⟩
        unfold edgeBirths
        refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
        simp only [hci]
        simp
      have hnd' : (τ.2.map Prod.snd ++
          (edgeBirths F S j.val (permuteLogPoint π τ).1 c).map Prod.snd).Nodup := by
        rw [← List.map_append]; exact hlogNd
      exact List.disjoint_of_nodup_append hnd' h1 h2
    · rfl

theorem guided_target_eq {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x)) (τ : LogPoint S.x K)
    (hl : τ.1.2.1 = (γ j.castSucc).2)
    (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (hST : IsSlotTransition (permuteLists π (γ j.castSucc).2)
      (permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2))
    (q : (i : Fin K) → primeBand S.x (F.a i))
    (hq : ∀ i, (q i).1 =
      permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2 i (lastSlot S.x)) :
    edgeTargetLists F S (permuteLogPoint π τ).1 (guidedEdgeChoice F S γ H j τ π q) =
      permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2 := by
  funext i jj
  unfold edgeTargetLists
  split_ifs with hjj
  · show permuteLists π τ.1.2.1 i jj = _
    rw [hl]
    exact (hST.1 i jj hjj).symm
  · rw [slot_eq_last jj hjj, ← hq i]
    exact guidedFill_label F S τ i (q i) _

/-- The entry factor of group `i` for the forced fill. -/
theorem guided_entry_eq {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x)) (τ : LogPoint S.x K)
    (hτ : IsLifeStateAfter F S γ H j.castSucc τ)
    (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (hST : IsSlotTransition (permuteLists π (γ j.castSucc).2)
      (permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2))
    (q : (i : Fin K) → primeBand S.x (F.a i))
    (hq : ∀ i, (q i).1 =
      permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2 i (lastSlot S.x)) (i : Fin K) :
    (if ∃ r : Fin (τ.1.2.2 i).length, ((τ.1.2.2 i).get r).1 = (q i).1 then
        (bandMass S.x (F.a i))⁻¹ else memoryNu S.x K F.a F.q_d i (q i).1) =
      ∏ p : primeBand S.x (F.a i),
        (if IsActiveAt γ p.1 j.succ ∧ ¬ IsActiveAt γ p.1 j.castSucc then
          (if pdLifePending S γ p.1 (H i p) true j.castSucc then (bandMass S.x (F.a i))⁻¹
            else memoryNu S.x K F.a F.q_d i p.1)
        else 1) := by
  obtain ⟨-, hnd, hmem, -, -⟩ := hτ
  set P := permuteLists π (γ j.castSucc).2 with hPdef
  set Q := permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2 with hQdef
  have hPv : ValidPrimeLists S.x K F.a P :=
    guided_validPrimeLists_permute π _ (hγ.1 j.castSucc).2
  have hQv : ValidPrimeLists S.x K F.a Q :=
    guided_validPrimeLists_permute _ _ (hγ.1 j.succ).2
  have hactj : ∀ p, IsActiveAt γ p j.castSucc ↔ ∃ i jj, P i jj = p :=
    active_iff_permute S γ π _
  have hactj1 : ∀ p, IsActiveAt γ p j.succ ↔ ∃ i jj, Q i jj = p :=
    active_iff_permute S γ (fun i => (π' i)⁻¹) _
  have hfacts := edge_slot_facts F S hBands P Q hPv hQv hST
  have h1 : IsActiveAt γ (q i).1 j.succ := (hactj1 _).mpr ⟨i, lastSlot S.x, (hq i).symm⟩
  have h0 : ¬ IsActiveAt γ (q i).1 j.castSucc := by
    intro h
    apply (hfacts i _ (q i).2).2.2.1
    rw [← hq i]
    exact (hactj _).mp h
  rw [Finset.prod_eq_single (q i)]
  · rw [if_pos (⟨h1, h0⟩ : IsActiveAt γ (q i).1 j.succ ∧ ¬ IsActiveAt γ (q i).1 j.castSucc)]
    by_cases hex : ∃ r : Fin (τ.1.2.2 i).length, ((τ.1.2.2 i).get r).1 = (q i).1
    · rw [if_pos hex]
      obtain ⟨r, hr⟩ := hex
      obtain ⟨hp, hpend, -⟩ := (hmem i _).mp (List.get_mem _ r)
      have : pdLifePending S γ (q i).1 (H i (q i)) true j.castSucc := by
        have e : (⟨((τ.1.2.2 i).get r).1, hp⟩ : primeBand S.x (F.a i)) = q i := Subtype.ext hr
        rw [← e]; exact hpend
      rw [if_pos this]
    · rw [if_neg hex, if_neg]
      intro hpend
      apply hex
      obtain ⟨r, hr⟩ := List.mem_iff_get.mp
        ((hmem i ((q i).1, (lifeLine S γ (q i).1 (H i (q i)).1).val)).mpr ⟨(q i).2, hpend, rfl⟩)
      exact ⟨r, by rw [hr]⟩
  · intro p _ hpq
    rw [if_neg]
    rintro ⟨hp1, hp0⟩
    apply hpq
    apply Subtype.ext
    rw [hq i]
    exact (hfacts i p.1 p.2).1 ⟨(hactj1 _).mp hp1, fun h => hp0 ((hactj _).mpr h)⟩
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The edgeGeo test of a pair of slot permutations at edge `j`. -/
def edgeTest {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (j : Fin (pathLength S.x)) (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x))) : Prop :=
  let P := permuteLists π (γ j.castSucc).2
  let Q := permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2
  let z := (γ j.castSucc).1
  let z' := (γ j.succ).1
  ValidPrimeLists S.x K F.a P ∧ ValidPrimeLists S.x K F.a Q ∧
    IsSlotTransition P Q ∧ IsPadAdmissible S.d₀ (sharedProduct P) (det2 z z') ∧
    Int.gcd z'.1 z'.2 = 1 ∧ envBox S w z ∧ envBox S w z' ∧
    envGood F S w (z, P) ∧ envGood F S w (z', Q)

/-- The literal charge of the forced edge choice. -/
theorem guided_edge_charge {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x)) (τ : LogPoint S.x K)
    (hτ : IsLifeStateAfter F S γ H j.castSucc τ)
    (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (hST : IsSlotTransition (permuteLists π (γ j.castSucc).2)
      (permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2))
    (q : (i : Fin K) → primeBand S.x (F.a i))
    (hq : ∀ i, (q i).1 =
      permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2 i (lastSlot S.x)) :
    edgeTraceCharge F S ρ w j.val (γ j.succ).1 τ (π, guidedEdgeChoice F S γ H j τ π q, π') =
      ((permCount S.x K : ℂ)⁻¹) ^ 2 *
        (if edgeTest F S w γ j π π' then
          ((∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
              lifeEdgeLocal F S ρ γ i p.1 (H i p) j : ℝ) : ℂ) *
            (edgeMultiplier F S (decide (j.val % 2 = 0)) true
                (permuteLists π (γ j.castSucc).2)
                (permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2)
                (γ j.castSucc).1 (γ j.succ).1 -
              edgeMultiplier F S (decide (j.val % 2 = 0)) false
                (permuteLists π (γ j.castSucc).2)
                (permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2)
                (γ j.castSucc).1 (γ j.succ).1)
        else 0) := by
  have hτ0 := hτ
  obtain ⟨hpos, hnd, hmem, -, -⟩ := hτ0
  have hz : τ.1.1 = (γ j.castSucc).1 := congrArg Prod.fst hpos
  have hl : τ.1.2.1 = (γ j.castSucc).2 := congrArg Prod.snd hpos
  have hL := guided_target_eq F S γ H j τ hl π π' hST q hq
  have hυ := guided_edge_output F S γ hγ hBands H j τ hτ π π' hST q hq
  set c := guidedEdgeChoice F S γ H j τ π q with hcdef
  have e1 : (permuteLogPoint π τ).1.2.1 = permuteLists π (γ j.castSucc).2 := by
    show permuteLists π τ.1.2.1 = _
    rw [hl]
  have e2 : (permuteLogPoint π τ).1.1 = (γ j.castSucc).1 := hz
  have hQv : ValidPrimeLists S.x K F.a (permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2) :=
    guided_validPrimeLists_permute _ _ (hγ.1 j.succ).2
  -- promoted particles hit the target
  have hprom : ∀ i, ∀ k, (c i).2 = Sum.inl k →
      particleHits (((permuteLogPoint π τ).1.2.2 i).get k) (γ j.succ).1 := by
    intro i k hk
    have hk' := guidedFill_inl F S τ i (q i) k hk
    obtain ⟨hp, -, hanc⟩ := (hmem i _).mp (List.get_mem _ k)
    have h1 : IsActiveAt γ (q i).1 j.succ :=
      (active_iff_permute S γ (fun i => (π' i)⁻¹) j.succ _).mpr
        ⟨i, lastSlot S.x, (hq i).symm⟩
    have e : (⟨((τ.1.2.2 i).get k).1, hp⟩ : primeBand S.x (F.a i)) = q i := Subtype.ext hk'
    show ((τ.1.2.2 i).get k).2 = (projLine ((τ.1.2.2 i).get k).1 (γ j.succ).1).val
    rw [hanc]
    have hline := lifeLine_of_active S γ _ (H i (q i)) j.succ h1
    rw [← e] at hline
    rw [hline]
  have hAdm : EdgeAdmissible F S w (permuteLogPoint π τ).1 c (γ j.succ).1 ↔
      edgeTest F S w γ j π π' := by
    unfold EdgeAdmissible edgeTest
    rw [hL, e1, e2]
    exact ⟨fun h => h.2, fun h => ⟨hprom, h⟩⟩
  unfold edgeTraceCharge
  dsimp only
  congr 1
  by_cases ht : edgeTest F S w γ j π π'
  · rw [if_pos (hAdm.mpr ht), if_pos ht, hL, e1, e2]
    congr 1
    congr 1
    have hA : ρ ^ (∑ i, hitCount ((permuteLogPoint π τ).1.2.2 i) (γ j.castSucc).1) =
        ∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
          (if pdLifePending S γ p.1 (H i p) true j.castSucc ∧
              lifeHit S γ p.1 (H i p).1 j.castSucc then ρ else 1) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro i _
      rw [hitCount_life F S γ H i true j.castSucc j.castSucc ((permuteLogPoint π τ).1.2.2 i)
        (hτ.2.1 i) (hτ.2.2.1 i)]
      exact (prod_ite_one_pow _ ρ).symm
    have hY : (∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
          lifeEdgeLocal F S ρ γ i p.1 (H i p) j) =
        (∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
          (if pdLifePending S γ p.1 (H i p) true j.castSucc ∧
              lifeHit S γ p.1 (H i p).1 j.castSucc then ρ else 1)) *
        (∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
          (if IsActiveAt γ p.1 j.succ ∧ ¬ IsActiveAt γ p.1 j.castSucc then
            (if pdLifePending S γ p.1 (H i p) true j.castSucc then (bandMass S.x (F.a i))⁻¹
              else memoryNu S.x K F.a F.q_d i p.1)
          else 1)) *
        (∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
          (if pdLifePending S γ p.1 (H i p) false j.succ ∧
              lifeHit S γ p.1 (H i p).1 j.succ then ρ else 1)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      rfl
    rw [hY, hA]
    congr 1
    · congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [← guided_entry_eq F S γ hγ hBands H j τ hτ π π' hST q hq i]
      split
      · rename_i k heq
        have hf : guidedFill F S τ i (q i) = Sum.inl k := heq
        rw [if_pos ⟨k, guidedFill_inl F S τ i (q i) k hf⟩]
      · rename_i p' heq
        have hf : guidedFill F S τ i (q i) = Sum.inr p' := heq
        obtain ⟨hp', hnone⟩ := guidedFill_inr F S τ i (q i) p' hf
        rw [if_neg hnone, hp']
    · rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro i _
      erw [hitCount_life F S γ H i false j.succ j.succ _ (hυ.2.1 i) (hυ.2.2.1 i)]
      exact (prod_ite_one_pow _ ρ).symm
  · rw [if_neg (mt hAdm.mp ht), if_neg ht]

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
