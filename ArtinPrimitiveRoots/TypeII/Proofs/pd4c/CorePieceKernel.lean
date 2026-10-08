import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.GroupKernel
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.PhysicalTranspose
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Mass

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

theorem pd4c_prod_ite_all {ι : Type*} [Fintype ι] (P : ι → Prop) [∀ i, Decidable (P i)] [Decidable (∀ i, P i)] (f : ι → ℂ) :
    (if ∀ i, P i then ∏ i, f i else 0) = ∏ i, if P i then f i else 0 := by
  by_cases h : ∀ i, P i
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i hi
    exact (if_pos (h i)).symm
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

theorem pd4c_bool_eq_decide (b : Bool) (P : Prop) [Decidable P] : b = decide P ↔ (b = true ↔ P) := by
  cases b <;> by_cases h : P <;> simp [h]

theorem pd4c_storedSet_eq_iff {K : ℕ} (F : PDFix K) (S : PDScale) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (St : Finset (Fin K)) :
    edgeStoredSet c = St ↔ ∀ i, (c i).1 = decide (i ∈ St) := by
  constructor
  · intro h i
    apply (pd4c_bool_eq_decide _ _).mpr
    have hm := Finset.ext_iff.mp h i
    simpa only [edgeStoredSet, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  · intro h
    ext i
    simp [edgeStoredSet, h i]

theorem pd4c_promotedSet_eq_iff {K : ℕ} (F : PDFix K) (S : PDScale) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (Pr : Finset (Fin K)) :
    edgePromotedSet c = Pr ↔ ∀ i, (c i).2.isLeft = decide (i ∈ Pr) := by
  constructor
  · intro h i
    apply (pd4c_bool_eq_decide _ _).mpr
    have hm := Finset.ext_iff.mp h i
    simpa only [edgePromotedSet, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  · intro h
    ext i
    simp [edgePromotedSet, h i]

theorem pd4c_targetLists_last {K : ℕ} (F : PDFix K) (S : PDScale) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
    edgeTargetLists F S s c i (lastSlot S.x) = edgeNewLabel (c i) := by
  simp [edgeTargetLists, lastSlot]

theorem pd4c_targetLists_eq_of_labels {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (q : PrimeLists S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (hshared : ∀ i j, j.val < momentJ S.x → q i j = s.2.1 i j)
    (hlabels : ∀ i, edgeNewLabel (c i) = q i (lastSlot S.x)) : edgeTargetLists F S s c = q := by
  funext i j
  by_cases hj : j.val < momentJ S.x
  · simpa only [edgeTargetLists, if_pos hj] using (hshared i j hj).symm
  · have hlast : j = lastSlot S.x := by
      apply Fin.ext
      have hlt := j.isLt
      dsimp [slotCount] at hlt
      dsimp [lastSlot]
      omega
    subst j
    rw [pd4c_targetLists_last]
    exact hlabels i

def Pd4cTargetChoice {K : ℕ} (F : PDFix K) (S : PDScale) (s t : MemPoint S.x K)
    (St Pr : Finset (Fin K)) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) : Prop :=
  ∀ i, (c i).1 = decide (i ∈ St) ∧ (c i).2.isLeft = decide (i ∈ Pr) ∧
    edgeNewLabel (c i) = t.2.1 i (lastSlot S.x) ∧
      (match (c i).2 with | Sum.inl k => particleHits ((s.2.2 i).get k) t.1 | Sum.inr _ => True)

/-- The physical restrictions and independent group conditions give exactly the edge restrictions. -/
theorem pd4c_targetChoice_admissible_iff {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (s t : MemPoint S.x K) (hs : MemValid F S s) (St Pr : Finset (Fin K))
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :
    (edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c t.1 ∧
      edgeTargetLists F S s c = t.2.1) ↔
      Pd4cPhysicalEdge F S w s.2.1 t.2.1 s.1 t.1 ∧ Pd4cTargetChoice F S s t St Pr c := by
  constructor
  · rintro ⟨hSt, hPr, hadm, htarget⟩
    have hphy := pd4c_edgeAdmissible_physical F S w s c t.1 hs hadm
    rw [htarget] at hphy
    refine ⟨hphy, ?_⟩
    intro i
    have hlabel := congrArg (fun p : PrimeLists S.x K => p i (lastSlot S.x)) htarget
    rw [pd4c_targetLists_last] at hlabel
    refine ⟨(pd4c_storedSet_eq_iff F S s c St).mp hSt i,
      (pd4c_promotedSet_eq_iff F S s c Pr).mp hPr i, hlabel, ?_⟩
    cases hc : (c i).2 with
    | inl k => exact hadm.1 i k hc
    | inr p => trivial
  · rintro ⟨hphy, hchoice⟩
    rcases hphy with ⟨hz, hz', hp, hq, hslot, hpad, hbox, hbox', hgood, hgood'⟩
    have htarget := pd4c_targetLists_eq_of_labels F S s t.2.1 c hslot.1 (fun i => (hchoice i).2.2.1)
    refine ⟨(pd4c_storedSet_eq_iff F S s c St).mpr (fun i => (hchoice i).1),
      (pd4c_promotedSet_eq_iff F S s c Pr).mpr (fun i => (hchoice i).2.1), ?_, htarget⟩
    refine ⟨?_, hp, by simpa only [htarget] using hq,
      by simpa only [htarget] using hslot, hpad, hz', hbox, hbox', hgood,
      by simpa only [htarget] using hgood'⟩
    intro i k hc
    simpa only [hc] using (hchoice i).2.2.2

set_option backward.isDefEq.respectTransparency false in
/-- The actual one-group EdgeChoice sum is the projected damped group kernel. -/
theorem pd4c_groupKernel_choice {K : ℕ} (F : PDFix K) (S : PDScale) (i : Fin K)
    (l m : List Particle) (p : Particle) (q : primeBand S.x (F.a i)) (z z' : ℤ × ℤ)
    (ρ : ℝ) (stored promoted : Bool) :
    ((ρ ^ hitCount l z : ℝ) : ℂ) *
      (∑ c : EdgeChoice S.x F.a l i,
        if c.1 = stored ∧ c.2.isLeft = promoted ∧ edgeNewLabel c = (q : ℕ) ∧
          (match c.2 with | Sum.inl k => particleHits (l.get k) z' | Sum.inr _ => True)
        then (((match c.2 with
          | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
          | Sum.inr r => memoryNu S.x K F.a F.q_d i r : ℝ) : ℂ)) *
            pd4c_listDampedDelta ρ z' m (pd4c_groupNewMemory l p c)
        else 0) =
      pd4c_groupProjectedKernel (fun e : Particle => memoryNu S.x K F.a F.q_d i e.1)
        (bandMass S.x (F.a i)) p (anchorAt (q : ℕ) z') stored promoted ρ z z' l m := by
  have h := pd4c_group_choice_fixed_target F S i l p q z' stored promoted
    (pd4c_listDampedDelta ρ z' m)
  unfold pd4c_groupProjectedKernel
  congr 1
  calc
    _ = _ := h
    _ = _ := by
      unfold pd4c_listTransfer pd4c_listCreate
      cases stored <;> cases promoted <;> simp [anchorAt]

def pd4c_corePiece {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ) :
    (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ :=
  plainOp (logEdgePiece F S ρ w j raw St Pr)

def pd4c_coreTarget {K : ℕ} (F : PDFix K) (S : PDScale) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) : MemPoint S.x K :=
  (z', edgeTargetLists F S s c, edgeNewMemory F S s c)

def pd4c_coreCoefficient {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (raw : Bool) (j : ℕ)
    (s : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) : ℂ :=
  (((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
    (∏ i : Fin K, pd4c_choicePrimeWeight F S s i (c i)) *
    ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s c i) z') : ℝ) : ℂ)) *
      edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1 (edgeTargetLists F S s c) s.1 z'

theorem pd4c_projected_delta_zero_pos {x : ℝ} {K : ℕ} (s t : MemPoint x K) (h : s.1 ≠ t.1) :
    memorySym (fun u => if u = t then (1 : ℂ) else 0) s = 0 := by
  rw [pd4c_memorySym_delta_factor]
  exact if_neg (fun hh => h hh.1)

theorem pd4c_projected_delta_zero_active {x : ℝ} {K : ℕ} (s t : MemPoint x K) (h : s.2.1 ≠ t.2.1) :
    memorySym (fun u => if u = t then (1 : ℂ) else 0) s = 0 := by
  rw [pd4c_memorySym_delta_factor]
  exact if_neg (fun hh => h hh.2)

/-- A continuation on one physical slice reduces the infinite position sum to one term. -/
theorem pd4c_corePiece_evalAt {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ) (f : MemPoint S.x K → ℂ)
    (z : ℤ × ℤ) (hf : ∀ u : MemPoint S.x K, u.1 ≠ z → f u = 0) (s : MemPoint S.x K) :
    pd4c_corePiece F S ρ w raw St Pr j f s =
      ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
        if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c z then
          pd4c_coreCoefficient F S ρ raw j s c z * f (pd4c_coreTarget F S s c z) else 0 := by
  change (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      ∑' z', if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c z' then
        pd4c_coreCoefficient F S ρ raw j s c z' * f (pd4c_coreTarget F S s c z') else 0) = _
  apply Finset.sum_congr rfl
  intro c hc
  apply tsum_eq_single z
  intro z' hz'
  by_cases ha : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c z'
  · rw [if_pos ha, hf (pd4c_coreTarget F S s c z') hz', mul_zero]
  · exact if_neg ha

theorem pd4c_corePiece_mul {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ) (a : ℂ) (f : MemPoint S.x K → ℂ) :
    pd4c_corePiece F S ρ w raw St Pr j (fun u => a * f u) =
      fun u => a * pd4c_corePiece F S ρ w raw St Pr j f u := by
  funext s
  unfold pd4c_corePiece plainOp logEdgePiece
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z'
  split_ifs <;> ring

theorem pd4c_corePiece_sum_at_position {K : ℕ} {ι : Type*} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ)
    (R : Finset ι) (f : ι → MemPoint S.x K → ℂ) (z : ℤ × ℤ)
    (hf : ∀ i u, u.1 ≠ z → f i u = 0) (s : MemPoint S.x K) :
    pd4c_corePiece F S ρ w raw St Pr j (fun u => ∑ i ∈ R, f i u) s =
      ∑ i ∈ R, pd4c_corePiece F S ρ w raw St Pr j (f i) s := by
  have hsum u hu : (∑ i ∈ R, f i u) = 0 := Finset.sum_eq_zero fun i hi => hf i u hu
  rw [pd4c_corePiece_evalAt F S ρ w raw St Pr j _ z hsum]
  simp_rw [pd4c_corePiece_evalAt F S ρ w raw St Pr j _ z (hf _)]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases ha : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c z
  · simp only [if_pos ha, Finset.mul_sum]
  · simp only [if_neg ha, Finset.sum_const_zero]

def pd4c_coreProjectedKernel {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ) (s t : MemPoint S.x K) : ℂ :=
  memKernel (fun f => pd4c_corePiece F S ρ w raw St Pr j (memorySym f)) s t

theorem pd4c_coreProjectedKernel_eval {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ) (s t : MemPoint S.x K) :
    pd4c_coreProjectedKernel F S ρ w raw St Pr j s t =
      ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
        if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c t.1 then
          pd4c_coreCoefficient F S ρ raw j s c t.1 *
            memorySym (fun u => if u = t then (1 : ℂ) else 0) (pd4c_coreTarget F S s c t.1) else 0 := by
  exact pd4c_corePiece_evalAt F S ρ w raw St Pr j _ t.1
    (fun u hu => pd4c_projected_delta_zero_pos u t hu) s

def pd4c_coreGroupCoefficient {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (s t : MemPoint S.x K) (i : Fin K) (c : EdgeChoice S.x F.a (s.2.2 i) i) : ℂ :=
  ((ρ ^ hitCount (s.2.2 i) s.1 : ℝ) : ℂ) * (pd4c_choicePrimeWeight F S s i c : ℂ) *
    pd4c_listDampedDelta ρ t.1 (t.2.2 i)
      (pd4c_groupNewMemory (s.2.2 i) (anchorAt (s.2.1 i (lastSlot S.x)) s.1) c)

/-- The projected continuation separates the coefficient into independent group factors. -/
theorem pd4c_coreCoefficient_factor {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (raw : Bool) (j : ℕ) (s t : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (hq : edgeTargetLists F S s c = t.2.1) :
    pd4c_coreCoefficient F S ρ raw j s c t.1 *
      memorySym (fun u => if u = t then (1 : ℂ) else 0) (pd4c_coreTarget F S s c t.1) =
        edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1 t.2.1 s.1 t.1 *
          ∏ i : Fin K, pd4c_coreGroupCoefficient F S ρ s t i (c i) := by
  rw [pd4c_memorySym_delta_factor]
  have hp : (pd4c_coreTarget F S s c t.1).1 = t.1 ∧
      (pd4c_coreTarget F S s c t.1).2.1 = t.2.1 := ⟨rfl, hq⟩
  rw [if_pos hp]
  unfold pd4c_coreCoefficient pd4c_coreGroupCoefficient pd4c_listDampedDelta pd4c_coreTarget
  rw [hq]
  simp only [pd4c_edgeNewMemory_component]
  push_cast
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/-- Fixing the target data leaves a geometric factor and independent choice conditions. -/
theorem pd4c_coreProjectedKernel_choice {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (w : ArchRoot) (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ)
    (s t : MemPoint S.x K) (hs : MemValid F S s) :
    pd4c_coreProjectedKernel F S ρ w raw St Pr j s t =
      ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
        if Pd4cPhysicalEdge F S w s.2.1 t.2.1 s.1 t.1 ∧ Pd4cTargetChoice F S s t St Pr c then
          edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1 t.2.1 s.1 t.1 *
            ∏ i : Fin K, pd4c_coreGroupCoefficient F S ρ s t i (c i) else 0 := by
  rw [pd4c_coreProjectedKernel_eval]
  apply Finset.sum_congr rfl
  intro c hc
  let A := edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c t.1
  let Q := edgeTargetLists F S s c = t.2.1
  have hequiv : A ∧ Q ↔ Pd4cPhysicalEdge F S w s.2.1 t.2.1 s.1 t.1 ∧ Pd4cTargetChoice F S s t St Pr c := by
    simpa only [A, Q, and_assoc] using pd4c_targetChoice_admissible_iff F S w s t hs St Pr c
  by_cases ha : A
  · rw [if_pos ha]
    by_cases hq : Q
    · rw [if_pos (hequiv.mp ⟨ha, hq⟩)]
      exact pd4c_coreCoefficient_factor F S ρ raw j s t c hq
    · have hn : ¬ (Pd4cPhysicalEdge F S w s.2.1 t.2.1 s.1 t.1 ∧ Pd4cTargetChoice F S s t St Pr c) :=
        fun h => hq (hequiv.mpr h).2
      rw [if_neg hn, pd4c_projected_delta_zero_active _ t hq, mul_zero]
  · rw [if_neg ha]
    have hn : ¬ (Pd4cPhysicalEdge F S w s.2.1 t.2.1 s.1 t.1 ∧ Pd4cTargetChoice F S s t St Pr c) :=
      fun h => ha (hequiv.mpr h).1
    exact (if_neg hn).symm

def pd4c_coreGroupKernel {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (s t : MemPoint S.x K) (St Pr : Finset (Fin K)) (i : Fin K) : ℂ :=
  pd4c_groupProjectedKernel (fun e : Particle => memoryNu S.x K F.a F.q_d i e.1)
    (bandMass S.x (F.a i)) (anchorAt (s.2.1 i (lastSlot S.x)) s.1)
    (anchorAt (t.2.1 i (lastSlot S.x)) t.1) (decide (i ∈ St)) (decide (i ∈ Pr))
    ρ s.1 t.1 (s.2.2 i) (t.2.2 i)

/-- The core projected edge kernel is the physical multiplier times its factorial group kernels. -/
theorem pd4c_coreProjectedKernel_formula {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (w : ArchRoot) (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ)
    (s t : MemPoint S.x K) (hs : MemValid F S s) (ht : MemValid F S t) :
    pd4c_coreProjectedKernel F S ρ w raw St Pr j s t =
      if Pd4cPhysicalEdge F S w s.2.1 t.2.1 s.1 t.1 then
        edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1 t.2.1 s.1 t.1 *
          ∏ i : Fin K, pd4c_coreGroupKernel F S ρ s t St Pr i else 0 := by
  let C (i : Fin K) (c : EdgeChoice S.x F.a (s.2.2 i) i) : Prop :=
    c.1 = decide (i ∈ St) ∧ c.2.isLeft = decide (i ∈ Pr) ∧
      edgeNewLabel c = t.2.1 i (lastSlot S.x) ∧
        (match c.2 with | Sum.inl k => particleHits ((s.2.2 i).get k) t.1 | Sum.inr _ => True)
  let g (i : Fin K) (c : EdgeChoice S.x F.a (s.2.2 i) i) := pd4c_coreGroupCoefficient F S ρ s t i c
  let b := edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1 t.2.1 s.1 t.1
  rw [pd4c_coreProjectedKernel_choice F S ρ w raw St Pr j s t hs]
  by_cases hp : Pd4cPhysicalEdge F S w s.2.1 t.2.1 s.1 t.1
  · rw [if_pos hp]
    have hterm (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :
        (if Pd4cPhysicalEdge F S w s.2.1 t.2.1 s.1 t.1 ∧ Pd4cTargetChoice F S s t St Pr c then
          b * ∏ i : Fin K, g i (c i) else 0) = b * ∏ i : Fin K, if C i (c i) then g i (c i) else 0 := by
      simp only [hp, true_and]
      by_cases hc : ∀ i, C i (c i)
      · have hh : Pd4cTargetChoice F S s t St Pr c := hc
        rw [if_pos hh]
        congr 1
        exact Finset.prod_congr rfl (fun i hi => (if_pos (hc i)).symm)
      · have hh : ¬ Pd4cTargetChoice F S s t St Pr c := hc
        rw [if_neg hh]
        push_neg at hc
        obtain ⟨i, hi⟩ := hc
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), mul_zero]
    change (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      if Pd4cPhysicalEdge F S w s.2.1 t.2.1 s.1 t.1 ∧ Pd4cTargetChoice F S s t St Pr c then
        b * ∏ i : Fin K, g i (c i) else 0) = b * ∏ i : Fin K, pd4c_coreGroupKernel F S ρ s t St Pr i
    simp only [hterm]
    rw [← Finset.mul_sum]
    have hprod := Fintype.prod_sum (fun (i : Fin K) (c : EdgeChoice S.x F.a (s.2.2 i) i) =>
      if C i c then g i c else 0)
    rw [← hprod]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    let q : primeBand S.x (F.a i) := ⟨t.2.1 i (lastSlot S.x), ht.2.1 i (lastSlot S.x)⟩
    have hsum : (∑ c : EdgeChoice S.x F.a (s.2.2 i) i, if C i c then g i c else 0) =
        ((ρ ^ hitCount (s.2.2 i) s.1 : ℝ) : ℂ) *
          ∑ c : EdgeChoice S.x F.a (s.2.2 i) i, if C i c then
            (pd4c_choicePrimeWeight F S s i c : ℂ) *
              pd4c_listDampedDelta ρ t.1 (t.2.2 i)
                (pd4c_groupNewMemory (s.2.2 i) (anchorAt (s.2.1 i (lastSlot S.x)) s.1) c) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases h : C i c
      · rw [if_pos h, if_pos h]
        dsimp [g, pd4c_coreGroupCoefficient]
        ring
      · rw [if_neg h, if_neg h, mul_zero]
    rw [hsum]
    dsimp only [C, pd4c_choicePrimeWeight, pd4c_coreGroupKernel]
    convert pd4c_groupKernel_choice F S i (s.2.2 i) (t.2.2 i)
      (anchorAt (s.2.1 i (lastSlot S.x)) s.1)
      ⟨t.2.1 i (lastSlot S.x), ht.2.1 i (lastSlot S.x)⟩
      s.1 t.1 ρ (decide (i ∈ St)) (decide (i ∈ Pr)) using 1
    · congr 1
      apply Finset.sum_congr rfl
      intro c hc
      split_ifs <;> simp_all only [Subtype.coe_mk, true_and, and_true, false_and, and_false, not_true_eq_false]
      all_goals
        rcases c with ⟨bc, ec⟩
        cases bc <;> cases ec
        all_goals simp_all only [Subtype.coe_mk, true_and, and_true, false_and, and_false,
          not_true_eq_false, pd4c_groupNewMemory] <;> rfl

  · simp only [hp, false_and, if_false, Finset.sum_const_zero]

end

end ArtinPrimitiveRoots.TypeII.PD
