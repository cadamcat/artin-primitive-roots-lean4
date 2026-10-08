import ArtinPrimitiveRoots.TypeII.Proofs.pcr_opus.Triangular
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».SignSupport

/-! Positive edge choice rows with prescribed births (guide
`runs/lanes/sol-thin-pd5/PROOFS.md:245–327`). The position sum is supplied as a hypothesis
(uniform in target lists and direction); the fresh/promotion choices are summed with the
triangular bound on `Fin K`, encoding promotion index `k` as `k` and fresh prime `p` as
`p + len`. Active averages are probability averages. -/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

theorem pcr_permCount_pos (x : ℝ) (K : ℕ) : 0 < (permCount x K : ℝ) := by
  unfold permCount
  exact_mod_cast Fintype.card_pos

/-- The active average of a function of the memory alone is that function. -/
theorem pcr_activeAverage_pow_memSize {K : ℕ} (S : PDScale) (v : ℝ) (t : MemPoint S.x K) :
    pd5_activeAverage S (fun t => v ^ memSize t) t = v ^ memSize t := by
  unfold pd5_activeAverage
  have h : ∀ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      v ^ memSize ((t.1, permuteLists σ t.2.1, t.2.2) : MemPoint S.x K) = v ^ memSize t :=
    fun σ => rfl
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hp := pcr_permCount_pos S.x K
  unfold permCount at hp ⊢
  field_simp

/-- An active average is a probability average. -/
theorem pcr_activeAverage_le {K : ℕ} (S : PDScale) (g : MemPoint S.x K → ℝ)
    (s : MemPoint S.x K) (X : ℝ)
    (h : ∀ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      g (s.1, permuteLists σ s.2.1, s.2.2) ≤ X) :
    pd5_activeAverage S g s ≤ X := by
  unfold pd5_activeAverage
  have hp := pcr_permCount_pos S.x K
  calc
    (permCount S.x K : ℝ)⁻¹ * ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        g (s.1, permuteLists σ s.2.1, s.2.2) ≤
        (permCount S.x K : ℝ)⁻¹ * ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), X :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => h σ) (inv_nonneg.mpr hp.le)
    _ = X := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold permCount at hp ⊢
      field_simp

theorem pcr_removeIndices_length_le (l : List Particle) (D : Finset (Fin l.length)) :
    (removeIndices l D).length ≤ l.length := by
  have h := pd5_removeIndices_length_balance l D
  omega

theorem pcr_edgeNewMemory_length_le {K : ℕ} (F : PDFix K) (S : PDScale) (r : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) (i : Fin K) :
    (edgeNewMemory F S r c i).length ≤ (r.2.2 i).length + (if (c i).1 then 1 else 0) := by
  unfold edgeNewMemory
  rw [List.length_append]
  apply add_le_add (pcr_removeIndices_length_le _ _)
  split_ifs <;> simp

theorem pcr_edge_pow_memSize_le {K : ℕ} (F : PDFix K) (S : PDScale) (r : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) (z' : ℤ × ℤ) (v : ℝ) (hv : 1 ≤ v) :
    v ^ memSize ((z', edgeTargetLists F S r c, edgeNewMemory F S r c) : MemPoint S.x K) ≤
      v ^ memSize r * ∏ i : Fin K, (if (c i).1 then v else 1) := by
  have hle : memSize ((z', edgeTargetLists F S r c, edgeNewMemory F S r c) : MemPoint S.x K) ≤
      memSize r + ∑ i : Fin K, (if (c i).1 then 1 else 0) := by
    unfold memSize
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => pcr_edgeNewMemory_length_le F S r c i
  calc
    _ ≤ v ^ (memSize r + ∑ i : Fin K, (if (c i).1 then 1 else 0)) := pow_le_pow_right₀ hv hle
    _ = v ^ memSize r * ∏ i : Fin K, (if (c i).1 then v else 1) := by
      rw [pow_add, ← Finset.prod_pow_eq_pow_sum]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      split_ifs <;> simp

/-- Encoded second component of an edge choice. -/
def pcr_edgeEnc {x : ℝ} {K : ℕ} {a : Fin K → ℝ} (l : List Particle) (i : Fin K) :
    (Fin l.length ⊕ primeBand x (a i)) → ℕ
  | Sum.inl k => k.val
  | Sum.inr p => (p : ℕ) + l.length

/-- Per-coordinate edge choice mass. -/
def pcr_edgeMass {K : ℕ} (F : PDFix K) (S : PDScale) (l : List Particle) (i : Fin K) :
    (Fin l.length ⊕ primeBand S.x (F.a i)) → ℝ
  | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
  | Sum.inr p => memoryNu S.x K F.a F.q_d i p

theorem pcr_edgeChoiceMass_eq {K : ℕ} (F : PDFix K) (S : PDScale) (r : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) (i : Fin K) :
    pd5_edgeChoiceMass F S r c i = pcr_edgeMass F S (r.2.2 i) i (c i).2 := by
  unfold pd5_edgeChoiceMass
  cases (c i).2 <;> rfl

theorem pcr_edgeMass_nonneg {K : ℕ} (F : PDFix K) (S : PDScale) (l : List Particle) (i : Fin K)
    (hV : 0 < bandMass S.x (F.a i))
    (hν : ∀ p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (y : Fin l.length ⊕ primeBand S.x (F.a i)) : 0 ≤ pcr_edgeMass F S l i y := by
  cases y with
  | inl k => exact inv_nonneg.mpr hV.le
  | inr p => exact hν p p.property

/-- Fresh edge births of strictly earlier groups, decoded from encoded values. -/
def pcr_edgeDecodeLog {K : ℕ} (j : ℕ) (len : Fin K → ℕ) (i : Fin K) (pre : Fin i.val → ℕ) :
    BirthLog K :=
  (List.finRange K).flatMap fun i' =>
    if h : i'.val < i.val then
      (if len i' ≤ pre ⟨i'.val, h⟩ then [(BirthAddress.edge j i', pre ⟨i'.val, h⟩ - len i')]
        else [])
    else []

theorem pcr_edge_birthIndex_lt {K : ℕ} (S : PDScale) (B j : ℕ) (i' i : Fin K) :
    pd5_birthIndex S B (BirthAddress.edge j i' : BirthAddress K) <
      pd5_birthIndex S B (BirthAddress.edge j i) ↔ i'.val < i.val := by
  simp only [pd5_birthIndex]
  have hT : 0 < max (slotCount S.x) B + 1 := Nat.succ_pos _
  constructor
  · intro h
    have h2 := lt_of_mul_lt_mul_right h (Nat.zero_le _)
    omega
  · intro h
    exact mul_lt_mul_of_pos_right (by omega) hT

theorem pcr_edgeBirths_filter_one {K : ℕ} (F : PDFix K) (S : PDScale) (B j : ℕ)
    (r : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) (i i' : Fin K) :
    (match (c i').2 with
      | Sum.inl _ => []
      | Sum.inr p => [(BirthAddress.edge j i', (p : ℕ))] : BirthLog K).filter
        (fun e => pd5_birthIndex S B e.1 < pd5_birthIndex S B (BirthAddress.edge j i)) =
      if h : i'.val < i.val then
        (if (r.2.2 i').length ≤ pcr_edgeEnc (r.2.2 i') i' (c i').2 then
          [(BirthAddress.edge j i', pcr_edgeEnc (r.2.2 i') i' (c i').2 - (r.2.2 i').length)]
          else [])
      else [] := by
  cases (c i').2 with
  | inl k =>
    have hk := k.isLt
    have hn : ¬ (r.2.2 i').length ≤ k.val := by omega
    by_cases h : i'.val < i.val <;> simp [pcr_edgeEnc, h, hn]
  | inr p =>
    have hidx := pcr_edge_birthIndex_lt (K := K) S B j i' i
    by_cases h : i'.val < i.val
    · have h' : pd5_birthIndex S B (BirthAddress.edge j i' : BirthAddress K) <
          pd5_birthIndex S B (BirthAddress.edge j i) := hidx.2 h
      simp [pcr_edgeEnc, h, h', List.filter_cons]
    · have h' : ¬ pd5_birthIndex S B (BirthAddress.edge j i' : BirthAddress K) <
          pd5_birthIndex S B (BirthAddress.edge j i) := fun hh => h (hidx.1 hh)
      simp [pcr_edgeEnc, h, h', List.filter_cons]

theorem pcr_edgeBirths_filter {K : ℕ} (F : PDFix K) (S : PDScale) (B j : ℕ)
    (r : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) (i : Fin K) :
    (edgeBirths F S j r c).filter
        (fun e => pd5_birthIndex S B e.1 < pd5_birthIndex S B (BirthAddress.edge j i)) =
      pcr_edgeDecodeLog j (fun i => (r.2.2 i).length) i
        (fun i' => pcr_edgeEnc (r.2.2 ⟨i'.val, lt_trans i'.isLt i.isLt⟩)
          ⟨i'.val, lt_trans i'.isLt i.isLt⟩ (c ⟨i'.val, lt_trans i'.isLt i.isLt⟩).2) := by
  unfold edgeBirths pcr_edgeDecodeLog
  rw [List.filter_flatMap]
  congr 1
  funext i'
  exact pcr_edgeBirths_filter_one F S B j r c i i'

theorem pcr_label_mem {K : ℕ} (log : BirthLog K) (a : BirthAddress K) (p : ℕ)
    (h : pd5b_label log a = some p) : (a, p) ∈ log := by
  unfold pd5b_label at h
  split_ifs at h with hex
  · exact (Option.some.inj h) ▸ Classical.choose_spec hex

theorem pcr_edgeBirths_mem {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ) (r : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) (i : Fin K) (p : ℕ)
    (h : (BirthAddress.edge j i, p) ∈ edgeBirths F S j r c) :
    pcr_edgeEnc (r.2.2 i) i (c i).2 = p + (r.2.2 i).length := by
  unfold edgeBirths at h
  obtain ⟨i', _, hi'⟩ := List.mem_flatMap.mp h
  revert hi'
  cases hc : (c i').2 with
  | inl k => simp
  | inr q =>
    intro hm
    have hm' : (BirthAddress.edge j i, p) = (BirthAddress.edge j i', (q : ℕ)) :=
      List.mem_singleton.mp hm
    obtain ⟨ha, hp⟩ := Prod.mk.inj hm'
    obtain ⟨-, hii⟩ := BirthAddress.edge.inj ha
    subst hii
    rw [hc, hp]
    rfl

/-- The local edge instruction as a function of the encoded values of earlier groups. -/
def pcr_edgePick {K : ℕ} (S : PDScale) (B j : ℕ) (len : Fin K → ℕ)
    (pick : BirthAddress K → BirthLog K → ℕ) (pastLog : BirthLog K)
    (i : Fin K) (pre : Fin i.val → ℕ) : ℕ :=
  pick (BirthAddress.edge j i)
    (pastLog.filter (fun e => pd5_birthIndex S B e.1 < pd5_birthIndex S B (BirthAddress.edge j i)) ++
      pcr_edgeDecodeLog j len i pre) + len i

theorem pcr_edge_weight_le_event {K : ℕ} (F : PDFix K) (S : PDScale) (B j : ℕ)
    (r : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i)
    (U R : Finset (BirthAddress K)) (hRU : R ⊆ U)
    (pick : BirthAddress K → BirthLog K → ℕ) (pastLog : BirthLog K) :
    pd5_prescribedWeight S B U R pick pastLog (edgeBirths F S j r c) ≤
      if ∀ i ∈ Finset.univ.filter (fun i => BirthAddress.edge j i ∈ R),
          pcr_edgeEnc (r.2.2 i) i (c i).2 =
            pcr_edgePick S B j (fun i => (r.2.2 i).length) pick pastLog i
              (fun i' => pcr_edgeEnc (r.2.2 ⟨i'.val, lt_trans i'.isLt i.isLt⟩)
                ⟨i'.val, lt_trans i'.isLt i.isLt⟩ (c ⟨i'.val, lt_trans i'.isLt i.isLt⟩).2)
      then 1 else 0 := by
  unfold pd5_prescribedWeight
  split_ifs with hW hE hE
  · exact le_rfl
  · exfalso
    apply hE
    intro i hi
    have hiR := (Finset.mem_filter.mp hi).2
    obtain ⟨p, hp, hforced⟩ := hW _ (hRU hiR)
    rw [pcr_edgeBirths_mem F S j r c i p (pcr_label_mem _ _ _ hp), hforced hiR]
    unfold pcr_edgePick
    rw [List.filter_append, pcr_edgeBirths_filter F S B j r c i]
  · norm_num
  · exact le_rfl

/-- A forced edge coordinate has fibre mass at most `(1+v)Δ`. -/
theorem pcr_edge_fibre_le {K : ℕ} (F : PDFix K) (S : PDScale) (l : List Particle) (i : Fin K)
    (v Δ : ℝ) (hv : 0 ≤ v) (hΔ : 0 ≤ Δ)
    (hatom : ∀ p, p ∈ primeBand S.x (F.a i) → memoryNu S.x K F.a F.q_d i p ≤ Δ) (q : ℕ) :
    (∑ x : EdgeChoice S.x F.a l i,
      if pcr_edgeEnc l i x.2 = q + l.length then
        pcr_edgeMass F S l i x.2 * (if x.1 then v else 1) else 0) ≤ (1 + v) * Δ := by
  have hy : (∑ y : Fin l.length ⊕ primeBand S.x (F.a i),
      if pcr_edgeEnc l i y = q + l.length then pcr_edgeMass F S l i y else 0) ≤ Δ := by
    rw [Fintype.sum_sum_type]
    have h1 : (∑ k : Fin l.length,
        if pcr_edgeEnc (x := S.x) (a := F.a) l i (Sum.inl k) = q + l.length then
          pcr_edgeMass F S l i (Sum.inl k) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hk := k.isLt
      have hne : pcr_edgeEnc (x := S.x) (a := F.a) l i (Sum.inl k) ≠ q + l.length := by
        simp only [pcr_edgeEnc]
        omega
      simp [hne]
    rw [h1, zero_add]
    have h2 : ∀ p : primeBand S.x (F.a i),
        (if pcr_edgeEnc (x := S.x) (a := F.a) l i (Sum.inr p) = q + l.length then
          pcr_edgeMass F S l i (Sum.inr p) else 0) =
          if (p : ℕ) = q then memoryNu S.x K F.a F.q_d i p else 0 := by
      intro p
      have hiff : pcr_edgeEnc (x := S.x) (a := F.a) l i (Sum.inr p) = q + l.length ↔
          (p : ℕ) = q := by
        simp only [pcr_edgeEnc]
        omega
      simp only [hiff, pcr_edgeMass]
    simp only [h2]
    exact pcr_coordinate_fibre (primeBand S.x (F.a i)) (memoryNu S.x K F.a F.q_d i) q Δ hΔ hatom
  have hsplit : ∀ b : Bool, (∑ y : Fin l.length ⊕ primeBand S.x (F.a i),
      if pcr_edgeEnc l i y = q + l.length then
        pcr_edgeMass F S l i y * (if b then v else 1) else 0) =
      (if b then v else 1) * ∑ y : Fin l.length ⊕ primeBand S.x (F.a i),
        (if pcr_edgeEnc l i y = q + l.length then pcr_edgeMass F S l i y else 0) := by
    intro b
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> ring
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  dsimp only
  rw [hsplit true, hsplit false]
  simp only [if_true, Bool.false_eq_true, if_false]
  nlinarith

/-- A free edge coordinate has mass at most `(1+v)(B·Vinv+2)`. -/
theorem pcr_edge_free_mass_le {K : ℕ} (F : PDFix K) (S : PDScale) (l : List Particle)
    (i : Fin K) (B : ℕ) (hl : l.length ≤ B) (v Vinv : ℝ) (hv : 0 ≤ v)
    (hV0 : 0 ≤ (bandMass S.x (F.a i))⁻¹) (hVinv : (bandMass S.x (F.a i))⁻¹ ≤ Vinv)
    (hmass : (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ≤ 2) :
    (∑ x : EdgeChoice S.x F.a l i, pcr_edgeMass F S l i x.2 * (if x.1 then v else 1)) ≤
      (1 + v) * ((B : ℝ) * Vinv + 2) := by
  have hy : (∑ y : Fin l.length ⊕ primeBand S.x (F.a i), pcr_edgeMass F S l i y) ≤
      (B : ℝ) * Vinv + 2 := by
    rw [Fintype.sum_sum_type]
    simp only [pcr_edgeMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_coe_sort (primeBand S.x (F.a i)) (memoryNu S.x K F.a F.q_d i)]
    have hlB : (l.length : ℝ) ≤ B := by exact_mod_cast hl
    have : (l.length : ℝ) * (bandMass S.x (F.a i))⁻¹ ≤ (B : ℝ) * Vinv :=
      mul_le_mul hlB hVinv hV0 (Nat.cast_nonneg _)
    linarith
  have hsplit : ∀ b : Bool, (∑ y : Fin l.length ⊕ primeBand S.x (F.a i),
      pcr_edgeMass F S l i y * (if b then v else 1)) =
      (if b then v else 1) * ∑ y : Fin l.length ⊕ primeBand S.x (F.a i), pcr_edgeMass F S l i y := by
    intro b
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  dsimp only
  rw [hsplit true, hsplit false]
  simp only [if_true, Bool.false_eq_true, if_false]
  nlinarith

/-- All prescribed edge choices of one edge, before the position sum. -/
theorem pcr_edge_choice_sum_le {K : ℕ} (F : PDFix K) (S : PDScale) (B j : ℕ)
    (r : MemPoint S.x K) (hr : ∀ i, (r.2.2 i).length ≤ B)
    (U R : Finset (BirthAddress K)) (hRU : R ⊆ U) (hU : U ⊆ pd5_edgeAddresses K j)
    (pick : BirthAddress K → BirthLog K → ℕ) (pastLog : BirthLog K)
    (v Δ Vinv : ℝ) (hv : 0 ≤ v) (hΔ : 0 ≤ Δ) (hVinv0 : 0 ≤ Vinv)
    (hV : ∀ i, 0 < bandMass S.x (F.a i)) (hVinv : ∀ i, (bandMass S.x (F.a i))⁻¹ ≤ Vinv)
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hmass : ∀ i, (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ≤ 2)
    (hatom : ∀ i p, p ∈ primeBand S.x (F.a i) → memoryNu S.x K F.a F.q_d i p ≤ Δ) :
    (∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i,
      (∏ i : Fin K, pd5_edgeChoiceMass F S r c i) *
        pd5_prescribedWeight S B U R pick pastLog (edgeBirths F S j r c) *
          ∏ i : Fin K, (if (c i).1 then v else 1)) ≤
      ((1 + v) * (Vinv + 2) * ((B : ℝ) + 1)) ^ K * Δ ^ R.card := by
  let R' : Finset (Fin K) := Finset.univ.filter fun i => BirthAddress.edge j i ∈ R
  let ν' : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i → ℝ := fun i x =>
    pcr_edgeMass F S (r.2.2 i) i x.2 * (if x.1 then v else 1)
  have hν' (i : Fin K) (x : EdgeChoice S.x F.a (r.2.2 i) i) : 0 ≤ ν' i x := by
    dsimp only [ν']
    apply mul_nonneg (pcr_edgeMass_nonneg F S _ i (hV i) (hν i) x.2)
    split_ifs <;> linarith
  let C' : ℝ := (1 + v) * (Vinv + 2) * ((B : ℝ) + 1)
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hC'1 : (1 + v) ≤ C' := by
    dsimp only [C']
    have : (1 : ℝ) ≤ (Vinv + 2) * ((B : ℝ) + 1) := by nlinarith
    nlinarith
  have hstep1 (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) :
      (∏ i : Fin K, pd5_edgeChoiceMass F S r c i) *
        pd5_prescribedWeight S B U R pick pastLog (edgeBirths F S j r c) *
          (∏ i : Fin K, (if (c i).1 then v else 1)) ≤
      if ∀ i ∈ R', pcr_edgeEnc (r.2.2 i) i (c i).2 =
            pcr_edgePick S B j (fun i => (r.2.2 i).length) pick pastLog i
              (fun i' => pcr_edgeEnc (r.2.2 ⟨i'.val, lt_trans i'.isLt i.isLt⟩)
                ⟨i'.val, lt_trans i'.isLt i.isLt⟩ (c ⟨i'.val, lt_trans i'.isLt i.isLt⟩).2)
      then ∏ i : Fin K, ν' i (c i) else 0 := by
    have hW := pcr_edge_weight_le_event F S B j r c U R hRU pick pastLog
    have hprod : (∏ i : Fin K, pd5_edgeChoiceMass F S r c i) *
        (∏ i : Fin K, (if (c i).1 then v else 1)) = ∏ i : Fin K, ν' i (c i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [pcr_edgeChoiceMass_eq]
    have hnn : 0 ≤ ∏ i : Fin K, ν' i (c i) := Finset.prod_nonneg fun i _ => hν' i (c i)
    calc
      _ = (∏ i : Fin K, ν' i (c i)) *
          pd5_prescribedWeight S B U R pick pastLog (edgeBirths F S j r c) := by
        rw [← hprod]; ring
      _ ≤ (∏ i : Fin K, ν' i (c i)) * (if ∀ i ∈ R', pcr_edgeEnc (r.2.2 i) i (c i).2 =
            pcr_edgePick S B j (fun i => (r.2.2 i).length) pick pastLog i
              (fun i' => pcr_edgeEnc (r.2.2 ⟨i'.val, lt_trans i'.isLt i.isLt⟩)
                ⟨i'.val, lt_trans i'.isLt i.isLt⟩ (c ⟨i'.val, lt_trans i'.isLt i.isLt⟩).2)
            then 1 else 0) := mul_le_mul_of_nonneg_left hW hnn
      _ = _ := by split_ifs <;> simp
  have htri := pcr_triangular_general K (fun i => EdgeChoice S.x F.a (r.2.2 i) i)
    (fun i x => pcr_edgeEnc (r.2.2 i) i x.2) ν' R' ((1 + v) * Δ)
    (mul_nonneg (by linarith) hΔ)
    (pcr_edgePick S B j (fun i => (r.2.2 i).length) pick pastLog) hν'
    (fun i hi pre => by
      have h := pcr_edge_fibre_le F S (r.2.2 i) i v Δ hv hΔ (hatom i)
        (pick (BirthAddress.edge j i)
          (pastLog.filter (fun e => pd5_birthIndex S B e.1 <
              pd5_birthIndex S B (BirthAddress.edge j i)) ++
            pcr_edgeDecodeLog j (fun i => (r.2.2 i).length) i pre))
      exact h)
  have hfree (i : Fin K) : (∑ x : EdgeChoice S.x F.a (r.2.2 i) i, ν' i x) ≤ C' := by
    have h := pcr_edge_free_mass_le F S (r.2.2 i) i B (hr i) v Vinv hv
      (inv_nonneg.mpr (hV i).le) (hVinv i) (hmass i)
    refine h.trans ?_
    dsimp only [C']
    have : (B : ℝ) * Vinv + 2 ≤ (Vinv + 2) * ((B : ℝ) + 1) := by nlinarith
    have h1v : 0 ≤ 1 + v := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this h1v]
  have hcard : R'.card = R.card := by
    have himage : R'.image (fun i => (BirthAddress.edge j i : BirthAddress K)) = R := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact (Finset.mem_filter.mp hi).2
      · intro ha
        have haE := hU (hRU ha)
        unfold pd5_edgeAddresses at haE
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp haE
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
    rw [← himage, Finset.card_image_of_injective]
    intro a b hab
    exact (BirthAddress.edge.inj hab).2
  calc
    _ ≤ ∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i,
        (if ∀ i ∈ R', pcr_edgeEnc (r.2.2 i) i (c i).2 =
            pcr_edgePick S B j (fun i => (r.2.2 i).length) pick pastLog i
              (fun i' => pcr_edgeEnc (r.2.2 ⟨i'.val, lt_trans i'.isLt i.isLt⟩)
                ⟨i'.val, lt_trans i'.isLt i.isLt⟩ (c ⟨i'.val, lt_trans i'.isLt i.isLt⟩).2)
          then ∏ i : Fin K, ν' i (c i) else 0) := Finset.sum_le_sum fun c _ => hstep1 c
    _ ≤ ∏ i : Fin K, if i ∈ R' then (1 + v) * Δ else
          ∑ x : EdgeChoice S.x F.a (r.2.2 i) i, ν' i x := htri
    _ ≤ ∏ i : Fin K, if i ∈ R' then C' * Δ else C' := by
      apply Finset.prod_le_prod₀
      · intro i _
        split_ifs
        · exact mul_nonneg (by linarith) hΔ
        · exact Finset.sum_nonneg fun x _ => hν' i x
      · intro i _
        split_ifs
        · exact mul_le_mul_of_nonneg_right hC'1 hΔ
        · exact hfree i
    _ = C' ^ K * Δ ^ R'.card := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const]
      have hyes : (Finset.univ.filter fun i : Fin K => i ∈ R') = R' := by ext a; simp
      have hno : (Finset.univ.filter fun i : Fin K => i ∉ R') = Finset.univ \ R' := by
        ext a; simp
      rw [hyes, hno, mul_pow, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin]
      have hle : R'.card ≤ K := by
        simpa using Finset.card_le_univ R'
      rw [mul_comm (C' ^ R'.card), mul_assoc, ← pow_add, Nat.add_sub_of_le hle]
      ring
    _ = _ := by rw [hcard]

/-- One `(choice, position)` term of `pd5_edgeAbsChoice`. -/
def pcr_edgeTerm {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j B : ℕ) (W : BirthLog K → ℝ) (f : MemPoint S.x K → ℝ) (r : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) (z' : ℤ × ℤ) : ℝ :=
  let t : MemPoint S.x K := (z', edgeTargetLists F S r c, edgeNewMemory F S r c)
  if EdgeAdmissible F S w r c z' ∧ memSize t ≤ B then
    |ρ ^ (∑ i : Fin K, hitCount (r.2.2 i) r.1) *
      (∏ i : Fin K, pd5_edgeChoiceMass F S r c i) *
        ρ ^ (∑ i : Fin K, hitCount (t.2.2 i) z')| *
      (‖edgeMultiplier F S (decide (j % 2 = 0)) true r.2.1 t.2.1 r.1 z'‖ +
        ‖edgeMultiplier F S (decide (j % 2 = 0)) false r.2.1 t.2.1 r.1 z'‖) *
      W (edgeBirths F S j r c) * pd5_activeAverage S f t
  else 0

/-- The per-active-permutation part of `pd5_edgeAbsChoice`. -/
def pcr_edgeInner {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j B : ℕ) (Z : Finset (ℤ × ℤ)) (W : BirthLog K → ℝ)
    (f : MemPoint S.x K → ℝ) (r : MemPoint S.x K) : ℝ :=
  ∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i,
    ∑ z' ∈ Z, pcr_edgeTerm F S ρ w j B W f r c z'

theorem pcr_edgeAbsChoice_eq {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j B : ℕ) (Z : Finset (ℤ × ℤ)) (W : BirthLog K → ℝ)
    (f : MemPoint S.x K → ℝ) (s : MemPoint S.x K) :
    pd5_edgeAbsChoice F S ρ w j B Z W f s =
      if memSize s ≤ B then pd5_activeAverage S (pcr_edgeInner F S ρ w j B Z W f) s else 0 :=
  rfl

/-- Pointwise domination of one term by the absolute choice weight and the position kernel. -/
theorem pcr_edge_term_le {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j B : ℕ) (W : BirthLog K → ℝ) (v : ℝ) (r : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) (z' : ℤ × ℤ)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hv : 1 ≤ v) (hW : 0 ≤ W (edgeBirths F S j r c))
    (hmass0 : 0 ≤ ∏ i : Fin K, pd5_edgeChoiceMass F S r c i) :
    pcr_edgeTerm F S ρ w j B W (fun t => v ^ memSize t) r c z' ≤
      ((∏ i : Fin K, pd5_edgeChoiceMass F S r c i) * W (edgeBirths F S j r c) *
          ∏ i : Fin K, (if (c i).1 then v else 1)) * v ^ memSize r *
        (if S.d₀ ≤ sharedProduct r.2.1 ∧ envBox S w r.1 ∧ envBox S w z' ∧
            (sharedProduct r.2.1 : ℤ) ∣ det2 r.1 z' then
          ‖edgeMultiplier F S (decide (j % 2 = 0)) true r.2.1 (edgeTargetLists F S r c) r.1 z'‖ +
            ‖edgeMultiplier F S (decide (j % 2 = 0)) false r.2.1 (edgeTargetLists F S r c) r.1 z'‖
         else 0) := by
  have hstore0 : 0 ≤ ∏ i : Fin K, (if (c i).1 then v else 1) :=
    Finset.prod_nonneg fun i _ => by split_ifs <;> linarith
  have hvpow : 0 ≤ v ^ memSize r := pow_nonneg (by linarith) _
  have hN0 : 0 ≤ ‖edgeMultiplier F S (decide (j % 2 = 0)) true r.2.1
      (edgeTargetLists F S r c) r.1 z'‖ +
      ‖edgeMultiplier F S (decide (j % 2 = 0)) false r.2.1 (edgeTargetLists F S r c) r.1 z'‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  unfold pcr_edgeTerm
  dsimp only
  split_ifs with hA hI
  · -- admissible term
    rw [pcr_activeAverage_pow_memSize]
    have hρabs (n : ℕ) : |ρ ^ n| ≤ 1 := by
      rw [abs_pow, abs_of_pos hρ0]
      exact pow_le_one₀ hρ0.le hρ1
    have habs : |ρ ^ (∑ i : Fin K, hitCount (r.2.2 i) r.1) *
        (∏ i : Fin K, pd5_edgeChoiceMass F S r c i) *
          ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S r c i) z')| ≤
        ∏ i : Fin K, pd5_edgeChoiceMass F S r c i := by
      rw [abs_mul, abs_mul, abs_of_nonneg hmass0]
      have h1 := hρabs (∑ i : Fin K, hitCount (r.2.2 i) r.1)
      have h2 := hρabs (∑ i : Fin K, hitCount (edgeNewMemory F S r c i) z')
      have h1' : 0 ≤ |ρ ^ (∑ i : Fin K, hitCount (r.2.2 i) r.1)| := abs_nonneg _
      have h2' : 0 ≤ |ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S r c i) z')| := abs_nonneg _
      calc
        _ ≤ 1 * (∏ i : Fin K, pd5_edgeChoiceMass F S r c i) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hmass0) h2 h2'
          positivity
        _ = _ := by ring
    have hpow := pcr_edge_pow_memSize_le F S r c z' v hv
    have habs0 : 0 ≤ |ρ ^ (∑ i : Fin K, hitCount (r.2.2 i) r.1) *
        (∏ i : Fin K, pd5_edgeChoiceMass F S r c i) *
          ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S r c i) z')| := abs_nonneg _
    have hvt0 : 0 ≤ v ^ memSize ((z', edgeTargetLists F S r c, edgeNewMemory F S r c) :
        MemPoint S.x K) := pow_nonneg (by linarith) _
    calc
      _ ≤ (∏ i : Fin K, pd5_edgeChoiceMass F S r c i) *
          (‖edgeMultiplier F S (decide (j % 2 = 0)) true r.2.1 (edgeTargetLists F S r c) r.1 z'‖ +
            ‖edgeMultiplier F S (decide (j % 2 = 0)) false r.2.1
              (edgeTargetLists F S r c) r.1 z'‖) *
          W (edgeBirths F S j r c) *
          (v ^ memSize r * ∏ i : Fin K, (if (c i).1 then v else 1)) := by
        apply mul_le_mul _ hpow hvt0
        · exact mul_nonneg (mul_nonneg hmass0 hN0) hW
        · apply mul_le_mul_of_nonneg_right _ hW
          exact mul_le_mul_of_nonneg_right habs hN0
      _ = _ := by ring
  · -- admissible but the indicator fails: impossible
    exfalso
    apply hI
    obtain ⟨-, -, -, -, ⟨hd0, -, hdvd⟩, -, hbox, hbox', -, -⟩ := hA.1
    exact ⟨by exact_mod_cast hd0, hbox, hbox', hdvd⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hmass0 hW) hstore0) hvpow) hN0
  · rw [mul_zero]

/-- The inner edge row at one active permutation. -/
theorem pcr_edgeInner_le {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j B : ℕ) (Z : Finset (ℤ × ℤ)) (r : MemPoint S.x K)
    (U R : Finset (BirthAddress K)) (hRU : R ⊆ U) (hU : U ⊆ pd5_edgeAddresses K j)
    (pick : BirthAddress K → BirthLog K → ℕ) (pastLog : BirthLog K)
    (v Δ Vinv G : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hv : 1 ≤ v) (hΔ : 0 ≤ Δ)
    (hVinv0 : 0 ≤ Vinv) (hG : 0 ≤ G) (hr : memSize r ≤ B)
    (hV : ∀ i, 0 < bandMass S.x (F.a i)) (hVinv : ∀ i, (bandMass S.x (F.a i))⁻¹ ≤ Vinv)
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hmass : ∀ i, (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ≤ 2)
    (hatom : ∀ i p, p ∈ primeBand S.x (F.a i) → memoryNu S.x K F.a F.q_d i p ≤ Δ)
    (hgeom : S.d₀ ≤ sharedProduct r.2.1 → envBox S w r.1 →
      ∀ (q : PrimeLists S.x K) (forward : Bool),
        (∑ z' ∈ Z, if envBox S w z' ∧ (sharedProduct r.2.1 : ℤ) ∣ det2 r.1 z' then
          ‖edgeMultiplier F S forward true r.2.1 q r.1 z'‖ +
            ‖edgeMultiplier F S forward false r.2.1 q r.1 z'‖ else 0) ≤ G) :
    pcr_edgeInner F S ρ w j B Z (pd5_prescribedWeight S B U R pick pastLog)
        (fun t => v ^ memSize t) r ≤
      G * (((1 + v) * (Vinv + 2) * ((B : ℝ) + 1)) ^ K * Δ ^ R.card) * v ^ memSize r := by
  let W := pd5_prescribedWeight S B U R pick pastLog
  have hW (log : BirthLog K) : 0 ≤ W log := by
    dsimp only [W]
    unfold pd5_prescribedWeight
    split_ifs <;> norm_num
  have hlen (i : Fin K) : (r.2.2 i).length ≤ B := by
    have h : (r.2.2 i).length ≤ memSize r := by
      unfold memSize
      exact Finset.single_le_sum (f := fun i => (r.2.2 i).length) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  let a (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) : ℝ :=
    (∏ i : Fin K, pd5_edgeChoiceMass F S r c i) * W (edgeBirths F S j r c) *
      ∏ i : Fin K, (if (c i).1 then v else 1)
  have hmass0 (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) :
      0 ≤ ∏ i : Fin K, pd5_edgeChoiceMass F S r c i := by
    apply Finset.prod_nonneg
    intro i _
    rw [pcr_edgeChoiceMass_eq]
    exact pcr_edgeMass_nonneg F S _ i (hV i) (hν i) _
  have ha0 (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) : 0 ≤ a c := by
    dsimp only [a]
    apply mul_nonneg (mul_nonneg (hmass0 c) (hW _))
    exact Finset.prod_nonneg fun i _ => by split_ifs <;> linarith
  have hvpow : 0 ≤ v ^ memSize r := pow_nonneg (by linarith) _
  have hInd (c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i) :
      (∑ z' ∈ Z, if S.d₀ ≤ sharedProduct r.2.1 ∧ envBox S w r.1 ∧ envBox S w z' ∧
            (sharedProduct r.2.1 : ℤ) ∣ det2 r.1 z' then
          ‖edgeMultiplier F S (decide (j % 2 = 0)) true r.2.1 (edgeTargetLists F S r c) r.1 z'‖ +
            ‖edgeMultiplier F S (decide (j % 2 = 0)) false r.2.1 (edgeTargetLists F S r c) r.1 z'‖
         else 0) ≤ G := by
    by_cases h : S.d₀ ≤ sharedProduct r.2.1 ∧ envBox S w r.1
    · refine le_trans (le_of_eq ?_) (hgeom h.1 h.2 (edgeTargetLists F S r c) (decide (j % 2 = 0)))
      apply Finset.sum_congr rfl
      intro z' _
      simp only [h.1, h.2, true_and]
    · have hz : ∀ z' ∈ Z, (if S.d₀ ≤ sharedProduct r.2.1 ∧ envBox S w r.1 ∧ envBox S w z' ∧
            (sharedProduct r.2.1 : ℤ) ∣ det2 r.1 z' then
          ‖edgeMultiplier F S (decide (j % 2 = 0)) true r.2.1 (edgeTargetLists F S r c) r.1 z'‖ +
            ‖edgeMultiplier F S (decide (j % 2 = 0)) false r.2.1 (edgeTargetLists F S r c) r.1 z'‖
         else 0) = 0 := by
        intro z' _
        rw [if_neg]
        intro hh
        exact h ⟨hh.1, hh.2.1⟩
      rw [Finset.sum_eq_zero hz]
      exact hG
  have hsum := pcr_edge_choice_sum_le F S B j r hlen U R hRU hU pick pastLog v Δ Vinv
    (by linarith) hΔ hVinv0 hV hVinv hν hmass hatom
  unfold pcr_edgeInner
  calc
    _ ≤ ∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i, a c * v ^ memSize r * G := by
      apply Finset.sum_le_sum
      intro c _
      calc
        _ ≤ ∑ z' ∈ Z, a c * v ^ memSize r *
            (if S.d₀ ≤ sharedProduct r.2.1 ∧ envBox S w r.1 ∧ envBox S w z' ∧
                (sharedProduct r.2.1 : ℤ) ∣ det2 r.1 z' then
              ‖edgeMultiplier F S (decide (j % 2 = 0)) true r.2.1
                (edgeTargetLists F S r c) r.1 z'‖ +
                ‖edgeMultiplier F S (decide (j % 2 = 0)) false r.2.1
                  (edgeTargetLists F S r c) r.1 z'‖
             else 0) := by
          apply Finset.sum_le_sum
          intro z' _
          exact pcr_edge_term_le F S ρ w j B W v r c z' hρ0 hρ1 hv (hW _) (hmass0 c)
        _ = a c * v ^ memSize r * ∑ z' ∈ Z,
            (if S.d₀ ≤ sharedProduct r.2.1 ∧ envBox S w r.1 ∧ envBox S w z' ∧
                (sharedProduct r.2.1 : ℤ) ∣ det2 r.1 z' then
              ‖edgeMultiplier F S (decide (j % 2 = 0)) true r.2.1
                (edgeTargetLists F S r c) r.1 z'‖ +
                ‖edgeMultiplier F S (decide (j % 2 = 0)) false r.2.1
                  (edgeTargetLists F S r c) r.1 z'‖
             else 0) := by rw [Finset.mul_sum]
        _ ≤ a c * v ^ memSize r * G :=
          mul_le_mul_of_nonneg_left (hInd c) (mul_nonneg (ha0 c) hvpow)
    _ = (∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i, a c) * (v ^ memSize r * G) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ (((1 + v) * (Vinv + 2) * ((B : ℝ) + 1)) ^ K * Δ ^ R.card) * (v ^ memSize r * G) :=
      mul_le_mul_of_nonneg_right hsum (mul_nonneg hvpow hG)
    _ = _ := by ring

/-- The prescribed positive edge row. `G` is the supplied uniform position bound. -/
theorem pcr_edge_prescribed_row {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j B : ℕ) (Z : Finset (ℤ × ℤ)) (s : MemPoint S.x K) (hs : memSize s ≤ B)
    (U R : Finset (BirthAddress K)) (hRU : R ⊆ U) (hU : U ⊆ pd5_edgeAddresses K j)
    (pick : BirthAddress K → BirthLog K → ℕ) (pastLog : BirthLog K)
    (v Δ Vinv G : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hv : 1 ≤ v) (hΔ : 0 ≤ Δ)
    (hVinv0 : 0 ≤ Vinv) (hG : 0 ≤ G)
    (hV : ∀ i, 0 < bandMass S.x (F.a i)) (hVinv : ∀ i, (bandMass S.x (F.a i))⁻¹ ≤ Vinv)
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hmass : ∀ i, (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ≤ 2)
    (hatom : ∀ i p, p ∈ primeBand S.x (F.a i) → memoryNu S.x K F.a F.q_d i p ≤ Δ)
    (hgeom : ∀ p q : PrimeLists S.x K, S.d₀ ≤ sharedProduct p → envBox S w s.1 →
      ∀ forward : Bool,
        (∑ z' ∈ Z, if envBox S w z' ∧ (sharedProduct p : ℤ) ∣ det2 s.1 z' then
          ‖edgeMultiplier F S forward true p q s.1 z'‖ +
            ‖edgeMultiplier F S forward false p q s.1 z'‖ else 0) ≤ G) :
    pd5_edgeAbsChoice F S ρ w j B Z (pd5_prescribedWeight S B U R pick pastLog)
        (fun t => v ^ memSize t) s ≤
      G * (((1 + v) * (Vinv + 2) * ((B : ℝ) + 1)) ^ K * Δ ^ R.card) * v ^ memSize s := by
  rw [pcr_edgeAbsChoice_eq, if_pos hs]
  apply pcr_activeAverage_le
  intro σ
  exact pcr_edgeInner_le F S ρ w j B Z (s.1, permuteLists σ s.2.1, s.2.2) U R hRU hU pick pastLog
    v Δ Vinv G hρ0 hρ1 hv hΔ hVinv0 hG hs hV hVinv hν hmass hatom
    (fun hd hb q forward => hgeom (permuteLists σ s.2.1) q hd hb forward)

end
end ArtinPrimitiveRoots.TypeII.PD
