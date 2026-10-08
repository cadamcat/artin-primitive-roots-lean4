import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».pd5_boundary_norm_near_one
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».pd5_phase_at_births
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».pd5_modified_ops_symmetry_domination
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_rank_support_mass

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

private theorem pd5_iteration_memSize_memoryPermute {x : ℝ} {K : ℕ}
    (s : MemPoint x K) (σ : MemoryPermutation s) :
    memSize (memoryPermute s σ) = memSize s := by
  simp [memSize, memoryPermute]

private theorem pd5_memValid_memoryPermute_iff {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (σ : MemoryPermutation s) :
    MemValid F S (memoryPermute s σ) ↔ MemValid F S s := by
  constructor
  · intro h
    refine ⟨h.1, ?_, ?_⟩
    · intro i j
      exact h.2.1 i j
    · intro i e he
      have hp := listPermute_perm (s.2.2 i) (σ i)
      exact h.2.2 i e ((hp.mem_iff).mpr he)
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro i e he
    have hp := listPermute_perm (s.2.2 i) (σ i)
    exact h.2.2 i e ((hp.mem_iff).mp he)

private theorem pd5_stateRegion_memoryPermute_iff {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (B : ℕ)
    (s : MemPoint S.x K) (σ : MemoryPermutation s) :
    pd5_stateRegion F S w B (memoryPermute s σ) ↔ pd5_stateRegion F S w B s := by
  unfold pd5_stateRegion
  rw [pd5_memValid_memoryPermute_iff]
  simp only [pd5_iteration_memSize_memoryPermute]
  rfl

private def pd5_restrictTo {α : Type*} (T : Finset α) (f : α → ℂ) : α → ℂ :=
  fun s => if s ∈ T then f s else 0

private theorem pd5_restrictTo_idempotent {α : Type*} (T : Finset α)
    (f : α → ℂ) : pd5_restrictTo T (pd5_restrictTo T f) = pd5_restrictTo T f := by
  funext s
  by_cases hs : s ∈ T <;> simp [pd5_restrictTo, hs]

private theorem pd5_restrictTo_memSymmetric {K : ℕ} (S : PDScale)
    (T : Finset (MemPoint S.x K))
    (hT : ∀ s σ, memoryPermute s σ ∈ T ↔ s ∈ T)
    (f : MemPoint S.x K → ℂ) (hf : IsMemorySymmetric f) :
    IsMemorySymmetric (pd5_restrictTo T f) := by
  intro s σ
  by_cases hs : s ∈ T
  · have hp : memoryPermute s σ ∈ T := (hT s σ).2 hs
    simp [pd5_restrictTo, hs, hp, hf s σ]
  · have hp : memoryPermute s σ ∉ T := by
      intro hp
      exact hs ((hT s σ).1 hp)
    simp [pd5_restrictTo, hs, hp]

private theorem pd5_memorySym_eq_self_of_symmetric {x : ℝ} {K : ℕ}
    (f : MemPoint x K → ℂ) (hf : IsMemorySymmetric f) : memorySym f = f := by
  funext s
  classical
  have hsum :
      (∑ σ : MemoryPermutation s, f (memoryPermute s σ)) =
        (Fintype.card (MemoryPermutation s) : ℂ) * f s := by
    calc
      _ = ∑ _σ : MemoryPermutation s, f s := by
        apply Finset.sum_congr rfl
        intro σ hσ
        exact hf s σ
      _ = _ := by simp
  unfold memorySym
  rw [hsum]
  have hcard : (Fintype.card (MemoryPermutation s) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (MemoryPermutation s) ≠ 0)
  field_simp [hcard]

private theorem pd5_restrictTo_memNormSq_eq {K : ℕ} (F : PDFix K) (S : PDScale)
    (T : Finset (MemPoint S.x K)) (f : MemPoint S.x K → ℂ) :
    memNormSqOn F S T (pd5_restrictTo T f) = memNormSqOn F S T f := by
  unfold memNormSqOn
  apply Finset.sum_congr rfl
  intro s hs
  simp [pd5_restrictTo, hs]

private theorem pd5_plainTrunc_restrict_eq {x : ℝ} {K : ℕ} (B : ℕ)
    (T : Finset (MemPoint x K)) (hT : ∀ s ∈ T, memSize s ≤ B)
    (f : MemPoint x K → ℂ) :
    pd5_plainTrunc B (pd5_restrictTo T f) = pd5_restrictTo T f := by
  funext s
  by_cases hs : s ∈ T
  · simp [pd5_plainTrunc, pd5_restrictTo, hs, hT s hs]
  · simp [pd5_plainTrunc, pd5_restrictTo, hs]

private theorem pd5_memOpNormLE_sym_restrict {K : ℕ} (F : PDFix K) (S : PDScale)
    (B : ℕ) (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (c : ℝ)
    (T : Finset (MemPoint S.x K)) (hT : ∀ s ∈ T, memSize s ≤ B)
    (hOp : MemOpNormLE_sym F S B op c)
    (f : MemPoint S.x K → ℂ) (hf : IsMemorySymmetric f)
    (hTmem : ∀ s σ, memoryPermute s σ ∈ T ↔ s ∈ T) :
    memNormSqOn F S T (pd5_restrictTo T (op (pd5_restrictTo T f))) ≤
      c ^ 2 * memNormSqOn F S T f := by
  let fT := pd5_restrictTo T f
  have hfT : IsMemorySymmetric fT := pd5_restrictTo_memSymmetric S T hTmem f hf
  have hms : memorySym fT = fT := pd5_memorySym_eq_self_of_symmetric fT hfT
  have hsupp : ∀ s, s ∉ T → fT s = 0 := by
    intro s hs
    simp [fT, pd5_restrictTo, hs]
  have h := hOp T T fT hsupp hT hT
  change memNormSqOn F S T (op (memorySym fT)) ≤
    c ^ 2 * memNormSqOn F S T fT at h
  calc
    _ = memNormSqOn F S T (op fT) :=
      pd5_restrictTo_memNormSq_eq F S T (op fT)
    _ ≤ c ^ 2 * memNormSqOn F S T fT := by simpa [hms] using h
    _ = c ^ 2 * memNormSqOn F S T f := by
      rw [pd5_restrictTo_memNormSq_eq]

private theorem pd5_memBoundary_symmetric {x : ℝ} {K : ℕ} :
    IsMemorySymmetric (@memBoundary x K) := by
  intro s σ
  have hlen (i : Fin K) :
      ((memoryPermute s σ).2.2 i).length = (s.2.2 i).length := by
    simp [memoryPermute]
  have hempty :
      (∀ i, (memoryPermute s σ).2.2 i = []) ↔ ∀ i, s.2.2 i = [] := by
    constructor
    · intro h i
      have hz : (s.2.2 i).length = 0 := by
        rw [← hlen i, h i]
        rfl
      exact List.eq_nil_of_length_eq_zero hz
    · intro h i
      simp [memoryPermute, h i]
  simp [memBoundary, memoryPermute, hempty]

private theorem pd5_finset_norm_prod_le_one {α : Type*} (A : Finset α)
    (f : α → ℂ) (hf : ∀ a ∈ A, ‖f a‖ ≤ 1) : ‖∏ a ∈ A, f a‖ ≤ 1 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    rw [Finset.prod_insert ha, norm_mul]
    have hhead := hf a (Finset.mem_insert_self a A)
    have htail := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    have hnonnegHead := norm_nonneg (f a)
    have hnonnegTail := norm_nonneg (∏ b ∈ A, f b)
    calc
      ‖f a‖ * ‖∏ b ∈ A, f b‖ ≤ 1 * ‖∏ b ∈ A, f b‖ :=
        mul_le_mul_of_nonneg_right hhead hnonnegTail
      _ ≤ 1 := by nlinarith [htail, hnonnegTail]

private theorem pd5_operationPhase_norm_le_one {K : ℕ}
    (U Ops : Finset (BirthAddress K)) (φ : BirthAddress K → ℕ → ℂ)
    (hφ : ∀ a p, ‖φ a p‖ ≤ 1) (log : BirthLog K) :
    ‖pd5_operationPhase U Ops φ log‖ ≤ 1 := by
  classical
  unfold pd5_operationPhase pd5_birthPhaseWeight
  apply pd5_finset_norm_prod_le_one
  intro a ha
  unfold pd5_addressPhase
  cases hlabel : pd5b_label log a with
  | none => simp
  | some p => simpa using hφ a p

private theorem pd5_stdAddChar_norm {T : ℕ} [NeZero T] (z : ZMod T) :
    ‖ZMod.stdAddChar z‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact (ZMod.toCircle z).norm_coe

private theorem pd5_finite_inner_sq_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (T : Finset (MemPoint S.x K)) (g f : MemPoint S.x K → ℂ)
    (hμ : ∀ s ∈ T, 0 ≤ memMeasure F S s) :
    ‖∑ s ∈ T, (memMeasure F S s : ℂ) * star (g s) * f s‖ ^ 2 ≤
      memNormSqOn F S T g * memNormSqOn F S T f := by
  classical
  let r (s : MemPoint S.x K) : ℝ :=
    memMeasure F S s * ‖g s‖ * ‖f s‖
  let a (s : MemPoint S.x K) : ℝ := memMeasure F S s * ‖g s‖ ^ 2
  let b (s : MemPoint S.x K) : ℝ := memMeasure F S s * ‖f s‖ ^ 2
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := T)
    (r := r) (f := a) (g := b)
    (by intro s hs; exact mul_nonneg (hμ s hs) (sq_nonneg (‖g s‖)))
    (by intro s hs; exact mul_nonneg (hμ s hs) (sq_nonneg (‖f s‖)))
    (by intro s hs; dsimp [r, a, b]; ring_nf; rfl)
  have htri :
      ‖∑ s ∈ T, (memMeasure F S s : ℂ) * star (g s) * f s‖ ≤
        ∑ s ∈ T, r s := by
    calc
      _ ≤ ∑ s ∈ T,
            ‖(memMeasure F S s : ℂ) * star (g s) * f s‖ := norm_sum_le _ _
      _ = ∑ s ∈ T, r s := by
            apply Finset.sum_congr rfl
            intro s hs
            simp [r, norm_mul, Complex.norm_real, abs_of_nonneg (hμ s hs)]
  have hr : 0 ≤ ∑ s ∈ T, r s :=
    Finset.sum_nonneg fun s hs => mul_nonneg (mul_nonneg (hμ s hs) (norm_nonneg _))
      (norm_nonneg _)
  have hsq :
      ‖∑ s ∈ T, (memMeasure F S s : ℂ) * star (g s) * f s‖ ^ 2 ≤
        (∑ s ∈ T, r s) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr htri)
      (add_nonneg (norm_nonneg (∑ s ∈ T,
        (memMeasure F S s : ℂ) * star (g s) * f s)) hr)
    nlinarith [hprod]
  calc
    _ ≤ (∑ s ∈ T, r s) ^ 2 := hsq
    _ ≤ (∑ s ∈ T, a s) * ∑ s ∈ T, b s := hCS
    _ = memNormSqOn F S T g * memNormSqOn F S T f := by
      simp [a, b, memNormSqOn]

private def PD5IterationChronologicalExpansion {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : ℕ) (T : Finset (MemPoint S.x K)) : Prop :=
  ∀ W : BirthLog K → ℂ, ∀ f : MemPoint S.x K → ℂ, ∀ s ∈ T,
    (∀ j : ℕ, j ≤ S.N →
      pd5_ghostBirthTwist F S ρ j W (pd5_plainTrunc B f) s =
        ∑ t ∈ T, memKernel (fun g => pd5_ghostBirthTwist F S ρ j W
          (pd5_plainTrunc B g)) s t * f t) ∧
    (∀ j : ℕ, j < S.N →
      pd5_edgeBirthTwist F S ρ w j W (pd5_plainTrunc B f) s =
        ∑ t ∈ T, memKernel (fun g => pd5_edgeBirthTwist F S ρ w j W
          (pd5_plainTrunc B g)) s t * f t)

set_option maxHeartbeats 8000000 in
private theorem pd5_phaseHistoryFn_norm_sq_bound {K : ℕ}
    (δ c₁ c₂ : ℝ) (F : PDFix K) (S : PDScale) (hS : S.Valid K δ c₁ c₂)
    (ρ : ℝ) (w : ArchRoot) (hw : w.InRegion S)
    (C_K Ccr x₀ : ℝ) (hC_K : 0 < C_K) (hx₀ : x₀ ≤ S.x)
    (hMod : PD5ModifiedBounds δ c₁ c₂ F ρ C_K Ccr x₀)
    (G : ℝ) (hEdge : ∀ j : ℕ, j < S.N →
      MemOpNormLE_sym F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
        (Real.rpow S.L (-G)))
    (U : Finset (BirthAddress K)) (φ : BirthAddress K → ℕ → ℂ)
    (hφ : ∀ a p, ‖φ a p‖ ≤ 1)
    (T : Finset (MemPoint S.x K))
    (hTstate : ∀ s, s ∈ T ↔ pd5_stateRegion F S w (memoryCutoff S) s)
    (hTmem : ∀ s σ, memoryPermute s σ ∈ T ↔ s ∈ T)
    (hModel : PD5IterationChronologicalExpansion F S ρ w (memoryCutoff S) T)
    (hBoundary : memNormSqOn F S T memBoundary ≤ 2) :
    memNormSqOn F S T
        (pd5_restrictTo T (pd5_phaseHistoryFn F S ρ w (memoryCutoff S) U φ S.N)) ≤
      2 * C_K ^ (2 * (S.N + 1)) *
        (∏ k ∈ Finset.range S.N,
          if ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U then
            Real.rpow S.L Ccr else Real.rpow S.L (-G)) ^ 2 := by
  classical
  let B := memoryCutoff S
  let P := pd5_restrictTo T
  let ghostPhase (j : ℕ) := pd5_operationPhase U (pd5_ghostAddresses K j B) φ
  let edgePhase (j : ℕ) := pd5_operationPhase U (pd5_edgeAddresses K j) φ
  let edgeModified (k : ℕ) : Prop :=
    ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U
  let edgeFactor (k : ℕ) : ℝ :=
    if edgeModified k then Real.rpow S.L Ccr else Real.rpow S.L (-G)
  let gain (k : ℕ) : ℝ := ∏ q ∈ Finset.range k, edgeFactor q
  have hTsize (s : MemPoint S.x K) (hs : s ∈ T) : memSize s ≤ B :=
    ((hTstate s).1 hs).2.1
  have hPlainP (f : MemPoint S.x K → ℂ) : pd5_plainTrunc B (P f) = P f := by
    exact pd5_plainTrunc_restrict_eq B T hTsize f
  have hWghost (j : ℕ) : ∀ log, ‖ghostPhase j log‖ ≤ 1 := by
    intro log
    exact pd5_operationPhase_norm_le_one U (pd5_ghostAddresses K j B) φ hφ log
  have hWedge (j : ℕ) : ∀ log, ‖edgePhase j log‖ ≤ 1 := by
    intro log
    exact pd5_operationPhase_norm_le_one U (pd5_edgeAddresses K j) φ hφ log
  have hModAt (W : BirthLog K → ℂ) (hW : ∀ log, ‖W log‖ ≤ 1) :=
    hMod S hS hx₀ w hw W hW
  have hReplaceGhost (W : BirthLog K → ℂ) (f g : MemPoint S.x K → ℂ)
      (hfg : ∀ t ∈ T, f t = g t) (s : MemPoint S.x K) (hs : s ∈ T)
      (j : ℕ) (hj : j ≤ S.N) :
      pd5_ghostBirthTwist F S ρ j W (pd5_plainTrunc B f) s =
        pd5_ghostBirthTwist F S ρ j W (pd5_plainTrunc B g) s := by
    rw [(hModel W f s hs).1 j hj, (hModel W g s hs).1 j hj]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hfg t ht]
  have hReplaceEdge (W : BirthLog K → ℂ) (f g : MemPoint S.x K → ℂ)
      (hfg : ∀ t ∈ T, f t = g t) (s : MemPoint S.x K) (hs : s ∈ T)
      (j : ℕ) (hj : j < S.N) :
      pd5_edgeBirthTwist F S ρ w j W (pd5_plainTrunc B f) s =
        pd5_edgeBirthTwist F S ρ w j W (pd5_plainTrunc B g) s := by
    rw [(hModel W f s hs).2 j hj, (hModel W g s hs).2 j hj]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hfg t ht]
  have hEdgePhase_eq_one (j : ℕ)
      (hno : ¬ ∃ i : Fin K, BirthAddress.edge j i ∈ U) :
      edgePhase j = fun _ => (1 : ℂ) := by
    funext log
    have hdisj : U ∩ pd5_edgeAddresses K j = ∅ := by
      ext a
      constructor
      · intro ha
        rcases Finset.mem_inter.mp ha with ⟨haU, haE⟩
        have hform : ∃ i : Fin K, BirthAddress.edge j i = a := by
          simpa [pd5_edgeAddresses] using haE
        rcases hform with ⟨i, rfl⟩
        exact (hno ⟨i, haU⟩).elim
      · simp
    simp [edgePhase, pd5_operationPhase, pd5_birthPhaseWeight, hdisj]
  have hEdgePhase_eq_memEdge (j : ℕ)
      (hno : ¬ ∃ i : Fin K, BirthAddress.edge j i ∈ U) :
      pd5_edgeBirthTwist F S ρ w j (edgePhase j) =
        memEdge F S ρ w EdgeKind.full j := by
    funext f s
    simp [pd5_edgeBirthTwist, memEdge, plainOp, hEdgePhase_eq_one j hno]
  have hBaseInputSym : IsMemorySymmetric (P memBoundary) :=
    pd5_restrictTo_memSymmetric S T hTmem memBoundary pd5_memBoundary_symmetric
  have hBaseGhostData := hModAt (ghostPhase S.N) (hWghost S.N)
  have hBaseGhostSym : IsMemorySymmetric
      (pd5_ghostBirthTwist F S ρ S.N (ghostPhase S.N) (P memBoundary)) :=
    (hBaseGhostData.1 S.N (le_rfl)).2 (P memBoundary) hBaseInputSym
  let v : ℕ → MemPoint S.x K → ℂ := Nat.rec
    (P (pd5_ghostBirthTwist F S ρ S.N (ghostPhase S.N) (P memBoundary)))
    (fun k fk =>
      let j := S.N - (k + 1)
      P (pd5_ghostBirthTwist F S ρ j (ghostPhase j)
        (P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) fk))))
  have hVsym : ∀ k, k ≤ S.N → IsMemorySymmetric (v k) := by
    intro k hk
    induction k with
    | zero =>
        simpa [v] using
          (pd5_restrictTo_memSymmetric S T hTmem
            (pd5_ghostBirthTwist F S ρ S.N (ghostPhase S.N) (P memBoundary))
            hBaseGhostSym)
    | succ k ih =>
        have hkN : k < S.N := by omega
        have hPrev : IsMemorySymmetric (v k) := ih (by omega)
        let j := S.N - (k + 1)
        have hEdgeSym : IsMemorySymmetric
            (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k)) := by
          exact ((hModAt (edgePhase j) (hWedge j)).2 j (by omega)).2 (v k) hPrev
        have hEdgeProjSym := pd5_restrictTo_memSymmetric S T hTmem
          (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k)) hEdgeSym
        have hGhostData := hModAt (ghostPhase j) (hWghost j)
        have hGhostSym := (hGhostData.1 j (by omega)).2
          (P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k))) hEdgeProjSym
        simpa [v, j] using
          (pd5_restrictTo_memSymmetric S T hTmem
            (pd5_ghostBirthTwist F S ρ j (ghostPhase j)
              (P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k)))) hGhostSym)
  have hGhostContract (j : ℕ) (hj : j ≤ S.N) (W : BirthLog K → ℂ)
      (hW : ∀ log, ‖W log‖ ≤ 1) (f : MemPoint S.x K → ℂ)
      (hf : IsMemorySymmetric f) :
      memNormSqOn F S T
          (P (pd5_ghostBirthTwist F S ρ j W (P f))) ≤
        C_K ^ 2 * memNormSqOn F S T f := by
    exact pd5_memOpNormLE_sym_restrict F S B
      (pd5_ghostBirthTwist F S ρ j W) C_K T hTsize
      ((hModAt W hW).1 j hj).1 f hf hTmem
  have hEdgeContract (k : ℕ) (hk : k < S.N)
      (f : MemPoint S.x K → ℂ) (hf : IsMemorySymmetric f) :
      memNormSqOn F S T
          (P (pd5_edgeBirthTwist F S ρ w (S.N - (k + 1))
            (edgePhase (S.N - (k + 1))) (P f))) ≤
        edgeFactor k ^ 2 * memNormSqOn F S T f := by
    let j := S.N - (k + 1)
    by_cases hm : edgeModified k
    · have hdata := hModAt (edgePhase j) (hWedge j)
      have hbound := pd5_memOpNormLE_sym_restrict F S B
        (pd5_edgeBirthTwist F S ρ w j (edgePhase j)) (Real.rpow S.L Ccr)
        T hTsize (hdata.2 j (by omega)).1 f hf hTmem
      simpa [edgeFactor, edgeModified, j, hm] using hbound
    · have hno : ¬ ∃ i : Fin K, BirthAddress.edge j i ∈ U := by
        intro h
        apply hm
        simpa [edgeModified, j] using h
      have hEq := hEdgePhase_eq_memEdge j hno
      have hbound := pd5_memOpNormLE_sym_restrict F S B
        (memEdge F S ρ w EdgeKind.full j) (Real.rpow S.L (-G))
        T hTsize (hEdge j (by omega)) f hf hTmem
      simpa [edgeFactor, edgeModified, j, hm, hEq] using hbound
  have hBoundaryP : memNormSqOn F S T (P memBoundary) ≤ 2 := by
    rw [pd5_restrictTo_memNormSq_eq]
    exact hBoundary
  have hBaseNorm :
      memNormSqOn F S T (v 0) ≤ 2 * C_K ^ 2 := by
    have hbase := hGhostContract S.N le_rfl (ghostPhase S.N)
      (hWghost S.N) memBoundary pd5_memBoundary_symmetric
    calc
      _ = memNormSqOn F S T
          (P (pd5_ghostBirthTwist F S ρ S.N (ghostPhase S.N) (P memBoundary))) := by
            rfl
      _ ≤ C_K ^ 2 * memNormSqOn F S T memBoundary := hbase
      _ ≤ C_K ^ 2 * 2 := mul_le_mul_of_nonneg_left hBoundary (sq_nonneg C_K)
      _ = 2 * C_K ^ 2 := by ring
  have hVrestrict : ∀ k, P (v k) = v k := by
    intro k
    induction k with
    | zero =>
        change P (P (pd5_ghostBirthTwist F S ρ S.N (ghostPhase S.N)
          (P memBoundary))) = P (pd5_ghostBirthTwist F S ρ S.N
            (ghostPhase S.N) (P memBoundary))
        simpa [P] using pd5_restrictTo_idempotent T
          (pd5_ghostBirthTwist F S ρ S.N (ghostPhase S.N) (P memBoundary))
    | succ k ih =>
        let j := S.N - (k + 1)
        change P (P (pd5_ghostBirthTwist F S ρ j (ghostPhase j)
          (P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k))))) = _
        simpa [P] using pd5_restrictTo_idempotent T
          (pd5_ghostBirthTwist F S ρ j (ghostPhase j)
            (P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k))))
  have hVnorm : ∀ k, k ≤ S.N →
      memNormSqOn F S T (v k) ≤
        2 * C_K ^ (2 * (k + 1)) * gain k ^ 2 := by
    intro k hk
    induction k with
    | zero =>
        simpa [gain] using hBaseNorm
    | succ k ih =>
        have hkN : k < S.N := by omega
        have hPrevNorm := ih (by omega)
        have hPrevSym : IsMemorySymmetric (v k) := hVsym k (by omega)
        let j := S.N - (k + 1)
        let eVec := P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k))
        have hPvk : P (v k) = v k := hVrestrict k
        have hEdgeNorm :
            memNormSqOn F S T eVec ≤ edgeFactor k ^ 2 * memNormSqOn F S T (v k) := by
          simpa [eVec, hPvk] using hEdgeContract k hkN (v k) hPrevSym
        have hInputSym : IsMemorySymmetric eVec := by
          have hEdgeOpSym : IsMemorySymmetric
              (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k)) := by
            by_cases hm : edgeModified k
            · exact ((hModAt (edgePhase j) (hWedge j)).2 j (by omega)).2 (v k) hPrevSym
            · have hno : ¬ ∃ i : Fin K, BirthAddress.edge j i ∈ U := by
                intro h
                apply hm
                simpa [edgeModified, j] using h
              rw [hEdgePhase_eq_one j hno]
              simpa using pd5_edgeBirthTwist_preserves_sym F S ρ w j (fun _ => (1 : ℂ))
                (v k) hPrevSym
          exact pd5_restrictTo_memSymmetric S T hTmem
            (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k)) hEdgeOpSym
        have hPeVec : P eVec = eVec := by
          dsimp [eVec]
          simpa [P] using pd5_restrictTo_idempotent T
            (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k))
        have hGhostNorm :
            memNormSqOn F S T (P (pd5_ghostBirthTwist F S ρ j (ghostPhase j) eVec)) ≤
              C_K ^ 2 * memNormSqOn F S T eVec := by
          simpa [hPeVec] using
            hGhostContract j (by omega) (ghostPhase j) (hWghost j) eVec hInputSym
        have hGain : gain (k + 1) = gain k * edgeFactor k := by
          simp [gain, Finset.prod_range_succ]
        have hPow : C_K ^ 2 * C_K ^ (2 * (k + 1)) = C_K ^ (2 * (k + 2)) := by
          rw [← pow_add]
          congr 1
          omega
        calc
          _ = memNormSqOn F S T
              (P (pd5_ghostBirthTwist F S ρ j (ghostPhase j) eVec)) := by
                simp [v, j, eVec, hPeVec]
          _ ≤ C_K ^ 2 * memNormSqOn F S T eVec := hGhostNorm
          _ ≤ C_K ^ 2 * (edgeFactor k ^ 2 * memNormSqOn F S T (v k)) :=
                mul_le_mul_of_nonneg_left hEdgeNorm (sq_nonneg C_K)
          _ ≤ C_K ^ 2 * (edgeFactor k ^ 2 *
                (2 * C_K ^ (2 * (k + 1)) * gain k ^ 2)) := by
                calc
                  _ = (C_K ^ 2 * edgeFactor k ^ 2) * memNormSqOn F S T (v k) := by ring
                  _ ≤ (C_K ^ 2 * edgeFactor k ^ 2) *
                        (2 * C_K ^ (2 * (k + 1)) * gain k ^ 2) :=
                    mul_le_mul_of_nonneg_left hPrevNorm
                      (mul_nonneg (sq_nonneg C_K) (sq_nonneg (edgeFactor k)))
                  _ = _ := by ring
          _ = 2 * (C_K ^ 2 * C_K ^ (2 * (k + 1))) *
                (gain k * edgeFactor k) ^ 2 := by ring
          _ = 2 * C_K ^ (2 * (k + 2)) * gain (k + 1) ^ 2 := by
                rw [hPow, hGain]
  have hVeq : ∀ k, k ≤ S.N → ∀ s ∈ T,
      v k s = pd5_phaseHistoryFn F S ρ w B U φ k s := by
    intro k hk
    induction k with
    | zero =>
        intro s hs
        have hfg : ∀ t ∈ T, memBoundary t = (P memBoundary) t := by
          intro t ht
          simp [P, pd5_restrictTo, ht]
        have hrep := hReplaceGhost (ghostPhase S.N) memBoundary (P memBoundary)
          hfg s hs S.N (le_rfl)
        calc
          v 0 s = pd5_ghostBirthTwist F S ρ S.N (ghostPhase S.N)
              (P memBoundary) s := by simp [v, P, pd5_restrictTo, hs]
          _ = pd5_ghostBirthTwist F S ρ S.N (ghostPhase S.N)
                (pd5_plainTrunc B (P memBoundary)) s := by
                  rw [hPlainP memBoundary]
          _ = pd5_ghostBirthTwist F S ρ S.N (ghostPhase S.N)
                (pd5_plainTrunc B memBoundary) s := hrep.symm
          _ = pd5_phaseHistoryFn F S ρ w B U φ 0 s := by
                simpa [pd5_phaseHistoryFn, pd5_plainTrunc, ghostPhase, hTsize s hs]
                  using hrep.symm
    | succ k ih =>
        have hkN : k < S.N := by omega
        let j := S.N - (k + 1)
        intro s hs
        have hprev : ∀ t ∈ T, pd5_phaseHistoryFn F S ρ w B U φ k t = v k t := by
          intro t ht
          exact (ih (by omega) t ht).symm
        have hTruncPrev : pd5_plainTrunc B (v k) = v k := by
          calc
            _ = pd5_plainTrunc B (P (v k)) := by rw [hVrestrict k]
            _ = P (v k) := hPlainP (v k)
            _ = v k := hVrestrict k
        have hfgEdge :
            ∀ t ∈ T,
              pd5_edgeBirthTwist F S ρ w j (edgePhase j)
                  (pd5_plainTrunc B (pd5_phaseHistoryFn F S ρ w B U φ k)) t =
                (P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k))) t := by
          intro t ht
          have hj : j < S.N := by dsimp [j]; omega
          have he := hReplaceEdge (edgePhase j)
            (pd5_phaseHistoryFn F S ρ w B U φ k) (v k) hprev t ht j hj
          rw [hTruncPrev] at he
          simpa [P, pd5_restrictTo, ht] using he
        have hfgGhost := hReplaceGhost (ghostPhase j)
          (pd5_edgeBirthTwist F S ρ w j (edgePhase j)
            (pd5_plainTrunc B (pd5_phaseHistoryFn F S ρ w B U φ k)))
          (P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k)))
          hfgEdge s hs j (by omega)
        have hTruncEdge : pd5_plainTrunc B
            (P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k))) =
              P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k)) :=
          hPlainP _
        calc
          v (k + 1) s =
              pd5_ghostBirthTwist F S ρ j (ghostPhase j)
                (P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k))) s := by
                  simp [v, P, pd5_restrictTo, hs, j]
          _ = pd5_ghostBirthTwist F S ρ j (ghostPhase j)
                (pd5_plainTrunc B
                  (P (pd5_edgeBirthTwist F S ρ w j (edgePhase j) (v k)))) s := by
                  rw [hTruncEdge]
          _ = pd5_ghostBirthTwist F S ρ j (ghostPhase j)
                (pd5_plainTrunc B (pd5_edgeBirthTwist F S ρ w j (edgePhase j)
                  (pd5_plainTrunc B (pd5_phaseHistoryFn F S ρ w B U φ k)))) s :=
                  hfgGhost.symm
          _ = pd5_phaseHistoryFn F S ρ w B U φ (k + 1) s := by
                simp [pd5_phaseHistoryFn, j, ghostPhase, edgePhase,
                  pd5_plainTrunc, hTsize s hs]
  have hfinalEq :
      memNormSqOn F S T (P (pd5_phaseHistoryFn F S ρ w B U φ S.N)) =
        memNormSqOn F S T (v S.N) := by
    calc
      _ = memNormSqOn F S T (pd5_phaseHistoryFn F S ρ w B U φ S.N) :=
        pd5_restrictTo_memNormSq_eq F S T _
      _ = memNormSqOn F S T (v S.N) := by
        unfold memNormSqOn
        apply Finset.sum_congr rfl
        intro s hs
        rw [hVeq S.N (le_rfl) s hs]
  rw [hfinalEq]
  simpa [gain, edgeFactor, edgeModified] using hVnorm S.N (le_rfl)

set_option maxHeartbeats 6000000 in
private theorem pd5_phaseHistory_norm_bound {K : ℕ}
    (δ c₁ c₂ : ℝ) (F : PDFix K) (S : PDScale) (hS : S.Valid K δ c₁ c₂)
    (ρ : ℝ) (w : ArchRoot) (hw : w.InRegion S) (hLone : 1 ≤ S.L)
    (C_K Ccr x₀ : ℝ) (hC_K : 0 < C_K) (hx₀ : x₀ ≤ S.x)
    (hMod : PD5ModifiedBounds δ c₁ c₂ F ρ C_K Ccr x₀)
    (G : ℝ) (hEdge : ∀ j : ℕ, j < S.N →
      MemOpNormLE_sym F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
        (Real.rpow S.L (-G)))
    (U : Finset (BirthAddress K)) (φ : BirthAddress K → ℕ → ℂ)
    (hφ : ∀ a p, ‖φ a p‖ ≤ 1)
    (T : Finset (MemPoint S.x K))
    (hTstate : ∀ s, s ∈ T ↔ pd5_stateRegion F S w (memoryCutoff S) s)
    (hTmem : ∀ s σ, memoryPermute s σ ∈ T ↔ s ∈ T)
    (hModel : PD5IterationChronologicalExpansion F S ρ w (memoryCutoff S) T)
    (hμ : ∀ s, 0 ≤ memMeasure F S s)
    (hBoundary : memNormSqOn F S T memBoundary ≤ 2) :
    ‖pd5_phaseHistory F S ρ w (memoryCutoff S) U φ‖ ≤
      2 * C_K ^ (S.N + 1) *
        ∏ k ∈ Finset.range S.N,
          if ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U then
            Real.rpow S.L Ccr else Real.rpow S.L (-G) := by
  classical
  let B := memoryCutoff S
  let P := pd5_restrictTo T
  let initPhase := pd5_operationPhase U (pd5_initialAddresses S.x K) φ
  let bPhase : MemPoint S.x K → ℂ := fun s =>
    memBoundary s * star (initPhase (initialLog s))
  have hBPhaseNorm : memNormSqOn F S T bPhase ≤ 2 := by
    unfold memNormSqOn
    calc
      _ ≤ ∑ s ∈ T, memMeasure F S s * ‖memBoundary s‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro s hs
            apply mul_le_mul_of_nonneg_left _ (hμ s)
            have hphase := pd5_operationPhase_norm_le_one U
              (pd5_initialAddresses S.x K) φ hφ (initialLog s)
            have hnorm : ‖bPhase s‖ ≤ ‖memBoundary s‖ := by
              dsimp [bPhase]
              rw [norm_mul]
              have hphaseStar : ‖star (initPhase (initialLog s))‖ ≤ 1 := by
                simpa using hphase
              calc
                ‖memBoundary s‖ * ‖star (initPhase (initialLog s))‖ ≤
                    ‖memBoundary s‖ * 1 :=
                  mul_le_mul_of_nonneg_left hphaseStar (norm_nonneg _)
                _ = ‖memBoundary s‖ := by ring
            exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
      _ = memNormSqOn F S T memBoundary := by rfl
      _ ≤ 2 := hBoundary
  let fFinal := P (pd5_phaseHistoryFn F S ρ w B U φ S.N)
  have hFinalNormSq : memNormSqOn F S T fFinal ≤
      2 * C_K ^ (2 * (S.N + 1)) *
        (∏ k ∈ Finset.range S.N,
          if ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U then
            Real.rpow S.L Ccr else Real.rpow S.L (-G)) ^ 2 := by
    simpa [fFinal] using pd5_phaseHistoryFn_norm_sq_bound δ c₁ c₂ F S hS
      ρ w hw C_K Ccr x₀ hC_K hx₀ hMod G hEdge U φ hφ T hTstate hTmem hModel hBoundary
  let summand (s : MemPoint S.x K) : ℂ :=
    (memMeasure F S s : ℂ) * star (memBoundary s) *
      initPhase (initialLog s) * pd5_phaseHistoryFn F S ρ w B U φ S.N s
  have hzero (s : MemPoint S.x K) (hs : s ∉ T) : summand s = 0 := by
    by_cases hμ0 : memMeasure F S s = 0
    · simp [summand, hμ0]
    · by_cases hB0 : memBoundary s = 0
      · simp [summand, hB0]
      · have hvalid : MemValid F S s := by
          by_contra hnot
          have hz : memMeasure F S s = 0 := by simp [memMeasure, hnot]
          exact hμ0 hz
        have hboundaryState : s.1 = (1, 0) ∧ ∀ i, s.2.2 i = [] := by
          by_contra hnot
          have hz : memBoundary s = 0 := by simp [memBoundary, hnot]
          exact hB0 hz
        have hstate : pd5_stateRegion F S w B s := by
          refine ⟨hvalid, ?_, Or.inl hboundaryState.1⟩
          simp [memSize, hboundaryState.2]
        exact False.elim (hs ((hTstate s).2 hstate))
  have hpairEq :
      pd5_phaseHistory F S ρ w B U φ =
        ∑ s ∈ T, (memMeasure F S s : ℂ) * star (bPhase s) * fFinal s := by
    unfold pd5_phaseHistory
    rw [tsum_eq_sum hzero]
    apply Finset.sum_congr rfl
    intro s hs
    have hstar : star (bPhase s) = star (memBoundary s) * initPhase (initialLog s) := by
      simp [bPhase, star_mul, star_star] <;> ring
    have hfFinal : fFinal s = pd5_phaseHistoryFn F S ρ w B U φ S.N s := by
      simp [fFinal, P, pd5_restrictTo, hs]
    dsimp [summand]
    have hstar' : (starRingEnd ℂ) (bPhase s) =
        star (memBoundary s) * initPhase (initialLog s) := hstar
    rw [hstar', hfFinal]
    ac_rfl
  have hPairSq := pd5_finite_inner_sq_le F S T bPhase fFinal
    (fun s hs => hμ s)
  have hFinalNormNonneg : 0 ≤ memNormSqOn F S T fFinal := by
    unfold memNormSqOn
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (hμ s) (sq_nonneg _)
  have hPairNormSq :
      ‖pd5_phaseHistory F S ρ w B U φ‖ ^ 2 ≤
        4 * C_K ^ (2 * (S.N + 1)) *
          (∏ k ∈ Finset.range S.N,
            if ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U then
              Real.rpow S.L Ccr else Real.rpow S.L (-G)) ^ 2 := by
    rw [hpairEq]
    calc
      _ ≤ memNormSqOn F S T bPhase * memNormSqOn F S T fFinal := hPairSq
      _ ≤ 2 * memNormSqOn F S T fFinal :=
        mul_le_mul_of_nonneg_right hBPhaseNorm hFinalNormNonneg
      _ ≤ 2 * (2 * C_K ^ (2 * (S.N + 1)) *
            (∏ k ∈ Finset.range S.N,
              if ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U then
                Real.rpow S.L Ccr else Real.rpow S.L (-G)) ^ 2) :=
        mul_le_mul_of_nonneg_left hFinalNormSq (by norm_num)
      _ = _ := by ring
  have hprodNonneg : 0 ≤ ∏ k ∈ Finset.range S.N,
      if ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U then
        Real.rpow S.L Ccr else Real.rpow S.L (-G) := by
    apply Finset.prod_nonneg
    intro k hk
    split_ifs <;> exact Real.rpow_nonneg (le_trans (by norm_num) hLone) _
  have htargetNonneg : 0 ≤ 2 * C_K ^ (S.N + 1) *
      (∏ k ∈ Finset.range S.N,
        if ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U then
          Real.rpow S.L Ccr else Real.rpow S.L (-G)) := by
    exact mul_nonneg (by positivity) hprodNonneg
  have htargetSq :
      (2 * C_K ^ (S.N + 1) *
        (∏ k ∈ Finset.range S.N,
          if ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U then
            Real.rpow S.L Ccr else Real.rpow S.L (-G)) ) ^ 2 =
        4 * C_K ^ (2 * (S.N + 1)) *
          (∏ k ∈ Finset.range S.N,
            if ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U then
              Real.rpow S.L Ccr else Real.rpow S.L (-G)) ^ 2 := by
    rw [mul_pow, pow_mul]
    ring
  apply (sq_le_sq₀ (norm_nonneg _) htargetNonneg).mp
  rw [htargetSq]
  exact hPairNormSq

private theorem pd5_iteration_edgeGain_product_le (L G C r : ℝ)
    (hLone : 1 ≤ L) (hG : 0 < G) (hC : 0 < C)
    (N : ℕ) (E : Finset ℕ) (hE : E ⊆ Finset.range N)
    (hcard : (E.card : ℝ) ≤ 2 * r) :
    (∏ k ∈ Finset.range N,
      if k ∈ E then Real.rpow L C else Real.rpow L (-G)) ≤
      Real.rpow L (-G * ((N : ℝ) - 2 * r)) * Real.rpow L (2 * C * r) := by
  classical
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hfactor :
      (∏ k ∈ Finset.range N,
        if k ∈ E then Real.rpow L C else Real.rpow L (-G)) =
        (∏ k ∈ Finset.range N, Real.rpow L (-G)) *
          (∏ k ∈ Finset.range N,
            if k ∈ E then Real.rpow L (C + G) else 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    by_cases he : k ∈ E
    · simp [he]
      calc
        Real.rpow L C = Real.rpow L (-G + (C + G)) := by congr 1 <;> ring
        _ = Real.rpow L (-G) * Real.rpow L (C + G) := Real.rpow_add hLpos _ _
    · simp [he]
  have hconst : (∏ k ∈ Finset.range N, Real.rpow L (-G)) =
      Real.rpow L ((-G) * (N : ℝ)) := by
    calc
      _ = (Real.rpow L (-G)) ^ N := by simp
      _ = Real.rpow L ((-G) * (N : ℝ)) :=
        (Real.rpow_mul_natCast hLpos.le (-G) N).symm
  have hfilter : (Finset.range N).filter (fun k => k ∈ E) = E := by
    ext k
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro h
      exact Finset.mem_filter.mpr ⟨hE h, h⟩
  have hselected :
      (∏ k ∈ Finset.range N,
        if k ∈ E then Real.rpow L (C + G) else 1) =
        Real.rpow L ((C + G) * (E.card : ℝ)) := by
    calc
      _ = ∏ k ∈ (Finset.range N).filter (fun k => k ∈ E), Real.rpow L (C + G) := by
        rw [← Finset.prod_filter]
      _ = ∏ k ∈ E, Real.rpow L (C + G) := by rw [hfilter]
      _ = (Real.rpow L (C + G)) ^ E.card := by simp
      _ = Real.rpow L ((C + G) * (E.card : ℝ)) :=
        (Real.rpow_mul_natCast hLpos.le (C + G) E.card).symm
  have hEq :
      (∏ k ∈ Finset.range N,
        if k ∈ E then Real.rpow L C else Real.rpow L (-G)) =
        Real.rpow L ((-G) * (N : ℝ) + (C + G) * (E.card : ℝ)) := by
    rw [hfactor, hconst, hselected]
    exact (Real.rpow_add hLpos _ _).symm
  have hA : (E.card : ℝ) ≤ 2 * r := hcard
  have hExp :
      (-G) * (N : ℝ) + (C + G) * (E.card : ℝ) ≤
        (-G) * ((N : ℝ) - 2 * r) + 2 * C * r := by
    have hN : (N : ℝ) - 2 * r ≤ (N : ℝ) - (E.card : ℝ) := by linarith
    calc
      (-G) * (N : ℝ) + (C + G) * (E.card : ℝ)
          = (-G) * ((N : ℝ) - (E.card : ℝ)) + C * (E.card : ℝ) := by ring
      _ ≤ (-G) * ((N : ℝ) - 2 * r) + C * (2 * r) := by
        apply add_le_add
        · exact mul_le_mul_of_nonpos_left hN (by linarith)
        · exact mul_le_mul_of_nonneg_left hA hC.le
      _ = (-G) * ((N : ℝ) - 2 * r) + 2 * C * r := by ring
  calc
    _ = Real.rpow L ((-G) * (N : ℝ) + (C + G) * (E.card : ℝ)) := hEq
    _ ≤ Real.rpow L ((-G) * ((N : ℝ) - 2 * r) + 2 * C * r) :=
      Real.rpow_le_rpow_of_exponent_le hLone hExp
    _ = Real.rpow L (-G * ((N : ℝ) - 2 * r)) * Real.rpow L (2 * C * r) :=
      Real.rpow_add hLpos _ _

private def pd5_modifiedEdgeVisits {K : ℕ} (N : ℕ) (U : Finset (BirthAddress K)) :
    Finset ℕ :=
  (Finset.range N).filter fun k =>
    ∃ i : Fin K, BirthAddress.edge (N - (k + 1)) i ∈ U

private theorem pd5_modifiedEdgeVisits_card_le {K : ℕ} (N : ℕ)
    (U : Finset (BirthAddress K)) : (pd5_modifiedEdgeVisits N U).card ≤ U.card := by
  classical
  let E := pd5_modifiedEdgeVisits N U
  let f : {k // k ∈ E} → {a // a ∈ U} := fun k =>
    let hs := (Finset.mem_filter.mp k.property).2
    ⟨BirthAddress.edge (N - (k.1 + 1)) (Classical.choose hs), Classical.choose_spec hs⟩
  have hf : Function.Injective f := by
    intro k k' h
    apply Subtype.ext
    have haddr := congrArg Subtype.val h
    injection haddr with hstep hi
    have hk : k.1 < N := by simpa [E, pd5_modifiedEdgeVisits] using
      (Finset.mem_filter.mp k.property).1
    have hk' : k'.1 < N := by simpa [E, pd5_modifiedEdgeVisits] using
      (Finset.mem_filter.mp k'.property).1
    omega
  simpa [E] using Finset.card_le_card_of_injective hf

set_option maxHeartbeats 8000000 in
/-- Iterate norms on the finite invariant state set, with at most twice the rank modified
edges. The exponent uses real N-2r even when negative. Guide
`runs/lanes/sol-thin-pd5/PROOFS.md:771–832`; uses boundary, finite model, Fourier, phase
attachment, rank support and the supplied modified bounds; feeds frozen history_rank_low. -/
theorem pd5_low_rank_iteration (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ)
    (hboundary : PD5BoundaryAvailable δ c₁ c₂ F)
    (hmodified : PD5ModifiedBoundsAvailable δ c₁ c₂ F ρ) :
    ∃ C_K Ccr x₀ : ℝ, 0 < C_K ∧ 0 < Ccr ∧ 2 ≤ x₀ ∧
      ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
        ∀ G : ℝ, 0 < G →
          (∀ j : ℕ, j < S.N →
            MemOpNormLE_sym F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
              (Real.rpow S.L (-G))) →
          ∀ C ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)),
            ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ ≤
              2 * C_K ^ (S.N + 1) *
                Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (constraintRank C : ℝ))) *
                Real.rpow S.L (2 * Ccr * (constraintRank C : ℝ)) := by
  classical
  rcases hboundary with ⟨xB, hxB, hBoundary⟩
  rcases hmodified with ⟨C_K, Ccr, xM, hC_K, hCcr, hxM, hMod⟩
  obtain ⟨xScale, hxScale, hScale⟩ := pd5_scale_facts K F hF
  let x₀ : ℝ := max xB (max xM xScale)
  refine ⟨C_K, Ccr, x₀, hC_K, hCcr, ?_, ?_⟩
  · dsimp [x₀]
    exact le_trans hxB (le_max_left _ _)
  · intro S hS hxS w hw G hG hEdge C hC
    have hxB' : xB ≤ S.x := by
      have hle : xB ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
      exact hle.trans hxS
    have hxM' : xM ≤ S.x := by
      have hle₁ : xM ≤ max xM xScale := le_max_left _ _
      have hle₂ : max xM xScale ≤ x₀ := by
        dsimp [x₀]
        exact le_max_right _ _
      exact (hle₁.trans hle₂).trans hxS
    have hxScale' : xScale ≤ S.x := by
      have hle₁ : xScale ≤ max xM xScale := le_max_right _ _
      have hle₂ : max xM xScale ≤ x₀ := by
        dsimp [x₀]
        exact le_max_right _ _
      exact (hle₁.trans hle₂).trans hxS
    rcases hScale S hxScale' with ⟨hLone, hNtwo, hNlow, hNup, hMup,
      hBbound, hMleN, hMass⟩
    let B : ℕ := memoryCutoff S
    let A : Finset (BirthAddress K) := birthAddresses S.x K B
    let U : Finset (BirthAddress K) := C.biUnion id
    have hCS : IsConstraintSystem A C := (Finset.mem_filter.mp hC).2
    have hU : U ⊆ A := by
      intro a ha
      rcases Finset.mem_biUnion.mp ha with ⟨D, hD, haD⟩
      exact (hCS.1 D hD).1 haD
    have hRankSupport := pd5_rank_support_mass A
    have hUcard : U.card ≤ 2 * constraintRank C := by
      simpa [U] using (hRankSupport.1 C hC).1
    let E : Finset ℕ := pd5_modifiedEdgeVisits S.N U
    have hEsubset : E ⊆ Finset.range S.N := by
      exact Finset.filter_subset _ _
    have hEcard : E.card ≤ 2 * constraintRank C :=
      (pd5_modifiedEdgeVisits_card_le S.N U).trans hUcard
    have hEcardReal : (E.card : ℝ) ≤ 2 * (constraintRank C : ℝ) := by
      exact_mod_cast hEcard
    have hGainBound := pd5_iteration_edgeGain_product_le S.L G Ccr
      (constraintRank C : ℝ) hLone hG hCcr S.N E hEsubset hEcardReal
    obtain ⟨T, hTstate, hTmem, hModel⟩ :=
      pd5_chronological_model δ c₁ c₂ K F S hS ρ w hw B
    let hExpansion : PD5IterationChronologicalExpansion F S ρ w B T := hModel
    have hTmemIff : ∀ s σ, memoryPermute s σ ∈ T ↔ s ∈ T := by
      intro s σ
      rw [hTstate, hTstate, pd5_stateRegion_memoryPermute_iff]
    let hBoundaryS := hBoundary S hS hxB'
    have hbox := pd5_envBox_finite_of_valid hS hw
    let Pset := markedPrimes S.x K F.a
    let Tprime : ℕ := Pset.sup id + 1
    have hTprimePos : 0 < Tprime := by dsimp [Tprime]; omega
    letI : NeZero Tprime := ⟨ne_of_gt hTprimePos⟩
    have hPrimeLt : ∀ p ∈ Pset, p < Tprime := by
      intro p hp
      dsimp [Tprime]
      exact Nat.lt_succ_of_le (Finset.le_sup (s := Pset) (f := id) hp)
    have hFourier := pd5_fourier_birth_constraints F S ρ w B A C hCS
      (by intro a ha; exact ha) hPrimeLt hbox
    let Θ := {p : A × A // p ∈ pd5_systemPairs A C hCS} → ZMod Tprime
    let productBound : ℝ :=
      2 * C_K ^ (S.N + 1) *
        (Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (constraintRank C : ℝ))) *
          Real.rpow S.L (2 * Ccr * (constraintRank C : ℝ)))
    have hModifiedEdgeVisits :
        (∏ k ∈ Finset.range S.N,
          if ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U then
            Real.rpow S.L Ccr else Real.rpow S.L (-G)) =
          ∏ k ∈ Finset.range S.N,
            if k ∈ E then Real.rpow S.L Ccr else Real.rpow S.L (-G) := by
      apply Finset.prod_congr rfl
      intro k hk
      by_cases hmod : ∃ i : Fin K, BirthAddress.edge (S.N - (k + 1)) i ∈ U
      · simp [E, pd5_modifiedEdgeVisits, hmod, hk]
      · simp [E, pd5_modifiedEdgeVisits, hmod, hk]
    have hPhaseBound : ∀ θ : Θ,
        ‖memHistory F S ρ w (some B) none
          (fun log => pd5b_systemPairPhase A C hCS log θ)‖ ≤ productBound := by
      intro θ
      let φθ : BirthAddress K → ℕ → ℂ := fun a p =>
        ZMod.stdAddChar
          (pd5b_pairAddressCoeff A C hCS θ a * (p : ZMod Tprime))
      have hφθ : ∀ a p, ‖φθ a p‖ ≤ 1 := by
        intro a p
        exact (pd5_stdAddChar_norm
          (pd5b_pairAddressCoeff A C hCS θ a * (p : ZMod Tprime))).le
      have hPairEq :
          (fun log => pd5b_systemPairPhase A C hCS log θ) =
            pd5_birthPhaseWeight U φθ := by
        funext log
        simpa [U, φθ] using pd5_pairPhase_eq_birthPhase A C hCS θ log
      have hAttach := pd5_phase_at_births F S ρ w B U hU φθ hφθ hbox
      have hPhaseHistEq :
          memHistory F S ρ w (some B) none
              (fun log => pd5b_systemPairPhase A C hCS log θ) =
            pd5_phaseHistory F S ρ w B U φθ := by
        rw [hPairEq]
        exact hAttach
      have hPhaseRaw := pd5_phaseHistory_norm_bound δ c₁ c₂ F S hS ρ w hw
        hLone C_K Ccr xM hC_K hxM' hMod G hEdge U φθ hφθ T hTstate hTmemIff
        hExpansion hBoundaryS.1 (hBoundaryS.2 T)
      rw [hModifiedEdgeVisits] at hPhaseRaw
      have hPhaseFinal : ‖pd5_phaseHistory F S ρ w B U φθ‖ ≤ productBound := by
        dsimp [productBound]
        calc
          _ ≤ 2 * C_K ^ (S.N + 1) *
                (∏ k ∈ Finset.range S.N,
                  if k ∈ E then Real.rpow S.L Ccr else Real.rpow S.L (-G)) := hPhaseRaw
          _ ≤ 2 * C_K ^ (S.N + 1) *
                (Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (constraintRank C : ℝ))) *
                  Real.rpow S.L (2 * Ccr * (constraintRank C : ℝ))) :=
              mul_le_mul_of_nonneg_left hGainBound (by positivity)
      rw [hPhaseHistEq]
      exact hPhaseFinal
    have hcardThetaPos : 0 < Fintype.card Θ := Fintype.card_pos
    have hcardThetaRealPos : 0 < (Fintype.card Θ : ℝ) := by exact_mod_cast hcardThetaPos
    have hcardThetaNe : (Fintype.card Θ : ℝ) ≠ 0 := ne_of_gt hcardThetaRealPos
    have hInvNorm : ‖(Fintype.card Θ : ℂ)⁻¹‖ = (Fintype.card Θ : ℝ)⁻¹ := by
      rw [norm_inv, norm_natCast]
    have hSumBound :
        (∑ θ : Θ,
          ‖memHistory F S ρ w (some B) none
            (fun log => pd5b_systemPairPhase A C hCS log θ)‖) ≤
          (Fintype.card Θ : ℝ) * productBound := by
      calc
        _ ≤ ∑ _θ : Θ, productBound :=
          Finset.sum_le_sum fun θ hθ => hPhaseBound θ
        _ = (Fintype.card Θ : ℝ) * productBound := by simp
    have hAverage :
        ‖(Fintype.card Θ : ℂ)⁻¹ *
          ∑ θ : Θ,
            memHistory F S ρ w (some B) none
              (fun log => pd5b_systemPairPhase A C hCS log θ)‖ ≤ productBound := by
      calc
        _ = ‖(Fintype.card Θ : ℂ)⁻¹‖ *
              ‖∑ θ : Θ,
                memHistory F S ρ w (some B) none
                  (fun log => pd5b_systemPairPhase A C hCS log θ)‖ := norm_mul _ _
        _ ≤ (Fintype.card Θ : ℝ)⁻¹ *
              (∑ θ : Θ,
                ‖memHistory F S ρ w (some B) none
                  (fun log => pd5b_systemPairPhase A C hCS log θ)‖) := by
              rw [hInvNorm]
              exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
        _ ≤ (Fintype.card Θ : ℝ)⁻¹ *
              ((Fintype.card Θ : ℝ) * productBound) :=
              mul_le_mul_of_nonneg_left hSumBound (by positivity)
        _ = productBound := by field_simp [hcardThetaNe]
    calc
      _ = ‖(Fintype.card Θ : ℂ)⁻¹ *
            ∑ θ : Θ,
              memHistory F S ρ w (some B) none
                (fun log => pd5b_systemPairPhase A C hCS log θ)‖ := by rw [hFourier]
      _ ≤ productBound := hAverage
      _ = _ := by dsimp [productBound]; ring

end
end ArtinPrimitiveRoots.TypeII.PD
