import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_edge_position_mass_le
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_positive_choice_rows
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_chronological_model
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».Defs
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».pd5_edgeBirthTwist_preserves_sym

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

private theorem pd5_memSize_memoryPermute {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) : memSize (memoryPermute s σ) = memSize s := by
  simp [memSize, memoryPermute]

/-- The memory-symmetrized delta has total absolute mass at most one on any finite set. -/
private theorem pd5_memorySym_delta_norm_sum_le {x : ℝ} {K : ℕ}
    (T : Finset (MemPoint x K)) (s : MemPoint x K) :
    (∑ t ∈ T, ‖memorySym (fun u => if u = t then (1 : ℂ) else 0) s‖) ≤ 1 := by
  classical
  let G := MemoryPermutation s
  let d := Fintype.card G
  have hd : 0 < d := Fintype.card_pos
  have hterm (t : MemPoint x K) :
      ‖memorySym (fun u => if u = t then (1 : ℂ) else 0) s‖ ≤
        (d : ℝ)⁻¹ * ∑ σ : G, if memoryPermute s σ = t then (1 : ℝ) else 0 := by
    unfold memorySym
    have hInv : ‖(d : ℂ)⁻¹‖ = (d : ℝ)⁻¹ := by
      rw [norm_inv, norm_natCast]
    have hSummand (σ : G) :
        ‖(if memoryPermute s σ = t then (1 : ℂ) else 0)‖ =
          if memoryPermute s σ = t then (1 : ℝ) else 0 := by
      by_cases h : memoryPermute s σ = t <;> simp [h]
    calc
      ‖(d : ℂ)⁻¹ * ∑ σ : G, (if memoryPermute s σ = t then (1 : ℂ) else 0)‖
          = ‖(d : ℂ)⁻¹‖ *
              ‖∑ σ : G, (if memoryPermute s σ = t then (1 : ℂ) else 0)‖ := norm_mul _ _
      _ ≤ (d : ℝ)⁻¹ *
            ∑ σ : G, ‖if memoryPermute s σ = t then (1 : ℂ) else 0‖ := by
          rw [hInv]
          exact mul_le_mul_of_nonneg_left
            (norm_sum_le (Finset.univ : Finset G)
              (fun σ => if memoryPermute s σ = t then (1 : ℂ) else 0)) (by positivity)
      _ = (d : ℝ)⁻¹ *
            ∑ σ : G, if memoryPermute s σ = t then (1 : ℝ) else 0 := by
          exact congrArg (fun r : ℝ => (d : ℝ)⁻¹ * r)
            (Finset.sum_congr rfl fun σ _ => hSummand σ)
  have hinner (σ : G) :
      (∑ t ∈ T, if memoryPermute s σ = t then (1 : ℝ) else 0) ≤ 1 := by
    by_cases hσ : memoryPermute s σ ∈ T
    · rw [Finset.sum_eq_single (memoryPermute s σ)]
      · simp
      · intro t ht hne
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot hσ).elim
    · have hzero :
          (∑ t ∈ T, if memoryPermute s σ = t then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        by_cases heq : memoryPermute s σ = t
        · subst t
          exact False.elim (hσ ht)
        · simp [heq]
      rw [hzero]
      norm_num
  calc
    (∑ t ∈ T, ‖memorySym (fun u => if u = t then (1 : ℂ) else 0) s‖)
        ≤ ∑ t ∈ T, (d : ℝ)⁻¹ *
            ∑ σ : G, if memoryPermute s σ = t then (1 : ℝ) else 0 :=
          Finset.sum_le_sum fun t ht => hterm t
    _ = ∑ t ∈ T, ∑ σ : G,
          (d : ℝ)⁻¹ * (if memoryPermute s σ = t then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
    _ = ∑ σ : G, ∑ t ∈ T,
          (d : ℝ)⁻¹ * (if memoryPermute s σ = t then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ σ : G, (d : ℝ)⁻¹ *
          ∑ t ∈ T, if memoryPermute s σ = t then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [Finset.mul_sum]
    _ = (d : ℝ)⁻¹ *
          ∑ σ : G, ∑ t ∈ T, if memoryPermute s σ = t then (1 : ℝ) else 0 := by
          symm
          rw [Finset.mul_sum]
    _ ≤ (d : ℝ)⁻¹ * ∑ _σ : G, (1 : ℝ) := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.sum_le_sum fun σ hσ => hinner σ
          · positivity
    _ = 1 := by simp [d]

private theorem pd5_memorySym_delta_size_eq_of_ne_zero {x : ℝ} {K : ℕ}
    (s t : MemPoint x K)
    (h : memorySym (fun u => if u = t then (1 : ℂ) else 0) s ≠ 0) :
    memSize s = memSize t := by
  classical
  by_contra hsize
  have hne (σ : MemoryPermutation s) : memoryPermute s σ ≠ t := by
    intro heq
    apply hsize
    calc
      memSize s = memSize (memoryPermute s σ) := (pd5_memSize_memoryPermute s σ).symm
      _ = memSize t := by rw [heq]
  have hzero :
      (∑ σ : MemoryPermutation s,
        if memoryPermute s σ = t then (1 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro σ hσ
    simp [hne σ]
  have hz : memorySym (fun u => if u = t then (1 : ℂ) else 0) s = 0 := by
    simp [memorySym, hzero]
  exact h hz

private theorem pd5_memorySym_delta_weighted_norm_sum_le {x : ℝ} {K : ℕ}
    (T : Finset (MemPoint x K)) (s : MemPoint x K) (v : ℝ) (hv : 1 < v) :
    (∑ t ∈ T,
      ‖memorySym (fun u => if u = t then (1 : ℂ) else 0) s‖ * v ^ memSize t) ≤
        v ^ memSize s := by
  have hterm (t : MemPoint x K) :
      ‖memorySym (fun u => if u = t then (1 : ℂ) else 0) s‖ * v ^ memSize t ≤
        ‖memorySym (fun u => if u = t then (1 : ℂ) else 0) s‖ * v ^ memSize s := by
    by_cases hzero : memorySym (fun u => if u = t then (1 : ℂ) else 0) s = 0
    · simp [hzero]
    · have hs := pd5_memorySym_delta_size_eq_of_ne_zero s t hzero
      rw [hs]
  calc
    _ ≤ ∑ t ∈ T,
          ‖memorySym (fun u => if u = t then (1 : ℂ) else 0) s‖ * v ^ memSize s :=
        Finset.sum_le_sum fun t ht => hterm t
    _ = (∑ t ∈ T, ‖memorySym (fun u => if u = t then (1 : ℂ) else 0) s‖) *
          v ^ memSize s := by rw [Finset.sum_mul]
    _ ≤ 1 * v ^ memSize s :=
        mul_le_mul_of_nonneg_right (pd5_memorySym_delta_norm_sum_le T s) (by positivity)
    _ = v ^ memSize s := by ring

private theorem pd5_memSize_activePermute {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) :
    memSize (s.1, permuteLists σ s.2.1, s.2.2) = memSize s := by
  rfl

private theorem pd5_memValid_activePermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
    MemValid F S (s.1, permuteLists σ s.2.1, s.2.2) := by
  refine ⟨hs.1, ?_, hs.2.2⟩
  intro i j
  exact hs.2.1 i (σ i j)

private theorem pd5_stateRegion_activePermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (B : ℕ) (s : MemPoint S.x K) (hs : pd5_stateRegion F S w B s)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
    pd5_stateRegion F S w B (s.1, permuteLists σ s.2.1, s.2.2) := by
  rcases hs with ⟨hvalid, hsize, hpos⟩
  refine ⟨pd5_memValid_activePermute F S s hvalid σ, ?_, hpos⟩
  simpa [pd5_memSize_activePermute] using hsize

private theorem pd5_activeAverage_delta_weighted_sum_eq {K : ℕ}
    (S : PDScale) (T : Finset (MemPoint S.x K)) (s : MemPoint S.x K)
    (hT : ∀ r ∈ T, ∀ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      (r.1, permuteLists σ r.2.1, r.2.2) ∈ T)
    (hs : s ∈ T) (v : ℝ) :
    (∑ t ∈ T,
      pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0) s *
        v ^ memSize t) = v ^ memSize s := by
  classical
  let G := Fin K → Equiv.Perm (Fin (slotCount S.x))
  let d := permCount S.x K
  have hd : 0 < d := by
    dsimp [d, permCount]
    exact Fintype.card_pos
  have hinner (σ : G) :
      (∑ t ∈ T,
        (if (s.1, permuteLists σ s.2.1, s.2.2) = t then (1 : ℝ) else 0) *
          v ^ memSize t) = v ^ memSize s := by
    let sσ := (s.1, permuteLists σ s.2.1, s.2.2)
    have hsσ : sσ ∈ T := hT s hs σ
    have hsize : memSize sσ = memSize s := by
      simp [sσ, memSize]
    rw [Finset.sum_eq_single sσ]
    · simp [sσ, hsize]
    · intro t ht hne
      simp [sσ, Ne.symm hne]
    · intro hnot
      exact (hnot hsσ).elim
  calc
    _ = ∑ t ∈ T, ∑ σ : G,
          (d : ℝ)⁻¹ *
            ((if (s.1, permuteLists σ s.2.1, s.2.2) = t then (1 : ℝ) else 0) *
              v ^ memSize t) := by
          apply Finset.sum_congr rfl
          intro t ht
          dsimp [pd5_activeAverage, G, d]
          calc
            ((↑(permCount S.x K))⁻¹ *
                ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                  (if (s.1, permuteLists σ s.2.1, s.2.2) = t then (1 : ℝ) else 0)) *
                v ^ memSize t =
              (↑(permCount S.x K))⁻¹ *
                ((∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                    if (s.1, permuteLists σ s.2.1, s.2.2) = t then (1 : ℝ) else 0) *
                  v ^ memSize t) := by ring
            _ = (↑(permCount S.x K))⁻¹ *
                  ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                    (if (s.1, permuteLists σ s.2.1, s.2.2) = t then (1 : ℝ) else 0) *
                      v ^ memSize t := by rw [Finset.sum_mul]
            _ = ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                  (↑(permCount S.x K))⁻¹ *
                    ((if (s.1, permuteLists σ s.2.1, s.2.2) = t then (1 : ℝ) else 0) *
                      v ^ memSize t) := by rw [Finset.mul_sum]
    _ = ∑ σ : G, ∑ t ∈ T,
          (d : ℝ)⁻¹ *
            ((if (s.1, permuteLists σ s.2.1, s.2.2) = t then (1 : ℝ) else 0) *
              v ^ memSize t) := by
          rw [Finset.sum_comm]
    _ = ∑ σ : G, (d : ℝ)⁻¹ * v ^ memSize s := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [← Finset.mul_sum, hinner]
    _ = (d : ℝ)⁻¹ * ∑ σ : G, v ^ memSize s := by
          symm
          rw [Finset.mul_sum]
    _ = v ^ memSize s := by
          simp [d, permCount, G]

private theorem pd5_edge_piece_partition_sum {K : ℕ} (St₀ Pr₀ : Finset (Fin K))
    (A : Prop) [Decidable A] (z : ℂ) :
    (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      if St₀ = St ∧ Pr₀ = Pr ∧ A then z else 0) = if A then z else 0 := by
  by_cases hA : A
  · simp only [hA, and_true]
    rw [Finset.sum_eq_single St₀]
    · rw [Finset.sum_eq_single Pr₀]
      · simp
      · intro Pr hPr hne
        have hEq : ¬ Pr₀ = Pr := fun h => hne h.symm
        simp [hEq]
      · intro hnot
        exact (hnot (Finset.mem_univ Pr₀)).elim
    · intro St hSt hne
      have hEq : ¬ St₀ = St := fun h => hne h.symm
      simp [hEq]
    · intro hnot
      exact (hnot (Finset.mem_univ St₀)).elim
  · simp [hA]

private def pd5_edgeChoiceCoeff {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) : ℂ :=
  ((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
      (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
        ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s c i)
          z') : ℝ) : ℂ)

private theorem pd5_edge_partition_choice_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) (raw : Bool) (s : MemPoint S.x K)
    (Z : Finset (ℤ × ℤ)) (g : LogPoint S.x K → ℂ) :
    (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
        ∑ z' ∈ Z,
          if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
              EdgeAdmissible F S w s c z' then
            pd5_edgeChoiceCoeff F S ρ s c z' *
              edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1
                (edgeTargetLists F S s c) s.1 z' *
              g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                edgeBirths F S j s c)
          else 0) =
      ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
        ∑ z' ∈ Z,
          if EdgeAdmissible F S w s c z' then
            pd5_edgeChoiceCoeff F S ρ s c z' *
              edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1
                (edgeTargetLists F S s c) s.1 z' *
              g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                edgeBirths F S j s c)
          else 0 := by
  classical
  calc
    _ = ∑ St : Finset (Fin K), ∑ c : (i : Fin K) → EdgeChoice S.x F.a
          (s.2.2 i) i, ∑ Pr : Finset (Fin K), ∑ z' ∈ Z,
            if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
                EdgeAdmissible F S w s c z' then
              pd5_edgeChoiceCoeff F S ρ s c z' *
                edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1
                  (edgeTargetLists F S s c) s.1 z' *
                g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                  edgeBirths F S j s c)
            else 0 := by
          apply Finset.sum_congr rfl
          intro St hSt
          rw [Finset.sum_comm]
    _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K), ∑ z' ∈ Z,
            if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
                EdgeAdmissible F S w s c z' then
              pd5_edgeChoiceCoeff F S ρ s c z' *
                edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1
                  (edgeTargetLists F S s c) s.1 z' *
                g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                  edgeBirths F S j s c)
            else 0 := by rw [Finset.sum_comm]
    _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ St : Finset (Fin K), ∑ z' ∈ Z, ∑ Pr : Finset (Fin K),
            if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
                EdgeAdmissible F S w s c z' then
              pd5_edgeChoiceCoeff F S ρ s c z' *
                edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1
                  (edgeTargetLists F S s c) s.1 z' *
                g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                  edgeBirths F S j s c)
            else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro St hSt
          rw [Finset.sum_comm]
    _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ z' ∈ Z, ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
            if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
                EdgeAdmissible F S w s c z' then
              pd5_edgeChoiceCoeff F S ρ s c z' *
                edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1
                  (edgeTargetLists F S s c) s.1 z' *
                g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                  edgeBirths F S j s c)
            else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.sum_comm]
    _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ z' ∈ Z,
            if EdgeAdmissible F S w s c z' then
              pd5_edgeChoiceCoeff F S ρ s c z' *
                edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1
                  (edgeTargetLists F S s c) s.1 z' *
                g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                  edgeBirths F S j s c)
            else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro z' hz'
          exact pd5_edge_piece_partition_sum (edgeStoredSet c) (edgePromotedSet c)
            (EdgeAdmissible F S w s c z')
            (pd5_edgeChoiceCoeff F S ρ s c z' *
              edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1
                (edgeTargetLists F S s c) s.1 z' *
              g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                edgeBirths F S j s c))

private theorem pd5_logEdge_full_finite_at {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) (s : MemPoint S.x K)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite)
    (Z : Finset (ℤ × ℤ)) (hZ : Z = hbox.toFinset) (g : LogPoint S.x K → ℂ) :
    (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      (logEdgePiece F S ρ w j true St Pr g (s, []) -
        logEdgePiece F S ρ w j false St Pr g (s, []))) =
      ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
        ∑ z' ∈ Z,
          if EdgeAdmissible F S w s c z' then
            pd5_edgeChoiceCoeff F S ρ s c z' *
              (edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                  (edgeTargetLists F S s c) s.1 z' -
                edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                  (edgeTargetLists F S s c) s.1 z') *
              g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                edgeBirths F S j s c)
          else 0 := by
  classical
  calc
    _ = ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          ((∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
              ∑ z' ∈ Z,
                if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
                    EdgeAdmissible F S w s c z' then
                  pd5_edgeChoiceCoeff F S ρ s c z' *
                    edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                      (edgeTargetLists F S s c) s.1 z' *
                    g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                      edgeBirths F S j s c)
                else 0) -
            (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
              ∑ z' ∈ Z,
                if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
                    EdgeAdmissible F S w s c z' then
                  pd5_edgeChoiceCoeff F S ρ s c z' *
                    edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                      (edgeTargetLists F S s c) s.1 z' *
                    g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                      edgeBirths F S j s c)
                else 0)) := by
          apply Finset.sum_congr rfl
          intro St hSt
          apply Finset.sum_congr rfl
          intro Pr hPr
          rw [pd5_logEdgePiece_finite F S ρ w j true St Pr g (s, []) hbox,
            pd5_logEdgePiece_finite F S ρ w j false St Pr g (s, []) hbox]
          rw [← hZ]
          simp [pd5_edgeChoiceCoeff, pd5_edgeChoiceMass]
    _ = (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
            ∑ z' ∈ Z,
              if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
                  EdgeAdmissible F S w s c z' then
                pd5_edgeChoiceCoeff F S ρ s c z' *
                  edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                    (edgeTargetLists F S s c) s.1 z' *
                  g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                    edgeBirths F S j s c)
              else 0) -
        (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
            ∑ z' ∈ Z,
              if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
                  EdgeAdmissible F S w s c z' then
                pd5_edgeChoiceCoeff F S ρ s c z' *
                  edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                    (edgeTargetLists F S s c) s.1 z' *
                  g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                    edgeBirths F S j s c)
              else 0) := by
          simp_rw [Finset.sum_sub_distrib]
    _ = (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ z' ∈ Z,
            if EdgeAdmissible F S w s c z' then
              pd5_edgeChoiceCoeff F S ρ s c z' *
                edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                  (edgeTargetLists F S s c) s.1 z' *
                g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                  edgeBirths F S j s c)
            else 0) -
        (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ z' ∈ Z,
            if EdgeAdmissible F S w s c z' then
              pd5_edgeChoiceCoeff F S ρ s c z' *
                edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                  (edgeTargetLists F S s c) s.1 z' *
                g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                  edgeBirths F S j s c)
            else 0) := by
          rw [pd5_edge_partition_choice_sum F S ρ w j true s Z g,
            pd5_edge_partition_choice_sum F S ρ w j false s Z g]
    _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ z' ∈ Z,
            (if EdgeAdmissible F S w s c z' then
              pd5_edgeChoiceCoeff F S ρ s c z' *
                (edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                    (edgeTargetLists F S s c) s.1 z' -
                  edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                    (edgeTargetLists F S s c) s.1 z') *
                g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                  edgeBirths F S j s c)
            else 0) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro c hc
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro z' hz'
          by_cases ha : EdgeAdmissible F S w s c z' <;>
            simp [ha] <;> ring

private theorem pd5_logEdge_full_finite_expansion {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (j : ℕ)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite)
    (f : LogPoint S.x K → ℂ) (s : MemPoint S.x K) :
    logEdge F S ρ w EdgeKind.full j f (s, []) =
      ((permCount S.x K : ℂ))⁻¹ *
        ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ c : (i : Fin K) → EdgeChoice S.x F.a
            ((s.1, permuteLists σ s.2.1, s.2.2).2.2 i) i,
            ∑ z' ∈ hbox.toFinset,
              if EdgeAdmissible F S w (s.1, permuteLists σ s.2.1, s.2.2) c z' then
                pd5_edgeChoiceCoeff F S ρ (s.1, permuteLists σ s.2.1, s.2.2) c z' *
                  (edgeMultiplier F S (decide (j % 2 = 0)) true
                      (s.1, permuteLists σ s.2.1, s.2.2).2.1
                      (edgeTargetLists F S (s.1, permuteLists σ s.2.1, s.2.2) c) s.1 z' -
                    edgeMultiplier F S (decide (j % 2 = 0)) false
                      (s.1, permuteLists σ s.2.1, s.2.2).2.1
                      (edgeTargetLists F S (s.1, permuteLists σ s.2.1, s.2.2) c) s.1 z') *
                  (logSym F S f)
                    ((z', edgeTargetLists F S (s.1, permuteLists σ s.2.1, s.2.2) c,
                      edgeNewMemory F S (s.1, permuteLists σ s.2.1, s.2.2) c),
                      edgeBirths F S j (s.1, permuteLists σ s.2.1, s.2.2) c)
              else 0 := by
  classical
  unfold logEdge
  simp only [EdgeKind.full, logSym]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  exact pd5_logEdge_full_finite_at F S ρ w j
    (s.1, permuteLists σ s.2.1, s.2.2) hbox hbox.toFinset rfl (logSym F S f)

private theorem pd5_logSym_twist_delta_norm_le {K : ℕ} (F : PDFix K)
    (S : PDScale) (W : BirthLog K → ℂ) (t : MemPoint S.x K)
    (hW : ∀ log, ‖W log‖ ≤ 1) (sL : LogPoint S.x K) :
    ‖logSym F S (fun uL => W uL.2 * (if uL.1 = t then (1 : ℂ) else 0)) sL‖ ≤
      pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0) sL.1 := by
  classical
  let d := permCount S.x K
  have hd : 0 < d := by
    dsimp [d, permCount]
    exact Fintype.card_pos
  have hInv : ‖(d : ℂ)⁻¹‖ = (d : ℝ)⁻¹ := by
    rw [norm_inv, norm_natCast]
  have hterm (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      ‖W sL.2 *
        (if (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) = t then (1 : ℂ) else 0)‖ ≤
        if (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) = t then (1 : ℝ) else 0 := by
    by_cases h : (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) = t <;>
      simp [h, hW]
  unfold logSym
  calc
    _ = ‖(d : ℂ)⁻¹‖ *
          ‖∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            W sL.2 *
              (if (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) = t then
                (1 : ℂ) else 0)‖ := norm_mul _ _
    _ ≤ (d : ℝ)⁻¹ *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            if (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) = t then
              (1 : ℝ) else 0 := by
          rw [hInv]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            ‖∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                W sL.2 *
                  (if (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) = t then
                    (1 : ℂ) else 0)‖ ≤
              ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                ‖W sL.2 *
                  (if (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) = t then
                    (1 : ℂ) else 0)‖ := norm_sum_le _ _
            _ ≤ ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                  if (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) = t then
                    (1 : ℝ) else 0 := Finset.sum_le_sum fun σ hσ => hterm σ
    _ = pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0) sL.1 := by
          simp [pd5_activeAverage, d]

private theorem pd5_logSym_twist_delta_zero_of_size_gt {K : ℕ} (F : PDFix K)
    (S : PDScale) (W : BirthLog K → ℂ) (t : MemPoint S.x K)
    (B : ℕ) (ht : memSize t ≤ B) (sL : LogPoint S.x K)
    (hs : B < memSize sL.1) :
    logSym F S (fun uL => W uL.2 * (if uL.1 = t then (1 : ℂ) else 0)) sL = 0 := by
  classical
  have hne (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) ≠ t := by
    intro hEq
    have hsze : memSize sL.1 = memSize t := by
      calc
        memSize sL.1 = memSize (sL.1.1, permuteLists σ sL.1.2.1, sL.1.2.2) :=
          (pd5_memSize_activePermute sL.1 σ).symm
        _ = memSize t := by rw [hEq]
    omega
  unfold logSym
  simp [hne]

private theorem pd5_edgeBirthTwist_zero_of_source_not_box {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (j : ℕ)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) (W : BirthLog K → ℂ)
    (f : MemPoint S.x K → ℂ) (s : MemPoint S.x K)
    (hnot : ¬ envBox S w s.1) :
    pd5_edgeBirthTwist F S ρ w j W (memorySym f) s = 0 := by
  classical
  change logEdge F S ρ w EdgeKind.full j
      (fun uL => W uL.2 * memorySym f uL.1) (s, []) = 0
  rw [pd5_logEdge_full_finite_expansion F S ρ w j hbox
    (fun uL => W uL.2 * memorySym f uL.1) s]
  simp [EdgeAdmissible, hnot]

private theorem pd5_edge_finite_kernel_inner_le {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (j B : ℕ) (Z : Finset (ℤ × ℤ))
    (W : BirthLog K → ℂ) (hW : ∀ log, ‖W log‖ ≤ 1)
    (t s : MemPoint S.x K) (ht : memSize t ≤ B) :
    ‖∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
        ∑ z' ∈ Z,
          if EdgeAdmissible F S w s c z' then
            pd5_edgeChoiceCoeff F S ρ s c z' *
              (edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                  (edgeTargetLists F S s c) s.1 z' -
                edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                  (edgeTargetLists F S s c) s.1 z') *
              logSym F S (fun uL => W uL.2 * (if uL.1 = t then (1 : ℂ) else 0))
                ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                  edgeBirths F S j s c)
          else 0‖ ≤
      ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
        ∑ z' ∈ Z,
          if EdgeAdmissible F S w s c z' ∧
              memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ B then
            |ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
              (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
                ρ ^ (∑ i : Fin K,
                  hitCount (edgeNewMemory F S s c i) z')| *
              (‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                  (edgeTargetLists F S s c) s.1 z'‖ +
                ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                  (edgeTargetLists F S s c) s.1 z'‖) *
              pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
                (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
          else 0 := by
  classical
  let kTerm (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
      (z' : ℤ × ℤ) : ℂ :=
    if EdgeAdmissible F S w s c z' then
      pd5_edgeChoiceCoeff F S ρ s c z' *
        (edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
            (edgeTargetLists F S s c) s.1 z' -
          edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
            (edgeTargetLists F S s c) s.1 z') *
        logSym F S (fun uL => W uL.2 * (if uL.1 = t then (1 : ℂ) else 0))
          ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
            edgeBirths F S j s c)
    else 0
  let pTerm (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
      (z' : ℤ × ℤ) : ℝ :=
    if EdgeAdmissible F S w s c z' ∧
        memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ B then
      |ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
        (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
          ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s c i) z')| *
        (‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
            (edgeTargetLists F S s c) s.1 z'‖ +
          ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
            (edgeTargetLists F S s c) s.1 z'‖) *
        pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
          (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
    else 0
  change ‖∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      ∑ z' ∈ Z, kTerm c z'‖ ≤
    ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      ∑ z' ∈ Z, pTerm c z'
  calc
    _ ≤ ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ‖∑ z' ∈ Z, kTerm c z'‖ := norm_sum_le _ _
    _ ≤ ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ z' ∈ Z, ‖kTerm c z'‖ := by
          apply Finset.sum_le_sum
          intro c hc
          exact norm_sum_le _ _
    _ ≤ ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ z' ∈ Z, pTerm c z' := by
          apply Finset.sum_le_sum
          intro c hc
          apply Finset.sum_le_sum
          intro z' hz'
          by_cases hAdm : EdgeAdmissible F S w s c z'
          · let out : MemPoint S.x K :=
              (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
            by_cases hsize : memSize out ≤ B
            · have hsym := pd5_logSym_twist_delta_norm_le F S W t hW
                (out, edgeBirths F S j s c)
              have havg : 0 ≤ pd5_activeAverage S
                  (fun u => if u = t then (1 : ℝ) else 0) out := by
                unfold pd5_activeAverage
                apply mul_nonneg
                · positivity
                · apply Finset.sum_nonneg
                  intro σ hσ
                  change 0 ≤ if
                    (out.1, permuteLists σ out.2.1, out.2.2) = t then (1 : ℝ) else 0
                  split_ifs <;> norm_num
              have hcoef : ‖pd5_edgeChoiceCoeff F S ρ s c z'‖ =
                  |ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
                    (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
                      ρ ^ (∑ i : Fin K,
                        hitCount (edgeNewMemory F S s c i) z')| := by
                change ‖((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
                  (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
                    ρ ^ (∑ i : Fin K,
                      hitCount (edgeNewMemory F S s c i) z') : ℝ) : ℂ)‖ = _
                rw [Complex.norm_real]
                rw [Real.norm_eq_abs]
              have hmul :
                  ‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                      (edgeTargetLists F S s c) s.1 z' -
                    edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                      (edgeTargetLists F S s c) s.1 z'‖ ≤
                    ‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                        (edgeTargetLists F S s c) s.1 z'‖ +
                      ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                        (edgeTargetLists F S s c) s.1 z'‖ := norm_sub_le _ _
              have hnonneg : 0 ≤ |ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
                  (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
                    ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s c i) z')| := abs_nonneg _
              have hgeom : 0 ≤ ‖edgeMultiplier F S (decide (j % 2 = 0)) true
                    s.2.1 (edgeTargetLists F S s c) s.1 z'‖ +
                  ‖edgeMultiplier F S (decide (j % 2 = 0)) false
                    s.2.1 (edgeTargetLists F S s c) s.1 z'‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
              have hsizeOut :
                  memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ B := by
                simpa [out] using hsize
              simp only [kTerm, pTerm, if_pos hAdm,
                if_pos (And.intro hAdm hsizeOut)]
              have hmulSym :
                  ‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                      (edgeTargetLists F S s c) s.1 z' -
                    edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                      (edgeTargetLists F S s c) s.1 z'‖ *
                    ‖logSym F S (fun uL => W uL.2 * (if uL.1 = t then (1 : ℂ) else 0))
                      (out, edgeBirths F S j s c)‖ ≤
                  (‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                      (edgeTargetLists F S s c) s.1 z'‖ +
                    ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                      (edgeTargetLists F S s c) s.1 z'‖) *
                    pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0) out := by
                calc
                  _ ≤ (‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                        (edgeTargetLists F S s c) s.1 z'‖ +
                      ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                        (edgeTargetLists F S s c) s.1 z'‖) *
                      ‖logSym F S (fun uL => W uL.2 * (if uL.1 = t then (1 : ℂ) else 0))
                        (out, edgeBirths F S j s c)‖ :=
                    by gcongr
                  _ ≤ _ := by gcongr
              let aCoeff : ℝ := |ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
                (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
                  ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s c i) z')|
              let gGeom : ℝ :=
                ‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                    (edgeTargetLists F S s c) s.1 z'‖ +
                  ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                    (edgeTargetLists F S s c) s.1 z'‖
              let aAvg : ℝ := pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0) out
              have hnorm :
                  ‖pd5_edgeChoiceCoeff F S ρ s c z' *
                    (edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                        (edgeTargetLists F S s c) s.1 z' -
                      edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                        (edgeTargetLists F S s c) s.1 z') *
                    logSym F S (fun uL => W uL.2 *
                      (if uL.1 = t then (1 : ℂ) else 0))
                      (out, edgeBirths F S j s c)‖ =
                  aCoeff *
                    (‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                        (edgeTargetLists F S s c) s.1 z' -
                      edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                        (edgeTargetLists F S s c) s.1 z'‖ *
                      ‖logSym F S (fun uL => W uL.2 *
                        (if uL.1 = t then (1 : ℂ) else 0))
                        (out, edgeBirths F S j s c)‖) := by
                rw [norm_mul, norm_mul, hcoef]
                simp [aCoeff, mul_assoc]
              have hbound :
                  aCoeff *
                    (‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                        (edgeTargetLists F S s c) s.1 z' -
                      edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                        (edgeTargetLists F S s c) s.1 z'‖ *
                      ‖logSym F S (fun uL => W uL.2 *
                        (if uL.1 = t then (1 : ℂ) else 0))
                        (out, edgeBirths F S j s c)‖) ≤
                    |ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
                      (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
                        ρ ^ (∑ i : Fin K,
                          hitCount (edgeNewMemory F S s c i) z')| *
                      (‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                          (edgeTargetLists F S s c) s.1 z'‖ +
                        ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                          (edgeTargetLists F S s c) s.1 z'‖) *
                      pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
                        (z', edgeTargetLists F S s c, edgeNewMemory F S s c) := by
                calc
                  _ ≤ aCoeff * (gGeom * aAvg) :=
                    mul_le_mul_of_nonneg_left hmulSym hnonneg
                  _ = |ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
                        (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
                          ρ ^ (∑ i : Fin K,
                            hitCount (edgeNewMemory F S s c i) z')| *
                      (‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                          (edgeTargetLists F S s c) s.1 z'‖ +
                        ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                          (edgeTargetLists F S s c) s.1 z'‖) *
                      pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
                        (z', edgeTargetLists F S s c, edgeNewMemory F S s c) := by
                        simp [aCoeff, gGeom, aAvg, out]
                        ring
              exact hnorm.le.trans hbound
            · have hsize' : B < memSize out := by omega
              have hzero := pd5_logSym_twist_delta_zero_of_size_gt F S W t B ht
                (out, edgeBirths F S j s c) hsize'
              have hsizeOut :
                  ¬ memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ B := by
                simpa [out] using hsize
              have hnot : ¬ (EdgeAdmissible F S w s c z' ∧
                  memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ B) :=
                fun h => hsizeOut h.2
              change ‖(if EdgeAdmissible F S w s c z' then
                  pd5_edgeChoiceCoeff F S ρ s c z' *
                    (edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                        (edgeTargetLists F S s c) s.1 z' -
                      edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                        (edgeTargetLists F S s c) s.1 z') *
                    logSym F S (fun uL => W uL.2 * (if uL.1 = t then (1 : ℂ) else 0))
                      ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                        edgeBirths F S j s c)
                else 0)‖ ≤
                if EdgeAdmissible F S w s c z' ∧
                    memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ B then
                  |ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
                    (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
                      ρ ^ (∑ i : Fin K,
                        hitCount (edgeNewMemory F S s c i) z')| *
                    (‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                        (edgeTargetLists F S s c) s.1 z'‖ +
                      ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                        (edgeTargetLists F S s c) s.1 z'‖) *
                    pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
                      (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
                else 0
              have hzero' :
                  logSym F S (fun uL => if uL.1 = t then W uL.2 else 0)
                    (out, edgeBirths F S j s c) = 0 := by
                simpa [mul_ite] using hzero
              simp [hAdm, hsizeOut]
              have hzero'' :
                  logSym F S (fun uL => if uL.1 = t then W uL.2 else 0)
                    ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                      edgeBirths F S j s c) = 0 := by
                simpa [out] using hzero'
              rw [hzero'']
              simp
          · change ‖(if EdgeAdmissible F S w s c z' then
                pd5_edgeChoiceCoeff F S ρ s c z' *
                  (edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                      (edgeTargetLists F S s c) s.1 z' -
                    edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                      (edgeTargetLists F S s c) s.1 z') *
                  logSym F S (fun uL => W uL.2 * (if uL.1 = t then (1 : ℂ) else 0))
                    ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                      edgeBirths F S j s c)
              else 0)‖ ≤
                if EdgeAdmissible F S w s c z' ∧
                    memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ B then
                  |ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
                    (∏ i : Fin K, pd5_edgeChoiceMass F S s c i) *
                      ρ ^ (∑ i : Fin K,
                        hitCount (edgeNewMemory F S s c i) z')| *
                    (‖edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1
                        (edgeTargetLists F S s c) s.1 z'‖ +
                      ‖edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1
                        (edgeTargetLists F S s c) s.1 z'‖) *
                    pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
                      (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
                else 0
            simp [hAdm]

private theorem pd5_edgeKernel_delta_bound {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (j B : ℕ)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite)
    (W : BirthLog K → ℂ) (hW : ∀ log, ‖W log‖ ≤ 1)
    (s t : MemPoint S.x K) (hs : memSize s ≤ B) (ht : memSize t ≤ B) :
    ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s t‖ ≤
      pd5_edgeAbsChoice F S ρ w j B hbox.toFinset (fun _ => 1)
        (fun u => if u = t then 1 else 0) s := by
  classical
  let src (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) : MemPoint S.x K :=
    (s.1, permuteLists σ s.2.1, s.2.2)
  let kTerm (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) : ℂ :=
    ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      ∑ z' ∈ hbox.toFinset,
        if EdgeAdmissible F S w (src σ) c z' then
          pd5_edgeChoiceCoeff F S ρ (src σ) c z' *
            (edgeMultiplier F S (decide (j % 2 = 0)) true (src σ).2.1
                (edgeTargetLists F S (src σ) c) (src σ).1 z' -
              edgeMultiplier F S (decide (j % 2 = 0)) false (src σ).2.1
                (edgeTargetLists F S (src σ) c) (src σ).1 z') *
            logSym F S (fun uL => W uL.2 * (if uL.1 = t then (1 : ℂ) else 0))
              ((z', edgeTargetLists F S (src σ) c, edgeNewMemory F S (src σ) c),
                edgeBirths F S j (src σ) c)
        else 0
  have hInv : ‖(permCount S.x K : ℂ)⁻¹‖ = (permCount S.x K : ℝ)⁻¹ := by
    rw [norm_inv, norm_natCast]
  change ‖logEdge F S ρ w EdgeKind.full j
      (fun uL => W uL.2 * (if uL.1 = t then (1 : ℂ) else 0)) (s, [])‖ ≤ _
  rw [pd5_logEdge_full_finite_expansion F S ρ w j hbox
    (fun uL => W uL.2 * (if uL.1 = t then (1 : ℂ) else 0)) s]
  change ‖(permCount S.x K : ℂ)⁻¹ *
      ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), kTerm σ‖ ≤ _
  calc
    _ = (permCount S.x K : ℝ)⁻¹ *
          ‖∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), kTerm σ‖ := by
          rw [norm_mul, hInv]
    _ ≤ (permCount S.x K : ℝ)⁻¹ *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), ‖kTerm σ‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (permCount S.x K : ℝ)⁻¹ *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
              ∑ z' ∈ hbox.toFinset,
                if EdgeAdmissible F S w (src σ) c z' ∧
                    memSize (z', edgeTargetLists F S (src σ) c,
                      edgeNewMemory F S (src σ) c) ≤ B then
                  |ρ ^ (∑ i : Fin K, hitCount ((src σ).2.2 i) (src σ).1) *
                    (∏ i : Fin K, pd5_edgeChoiceMass F S (src σ) c i) *
                      ρ ^ (∑ i : Fin K,
                        hitCount (edgeNewMemory F S (src σ) c i) z')| *
                    (‖edgeMultiplier F S (decide (j % 2 = 0)) true (src σ).2.1
                        (edgeTargetLists F S (src σ) c) (src σ).1 z'‖ +
                      ‖edgeMultiplier F S (decide (j % 2 = 0)) false (src σ).2.1
                        (edgeTargetLists F S (src σ) c) (src σ).1 z'‖) *
                    pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
                      (z', edgeTargetLists F S (src σ) c,
                        edgeNewMemory F S (src σ) c)
                else 0) := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro σ hσ
            exact pd5_edge_finite_kernel_inner_le F S ρ w j B hbox.toFinset W hW t
              (src σ) ht
          · positivity
    _ = pd5_edgeAbsChoice F S ρ w j B hbox.toFinset (fun _ => 1)
          (fun u => if u = t then 1 else 0) s := by
          simp [pd5_edgeAbsChoice, pd5_activeAverage, src, kTerm, hs]

private theorem pd5_get_append_singleton {α : Type*} (l : List α) (a : α) :
    (l ++ [a]).get ⟨l.length, by simp⟩ = a := by
  rw [List.get_eq_getElem]
  rw [List.getElem_append_right (as := l) (bs := [a])
    (i := l.length) (Nat.le_refl _)]
  simp

private theorem pd5_get_append_last_cast {α : Type*} (l : List α) (a : α)
    (hlen : l.length + 1 = (l ++ [a]).length) :
    (l ++ [a]).get (Fin.cast hlen (Fin.last l.length)) = a := by
  rw [List.get_eq_getElem]
  have hval : (Fin.cast hlen (Fin.last l.length)).val = l.length := by
    simp [Fin.cast, Fin.last]
  simp [hval, List.getElem_append_right]

private theorem pd5_list_get_eq_of_eq {α : Type*} {l₁ l₂ : List α}
    (h : l₁ = l₂) (i : Fin l₁.length) :
    l₁.get i = l₂.get (Fin.cast (congrArg List.length h) i) := by
  cases h
  rfl

private def pd5_edgeRemovedIndices {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
    Finset (Fin (s.2.2 i).length) :=
  match (c i).2 with
  | Sum.inl k => {k}
  | Sum.inr _ => ∅

private def pd5_edgeReverseChoice {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
    EdgeChoice S.x F.a (edgeNewMemory F S s c i) i :=
  ((c i).2.isLeft,
    if hstore : (c i).1 then
      let pre := removeIndices (s.2.2 i) (pd5_edgeRemovedIndices F S s c i)
      let hlen : pre.length + 1 = (edgeNewMemory F S s c i).length := by
        simp [pre, edgeNewMemory, pd5_edgeRemovedIndices, hstore] <;> rfl
      Sum.inl (Fin.cast hlen (Fin.last pre.length))
    else
      Sum.inr ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩)

private theorem pd5_edgeNewMemory_inl {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K)
    (stored : Bool) (k : Fin (s.2.2 i).length)
    (hchoice : c i = (stored, Sum.inl k)) :
    edgeNewMemory F S s c i = removeIndices (s.2.2 i) {k} ++
      (if stored then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else []) := by
  rw [edgeNewMemory, hchoice]

private theorem pd5_removeIndices_empty (l : List Particle) :
    removeIndices l ∅ = l := by
  simp [removeIndices]

private theorem pd5_edgeNewMemory_inr {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K)
    (stored : Bool) (p : {p : ℕ // p ∈ primeBand S.x (F.a i)})
    (hchoice : c i = (stored, Sum.inr p)) :
    edgeNewMemory F S s c i = s.2.2 i ++
      (if stored then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else []) := by
  rw [edgeNewMemory, hchoice]
  simp [pd5_removeIndices_empty]

private def pd5_selectIndices (l : List Particle) (D : Finset (Fin l.length)) :
    List Particle :=
  (List.finRange l.length).filterMap fun k => if k ∈ D then some (l.get k) else none

private theorem pd5_filterMap_complement_perm {α β : Type*} (l : List α)
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

private theorem pd5_remove_select_perm (l : List Particle)
    (D : Finset (Fin l.length)) :
    List.Perm (removeIndices l D ++ pd5_selectIndices l D) l := by
  classical
  unfold removeIndices pd5_selectIndices
  simpa [List.map_get_finRange] using
    (pd5_filterMap_complement_perm (List.finRange l.length) (fun k => k ∈ D)
      (fun k => l.get k))

private theorem pd5_select_singleton (l : List Particle) (k : Fin l.length) :
    pd5_selectIndices l {k} = [l.get k] := by
  induction l with
  | nil => exact Fin.elim0 k
  | cons a l ih =>
      refine Fin.cases ?_ ?_ k
      · simp [pd5_selectIndices, List.finRange]
      · intro j
        unfold pd5_selectIndices
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
        change pd5_selectIndices l {j} = [l.get j]
        exact ih j

private theorem pd5_remove_singleton_append_perm (l : List Particle) (k : Fin l.length) :
    List.Perm (removeIndices l {k} ++ [l.get k]) l := by
  rw [← pd5_select_singleton l k]
  exact pd5_remove_select_perm l {k}

private theorem pd5_remove_append_last_perm (l : List Particle) (a : Particle) :
    List.Perm (removeIndices (l ++ [a]) {⟨l.length, by simp⟩}) l := by
  let k : Fin (l ++ [a]).length := ⟨l.length, by simp⟩
  have hp := pd5_remove_singleton_append_perm (l ++ [a]) k
  have hget : (l ++ [a]).get k = a := by
    simpa [k] using pd5_get_append_singleton l a
  rw [hget] at hp
  apply List.perm_iff_count.mpr
  intro e
  have hc := (List.perm_iff_count.mp hp) e
  simp only [List.count_append, List.count_singleton] at hc
  exact Nat.add_right_cancel hc

private theorem pd5_remove_last_perm_of_eq {m l : List Particle} (a : Particle)
    (hm : m = l ++ [a]) (k : Fin m.length)
    (hk : k = Fin.cast (congrArg List.length hm).symm ⟨l.length, by simp⟩) :
    List.Perm (removeIndices m {k}) l := by
  cases hm
  have hk' : k = ⟨l.length, by simp⟩ := by simpa using hk
  rw [hk']
  exact pd5_remove_append_last_perm l a

private def pd5_activeNuGroup {K : ℕ} (F : PDFix K) (S : PDScale)
    (p : PrimeLists S.x K) (i : Fin K) : ℝ :=
  ∏ j : Fin (slotCount S.x), memoryNu S.x K F.a F.q_d i (p i j)

private theorem pd5_activeNuGroup_edge {K : ℕ} (F : PDFix K) (S : PDScale)
    (p q : PrimeLists S.x K) (i : Fin K)
    (hshared : ∀ j : Fin (slotCount S.x), j.val < momentJ S.x → p i j = q i j) :
    pd5_activeNuGroup F S p i *
        memoryNu S.x K F.a F.q_d i (q i (lastSlot S.x)) =
      pd5_activeNuGroup F S q i *
        memoryNu S.x K F.a F.q_d i (p i (lastSlot S.x)) := by
  classical
  let E : Finset (Fin (slotCount S.x)) :=
    Finset.univ.erase (lastSlot S.x)
  have hlast : lastSlot S.x ∈ (Finset.univ : Finset (Fin (slotCount S.x))) :=
    Finset.mem_univ _
  have hsplitP : pd5_activeNuGroup F S p i =
      (∏ j ∈ E, memoryNu S.x K F.a F.q_d i (p i j)) *
        memoryNu S.x K F.a F.q_d i (p i (lastSlot S.x)) := by
    dsimp [pd5_activeNuGroup, E]
    rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin (slotCount S.x)))
      (fun j => memoryNu S.x K F.a F.q_d i (p i j)) hlast]
  have hsplitQ : pd5_activeNuGroup F S q i =
      (∏ j ∈ E, memoryNu S.x K F.a F.q_d i (q i j)) *
        memoryNu S.x K F.a F.q_d i (q i (lastSlot S.x)) := by
    dsimp [pd5_activeNuGroup, E]
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

private def pd5_memoryNuListProd {K : ℕ} (F : PDFix K) (S : PDScale)
    (i : Fin K) (l : List Particle) : ℝ :=
  (l.map fun e => memoryNu S.x K F.a F.q_d i e.1).prod

private def pd5_memoryNuListMass {K : ℕ} (F : PDFix K) (S : PDScale)
    (i : Fin K) (l : List Particle) : ℝ :=
  pd5_memoryNuListProd F S i l / (l.length.factorial : ℝ)

private theorem pd5_memoryNuListProd_perm {K : ℕ} (F : PDFix K) (S : PDScale)
    (i : Fin K) (l₁ l₂ : List Particle) (h : List.Perm l₁ l₂) :
    pd5_memoryNuListProd F S i l₁ = pd5_memoryNuListProd F S i l₂ := by
  unfold pd5_memoryNuListProd
  exact (h.map fun e => memoryNu S.x K F.a F.q_d i e.1).prod_eq

private def pd5_memGroupWeight {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (i : Fin K) : ℝ :=
  pd5_activeNuGroup F S s.2.1 i * pd5_memoryNuListMass F S i (s.2.2 i)

private theorem pd5_memMeasure_eq_groupProd {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s) :
    memMeasure F S s = ∏ i : Fin K, pd5_memGroupWeight F S s i := by
  simp [memMeasure, hs, pd5_memGroupWeight, pd5_activeNuGroup,
    pd5_memoryNuListMass, pd5_memoryNuListProd, Finset.prod_mul_distrib]

private theorem pd5_active_balance_algebra (A At νsrc νt P den C r : ℝ)
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

private theorem pd5_edgeChoiceMass_inl {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (i : Fin K) (k : Fin (s.2.2 i).length) (stored : Bool)
    (hchoice : c i = (stored, Sum.inl k)) :
    pd5_edgeChoiceMass F S s c i = (bandMass S.x (F.a i))⁻¹ := by
  simp [pd5_edgeChoiceMass, hchoice]

private theorem pd5_edgeChoiceMass_inr {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (i : Fin K) (p : {p : ℕ // p ∈ primeBand S.x (F.a i)}) (stored : Bool)
    (hchoice : c i = (stored, Sum.inr p)) :
    pd5_edgeChoiceMass F S s c i = memoryNu S.x K F.a F.q_d i p := by
  simp [pd5_edgeChoiceMass, hchoice]

private theorem pd5_edgeGroupWeight_fresh_noStore {K : ℕ} (F : PDFix K)
    (S : PDScale) (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (z' : ℤ × ℤ) (i : Fin K) (p : {p : ℕ // p ∈ primeBand S.x (F.a i)})
    (hchoice : c i = (false, Sum.inr p))
    (hVlow : Real.log 2 / 2 ≤ bandMass S.x (F.a i))
    (hVhigh : bandMass S.x (F.a i) ≤ 2 * Real.log 2)
    (hbase : 0 ≤ pd5_memGroupWeight F S
      (z', edgeTargetLists F S s c, edgeNewMemory F S s c) i *
        pd5_edgeChoiceMass F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
          (pd5_edgeReverseChoice F S s hs c) i) :
    pd5_memGroupWeight F S s i * pd5_edgeChoiceMass F S s c i ≤
      (1 + 2 / Real.log 2 + 2 * Real.log 2) *
        ((s.2.2 i).length + 1 : ℕ) *
        pd5_memGroupWeight F S
          (z', edgeTargetLists F S s c, edgeNewMemory F S s c) i *
          pd5_edgeChoiceMass F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
            (pd5_edgeReverseChoice F S s hs c) i := by
  classical
  let t : MemPoint S.x K :=
    (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
  let rc := pd5_edgeReverseChoice F S s hs c
  let A := pd5_activeNuGroup F S s.2.1 i
  let At := pd5_activeNuGroup F S t.2.1 i
  let l := s.2.2 i
  let P := pd5_memoryNuListProd F S i l
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
  have hactiveRaw := pd5_activeNuGroup_edge F S s.2.1 t.2.1 i hshared
  have hactive : A * νt = At * νs := by
    simpa [A, At, νs, νt, t, hlast, edgeTargetLists] using hactiveRaw
  have htargetLast : edgeTargetLists F S s c i (lastSlot S.x) = edgeNewLabel (c i) := by
    simp [edgeTargetLists, hlast]
  have hmem : t.2.2 i = l := by
    simp [t, edgeNewMemory, hchoice, l, pd5_removeIndices_empty]
  have hgroupS : pd5_memGroupWeight F S s i = A * (P / den) := by
    simp [pd5_memGroupWeight, pd5_memoryNuListMass, A, P, den, l]
  have hgroupT : pd5_memGroupWeight F S t i = At * (P / den) := by
    change pd5_activeNuGroup F S t.2.1 i *
      (pd5_memoryNuListProd F S i (t.2.2 i) / ((t.2.2 i).length.factorial : ℝ)) = _
    rw [hmem]
  have hmassS : pd5_edgeChoiceMass F S s c i = νt := by
    have hlabel : edgeNewLabel (c i) = p.1 := by
      simp [edgeNewLabel, hchoice]
    simpa [νt, hlabel] using pd5_edgeChoiceMass_inr F S s c i p false hchoice
  have hrc : rc i =
      (false, Sum.inr ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩) := by
    simp [rc, pd5_edgeReverseChoice, hchoice]
  have hmassT : pd5_edgeChoiceMass F S t rc i = νs := by
    simpa [νs] using pd5_edgeChoiceMass_inr F S t rc i
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
    pd5_active_balance_algebra A At νs νt P den C0 r hactive hbase' hfac

private theorem pd5_edgeReverseChoice_label {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
    edgeNewLabel (pd5_edgeReverseChoice F S s hs c i) = s.2.1 i (lastSlot S.x) := by
  by_cases hb : (c i).1 = true
  · let pre := removeIndices (s.2.2 i) (pd5_edgeRemovedIndices F S s c i)
    have happend : pre.length + 1 = (pre ++ [anchorAt (s.2.1 i (lastSlot S.x)) s.1]).length := by
      simp
    have hget := pd5_get_append_last_cast pre (anchorAt (s.2.1 i (lastSlot S.x)) s.1) happend
    have hlen : pre.length + 1 = (edgeNewMemory F S s c i).length := by
      simp [pre, edgeNewMemory, pd5_edgeRemovedIndices, hb] <;> rfl
    have hnew : edgeNewMemory F S s c i =
        pre ++ [anchorAt (s.2.1 i (lastSlot S.x)) s.1] := by
      simp [pre, edgeNewMemory, pd5_edgeRemovedIndices, hb] <;> rfl
    simp only [pd5_edgeReverseChoice, hb, dite_true, edgeNewLabel]
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
    have hget' := pd5_list_get_eq_of_eq hnew (Fin.cast hlen (Fin.last pre.length))
    rw [hindex] at hget'
    rw [hcast] at hget'
    rw [hget', hget]
    rfl
  · have hb' : (c i).1 = false := Bool.eq_false_of_not_eq_true hb
    simp [pd5_edgeReverseChoice, edgeNewLabel, hb']

private theorem pd5_edgeReverse_targetLists {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) :
    edgeTargetLists F S (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
      (pd5_edgeReverseChoice F S s hs c) = s.2.1 := by
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
    simp [edgeTargetLists, hlast, pd5_edgeReverseChoice_label]

private theorem pd5_removeIndices_mem_of_mem {l : List Particle}
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

private theorem pd5_anchorAt_le_prime (p : ℕ) (z : ℤ × ℤ) :
    (anchorAt p z).2 ≤ p := by
  dsimp [anchorAt]
  exact Nat.le_of_lt_succ (projLine p z).isLt

private theorem pd5_edge_output_valid {K : ℕ} (F : PDFix K) (S : PDScale)
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
  · exact hs.2.2 i e (pd5_removeIndices_mem_of_mem _ hrem)
  · cases hflag : (c i).1 with
    | false => simp [hflag] at hstore
    | true =>
        have heq : e = anchorAt (s.2.1 i (lastSlot S.x)) s.1 := by
          simpa [hflag] using hstore
        rw [heq]
        exact ⟨hs.2.1 i (lastSlot S.x),
          pd5_anchorAt_le_prime (s.2.1 i (lastSlot S.x)) s.1⟩

private theorem pd5_edge_output_region {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (B : ℕ) (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ)
    (hc : EdgeAdmissible F S w s c z')
    (hsize : memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ B) :
    pd5_stateRegion F S w B (z', edgeTargetLists F S s c, edgeNewMemory F S s c) := by
  have hEdge := hc
  rcases hc with ⟨_, _, _, _, _, _, _, hboxTarget, _, _⟩
  exact ⟨pd5_edge_output_valid F S w s hs c z' hEdge, hsize, Or.inr hboxTarget⟩

private theorem pd5_removeIndices_length {l : List Particle}
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

private theorem pd5_memoryNuListProd_append {K : ℕ} (F : PDFix K) (S : PDScale)
    (i : Fin K) (l : List Particle) (a : Particle) :
    pd5_memoryNuListProd F S i (l ++ [a]) =
      pd5_memoryNuListProd F S i l * memoryNu S.x K F.a F.q_d i a.1 := by
  simp [pd5_memoryNuListProd, List.map_append]

private theorem pd5_memoryNuListProd_remove_singleton {K : ℕ} (F : PDFix K)
    (S : PDScale) (i : Fin K) (l : List Particle) (k : Fin l.length) :
    pd5_memoryNuListProd F S i l =
      pd5_memoryNuListProd F S i (removeIndices l {k}) *
        memoryNu S.x K F.a F.q_d i (l.get k).1 := by
  have hp := pd5_remove_singleton_append_perm l k
  have hprod := pd5_memoryNuListProd_perm F S i _ _ hp
  rw [pd5_memoryNuListProd_append] at hprod
  exact hprod.symm

private theorem pd5_remove_singleton_length {l : List Particle} (k : Fin l.length) :
    (removeIndices l {k}).length + 1 = l.length := by
  have hlen := pd5_removeIndices_length (l := l) ({k} : Finset (Fin l.length))
  have hcard : ({k} : Finset (Fin l.length)).card = 1 := by simp
  rw [hcard] at hlen
  have hk : 0 < l.length := Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  omega

private theorem pd5_memoryNuListMass_remove_singleton_le {K : ℕ}
    (F : PDFix K) (S : PDScale) (i : Fin K) (l : List Particle)
    (k : Fin l.length)
    (hP : 0 ≤ pd5_memoryNuListProd F S i (removeIndices l {k}))
    (hν : 0 ≤ memoryNu S.x K F.a F.q_d i (l.get k).1) :
    pd5_memoryNuListMass F S i l ≤
      pd5_memoryNuListMass F S i (removeIndices l {k}) *
        memoryNu S.x K F.a F.q_d i (l.get k).1 := by
  let pre := removeIndices l {k}
  have hprod := pd5_memoryNuListProd_remove_singleton F S i l k
  have hlen : pre.length + 1 = l.length := pd5_remove_singleton_length k
  have hfact : (l.length.factorial : ℝ) =
      (l.length : ℝ) * (pre.length.factorial : ℝ) := by
    rw [← hlen, Nat.factorial_succ]
    simp [Nat.cast_mul]
  have hfactPos : 0 < (pre.length.factorial : ℝ) := by positivity
  have hlenPos : 1 ≤ (l.length : ℝ) := by
    have hpos : 0 < l.length := by omega
    exact_mod_cast (Nat.succ_le_iff.mpr hpos)
  rw [pd5_memoryNuListMass, pd5_memoryNuListMass, hprod, hfact]
  have hnum : 0 ≤ pd5_memoryNuListProd F S i pre *
      memoryNu S.x K F.a F.q_d i (l.get k).1 := mul_nonneg hP hν
  calc
    (pd5_memoryNuListProd F S i pre * memoryNu S.x K F.a F.q_d i (l.get k).1) /
        ((l.length : ℝ) * (pre.length.factorial : ℝ))
        = ((pd5_memoryNuListProd F S i pre * memoryNu S.x K F.a F.q_d i (l.get k).1) /
            (pre.length.factorial : ℝ)) / (l.length : ℝ) := by
              rw [div_div, mul_comm]
    _ ≤ (pd5_memoryNuListProd F S i pre * memoryNu S.x K F.a F.q_d i (l.get k).1) /
          (pre.length.factorial : ℝ) := by
          exact div_le_self (div_nonneg hnum hfactPos.le) hlenPos
    _ = pd5_memoryNuListMass F S i pre *
          memoryNu S.x K F.a F.q_d i (l.get k).1 := by
          unfold pd5_memoryNuListMass
          ring

private theorem pd5_edgeReverse_memory_perm {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ)
    (hhit : ∀ i, ∀ k, (c i).2 = Sum.inl k →
      particleHits ((s.2.2 i).get k) z') :
    ∀ i, List.Perm
      (edgeNewMemory F S
        (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
        (pd5_edgeReverseChoice F S s hs c) i) (s.2.2 i) := by
  intro i
  let t : MemPoint S.x K :=
    (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
  let rc := pd5_edgeReverseChoice F S s hs c
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
          have hremoved : pd5_edgeRemovedIndices F S s c i = {k} := by
            simp [pd5_edgeRemovedIndices, hchoice]
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
            pd5_edgeNewMemory_inl F S s c i stored k hchoice
          cases stored with
          | false =>
              have hrc : rc i =
                  (true, Sum.inr ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩) := by
                simp [rc, pd5_edgeReverseChoice, hchoice]
              have hout := pd5_edgeNewMemory_inr F S t rc i true
                ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩ hrc
              rw [hout]
              simpa [t, hforward, hanchor, pre, old, l] using
                pd5_remove_singleton_append_perm l k
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
                · simp [rc, pd5_edgeReverseChoice, hchoice]
                · change (rc i).2 = Sum.inl kLast
                  simp [rc, pd5_edgeReverseChoice, hchoice, hremoved,
                    pre, kLast, kBase, htMem, Fin.cast, Fin.last]
                  rfl
              have hout := pd5_edgeNewMemory_inl F S t rc i true kLast hrc
              rw [hout]
              have hp : List.Perm (removeIndices (t.2.2 i) {kLast}) pre :=
                pd5_remove_last_perm_of_eq anchorSrc htMem kLast rfl
              have hsource : List.Perm (pre ++ [old]) l := by
                simpa [pre, old, l] using pd5_remove_singleton_append_perm l k
              have hanchorT : anchorAt (t.2.1 i (lastSlot S.x)) t.1 = old := by
                simpa [t] using hanchor
              simpa [hanchorT] using (hp.append_right [old]).trans hsource
      | inr p =>
          let l := s.2.2 i
          have hremoved : pd5_edgeRemovedIndices F S s c i = ∅ := by
            simp [pd5_edgeRemovedIndices, hchoice]
          have hforward : edgeNewMemory F S s c i = l ++
              (if stored then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else []) :=
            pd5_edgeNewMemory_inr F S s c i stored p hchoice
          cases stored with
          | false =>
              have hrc : rc i =
                  (false, Sum.inr ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩) := by
                simp [rc, pd5_edgeReverseChoice, hchoice]
              have hout := pd5_edgeNewMemory_inr F S t rc i false
                ⟨s.2.1 i (lastSlot S.x), hs.2.1 i (lastSlot S.x)⟩ hrc
              rw [hout]
              have he : removeIndices l ∅ = l := pd5_removeIndices_empty l
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
                · simp [rc, pd5_edgeReverseChoice, hchoice]
                · change (rc i).2 = Sum.inl kLast
                  simp [rc, pd5_edgeReverseChoice, hchoice, hremoved,
                    l, kLast, kBase, htMem, Fin.cast, Fin.last,
                    pd5_removeIndices_empty]
              have hout := pd5_edgeNewMemory_inl F S t rc i false kLast hrc
              rw [hout]
              simpa [t] using pd5_remove_last_perm_of_eq anchorSrc htMem kLast rfl

private theorem pd5_edgeNewMemory_length_bounds {K : ℕ} (F : PDFix K)
    (S : PDScale) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
    (edgeNewMemory F S s c i).length ≤ (s.2.2 i).length + 1 ∧
      (s.2.2 i).length ≤ (edgeNewMemory F S s c i).length + 1 := by
  classical
  cases hkind : (c i).2 with
  | inl k =>
      cases hstore : (c i).1 <;>
        simp [edgeNewMemory, hkind, hstore, pd5_removeIndices_length] <;> omega
  | inr p =>
      cases hstore : (c i).1 <;>
        simp [edgeNewMemory, hkind, hstore, pd5_removeIndices_length] <;> omega

private theorem pd5_edgeNewMemory_size_diff_le {K : ℕ} (F : PDFix K)
    (S : PDScale) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :
    memSize (s.1, edgeTargetLists F S s c, edgeNewMemory F S s c) ≤ memSize s + K ∧
      memSize s ≤ memSize (s.1, edgeTargetLists F S s c, edgeNewMemory F S s c) + K := by
  have hlen := fun i => pd5_edgeNewMemory_length_bounds F S s c i
  have h₁ :
      (∑ i : Fin K, (edgeNewMemory F S s c i).length) ≤
        ∑ i : Fin K, ((s.2.2 i).length + 1) :=
    Finset.sum_le_sum fun i hi => (hlen i).1
  have h₂ :
      (∑ i : Fin K, (s.2.2 i).length) ≤
        ∑ i : Fin K, ((edgeNewMemory F S s c i).length + 1) :=
    Finset.sum_le_sum fun i hi => (hlen i).2
  have hsum₁ :
      (∑ i : Fin K, ((s.2.2 i).length + 1)) = memSize s + K := by
    simp [memSize, Finset.sum_add_distrib]
  have hsum₂ :
      (∑ i : Fin K, ((edgeNewMemory F S s c i).length + 1)) =
        memSize (s.1, edgeTargetLists F S s c, edgeNewMemory F S s c) + K := by
    simp [memSize, Finset.sum_add_distrib]
  constructor
  · simpa [memSize] using h₁.trans_eq hsum₁
  · simpa [memSize] using h₂.trans_eq hsum₂

private theorem pd5_natPow_ratio_bound (v v₀ : ℝ) (hv : 0 < v) (hv₀ : 0 < v₀)
    (K m n : ℕ) (hmn : m ≤ n + K) (hnm : n ≤ m + K) :
    v ^ m ≤ (1 + v / v₀ + (v / v₀)⁻¹) ^ K * (v / v₀) ^ n * v₀ ^ m := by
  let r := v / v₀
  let q := 1 + r + r⁻¹
  have hr : 0 < r := div_pos hv hv₀
  have hrInv : 0 < r⁻¹ := inv_pos.mpr hr
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hrq : r ≤ q := by dsimp [q]; linarith
  have hriq : r⁻¹ ≤ q := by dsimp [q]; linarith
  have hvEq : v = v₀ * r := by
    dsimp [r]
    field_simp [hv₀.ne']
  have hratio : r ^ m ≤ q ^ K * r ^ n := by
    by_cases hrge : 1 ≤ r
    · by_cases hmn' : m ≤ n
      · have hpow : r ^ m ≤ r ^ n := by gcongr
        have hD : 1 ≤ q ^ K := one_le_pow₀ hq
        calc
          _ ≤ r ^ n := hpow
          _ ≤ q ^ K * r ^ n := by
            exact le_mul_of_one_le_left (pow_nonneg hr.le _) hD
      · have hnle : n ≤ m := Nat.le_of_not_ge hmn'
        have hdiff : m - n ≤ K := by omega
        have heq : n + (m - n) = m := Nat.add_sub_of_le hnle
        have heqPow : r ^ m = r ^ n * r ^ (m - n) := by
          calc
            r ^ m = r ^ (n + (m - n)) := congrArg (fun d : ℕ => r ^ d) heq.symm
            _ = r ^ n * r ^ (m - n) := by rw [pow_add]
        have hpow : r ^ (m - n) ≤ q ^ K := by
          calc
            _ ≤ q ^ (m - n) := by gcongr
            _ ≤ q ^ K := by gcongr
        calc
          r ^ m = r ^ n * r ^ (m - n) := heqPow
          _ ≤ r ^ n * q ^ K :=
            mul_le_mul_of_nonneg_left hpow (pow_nonneg hr.le _)
          _ = q ^ K * r ^ n := by ring
    · have hrle : r ≤ 1 := le_of_not_ge hrge
      by_cases hnle : n ≤ m
      · have hdiff : m - n ≤ K := by omega
        have heq : n + (m - n) = m := Nat.add_sub_of_le hnle
        have hpow0 : r ^ (m - n) ≤ 1 := pow_le_one₀ hr.le hrle
        have hpow : r ^ m ≤ r ^ n := by
          rw [← heq, pow_add]
          calc
            _ ≤ r ^ n * 1 := mul_le_mul_of_nonneg_left hpow0 (pow_nonneg hr.le _)
            _ = r ^ n := by ring
        have hD : 1 ≤ q ^ K := one_le_pow₀ hq
        calc
          _ ≤ r ^ n := hpow
          _ ≤ q ^ K * r ^ n := by
            exact le_mul_of_one_le_left (pow_nonneg hr.le _) hD
      · have hmle : m ≤ n := Nat.le_of_not_ge hnle
        have hdiff : n - m ≤ K := by omega
        have heq : m + (n - m) = n := Nat.add_sub_of_le hmle
        have heqPow : r ^ n = r ^ m * r ^ (n - m) := by
          calc
            r ^ n = r ^ (m + (n - m)) := congrArg (fun d : ℕ => r ^ d) heq.symm
            _ = r ^ m * r ^ (n - m) := by rw [pow_add]
        have hpow : (r⁻¹) ^ (n - m) ≤ q ^ K := by
          calc
            _ ≤ q ^ (n - m) := by gcongr
            _ ≤ q ^ K := by gcongr
        have hcancel : (r⁻¹) ^ (n - m) * r ^ (n - m) = 1 := by
          rw [← mul_pow]
          simp [hr.ne']
        have hbig : 1 ≤ q ^ K * r ^ (n - m) := by
          calc
            _ = (r⁻¹) ^ (n - m) * r ^ (n - m) := hcancel.symm
            _ ≤ q ^ K * r ^ (n - m) :=
              mul_le_mul_of_nonneg_right hpow (pow_nonneg hr.le _)
        calc
          _ = r ^ m * 1 := by ring
          _ ≤ r ^ m * (q ^ K * r ^ (n - m)) :=
            mul_le_mul_of_nonneg_left hbig (pow_nonneg hr.le _)
          _ = q ^ K * (r ^ m * r ^ (n - m)) := by ring
          _ = q ^ K * r ^ n := by rw [heqPow]
  calc
    v ^ m = (v₀ * r) ^ m := by rw [hvEq]
    _ = v₀ ^ m * r ^ m := mul_pow _ _ _
    _ ≤ v₀ ^ m * (q ^ K * r ^ n) :=
      mul_le_mul_of_nonneg_left hratio (pow_nonneg hv₀.le _)
    _ = q ^ K * r ^ n * v₀ ^ m := by ring

private theorem pd5_absorb_edge_row_constant (L C A₀ : ℝ) (K : ℕ)
    (hL : 1 ≤ L) (hC0 : 0 ≤ C) (hC : C ≤ L ^ 3) :
    C * Real.rpow L (2 * (K : ℝ)) * Real.rpow L (3 * A₀) ≤
      Real.rpow L (4 * (K : ℝ) + 3 * A₀ + 3) := by
  have hLpos : 0 < L := by linarith
  have hFactor : 0 ≤ Real.rpow L (2 * (K : ℝ)) * Real.rpow L (3 * A₀) :=
    mul_nonneg (Real.rpow_nonneg hLpos.le _) (Real.rpow_nonneg hLpos.le _)
  have hExp :
      3 + (2 * (K : ℝ)) + 3 * A₀ ≤ 4 * (K : ℝ) + 3 * A₀ + 3 := by
    have hK : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (Nat.zero_le K)
    have h2K : 2 * (K : ℝ) ≤ 4 * (K : ℝ) := by nlinarith [hK]
    linarith
  calc
    _ = C * (Real.rpow L (2 * (K : ℝ)) * Real.rpow L (3 * A₀)) := by ring
    _ ≤ L ^ 3 * (Real.rpow L (2 * (K : ℝ)) * Real.rpow L (3 * A₀)) :=
      mul_le_mul_of_nonneg_right hC hFactor
    _ = Real.rpow L 3 * Real.rpow L (2 * (K : ℝ)) * Real.rpow L (3 * A₀) := by
      calc
        _ = Real.rpow L 3 *
              (Real.rpow L (2 * (K : ℝ)) * Real.rpow L (3 * A₀)) :=
            congrArg (fun x : ℝ => x *
              (Real.rpow L (2 * (K : ℝ)) * Real.rpow L (3 * A₀)))
                (Real.rpow_natCast L (3 : ℕ)).symm
        _ = _ := by ring
    _ = Real.rpow L (3 + (2 * (K : ℝ)) + 3 * A₀) := by
      calc
        _ = (Real.rpow L 3 * Real.rpow L (2 * (K : ℝ))) *
            Real.rpow L (3 * A₀) := by ring
        _ = Real.rpow L (3 + (2 * (K : ℝ))) * Real.rpow L (3 * A₀) := by
          exact congrArg (fun x : ℝ => x * Real.rpow L (3 * A₀))
            (Real.rpow_add hLpos 3 (2 * (K : ℝ))).symm
        _ = Real.rpow L (3 + (2 * (K : ℝ)) + 3 * A₀) :=
          (Real.rpow_add hLpos (3 + 2 * (K : ℝ)) (3 * A₀)).symm
    _ ≤ Real.rpow L (4 * (K : ℝ) + 3 * A₀ + 3) :=
      Real.rpow_le_rpow_of_exponent_le hL hExp

private def pd5_edgePositiveBase {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j B : ℕ) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) : ℝ :=
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

private theorem pd5_activeAverage_finsetSum {K : ℕ} {α : Type*} [DecidableEq α]
    (S : PDScale)
    (T : Finset α) (a : α → ℝ) (g : α → MemPoint S.x K → ℝ)
    (s : MemPoint S.x K) :
    pd5_activeAverage S (fun r => ∑ t ∈ T, a t * g t r) s =
      ∑ t ∈ T, a t * pd5_activeAverage S (g t) s := by
  classical
  unfold pd5_activeAverage
  calc
    _ = (permCount S.x K : ℝ)⁻¹ *
          ∑ t ∈ T, ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            a t * g t (s.1, permuteLists σ s.2.1, s.2.2) := by
          congr 1
          rw [Finset.sum_comm]
    _ = ∑ t ∈ T, a t *
          ((permCount S.x K : ℝ)⁻¹ *
            ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              g t (s.1, permuteLists σ s.2.1, s.2.2)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          rw [← Finset.mul_sum]
          ring

private theorem pd5_activeAverage_memSize_pow {K : ℕ} (S : PDScale)
    (s : MemPoint S.x K) (v : ℝ) :
    pd5_activeAverage S (fun u => v ^ memSize u) s = v ^ memSize s := by
  classical
  let G := Fin K → Equiv.Perm (Fin (slotCount S.x))
  have hsum :
      (∑ σ : G, v ^ memSize (s.1, permuteLists σ s.2.1, s.2.2)) =
        (Fintype.card G : ℝ) * v ^ memSize s := by
    simp [G, pd5_memSize_activePermute]
  unfold pd5_activeAverage
  change (permCount S.x K : ℝ)⁻¹ *
      ∑ σ : G, v ^ memSize (s.1, permuteLists σ s.2.1, s.2.2) = _
  rw [hsum]
  have hcard : permCount S.x K = Fintype.card G := rfl
  rw [hcard]
  have hcardNe : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  field_simp

private def pd5_edgePositiveRowInner {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j B : ℕ) (Z : Finset (ℤ × ℤ)) (v : ℝ)
    (s : MemPoint S.x K) : ℝ :=
  ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
    ∑ z' ∈ Z,
      pd5_edgePositiveBase F S ρ w j B s c z' *
        v ^ memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c)

private theorem pd5_edgeAbsChoice_pow_eq {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j B : ℕ) (Z : Finset (ℤ × ℤ)) (v : ℝ)
    (s : MemPoint S.x K) :
    pd5_edgeAbsChoice F S ρ w j B Z (fun _ => 1) (fun t => v ^ memSize t) s =
      if memSize s ≤ B then pd5_activeAverage S
        (pd5_edgePositiveRowInner F S ρ w j B Z v) s else 0 := by
  classical
  by_cases hs : memSize s ≤ B
  · rw [pd5_edgeAbsChoice]
    simp only [if_pos hs]
    congr 1
    funext r
    simp [pd5_edgePositiveRowInner, pd5_edgePositiveBase,
      pd5_edgeChoiceMass, pd5_activeAverage_memSize_pow]
  · simp [pd5_edgeAbsChoice, hs]

private theorem pd5_edgePositiveBase_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j B : ℕ) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) :
    0 ≤ pd5_edgePositiveBase F S ρ w j B s c z' := by
  unfold pd5_edgePositiveBase
  split_ifs <;> positivity

private theorem pd5_edgePositiveRowInner_weight_change {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (j B : ℕ) (Z : Finset (ℤ × ℤ))
    (s : MemPoint S.x K) (hs : memSize s ≤ B)
    (v v₀ : ℝ) (hv : 0 < v) (hv₀ : 0 < v₀) :
    pd5_edgePositiveRowInner F S ρ w j B Z v s ≤
      (1 + v / v₀ + (v / v₀)⁻¹) ^ K * (v / v₀) ^ memSize s *
        pd5_edgePositiveRowInner F S ρ w j B Z v₀ s := by
  classical
  let C : ℝ := (1 + v / v₀ + (v / v₀)⁻¹) ^ K * (v / v₀) ^ memSize s
  have hterm (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
      (z' : ℤ × ℤ) :
      pd5_edgePositiveBase F S ρ w j B s c z' *
          v ^ memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c) ≤
        C * (pd5_edgePositiveBase F S ρ w j B s c z' *
          v₀ ^ memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c)) := by
    let out : MemPoint S.x K := (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
    by_cases hbase : EdgeAdmissible F S w s c z' ∧ memSize out ≤ B
    · have hdiff := pd5_edgeNewMemory_size_diff_le F S s c
      have hpow := pd5_natPow_ratio_bound v v₀ hv hv₀ K (memSize out) (memSize s)
        (by simpa [out, memSize] using hdiff.1)
        (by simpa [out, memSize] using hdiff.2)
      have hnonneg := pd5_edgePositiveBase_nonneg F S ρ w j B s c z'
      calc
        _ ≤ pd5_edgePositiveBase F S ρ w j B s c z' *
              ((1 + v / v₀ + (v / v₀)⁻¹) ^ K * (v / v₀) ^ memSize s *
                v₀ ^ memSize out) :=
          mul_le_mul_of_nonneg_left hpow hnonneg
        _ = C * (pd5_edgePositiveBase F S ρ w j B s c z' * v₀ ^ memSize out) := by
          dsimp [C]
          ring
    · simp [pd5_edgePositiveBase, hbase, out]
  unfold pd5_edgePositiveRowInner
  calc
    _ ≤ ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ z' ∈ Z,
            C * (pd5_edgePositiveBase F S ρ w j B s c z' *
              v₀ ^ memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c)) := by
          apply Finset.sum_le_sum
          intro c hc
          apply Finset.sum_le_sum
          intro z' hz'
          exact hterm c z'
    _ = C * pd5_edgePositiveRowInner F S ρ w j B Z v₀ s := by
          symm
          change C *
            (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
              ∑ z' ∈ Z,
                pd5_edgePositiveBase F S ρ w j B s c z' *
                  v₀ ^ memSize (z', edgeTargetLists F S s c, edgeNewMemory F S s c)) = _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.mul_sum]

private theorem pd5_edgeAbsChoice_weight_change {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (j B : ℕ) (Z : Finset (ℤ × ℤ))
    (s : MemPoint S.x K) (hs : memSize s ≤ B)
    (v v₀ : ℝ) (hv : 0 < v) (hv₀ : 0 < v₀) :
    pd5_edgeAbsChoice F S ρ w j B Z (fun _ => 1) (fun t => v ^ memSize t) s ≤
      (1 + v / v₀ + (v / v₀)⁻¹) ^ K * (v / v₀) ^ memSize s *
        pd5_edgeAbsChoice F S ρ w j B Z (fun _ => 1)
          (fun t => v₀ ^ memSize t) s := by
  rw [pd5_edgeAbsChoice_pow_eq F S ρ w j B Z v s, if_pos hs,
    pd5_edgeAbsChoice_pow_eq F S ρ w j B Z v₀ s, if_pos hs]
  have hrow (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      pd5_edgePositiveRowInner F S ρ w j B Z v
          (s.1, permuteLists σ s.2.1, s.2.2) ≤
        (1 + v / v₀ + (v / v₀)⁻¹) ^ K * (v / v₀) ^ memSize s *
          pd5_edgePositiveRowInner F S ρ w j B Z v₀
            (s.1, permuteLists σ s.2.1, s.2.2) := by
    have hsize : memSize (s.1, permuteLists σ s.2.1, s.2.2) ≤ B := by
      simpa [pd5_memSize_activePermute] using hs
    have hchange := pd5_edgePositiveRowInner_weight_change F S ρ w j B Z
      (s.1, permuteLists σ s.2.1, s.2.2) hsize v v₀ hv hv₀
    simpa [pd5_memSize_activePermute] using hchange
  unfold pd5_activeAverage
  calc
    _ ≤ (permCount S.x K : ℝ)⁻¹ *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ((1 + v / v₀ + (v / v₀)⁻¹) ^ K * (v / v₀) ^ memSize s) *
              pd5_edgePositiveRowInner F S ρ w j B Z v₀
                (s.1, permuteLists σ s.2.1, s.2.2) := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro σ hσ
            exact hrow σ
          · positivity
    _ = (1 + v / v₀ + (v / v₀)⁻¹) ^ K * (v / v₀) ^ memSize s *
          ((permCount S.x K : ℝ)⁻¹ *
            ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              pd5_edgePositiveRowInner F S ρ w j B Z v₀
                (s.1, permuteLists σ s.2.1, s.2.2)) := by
          rw [← Finset.mul_sum]
          ring

private theorem pd5_edgeAbsChoice_target_sum {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (j B : ℕ) (Z : Finset (ℤ × ℤ))
    (T : Finset (MemPoint S.x K))
    (hT : ∀ u, u ∈ T ↔ pd5_stateRegion F S w B u)
    (s : MemPoint S.x K) (hs : pd5_stateRegion F S w B s)
    (v : ℝ) :
    (∑ t ∈ T,
      pd5_edgeAbsChoice F S ρ w j B Z (fun _ => 1)
        (fun u => if u = t then (1 : ℝ) else 0) s * v ^ memSize t) =
      pd5_edgeAbsChoice F S ρ w j B Z (fun _ => 1)
        (fun u => v ^ memSize u) s := by
  classical
  have hTactive : ∀ r ∈ T,
      ∀ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        (r.1, permuteLists σ r.2.1, r.2.2) ∈ T := by
    intro r hr σ
    exact (hT _).2 (pd5_stateRegion_activePermute F S w B r ((hT r).1 hr) σ)
  have hsT : s ∈ T := (hT s).2 hs
  let qδ (t r : MemPoint S.x K) : ℝ :=
    ∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i,
      ∑ z' ∈ Z,
        pd5_edgePositiveBase F S ρ w j B r c z' *
          pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
            (z', edgeTargetLists F S r c, edgeNewMemory F S r c)
  let qv (r : MemPoint S.x K) : ℝ :=
    ∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i,
      ∑ z' ∈ Z,
        pd5_edgePositiveBase F S ρ w j B r c z' *
          pd5_activeAverage S (fun u => v ^ memSize u)
            (z', edgeTargetLists F S r c, edgeNewMemory F S r c)
  have hQδ (t : MemPoint S.x K) :
      pd5_edgeAbsChoice F S ρ w j B Z (fun _ => 1)
        (fun u => if u = t then (1 : ℝ) else 0) s =
    pd5_activeAverage S (qδ t) s := by
    simp [pd5_edgeAbsChoice, pd5_edgePositiveBase, pd5_edgeChoiceMass,
      qδ, hs.2.1, pd5_activeAverage, pd5_memSize_activePermute]
  have hQv :
    pd5_edgeAbsChoice F S ρ w j B Z (fun _ => 1)
        (fun u => v ^ memSize u) s = pd5_activeAverage S qv s := by
    simp [pd5_edgeAbsChoice, pd5_edgePositiveBase, pd5_edgeChoiceMass,
      qv, hs.2.1, pd5_activeAverage, pd5_memSize_activePermute]
  have hlinear :
      (∑ t ∈ T, pd5_activeAverage S (qδ t) s * v ^ memSize t) =
        pd5_activeAverage S (fun r => ∑ t ∈ T, v ^ memSize t * qδ t r) s := by
    calc
      _ = ∑ t ∈ T, v ^ memSize t * pd5_activeAverage S (qδ t) s := by
            apply Finset.sum_congr rfl
            intro t ht
            ring
      _ = _ := (pd5_activeAverage_finsetSum S T (fun t => v ^ memSize t) qδ s).symm
  have hcombined (r : MemPoint S.x K) (hr : r ∈ T) :
      (∑ t ∈ T, v ^ memSize t * qδ t r) = qv r := by
    have hrState : pd5_stateRegion F S w B r := (hT r).1 hr
    have hrsize : memSize r ≤ B := hrState.2.1
    calc
      _ = ∑ t ∈ T, ∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i,
            ∑ z' ∈ Z,
              v ^ memSize t * (pd5_edgePositiveBase F S ρ w j B r c z' *
                pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
                  (z', edgeTargetLists F S r c, edgeNewMemory F S r c)) := by
          apply Finset.sum_congr rfl
          intro t ht
          simp only [qδ]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.mul_sum]
      _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i,
            ∑ z' ∈ Z,
              ∑ t ∈ T,
                v ^ memSize t * (pd5_edgePositiveBase F S ρ w j B r c z' *
                  pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
                    (z', edgeTargetLists F S r c, edgeNewMemory F S r c)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c hc
            rw [Finset.sum_comm]
      _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i,
            ∑ z' ∈ Z,
              pd5_edgePositiveBase F S ρ w j B r c z' *
                ∑ t ∈ T,
                  v ^ memSize t * pd5_activeAverage S
                    (fun u => if u = t then (1 : ℝ) else 0)
                    (z', edgeTargetLists F S r c, edgeNewMemory F S r c) := by
            apply Finset.sum_congr rfl
            intro c hc
            apply Finset.sum_congr rfl
            intro z' hz'
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t ht
            ring
      _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i,
            ∑ z' ∈ Z,
              pd5_edgePositiveBase F S ρ w j B r c z' *
                pd5_activeAverage S (fun u => v ^ memSize u)
                  (z', edgeTargetLists F S r c, edgeNewMemory F S r c) := by
            apply Finset.sum_congr rfl
            intro c hc
            apply Finset.sum_congr rfl
            intro z' hz'
            by_cases hbase : EdgeAdmissible F S w r c z' ∧
                memSize (z', edgeTargetLists F S r c,
                  edgeNewMemory F S r c) ≤ B
            · have hout := pd5_edge_output_region F S w B r hrState.1 c z'
                hbase.1 hbase.2
              have houtT :
                  (z', edgeTargetLists F S r c, edgeNewMemory F S r c) ∈ T :=
                (hT _).2 hout
              have hdelta := pd5_activeAverage_delta_weighted_sum_eq S T
                (z', edgeTargetLists F S r c, edgeNewMemory F S r c)
                hTactive houtT v
              have hdelta' :
                  (∑ t ∈ T, v ^ memSize t *
                    pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
                      (z', edgeTargetLists F S r c, edgeNewMemory F S r c)) =
                    v ^ memSize (z', edgeTargetLists F S r c, edgeNewMemory F S r c) := by
                calc
                  _ = ∑ t ∈ T,
                        pd5_activeAverage S (fun u => if u = t then (1 : ℝ) else 0)
                          (z', edgeTargetLists F S r c, edgeNewMemory F S r c) *
                          v ^ memSize t := by
                        apply Finset.sum_congr rfl
                        intro t ht
                        ring
                  _ = _ := hdelta
              rw [hdelta']
              rw [pd5_activeAverage_memSize_pow]
            · simp [pd5_edgePositiveBase, hbase]
      _ = qv r := by rfl
  calc
    _ = ∑ t ∈ T, pd5_activeAverage S (qδ t) s * v ^ memSize t := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hQδ t]
    _ = pd5_activeAverage S (fun r => ∑ t ∈ T, v ^ memSize t * qδ t r) s := hlinear
    _ = pd5_activeAverage S qv s := by
          unfold pd5_activeAverage
          apply congrArg (fun x : ℝ => (permCount S.x K : ℝ)⁻¹ * x)
          apply Finset.sum_congr rfl
          intro σ hσ
          exact hcombined (s.1, permuteLists σ s.2.1, s.2.2)
            (hTactive s hsT σ)
    _ = pd5_edgeAbsChoice F S ρ w j B Z (fun _ => 1)
          (fun u => v ^ memSize u) s := hQv.symm

private theorem pd5_plainTrunc_memSym_delta_eq {x : ℝ} {K : ℕ} (B : ℕ)
    (t : MemPoint x K) (ht : memSize t ≤ B) :
    pd5_plainTrunc B (memorySym (fun u => if u = t then (1 : ℂ) else 0)) =
      memorySym (fun u => if u = t then (1 : ℂ) else 0) := by
  funext s
  by_cases hs : memSize s ≤ B
  · simp [pd5_plainTrunc, hs]
  · have hneq : memSize s ≠ memSize t := by omega
    have hzero : memorySym (fun u => if u = t then (1 : ℂ) else 0) s = 0 := by
      by_contra hz
      exact hneq (pd5_memorySym_delta_size_eq_of_ne_zero s t hz)
    simp [pd5_plainTrunc, hs, hzero]

private theorem pd5_plainTrunc_delta_eq {x : ℝ} {K : ℕ} (B : ℕ)
    (t : MemPoint x K) (ht : memSize t ≤ B) :
    pd5_plainTrunc B (fun u => if u = t then (1 : ℂ) else 0) =
      (fun u => if u = t then (1 : ℂ) else 0) := by
  funext s
  by_cases hs : s = t
  · subst s
    simp [pd5_plainTrunc, ht]
  · simp [pd5_plainTrunc, hs]

private theorem pd5_edgeProjected_row_le_choice {K : ℕ}
    (δ c₁ c₂ : ℝ) (F : PDFix K) (S : PDScale) (hS : S.Valid K δ c₁ c₂)
    (ρ : ℝ) (w : ArchRoot) (hw : w.InRegion S)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) (B j : ℕ) (hj : j < S.N)
    (W : BirthLog K → ℂ) (hW : ∀ log, ‖W log‖ ≤ 1)
    (s : MemPoint S.x K) (hs : pd5_stateRegion F S w B s)
    (T : Finset (MemPoint S.x K)) (hTsize : ∀ t ∈ T, memSize t ≤ B)
    (v : ℝ) (hv : 1 < v) :
    (∑ t ∈ T,
      ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W (memorySym f)) s t‖ *
        v ^ memSize t) ≤
      pd5_edgeAbsChoice F S ρ w j B
        hbox.toFinset (fun _ => 1)
        (fun u => v ^ memSize u) s := by
  classical
  obtain ⟨T0, hT0, hT0mem, hModel⟩ :=
    pd5_chronological_model δ c₁ c₂ K F S hS ρ w hw B
  have hsT0 : s ∈ T0 := (hT0 s).2 hs
  have hT0active : ∀ r ∈ T0,
      ∀ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        (r.1, permuteLists σ r.2.1, r.2.2) ∈ T0 := by
    intro r hr σ
    exact (hT0 _).2 (pd5_stateRegion_activePermute F S w B r ((hT0 r).1 hr) σ)
  have hT0size (u : MemPoint S.x K) (hu : u ∈ T0) : memSize u ≤ B :=
    ((hT0 u).1 hu).2.1
  have hdecomp (t : MemPoint S.x K) (ht : memSize t ≤ B) :
      memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W (memorySym f)) s t =
        ∑ u ∈ T0,
          memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s u *
            memorySym (fun g => if g = t then (1 : ℂ) else 0) u := by
    let δt : MemPoint S.x K → ℂ := fun g => if g = t then 1 else 0
    have hExpansion := (hModel W (memorySym δt) s hsT0).2 j hj
    rw [pd5_plainTrunc_memSym_delta_eq B t ht] at hExpansion
    have hkernel (u : MemPoint S.x K) (hu : u ∈ T0) :
        memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W
          (pd5_plainTrunc B f)) s u =
          memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s u := by
      change pd5_edgeBirthTwist F S ρ w j W
          (pd5_plainTrunc B (fun g => if g = u then (1 : ℂ) else 0)) s =
        pd5_edgeBirthTwist F S ρ w j W (fun g => if g = u then (1 : ℂ) else 0) s
      rw [pd5_plainTrunc_delta_eq B u (hT0size u hu)]
    change pd5_edgeBirthTwist F S ρ w j W
        (memorySym δt) s = _
    calc
      _ = ∑ u ∈ T0,
            memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W
              (pd5_plainTrunc B f)) s u * memorySym δt u := hExpansion
      _ = _ := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hkernel u hu]
  have hrowExpansion :
      (∑ t ∈ T,
        ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W
          (memorySym f)) s t‖ * v ^ memSize t) ≤
        ∑ u ∈ T0,
          ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s u‖ *
            v ^ memSize u := by
    calc
      _ = ∑ t ∈ T,
            ‖∑ u ∈ T0,
              memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s u *
                memorySym (fun g => if g = t then (1 : ℂ) else 0) u‖ * v ^ memSize t := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [hdecomp t (hTsize t ht)]
      _ ≤ ∑ t ∈ T,
            (∑ u ∈ T0,
              ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s u *
                memorySym (fun g => if g = t then (1 : ℂ) else 0) u‖) * v ^ memSize t := by
              apply Finset.sum_le_sum
              intro t ht
              apply mul_le_mul_of_nonneg_right
              · exact norm_sum_le _ _
              · positivity
      _ = ∑ t ∈ T,
            (∑ u ∈ T0,
              ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s u‖ *
                ‖memorySym (fun g => if g = t then (1 : ℂ) else 0) u‖) * v ^ memSize t := by
              apply Finset.sum_congr rfl
              intro t ht
              apply congrArg (fun x : ℝ => x * v ^ memSize t)
              apply Finset.sum_congr rfl
              intro u hu
              simp [norm_mul]
      _ = ∑ t ∈ T, ∑ u ∈ T0,
            ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s u‖ *
              ‖memorySym (fun g => if g = t then (1 : ℂ) else 0) u‖ * v ^ memSize t := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [Finset.sum_mul]
      _ = ∑ u ∈ T0, ∑ t ∈ T,
            ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s u‖ *
              ‖memorySym (fun g => if g = t then (1 : ℂ) else 0) u‖ * v ^ memSize t := by
              rw [Finset.sum_comm]
      _ = ∑ u ∈ T0,
            ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s u‖ *
              (∑ t ∈ T,
                ‖memorySym (fun g => if g = t then (1 : ℂ) else 0) u‖ * v ^ memSize t) := by
              apply Finset.sum_congr rfl
              intro u hu
              symm
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro t ht
              ring
      _ ≤ ∑ u ∈ T0,
            ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s u‖ *
              v ^ memSize u := by
              apply Finset.sum_le_sum
              intro u hu
              exact mul_le_mul_of_nonneg_left
                (pd5_memorySym_delta_weighted_norm_sum_le T u v hv)
                (norm_nonneg _)
  have hPositive :
      (∑ u ∈ T0,
        ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W f) s u‖ *
          v ^ memSize u) ≤
        pd5_edgeAbsChoice F S ρ w j B hbox.toFinset (fun _ => 1)
          (fun u => v ^ memSize u) s := by
    calc
      _ ≤ ∑ u ∈ T0,
            pd5_edgeAbsChoice F S ρ w j B hbox.toFinset (fun _ => 1)
              (fun g => if g = u then (1 : ℝ) else 0) s * v ^ memSize u := by
              apply Finset.sum_le_sum
              intro u hu
              exact mul_le_mul_of_nonneg_right
                (pd5_edgeKernel_delta_bound F S ρ w j B hbox W
                  (by intro log; simpa using hW log) s u hs.2.1 (hT0size u hu))
                (by positivity)
      _ = pd5_edgeAbsChoice F S ρ w j B hbox.toFinset (fun _ => 1)
            (fun u => v ^ memSize u) s :=
          pd5_edgeAbsChoice_target_sum F S ρ w j B hbox.toFinset T0 hT0 s hs v
  exact hrowExpansion.trans hPositive

set_option maxHeartbeats 8000000 in
private theorem pd5_edge_twisted_row_point_bound {K : ℕ}
    (δ c₁ c₂ : ℝ) (F : PDFix K) (S : PDScale) (hS : S.Valid K δ c₁ c₂)
    (ρ : ℝ) (w : ArchRoot) (hw : w.InRegion S) (j : ℕ) (hj : j < S.N)
    (v v₀ Cghost Cedge cmax aAtom xPos : ℝ) (hv : 1 < v) (hv₀ : 1 < v₀)
    (hCedge : 0 < Cedge) (hLone : 1 ≤ S.L)
    (hRows : PD5PositiveRows δ c₁ c₂ F ρ v₀ Cghost Cedge cmax aAtom xPos)
    (hxPosS : xPos ≤ S.x)
    (hBpow : ((memoryCutoff S + 1 : ℕ) : ℝ) ^ K ≤ 3 ^ K * S.L ^ (2 * K))
    (hAbsorbNat :
      ((1 + v / v₀ + (v / v₀)⁻¹) ^ K * Cedge * (3 : ℝ) ^ K) *
          S.L ^ (2 * K) * Real.rpow S.L (3 * F.A₀) ≤
        Real.rpow S.L (4 * (K : ℝ) + 3 * F.A₀ + 3))
    (W : BirthLog K → ℂ) (hW : ∀ log, ‖W log‖ ≤ 1)
    (s : MemPoint S.x K) (hs : MemValid F S s) (hsize : memSize s ≤ memoryCutoff S)
    (T : Finset (MemPoint S.x K)) (hT : ∀ t ∈ T, memSize t ≤ memoryCutoff S) :
    (∑ t ∈ T,
      ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W (memorySym f)) s t‖ *
        v ^ memSize t) ≤
      Real.rpow S.L (4 * (K : ℝ) + 3 * F.A₀ + 3) * v ^ memSize s := by
  classical
  let rowConst : ℝ :=
    (1 + v / v₀ + (v / v₀)⁻¹) ^ K * Cedge * (3 : ℝ) ^ K
  have hLpos : 0 < S.L := by linarith [hLone]
  by_cases hboxSource : envBox S w s.1
  · have hstate : pd5_stateRegion F S w (memoryCutoff S) s :=
      ⟨hs, hsize, Or.inr hboxSource⟩
    have hbox := pd5_envBox_finite_of_valid hS hw
    have hproj := pd5_edgeProjected_row_le_choice δ c₁ c₂ F S hS ρ w hw
      hbox (memoryCutoff S) j hj W hW s hstate T hT v hv
    have hchoiceState := hRows S hS hxPosS w hw s hstate
    have hchoiceRaw := hchoiceState.2 j hj
      (∅ : Finset (BirthAddress K)) (∅ : Finset (BirthAddress K))
      (by simp) (by simp) (fun _ _ => 0) [] hbox.toFinset
      (by intro z hz; exact hbox.mem_toFinset.mpr hz)
    have hchoice :
        pd5_edgeAbsChoice F S ρ w j (memoryCutoff S) hbox.toFinset
          (fun _ => 1) (fun t => v₀ ^ memSize t) s ≤
          Cedge * ((memoryCutoff S + 1 : ℕ) : ℝ) ^ K *
            Real.rpow S.L (3 * F.A₀) * v₀ ^ memSize s := by
      have hprescribed :
          pd5_prescribedWeight S (memoryCutoff S) (∅ : Finset (BirthAddress K))
            ∅ (fun _ _ => 0) [] = fun _ => (1 : ℝ) := by
        funext log
        simp [pd5_prescribedWeight]
      rw [hprescribed] at hchoiceRaw
      simpa using hchoiceRaw
    have hchange := pd5_edgeAbsChoice_weight_change F S ρ w j
      (memoryCutoff S) hbox.toFinset s hsize v v₀
      (by linarith [hv]) (by linarith [hv₀])
    have hRatioBase : (v / v₀) ^ memSize s * v₀ ^ memSize s = v ^ memSize s := by
      calc
        _ = ((v / v₀) * v₀) ^ memSize s := by rw [← mul_pow]
        _ = v ^ memSize s := by
          rw [div_mul_cancel₀ v (ne_of_gt (by linarith [hv₀]))]
    have hmassStep :
        Cedge * ((memoryCutoff S + 1 : ℕ) : ℝ) ^ K *
            Real.rpow S.L (3 * F.A₀) * v₀ ^ memSize s ≤
          Cedge * (3 ^ K * S.L ^ (2 * K)) *
            Real.rpow S.L (3 * F.A₀) * v₀ ^ memSize s := by
      have hv₀nonneg : 0 ≤ v₀ := by linarith [hv₀]
      have hfac : 0 ≤ Cedge * Real.rpow S.L (3 * F.A₀) * v₀ ^ memSize s :=
        mul_nonneg (mul_nonneg hCedge.le (Real.rpow_nonneg hLpos.le _))
          (pow_nonneg hv₀nonneg _)
      calc
        _ = (Cedge * Real.rpow S.L (3 * F.A₀) * v₀ ^ memSize s) *
              ((memoryCutoff S + 1 : ℕ) : ℝ) ^ K := by ring
        _ ≤ (Cedge * Real.rpow S.L (3 * F.A₀) * v₀ ^ memSize s) *
              (3 ^ K * S.L ^ (2 * K)) := mul_le_mul_of_nonneg_left hBpow hfac
        _ = _ := by ac_rfl
    have hQbound :
        pd5_edgeAbsChoice F S ρ w j (memoryCutoff S) hbox.toFinset
          (fun _ => 1) (fun t => v ^ memSize t) s ≤
          rowConst * S.L ^ (2 * K) * Real.rpow S.L (3 * F.A₀) * v ^ memSize s := by
      calc
        _ ≤ (1 + v / v₀ + (v / v₀)⁻¹) ^ K *
              (v / v₀) ^ memSize s *
              pd5_edgeAbsChoice F S ρ w j (memoryCutoff S) hbox.toFinset
                (fun _ => 1) (fun t => v₀ ^ memSize t) s := hchange
        _ ≤ (1 + v / v₀ + (v / v₀)⁻¹) ^ K *
              (v / v₀) ^ memSize s *
              (Cedge * ((memoryCutoff S + 1 : ℕ) : ℝ) ^ K *
                Real.rpow S.L (3 * F.A₀) * v₀ ^ memSize s) := by
              apply mul_le_mul_of_nonneg_left hchoice
              positivity
        _ ≤ (1 + v / v₀ + (v / v₀)⁻¹) ^ K *
              (v / v₀) ^ memSize s *
              (Cedge * (3 ^ K * S.L ^ (2 * K)) *
                Real.rpow S.L (3 * F.A₀) * v₀ ^ memSize s) :=
              mul_le_mul_of_nonneg_left hmassStep (by positivity)
        _ = rowConst * S.L ^ (2 * K) * Real.rpow S.L (3 * F.A₀) *
              v ^ memSize s := by
              calc
                _ = (rowConst * S.L ^ (2 * K) * Real.rpow S.L (3 * F.A₀)) *
                    ((v / v₀) ^ memSize s * v₀ ^ memSize s) := by
                      dsimp [rowConst]
                      ac_rfl
                _ = _ := by rw [hRatioBase]
    have hQfinal :
        pd5_edgeAbsChoice F S ρ w j (memoryCutoff S) hbox.toFinset
          (fun _ => 1) (fun t => v ^ memSize t) s ≤
          Real.rpow S.L (4 * (K : ℝ) + 3 * F.A₀ + 3) * v ^ memSize s :=
      hQbound.trans (mul_le_mul_of_nonneg_right hAbsorbNat (by positivity))
    exact hproj.trans hQfinal
  · have hbox := pd5_envBox_finite_of_valid hS hw
    have hzero (t : MemPoint S.x K) :
        memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W (memorySym f)) s t = 0 := by
      simpa only [memKernel] using
        (pd5_edgeBirthTwist_zero_of_source_not_box F S ρ w j hbox W
          (fun g => if g = t then (1 : ℂ) else 0) s hboxSource)
    have hsum :
        (∑ t ∈ T,
          ‖memKernel (fun f => pd5_edgeBirthTwist F S ρ w j W (memorySym f)) s t‖ *
            v ^ memSize t) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      simp [hzero t]
    rw [hsum]
    exact mul_nonneg (Real.rpow_nonneg hLpos.le _)
      (pow_nonneg (by linarith [hv]) _)

set_option maxHeartbeats 4000000

/-- Polynomial Schur bounds for every bounded birth twist at a supplied fixed weight v.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:712–752`; uses positive raw-plus-comparison choice
weights before subtraction, pd5_edge_position_mass_le, finite prime masses and indexed
insertion/factorial counts after target memorySym. Feeds modified operation bounds;
no signed-kernel bound alone justifies this interface. -/
theorem pd5_twisted_edge_schur (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ)
    (v : ℝ) (hv : 1 < v) :
    ∃ Ccr x₀ : ℝ, 0 < Ccr ∧ 2 ≤ x₀ ∧
      ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
        ∀ j : ℕ, j < S.N → ∀ W : BirthLog K → ℂ, (∀ log, ‖W log‖ ≤ 1) →
          MemRowSchurLE_sym F S (memoryCutoff S) (pd5_edgeBirthTwist F S ρ w j W) v
            (Real.rpow S.L Ccr) ∧
          MemColSchurLE_sym F S (memoryCutoff S) (pd5_edgeBirthTwist F S ρ w j W) v
            (Real.rpow S.L Ccr) := by
  classical
  obtain ⟨v₀, Cghost, Cedge, cmax, aAtom, xPos,
      hv₀, hCghost, hCedge, hcmax, haAtom, hxPos, hRows⟩ :=
    pd5_positive_choice_rows δ c₁ c₂ hδ hc₁ K F hF ρ hρ
  obtain ⟨xScale, hxScale, hScale⟩ := pd5_scale_facts K F hF
  let Ccr : ℝ := 4 * (K : ℝ) + 3 * F.A₀ + 3
  let rowConst : ℝ :=
    (1 + v / v₀ + (v / v₀)⁻¹) ^ K * Cedge * (3 : ℝ) ^ K
  let L₀ : ℝ := max 1 rowConst
  let xAbs : ℝ := max 2 (Real.exp L₀)
  let x₀ : ℝ := max xPos (max xScale xAbs)
  refine ⟨Ccr, x₀, ?_, ?_, ?_⟩
  · dsimp [Ccr]
    positivity [hF.2.2.2.1]
  · have hxp : 2 ≤ xPos := hxPos
    have hxle : xPos ≤ x₀ := by
      dsimp [x₀]
      exact le_max_left _ _
    exact hxp.trans hxle
  · intro S hS hxS w hw j hj W hW
    have hxPosS : xPos ≤ S.x := by
      have h₁ : xPos ≤ max xPos (max xScale xAbs) := le_max_left _ _
      exact h₁.trans hxS
    have hxScaleS : xScale ≤ S.x := by
      have h₁ : xScale ≤ max xScale xAbs := le_max_left _ _
      have h₂ : max xScale xAbs ≤ max xPos (max xScale xAbs) := le_max_right _ _
      exact (h₁.trans h₂).trans hxS
    have hxAbsS : xAbs ≤ S.x := by
      have h₁ : xAbs ≤ max xScale xAbs := le_max_right _ _
      have h₂ : max xScale xAbs ≤ max xPos (max xScale xAbs) := le_max_right _ _
      exact (h₁.trans h₂).trans hxS
    have hExpL₀ : Real.exp L₀ ≤ S.x := by
      have hle : Real.exp L₀ ≤ xAbs := by
        dsimp [xAbs]
        exact le_max_right _ _
      exact hle.trans hxAbsS
    have hScaleS := hScale S hxScaleS
    rcases hScaleS with ⟨hLone, hNtwo, hNlow, hNup, hMup, hBbound, hMleN, hMass⟩
    have hSpos : 0 < S.x := by linarith [hS.1]
    have hL₀ : L₀ ≤ S.L := by
      have hLog := Real.log_le_log (Real.exp_pos L₀) hExpL₀
      simpa [PDScale.L] using hLog
    have hLpos : 0 < S.L := by linarith [hLone]
    have hA₀ : 0 < F.A₀ := hF.2.2.2.1
    have hRowConst : rowConst ≤ S.L ^ 3 := by
      have hC : rowConst ≤ L₀ := by
        dsimp [L₀]
        exact le_max_right _ _
      have hL₀leL : L₀ ≤ S.L := hL₀
      have hLcube : S.L ≤ S.L ^ 3 := by
        have hLsq : 1 ≤ S.L ^ 2 := by nlinarith [sq_nonneg (S.L - 1)]
        calc
          S.L = S.L * 1 := by ring
          _ ≤ S.L * S.L ^ 2 := mul_le_mul_of_nonneg_left hLsq hLpos.le
          _ = S.L ^ 3 := by ring
      exact hC.trans (hL₀leL.trans hLcube)
    have hBplus : ((memoryCutoff S + 1 : ℕ) : ℝ) ≤ 3 * S.L ^ 2 := by
      have hLsq : 1 ≤ S.L ^ 2 := by nlinarith [sq_nonneg (S.L - 1)]
      push_cast
      nlinarith [hBbound, hLsq]
    have hBpow : ((memoryCutoff S + 1 : ℕ) : ℝ) ^ K ≤
        3 ^ K * S.L ^ (2 * K) := by
      calc
        _ ≤ (3 * S.L ^ 2) ^ K := by
          exact pow_le_pow_left₀ (by positivity) hBplus K
        _ = 3 ^ K * S.L ^ (2 * K) := by rw [mul_pow, pow_mul]
    have hAbsorb := pd5_absorb_edge_row_constant S.L rowConst F.A₀ K
      hLone (by positivity) hRowConst
    have hLpow : S.L ^ (2 * K) = Real.rpow S.L (2 * (K : ℝ)) := by
      calc
        _ = Real.rpow S.L ((2 * K : ℕ) : ℝ) :=
          (Real.rpow_natCast S.L (2 * K)).symm
        _ = Real.rpow S.L (2 * (K : ℝ)) := by congr 1; push_cast; ring
    have hAbsorbNat : rowConst * S.L ^ (2 * K) * Real.rpow S.L (3 * F.A₀) ≤
        Real.rpow S.L Ccr := by
      rw [hLpow]
      exact hAbsorb
    change MemRowSchurLE F S (memoryCutoff S)
      (fun f => pd5_edgeBirthTwist F S ρ w j W (memorySym f)) v
      (Real.rpow S.L Ccr) ∧ _
    constructor
    · intro s hs hsize T hT
      exact pd5_edge_twisted_row_point_bound δ c₁ c₂ F S hS ρ w hw j hj
        v v₀ Cghost Cedge cmax aAtom xPos hv hv₀ hCedge hLone hRows hxPosS
        hBpow hAbsorbNat W hW s hs hsize T hT
    · sorry

set_option maxHeartbeats 800000

end
end ArtinPrimitiveRoots.TypeII.PD
