import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

private def pd5_boundedListFinset {α : Type*} [Fintype α] (B : ℕ) : Finset (List α) :=
  (Finset.range (B + 1)).biUnion fun n =>
    (Finset.univ : Finset (Fin n → α)).image List.ofFn

private theorem pd5_mem_boundedListFinset {α : Type*} [Fintype α] (B : ℕ)
    (l : List α) : l ∈ pd5_boundedListFinset B ↔ l.length ≤ B := by
  classical
  constructor
  · intro hl
    rcases Finset.mem_biUnion.mp hl with ⟨n, hn, himage⟩
    rcases Finset.mem_image.mp himage with ⟨v, _, rfl⟩
    simp only [List.length_ofFn]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  · intro hl
    let n := l.length
    have hn : n < B + 1 := by dsimp [n]; omega
    apply Finset.mem_biUnion.mpr
    refine ⟨n, Finset.mem_range.mpr hn, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨fun j : Fin n => l.get j, Finset.mem_univ _, ?_⟩
    simpa [n] using List.ofFn_get l

private theorem pd5_memValid_memoryPermute {K : ℕ} (F : PDFix K)
    (S : PDScale) (s : MemPoint S.x K) (σ : MemoryPermutation s)
    (hs : MemValid F S s) : MemValid F S (memoryPermute s σ) := by
  classical
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro i e he
  have he' : e ∈ List.ofFn (fun j : Fin (s.2.2 i).length =>
      (s.2.2 i).get (σ i j)) := by
    simpa [memoryPermute] using he
  rcases (List.mem_ofFn' (fun j : Fin (s.2.2 i).length =>
      (s.2.2 i).get (σ i j)) e).mp he' with ⟨j, hj⟩
  have hmem := hs.2.2 i ((s.2.2 i).get (σ i j)) (List.get_mem _ _)
  rw [← hj]
  exact hmem

private theorem pd5_removeIndices_mem {l : List Particle}
    (D : Finset (Fin l.length)) {e : Particle}
    (he : e ∈ removeIndices l D) : e ∈ l := by
  classical
  unfold removeIndices at he
  rcases List.mem_filterMap.mp he with ⟨j, -, hj⟩
  by_cases hD : j ∈ D
  · simp [hD] at hj
  · simp [hD] at hj
    subst e
    exact List.get_mem l j

private theorem pd5_anchorAt_bound (p : ℕ) (z : ℤ × ℤ) :
    (anchorAt p z).2 ≤ p := by
  change (projLine p z).val ≤ p
  exact Nat.le_of_lt_succ (projLine p z).isLt

private theorem pd5_ghostOutput_stateRegion {K : ℕ} (F : PDFix K)
    (S : PDScale) (w : ArchRoot) (B j : ℕ) {s : MemPoint S.x K}
    (hs : pd5_stateRegion F S w B s)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length))
    (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
    (hdel : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1)
    (hsize : memSize (s.1, s.2.1, fun i =>
      removeIndices (s.2.2 i) (D i) ++
        List.ofFn (fun k => anchorAt (new i k) s.1)) ≤ B) :
    pd5_stateRegion F S w B
      (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
        List.ofFn (fun k => anchorAt (new i k) s.1)) := by
  rcases hs with ⟨hvalid, -, hposition⟩
  refine ⟨?_, hsize, hposition⟩
  refine ⟨hvalid.1, hvalid.2.1, ?_⟩
  intro i e he
  rcases List.mem_append.mp he with he | he
  · exact hvalid.2.2 i e (pd5_removeIndices_mem (D i) he)
  · rcases (List.mem_ofFn' (fun k : Fin (l i) => anchorAt (new i k) s.1) e).mp
      (by simpa using he) with ⟨k, hk⟩
    subst e
    exact ⟨(new i k).property, pd5_anchorAt_bound _ _⟩

private def pd5_pointMass {x : ℝ} {K : ℕ} (t : MemPoint x K) :
    MemPoint x K → ℂ := fun u => if u = t then 1 else 0

private theorem pd5_pointMass_sum {x : ℝ} {K : ℕ}
    (T : Finset (MemPoint x K)) (f : MemPoint x K → ℂ) (u : MemPoint x K) :
    (∑ t ∈ T, f t * pd5_pointMass t u) = if u ∈ T then f u else 0 := by
  classical
  simp [pd5_pointMass]

private theorem pd5_weightedPointMass_sum {x : ℝ} {K : ℕ}
    (T : Finset (MemPoint x K)) (f : MemPoint x K → ℂ) (u : MemPoint x K)
    (c : ℂ) (hu : u ∈ T) :
    (∑ t ∈ T, f t * (c * pd5_pointMass t u)) = c * f u := by
  calc
    _ = c * ∑ t ∈ T, f t * pd5_pointMass t u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = c * f u := by rw [pd5_pointMass_sum, if_pos hu]

set_option maxHeartbeats 0 in
private theorem pd5_ghost_kernel_expansion {K : ℕ} (F : PDFix K)
    (S : PDScale) (w : ArchRoot) (ρ : ℝ) (B : ℕ) (T : Finset (MemPoint S.x K))
    (hT : ∀ u, u ∈ T ↔ pd5_stateRegion F S w B u)
    (W : BirthLog K → ℂ) (f : MemPoint S.x K → ℂ) (s : MemPoint S.x K)
    (hs : s ∈ T) (j : ℕ) :
    pd5_ghostBirthTwist F S ρ j W (pd5_plainTrunc B f) s =
      ∑ t ∈ T,
        memKernel (fun g => pd5_ghostBirthTwist F S ρ j W
          (pd5_plainTrunc B g)) s t * f t := by
  classical
  let g₁ : LogPoint S.x K → ℂ := fun σL =>
    W σL.2 * pd5_plainTrunc B f σL.1
  let g₂ : LogPoint S.x K → ℂ := fun σL =>
    ∑ t ∈ T, f t * (W σL.2 * pd5_pointMass t σL.1)
  have hcongr : logGhost F S ρ j g₁ (s, ([] : BirthLog K)) =
      logGhost F S ρ j (logTrunc (some B) g₂) (s, ([] : BirthLog K)) := by
    unfold logGhost
    apply Finset.sum_congr rfl
    intro D hD
    apply tsum_congr
    intro l
    apply Finset.sum_congr rfl
    intro new hnew
    by_cases hdel' : ∀ i, D i ⊆ hitIndices
        ((s, ([] : BirthLog K)).1.2.2 i) (s, ([] : BirthLog K)).1.1
    · simp only [if_pos hdel']
      let u : MemPoint S.x K :=
        (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
          List.ofFn (fun k => anchorAt (new i k) s.1))
      by_cases hsize : memSize u ≤ B
      · have huRegion : pd5_stateRegion F S w B u := by
          have hsRegion : pd5_stateRegion F S w B s := (hT s).1 hs
          have hdel : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1 := by
            simpa using hdel'
          apply pd5_ghostOutput_stateRegion F S w B j hsRegion D l new hdel
          simpa [u] using hsize
        have huT := (hT u).2 huRegion
        let G : BirthLog K := (List.finRange K).flatMap fun i =>
          List.ofFn fun k : Fin (l i) =>
            (BirthAddress.ghost j i k.val, (new i k : ℕ))
        have hEq (L : BirthLog K) : g₁ (u, L) =
            logTrunc (some B) g₂ (u, L) := by
          have hleft : g₁ (u, L) = W L * f u := by
            simp [g₁, pd5_plainTrunc, hsize]
          have hright : g₂ (u, L) = W L * f u := by
            exact pd5_weightedPointMass_sum T f u (W L) huT
          calc
            g₁ (u, L) = W L * f u := hleft
            _ = g₂ (u, L) := hright.symm
            _ = logTrunc (some B) g₂ (u, L) := by simp [logTrunc, hsize]
        let coeff : ℂ := ((∏ i : Fin K, ghostGroupCoeff F S ρ j i
          (hitCount (s.2.2 i) s.1) (D i).card (l i)
          (List.ofFn fun k => (new i k : ℕ)) : ℝ) : ℂ)
        have hEq' := congrArg (fun z : ℂ => coeff * z) (hEq G)
        simpa [coeff, u, G, pd5_ghostOutput] using hEq'
      · simp [g₁, g₂, pd5_plainTrunc, logTrunc, u, hsize]
    · simp only [if_neg hdel']
  have hlin := pd5_logGhost_finsetSumFun F S ρ j B T
    (fun t => f t) (fun t σL => W σL.2 * pd5_pointMass t σL.1)
  have hlinAt := congrFun hlin (s, ([] : BirthLog K))
  have hdelta (t : MemPoint S.x K) :
      (fun σL => W σL.2 * pd5_plainTrunc B (pd5_pointMass t) σL.1) =
        logTrunc (some B) (fun σL => W σL.2 * pd5_pointMass t σL.1) := by
    funext σL
    by_cases hsize : memSize σL.1 ≤ B <;>
      simp [logTrunc, pd5_plainTrunc, hsize]
  calc
    pd5_ghostBirthTwist F S ρ j W (pd5_plainTrunc B f) s =
        logGhost F S ρ j g₁ (s, ([] : BirthLog K)) := rfl
    _ =
        logGhost F S ρ j (logTrunc (some B) g₂) (s, ([] : BirthLog K)) := hcongr
    _ = ∑ t ∈ T, f t *
          logGhost F S ρ j
            (logTrunc (some B) (fun σL => W σL.2 * pd5_pointMass t σL.1))
            (s, ([] : BirthLog K)) := hlinAt
    _ = ∑ t ∈ T,
          memKernel (fun g => pd5_ghostBirthTwist F S ρ j W
            (pd5_plainTrunc B g)) s t * f t := by
          apply Finset.sum_congr rfl
          intro t ht
          have hkernel : logGhost F S ρ j
              (logTrunc (some B) (fun σL => W σL.2 * pd5_pointMass t σL.1)) (s, []) =
              memKernel (fun g => pd5_ghostBirthTwist F S ρ j W
                (pd5_plainTrunc B g)) s t := by
            rw [← hdelta t]
            rfl
          rw [hkernel]
          ring

private theorem pd5_stateRegion_activePermute {K : ℕ} (F : PDFix K)
    (S : PDScale) (w : ArchRoot) (B : ℕ) (s : MemPoint S.x K)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (hs : pd5_stateRegion F S w B s) :
    pd5_stateRegion F S w B (s.1, (permuteLists σ s.2.1, s.2.2)) := by
  rcases hs with ⟨hvalid, hsize, hposition⟩
  refine ⟨⟨hvalid.1, ?_, hvalid.2.2⟩, ?_, hposition⟩
  · intro i j
    exact hvalid.2.1 i (σ i j)
  · simpa [memSize] using hsize

private theorem pd5_edgeOutput_stateRegion {K : ℕ} (F : PDFix K)
    (S : PDScale) (w : ArchRoot) (B : ℕ) {s : MemPoint S.x K}
    (hs : pd5_stateRegion F S w B s)
    {c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i} {z' : ℤ × ℤ}
    (hadm : EdgeAdmissible F S w s c z')
    (hsize : memSize (z', (edgeTargetLists F S s c, edgeNewMemory F S s c)) ≤ B) :
    pd5_stateRegion F S w B
      (z', (edgeTargetLists F S s c, edgeNewMemory F S s c)) := by
  rcases hs with ⟨hvalid, -, -⟩
  rcases hadm with ⟨-, -, htarget, -, -, hGcd, -, hbox, -, -⟩
  refine ⟨⟨hGcd, (fun i j => (htarget.1 i j).2), ?_⟩, hsize, Or.inr hbox⟩
  intro i e he
  simp only [edgeNewMemory] at he
  rcases List.mem_append.mp he with he | he
  · exact hvalid.2.2 i e (pd5_removeIndices_mem _ he)
  · by_cases hstore : (c i).1
    · simp [hstore] at he
      subst e
      exact ⟨hvalid.2.1 i (lastSlot S.x), pd5_anchorAt_bound _ _⟩
    · simp [hstore] at he

set_option maxHeartbeats 0 in
private theorem pd5_edge_kernel_expansion {δ c₁ c₂ : ℝ} {K : ℕ}
    (F : PDFix K) (S : PDScale) (hS : S.Valid K δ c₁ c₂)
    (ρ : ℝ) (w : ArchRoot) (hw : w.InRegion S) (B : ℕ)
    (T : Finset (MemPoint S.x K))
    (hT : ∀ u, u ∈ T ↔ pd5_stateRegion F S w B u)
    (W : BirthLog K → ℂ) (f : MemPoint S.x K → ℂ)
    (s : MemPoint S.x K) (hs : s ∈ T) (j : ℕ) :
    pd5_edgeBirthTwist F S ρ w j W (pd5_plainTrunc B f) s =
      ∑ t ∈ T,
        memKernel (fun g => pd5_edgeBirthTwist F S ρ w j W
          (pd5_plainTrunc B g)) s t * f t := by
  classical
  let g₁ : LogPoint S.x K → ℂ := fun σL =>
    W σL.2 * pd5_plainTrunc B f σL.1
  let g₂ : LogPoint S.x K → ℂ := fun σL =>
    ∑ t ∈ T, f t *
      (W σL.2 * pd5_plainTrunc B (pd5_pointMass t) σL.1)
  let hbox := pd5_envBox_finite_of_valid hS hw
  have hcontinuation (u : MemPoint S.x K) (hu : u ∈ T) (L : BirthLog K) :
      g₁ (u, L) = g₂ (u, L) := by
    have hregion := (hT u).1 hu
    rcases hregion with ⟨-, hsize, -⟩
    have hleft : g₁ (u, L) = W L * f u := by
      simp [g₁, pd5_plainTrunc, hsize]
    have hright : g₂ (u, L) = W L * f u := by
      calc
        g₂ (u, L) =
            ∑ t ∈ T, f t * (W L * pd5_pointMass t u) := by
              dsimp [g₂]
              apply Finset.sum_congr rfl
              intro t ht
              simp [pd5_plainTrunc, hsize]
        _ = W L * f u := pd5_weightedPointMass_sum T f u (W L) hu
    exact hleft.trans hright.symm
  have hSym (σL : LogPoint S.x K) (hσ : σL.1 ∈ T) :
      logSym F S g₁ σL = logSym F S g₂ σL := by
    unfold logSym
    apply congrArg (fun z : ℂ => ((permCount S.x K : ℂ)⁻¹) * z)
    apply Finset.sum_congr rfl
    intro τ hτ
    let u : MemPoint S.x K :=
      (σL.1.1, (permuteLists τ σL.1.2.1, σL.1.2.2))
    have huRegion := pd5_stateRegion_activePermute F S w B σL.1 τ
      ((hT σL.1).1 hσ)
    have hu : u ∈ T := by
      apply (hT u).2
      simpa [u] using huRegion
    exact hcontinuation u hu σL.2
  have hPiece (step : ℕ) (raw : Bool) (St Pr : Finset (Fin K))
      (σL : LogPoint S.x K) (hσ : σL.1 ∈ T) :
      logEdgePiece F S ρ w step raw St Pr (logSym F S g₁) σL =
        logEdgePiece F S ρ w step raw St Pr (logSym F S g₂) σL := by
    rw [pd5_logEdgePiece_finite F S ρ w step raw St Pr (logSym F S g₁) σL hbox,
      pd5_logEdgePiece_finite F S ρ w step raw St Pr (logSym F S g₂) σL hbox]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro z hz
    let u : MemPoint S.x K :=
      (z, (edgeTargetLists F S σL.1 c, edgeNewMemory F S σL.1 c))
    by_cases hadm : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
        EdgeAdmissible F S w σL.1 c z
    · simp only [if_pos hadm]
      by_cases hsize : memSize u ≤ B
      · have huRegion := pd5_edgeOutput_stateRegion F S w B
          ((hT σL.1).1 hσ) hadm.2.2 (by simpa [u] using hsize)
        have hu : u ∈ T := by
          apply (hT u).2
          simpa [u] using huRegion
        have hsame := hSym (u, σL.2 ++ edgeBirths F S step σL.1 c) hu
        let coeff : ℂ :=
          (((ρ ^ (∑ i : Fin K, hitCount (σL.1.2.2 i) σL.1.1) *
              (∏ i : Fin K, pd5_edgeChoiceMass F S σL.1 c i) *
            ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S σL.1 c i) z) : ℝ) : ℂ) *
            edgeMultiplier F S (decide (step % 2 = 0)) raw σL.1.2.1
              (edgeTargetLists F S σL.1 c) σL.1.1 z)
        have hsame' := congrArg (fun v : ℂ => coeff * v) hsame
        simpa [u, coeff] using hsame'
      · have hsizePerm (τ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
            memSize (u.1, (permuteLists τ u.2.1, u.2.2)) > B := by
          have heq : memSize (u.1, (permuteLists τ u.2.1, u.2.2)) = memSize u := by
            simp [memSize]
          rw [heq]
          exact lt_of_not_ge hsize
        have hzero (g : LogPoint S.x K → ℂ) (hg : ∀ v, memSize v.1 > B → g v = 0) :
            logSym F S g (u, σL.2 ++ edgeBirths F S step σL.1 c) = 0 := by
          have hsum : (∑ τ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              g ((u.1, (permuteLists τ u.2.1, u.2.2)),
                σL.2 ++ edgeBirths F S step σL.1 c)) = 0 := by
            apply Finset.sum_eq_zero
            intro τ hτ
            exact hg ((u.1, (permuteLists τ u.2.1, u.2.2)),
              σL.2 ++ edgeBirths F S step σL.1 c) (hsizePerm τ)
          unfold logSym
          rw [hsum]
          simp
        have hg₁ : ∀ v, memSize v.1 > B → g₁ v = 0 := by
          intro v hv
          have hnot : ¬ memSize v.1 ≤ B := not_le_of_gt hv
          simp [g₁, pd5_plainTrunc, hnot]
        have hg₂ : ∀ v, memSize v.1 > B → g₂ v = 0 := by
          intro v hv
          have hnot : ¬ memSize v.1 ≤ B := not_le_of_gt hv
          simp [g₂, pd5_plainTrunc, hnot]
        have hzero₁ := hzero g₁ hg₁
        have hzero₂ := hzero g₂ hg₂
        simp [u, hzero₁, hzero₂]
    · simp only [if_neg hadm]
  let core (g : LogPoint S.x K → ℂ) : LogPoint S.x K → ℂ := fun σL =>
    ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      (logEdgePiece F S ρ w j true St Pr (logSym F S g) σL -
        logEdgePiece F S ρ w j false St Pr (logSym F S g) σL)
  have hCore (σL : LogPoint S.x K) (hσ : σL.1 ∈ T) :
      core g₁ σL = core g₂ σL := by
    dsimp [core]
    apply Finset.sum_congr rfl
    intro St hSt
    apply Finset.sum_congr rfl
    intro Pr hPr
    rw [hPiece j true St Pr σL hσ, hPiece j false St Pr σL hσ]
  have hEdgeCongr : logEdge F S ρ w EdgeKind.full j g₁ (s, ([] : BirthLog K)) =
      logEdge F S ρ w EdgeKind.full j g₂ (s, ([] : BirthLog K)) := by
    change logSym F S (core g₁) (s, ([] : BirthLog K)) =
      logSym F S (core g₂) (s, ([] : BirthLog K))
    unfold logSym
    apply congrArg (fun z : ℂ => ((permCount S.x K : ℂ)⁻¹) * z)
    apply Finset.sum_congr rfl
    intro τ hτ
    let source : MemPoint S.x K := (s.1, (permuteLists τ s.2.1, s.2.2))
    have hsourceRegion := pd5_stateRegion_activePermute F S w B s τ
      ((hT s).1 hs)
    have hsourceT : source ∈ T := by
      apply (hT source).2
      simpa [source] using hsourceRegion
    exact hCore (source, ([] : BirthLog K)) hsourceT
  have hlinFun := pd5_logEdge_full_finsetSumFun F S ρ w j T
    (fun t => f t)
    (fun t σL => W σL.2 * pd5_plainTrunc B (pd5_pointMass t) σL.1) hbox
  have hlin := congrFun hlinFun (s, ([] : BirthLog K))
  calc
    pd5_edgeBirthTwist F S ρ w j W (pd5_plainTrunc B f) s =
        logEdge F S ρ w EdgeKind.full j g₁ (s, ([] : BirthLog K)) := rfl
    _ = logEdge F S ρ w EdgeKind.full j g₂ (s, ([] : BirthLog K)) := hEdgeCongr
    _ = ∑ t ∈ T, f t *
          logEdge F S ρ w EdgeKind.full j
            (fun σL => W σL.2 * pd5_plainTrunc B (pd5_pointMass t) σL.1)
            (s, ([] : BirthLog K)) := hlin
    _ = ∑ t ∈ T,
          memKernel (fun g => pd5_edgeBirthTwist F S ρ w j W
            (pd5_plainTrunc B g)) s t * f t := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [show logEdge F S ρ w EdgeKind.full j
              (fun σL => W σL.2 * pd5_plainTrunc B (pd5_pointMass t) σL.1)
              (s, ([] : BirthLog K)) =
                memKernel (fun g => pd5_edgeBirthTwist F S ρ w j W
                  (pd5_plainTrunc B g)) s t by rfl]
          ring

private theorem pd5_stateRegion_finite {δ c₁ c₂ : ℝ} {K : ℕ}
    (F : PDFix K) (S : PDScale) (hS : S.Valid K δ c₁ c₂)
    (w : ArchRoot) (hw : w.InRegion S) (B : ℕ) :
    ∃ T : Finset (MemPoint S.x K),
      ∀ s, s ∈ T ↔ pd5_stateRegion F S w B s := by
  classical
  let hbox := pd5_envBox_finite_of_valid hS hw
  let Candidate : Finset (ℤ × ℤ) := hbox.toFinset ∪ {(1, 0)}
  let PosPred (z : ℤ × ℤ) : Prop :=
    (z = (1, 0) ∨ envBox S w z) ∧ Int.gcd z.1 z.2 = 1
  let Pos : Type := {z : ℤ × ℤ // PosPred z}
  let posFinset : Finset (ℤ × ℤ) := Candidate.filter PosPred
  have hposFinset (z : ℤ × ℤ) : z ∈ posFinset ↔ PosPred z := by
    simp [posFinset, PosPred, Candidate, hbox.mem_toFinset, or_comm]
  letI : Fintype Pos := Fintype.ofFinset posFinset hposFinset

  let PrimeCode : Type := {p : ℕ // p ∈ markedPrimes S.x K F.a}
  letI : Fintype PrimeCode :=
    Fintype.ofFinset (markedPrimes S.x K F.a) (by intro p; rfl)
  let ActiveArray : Type := Fin K → Fin (slotCount S.x) → PrimeCode
  let ActivePred (p : ActiveArray) : Prop :=
    ∀ i j, (p i j).val ∈ primeBand S.x (F.a i)
  let Active : Type := {p : ActiveArray // ActivePred p}
  let activeFinset : Finset ActiveArray := Finset.univ.filter ActivePred
  have hactiveFinset (p : ActiveArray) : p ∈ activeFinset ↔ ActivePred p := by
    simp [activeFinset]
  letI : Fintype Active := Fintype.ofFinset activeFinset hactiveFinset

  let ParticleSet : Finset Particle :=
    (markedPrimes S.x K F.a).biUnion fun p =>
      (Finset.range (p + 1)).image fun ℓ => (p, ℓ)
  have hparticle (e : Particle) : e ∈ ParticleSet ↔
      e.1 ∈ markedPrimes S.x K F.a ∧ e.2 ≤ e.1 := by
    simp only [ParticleSet, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨p, hp, ℓ, hℓ, rfl⟩
      exact ⟨hp, hℓ⟩
    · rintro ⟨hp, hle⟩
      exact ⟨e.1, hp, e.2, hle, rfl⟩
  let ParticleCode : Type := {e : Particle // e ∈ ParticleSet}
  letI : Fintype ParticleCode := Fintype.ofFinset ParticleSet (by intro e; rfl)
  let BoundedList : Type := {l : List ParticleCode // l.length ≤ B}
  letI : Fintype BoundedList := Fintype.ofFinset (pd5_boundedListFinset B) (by
    intro l
    exact pd5_mem_boundedListFinset B l)
  let MemoryArray : Type := Fin K → BoundedList
  let MemoryPred (m : MemoryArray) : Prop :=
    (∑ i : Fin K, (m i).val.length ≤ B) ∧
      ∀ i e, e ∈ (m i).val → (e.val).1 ∈ primeBand S.x (F.a i)
  let MemoryCode : Type := {m : MemoryArray // MemoryPred m}
  let memoryFinset : Finset MemoryArray := Finset.univ.filter MemoryPred
  have hmemoryFinset (m : MemoryArray) : m ∈ memoryFinset ↔ MemoryPred m := by
    simp [memoryFinset]
  letI : Fintype MemoryCode := Fintype.ofFinset memoryFinset hmemoryFinset
  let Code : Type := Pos × (Active × MemoryCode)
  let stateOf (c : Code) : MemPoint S.x K :=
    (c.1.val,
      (fun i j => (c.2.1.val i j).val,
        fun i => (c.2.2.val i).val.map Subtype.val))
  let T : Finset (MemPoint S.x K) := Finset.univ.image stateOf
  refine ⟨T, ?_⟩
  intro s
  constructor
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨c, -, rfl⟩
    have hvalid : MemValid F S (stateOf c) := by
      refine ⟨c.1.property.2, ?_, ?_⟩
      · intro i j
        exact c.2.1.property i j
      · intro i e he
        rcases List.mem_map.mp he with ⟨q, hq, rfl⟩
        have hband := c.2.2.property.2 i q hq
        exact ⟨hband, (hparticle q.val).mp q.property |>.2⟩
    have hsize : memSize (stateOf c) ≤ B := by
      simpa [memSize, stateOf, List.length_map] using c.2.2.property.1
    exact ⟨hvalid, hsize, c.1.property.1⟩
  · rintro ⟨⟨hGcd, hActive, hMem⟩, hsize, hpos⟩
    let pos : Pos := ⟨s.1, ⟨hpos, hGcd⟩⟩
    let activeValues : ActiveArray := fun i j =>
      ⟨s.2.1 i j, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hActive i j⟩⟩
    let active : Active := ⟨activeValues, hActive⟩
    have hlen (i : Fin K) : (s.2.2 i).length ≤ B := by
      have hle : (s.2.2 i).length ≤ memSize s := by
        unfold memSize
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin K => (s.2.2 j).length)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      exact hle.trans hsize
    let memoryValues : MemoryArray := fun i =>
      ⟨(s.2.2 i).attach.map fun e =>
        ⟨e.val, (hparticle e.val).mpr ⟨
          Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, (hMem i e.val e.property).1⟩,
          (hMem i e.val e.property).2⟩⟩,
        by simpa using hlen i⟩
    have hMemoryTotal : (∑ i : Fin K, (memoryValues i).val.length) ≤ B := by
      simpa [memoryValues, List.length_map, memSize] using hsize
    have hMemoryBand : ∀ i e, e ∈ (memoryValues i).val →
        (e.val).1 ∈ primeBand S.x (F.a i) := by
      intro i e he
      rcases List.mem_map.mp he with ⟨e', he', rfl⟩
      exact (hMem i e'.val e'.property).1
    let memory : MemoryCode := ⟨memoryValues, hMemoryTotal, hMemoryBand⟩
    let c : Code := (pos, (active, memory))
    have hdecode : stateOf c = s := by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext i j
          rfl
        · funext i
          simp [stateOf, c, memory, memoryValues, List.map_map,
            Function.comp_def, List.attach_map_subtype_val]
    apply Finset.mem_image.mpr
    exact ⟨c, Finset.mem_univ c, hdecode⟩

/-- Finite invariant cutoff state set and exact finite kernel expansions of local twists.
Uses pd5_envBox_finite_of_valid
and finite cutoff expansions; feeds fixed-system estimates and low-rank norm iteration. -/
theorem pd5_chronological_model (δ c₁ c₂ : ℝ) (K : ℕ) (F : PDFix K)
    (S : PDScale) (hS : S.Valid K δ c₁ c₂) (ρ : ℝ) (w : ArchRoot) (hw : w.InRegion S)
    (B : ℕ) :
    ∃ T : Finset (MemPoint S.x K),
      (∀ s, s ∈ T ↔ pd5_stateRegion F S w B s) ∧
      (∀ s ∈ T, ∀ σ : MemoryPermutation s, memoryPermute s σ ∈ T) ∧
      ∀ W : BirthLog K → ℂ, ∀ f : MemPoint S.x K → ℂ, ∀ s ∈ T,
        (∀ j : ℕ, j ≤ S.N →
          pd5_ghostBirthTwist F S ρ j W (pd5_plainTrunc B f) s =
            ∑ t ∈ T, memKernel (fun g => pd5_ghostBirthTwist F S ρ j W
              (pd5_plainTrunc B g)) s t * f t) ∧
        (∀ j : ℕ, j < S.N →
          pd5_edgeBirthTwist F S ρ w j W (pd5_plainTrunc B f) s =
            ∑ t ∈ T, memKernel (fun g => pd5_edgeBirthTwist F S ρ w j W
              (pd5_plainTrunc B g)) s t * f t) := by
  classical
  obtain ⟨T, hT⟩ := pd5_stateRegion_finite F S hS w hw B
  refine ⟨T, hT, ?_, ?_⟩
  · intro s hs σ
    have hsRegion := (hT s).1 hs
    apply (hT (memoryPermute s σ)).2
    refine ⟨pd5_memValid_memoryPermute F S s σ hsRegion.1, ?_, hsRegion.2.2⟩
    simpa [memSize, memoryPermute] using hsRegion.2.1
  · intro W f s hs
    constructor
    · intro j hj
      exact pd5_ghost_kernel_expansion F S w ρ B T hT W f s hs j
    · intro j hj
      exact pd5_edge_kernel_expansion F S hS ρ w hw B T hT W f s hs j

end
end ArtinPrimitiveRoots.TypeII.PD
