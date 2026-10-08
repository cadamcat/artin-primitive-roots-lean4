import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».SignSupport

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- The literal scalar ghost coefficient has its deletion/birth parity sign whenever its
remaining factors are nonnegative. No distinct-value hypothesis is needed for a batch. -/
theorem pd5_ghostGroupCoeff_abs_sign {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (hρ : 0 < ρ) (j : ℕ) (i : Fin K) (hits deleted born : ℕ) (batch : List ℕ)
    (hη : 0 ≤ memoryEta S.x F.q_d j) (hq : 0 ≤ memoryQ S.x F.q_d j)
    (hV : 0 ≤ bandMass S.x (F.a i))
    (hbatch : ∀ p ∈ batch, 0 ≤ memoryNu S.x K F.a F.q_d i p) :
    ghostGroupCoeff F S ρ j i hits deleted born batch =
      (-1 : ℝ) ^ (deleted + born) * |ghostGroupCoeff F S ρ j i hits deleted born batch| := by
  let A : ℝ := (memoryEta S.x F.q_d j / ρ) ^ deleted *
    (memoryQ S.x F.q_d j / ρ ^ 2) ^ (hits - deleted) *
    (memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ) ^ born /
      (born.factorial : ℝ) *
    (batch.map fun p => memoryNu S.x K F.a F.q_d i p).prod
  have hp : 0 ≤ (batch.map fun p => memoryNu S.x K F.a F.q_d i p).prod := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact hbatch p hp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he : ghostGroupCoeff F S ρ j i hits deleted born batch =
      (-1 : ℝ) ^ (deleted + born) * A := pd5_ghostGroupCoeff_sign F S ρ j i hits deleted born batch
  rw [he]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hA]

/-- Averaging a target delta cannot change total memory size. -/
theorem pd5_memorySym_delta_size_ne {x : ℝ} {K : ℕ} (s t : MemPoint x K)
    (hsize : memSize s ≠ memSize t) :
    memorySym (fun u => if u = t then (1 : ℂ) else 0) s = 0 := by
  have hz : (∑ σ : MemoryPermutation s,
      if memoryPermute s σ = t then (1 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    have hn : memoryPermute s σ ≠ t := by
      intro he
      apply hsize
      exact (pd5_memSize_memoryPermute s σ).symm.trans (congrArg memSize he)
    simp [hn]
  change (Fintype.card (MemoryPermutation s) : ℂ)⁻¹ * _ = 0
  rw [hz, mul_zero]

/-- The entire product of ghost group coefficients has one deletion/birth parity sign. -/
theorem pd5_ghostWeight_abs_sign {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (hρ : 0 < ρ) (j : ℕ) (s : MemPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
    (hη : 0 ≤ memoryEta S.x F.q_d j) (hq : 0 ≤ memoryQ S.x F.q_d j)
    (hV : ∀ i, 0 ≤ bandMass S.x (F.a i))
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p) :
    (∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1)
      (D i).card (l i) (List.ofFn fun k => (new i k : ℕ))) =
      (-1 : ℝ) ^ ((∑ i, (D i).card) + ∑ i, l i) *
        |∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1)
          (D i).card (l i) (List.ofFn fun k => (new i k : ℕ))| := by
  let C : Fin K → ℝ := fun i => ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1)
    (D i).card (l i) (List.ofFn fun k => (new i k : ℕ))
  have hi (i : Fin K) : C i = (-1 : ℝ) ^ ((D i).card + l i) * |C i| := by
    apply pd5_ghostGroupCoeff_abs_sign F S ρ hρ j i _ _ _ _ hη hq (hV i)
    intro p hp
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hp
    exact hν i _ (new i k).property
  change (∏ i, C i) = _ * |∏ i, C i|
  calc
    _ = ∏ i, (-1 : ℝ) ^ ((D i).card + l i) * |C i| :=
      Finset.prod_congr rfl (fun i _ => hi i)
    _ = (-1 : ℝ) ^ ((∑ i, (D i).card) + ∑ i, l i) * |∏ i, C i| := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.abs_prod]
      rw [Finset.sum_add_distrib]

/-- The real-valued target memory average of a delta. Its normalizing cardinal is nonzero
because each memory-coordinate permutation group contains the identity. -/
noncomputable def pd5_ghostDeltaReal {x : ℝ} {K : ℕ} (u t : MemPoint x K) : ℝ :=
  (Fintype.card (MemoryPermutation u) : ℝ)⁻¹ *
    ∑ σ : MemoryPermutation u, if memoryPermute u σ = t then 1 else 0

theorem pd5_ghostDeltaReal_nonneg {x : ℝ} {K : ℕ} (u t : MemPoint x K) :
    0 ≤ pd5_ghostDeltaReal u t := by
  unfold pd5_ghostDeltaReal
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro σ _
    split_ifs <;> norm_num

theorem pd5_memorySym_delta_eq_real {x : ℝ} {K : ℕ} (u t : MemPoint x K) :
    memorySym (fun v => if v = t then (1 : ℂ) else 0) u = (pd5_ghostDeltaReal u t : ℂ) := by
  unfold memorySym pd5_ghostDeltaReal
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> norm_num

/-- A projected target delta permits the literal infinite ghost sum to be cut to finite
batch lengths. The target size hypothesis is the domain condition justifying this cutoff. -/
theorem pd5_twisted_ghost_kernel_finite {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (j B : ℕ) (W : BirthLog K → ℂ) (s t : MemPoint S.x K) (ht : memSize t ≤ B) :
    memKernel (fun f => pd5_ghostBirthTwist F S ρ j W (memorySym f)) s t =
      ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
        ∑ l ∈ pd5_boundedLengths K B,
          pd5_ghostLengthTerm F S ρ j (s, []) D l
            (logTrunc (some B) (fun uL => W uL.2 *
              memorySym (fun u => if u = t then (1 : ℂ) else 0) uL.1)) := by
  let f : LogPoint S.x K → ℂ := fun uL => W uL.2 *
    memorySym (fun u => if u = t then (1 : ℂ) else 0) uL.1
  have hcut : logTrunc (some B) f = f := by
    funext uL
    by_cases hu : memSize uL.1 ≤ B
    · simp [logTrunc, hu]
    · have hn : memSize uL.1 ≠ memSize t := by omega
      have hd := pd5_memorySym_delta_size_ne uL.1 t hn
      simp [logTrunc, hu, f, hd]
  change logGhost F S ρ j f (s, []) = _
  calc
    _ = logGhost F S ρ j (logTrunc (some B) f) (s, []) :=
      congrArg (fun g => logGhost F S ρ j g (s, [])) hcut.symm
    _ = _ := pd5_logGhost_truncated_finite F S ρ j B f (s, [])

/-- Whenever a ghost choice can contribute to the averaged target delta, its sign is the
single endpoint-size parity. Choices with another output size have zero delta weight. -/
theorem pd5_ghost_choice_delta_sign {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (hρ : 0 < ρ) (j : ℕ) (s t : MemPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
    (hη : 0 ≤ memoryEta S.x F.q_d j) (hq : 0 ≤ memoryQ S.x F.q_d j)
    (hV : ∀ i, 0 ≤ bandMass S.x (F.a i))
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p) :
    let u := (pd5_ghostOutput F S (s, []) D l new j).1
    let C := ∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1)
      (D i).card (l i) (List.ofFn fun k => (new i k : ℕ))
    (C : ℂ) * memorySym (fun v => if v = t then (1 : ℂ) else 0) u =
      (-1 : ℂ) ^ (memSize s + memSize t) * (|C| * pd5_ghostDeltaReal u t : ℝ) := by
  dsimp only
  let u := (pd5_ghostOutput F S (s, []) D l new j).1
  let C := ∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1)
    (D i).card (l i) (List.ofFn fun k => (new i k : ℕ))
  change (C : ℂ) * memorySym (fun v => if v = t then (1 : ℂ) else 0) u = _
  by_cases hsize : memSize u = memSize t
  · have hbal : memSize u + (∑ i, (D i).card) = memSize s + ∑ i, l i := by
      simpa [u, pd5_ghostOutput] using
        pd5_ghost_output_size_balance s D l (fun i k => (new i k : ℕ))
    have hsign := pd5_ghost_sign_parity (memSize s) (memSize u)
      (∑ i, (D i).card) (∑ i, l i) hbal
    have hC := pd5_ghostWeight_abs_sign F S ρ hρ j s D l new hη hq hV hν
    change C = (-1 : ℝ) ^ ((∑ i, (D i).card) + ∑ i, l i) * |C| at hC
    rw [hsign, hsize] at hC
    have hcc : (C : ℂ) = (-1 : ℂ) ^ (memSize s + memSize t) * ((|C| : ℝ) : ℂ) := by
      exact_mod_cast hC
    rw [pd5_memorySym_delta_eq_real, hcc]
    push_cast
    ring
  · have hd := pd5_memorySym_delta_size_ne u t hsize
    have hr : pd5_ghostDeltaReal u t = 0 := by
      have hc : (pd5_ghostDeltaReal u t : ℂ) = 0 :=
        (pd5_memorySym_delta_eq_real u t).symm.trans hd
      simpa using congrArg Complex.re hc
    rw [hd, hr]
    simp

/-- Nonnegative mass of one finite ghost choice after averaging the target delta. -/
noncomputable def pd5_ghostChoiceMass {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (j B : ℕ) (s t : MemPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) : ℝ :=
  let u := (pd5_ghostOutput F S (s, []) D l new j).1
  if (∀ i, D i ⊆ hitIndices (s.2.2 i) s.1) ∧ memSize u ≤ B then
    |∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1)
      (D i).card (l i) (List.ofFn fun k => (new i k : ℕ))| * pd5_ghostDeltaReal u t
  else 0

theorem pd5_ghostChoiceMass_nonneg {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (j B : ℕ) (s t : MemPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) :
    0 ≤ pd5_ghostChoiceMass F S ρ j B s t D l new := by
  dsimp only [pd5_ghostChoiceMass]
  split_ifs
  · exact mul_nonneg (abs_nonneg _) (pd5_ghostDeltaReal_nonneg _ _)
  · exact le_rfl

/-- Factor the fixed endpoint sign out of one finite batch-length row. -/
theorem pd5_ghost_length_factor {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (hρ : 0 < ρ) (j B : ℕ) (W : BirthLog K → ℂ) (s t : MemPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (l : Fin K → ℕ)
    (hη : 0 ≤ memoryEta S.x F.q_d j) (hq : 0 ≤ memoryQ S.x F.q_d j)
    (hV : ∀ i, 0 ≤ bandMass S.x (F.a i))
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p) :
    pd5_ghostLengthTerm F S ρ j (s, []) D l
      (logTrunc (some B) (fun uL => W uL.2 *
        memorySym (fun u => if u = t then (1 : ℂ) else 0) uL.1)) =
      (-1 : ℂ) ^ (memSize s + memSize t) *
        ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
          (pd5_ghostChoiceMass F S ρ j B s t D l new : ℂ) *
            W (pd5_ghostOutput F S (s, []) D l new j).2 := by
  unfold pd5_ghostLengthTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro new _
  let u := (pd5_ghostOutput F S (s, []) D l new j).1
  let C := ∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1)
    (D i).card (l i) (List.ofFn fun k => (new i k : ℕ))
  by_cases hd : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1
  · by_cases hc : memSize u ≤ B
    · simp only [if_pos hd]
      have hfactor := pd5_ghost_choice_delta_sign F S ρ hρ j s t D l new hη hq hV hν
      change (C : ℂ) * memorySym (fun v => if v = t then (1 : ℂ) else 0) u =
        (-1 : ℂ) ^ (memSize s + memSize t) * (|C| * pd5_ghostDeltaReal u t : ℝ) at hfactor
      have hm : pd5_ghostChoiceMass F S ρ j B s t D l new = |C| * pd5_ghostDeltaReal u t := by
        simp [pd5_ghostChoiceMass, hd, hc, u, C]
      rw [hm]
      change (C : ℂ) * (if memSize u ≤ B then
        W (pd5_ghostOutput F S (s, []) D l new j).2 *
          memorySym (fun v => if v = t then (1 : ℂ) else 0) u else 0) = _
      rw [if_pos hc]
      calc
        _ = ((C : ℂ) * memorySym (fun v => if v = t then (1 : ℂ) else 0) u) *
            W (pd5_ghostOutput F S (s, []) D l new j).2 := by ring
        _ = _ := by rw [hfactor]; ring
    · have hm : pd5_ghostChoiceMass F S ρ j B s t D l new = 0 := by
        simp [pd5_ghostChoiceMass, hc, u]
      simp [hd, pd5_ghostWeight, logTrunc, hc, hm, u]
  · simp [hd, pd5_ghostChoiceMass]

/-- The full truncated ghost kernel has one fixed sign multiplying a finite positive choice
sum, with every local phase left on the individual choice. -/
theorem pd5_twisted_ghost_kernel_factor {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (hρ : 0 < ρ) (j B : ℕ) (W : BirthLog K → ℂ) (s t : MemPoint S.x K)
    (ht : memSize t ≤ B)
    (hη : 0 ≤ memoryEta S.x F.q_d j) (hq : 0 ≤ memoryQ S.x F.q_d j)
    (hV : ∀ i, 0 ≤ bandMass S.x (F.a i))
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p) :
    memKernel (fun f => pd5_ghostBirthTwist F S ρ j W (memorySym f)) s t =
      (-1 : ℂ) ^ (memSize s + memSize t) *
        ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
          ∑ l ∈ pd5_boundedLengths K B,
            ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
              (pd5_ghostChoiceMass F S ρ j B s t D l new : ℂ) *
                W (pd5_ghostOutput F S (s, []) D l new j).2 := by
  rw [pd5_twisted_ghost_kernel_finite F S ρ j B W s t ht]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro l hl
  simpa only [Finset.mul_sum] using
    pd5_ghost_length_factor F S ρ hρ j B W s t D l hη hq hV hν

/-- Bounded local phases are dominated by the untwisted projected ghost kernel, because
all its contributing finite choices have one endpoint-size sign. -/
theorem pd5_twisted_ghost_kernel_domination {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (hρ : 0 < ρ) (j B : ℕ) (W : BirthLog K → ℂ) (hW : ∀ log, ‖W log‖ ≤ 1)
    (s t : MemPoint S.x K) (ht : memSize t ≤ B)
    (hη : 0 ≤ memoryEta S.x F.q_d j) (hq : 0 ≤ memoryQ S.x F.q_d j)
    (hV : ∀ i, 0 ≤ bandMass S.x (F.a i))
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p) :
    ‖memKernel (fun f => pd5_ghostBirthTwist F S ρ j W (memorySym f)) s t‖ ≤
      ‖memKernel (fun f => memGhost F S ρ j (memorySym f)) s t‖ := by
  let A := pd5_ghostChoiceMass F S ρ j B s t
  let ε : ℂ := (-1 : ℂ) ^ (memSize s + memSize t)
  let total : ℝ := ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
    ∑ l ∈ pd5_boundedLengths K B,
      ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), A D l new
  have hA D l new : 0 ≤ A D l new := pd5_ghostChoiceMass_nonneg F S ρ j B s t D l new
  have ht0 : 0 ≤ total :=
    Finset.sum_nonneg fun D _ => Finset.sum_nonneg fun l _ =>
      Finset.sum_nonneg fun new _ => hA D l new
  have hε : ‖ε‖ = 1 := by simp [ε]
  have hbase : memKernel (fun f => pd5_ghostBirthTwist F S ρ j (fun _ => 1) (memorySym f)) s t =
      memKernel (fun f => memGhost F S ρ j (memorySym f)) s t := by
    simp only [memKernel, pd5_ghostBirthTwist, memGhost, plainOp, one_mul]
  have hr : ‖memKernel (fun f => memGhost F S ρ j (memorySym f)) s t‖ = total := by
    rw [← hbase, pd5_twisted_ghost_kernel_factor F S ρ hρ j B (fun _ => 1) s t ht hη hq hV hν]
    simp only [mul_one]
    have hc : (∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
        ∑ l ∈ pd5_boundedLengths K B,
          ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
            (A D l new : ℂ)) = (total : ℂ) := by
      dsimp [total]
      push_cast
      rfl
    change ‖ε * _‖ = total
    rw [hc, norm_mul, hε, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  rw [hr, pd5_twisted_ghost_kernel_factor F S ρ hρ j B W s t ht hη hq hV hν]
  change ‖ε * _‖ ≤ total
  rw [norm_mul, hε, one_mul]
  calc
    _ ≤ ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
        ‖∑ l ∈ pd5_boundedLengths K B,
          ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
            (A D l new : ℂ) * W (pd5_ghostOutput F S (s, []) D l new j).2‖ := norm_sum_le _ _
    _ ≤ total := by
      apply Finset.sum_le_sum
      intro D _
      calc
        _ ≤ ∑ l ∈ pd5_boundedLengths K B,
            ‖∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
              (A D l new : ℂ) * W (pd5_ghostOutput F S (s, []) D l new j).2‖ := norm_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro l hl
          calc
            _ ≤ ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
                ‖(A D l new : ℂ) * W (pd5_ghostOutput F S (s, []) D l new j).2‖ := norm_sum_le _ _
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro new _
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA D l new)]
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left (hW _) (hA D l new)

end
end ArtinPrimitiveRoots.TypeII.PD
