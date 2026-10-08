import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedInduction

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- Closed form of the guided value from depth `k`. -/
theorem guidedV_closed {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (H : PDLifeAssignment F S γ) (k : ℕ)
    (hk : k ≤ pathLength S.x) :
    guidedV F S ρ w B γ H k =
      (∏ j ∈ Finset.univ.filter (fun j : Fin (pathLength S.x + 1) =>
          pathLength S.x - k ≤ j.val),
        cutF B (pdLifeMemorySize F S γ H false j) * cutF B (pdLifeMemorySize F S γ H true j) *
          ((ghostAt F S ρ γ H j : ℝ) : ℂ)) *
      ∏ j ∈ Finset.univ.filter (fun j : Fin (pathLength S.x) => pathLength S.x - k ≤ j.val),
        ((edgeAt F S ρ γ H j : ℝ) : ℂ) * edgeGeo F S w γ j := by
  induction k with
  | zero =>
    have h1 : Finset.univ.filter (fun j : Fin (pathLength S.x + 1) =>
        pathLength S.x - 0 ≤ j.val) = {Fin.last _} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Fin.ext_iff, Fin.val_last]
      have := x.isLt
      omega
    have h2 : Finset.univ.filter (fun j : Fin (pathLength S.x) =>
        pathLength S.x - 0 ≤ j.val) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_le]
      have := x.isLt
      omega
    rw [h1, h2, Finset.prod_singleton, Finset.prod_empty]
    unfold guidedV
    ring
  | succ k ih =>
    have hjN : pathLength S.x - (k + 1) < pathLength S.x := by omega
    have h1 : Finset.univ.filter (fun j : Fin (pathLength S.x + 1) =>
        pathLength S.x - (k + 1) ≤ j.val) =
        insert ⟨pathLength S.x - (k + 1), by omega⟩ (Finset.univ.filter
          (fun j : Fin (pathLength S.x + 1) => pathLength S.x - k ≤ j.val)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have h2 : Finset.univ.filter (fun j : Fin (pathLength S.x) =>
        pathLength S.x - (k + 1) ≤ j.val) =
        insert ⟨pathLength S.x - (k + 1), hjN⟩ (Finset.univ.filter
          (fun j : Fin (pathLength S.x) => pathLength S.x - k ≤ j.val)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    rw [h1, h2, Finset.prod_insert, Finset.prod_insert, guidedV.eq_2, dif_pos hjN,
      ih (by omega)]
    · ring
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]; omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]; omega

/-- The product of all cutoff indicators is the selector of `pdRawHistorySum`. -/
theorem cut_prod {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (B : Option ℕ) (H : PDLifeAssignment F S γ) :
    (∏ j : Fin (pathLength S.x + 1),
      cutF B (pdLifeMemorySize F S γ H false j) * cutF B (pdLifeMemorySize F S γ H true j)) =
      (match B with
       | none => 1
       | some b => if pdLifeMaxMemory F S γ H ≤ b then 1 else 0) := by
  cases B with
  | none => simp [cutF]
  | some b =>
    simp only [cutF]
    simp_rw [ite_zero_mul_ite_zero, mul_one]
    rw [Finset.prod_ite_zero, Finset.prod_const_one]
    unfold pdLifeMaxMemory
    simp only [Finset.mem_univ, true_implies, Finset.sup_le_iff, max_le_iff]

/-- The full guided value. -/
theorem guidedV_full {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (H : PDLifeAssignment F S γ) :
    guidedV F S ρ w B γ H (pathLength S.x) =
      (match B with
       | none => 1
       | some b => if pdLifeMaxMemory F S γ H ≤ b then 1 else 0) *
        ((∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
            ((∏ j, lifeGhostLocal F S ρ γ i p.1 (H i p) j) *
              ∏ j, lifeEdgeLocal F S ρ γ i p.1 (H i p) j) : ℝ) : ℂ) *
        ∏ j : Fin (pathLength S.x), edgeGeo F S w γ j := by
  rw [guidedV_closed F S ρ w B γ H _ le_rfl, ← cut_prod]
  have h1 : Finset.univ.filter (fun j : Fin (pathLength S.x + 1) =>
      pathLength S.x - pathLength S.x ≤ j.val) = Finset.univ := by
    ext x; simp
  have h2 : Finset.univ.filter (fun j : Fin (pathLength S.x) =>
      pathLength S.x - pathLength S.x ≤ j.val) = Finset.univ := by
    ext x; simp
  rw [h1, h2, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hswap : (∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
      ((∏ j, lifeGhostLocal F S ρ γ i p.1 (H i p) j) *
        ∏ j, lifeEdgeLocal F S ρ γ i p.1 (H i p) j)) =
      (∏ j, ghostAt F S ρ γ H j) * ∏ j, edgeAt F S ρ γ H j := by
    unfold ghostAt edgeAt
    rw [Finset.prod_comm (s := Finset.univ (α := Fin (pathLength S.x + 1))),
      Finset.prod_comm (s := Finset.univ (α := Fin (pathLength S.x))),
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_comm, Finset.prod_comm (s := Finset.univ (α := Fin (pathLength S.x))),
      ← Finset.prod_mul_distrib]
  rw [hswap]
  push_cast
  simp only [Finset.prod_mul_distrib]
  ring

/-- The initial logged state is a life state of every assignment. -/
theorem lifeState_initial {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ)
    (hnd : ((initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
      MemPoint S.x K)).map Prod.snd).Nodup) :
    IsLifeState F S γ H ⟨0, by omega⟩
      ((((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) : MemPoint S.x K),
        initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
          MemPoint S.x K)) := by
  refine ⟨rfl, fun i => List.nodup_nil, ?_, hnd, ?_⟩
  · intro i q
    simp only [List.not_mem_nil, false_iff, not_exists, not_and]
    intro hp hpend
    exact absurd hpend (pending_false_zero S γ _ _)
  · intro p
    have hlog : p ∈ (initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
        MemPoint S.x K)).map Prod.snd ↔ IsActiveAt γ p ⟨0, by omega⟩ := by
      unfold initialLog IsActiveAt
      simp only [List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_finRange, true_and,
        List.mem_map, Function.comp_def]
    rw [hlog]
    unfold lifeBornBefore
    constructor
    · intro h; exact Or.inl ⟨_, le_rfl, h⟩
    · rintro (⟨j', hj', h⟩ | ⟨i, a, ha, -⟩)
      · have : j' = ⟨0, by omega⟩ := by
          apply Fin.ext
          have h0 := Fin.le_def.mp hj'
          simp only [Fin.val_mk] at h0 ⊢
          omega
        rw [this] at h; exact h
      · exact absurd (Fin.lt_def.mp ha) (by simp)

/-- The initial active measure is the product of the initial local factors. -/
theorem initial_measure {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i'))) :
    (∏ i : Fin K, ∏ j : Fin (slotCount S.x),
        memoryNu S.x K F.a F.q_d i ((γ ⟨0, by omega⟩).2 i j)) =
      ∏ i : Fin K, ∏ p : primeBand S.x (F.a i), lifeInitLocal F S γ i p.1 := by
  have hv := (hγ.1 ⟨0, by omega⟩).2
  apply Finset.prod_congr rfl
  intro i _
  have hinj : Function.Injective ((γ ⟨0, by omega⟩).2 i) := by
    intro a b hab
    by_contra hne
    exact hv.2 i a b hne hab
  rw [← Finset.prod_image (f := memoryNu S.x K F.a F.q_d i) (fun a _ b _ h => hinj h)]
  rw [Finset.prod_coe_sort (primeBand S.x (F.a i)) (fun p => lifeInitLocal F S γ i p)]
  unfold lifeInitLocal
  rw [← Finset.prod_filter]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext p
  rw [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨j, -, rfl⟩
    exact ⟨(hv.1 i j).2, i, j, rfl⟩
  · rintro ⟨hp, i', j, hj⟩
    by_cases hii : i' = i
    · subst hii; exact ⟨j, Finset.mem_univ _, hj⟩
    · exact absurd hp (Finset.disjoint_left.mp (hBands i' i hii) (hj ▸ (hv.1 i' j).2))

/-- The memory selector of the raw history sum, as a real number. -/
def selR {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) (B : Option ℕ)
    (H : PDLifeAssignment F S γ) : ℝ :=
  match B with
  | none => 1
  | some b => if pdLifeMaxMemory F S γ H ≤ b then 1 else 0

theorem rawHistorySum_eq {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (γ : EnvPath S.x K)
    (B : Option ℕ) :
    pdRawHistorySum F S ρ γ B =
      ∑ H : PDLifeAssignment F S γ, selR F S γ B H * pdRawAssignmentCharge F S ρ γ H := by
  unfold pdRawHistorySum
  apply Finset.sum_congr rfl
  intro H _
  cases B with
  | none => simp [selR]
  | some b => dsimp only [selR]; split_ifs <;> simp

theorem sel_cast {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) (B : Option ℕ)
    (H : PDLifeAssignment F S γ) :
    (match B with
     | none => (1 : ℂ)
     | some b => if pdLifeMaxMemory F S γ H ≤ b then 1 else 0) =
      ((selR F S γ B H : ℝ) : ℂ) := by
  cases B with
  | none => simp [selR]
  | some b => dsimp only [selR]; split_ifs <;> simp

/-- **R7 (conditional).** The birth identity, given the decomposition of the finite history
sum from the initial state into guided sums. -/
theorem birth_assembly {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (hMass : ∀ i, 0 < bandMass S.x (F.a i)) (hN : 0 < pathLength S.x)
    (hnd : ((initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
      MemPoint S.x K)).map Prod.snd).Nodup)
    (hDecomp : finiteHistoryFn F S ρ w B γ (pathLength S.x)
        ((((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) : MemPoint S.x K),
          initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
            MemPoint S.x K)) =
      ∑ H : PDLifeAssignment F S γ, guidedTraceSum F S ρ w B γ H (pathLength S.x)
        ((((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) : MemPoint S.x K),
          initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
            MemPoint S.x K))) :
    (((∏ i : Fin K, ∏ j : Fin (slotCount S.x),
        memoryNu S.x K F.a F.q_d i ((γ ⟨0, by omega⟩).2 i j) : ℝ)) : ℂ) *
      logHistoryFn F S ρ w B (some γ) distinctWeight (pathLength S.x)
        ((((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) : MemPoint S.x K),
          initialLog (((γ ⟨0, by omega⟩).1, (γ ⟨0, by omega⟩).2, fun _ => []) :
            MemPoint S.x K)) =
      pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
        ((pdActiveNormalization F S)⁻¹ * pdRawHistorySum F S ρ γ B : ℝ) := by
  have e0 : (⟨pathLength S.x - pathLength S.x, by omega⟩ : Fin (pathLength S.x + 1)) =
      ⟨0, by omega⟩ := Fin.ext (Nat.sub_self _)
  rw [logHistoryFn_eq_finite F S ρ w B γ _ le_rfl, hDecomp]
  rw [Finset.sum_congr rfl (fun H _ => guidedTraceSum_eq F S ρ w B γ hγ hBands H _ le_rfl _
    (by rw [e0]; exact lifeState_initial F S γ H hnd))]
  simp only [guidedV_full, sel_cast]
  rw [edgeGeo_prod F S w γ hγ hBands hMass hN, initial_measure F S γ hγ hBands,
    rawHistorySum_eq]
  unfold pdRawAssignmentCharge
  simp only [rawPrimeLifeCharge_eq_local]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  simp only [Finset.prod_mul_distrib]
  ring

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
