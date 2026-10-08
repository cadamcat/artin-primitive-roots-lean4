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

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
