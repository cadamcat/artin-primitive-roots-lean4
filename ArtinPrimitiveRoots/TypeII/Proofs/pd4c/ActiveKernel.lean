import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CoreTranspose

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

abbrev Pd4cActivePermutation (x : ℝ) (K : ℕ) := Fin K → Equiv.Perm (Fin (slotCount x))

def pd4c_activePermute {x : ℝ} {K : ℕ} (s : MemPoint x K) (σ : Pd4cActivePermutation x K) : MemPoint x K :=
  (s.1, permuteLists σ s.2.1, s.2.2)

def pd4c_activeInverse (x : ℝ) (K : ℕ) : Pd4cActivePermutation x K ≃ Pd4cActivePermutation x K := {
  toFun := fun σ i => (σ i).symm
  invFun := fun σ i => (σ i).symm
  left_inv := by intro σ; funext i; simp
  right_inv := by intro σ; funext i; simp
}

def pd4c_activeSym {K : ℕ} (F : PDFix K) (S : PDScale) (f : MemPoint S.x K → ℂ)
    (s : MemPoint S.x K) : ℂ :=
  (permCount S.x K : ℂ)⁻¹ * ∑ σ : Pd4cActivePermutation S.x K, f (pd4c_activePermute s σ)

theorem pd4c_activePermute_valid {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (hs : MemValid F S s) (σ : Pd4cActivePermutation S.x K) :
    MemValid F S (pd4c_activePermute s σ) :=
  ⟨hs.1, fun i j => hs.2.1 i (σ i j), hs.2.2⟩

theorem pd4c_activePermute_measure {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (σ : Pd4cActivePermutation S.x K) :
    memMeasure F S (pd4c_activePermute s σ) = memMeasure F S s :=
  pd4c_memMeasure_activePermute F S s σ

theorem pd4c_permuteLists_inverse {x : ℝ} {K : ℕ} (p : PrimeLists x K)
    (σ : Pd4cActivePermutation x K) :
    permuteLists (pd4c_activeInverse x K σ) (permuteLists σ p) = p := by
  funext i j
  simp [permuteLists, pd4c_activeInverse]

/-- Reindex a projected point mass through an active-slot permutation. -/
theorem pd4c_activePermute_projected_delta {x : ℝ} {K : ℕ} (s t : MemPoint x K)
    (σ : Pd4cActivePermutation x K) :
    memorySym (fun u => if u = t then (1 : ℂ) else 0) (pd4c_activePermute s σ) =
      memorySym (fun u => if u = pd4c_activePermute t (pd4c_activeInverse x K σ) then (1 : ℂ) else 0) s := by
  have heq : permuteLists σ s.2.1 = t.2.1 ↔ s.2.1 = permuteLists (pd4c_activeInverse x K σ) t.2.1 := by
    constructor
    · intro h
      have hh := congrArg (permuteLists (pd4c_activeInverse x K σ)) h
      rw [pd4c_permuteLists_inverse] at hh
      exact hh
    · intro h
      rw [h]
      funext i j
      simp [permuteLists, pd4c_activeInverse]
  rw [pd4c_memorySym_delta_factor, pd4c_memorySym_delta_factor]
  change (if s.1 = t.1 ∧ permuteLists σ s.2.1 = t.2.1 then
      ∏ i, pd4c_listDelta (t.2.2 i) (s.2.2 i) else 0) =
    if s.1 = t.1 ∧ s.2.1 = permuteLists (pd4c_activeInverse x K σ) t.2.1 then
      ∏ i, pd4c_listDelta (t.2.2 i) (s.2.2 i) else 0
  by_cases h : s.1 = t.1 ∧ permuteLists σ s.2.1 = t.2.1
  · rw [if_pos h, if_pos ⟨h.1, heq.mp h.2⟩]
  · have hn : ¬ (s.1 = t.1 ∧ s.2.1 = permuteLists (pd4c_activeInverse x K σ) t.2.1) :=
      fun hh => h ⟨hh.1, heq.mpr hh.2⟩
    rw [if_neg h, if_neg hn]

theorem pd4c_activeSym_projected_delta {K : ℕ} (F : PDFix K) (S : PDScale) (t : MemPoint S.x K) :
    pd4c_activeSym F S (memorySym (fun u => if u = t then (1 : ℂ) else 0)) =
      fun s => (permCount S.x K : ℂ)⁻¹ * ∑ σ : Pd4cActivePermutation S.x K,
        memorySym (fun u => if u = pd4c_activePermute t (pd4c_activeInverse S.x K σ) then (1 : ℂ) else 0) s := by
  funext s
  unfold pd4c_activeSym
  congr 1
  exact Finset.sum_congr rfl fun σ hσ => pd4c_activePermute_projected_delta s t σ

theorem pd4c_memEdgePiece_sandwich {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ) (f : MemPoint S.x K → ℂ) :
    memEdgePiece F S ρ w raw St Pr j f =
      pd4c_activeSym F S (pd4c_corePiece F S ρ w raw St Pr j (pd4c_activeSym F S f)) := by
  funext s
  rfl

/-- The projected edge kernel averages the core kernels at the two active-slot endpoints. -/
theorem pd4c_memEdgePiece_kernel_average {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ)
    (s t : MemPoint S.x K) :
    memKernel (fun f => memEdgePiece F S ρ w raw St Pr j (memorySym f)) s t =
      (permCount S.x K : ℂ)⁻¹ ^ 2 *
        ∑ σ : Pd4cActivePermutation S.x K, ∑ τ : Pd4cActivePermutation S.x K,
          pd4c_coreProjectedKernel F S ρ w raw St Pr j
            (pd4c_activePermute s σ) (pd4c_activePermute t (pd4c_activeInverse S.x K τ)) := by
  change memEdgePiece F S ρ w raw St Pr j (memorySym (fun u => if u = t then (1 : ℂ) else 0)) s = _
  rw [pd4c_memEdgePiece_sandwich, pd4c_activeSym_projected_delta, pd4c_corePiece_mul]
  unfold pd4c_activeSym
  have hsum (σ : Pd4cActivePermutation S.x K) :
      pd4c_corePiece F S ρ w raw St Pr j
        (fun u => ∑ τ : Pd4cActivePermutation S.x K,
          memorySym (fun v => if v = pd4c_activePermute t (pd4c_activeInverse S.x K τ) then (1 : ℂ) else 0) u)
        (pd4c_activePermute s σ) =
      ∑ τ : Pd4cActivePermutation S.x K,
        pd4c_coreProjectedKernel F S ρ w raw St Pr j
          (pd4c_activePermute s σ) (pd4c_activePermute t (pd4c_activeInverse S.x K τ)) := by
    apply pd4c_corePiece_sum_at_position F S ρ w raw St Pr j Finset.univ _ t.1
    intro τ u hu
    exact pd4c_projected_delta_zero_pos u _ hu
  simp only [hsum]
  rw [← Finset.mul_sum]
  ring

theorem pd4c_activePair_average_reindex {x : ℝ} {K : ℕ} (s t : MemPoint x K)
    (f : MemPoint x K → MemPoint x K → ℂ) :
    (∑ σ : Pd4cActivePermutation x K, ∑ τ : Pd4cActivePermutation x K,
      f (pd4c_activePermute t (pd4c_activeInverse x K τ)) (pd4c_activePermute s σ)) =
      ∑ σ : Pd4cActivePermutation x K, ∑ τ : Pd4cActivePermutation x K,
        f (pd4c_activePermute t σ) (pd4c_activePermute s (pd4c_activeInverse x K τ)) := by
  rw [Finset.sum_comm]
  have hinner (τ : Pd4cActivePermutation x K) :
      (∑ σ : Pd4cActivePermutation x K,
        f (pd4c_activePermute t (pd4c_activeInverse x K τ)) (pd4c_activePermute s σ)) =
      ∑ σ : Pd4cActivePermutation x K,
        f (pd4c_activePermute t (pd4c_activeInverse x K τ))
          (pd4c_activePermute s (pd4c_activeInverse x K σ)) :=
    (Equiv.sum_comp (pd4c_activeInverse x K)
      (fun σ => f (pd4c_activePermute t (pd4c_activeInverse x K τ)) (pd4c_activePermute s σ))).symm
  simp only [hinner]
  exact Equiv.sum_comp (pd4c_activeInverse x K) (fun σ => ∑ τ : Pd4cActivePermutation x K,
    f (pd4c_activePermute t σ) (pd4c_activePermute s (pd4c_activeInverse x K τ)))

/-- Exact weighted reversal survives both active-slot endpoint averages. -/
theorem pd4c_memEdgePiece_kernel_measure_transpose {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ)
    (s t : MemPoint S.x K) (hs : MemValid F S s) (ht : MemValid F S t)
    (hV : ∀ i : Fin K, bandMass S.x (F.a i) ≠ 0)
    (hbands : ∀ i i' : Fin K, i ≠ i' → Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i'))) :
    (memMeasure F S s : ℂ) * (pd4c_bandFactor F S Pr : ℂ) *
      memKernel (fun f => memEdgePiece F S ρ w raw St Pr j (memorySym f)) s t =
    (memMeasure F S t : ℂ) * (pd4c_bandFactor F S St : ℂ) *
      star (memKernel (fun f => memEdgePiece F S ρ w raw Pr St (j + 1) (memorySym f)) t s) := by
  have hcore (σ τ : Pd4cActivePermutation S.x K) := pd4c_coreProjectedKernel_measure_transpose
    F S ρ w raw St Pr j (pd4c_activePermute s σ)
    (pd4c_activePermute t (pd4c_activeInverse S.x K τ))
    (pd4c_activePermute_valid F S s hs σ)
    (pd4c_activePermute_valid F S t ht (pd4c_activeInverse S.x K τ)) hV hbands
  simp only [pd4c_activePermute_measure] at hcore
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Pd4cActivePermutation S.x K))) rfl
    (fun σ hσ => Finset.sum_congr (s₁ := (Finset.univ : Finset (Pd4cActivePermutation S.x K))) rfl
      (fun τ hτ => hcore σ τ))
  simp only [← Finset.mul_sum] at hsum
  rw [pd4c_activePair_average_reindex s t
    (fun a b => star (pd4c_coreProjectedKernel F S ρ w raw Pr St (j + 1) a b))] at hsum
  have h := congrArg (fun a : ℂ => (permCount S.x K : ℂ)⁻¹ ^ 2 * a) hsum
  rw [pd4c_memEdgePiece_kernel_average, pd4c_memEdgePiece_kernel_average]
  rw [star_mul, star_sum]
  simp only [star_sum]
  have hd : star ((permCount S.x K : ℂ)⁻¹ ^ 2) = (permCount S.x K : ℂ)⁻¹ ^ 2 := by simp
  rw [hd]
  linear_combination h

end

end ArtinPrimitiveRoots.TypeII.PD
