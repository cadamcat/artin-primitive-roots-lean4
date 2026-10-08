import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».GhostDomination
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».ValidSupport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

theorem pd5_supported_expansion {α : Type*} [DecidableEq α] (T : Finset α)
    (f : α → ℂ) (hf : ∀ u, u ∉ T → f u = 0) (u : α) :
    f u = ∑ t ∈ T, f t * (if u = t then (1 : ℂ) else 0) := by
  by_cases hu : u ∈ T
  · symm
    rw [Finset.sum_eq_single u]
    · simp
    · intro t ht htu
      simp [Ne.symm htu]
    · intro hnot
      exact (hnot hu).elim
  · rw [hf u hu]
    symm
    apply Finset.sum_eq_zero
    intro t ht
    have hne : u ≠ t := fun he => hu (he ▸ ht)
    simp [hne]

theorem pd5_memorySym_supported_expansion {x : ℝ} {K : ℕ}
    (T : Finset (MemPoint x K)) (f : MemPoint x K → ℂ)
    (hf : ∀ u, u ∉ T → f u = 0) (u : MemPoint x K) :
    memorySym f u = ∑ t ∈ T, f t * memorySym (fun v => if v = t then (1 : ℂ) else 0) u := by
  unfold memorySym
  calc
    _ = (Fintype.card (MemoryPermutation u) : ℂ)⁻¹ *
        ∑ σ : MemoryPermutation u, ∑ t ∈ T, f t *
          (if memoryPermute u σ = t then (1 : ℂ) else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      exact pd5_supported_expansion T f hf _
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro σ _
      ring

theorem pd5_memorySym_zero_of_size_gt {x : ℝ} {K : ℕ} (B : ℕ)
    (T : Finset (MemPoint x K)) (f : MemPoint x K → ℂ)
    (hf : ∀ u, u ∉ T → f u = 0) (hT : ∀ u ∈ T, memSize u ≤ B)
    (u : MemPoint x K) (hu : B < memSize u) : memorySym f u = 0 := by
  have hz : (∑ σ : MemoryPermutation u, f (memoryPermute u σ)) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    apply hf
    intro hmem
    have hsize := hT _ hmem
    rw [pd5_memSize_memoryPermute] at hsize
    omega
  change (Fintype.card (MemoryPermutation u) : ℂ)⁻¹ * _ = 0
  rw [hz, mul_zero]

theorem pd5_ghost_supported_kernel {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (j B : ℕ) (W : BirthLog K → ℂ) (T : Finset (MemPoint S.x K))
    (f : MemPoint S.x K → ℂ) (hf : ∀ u, u ∉ T → f u = 0)
    (hT : ∀ u ∈ T, memSize u ≤ B) (s : MemPoint S.x K) :
    pd5_ghostBirthTwist F S ρ j W (memorySym f) s =
      ∑ t ∈ T, memKernel (fun g => pd5_ghostBirthTwist F S ρ j W (memorySym g)) s t * f t := by
  let g : LogPoint S.x K → ℂ := fun uL => W uL.2 * memorySym f uL.1
  let d : MemPoint S.x K → LogPoint S.x K → ℂ := fun t uL =>
    W uL.2 * memorySym (fun v => if v = t then (1 : ℂ) else 0) uL.1
  have hg : g = fun uL => ∑ t ∈ T, f t * d t uL := by
    funext uL
    dsimp [g, d]
    rw [pd5_memorySym_supported_expansion T f hf, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hcut : logTrunc (some B) g = g := by
    funext uL
    by_cases hu : memSize uL.1 ≤ B
    · simp [logTrunc, hu]
    · have hz := pd5_memorySym_zero_of_size_gt B T f hf hT uL.1 (by omega)
      simp [logTrunc, hu, g, hz]
  have hcutd (t : MemPoint S.x K) (ht : t ∈ T) : logTrunc (some B) (d t) = d t := by
    funext uL
    by_cases hu : memSize uL.1 ≤ B
    · simp [logTrunc, hu]
    · have hn : memSize uL.1 ≠ memSize t := by have h := hT t ht; omega
      have hz := pd5_memorySym_delta_size_ne uL.1 t hn
      simp [logTrunc, hu, d, hz]
  change logGhost F S ρ j g (s, []) = _
  calc
    _ = logGhost F S ρ j (logTrunc (some B) g) (s, []) :=
      congrArg (fun v => logGhost F S ρ j v (s, [])) hcut.symm
    _ = ∑ t ∈ T, f t * logGhost F S ρ j (logTrunc (some B) (d t)) (s, []) := by
      rw [hg]
      exact pd5_logGhost_finsetSum F S ρ j B T f d (s, [])
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hcutd t ht]
      change f t * memKernel (fun g => pd5_ghostBirthTwist F S ρ j W (memorySym g)) s t = _
      exact mul_comm _ _

theorem pd5_edge_supported_kernel {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (w : ArchRoot) (j : ℕ) (W : BirthLog K → ℂ) (T : Finset (MemPoint S.x K))
    (f : MemPoint S.x K → ℂ) (hf : ∀ u, u ∉ T → f u = 0)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) (s : MemPoint S.x K) :
    pd5_edgeBirthTwist F S ρ w j W (memorySym f) s =
      ∑ t ∈ T, memKernel (fun g => pd5_edgeBirthTwist F S ρ w j W (memorySym g)) s t * f t := by
  let d : MemPoint S.x K → LogPoint S.x K → ℂ := fun t uL =>
    W uL.2 * memorySym (fun v => if v = t then (1 : ℂ) else 0) uL.1
  have hg : (fun uL : LogPoint S.x K => W uL.2 * memorySym f uL.1) =
      fun uL => ∑ t ∈ T, f t * d t uL := by
    funext uL
    dsimp [d]
    rw [pd5_memorySym_supported_expansion T f hf, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  unfold pd5_edgeBirthTwist
  rw [hg, pd5_logEdge_full_finsetSum F S ρ w j T f d hbox (s, [])]
  apply Finset.sum_congr rfl
  intro t ht
  change f t * memKernel (fun g => pd5_edgeBirthTwist F S ρ w j W (memorySym g)) s t = _
  exact mul_comm _ _

end
end ArtinPrimitiveRoots.TypeII.PD
