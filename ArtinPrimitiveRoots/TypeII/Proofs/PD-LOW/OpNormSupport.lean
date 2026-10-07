import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDLow.NormSupport
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDLow.GhostDomination
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDLow.ValidSupport

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

/-- Instantiate the finite Schur adapter on the actual memory measure and cutoff space. -/
theorem pd5_memOpNormLE_of_schur {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (v c : ℝ)
    (hv : 0 < v) (hc : 0 ≤ c) (hμ : ∀ s, 0 ≤ memMeasure F S s)
    (hrow : MemRowSchurLE F S B op v c) (hcol : MemColSchurLE F S B op v c)
    (hnull : ∀ s, MemValid F S s → ∀ t, ¬ MemValid F S t → memKernel op s t = 0)
    (hrep : ∀ T : Finset (MemPoint S.x K), ∀ f : MemPoint S.x K → ℂ,
      (∀ u, u ∉ T → f u = 0) → (∀ u ∈ T, memSize u ≤ B) →
      ∀ s, MemValid F S s → memSize s ≤ B → op f s = ∑ t ∈ T, memKernel op s t * f t) :
    MemOpNormLE F S B op c := by
  intro T T' f hf hT hT'
  have hzero (s : MemPoint S.x K) (hs : ¬ MemValid F S s) : memMeasure F S s = 0 := by
    simp [memMeasure, hs]
  have hw (s : MemPoint S.x K) : 0 < v ^ memSize s := pow_pos hv _
  have h := pd5_schur_norm_from_finite_kernel (MemValid F S) (memMeasure F S)
    (fun s => v ^ memSize s) memSize B op (memKernel op) c c hμ hw hc hc
    hzero hnull hrep hrow hcol T T' f hf hT hT'
  simpa only [memNormSqOn, pow_two] using h

/-- Transfer the upstream ghost Schur bounds through common-sign domination and the finite
supported-function kernel expansion. -/
theorem pd5_twisted_ghost_norm {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (hρ : 0 < ρ) (j B : ℕ) (W : BirthLog K → ℂ) (hW : ∀ log, ‖W log‖ ≤ 1)
    (v c : ℝ) (hv : 0 < v) (hc : 0 ≤ c) (hμ : ∀ s, 0 ≤ memMeasure F S s)
    (hη : 0 ≤ memoryEta S.x F.q_d j) (hq : 0 ≤ memoryQ S.x F.q_d j)
    (hV : ∀ i, 0 ≤ bandMass S.x (F.a i))
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hrow : MemRowSchurLE_sym F S B (memGhost F S ρ j) v c)
    (hcol : MemColSchurLE_sym F S B (memGhost F S ρ j) v c)
    (hrep : ∀ T : Finset (MemPoint S.x K), ∀ f : MemPoint S.x K → ℂ,
      (∀ u, u ∉ T → f u = 0) → (∀ u ∈ T, memSize u ≤ B) →
      ∀ s, MemValid F S s → memSize s ≤ B →
        pd5_ghostBirthTwist F S ρ j W (memorySym f) s =
          ∑ t ∈ T, memKernel (fun g => pd5_ghostBirthTwist F S ρ j W (memorySym g)) s t * f t) :
    MemOpNormLE_sym F S B (pd5_ghostBirthTwist F S ρ j W) c := by
  let op := fun f => pd5_ghostBirthTwist F S ρ j W (memorySym f)
  change MemOpNormLE F S B op c
  apply pd5_memOpNormLE_of_schur F S B op v c hv hc hμ
  · intro s hs hsize T hT
    calc
      _ ≤ ∑ t ∈ T, ‖memKernel (fun f => memGhost F S ρ j (memorySym f)) s t‖ * v ^ memSize t := by
        apply Finset.sum_le_sum
        intro t ht
        exact mul_le_mul_of_nonneg_right
          (pd5_twisted_ghost_kernel_domination F S ρ hρ j B W hW s t (hT t ht) hη hq hV hν)
          (pow_nonneg hv.le _)
      _ ≤ _ := hrow s hs hsize T hT
  · intro t ht hsize T hT
    calc
      _ ≤ ∑ s ∈ T, memMeasure F S s *
          ‖memKernel (fun f => memGhost F S ρ j (memorySym f)) s t‖ * v ^ memSize s := by
        apply Finset.sum_le_sum
        intro s hs
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pd5_twisted_ghost_kernel_domination F S ρ hρ j B W hW s t hsize hη hq hV hν)
            (hμ s)) (pow_nonneg hv.le _)
      _ ≤ _ := hcol t ht hsize T hT
  · intro s hs t ht
    exact pd5_twisted_ghost_kernel_invalid F S ρ j W s t hs ht
  · exact hrep

end
end ArtinPrimitiveRoots.TypeII.PD
