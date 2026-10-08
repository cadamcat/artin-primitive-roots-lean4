import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».SchurSupport

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

/-- Schur-to-operator adapter with validity and cutoff hypotheses explicit. Invalid evaluation
states carry zero measure, and valid evaluations cannot reach invalid inputs. -/
theorem pd5_schur_norm_from_finite_kernel {α : Type*} [DecidableEq α]
    (valid : α → Prop) (μ v : α → ℝ) (size : α → ℕ) (B : ℕ)
    (op : (α → ℂ) → α → ℂ) (k : α → α → ℂ) (a b : ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hv : ∀ s, 0 < v s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hzero : ∀ s, ¬ valid s → μ s = 0)
    (hnull : ∀ s, valid s → ∀ t, ¬ valid t → k s t = 0)
    (hrep : ∀ T : Finset α, ∀ f : α → ℂ,
      (∀ s, s ∉ T → f s = 0) → (∀ s ∈ T, size s ≤ B) →
      ∀ s, valid s → size s ≤ B → op f s = ∑ t ∈ T, k s t * f t)
    (hrow : ∀ s, valid s → size s ≤ B → ∀ T : Finset α,
      (∀ t ∈ T, size t ≤ B) → ∑ t ∈ T, ‖k s t‖ * v t ≤ a * v s)
    (hcol : ∀ t, valid t → size t ≤ B → ∀ T : Finset α,
      (∀ s ∈ T, size s ≤ B) → ∑ s ∈ T, μ s * ‖k s t‖ * v s ≤ b * μ t * v t) :
    ∀ T T' : Finset α, ∀ f : α → ℂ,
      (∀ s, s ∉ T → f s = 0) → (∀ s ∈ T, size s ≤ B) → (∀ s ∈ T', size s ≤ B) →
      (∑ s ∈ T', μ s * ‖op f s‖ ^ 2) ≤ a * b * (∑ t ∈ T, μ t * ‖f t‖ ^ 2) := by
  intro T T' f hf hT hT'
  let k₀ : α → α → ℂ := fun s t => if valid s ∧ valid t then k s t else 0
  have hdom (s t : α) : ‖k₀ s t‖ ≤ ‖k s t‖ := by
    by_cases hst : valid s ∧ valid t
    · simp [k₀, hst]
    · simp [k₀, hst]
  have hrow₀ (s : α) (hs : s ∈ T') : ∑ t ∈ T, ‖k₀ s t‖ * v t ≤ a * v s := by
    by_cases hvs : valid s
    · calc
        _ ≤ ∑ t ∈ T, ‖k s t‖ * v t :=
          Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_right (hdom s t) (hv t).le
        _ ≤ _ := hrow s hvs (hT' s hs) T hT
    · have hsum : (∑ t ∈ T, ‖k₀ s t‖ * v t) = 0 := by simp [k₀, hvs]
      rw [hsum]
      exact mul_nonneg ha (hv s).le
  have hcol₀ (t : α) (ht : t ∈ T) :
      ∑ s ∈ T', μ s * ‖k₀ s t‖ * v s ≤ b * μ t * v t := by
    by_cases hvt : valid t
    · calc
        _ ≤ ∑ s ∈ T', μ s * ‖k s t‖ * v s :=
          Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hdom s t) (hμ s)) (hv s).le
        _ ≤ _ := hcol t hvt (hT t ht) T' hT'
    · have hsum : (∑ s ∈ T', μ s * ‖k₀ s t‖ * v s) = 0 := by simp [k₀, hvt]
      rw [hsum]
      exact mul_nonneg (mul_nonneg hb (hμ t)) (hv t).le
  have hpoint (s : α) (hs : s ∈ T') :
      μ s * ‖op f s‖ ^ 2 = μ s * ‖∑ t ∈ T, k₀ s t * f t‖ ^ 2 := by
    by_cases hvs : valid s
    · have he : (∑ t ∈ T, k₀ s t * f t) = ∑ t ∈ T, k s t * f t := by
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hvt : valid t
        · simp [k₀, hvs, hvt]
        · simp [k₀, hvt, hnull s hvs t hvt]
      rw [hrep T f hf hT s hvs (hT' s hs), he]
    · rw [hzero s hvs]
      simp
  calc
    _ = ∑ s ∈ T', μ s * ‖∑ t ∈ T, k₀ s t * f t‖ ^ 2 :=
      Finset.sum_congr rfl (fun s hs => hpoint s hs)
    _ ≤ _ := pd5_finite_weighted_schur_norm μ v k₀ f T T' a b hμ hv ha hb hrow₀ hcol₀

end
end ArtinPrimitiveRoots.TypeII.PD
