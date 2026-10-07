import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDLow.Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

/-- Finite weighted Schur estimate, exposed from the already proved MemoryResults helper.
No completion or infinite function-space argument is required by the low-rank adapters. -/
theorem pd5_finite_weighted_schur_norm {α : Type*} [DecidableEq α]
    (μ v : α → ℝ) (k : α → α → ℂ) (f : α → ℂ) (T T' : Finset α) (a b : ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hv : ∀ s, 0 < v s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrow : ∀ s ∈ T', ∑ t ∈ T, ‖k s t‖ * v t ≤ a * v s)
    (hcol : ∀ t ∈ T, ∑ s ∈ T', μ s * ‖k s t‖ * v s ≤ b * μ t * v t) :
    (∑ s ∈ T', μ s * ‖∑ t ∈ T, k s t * f t‖ ^ 2) ≤
      a * b * (∑ t ∈ T, μ t * ‖f t‖ ^ 2) := by
  classical
  have hpoint (s : α) :
      ‖∑ t ∈ T, k s t * f t‖ ^ 2 ≤
        (∑ t ∈ T, ‖k s t‖ * v t) *
          ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t := by
    have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := T)
      (r := fun t => ‖k s t‖ * ‖f t‖)
      (f := fun t => ‖k s t‖ * v t)
      (g := fun t => ‖k s t‖ * ‖f t‖ ^ 2 / v t)
      (fun t ht => mul_nonneg (norm_nonneg _) (hv t).le)
      (fun t ht => div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hv t).le)
      (fun t ht => by
        have hvt := hv t
        have heq : (‖k s t‖ * ‖f t‖) ^ 2 =
            (‖k s t‖ * v t) * (‖k s t‖ * ‖f t‖ ^ 2 / v t) := by
          field_simp [hvt.ne']
        exact heq.le)
    have htri :
        ‖∑ t ∈ T, k s t * f t‖ ≤ ∑ t ∈ T, ‖k s t‖ * ‖f t‖ := by
      calc
        ‖∑ t ∈ T, k s t * f t‖ ≤ ∑ t ∈ T, ‖k s t * f t‖ := norm_sum_le _ _
        _ = ∑ t ∈ T, ‖k s t‖ * ‖f t‖ := by simp [norm_mul]
    have hsumNonneg : 0 ≤ ∑ t ∈ T, ‖k s t‖ * ‖f t‖ :=
      Finset.sum_nonneg fun t ht => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : ‖∑ t ∈ T, k s t * f t‖ ^ 2 ≤
        (∑ t ∈ T, ‖k s t‖ * ‖f t‖) ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr htri)
        (add_nonneg (norm_nonneg (∑ t ∈ T, k s t * f t)) hsumNonneg)
      nlinarith [hprod]
    exact hsq.trans hCS
  have hinnerNonneg (s : α) :
      0 ≤ ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t :=
    Finset.sum_nonneg fun t ht =>
      div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hv t).le
  have hrowAll (s : α) (hs : s ∈ T') :
      0 ≤ ∑ t ∈ T, ‖k s t‖ * v t :=
    Finset.sum_nonneg fun t ht => mul_nonneg (norm_nonneg _) (hv t).le
  have hswap :
      (∑ s ∈ T', μ s * v s *
        (∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t)) =
        ∑ t ∈ T, (‖f t‖ ^ 2 / v t) *
          (∑ s ∈ T', μ s * ‖k s t‖ * v s) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro s hs
    ring
  calc
    (∑ s ∈ T', μ s * ‖∑ t ∈ T, k s t * f t‖ ^ 2)
        ≤ ∑ s ∈ T', μ s *
          ((∑ t ∈ T, ‖k s t‖ * v t) *
            ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t) := by
          apply Finset.sum_le_sum
          intro s hs
          exact mul_le_mul_of_nonneg_left (hpoint s) (hμ s)
    _ ≤ ∑ s ∈ T', μ s * ((a * v s) *
          ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t) := by
          apply Finset.sum_le_sum
          intro s hs
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hrow s hs) (hinnerNonneg s)) (hμ s)
    _ = a * (∑ s ∈ T', μ s * v s *
          (∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
    _ = a * (∑ t ∈ T, (‖f t‖ ^ 2 / v t) *
          (∑ s ∈ T', μ s * ‖k s t‖ * v s)) := by rw [hswap]
    _ ≤ a * (∑ t ∈ T, (‖f t‖ ^ 2 / v t) * (b * μ t * v t)) := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro t ht
            exact mul_le_mul_of_nonneg_left (hcol t ht)
              (div_nonneg (sq_nonneg _) (hv t).le)
          · exact ha
    _ = a * b * (∑ t ∈ T, μ t * ‖f t‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          have hvt := hv t
          field_simp [hvt.ne']

/-- A positive choice envelope gives the same finite Schur estimate to every kernel it
dominates. This is the adapter needed for phases before raw/comparison subtraction. -/
theorem pd5_finite_dominated_schur_norm {α : Type*} [DecidableEq α]
    (μ v : α → ℝ) (P : α → α → ℝ) (k : α → α → ℂ)
    (f : α → ℂ) (T T' : Finset α) (a b : ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hv : ∀ s, 0 < v s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdom : ∀ s ∈ T', ∀ t ∈ T, ‖k s t‖ ≤ P s t)
    (hrow : ∀ s ∈ T', ∑ t ∈ T, P s t * v t ≤ a * v s)
    (hcol : ∀ t ∈ T, ∑ s ∈ T', μ s * P s t * v s ≤ b * μ t * v t) :
    (∑ s ∈ T', μ s * ‖∑ t ∈ T, k s t * f t‖ ^ 2) ≤
      a * b * (∑ t ∈ T, μ t * ‖f t‖ ^ 2) := by
  apply pd5_finite_weighted_schur_norm μ v k f T T' a b hμ hv ha hb
  · intro s hs
    calc
      _ ≤ ∑ t ∈ T, P s t * v t :=
        Finset.sum_le_sum fun t ht =>
          mul_le_mul_of_nonneg_right (hdom s hs t ht) (hv t).le
      _ ≤ _ := hrow s hs
  · intro t ht
    calc
      _ ≤ ∑ s ∈ T', μ s * P s t * v s :=
        Finset.sum_le_sum fun s hs =>
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hdom s hs t ht) (hμ s)) (hv s).le
      _ ≤ _ := hcol t ht

end
end ArtinPrimitiveRoots.TypeII.PD
