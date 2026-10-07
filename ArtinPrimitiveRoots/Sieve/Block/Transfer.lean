import Mathlib

namespace ArtinPrimitiveRoots.Sieve.Block

open Finset

/-- Total weight of the objects satisfying all bad conditions indexed by `D`. -/
noncomputable def weightedIntersection {α β : Type*} [DecidableEq β]
    (A : Finset α) (wt : α → ℝ) (bad : β → α → Prop) (D : Finset β) : ℝ := by
  classical
  exact ∑ a ∈ A.filter (fun a => ∀ p ∈ D, bad p a), wt a

/-- A squarefree polynomial evaluated on the bad-condition indicators. -/
noncomputable def badPolynomial {α β : Type*} [DecidableEq β]
    (P : Finset β) (bad : β → α → Prop) (c : Finset β → ℝ) (a : α) : ℝ := by
  classical
  exact ∑ D ∈ P.powerset, c D * if ∀ p ∈ D, bad p a then (1 : ℝ) else 0

/-- Summing a polynomial over the weighted set is the same as summing its coefficients against
the intersection weights. -/
theorem weightedPolynomial_eq_intersection_sum {α β : Type*} [DecidableEq β]
    (A : Finset α) (wt : α → ℝ) (P : Finset β) (bad : β → α → Prop)
    (c : Finset β → ℝ) :
    (∑ a ∈ A, wt a * badPolynomial P bad c a) =
      ∑ D ∈ P.powerset, c D * weightedIntersection A wt bad D := by
  classical
  unfold badPolynomial weightedIntersection
  calc
    (∑ a ∈ A, wt a * ∑ D ∈ P.powerset,
        c D * if ∀ p ∈ D, bad p a then (1 : ℝ) else 0) =
      ∑ a ∈ A, ∑ D ∈ P.powerset,
        wt a * (c D * if ∀ p ∈ D, bad p a then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.mul_sum P.powerset
        (fun D => c D * if ∀ p ∈ D, bad p a then (1 : ℝ) else 0) (wt a)
    _ = ∑ D ∈ P.powerset,
        ∑ a ∈ A, wt a * (c D * if ∀ p ∈ D, bad p a then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ D ∈ P.powerset,
        c D * ∑ a ∈ A.filter (fun a => ∀ p ∈ D, bad p a), wt a := by
      apply Finset.sum_congr rfl
      intro D hD
      calc
        (∑ a ∈ A, wt a * (c D * if ∀ p ∈ D, bad p a then (1 : ℝ) else 0)) =
            c D * ∑ a ∈ A, wt a * if ∀ p ∈ D, bad p a then (1 : ℝ) else 0 := by
          rw [Finset.mul_sum (s := A)
            (f := fun a => wt a * if ∀ p ∈ D, bad p a then (1 : ℝ) else 0)
            (a := c D)]
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = c D * ∑ a ∈ A.filter (fun a => ∀ p ∈ D, bad p a), wt a := by
          congr 1
          calc
            (∑ a ∈ A, wt a * if ∀ p ∈ D, bad p a then (1 : ℝ) else 0) =
                ∑ a ∈ A, if ∀ p ∈ D, bad p a then wt a else 0 := by
              apply Finset.sum_congr rfl
              intro a ha
              split_ifs <;> simp
            _ = ∑ a ∈ A.filter (fun a => ∀ p ∈ D, bad p a), wt a := by
              rw [← Finset.sum_filter]
        _ = _ := by rw [mul_comm]

/-- A polynomial with coefficients in `[-1,1]` has its total intersection error bounded by the
unweighted sum of absolute errors on its support. -/
theorem supported_coefficient_error_bound {β : Type*} [DecidableEq β]
    (P : Finset β) (Q : Finset (Finset β)) (c E : Finset β → ℝ)
    (hQ : Q ⊆ P.powerset)
    (hc : ∀ D ∈ Q, |c D| ≤ 1)
    (hzero : ∀ D ∈ P.powerset, D ∉ Q → c D = 0) :
    |∑ D ∈ P.powerset, c D * E D| ≤ ∑ D ∈ Q, |E D| := by
  classical
  have hsum : (∑ D ∈ P.powerset, |c D * E D|) =
      ∑ D ∈ Q, |c D * E D| := by
    symm
    apply Finset.sum_subset hQ
    intro D hD hnot
    simp [hzero D hD hnot]
  calc
    |∑ D ∈ P.powerset, c D * E D| ≤ ∑ D ∈ P.powerset, |c D * E D| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ D ∈ Q, |c D * E D| := hsum
    _ ≤ ∑ D ∈ Q, |E D| := by
      apply Finset.sum_le_sum
      intro D hD
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hc D hD)

/-- The weighted polynomial sum differs from its independent main term by precisely the
coefficient-weighted intersection errors. -/
theorem weightedPolynomial_main_difference {α β : Type*} [DecidableEq β]
    (A : Finset α) (wt : α → ℝ) (P : Finset β) (bad : β → α → Prop)
    (c : Finset β → ℝ) (X : ℝ) (g : β → ℝ) (E : Finset β → ℝ)
    (hA : ∀ D ∈ P.powerset,
      weightedIntersection A wt bad D = X * ∏ p ∈ D, g p + E D) :
    (∑ a ∈ A, wt a * badPolynomial P bad c a) -
        X * ∑ D ∈ P.powerset, c D * ∏ p ∈ D, g p =
      ∑ D ∈ P.powerset, c D * E D := by
  classical
  rw [weightedPolynomial_eq_intersection_sum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [hA D hD]
  ring_nf

end ArtinPrimitiveRoots.Sieve.Block
