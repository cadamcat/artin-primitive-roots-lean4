import Mathlib
set_option autoImplicit false
open Classical

private theorem sum_fin_function_prod_local {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (w : α → ℝ) :
    (∑ g : Fin n → α, ∏ i : Fin n, w (g i)) = (∑ a : α, w a) ^ n := by
  classical
  rw [← Fintype.piFinset_univ]
  calc
    _ = ∏ i : Fin n, ∑ a : α, w a := by
      simpa using (Finset.prod_univ_sum (fun _ : Fin n => Finset.univ)
        (fun _ a => w a)).symm
    _ = _ := by simp [Finset.prod_const]

theorem finite_exp_batch_sum {α : Type*} [Fintype α] [DecidableEq α]
    (B : ℕ) (c : ℝ) (hc : 0 ≤ c) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (∑ m : Fin (B + 1),
      ∑ f : Fin m.val → α,
        c ^ m.val / (m.val.factorial : ℝ) * ∏ k : Fin m.val, w (f k)) ≤
      Real.exp (c * ∑ a : α, w a) := by
  classical
  let s : ℝ := ∑ a : α, w a
  have hinner (m : ℕ) :
      (∑ f : Fin m → α,
        c ^ m / (m.factorial : ℝ) * ∏ k : Fin m, w (f k)) =
        (c * s) ^ m / (m.factorial : ℝ) := by
    calc
      _ = c ^ m / (m.factorial : ℝ) *
            ∑ f : Fin m → α, ∏ k : Fin m, w (f k) := by rw [← Finset.mul_sum]
      _ = c ^ m / (m.factorial : ℝ) * s ^ m := by
            rw [sum_fin_function_prod_local]
      _ = (c * s) ^ m / (m.factorial : ℝ) := by
            calc
              c ^ m / (m.factorial : ℝ) * s ^ m = (c ^ m * s ^ m) / (m.factorial : ℝ) := by ring
              _ = (c * s) ^ m / (m.factorial : ℝ) := by rw [← mul_pow]
  have hsummable : Summable (fun m : ℕ => (c * s) ^ m / (m.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp (c * s)).summable
  have heq :
      (fun m : ℕ =>
        ∑ f : Fin m → α,
          c ^ m / (m.factorial : ℝ) * ∏ k : Fin m, w (f k)) =
        fun m : ℕ => (c * s) ^ m / (m.factorial : ℝ) := by
    funext m
    simpa [s] using hinner m
  have hseq : Summable (fun m : ℕ =>
      ∑ f : Fin m → α,
        c ^ m / (m.factorial : ℝ) * ∏ k : Fin m, w (f k)) := heq ▸ hsummable
  have hnonneg (m : ℕ) : 0 ≤
      ∑ f : Fin m → α,
        c ^ m / (m.factorial : ℝ) * ∏ k : Fin m, w (f k) := by
    apply Finset.sum_nonneg
    intro f hf
    apply mul_nonneg
    · exact div_nonneg (pow_nonneg hc _) (Nat.cast_nonneg _)
    · exact Finset.prod_nonneg_iff.mpr (by
        intro k hk
        exact hw (f k))
  have hpartial :
      (∑ m ∈ Finset.range (B + 1),
        ∑ f : Fin m → α,
          c ^ m / (m.factorial : ℝ) * ∏ k : Fin m, w (f k)) ≤
        ∑' m : ℕ,
          ∑ f : Fin m → α,
            c ^ m / (m.factorial : ℝ) * ∏ k : Fin m, w (f k) :=
    Summable.sum_le_tsum (Finset.range (B + 1)) (by
      intro m hm
      exact hnonneg m) hseq
  have hFin :
      (∑ m : Fin (B + 1),
        ∑ f : Fin m.val → α,
          c ^ m.val / (m.val.factorial : ℝ) * ∏ k : Fin m.val, w (f k)) =
        ∑ m ∈ Finset.range (B + 1),
          ∑ f : Fin m → α,
            c ^ m / (m.factorial : ℝ) * ∏ k : Fin m, w (f k) := by
    rw [Fin.sum_univ_eq_sum_range]
  calc
    _ = _ := hFin
    _ ≤ _ := hpartial
    _ = Real.exp (c * s) := by
          rw [HasSum.tsum_eq (NormedSpace.expSeries_div_hasSum_exp (c * s))]
    _ = _ := by simp [s]
