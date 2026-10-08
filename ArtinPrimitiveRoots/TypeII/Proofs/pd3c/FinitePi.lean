import Mathlib
set_option autoImplicit false
open Classical

private theorem finite_pi_sum_prod {ι : Type*} [Fintype ι]
    (α : ι → Type*) [∀ i, Fintype (α i)]
    (f : ∀ i, α i → ℝ) :
    (∑ x : ∀ i, α i, ∏ i, f i (x i)) = ∏ i, ∑ a : α i, f i a := by
  classical
  rw [← Fintype.piFinset_univ]
  simpa using (Finset.prod_univ_sum (fun i => (Finset.univ : Finset (α i))) f).symm
