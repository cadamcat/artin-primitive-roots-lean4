import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Order.Filter.Finite
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open scoped Topology BigOperators
open Filter Metric

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

/-- Finite windows converge when they eventually contain every nonzero summand. -/
theorem finset_sum_tendsto_of_eventually_mem {ι : Type*}
    (F : ι → ℂ) (hF : Summable F) (Z : ℕ → Finset ι)
    (hcover : ∀ i : ι, F i ≠ 0 → ∀ᶠ n in atTop, i ∈ Z n) :
    Tendsto (fun n : ℕ => ∑ i ∈ Z n, F i) atTop (𝓝 (∑' i : ι, F i)) := by
  classical
  have hsum : Tendsto (fun S : Finset ι => ∑ i ∈ S, F i)
      atTop (𝓝 (∑' i : ι, F i)) := hF.hasSum
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hsum ε hε)
  have hzero : ∀ᶠ n in (atTop : Filter ℕ), ∀ i ∈ S, i ∉ Z n → F i = 0 := by
    apply (Filter.eventually_all_finset S).mpr
    intro i hi
    by_cases hz : F i = 0
    · exact Filter.Eventually.of_forall (fun _ _ => hz)
    · filter_upwards [hcover i hz] with n hin
      intro hnot
      exact (hnot hin).elim
  filter_upwards [hzero] with n hn
  have heq : (∑ i ∈ Z n, F i) = ∑ i ∈ Z n ∪ S, F i := by
    apply Finset.sum_subset Finset.subset_union_left
    intro i hi hnot
    exact hn i ((Finset.mem_union.mp hi).resolve_left hnot) hnot
  rw [heq]
  exact hS (Z n ∪ S) Finset.subset_union_right

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
