import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Algebra.InfiniteSum.Group

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

/-- Extract a finite correction from a convergent product, including zero corrections. -/
theorem hasProd_finite_factor_tprod
    {ι : Type} (a b : ι → ℂ)
    (ha : (Function.mulSupport a).Finite) {z : ℂ}
    (h : HasProd (fun i => a i * b i) z) :
    z = (∏ᶠ i, a i) * ∏' i, b i := by
  classical
  have hfinite : HasProd a (∏ᶠ i, a i) := by
    rw [finprod_eq_prod a ha]
    apply hasProd_prod_of_ne_finset_one
    intro i hi
    simpa only [ha.mem_toFinset, Function.mem_mulSupport, not_not] using hi
  by_cases hA : (∏ᶠ i, a i) = 0
  · have hex : ∃ i, a i = 0 := by
      by_contra hnone
      have hne : ∀ i, a i ≠ 0 := by simpa only [not_exists] using hnone
      exact (finprod_ne_zero hne) hA
    obtain ⟨i, hi⟩ := hex
    have hz : z = 0 := h.unique (hasProd_zero_of_exists_eq_zero ⟨i, by simp [hi]⟩)
    rw [hz, hA, zero_mul]
  · have hai (i : ι) : a i ≠ 0 := by
      intro hi
      exact hA (finprod_eq_zero a i hi ha)
    have hb : HasProd b ((∏ᶠ i, a i)⁻¹ * z) := by
      convert (hfinite.inv₀ hA).mul h using 1
      ext i
      simp [← mul_assoc, hai i]
    rw [hb.tprod_eq, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]

end ArtinPrimitiveRoots.A1.Theta
