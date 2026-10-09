import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».Continuation
import Mathlib.Analysis.Meromorphic.Order

set_option autoImplicit false

open scoped NumberField Topology
open NumberField IsDedekindDomain Filter

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke

/-- The sharp Dedekind continuation has a simple pole at one. -/
theorem sharp_pole_one (K : Type*) [Field K] [NumberField K] :
    meromorphicOrderAt (dedekindZetaSharp K) 1 = (-1 : ℤ) := by
  obtain ⟨hinv, heq, hmerom, _⟩ := sharp_continuation K
  have hspec := Classical.choose_spec (dedekind_completed K)
  have hxi : Differentiable ℂ (dedekindXi K) := hspec.1
  have hD : (absoluteDiscriminant K : ℂ) ≠ 0 := by
    unfold absoluteDiscriminant
    exact_mod_cast abs_ne_zero.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hC : Complex.Gammaℂ (1 : ℂ) ≠ 0 := by
    rw [Complex.Gammaℂ_one]
    exact one_div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hP : invPrefactor K 1 ≠ 0 := by
    unfold invPrefactor
    refine mul_ne_zero (mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hD)) ?_) ?_
    · simp
    · exact pow_ne_zero _ (inv_ne_zero hC)
  let g : ℂ → ℂ := fun s => dedekindXi K s * invPrefactor K s / s
  have hgan : AnalyticAt ℂ g 1 :=
    ((hxi.analyticAt 1).mul (hinv.analyticAt 1)).div analyticAt_id one_ne_zero
  have hg1 : g 1 ≠ 0 := by
    dsimp [g]
    simp only [div_one]
    exact mul_ne_zero hspec.2.2.2 hP
  refine (meromorphicOrderAt_eq_int_iff (hmerom 1 (Set.mem_univ 1))).mpr
    ⟨g, hgan, hg1, ?_⟩
  exact Filter.Eventually.of_forall fun s => by
    rw [heq s]
    dsimp [g]
    simp only [zpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_inv]
    ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
