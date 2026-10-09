import ArtinPrimitiveRoots.Splitting.Defs
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option autoImplicit false

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke

/-- The reciprocal of the discriminant and archimedean prefactor, with its entire extension. -/
def invPrefactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (absoluteDiscriminant K : ℂ) ^ (-s / 2) *
    ((Complex.Gammaℝ s)⁻¹) ^ InfinitePlace.nrRealPlaces K *
    ((Complex.Gammaℂ s)⁻¹) ^ InfinitePlace.nrComplexPlaces K

/-- Removing the entire reciprocal prefactor leaves only the two explicit endpoint denominators. -/
theorem sharp_continuation (K : Type*) [Field K] [NumberField K] :
    Differentiable ℂ (invPrefactor K) ∧
    (∀ s : ℂ, dedekindZetaSharp K s =
      dedekindXi K s * invPrefactor K s / (s * (s - 1))) ∧
    MeromorphicOn (dedekindZetaSharp K) Set.univ ∧
    dedekindXi K 0 ≠ 0 := by
  have hD : (absoluteDiscriminant K : ℂ) ≠ 0 := by
    unfold absoluteDiscriminant
    exact_mod_cast abs_ne_zero.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hpow : Differentiable ℂ (fun s : ℂ =>
      (absoluteDiscriminant K : ℂ) ^ (-s / 2)) :=
    (differentiable_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hD)
  have hinv : Differentiable ℂ (invPrefactor K) :=
    (hpow.mul (Complex.differentiable_Gammaℝ_inv.pow _)).mul
      (Complex.differentiable_Gammaℂ_inv.pow _)
  have hreciprocal (s : ℂ) : invPrefactor K s = (dedekindPrefactor K s)⁻¹ := by
    simp only [invPrefactor, dedekindPrefactor, absoluteDiscriminant,
      neg_div, Complex.cpow_neg, mul_inv, inv_pow]
    ring
  have heq (s : ℂ) : dedekindZetaSharp K s =
      dedekindXi K s * invPrefactor K s / (s * (s - 1)) := by
    rw [hreciprocal s, dedekindZetaSharp]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hspec := Classical.choose_spec (dedekind_completed K)
  have hxi : Differentiable ℂ (dedekindXi K) := hspec.1
  refine ⟨hinv, heq, ?_, ?_⟩
  · have hfun : dedekindZetaSharp K =
        fun s : ℂ => dedekindXi K s * invPrefactor K s / (s * (s - 1)) :=
      funext heq
    rw [hfun]
    intro s _
    exact ((hxi.analyticAt s).mul (hinv.analyticAt s)).meromorphicAt.div
      (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).meromorphicAt
  · have hzero : dedekindXi K 0 = dedekindXi K 1 := by
      simpa only [dedekindXi, sub_zero] using (hspec.2.2.1 0).symm
    rw [hzero]
    exact hspec.2.2.2

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
