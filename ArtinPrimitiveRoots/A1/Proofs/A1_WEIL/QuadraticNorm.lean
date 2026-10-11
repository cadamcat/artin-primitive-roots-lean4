import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.NormIndex
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.FieldTheory.Perfect

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

private def quadraticNormSubgroup (K : Type) [Field K] (a : K) : Subgroup Kˣ :=
  (Units.map (QuadraticAlgebra.norm : QuadraticAlgebra K a 0 →* K)).range

private theorem mem_quadraticNormSubgroup_iff (K : Type) [Field K] (a : K) (n : Kˣ) :
    n ∈ quadraticNormSubgroup K a ↔ ∃ x y : K, (n : K) = x ^ 2 - a * y ^ 2 := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(z : QuadraticAlgebra K a 0).re, (z : QuadraticAlgebra K a 0).im, ?_⟩
    have hv := congrArg (fun u : Kˣ => (u : K)) hz
    change QuadraticAlgebra.norm (z : QuadraticAlgebra K a 0) = (n : K) at hv
    rw [← hv, QuadraticAlgebra.norm_def]
    ring
  · rintro ⟨x, y, hn⟩
    let z : QuadraticAlgebra K a 0 := ⟨x, y⟩
    have hz : QuadraticAlgebra.norm z = (n : K) := by
      rw [hn, QuadraticAlgebra.norm_def]
      change x * x + 0 * x * y - a * y * y = x ^ 2 - a * y ^ 2
      ring
    have hunit : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hz ▸ n.isUnit)
    obtain ⟨zu, hzu⟩ := hunit
    refine ⟨zu, ?_⟩
    apply Units.ext
    change QuadraticAlgebra.norm (zu : QuadraticAlgebra K a 0) = (n : K)
    rw [hzu, hz]

private theorem quadratic_algebra_norm_eq (K : Type) [Field K] (a : K)
    (z : QuadraticAlgebra K a 0) : Algebra.norm K z = QuadraticAlgebra.norm z := by
  have hmul : Algebra.lmul K (QuadraticAlgebra K a 0) z =
      DistribSMul.toLinearMap K (QuadraticAlgebra K a 0) z := by
    apply LinearMap.ext
    intro x
    simp only [Algebra.coe_lmul_eq_mul, DistribSMul.toLinearMap_apply,
      LinearMap.mul_apply', smul_eq_mul]
  rw [Algebra.norm_apply, hmul, QuadraticAlgebra.det_toLinearMap_eq_norm]

/-- The nonzero binary quadratic norms form an index-two subgroup for a nonsquare
coefficient over a characteristic-zero nonarchimedean local field.
Uses the two-coordinate quadratic algebra and the actual
local Artin map through `local_norm_index_eq_finrank`. -/
theorem quadratic_binary_norm_subgroup_index_two (K : Type) [Field K] [CharZero K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (a : K) (ha : ¬ IsSquare a) :
    ∃ N : Subgroup Kˣ,
      (∀ n : Kˣ, n ∈ N ↔ ∃ x y : K, (n : K) = x ^ 2 - a * y ^ 2) ∧ N.index = 2 := by
  have : Fact (¬ IsSquare a) := ⟨ha⟩
  let L := QuadraticAlgebra K a 0
  have : Algebra.IsQuadraticExtension K L :=
    { finrank_eq_two' := QuadraticAlgebra.finrank_eq_two a 0 }
  have : IsAbelianGalois K L := IsAbelianGalois.of_isCyclic K L
  have hN : quadraticNormSubgroup K a = LocalFieldTheory.localNormSubgroup K L := by
    have hnorm : (QuadraticAlgebra.norm : L →* K) = Algebra.norm K := by
      ext z
      exact (quadratic_algebra_norm_eq K a z).symm
    simp only [quadraticNormSubgroup, LocalFieldTheory.localNormSubgroup,
      LocalFieldTheory.normUnits, hnorm]
  refine ⟨quadraticNormSubgroup K a, mem_quadraticNormSubgroup_iff K a, ?_⟩
  rw [hN, local_norm_index_eq_finrank K L]
  exact QuadraticAlgebra.finrank_eq_two a 0

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
