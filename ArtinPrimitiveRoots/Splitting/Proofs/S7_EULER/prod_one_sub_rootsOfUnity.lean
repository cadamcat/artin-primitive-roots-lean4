import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.Defs
import Mathlib.FieldTheory.KummerExtension

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- The complete root-of-unity Euler polynomial.
Uses the factorization of `X^n - 1`;
feeds `prod_one_sub_character`. -/
theorem prod_one_sub_rootsOfUnity (n : ℕ) [NeZero n] (z : ℂ) :
    (∏ ζ : rootsOfUnity n ℂ, (1 - ((ζ : ℂˣ) : ℂ) * z)) = 1 - z ^ n := by
  classical
  let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have hξ : IsPrimitiveRoot ξ n := by
    exact Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  let u : ℂˣ := Units.mk0 ξ (Complex.exp_ne_zero _)
  have hu : IsPrimitiveRoot u n := by
    refine ⟨?_, ?_⟩
    · apply Units.ext
      simpa [u] using hξ.pow_eq_one
    · intro l hl
      apply hξ.dvd_of_pow_eq_one l
      have hval := congrArg Units.val hl
      simpa [u] using hval
  have hpowmem (i : ℕ) : u ^ i ∈ rootsOfUnity n ℂ := by
    rw [mem_rootsOfUnity]
    calc
      (u ^ i) ^ n = (u ^ n) ^ i := by rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ = 1 := by rw [hu.pow_eq_one, one_pow]
  let e : Fin n ≃ rootsOfUnity n ℂ :=
    { toFun := fun i => ⟨u ^ (i : ℕ), hpowmem i⟩
      invFun := fun x =>
        ⟨Classical.choose (hu.eq_pow_of_mem_rootsOfUnity x.property),
          (Classical.choose_spec (hu.eq_pow_of_mem_rootsOfUnity x.property)).1⟩
      left_inv := by
        intro i
        apply Fin.ext
        have hex := hu.eq_pow_of_mem_rootsOfUnity (hpowmem i)
        exact hu.pow_inj (Classical.choose_spec hex).1 i.isLt
          (Classical.choose_spec hex).2
      right_inv := by
        intro x
        apply Subtype.ext
        exact (Classical.choose_spec (hu.eq_pow_of_mem_rootsOfUnity x.property)).2 }
  have hprod_equiv :
      (∏ i : Fin n, (1 - ((u ^ (i : ℕ) : ℂˣ) : ℂ) * z)) =
        ∏ ζ : rootsOfUnity n ℂ, (1 - ((ζ : ℂˣ) : ℂ) * z) := by
    apply Fintype.prod_equiv e
    intro i
    rfl
  have hfin_range :
      (∏ i : Fin n, (1 - ((u ^ (i : ℕ) : ℂˣ) : ℂ) * z)) =
        ∏ i ∈ Finset.range n, (1 - ξ ^ i * z) := by
    let eRange : Fin n ≃ {i : ℕ // i ∈ Finset.range n} :=
      { toFun := fun i => ⟨i.val, Finset.mem_range.mpr i.isLt⟩
        invFun := fun i => ⟨i.val, Finset.mem_range.mp i.property⟩
        left_inv := by intro i; rfl
        right_inv := by intro i; apply Subtype.ext; rfl }
    calc
      _ = ∏ i : Fin n, (1 - ξ ^ (i : ℕ) * z) := by
        apply Fintype.prod_congr
        intro i
        simp [u, ξ]
      _ = ∏ i : {i : ℕ // i ∈ Finset.range n}, (1 - ξ ^ i.val * z) := by
        exact Fintype.prod_equiv eRange _ _ (by intro i; rfl)
      _ = ∏ i ∈ Finset.range n, (1 - ξ ^ i * z) :=
        Finset.prod_coe_sort (Finset.range n) (fun i : ℕ => 1 - ξ ^ i * z)
  by_cases hz : z = 0
  · simp [hz, NeZero.ne n]
  · have hfactor :
        (Polynomial.X ^ n - Polynomial.C (1 : ℂ)) =
          ∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ξ ^ i)) := by
        simpa [ξ, mul_one] using
          (X_pow_sub_C_eq_prod hξ (NeZero.pos n) (one_pow n))
    have heval : (z⁻¹) ^ n - 1 =
        ∏ i ∈ Finset.range n, ((z⁻¹) - ξ ^ i) := by
      have h := congrArg (Polynomial.eval (z⁻¹)) hfactor
      simpa [Polynomial.eval_prod] using h
    have hrew :
        (∏ i ∈ Finset.range n, ((z⁻¹) - ξ ^ i)) =
          (z⁻¹) ^ n * ∏ i ∈ Finset.range n, (1 - ξ ^ i * z) := by
      calc
        _ = ∏ i ∈ Finset.range n, (z⁻¹ * (1 - ξ ^ i * z)) := by
          apply Finset.prod_congr rfl
          intro i hi
          field_simp [hz]
        _ = (∏ i ∈ Finset.range n, z⁻¹) *
              ∏ i ∈ Finset.range n, (1 - ξ ^ i * z) := by
          rw [Finset.prod_mul_distrib]
        _ = (z⁻¹) ^ n * ∏ i ∈ Finset.range n, (1 - ξ ^ i * z) := by
          simp
    have hpow : z ^ n * (z⁻¹) ^ n = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
    have hrecip : (z⁻¹) ^ n - 1 =
        (z⁻¹) ^ n * ∏ i ∈ Finset.range n, (1 - ξ ^ i * z) := heval.trans hrew
    have hrange : ∏ i ∈ Finset.range n, (1 - ξ ^ i * z) = 1 - z ^ n := by
      calc
        _ = 1 * ∏ i ∈ Finset.range n, (1 - ξ ^ i * z) := by simp
        _ = (z ^ n * (z⁻¹) ^ n) *
              ∏ i ∈ Finset.range n, (1 - ξ ^ i * z) := by rw [hpow]
        _ = z ^ n * ((z⁻¹) ^ n *
              ∏ i ∈ Finset.range n, (1 - ξ ^ i * z)) := by ac_rfl
        _ = z ^ n * ((z⁻¹) ^ n - 1) := by rw [← hrecip]
        _ = 1 - z ^ n := by rw [mul_sub, hpow, mul_one]
    rw [hprod_equiv.symm, hfin_range]
    exact hrange

end ArtinPrimitiveRoots.Splitting
end
