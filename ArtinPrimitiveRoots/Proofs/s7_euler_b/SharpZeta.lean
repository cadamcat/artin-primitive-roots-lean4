import ArtinPrimitiveRoots.Splitting.Defs
import Mathlib.Analysis.Meromorphic.Complex

set_option autoImplicit false
open scoped NumberField
open NumberField IsDedekindDomain
noncomputable section

namespace ArtinPrimitiveRoots.Splitting

open ArtinPrimitiveRoots.Hecke

private theorem differentiable_nat_pow_complex {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ (fun s => f s ^ n) := by
  induction n with
  | zero => fun_prop
  | succ n ih =>
    change Differentiable ℂ ((fun s : ℂ => f s ^ n) * f)
    exact ih.mul hf

/-- The gamma/discriminant prefactor is nonzero on the positive half-plane. -/
theorem dedekindPrefactor_ne_zero_of_re_pos (T : Type*) [Field T] [NumberField T]
    {s : ℂ} (hs : 0 < s.re) : dedekindPrefactor T s ≠ 0 := by
  let D : ℂ := ((|(NumberField.discr T : ℝ)| : ℝ) : ℂ)
  have hDreal : |(NumberField.discr T : ℝ)| ≠ 0 := by
    exact_mod_cast (abs_ne_zero.mpr (NumberField.discr_ne_zero T))
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast hDreal
  have hR : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hbase : (2 * Real.pi : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hC : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)))
      (Complex.Gamma_ne_zero_of_re_pos hs)
  unfold dedekindPrefactor
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl hD)
  · exact mul_ne_zero (pow_ne_zero _ hR) (pow_ne_zero _ hC)

/-- The inverse completed-zeta prefactor is entire: reciprocal gamma factors are entire. -/
theorem differentiable_dedekindPrefactor_inv (T : Type*) [Field T] [NumberField T] :
    Differentiable ℂ (fun s : ℂ => (dedekindPrefactor T s)⁻¹) := by
  let D : ℂ := ((|(NumberField.discr T : ℝ)| : ℝ) : ℂ)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast (abs_ne_zero.mpr (NumberField.discr_ne_zero T))
  have hDdiff : Differentiable ℂ (fun s : ℂ => D ^ (-s / 2)) := by
    intro s
    exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hD)
  have hR : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) :=
    Complex.differentiable_Gammaℝ_inv
  have hC : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℂ s)⁻¹) :=
    Complex.differentiable_Gammaℂ_inv
  have hRpow := differentiable_nat_pow_complex hR (InfinitePlace.nrRealPlaces T)
  have hCpow := differentiable_nat_pow_complex hC (InfinitePlace.nrComplexPlaces T)
  have hform : (fun s : ℂ => (dedekindPrefactor T s)⁻¹) =
      fun s => D ^ (-s / 2) *
        ((Complex.Gammaℝ s)⁻¹ ^ InfinitePlace.nrRealPlaces T *
          (Complex.Gammaℂ s)⁻¹ ^ InfinitePlace.nrComplexPlaces T) := by
    funext s
    simp [dedekindPrefactor, D, mul_inv, inv_pow, ← Complex.cpow_neg]
    ring
  rw [hform]
  exact hDdiff.mul (hRpow.mul hCpow)

private theorem differentiable_dedekindXi (T : Type*) [Field T] [NumberField T] :
    Differentiable ℂ (dedekindXi T) := by
  change Differentiable ℂ (Classical.choose (dedekind_completed T))
  exact (Classical.choose_spec (dedekind_completed T)).1

private theorem dedekindZetaSharp_mul_form (T : Type*) [Field T] [NumberField T] :
    dedekindZetaSharp T = fun s : ℂ =>
      dedekindXi T s * (s * (s - 1))⁻¹ * (dedekindPrefactor T s)⁻¹ := by
  funext s
  simp [dedekindZetaSharp, div_eq_mul_inv, mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The canonical sharp zeta is meromorphic on the whole plane. -/
theorem dedekindZetaSharp_meromorphic_core (T : Type*) [Field T] [NumberField T] :
    Meromorphic (dedekindZetaSharp T) := by
  have hXi : Meromorphic (dedekindXi T) := by
    intro s
    exact ((differentiable_dedekindXi T).analyticAt s).meromorphicAt
  have hPoly : Meromorphic (fun s : ℂ => s * (s - 1)) := by
    fun_prop
  have hPolyInv : Meromorphic (fun s : ℂ => (s * (s - 1))⁻¹) := hPoly.inv
  have hPrefInv : Meromorphic (fun s : ℂ => (dedekindPrefactor T s)⁻¹) := by
    intro s
    exact ((differentiable_dedekindPrefactor_inv T).analyticAt s).meromorphicAt
  rw [dedekindZetaSharp_mul_form]
  exact (hXi.mul hPolyInv).mul hPrefInv

/-- The sharp zeta agrees with the Dirichlet series on `Re s > 1`. -/
theorem dedekindZetaSharp_eq_core (T : Type*) [Field T] [NumberField T]
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaSharp T s = NumberField.dedekindZeta T s := by
  have hxi : dedekindXi T s =
      s * (s - 1) * dedekindPrefactor T s * NumberField.dedekindZeta T s := by
    simpa [dedekindXi] using
      (Classical.choose_spec (dedekind_completed T)).2.1 s hs
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz] at hs
    norm_num [Complex.zero_re] at hs
  have hs1 : s ≠ 1 := by
    intro hz
    rw [hz] at hs
    norm_num [Complex.one_re] at hs
  have hden : s * (s - 1) * dedekindPrefactor T s ≠ 0 :=
    mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
      (dedekindPrefactor_ne_zero_of_re_pos T (by linarith))
  rw [dedekindZetaSharp, hxi]
  exact mul_div_cancel_left₀ (NumberField.dedekindZeta T s) hden

/-- Away from `1` in the positive half-plane, the sharp zeta is analytic. -/
theorem dedekindZetaSharp_analyticAt_core (T : Type*) [Field T] [NumberField T]
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (dedekindZetaSharp T) s := by
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz] at hs
    norm_num [Complex.zero_re] at hs
  have hpoly : AnalyticAt ℂ (fun z : ℂ => z * (z - 1)) s := by
    fun_prop
  have hpoly0 : s * (s - 1) ≠ 0 :=
    mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  have hpolyInv : AnalyticAt ℂ (fun z : ℂ => (z * (z - 1))⁻¹) s :=
    hpoly.inv hpoly0
  have hXi : AnalyticAt ℂ (dedekindXi T) s :=
    (differentiable_dedekindXi T).analyticAt s
  have hPrefInv : AnalyticAt ℂ (fun z : ℂ => (dedekindPrefactor T z)⁻¹) s :=
    (differentiable_dedekindPrefactor_inv T).analyticAt s
  rw [dedekindZetaSharp_mul_form]
  exact (hXi.mul hpolyInv).mul hPrefInv

end ArtinPrimitiveRoots.Splitting
end
