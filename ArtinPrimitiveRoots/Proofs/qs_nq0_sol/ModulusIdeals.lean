import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.Conductors

/-!
# Ideals with prescribed finite prime exponents

The planned ideal and exponent statement, in this module's context, are:
```
def qsNQModulusIdeal (e : FinPlace K →₀ ℕ) : Ideal (𝓞 K) :=
  e.prod (fun v n => v.asIdeal ^ n)

theorem qs_nq0_modulus_ideal_exponents (e : FinPlace K →₀ ℕ) :
    qsNQModulusIdeal e ≠ ⊥ ∧
      ∀ v : FinPlace K, idealExp v (qsNQModulusIdeal e) = e v ∧
        (qsNQModulusIdeal e ≤ v.asIdeal ↔ v ∈ e.support)
```
The fractional ideal count formula computes the exponents. Prime divisibility
then identifies the support.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- The integral ideal associated to finitely many natural prime exponents. -/
def qsNQModulusIdeal (e : FinPlace K →₀ ℕ) : Ideal (𝓞 K) :=
  e.prod (fun v n => v.asIdeal ^ n)

/-- The prime-power product is nonzero and has precisely the prescribed exponents and support. -/
theorem qs_nq0_modulus_ideal_exponents (e : FinPlace K →₀ ℕ) :
    qsNQModulusIdeal e ≠ ⊥ ∧
      ∀ v : FinPlace K, idealExp v (qsNQModulusIdeal e) = e v ∧
        (qsNQModulusIdeal e ≤ v.asIdeal ↔ v ∈ e.support) := by
  classical
  have hI : qsNQModulusIdeal e ≠ ⊥ := by
    change (∏ v ∈ e.support, v.asIdeal ^ e v) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ v.ne_bot)
  have hcount (v : FinPlace K) :
      FractionalIdeal.count K v
        (qsNQModulusIdeal e : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = (e v : ℤ) := by
    change FractionalIdeal.count K v
      ((FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K)) K)
        (∏ w ∈ e.support, w.asIdeal ^ e w)) = (e v : ℤ)
    rw [map_prod]
    simp_rw [map_pow]
    change FractionalIdeal.count K v
      (∏ w ∈ e.support,
        (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ e w) = (e v : ℤ)
    rw [FractionalIdeal.count_prod]
    · simp only [FractionalIdeal.count_pow, FractionalIdeal.count_maximal,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
      by_cases hv : v ∈ e.support
      · simp [hv]
      · simp [hv, Finsupp.notMem_support_iff.mp hv]
    · intro w _
      exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)
  refine ⟨hI, fun v => ?_⟩
  have hexp : idealExp v (qsNQModulusIdeal e) = e v := by
    have hcast : (idealExp v (qsNQModulusIdeal e) : ℤ) = (e v : ℤ) :=
      (FractionalIdeal.count_coe K v hI).symm.trans (hcount v)
    exact_mod_cast hcast
  refine ⟨hexp, ?_⟩
  rw [← Ideal.dvd_iff_le, ← Associates.count_ne_zero_iff_dvd hI v.irreducible]
  change idealExp v (qsNQModulusIdeal e) ≠ 0 ↔ v ∈ e.support
  rw [hexp, Finsupp.mem_support_iff]

end ArtinPrimitiveRoots.A2
