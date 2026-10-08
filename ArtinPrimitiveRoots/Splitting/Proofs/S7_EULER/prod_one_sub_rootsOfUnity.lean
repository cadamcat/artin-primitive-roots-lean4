import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.Defs

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- The complete root-of-unity Euler polynomial. Guide:
../sol-thin-s7/PROOFS.md:350–365. Uses the factorization of `X^n - 1`;
feeds `prod_one_sub_character`. -/
theorem prod_one_sub_rootsOfUnity (n : ℕ) [NeZero n] (z : ℂ) :
    (∏ ζ : rootsOfUnity n ℂ, (1 - ((ζ : ℂˣ) : ℂ) * z)) = 1 - z ^ n := by
  sorry

end ArtinPrimitiveRoots.Splitting
end
