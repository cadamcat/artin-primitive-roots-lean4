import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Adapt Kummer/Idelic finite-product support and continuity at one; localUnit is the two valuation-subring memberships and restricted-product neighborhoods make all exterior factors trivial.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem finite_local_product_exists
    (f : ∀ v : FinPlace F, ContinuousMonoidHom (v.adicCompletion F)ˣ ℂˣ)
    (hgood : ∀ᶠ v : FinPlace F in Filter.cofinite,
      ∀ u : (v.adicCompletion F)ˣ, localUnit v u → f v u = 1) :
    ∃ g : ContinuousMonoidHom (NumberField.IdeleGroup (𝓞 F) F) ℂˣ,
      (∀ x, g x = ∏ᶠ v : FinPlace F, f v (Dictionary.ideleFiniteCoord v x)) ∧
      ∀ x : NumberField.IdeleGroup (𝓞 F) F,
        Function.HasFiniteMulSupport (fun v : FinPlace F =>
          f v (Dictionary.ideleFiniteCoord v x)) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
