import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.FiniteLocalProduct

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Multiply the finite product by the finite product of infinite coordinates, descend using L.principal_product and QuotientGroup.lift. Compute single-place coordinates with Dictionary lemmas; local norms one give unitarity.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: FiniteLocalProduct. -/
theorem local_character_descent (L : LocalCharacterData F) :
    ∃ χ : LambdaChar F, unitary χ ∧
      (∀ (v : FinPlace F) (u : (v.adicCompletion F)ˣ),
        localComponent χ v u = L.finite v u) ∧
      ∀ (w : InfinitePlace F) (u : w.Completionˣ),
        infiniteComponent χ w u = L.infinite w u := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
