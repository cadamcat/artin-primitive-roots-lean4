import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: D.hζ12 gives a primitive cubic fourth power; use the cyclotomic power basis or embeddingsEquivPrimitiveRoots, aligned on omega.
Uses: Definitions. -/
theorem aligned_eisenstein_embedding_exists (D : FieldData F) :
    ∃ ι : E →ₐ[ℚ] F, ι (algebraMap OE E omega) = D.ζ12 ^ 4 := by
  have : IsCyclotomicExtension {3} ℚ E := CyclotomicField.isCyclotomicExtension 3 ℚ
  let ζE := IsCyclotomicExtension.zeta 3 ℚ E
  let hζE : IsPrimitiveRoot ζE 3 := IsCyclotomicExtension.zeta_spec 3 ℚ E
  have hirr : Irreducible (Polynomial.cyclotomic 3 ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (by norm_num)
  have hζF : IsPrimitiveRoot (D.ζ12 ^ 4) 3 :=
    D.hζ12.pow_of_dvd (p := 4) (by norm_num) (by norm_num)
  let target : primitiveRoots 3 F :=
    ⟨D.ζ12 ^ 4, (mem_primitiveRoots (by norm_num)).2 hζF⟩
  let e := hζE.embeddingsEquivPrimitiveRoots F hirr
  let ι : E →ₐ[ℚ] F := e.symm target
  have hι : ι ζE = D.ζ12 ^ 4 := by
    have he : e ι = target := e.apply_symm_apply target
    have hval := IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe
      hζE F hirr ι
    rw [he] at hval
    simpa [target] using hval.symm
  refine ⟨ι, ?_⟩
  have hgen : algebraMap OE E omega = ζE := by
    change ((IsCyclotomicExtension.zeta_spec 3 ℚ E).toInteger : E) = ζE
    exact (IsCyclotomicExtension.zeta_spec 3 ℚ E).coe_toInteger
  rw [hgen]
  exact hι

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
