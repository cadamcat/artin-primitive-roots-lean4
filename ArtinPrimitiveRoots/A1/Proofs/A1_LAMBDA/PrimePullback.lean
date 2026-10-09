import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

-- Preserve the cyclotomic instance used by the frozen Eisenstein interfaces.
attribute [local instance 2000] CyclotomicField.instNumberField
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: For local units use N.unit_norm and hC. For uniformizers use N.uniformizer_norm, kill the unit factor with hv, and unfold primeValue. Preserve residue-degree exponent.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem relative_norm_prime_pullback (D : FieldData F) (ι : E →ₐ[ℚ] F)
    (N : RelativeNormData D ι)
    (C : ContinuousMonoidHom (NumberField.IdeleClassGroup (𝓞 F) F) (NumberField.IdeleClassGroup OE E))
    (hC : ∀ x : NumberField.IdeleGroup (𝓞 F) F,
      C (QuotientGroup.mk x) = QuotientGroup.mk (N.norm x))
    (χ : LambdaChar E) (v : FinPlace F)
    (hv : unramifiedAt χ (basePlace ι v)) :
    unramifiedAt (χ.comp C) v ∧
      primeValue (χ.comp C) v = primeValue χ (basePlace ι v) ^ residueDegree ι v := by
  have hunram : unramifiedAt (χ.comp C) v := by
    intro x hx1 hx2
    have hunit : localUnit v x := ⟨hx1, hx2⟩
    obtain ⟨b, hb_unit, h_norm⟩ := N.unit_norm v x hunit
    change χ (C (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x)) = 1
    have hmk : IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x =
        QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 F) F v x) := rfl
    rw [hmk, hC, h_norm]
    change localComponent χ (basePlace ι v) b = 1
    exact hv b hb_unit.1 hb_unit.2
  refine ⟨hunram, ?_⟩
  dsimp only [primeValue, KummerProofs.primeValue]
  simp only [hunram, hv, ↓reduceIte]
  obtain ⟨b, hb_unit, h_norm⟩ := N.uniformizer_norm v
  change ((χ (C (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (toLoc v (KummerProofs.uniformizerUnit v)))) : ℂˣ) : ℂ) =
    ((localComponent χ (basePlace ι v) (toLoc (basePlace ι v) (KummerProofs.uniformizerUnit (basePlace ι v))) : ℂˣ) : ℂ) ^ residueDegree ι v
  have hmk : IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (toLoc v (KummerProofs.uniformizerUnit v)) =
      QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 F) F v (toLoc v (KummerProofs.uniformizerUnit v))) := rfl
  rw [hmk, hC, h_norm]
  change ((χ (QuotientGroup.mk (IdeleGroup.ofAdicCompletion OE E (basePlace ι v)
    (toLoc (basePlace ι v) (KummerProofs.uniformizerUnit (basePlace ι v)) ^ residueDegree ι v * b))) : ℂˣ) : ℂ) = _
  rw [map_mul, QuotientGroup.mk_mul, map_mul]
  have hb1 : localComponent χ (basePlace ι v) b = 1 := hv b hb_unit.1 hb_unit.2
  change χ (QuotientGroup.mk (IdeleGroup.ofAdicCompletion OE E (basePlace ι v) b)) = 1 at hb1
  rw [hb1, mul_one]
  rw [map_pow, QuotientGroup.mk_pow, map_pow]
  push_cast
  rfl

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
