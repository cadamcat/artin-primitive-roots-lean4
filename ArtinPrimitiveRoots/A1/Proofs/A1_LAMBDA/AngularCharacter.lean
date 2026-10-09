import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private def angularUnit (z : ℂˣ) : ℂˣ :=
  Units.mk0 ((z : ℂ) / ‖(z : ℂ)‖) (div_ne_zero z.ne_zero (by
    exact_mod_cast norm_ne_zero_iff.mpr z.ne_zero))

private def angularHom : ContinuousMonoidHom ℂˣ ℂˣ where
  toFun := angularUnit
  map_one' := by
    apply Units.ext
    simp [angularUnit]
  map_mul' z w := by
    apply Units.ext
    change ((z : ℂ) * (w : ℂ)) / ‖(z : ℂ) * (w : ℂ)‖ =
      ((z : ℂ) / ‖(z : ℂ)‖) * ((w : ℂ) / ‖(w : ℂ)‖)
    rw [Complex.norm_mul]
    push_cast
    field_simp [norm_ne_zero_iff.mpr z.ne_zero, norm_ne_zero_iff.mpr w.ne_zero]
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    constructor
    · exact Units.continuous_val.div
        (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val))
        (fun z => by exact_mod_cast norm_ne_zero_iff.mpr z.ne_zero)
    · have hcontInv : Continuous (fun z : ℂˣ =>
          (‖(z : ℂ)‖ : ℂ) / (z : ℂ)) :=
        (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)).div
          Units.continuous_val (fun z => z.ne_zero)
      simpa [angularUnit, inv_div] using hcontInv

/-- A1-LAMBDA IMPL: Bundle z/abs(z) on complex units; norm multiplicativity and continuous division give the homomorphism.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem angular_character_exists :
    ∃ a : ContinuousMonoidHom ℂˣ ℂˣ, ∀ z : ℂˣ,
      ((a z : ℂˣ) : ℂ) = (z : ℂ) / ‖(z : ℂ)‖ := by
  refine ⟨angularHom, ?_⟩
  intro z
  rfl

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
