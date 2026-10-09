import ArtinPrimitiveRoots.A1.Field

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A global sixth root of an S-unit is an S-unit: exterior valuations are multiples of 6
and already zero, so they vanish. -/
theorem s_unit_of_sixth (S : SData F CE condη) (u ε : Fˣ)
    (hu : u ∈ S.US) (heq : u = ε ^ 6) : ε ∈ S.US := by
  intro v hv
  have hval := hu v hv
  rw [heq, Units.val_pow_eq_pow_val, map_pow] at hval
  have hlog := congrArg WithZero.log hval
  simp only [WithZero.log_pow, WithZero.log_one, nsmul_eq_mul] at hlog
  have hzero : WithZero.log (v.valuation F (ε : F)) = 0 := by omega
  calc
    v.valuation F (ε : F) = WithZero.exp (WithZero.log (v.valuation F (ε : F))) :=
      (WithZero.exp_log ((v.valuation F).ne_zero_iff.mpr ε.ne_zero)).symm
    _ = 1 := by rw [hzero, WithZero.exp_zero]

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
