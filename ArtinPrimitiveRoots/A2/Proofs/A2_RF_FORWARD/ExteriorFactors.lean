import ArtinPrimitiveRoots.A1.Field

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1

theorem exterior_cube_factors {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη)
    (I c n : Ideal (𝓞 F)) (hI : S.IsExterior I) (hEq : I = c * n ^ (3 : ℕ)) :
    S.IsExterior c ∧ S.IsExterior n := by
  have hc0 : c ≠ ⊥ := by
    intro hc
    apply hI.1
    calc
      I = c * n ^ (3 : ℕ) := hEq
      _ = ⊥ := by simp [hc]
  have hn0 : n ≠ ⊥ := by
    intro hn
    apply hI.1
    calc
      I = c * n ^ (3 : ℕ) := hEq
      _ = ⊥ := by simp [hn]
  constructor
  · refine ⟨hc0, ?_⟩
    intro v hv hle
    apply hI.2 v hv
    apply Ideal.dvd_iff_le.mp
    rw [hEq]
    exact dvd_mul_of_dvd_left (Ideal.dvd_iff_le.mpr hle) _
  · refine ⟨hn0, ?_⟩
    intro v hv hle
    have hPn : v.asIdeal ∣ n := Ideal.dvd_iff_le.mpr hle
    have hP3 : v.asIdeal ∣ n ^ (3 : ℕ) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
      exact dvd_mul_of_dvd_right hPn _
    apply hI.2 v hv
    apply Ideal.dvd_iff_le.mp
    rw [hEq]
    exact dvd_mul_of_dvd_right hP3 _

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
