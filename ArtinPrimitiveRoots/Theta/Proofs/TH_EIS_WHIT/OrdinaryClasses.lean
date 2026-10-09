import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.ValuationGeometry
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.QuotientCoordinates

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

/-- At an ordinary place the local Lagrangian quotient is determined by valuation modulo three. -/
theorem whit_tame_alag_quotient_eq_iff {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (L : Subgroup (v.adicCompletion F)ˣ)
    (hL : ∀ x : (v.adicCompletion F)ˣ,
      x ∈ L ↔ ∃ (k : ℤ) (u : (v.adicCompletion F)ˣ),
        IsLocUnit v u ∧ x = unifLoc v ^ (3 * k) * u)
    (x y : (v.adicCompletion F)ˣ) :
    (QuotientGroup.mk x : (v.adicCompletion F)ˣ ⧸ L) = QuotientGroup.mk y ↔
      (ordv v x : ZMod 3) = (ordv v y : ZMod 3) := by
  obtain ⟨hπ, hmul, hpow, hunit, hdecomp⟩ := whit_ordv_geometry v
  have hkernel (a : (v.adicCompletion F)ˣ) :
      a ∈ L ↔ (ordv v a : ZMod 3) = 0 := by
    rw [hL a, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨k, u, hu, ha⟩
      refine ⟨k, ?_⟩
      rw [ha, hmul, hpow, hπ, (hunit u).mp hu]
      ring
    · rintro ⟨k, hk⟩
      norm_num at hk
      refine ⟨k, unitPart v a, (hdecomp a).1, ?_⟩
      rw [← hk]
      exact (hdecomp a).2
  have hinv : ordv v y⁻¹ = -ordv v y := by
    simpa using hpow y (-1)
  have hdiv : ordv v (x / y) = ordv v x - ordv v y := by
    rw [div_eq_mul_inv, hmul, hinv, sub_eq_add_neg]
  rw [QuotientGroup.eq_iff_div_mem, hkernel, hdiv, Int.cast_sub, sub_eq_zero]

end ArtinPrimitiveRoots.A1.Theta
