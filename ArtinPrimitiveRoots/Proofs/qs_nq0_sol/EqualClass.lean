import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ConductorBounds

/-!
# Sixth powers from the allowed-generator complement

The quotient of two allowed generators belongs to B. If it differs from
an S-unit by a diagonal element with trivial power class, it also belongs
to E. The complement condition then makes that quotient a sixth power
in the product of the S-completions.
-/

set_option autoImplicit false

open scoped NumberField
open ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- An allowed ratio whose power class comes from an S-unit is a sixth power at S. -/
theorem qs_nq0_allowed_ratio_sixth
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (Sd : SData K CE condη) (H : HilbertData K) (Bd : BData Sd H)
    (a b x : Kˣ) (ha : Bd.Allowed a) (hb : Bd.Allowed b)
    (hunit : a / b / x ∈ Sd.US)
    (hx : (QuotientGroup.mk (Sd.diagU x) : Sd.V) = 1) :
    ∃ y : Sd.FSˣ, Sd.diagU (a / b) = y ^ 6 := by
  let q : Kˣ →* Sd.V := (QuotientGroup.mk' _).comp Sd.diagU
  change q a ∈ Bd.B at ha
  change q b ∈ Bd.B at hb
  change q x = 1 at hx
  have hB : q (a / b) ∈ Bd.B := by
    rw [map_div]
    exact Bd.B.div_mem ha hb
  have hE : q (a / b) ∈ Sd.E := by
    have hunitClass : q (a / b / x) ∈ Sd.E := by
      exact ⟨a / b / x, hunit, rfl⟩
    simpa only [map_div, hx, div_one] using hunitClass
  have hclass : q (a / b) = 1 :=
    (Subgroup.disjoint_def.mp Bd.compl.disjoint) hE hB
  have hpower : Sd.diagU (a / b) ∈ (powMonoidHom 6 : Sd.FSˣ →* Sd.FSˣ).range :=
    (QuotientGroup.eq_one_iff (Sd.diagU (a / b))).mp hclass
  obtain ⟨y, hy⟩ := hpower
  exact ⟨y, hy.symm⟩

end ArtinPrimitiveRoots.A2
