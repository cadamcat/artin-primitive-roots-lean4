import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.IdealEncoding
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.OrdinaryClasses

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- Binary ordinary valuation classes and exceptional local coordinates determine a rational class. -/
theorem whit_rational_class_encoding
    (L : ∀ v : FinPlace F, Subgroup (v.adicCompletion F)ˣ)
    (E : Finset (FinPlace F))
    (hL : ∀ v, v ∉ E → ∀ x : (v.adicCompletion F)ˣ,
      x ∈ L v ↔ ∃ (k : ℤ) (u : (v.adicCompletion F)ˣ),
        IsLocUnit v u ∧ x = unifLoc v ^ (3 * k) * u) :
    ∃ supp : (Fˣ ⧸ whitRationalAlag L) → Finset (FinPlace F),
      (∀ q v, v ∈ supp q ↔ v ∉ E ∧
        (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 1) ∧
      ∀ q q' : Fˣ ⧸ whitRationalAlag L,
        (∀ v, v ∉ E →
          (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 0 ∨
          (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 1) →
        (∀ v, v ∉ E →
          (ordv v (toLoc v (Quotient.out q')) : ZMod 3) = 0 ∨
          (ordv v (toLoc v (Quotient.out q')) : ZMod 3) = 1) →
        whitPrimeSupportIdeal (supp q) = whitPrimeSupportIdeal (supp q') →
        (∀ v ∈ E, whitAlagCoordinate L v q = whitAlagCoordinate L v q') →
        q = q' := by
  let supp (q : Fˣ ⧸ whitRationalAlag L) : Finset (FinPlace F) :=
    (whit_rational_nonunit_finite (Quotient.out q)).toFinset.filter
      (fun v => v ∉ E ∧ (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 1)
  have hsupp (q : Fˣ ⧸ whitRationalAlag L) (v : FinPlace F) :
      v ∈ supp q ↔ v ∉ E ∧
        (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 1 := by
    dsimp [supp]
    rw [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [Set.Finite.mem_toFinset]
      intro hu
      have hord := ((whit_ordv_geometry v).2.2.2.1
        (toLoc v (Quotient.out q))).mp hu
      have hclass := h.2
      rw [hord, Int.cast_zero] at hclass
      exact zero_ne_one hclass
  refine ⟨supp, hsupp, ?_⟩
  intro q q' hq hq' hI hE
  have hsets : supp q = supp q' := whit_prime_support_encoding.1 hI
  apply whit_alag_coordinates_injective L
  funext v
  change whitAlagCoordinate L v q = whitAlagCoordinate L v q'
  by_cases hv : v ∈ E
  · exact hE v hv
  · have heqone :
        (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 1 ↔
          (ordv v (toLoc v (Quotient.out q')) : ZMod 3) = 1 := by
      have hm : v ∈ supp q ↔ v ∈ supp q' := by rw [hsets]
      rw [hsupp q v, hsupp q' v] at hm
      simpa only [hv, not_false_eq_true, true_and] using hm
    have hord : (ordv v (toLoc v (Quotient.out q)) : ZMod 3) =
        (ordv v (toLoc v (Quotient.out q')) : ZMod 3) := by
      rcases hq v hv with hzero | hone
      · rcases hq' v hv with hzero' | hone'
        · exact hzero.trans hzero'.symm
        · have hone := heqone.mpr hone'
          rw [hzero] at hone
          exact (zero_ne_one hone).elim
      · exact hone.trans (heqone.mp hone).symm
    have hlocal (r : Fˣ ⧸ whitRationalAlag L) :
        whitAlagCoordinate L v r =
          (QuotientGroup.mk (toLoc v (Quotient.out r)) : (v.adicCompletion F)ˣ ⧸ L v) := by
      conv_lhs => rw [← Quotient.out_eq r]
      rfl
    rw [hlocal q, hlocal q']
    exact (whit_tame_alag_quotient_eq_iff v (L v) (hL v hv)
      (toLoc v (Quotient.out q)) (toLoc v (Quotient.out q'))).mpr hord

end ArtinPrimitiveRoots.A1.Theta
