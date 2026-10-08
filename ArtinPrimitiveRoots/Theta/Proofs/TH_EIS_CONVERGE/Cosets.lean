import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

/-- Right translation reindexes a scalar sum over left cosets. -/
theorem leftCosetSum_rightTranslate {Γ K : Type*} [Group Γ] [Group K]
    (H : Subgroup Γ) (rat : Γ →* K) (f : K → ℂ)
    (hinv : ∀ b ∈ H, ∀ g, f (rat b * g) = f g) (γ : Γ) (g : K) :
    (∑' q : Quotient (QuotientGroup.rightRel H),
      f (rat (Quotient.out q) * (rat γ * g))) =
    ∑' q : Quotient (QuotientGroup.rightRel H), f (rat (Quotient.out q) * g) := by
  classical
  have hrep (a b : Γ) (hab : QuotientGroup.rightRel H a b) (h : K) :
      f (rat a * h) = f (rat b * h) := by
    have hb : b * a⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hab
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      (hinv (b * a⁻¹) hb (rat a * h)).symm
  let Q := Quotient (QuotientGroup.rightRel H)
  let translate (k : Γ) : Q → Q :=
    Quotient.map (fun a => a * k) (by
      intro a b hab
      apply QuotientGroup.rightRel_apply.mpr
      have hb : b * a⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hab
      simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hb)
  let e : Q ≃ Q :=
    { toFun := translate γ
      invFun := translate γ⁻¹
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro a
        change Quotient.mk (QuotientGroup.rightRel H) ((a * γ) * γ⁻¹) =
          Quotient.mk (QuotientGroup.rightRel H) a
        simp only [mul_inv_cancel_right]
      right_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro a
        change Quotient.mk (QuotientGroup.rightRel H) ((a * γ⁻¹) * γ) =
          Quotient.mk (QuotientGroup.rightRel H) a
        simp only [inv_mul_cancel_right] }
  have hout (q : Q) :
      QuotientGroup.rightRel H (Quotient.out (e q)) (Quotient.out q * γ) := by
    apply Quotient.exact
    calc
      Quotient.mk (QuotientGroup.rightRel H) (Quotient.out (e q)) = e q :=
        Quotient.out_eq (e q)
      _ = e (Quotient.mk (QuotientGroup.rightRel H) (Quotient.out q)) :=
        congrArg e (Quotient.out_eq q).symm
      _ = Quotient.mk (QuotientGroup.rightRel H) (Quotient.out q * γ) := rfl
  calc
    _ = ∑' q : Q, f (rat (Quotient.out (e q)) * g) := by
      apply tsum_congr
      intro q
      simpa only [map_mul, mul_assoc] using
        (hrep (Quotient.out (e q)) (Quotient.out q * γ) (hout q) g).symm
    _ = _ := e.tsum_eq (fun q => f (rat (Quotient.out q) * g))

end ArtinPrimitiveRoots.A1.Theta
