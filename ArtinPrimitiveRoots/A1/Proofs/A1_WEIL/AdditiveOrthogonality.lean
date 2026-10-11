import Mathlib.Algebra.Group.AddChar
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

open MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

/-- An additive character integrates to the subgroup mass when it is trivial there,
and to zero otherwise. Translation invariance applies to the subgroup indicator,
so the identity needs no global integrability assumption on the character.
Supplies compact-ball orthogonality for the Fourier support test. -/
theorem integral_addChar_addSubgroup {G : Type*} [AddCommGroup G]
    [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G)
    [Measure.IsAddLeftInvariant μ] (U : AddSubgroup G)
    (hU : MeasurableSet (U : Set G)) (χ : AddChar G ℂ) :
    (∫ x in (U : Set G), χ x ∂μ) =
      if ∀ x ∈ U, χ x = 1 then ((μ (U : Set G)).toReal : ℂ) else 0 := by
  by_cases htriv : ∀ x ∈ U, χ x = 1
  · rw [ite_eq_left htriv]
    calc
      (∫ x in (U : Set G), χ x ∂μ) = ∫ _ in (U : Set G), (1 : ℂ) ∂μ :=
        setIntegral_congr_fun hU htriv
      _ = _ := by
        simp only [setIntegral_const, measureReal_def, Complex.real_smul, mul_one]
  · rw [ite_eq_right htriv]
    push Not at htriv
    obtain ⟨b, hb, hχb⟩ := htriv
    let f : G → ℂ := (U : Set G).indicator (fun x => χ x)
    have hshift : ∀ x, f (b + x) = χ b * f x := by
      intro x
      by_cases hx : x ∈ U
      · have hbx : b + x ∈ U := U.add_mem hb hx
        simp only [f, Set.indicator_of_mem hx, Set.indicator_of_mem hbx,
          AddChar.map_add_eq_mul]
      · have hbx : b + x ∉ U := by
          intro h
          apply hx
          simpa only [neg_add_cancel_left] using U.add_mem (U.neg_mem hb) h
        simp only [f, Set.indicator_of_notMem hx, Set.indicator_of_notMem hbx, mul_zero]
    have hI : χ b * (∫ x, f x ∂μ) = ∫ x, f x ∂μ := by
      calc
        χ b * (∫ x, f x ∂μ) = ∫ x, χ b * f x ∂μ := (integral_const_mul (χ b) f).symm
        _ = ∫ x, f (b + x) ∂μ := integral_congr_ae (Filter.Eventually.of_forall
          fun x => (hshift x).symm)
        _ = ∫ x, f x ∂μ := integral_add_left_eq_self f b
    have hzero : ∫ x, f x ∂μ = 0 := by
      have he : (χ b - 1) * (∫ x, f x ∂μ) = 0 := by
        calc
          (χ b - 1) * (∫ x, f x ∂μ) = χ b * (∫ x, f x ∂μ) - (∫ x, f x ∂μ) := by ring
          _ = 0 := by rw [hI, sub_self]
      exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hχb)
    simpa only [f, integral_indicator hU] using hzero

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
