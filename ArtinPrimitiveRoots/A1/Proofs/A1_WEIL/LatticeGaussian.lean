import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.AdditiveOrthogonality
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

/-- Average a bounded phase over a small compact subgroup. Character orthogonality
reduces every sufficiently large compact subgroup to the same annihilator integral.
Supplies cutoff independence for the trace-form comparison.
Both restricted measures are finite before the Fubini step. -/
theorem large_subgroup_phase_integrals_eq
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd G] (μ : Measure G) [Measure.IsAddHaarMeasure μ]
    (U V K : AddSubgroup G)
    (hU : IsCompact (U : Set G)) (hV : IsCompact (V : Set G))
    (hK : IsCompact (K : Set G)) (hKmass : (μ (K : Set G)).toReal ≠ 0)
    (hKU : K ≤ U) (hKV : K ≤ V)
    (f : G → ℂ) (hf : Continuous f) (hfbound : ∀ x, ‖f x‖ ≤ 1)
    (χ : G → AddChar G ℂ)
    (hshift : ∀ x y, y ∈ K → f (y + x) = f x * χ x y)
    (hC : MeasurableSet {x : G | ∀ y ∈ K, χ x y = 1})
    (hCU : ∀ x, (∀ y ∈ K, χ x y = 1) → x ∈ U)
    (hCV : ∀ x, (∀ y ∈ K, χ x y = 1) → x ∈ V) :
    (∫ x in (U : Set G), f x ∂μ) = ∫ x in (V : Set G), f x ∂μ := by
  let C : Set G := {x | ∀ y ∈ K, χ x y = 1}
  let m : ℂ := ((μ (K : Set G)).toReal : ℂ)
  have hm : m ≠ 0 := by
    dsimp only [m]
    exact_mod_cast hKmass
  have hKmeas : MeasurableSet (K : Set G) := hK.measurableSet
  have hKfinite : μ (K : Set G) < ⊤ := hK.measure_lt_top
  have : IsFiniteMeasure (μ.restrict (K : Set G)) :=
    isFiniteMeasure_restrict.mpr hKfinite.ne
  have hlocalize (L : AddSubgroup G) (hL : IsCompact (L : Set G))
      (hKL : K ≤ L) (hCL : ∀ x, (∀ y ∈ K, χ x y = 1) → x ∈ L) :
      (∫ x in (L : Set G), f x ∂μ) = ∫ x in C, f x ∂μ := by
    have hLmeas : MeasurableSet (L : Set G) := hL.measurableSet
    have hLfinite : μ (L : Set G) < ⊤ := hL.measure_lt_top
    have : IsFiniteMeasure (μ.restrict (L : Set G)) :=
      isFiniteMeasure_restrict.mpr hLfinite.ne
    have htranslate (y : G) (hy : y ∈ K) :
        (∫ x in (L : Set G), f (y + x) ∂μ) = ∫ x in (L : Set G), f x ∂μ := by
      let F := (L : Set G).indicator f
      have hF : ∀ x,
          F (y + x) = (L : Set G).indicator (fun x => f (y + x)) x := by
        intro x
        by_cases hx : x ∈ L
        · have hyx : y + x ∈ L := L.add_mem (hKL hy) hx
          simp only [F, Set.indicator_of_mem hx, Set.indicator_of_mem hyx]
        · have hyx : y + x ∉ L := by
            intro h
            apply hx
            simpa only [neg_add_cancel_left] using L.add_mem (L.neg_mem (hKL hy)) h
          simp only [F, Set.indicator_of_notMem hx, Set.indicator_of_notMem hyx]
      calc
        (∫ x in (L : Set G), f (y + x) ∂μ) =
            ∫ x, (L : Set G).indicator (fun x => f (y + x)) x ∂μ :=
          (integral_indicator hLmeas).symm
        _ = ∫ x, F (y + x) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => (hF x).symm)
        _ = ∫ x, F x ∂μ := integral_add_left_eq_self F y
        _ = ∫ x in (L : Set G), f x ∂μ := integral_indicator hLmeas
    let g := fun y x : G => f (y + x)
    have hgcont : Continuous (Function.uncurry g) :=
      hf.comp (continuous_fst.add continuous_snd)
    have hgint : Integrable (Function.uncurry g)
        ((μ.restrict (K : Set G)).prod (μ.restrict (L : Set G))) :=
      (integrable_const (1 : ℝ)).mono' hgcont.stronglyMeasurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => hfbound (p.1 + p.2))
    have hmean : m * (∫ x in (L : Set G), f x ∂μ) = m * (∫ x in C, f x ∂μ) := by
      calc
        m * (∫ x in (L : Set G), f x ∂μ) =
            ∫ _ in (K : Set G), (∫ x in (L : Set G), f x ∂μ) ∂μ := by
          simp only [setIntegral_const, measureReal_def, Complex.real_smul, m]
        _ = ∫ y in (K : Set G), ∫ x in (L : Set G), g y x ∂μ ∂μ :=
          setIntegral_congr_fun hKmeas fun y hy => (htranslate y hy).symm
        _ = ∫ x in (L : Set G), ∫ y in (K : Set G), g y x ∂μ ∂μ :=
          integral_integral_swap hgint
        _ = ∫ x in (L : Set G), m * C.indicator f x ∂μ := by
          apply setIntegral_congr_fun hLmeas
          intro x _hx
          calc
            (∫ y in (K : Set G), g y x ∂μ) =
                f x * (∫ y in (K : Set G), χ x y ∂μ) := by
              rw [← integral_const_mul]
              exact setIntegral_congr_fun hKmeas fun y hy => hshift x y hy
            _ = m * C.indicator f x := by
              rw [integral_addChar_addSubgroup μ K hKmeas (χ x)]
              change f x * (if x ∈ C then m else 0) = m * C.indicator f x
              by_cases hx : x ∈ C
              · rw [ite_eq_left hx, Set.indicator_of_mem hx]
                exact mul_comm _ _
              · rw [ite_eq_right hx, Set.indicator_of_notMem hx, mul_zero, mul_zero]
        _ = m * (∫ x in (L : Set G), C.indicator f x ∂μ) := integral_const_mul m _
        _ = m * (∫ x in C, f x ∂μ) := by
          rw [setIntegral_indicator hC]
          have hLC : (L : Set G) ∩ C = C :=
            Set.inter_eq_right.mpr fun x hx => hCL x hx
          rw [hLC]
    exact mul_left_cancel₀ hm hmean
  exact (hlocalize U hU hKU hCU).trans (hlocalize V hV hKV hCV).symm

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
