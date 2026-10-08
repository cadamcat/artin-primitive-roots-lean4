import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
open MeasureTheory
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_prod_sol

theorem angle_translate (c : ℝ) :
    Measure.map (fun θ : ℝ => Complex.exp (2 * Real.pi * Complex.I * (θ + c)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) =
    Measure.map (fun θ : ℝ => Complex.exp (2 * Real.pi * Complex.I * θ))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let mk : ℝ → UnitAddCircle := fun x => (x : UnitAddCircle)
  let E : UnitAddCircle → ℂ := fun x => (AddCircle.toCircle x : ℂ)
  let tr : UnitAddCircle → UnitAddCircle := fun x => x + (c : UnitAddCircle)
  have hE : Measurable E :=
    (continuous_subtype_val.comp AddCircle.continuous_toCircle).measurable
  have hm : MeasurePreserving mk ν (volume : Measure UnitAddCircle) := by
    simpa only [ν, mk, zero_add] using UnitAddCircle.measurePreserving_mk 0
  have ht : MeasurePreserving tr (volume : Measure UnitAddCircle) volume :=
    measurePreserving_add_right volume (c : UnitAddCircle)
  have hexp (x : ℝ) : E (mk x) = Complex.exp (2 * Real.pi * Complex.I * x) := by
    dsimp only [E, mk]
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
    congr 1
    push_cast
    ring
  have hexp_tr (x : ℝ) :
      E (tr (mk x)) = Complex.exp (2 * Real.pi * Complex.I * (x + c)) := by
    change E ((x : UnitAddCircle) + (c : UnitAddCircle)) = _
    rw [← AddCircle.coe_add]
    simpa only [mk, Complex.ofReal_add] using hexp (x + c)
  have hright :
      Measure.map (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * x)) ν =
        Measure.map E (volume : Measure UnitAddCircle) := by
    calc
      _ = Measure.map (E ∘ mk) ν :=
        Measure.map_congr (Filter.Eventually.of_forall fun x => (hexp x).symm)
      _ = Measure.map E (Measure.map mk ν) :=
        (Measure.map_map hE hm.measurable).symm
      _ = Measure.map E volume := by rw [hm.map_eq]
  calc
    _ = Measure.map (E ∘ (tr ∘ mk)) ν :=
      Measure.map_congr (Filter.Eventually.of_forall fun x => (hexp_tr x).symm)
    _ = Measure.map E (Measure.map (tr ∘ mk) ν) :=
      (Measure.map_map hE (ht.measurable.comp hm.measurable)).symm
    _ = Measure.map E volume := by rw [(ht.comp hm).map_eq]
    _ = _ := hright.symm

end ArtinPrimitiveRoots.Proofs.a2_prod_sol
