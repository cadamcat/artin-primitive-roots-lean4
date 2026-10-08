import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false
open MeasureTheory
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_prod_sol

theorem inv_of_sigmaFinite_leftInvariant
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (ν : Measure G) [SigmaFinite ν] [Measure.IsMulLeftInvariant ν] :
    Measure.map (fun x : G => x⁻¹) ν = ν := by
  classical
  let K₀ : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have hν : ν = ν K₀ • Measure.haarMeasure K₀ := Measure.haarMeasure_unique ν K₀
  calc
    _ = Measure.map (fun x : G => x⁻¹) (ν K₀ • Measure.haarMeasure K₀) :=
      congrArg (Measure.map (fun x : G => x⁻¹)) hν
    _ = ν K₀ • Measure.map (fun x : G => x⁻¹) (Measure.haarMeasure K₀) :=
      Measure.map_smul _ continuous_inv.measurable.aemeasurable
    _ = ν K₀ • Measure.haarMeasure K₀ := by rw [Measure.map_inv_eq_self]
    _ = ν := hν.symm

end ArtinPrimitiveRoots.Proofs.a2_prod_sol
