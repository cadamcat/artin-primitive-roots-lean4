import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Group.Units

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

theorem inv_of_sigmaFinite_mulInvariant
    {K : Type*} [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [SecondCountableTopology K]
    (μ : Measure K) [SigmaFinite μ]
    (h0 : μ {0} = 0)
    (hμ : ∀ a : Kˣ,
      Measure.map (fun x : K => (a : K) * x) μ = μ) :
    Measure.map (fun x : K => x⁻¹) μ = μ := by
  classical
  letI : MeasurableSpace Kˣ := borel Kˣ
  haveI : BorelSpace Kˣ := ⟨rfl⟩
  haveI : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hrange : Set.range (Units.val : Kˣ → K) = ({0} : Set K)ᶜ := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.ne_zero
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  have he : MeasurableEmbedding (Units.val : Kˣ → K) :=
    Units.isEmbedding_val₀.measurableEmbedding (by
      rw [hrange]
      exact (measurableSet_singleton (0 : K)).compl)
  let ν : Measure Kˣ := Measure.comap Units.val μ
  have hpush : Measure.map (Units.val : Kˣ → K) ν = μ := by
    rw [he.map_comap, hrange]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    simpa using h0
  haveI : SigmaFinite (Measure.map (Units.val : Kˣ → K) ν) := by
    rw [hpush]
    infer_instance
  haveI : SigmaFinite ν := SigmaFinite.of_map ν he.measurable.aemeasurable inferInstance
  haveI : Measure.IsMulLeftInvariant ν := ⟨fun a => he.map_injective (by
    calc
      Measure.map (Units.val : Kˣ → K) (Measure.map (fun x : Kˣ => a * x) ν) =
          Measure.map (fun x : K => (a : K) * x)
            (Measure.map (Units.val : Kˣ → K) ν) := by
        have hmU : Measurable (fun x : Kˣ => a * x) :=
          (continuous_const.mul continuous_id).measurable
        have hmK : Measurable (fun x : K => (a : K) * x) :=
          (continuous_const.mul continuous_id).measurable
        rw [Measure.map_map he.measurable hmU, Measure.map_map hmK he.measurable]
        rfl
      _ = Measure.map (Units.val : Kˣ → K) ν := by rw [hpush, hμ a])⟩
  calc
    Measure.map (fun x : K => x⁻¹) μ =
        Measure.map (fun x : K => x⁻¹) (Measure.map (Units.val : Kˣ → K) ν) := by
      rw [hpush]
    _ = Measure.map (Units.val : Kˣ → K) (Measure.map (fun x : Kˣ => x⁻¹) ν) := by
      rw [Measure.map_map measurable_inv he.measurable,
        Measure.map_map he.measurable continuous_inv.measurable]
      congr 1
      funext x
      exact (Units.val_inv_eq_inv_val x).symm
    _ = Measure.map (Units.val : Kˣ → K) ν := by
      rw [inv_of_sigmaFinite_leftInvariant ν]
    _ = μ := hpush

end ArtinPrimitiveRoots.Proofs.a2_prod_sol
