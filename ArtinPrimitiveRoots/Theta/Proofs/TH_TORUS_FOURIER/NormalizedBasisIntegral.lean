import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open MeasureTheory Module
open scoped Classical NNReal ENNReal

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

/-- Normalizing by the volume of a basis fundamental domain cancels the Haar
scaling under its coordinate map. -/
theorem normalized_basis_integral {E d : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype d] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (b : Basis d ℝ E) (f : E → ℂ) :
    ((μ (ZSpan.fundamentalDomain b)).toReal)⁻¹ •
        (∫ x in ZSpan.fundamentalDomain b, f x ∂μ) =
      ∫ x in Set.pi Set.univ (fun _ : d => Set.Ico (0 : ℝ) 1),
        f (b.equivFun.symm x) := by
  classical
  let e : E ≃ᵐ (d → ℝ) := b.equivFunL.toHomeomorph.toMeasurableEquiv
  let B : Set (d → ℝ) := Set.pi Set.univ (fun _ : d => Set.Ico (0 : ℝ) 1)
  have hBmeas : MeasurableSet B :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)
  have hBvol : volume B = 1 := by
    simp [B, volume_pi, Measure.pi_pi]
  have hpre : e ⁻¹' B = ZSpan.fundamentalDomain b := by
    ext x
    simp only [Set.mem_preimage, B, Set.mem_pi, Set.mem_univ, forall_true_left,
      ZSpan.mem_fundamentalDomain]
    rfl
  let : Measure.IsAddHaarMeasure (μ.map e) :=
    b.equivFunL.isAddHaarMeasure_map μ
  let c : ℝ≥0 := Measure.addHaarScalarFactor (μ.map e) (volume : Measure (d → ℝ))
  have hc : 0 < c :=
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) volume
  have hscale : μ.map e = c • (volume : Measure (d → ℝ)) :=
    Measure.isAddLeftInvariant_eq_smul (μ.map e) volume
  have hmeasure : μ (ZSpan.fundamentalDomain b) = (c : ℝ≥0∞) := by
    calc
      μ (ZSpan.fundamentalDomain b) = (μ.map e) B := by
        rw [Measure.map_apply e.measurable hBmeas, hpre]
      _ = (c : ℝ≥0∞) := by simp [hscale, hBvol]
  have hTransfer : (∫ x in ZSpan.fundamentalDomain b, f x ∂μ) =
      ∫ x in B, f (e.symm x) ∂(μ.map e) := by
    simpa only [hpre, MeasurableEquiv.symm_apply_apply] using
      (setIntegral_map_equiv (μ := μ) e (fun x => f (e.symm x)) B).symm
  have hIntegral : (∫ x in ZSpan.fundamentalDomain b, f x ∂μ) =
      (c : ℝ) • ∫ x in B, f (b.equivFun.symm x) := by
    rw [hTransfer, hscale, Measure.restrict_smul, integral_smul_nnreal_measure]
    rfl
  have hcnz : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [hmeasure, ENNReal.coe_toReal, hIntegral, smul_smul,
    inv_mul_cancel₀ hcnz, one_smul]

end ArtinPrimitiveRoots.Proofs.thsol_torusf
