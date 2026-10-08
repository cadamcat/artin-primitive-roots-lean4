import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

open MeasureTheory Complex AddCircle
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Differentiation in one real coordinate multiplies a torus Fourier coefficient
by its corresponding frequency. The hypothesis describes the derivative on each
lifted circle slice, including the endpoints of a period. -/
theorem mFourierCoeff_coordinate_derivative {n : ℕ} (i : Fin (n + 1))
    (f f' : C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hD : ∀ (z : UnitAddTorus (Fin n)) (t : ℝ),
      HasDerivAt (fun s : ℝ => f (i.insertNth (s : UnitAddCircle) z))
        (f' (i.insertNth (t : UnitAddCircle) z)) t)
    (k : Fin (n + 1) → ℤ) :
    UnitAddTorus.mFourierCoeff f' k =
      (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) * UnitAddTorus.mFourierCoeff f k := by
  classical
  have hcircle (u u' : C(UnitAddCircle, ℂ))
      (hu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u (s : UnitAddCircle))
        (u' (t : UnitAddCircle)) t) (m : ℤ) :
      fourierCoeff u' m = (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * fourierCoeff u m := by
    let a : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)
    let v : ℝ → ℂ := fun t => fourier (-m) (t : UnitAddCircle)
    let v' : ℝ → ℂ := fun t => -a * v t
    have hv : Continuous v := (fourier (-m)).continuous.comp (AddCircle.continuous_mk' 1)
    have hv' : Continuous v' := continuous_const.mul hv
    have hD_v (t : ℝ) : HasDerivAt v (v' t) t := by
      convert hasDerivAt_fourier_neg (1 : ℝ) m t using 1 <;> simp [v, v', a] <;> ring
    have huc : Continuous (fun t : ℝ => u (t : UnitAddCircle)) :=
      u.continuous.comp (AddCircle.continuous_mk' 1)
    have hu'c : Continuous (fun t : ℝ => u' (t : UnitAddCircle)) :=
      u'.continuous.comp (AddCircle.continuous_mk' 1)
    have hInt := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      huc.continuousOn hv.continuousOn (fun t _ => hu t) (fun t _ => hD_v t)
      (hu'c.intervalIntegrable 0 1) (hv'.intervalIntegrable 0 1)
    have hzero : ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
      simpa using AddCircle.coe_add_period (1 : ℝ) (0 : ℝ)
    have hvends : v 1 = v 0 := by simp only [v, hzero]
    rw [hzero, hvends, sub_self, zero_sub] at hInt
    have hleft : (∫ t in (0 : ℝ)..1, u (t : UnitAddCircle) * v' t) =
        -a * fourierCoeff u m := by
      rw [fourierCoeff_eq_intervalIntegral u m 0]
      simp only [zero_add, one_div_one, one_smul, smul_eq_mul]
      simp_rw [show ∀ t : ℝ, u (t : UnitAddCircle) * v' t =
        -a * (fourier (-m) (t : UnitAddCircle) * u (t : UnitAddCircle)) by
          intro t; dsimp [v', v]; ring]
      exact intervalIntegral.integral_const_mul _ _
    have hright : (∫ t in (0 : ℝ)..1, u' (t : UnitAddCircle) * v t) =
        fourierCoeff u' m := by
      rw [fourierCoeff_eq_intervalIntegral u' m 0]
      simp only [zero_add, one_div_one, one_smul, smul_eq_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [v]
      ring
    rw [hleft, hright] at hInt
    change fourierCoeff u' m = a * fourierCoeff u m
    linear_combination hInt
  have hInsert : Continuous
      (fun p : UnitAddCircle × UnitAddTorus (Fin n) =>
        (i.insertNth p.1 p.2 : UnitAddTorus (Fin (n + 1)))) := by
    rw [continuous_pi_iff]
    rw [i.forall_iff_succAbove]
    constructor
    · simpa only [Fin.insertNth_apply_same] using
        (continuous_fst : Continuous (fun p : UnitAddCircle × UnitAddTorus (Fin n) => p.1))
    · intro j
      simpa only [Fin.insertNth_apply_succAbove, Function.comp_def] using
        (continuous_apply j).comp (continuous_snd : Continuous
          (fun p : UnitAddCircle × UnitAddTorus (Fin n) => p.2))
  let slice (u : C(UnitAddTorus (Fin (n + 1)), ℂ)) (z : UnitAddTorus (Fin n)) :
      C(UnitAddCircle, ℂ) :=
    ⟨fun t => u (i.insertNth t z), u.continuous.comp
      (hInsert.comp (continuous_id.prodMk continuous_const))⟩
  let tail (z : UnitAddTorus (Fin n)) : ℂ :=
    ∏ j : Fin n, fourier (-(k (i.succAbove j))) (z j)
  have hsplit (u : C(UnitAddTorus (Fin (n + 1)), ℂ)) :
      UnitAddTorus.mFourierCoeff u k =
        ∫ z : UnitAddTorus (Fin n), tail z * fourierCoeff (slice u z) (k i) := by
    let w : C(UnitAddTorus (Fin (n + 1)), ℂ) :=
      UnitAddTorus.mFourier (-k) * u
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) i
    have he := (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => UnitAddCircle) i).symm
    have hw : Integrable w volume := w.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have hw' : Integrable (fun p : UnitAddCircle × UnitAddTorus (Fin n) =>
        w (e.symm p)) (volume.prod volume) :=
      (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hw
    change (∫ z, w z) = _
    rw [← he.integral_comp' w]
    change (∫ p : UnitAddCircle × UnitAddTorus (Fin n), w (e.symm p)
      ∂(volume.prod volume)) = _
    rw [integral_prod_symm _ hw']
    apply integral_congr_ae
    filter_upwards [] with z
    rw [fourierCoeff, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    change UnitAddTorus.mFourier (-k) (i.insertNth t z) *
      u (i.insertNth t z) = tail z * (fourier (-(k i)) t * u (i.insertNth t z))
    unfold UnitAddTorus.mFourier
    simp only [ContinuousMap.coe_mk, Pi.neg_apply]
    rw [Fin.prod_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    dsimp [tail]
    ring
  rw [hsplit f', hsplit f]
  have hslice (z : UnitAddTorus (Fin n)) :
      fourierCoeff (slice f' z) (k i) =
        (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) * fourierCoeff (slice f z) (k i) :=
    hcircle (slice f z) (slice f' z) (hD z) (k i)
  simp_rw [hslice]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

end ArtinPrimitiveRoots.Proofs.thsol_torusf
