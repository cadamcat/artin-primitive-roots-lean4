import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTorus_normalized_integral
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_fourier_character

set_option autoImplicit false
open NumberField Module MeasureTheory
open scoped Classical ENNReal
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ)

/-- The normalized trace-frequency coefficient in ideal-basis coordinates
is the corresponding Fourier coefficient on the standard unit torus. -/
theorem idealTorus_fourierCoeff_eq [Fintype (Module.Free.ChooseBasisIndex ℤ I)]
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (idealArchBasis F I))).toAddSubgroup Pd volume)
    (g : C(UnitAddTorus (Module.Free.ChooseBasisIndex ℤ I), ℂ))
    (n : Module.Free.ChooseBasisIndex ℤ I → ℤ) :
    ((volume Pd).toReal : ℂ)⁻¹ *
      (∫ y in Pd, g (fun i => ((idealArchBasis F I).equivFun y i : UnitAddCircle)) *
        psiInf (-(idealTraceFrequency F I n)) y) =
          UnitAddTorus.mFourierCoeff g n := by
  let gn : C(UnitAddTorus (Module.Free.ChooseBasisIndex ℤ I), ℂ) :=
    UnitAddTorus.mFourier (-n) * g
  have hneg : idealTraceFrequency F I (-n) = -(idealTraceFrequency F I n) := by
    simp [idealTraceFrequency]
  have hchar (y : InfinitePlace F → ℂ) :
      psiInf (-(idealTraceFrequency F I n)) y =
        UnitAddTorus.mFourier (-n)
          (fun i => ((idealArchBasis F I).equivFun y i : UnitAddCircle)) := by
    have h := idealTraceFrequency_fourier_character F I (-n) ((idealArchBasis F I).equivFun y)
    simpa only [hneg, LinearEquiv.symm_apply_apply] using h
  have hcoef : (∫ u, gn u) = UnitAddTorus.mFourierCoeff g n := by
    change (∫ u, gn u) =
      ∫ u : UnitAddTorus (Module.Free.ChooseBasisIndex ℤ I),
        UnitAddTorus.mFourier (-n) u • g u
        ∂Measure.pi (fun _ : Module.Free.ChooseBasisIndex ℤ I =>
          (AddCircle.haarAddCircle : Measure UnitAddCircle))
    have hunit : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
      simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
    rw [volume_pi]
    simp_rw [hunit]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by simp [gn, smul_eq_mul])
  calc
    _ = ((volume Pd).toReal : ℂ)⁻¹ *
        (∫ y in Pd, gn (fun i => ((idealArchBasis F I).equivFun y i : UnitAddCircle))) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by simp [gn, hchar y, mul_comm])
    _ = ∫ u, gn u := idealTorus_normalized_integral F I Pd hPd gn
    _ = UnitAddTorus.mFourierCoeff g n := hcoef

end ArtinPrimitiveRoots.A1.Theta
