import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTorus_fourierCoeff_eq
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.unitTorus_lift_of_int_periodic
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.unitTorus_constant_of_nonzero_fourier_zero

set_option autoImplicit false
open NumberField Module MeasureTheory
open scoped Classical ENNReal
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ)

/-- An ideal-periodic continuous function is constant when all its
nonzero trace-frequency Fourier coefficients vanish. -/
theorem idealTorus_constant_of_nonzero_fourier_zero
    [Fintype (Module.Free.ChooseBasisIndex ℤ I)]
    (f : C(InfinitePlace F → ℂ, ℂ))
    (hper : ∀ ξ ∈ (I : Set F), ∀ x, f (x + infEmbA ξ) = f x)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (idealArchBasis F I))).toAddSubgroup Pd volume)
    (hzero : ∀ n : Module.Free.ChooseBasisIndex ℤ I → ℤ, n ≠ 0 →
      ((volume Pd).toReal : ℂ)⁻¹ *
        (∫ y in Pd, f y * psiInf (-(idealTraceFrequency F I n)) y) = 0) :
    ∀ y : InfinitePlace F → ℂ, f y = f 0 := by
  let b := idealArchBasis F I
  let fp : C(Module.Free.ChooseBasisIndex ℤ I → ℝ, ℂ) :=
    ⟨fun x => f (b.equivFun.symm x), f.continuous.comp b.equivFunL.symm.continuous⟩
  have hp : ∀ m : Module.Free.ChooseBasisIndex ℤ I → ℤ, ∀ x,
      fp (x + (fun i => (m i : ℝ))) = fp x := by
    intro m x
    have hm : b.equivFun.symm (fun i => (m i : ℝ)) ∈
        Submodule.span ℤ (Set.range b) := by
      apply (b.mem_span_iff_repr_mem ℤ _).mpr
      intro i
      refine ⟨m i, ?_⟩
      change (m i : ℝ) = b.equivFun (b.equivFun.symm (fun j => (m j : ℝ))) i
      rw [LinearEquiv.apply_symm_apply]
    obtain ⟨ξ, hξ, hEmb⟩ := (mem_span_idealArchBasis F I).mp hm
    change infEmbA ξ = b.equivFun.symm (fun i => (m i : ℝ)) at hEmb
    change f (b.equivFun.symm (x + (fun i => (m i : ℝ)))) = f (b.equivFun.symm x)
    rw [map_add, ← hEmb]
    exact hper ξ hξ (b.equivFun.symm x)
  obtain ⟨g, hg⟩ := unitTorus_lift_of_int_periodic fp hp
  have hgf (y : InfinitePlace F → ℂ) :
      g (fun i => (b.equivFun y i : UnitAddCircle)) = f y := by
    simpa only [fp, ContinuousMap.coe_mk, LinearEquiv.symm_apply_apply] using hg (b.equivFun y)
  have hcoeff : ∀ n : Module.Free.ChooseBasisIndex ℤ I → ℤ, n ≠ 0 →
      UnitAddTorus.mFourierCoeff g n = 0 := by
    intro n hn
    rw [← idealTorus_fourierCoeff_eq F I Pd hPd g n]
    change ((volume Pd).toReal : ℂ)⁻¹ *
      (∫ y in Pd, g (fun i => (b.equivFun y i : UnitAddCircle)) *
        psiInf (-(idealTraceFrequency F I n)) y) = 0
    simp_rw [hgf]
    exact hzero n hn
  have hconstant := unitTorus_constant_of_nonzero_fourier_zero g hcoeff
  intro y
  calc
    f y = g (fun i => (b.equivFun y i : UnitAddCircle)) := (hgf y).symm
    _ = UnitAddTorus.mFourierCoeff g 0 := hconstant _
    _ = g (fun i => (b.equivFun 0 i : UnitAddCircle)) := (hconstant _).symm
    _ = f 0 := hgf 0

end ArtinPrimitiveRoots.A1.Theta
