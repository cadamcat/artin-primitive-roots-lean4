import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.mem_span_idealArchBasis
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
open NumberField Module MeasureTheory MeasureTheory.Measure
open scoped Classical ENNReal NNReal
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F]
variable (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ)

/-- Normalizing the integral of a torus function over any ideal-basis
fundamental domain gives its integral on the standard unit torus. -/
theorem idealTorus_normalized_integral [Fintype (Module.Free.ChooseBasisIndex ℤ I)]
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (idealArchBasis F I))).toAddSubgroup Pd volume)
    (g : C(UnitAddTorus (Module.Free.ChooseBasisIndex ℤ I), ℂ)) :
    ((volume Pd).toReal : ℂ)⁻¹ *
      (∫ y in Pd, g (fun i => ((idealArchBasis F I).equivFun y i : UnitAddCircle))) =
        ∫ u : UnitAddTorus (Module.Free.ChooseBasisIndex ℤ I), g u := by
  let b := idealArchBasis F I
  let q : (Module.Free.ChooseBasisIndex ℤ I → ℝ) →
      UnitAddTorus (Module.Free.ChooseBasisIndex ℤ I) := fun x i => (x i : UnitAddCircle)
  let f : (InfinitePlace F → ℂ) → ℂ := fun y => g (q (b.equivFun y))
  let s := ZSpan.fundamentalDomain b
  let cube : Set (Module.Free.ChooseBasisIndex ℤ I → ℝ) := Set.Icc 0 1
  let : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hs : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup s volume :=
    ZSpan.isAddFundamentalDomain' b volume
  have hperiod : ∀ (m : (Submodule.span ℤ (Set.range b)).toAddSubgroup) y,
      f (m +ᵥ y) = f y := by
    intro m y
    apply congrArg g
    funext i
    change ((b.equivFun ((m : InfinitePlace F → ℂ) + y) i : ℝ) : UnitAddCircle) = _
    rw [map_add, Pi.add_apply, AddCircle.coe_add]
    obtain ⟨n, hn⟩ := (b.mem_span_iff_repr_mem ℤ (m : InfinitePlace F → ℂ)).mp m.property i
    have hm : (b.equivFun (m : InfinitePlace F → ℂ) i : UnitAddCircle) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
      exact ⟨n, by simpa [Basis.equivFun_apply, zsmul_eq_mul] using hn⟩
    rw [hm, zero_add]
  have hint : ∫ y in Pd, f y = ∫ y in s, f y := hPd.setIntegral_eq hs hperiod
  have hvol : volume Pd = volume s := hPd.measure_eq hs
  have hsone : b.addHaar s = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b b.addHaar)]
    exact b.addHaar_self
  have hbmap : b.map b.equivFunL.toLinearEquiv =
      Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ I) := by
    apply Basis.eq_of_apply_eq
    intro i
    funext j
    simp [Basis.map_apply, Basis.equivFunL_apply, Pi.basisFun_apply,
      Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hmap : Measure.map b.equivFunL b.addHaar =
      (volume : Measure (Module.Free.ChooseBasisIndex ℤ I → ℝ)) := by
    rw [Basis.map_addHaar b b.equivFunL, hbmap, Basis.addHaar_def,
      Basis.parallelepiped_basisFun, addHaarMeasure_eq_volume_pi]
  have hpre : b.equivFunL ⁻¹' cube = _root_.parallelepiped b := by
    ext y
    simp [cube, Set.mem_Icc, Pi.le_def, parallelepiped_basis_eq,
      Basis.equivFunL_apply, forall_and]
  have hintbase : ∫ y in s, f y ∂b.addHaar = ∫ u, g u := by
    calc
      ∫ y in s, f y ∂b.addHaar = ∫ y in _root_.parallelepiped b, f y ∂b.addHaar :=
        setIntegral_congr_set (ZSpan.fundamentalDomain_ae_parallelepiped b b.addHaar)
      _ = ∫ x in cube, g (q x) := by
        have h := setIntegral_map_equiv (μ := b.addHaar)
          b.equivFunL.toHomeomorph.toMeasurableEquiv (fun x => g (q x)) cube
        change (∫ x in cube, g (q x) ∂Measure.map b.equivFunL b.addHaar) =
          ∫ y in b.equivFunL ⁻¹' cube, f y ∂b.addHaar at h
        rw [hmap, hpre] at h
        exact h.symm
      _ = ∫ u, g u := by
        have hae : {x : Module.Free.ChooseBasisIndex ℤ I → ℝ |
            ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =ᵐ[volume] cube := by
          simpa [cube, Set.pi, Set.mem_Icc, Pi.le_def, volume_pi] using
            (Measure.univ_pi_Ioc_ae_eq_Icc
              (μ := fun _ : Module.Free.ChooseBasisIndex ℤ I => (volume : Measure ℝ))
              (f := (0 : Module.Free.ChooseBasisIndex ℤ I → ℝ)) (g := 1))
        have htor : (∫ u : UnitAddTorus (Module.Free.ChooseBasisIndex ℤ I), g u) =
            ∫ x in {x : Module.Free.ChooseBasisIndex ℤ I → ℝ |
              ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, g (q x) := by
          have h := UnitAddTorus.integral_preimage g 0
          simp only [Pi.zero_apply, zero_add] at h
          change (∫ u : UnitAddTorus (Module.Free.ChooseBasisIndex ℤ I), g u
            ∂Measure.pi (fun _ : Module.Free.ChooseBasisIndex ℤ I =>
              (AddCircle.haarAddCircle : Measure UnitAddCircle))) =
              ∫ x in {x : Module.Free.ChooseBasisIndex ℤ I → ℝ |
                ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, g (q x) at h
          have hunit : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
            simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
          rw [volume_pi]
          simp_rw [hunit]
          exact h
        exact (setIntegral_congr_set (f := fun x => g (q x)) hae).symm.trans htor.symm
  let c := addHaarScalarFactor (volume : Measure (InfinitePlace F → ℂ)) b.addHaar
  have hc : c ≠ 0 := (addHaarScalarFactor_pos_of_isAddHaarMeasure
    (volume : Measure (InfinitePlace F → ℂ)) b.addHaar).ne'
  have hscale : (volume : Measure (InfinitePlace F → ℂ)) = c • b.addHaar :=
    isAddLeftInvariant_eq_smul _ _
  have hvolc : volume Pd = (c : ℝ≥0∞) := by
    rw [hvol, hscale, Measure.smul_apply, hsone]
    simp
  have hcc : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  change ((volume Pd).toReal : ℂ)⁻¹ * (∫ y in Pd, f y) = _
  rw [hvolc, hint, hscale, Measure.restrict_smul, integral_smul_nnreal_measure, hintbase]
  simp [NNReal.smul_def, Complex.real_smul, hcc]

end ArtinPrimitiveRoots.A1.Theta
