import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Complex
import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Finite
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1

/-- The self-dual Fourier transform of a local tensor differs from the product of
its local Fourier transforms by the Haar normalization scalar. -/
theorem schwartz_tensor_fourier
    {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) (A : AddCharData F)
    (sd : S.SelfDualMeasure A) (μ : ∀ v : FinPlace F, Theta.LocHaar v)
    (ff : ∀ v : S.Sf, S.FiniteTest v)
    (fc : InfinitePlace F → SchwartzMap ℂ ℂ) :
    ∃ c : ℂ, ∀ y : S.FS,
      S.fourier A sd.measure
        (fun x : S.FS => (∏ v : S.Sf, (ff v).1 (x.1 v)) *
          ∏ w : InfinitePlace F, fc w (x.2 w)) y =
        c * ((∏ v : S.Sf,
          ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier v.1 A (μ v.1)
            (ff v).1 (y.1 v)) *
          ∏ w : InfinitePlace F,
            ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz (fc w) (y.2 w)) := by
  letI : ∀ v : S.Sf, ProperSpace (v.1.adicCompletion F) :=
    fun v => ArtinPrimitiveRoots.A2.bridgeFin_properSpace v.1
  letI : ∀ v : S.Sf, SigmaFinite (μ v.1).μ := fun v =>
    ArtinPrimitiveRoots.Proofs.thsol_smooth.locHaar_sigmaFinite v.1 (μ v.1)
  letI : ∀ v : S.Sf, Measure.IsAddHaarMeasure (μ v.1).μ := fun v => (μ v.1).isHaar
  haveI hνf : Measure.IsAddHaarMeasure (Measure.pi fun v : S.Sf => (μ v.1).μ) := by
    infer_instance
  haveI hνc : Measure.IsAddHaarMeasure
      (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ)) := by infer_instance
  let m0 : MeasurableSpace S.FS := inferInstance
  let ν0 : @Measure S.FS m0 :=
    (Measure.pi fun v : S.Sf => (μ v.1).μ).prod
      (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ))
  haveI hν0 : Measure.IsAddHaarMeasure ν0 := by dsimp [ν0, m0]; infer_instance
  haveI hBorel0 : @BorelSpace S.FS _ m0 := by infer_instance
  letI : MeasurableSpace S.FS := borel S.FS
  letI : BorelSpace S.FS := ⟨rfl⟩
  let e : @MeasurableEquiv S.FS S.FS m0 (borel S.FS) :=
    @MeasurableEquiv.mk S.FS S.FS m0 (borel S.FS) (Equiv.refl S.FS)
      (@Continuous.measurable S.FS S.FS _ m0 _ _ (borel S.FS) _ id continuous_id)
      (@Continuous.measurable S.FS S.FS _ (borel S.FS) _ _ m0 hBorel0 id continuous_id)
  let ν : Measure S.FS := @Measure.map S.FS S.FS m0 (borel S.FS) id ν0
  letI : Measure.IsAddHaarMeasure ν := by
    exact @AddEquiv.isAddHaarMeasure_map S.FS m0 _ _ ν0 hν0 hBorel0 _
      S.FS _ _ (borel S.FS) _ _ (AddEquiv.refl S.FS) continuous_id continuous_id
  letI : Measure.IsAddHaarMeasure sd.measure := sd.isHaar
  let q : NNReal := Measure.addHaarScalarFactor sd.measure ν
  have hμ : sd.measure = q • ν := Measure.isAddLeftInvariant_eq_smul sd.measure ν
  refine ⟨((q : ℝ) : ℂ), ?_⟩
  intro y
  let f (v : S.Sf) (x : v.1.adicCompletion F) : ℂ :=
    (ff v).1 x * A.ψ v.1 (-(x * y.1 v))
  let g (w : InfinitePlace F) (x : ℂ) : ℂ := fc w x * psiC (-(x * y.2 w))
  have hpoint (x : S.FS) :
      ((∏ v : S.Sf, (ff v).1 (x.1 v)) * ∏ w : InfinitePlace F, fc w (x.2 w)) *
        S.e A (-(x * y)) = (∏ v : S.Sf, f v (x.1 v)) * ∏ w : InfinitePlace F, g w (x.2 w) := by
    simp only [SData.e, Prod.fst_neg, Prod.snd_neg, Prod.fst_mul, Prod.snd_mul,
      Pi.neg_apply, Pi.mul_apply, f, g, Finset.prod_mul_distrib]
    ring
  unfold SData.fourier
  rw [hμ, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]
  congr 1
  change (∫ x, ((∏ v : S.Sf, (ff v).1 (x.1 v)) *
    ∏ w : InfinitePlace F, fc w (x.2 w)) * S.e A (-(x * y)) ∂ν) = _
  refine (show (∫ x, ((∏ v : S.Sf, (ff v).1 (x.1 v)) *
      ∏ w : InfinitePlace F, fc w (x.2 w)) * S.e A (-(x * y)) ∂ν) =
      @integral S.FS ℂ _ _ m0 ν0
        (fun x => ((∏ v : S.Sf, (ff v).1 (x.1 v)) *
          ∏ w : InfinitePlace F, fc w (x.2 w)) * S.e A (-(x * y))) from
      @integral_map_equiv S.FS ℂ _ _ m0 ν0 S.FS (borel S.FS) e _).trans ?_
  simp_rw [hpoint]
  letI : MeasurableSpace S.FS := m0
  change (∫ x, (∏ v : S.Sf, f v (x.1 v)) *
    ∏ w : InfinitePlace F, g w (x.2 w)
    ∂(Measure.pi fun v : S.Sf => (μ v.1).μ).prod
      (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ))) = _
  refine (integral_prod_mul
    (μ := Measure.pi fun v : S.Sf => (μ v.1).μ)
    (ν := Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ))
    (fun x : ∀ v : S.Sf, v.1.adicCompletion F => ∏ v : S.Sf, f v (x v))
    (fun x : InfinitePlace F → ℂ => ∏ w : InfinitePlace F, g w (x w))).trans ?_
  have hf := integral_fintype_prod_eq_prod (μ := fun v : S.Sf => (μ v.1).μ) f
  have hg := integral_fintype_prod_eq_prod
    (μ := fun _ : InfinitePlace F => (volume : Measure ℂ)) g
  refine (congrArg₂ (fun a b : ℂ => a * b) hf hg).trans ?_
  exact congrArg₂ (fun a b : ℂ => a * b) rfl
    (Finset.prod_congr rfl fun w hw =>
      (ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierSchwartz_eq_integral
        (fc w) (y.2 w)).symm)

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
