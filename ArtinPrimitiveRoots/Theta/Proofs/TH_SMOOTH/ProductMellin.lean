import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.CutoffMass
import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.WeightedHaar
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open ArtinPrimitiveRoots.A1
open scoped Classical

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

variable {F : Type} [Field F] [NumberField F]

/-- The finite cutoff times all weighted archimedean Bessel factors is integrable,
and its integral factors into the cutoff mass and local Mellin values. -/
theorem bessel_product_mellin {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, ArtinPrimitiveRoots.A1.Theta.LocHaar v)
    (U : Set (∀ v : S.Sf, v.1.adicCompletion F)) (hUo : IsOpen U) (hUc : IsCompact U)
    (hU1 : (1 : ∀ v : S.Sf, v.1.adicCompletion F) ∈ U)
    (hUunit : ∀ y ∈ U, ∀ v : S.Sf, Valued.v (y v) = 1)
    (cS : InfinitePlace F → ℝ) (hcS : ∀ w, 0 < cS w)
    (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    Integrable (fun y : S.FS => (if y.1 ∈ U then (1 : ℂ) else 0) *
      ∏ w : InfinitePlace F, (Complex.normSq (y.2 w) : ℂ) ^ s *
        (Complex.normSq (y.2 w) : ℂ) * (besselK (1 / 3) (cS w * ‖y.2 w‖) : ℂ))
      ((Measure.pi (fun v : S.Sf => (μ v.1).μ.withDensity
        (fun y => ENNReal.ofReal ((absFin v.1 y)⁻¹)))).prod
        (Measure.pi (fun _ : InfinitePlace F => volume.withDensity
          (fun z : ℂ => ENNReal.ofReal ((Complex.normSq z)⁻¹))))) ∧
    (∫ y : S.FS, (if y.1 ∈ U then (1 : ℂ) else 0) *
      ∏ w : InfinitePlace F, (Complex.normSq (y.2 w) : ℂ) ^ s *
        (Complex.normSq (y.2 w) : ℂ) * (besselK (1 / 3) (cS w * ‖y.2 w‖) : ℂ)
      ∂((Measure.pi (fun v : S.Sf => (μ v.1).μ.withDensity
        (fun y => ENNReal.ofReal ((absFin v.1 y)⁻¹)))).prod
        (Measure.pi (fun _ : InfinitePlace F => volume.withDensity
          (fun z : ℂ => ENNReal.ofReal ((Complex.normSq z)⁻¹)))))) =
      ((Measure.pi (fun v : S.Sf => (μ v.1).μ.withDensity
        (fun y => ENNReal.ofReal ((absFin v.1 y)⁻¹))) U).toReal : ℂ) *
        ∏ w : InfinitePlace F, (Real.pi : ℂ) *
          ((2 : ℂ) ^ (2 * s + 1) * (cS w : ℂ) ^ (-2 * s - 2) *
            Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by
  classical
  let νfin (v : S.Sf) : Measure (v.1.adicCompletion F) :=
    (μ v.1).μ.withDensity (fun y => ENNReal.ofReal ((absFin v.1 y)⁻¹))
  let νC : Measure ℂ :=
    volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Complex.normSq z)⁻¹))
  let H (w : InfinitePlace F) (z : ℂ) : ℂ :=
    (Complex.normSq z : ℂ) ^ s * (Complex.normSq z : ℂ) *
      (besselK (1 / 3) (cS w * ‖z‖) : ℂ)
  let Hfin (y : ∀ v : S.Sf, v.1.adicCompletion F) : ℂ := if y ∈ U then 1 else 0
  have : ∀ v : S.Sf, SigmaFinite (μ v.1).μ :=
    fun v => locHaar_sigmaFinite v.1 (μ v.1)
  have : ∀ v : S.Sf, SigmaFinite (νfin v) := fun v => by
    dsimp [νfin]
    infer_instance
  have : SigmaFinite νC := by
    dsimp [νC]
    infer_instance
  have hUm : MeasurableSet U := hUo.measurableSet
  have hfin : Measure.pi νfin U < ⊤ :=
    (finite_unit_cutoff_mass S μ U hUo hUc hU1 hUunit).2.2
  have hcut : Integrable Hfin (Measure.pi νfin) :=
    (integrableOn_const (C := (1 : ℂ)) hfin.ne).integrable_indicator hUm
  have hcutval : (∫ y, Hfin y ∂Measure.pi νfin) =
      ((Measure.pi νfin U).toReal : ℂ) := by
    simpa only [Set.indicator_apply, Complex.real_smul, mul_one, measureReal_def] using
      (integral_indicator_const (μ := Measure.pi νfin) (1 : ℂ) hUm)
  have hlocal (w : InfinitePlace F) : Integrable (H w) νC ∧
      (∫ z, H w z ∂νC) = (Real.pi : ℂ) *
        ((2 : ℂ) ^ (2 * s + 1) * (cS w : ℂ) ^ (-2 * s - 2) *
          Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) :=
    bessel_complex_mellin (cS w) (hcS w) s hs
  have harch : Integrable (fun z : InfinitePlace F → ℂ => ∏ w, H w (z w))
      (Measure.pi fun _ : InfinitePlace F => νC) :=
    Integrable.fintype_prod_dep fun w => (hlocal w).1
  constructor
  · change Integrable (fun y : S.FS => Hfin y.1 * ∏ w, H w (y.2 w))
        ((Measure.pi νfin).prod (Measure.pi fun _ : InfinitePlace F => νC))
    exact Integrable.mul_prod (f := Hfin) (g := fun z : InfinitePlace F → ℂ => ∏ w, H w (z w))
      (μ := Measure.pi νfin) (ν := Measure.pi fun _ : InfinitePlace F => νC) hcut harch
  · change (∫ y : S.FS, Hfin y.1 * ∏ w, H w (y.2 w)
        ∂((Measure.pi νfin).prod (Measure.pi fun _ : InfinitePlace F => νC))) = _
    rw [integral_prod_mul (μ := Measure.pi νfin)
      (ν := Measure.pi fun _ : InfinitePlace F => νC) Hfin
      (fun z : InfinitePlace F → ℂ => ∏ w, H w (z w)),
      hcutval, integral_fintype_prod_eq_prod H]
    congr 1
    apply Finset.prod_congr rfl
    intro w _
    exact (hlocal w).2

end ArtinPrimitiveRoots.Proofs.thsol_smooth
