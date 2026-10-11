import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianUniformBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

local instance frequencyMeasurable (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) :=
  borel _
local instance frequencyBorel (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The stabilized Gaussian as a function of frequency, extended by zero at zero.
The extension changes no Haar integral and does not assert stabilization there. -/
def frequencyStableValue {A : AddCharData F} (W : LocalGaussianData A)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) (t : v.adicCompletion F) : ℂ := by
  classical
  exact if ht : t = 0 then 0 else W.stableValue v (a * Units.mk0 t ht)

/-- Pass the actual finite Gaussian integrals through a compact frequency integral.
Character regularity and the norm Jacobian remain explicit. Stabilization gives the
almost everywhere limit, and the uniform inverse-square-root estimate dominates it.
This is the cutoff passage for the later Fourier support test. -/
theorem frequency_integral_tendsto_stable (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F)
    (hregular : LocalCharacterRegular A v)
    (hscale : ∀ c : (v.adicCompletion F)ˣ,
      Measure.map (fun x : v.adicCompletion F => (c : v.adicCompletion F) * x) (W.measure v) =
        (ENNReal.ofReal ‖(c : v.adicCompletion F)‖)⁻¹ • W.measure v)
    (a : (v.adicCompletion F)ˣ) (M : ℤ) :
    Filter.Tendsto
      (fun N : ℕ => ∫ t in localBallInt v M, A.ψ v (-t) *
        (∫ x in localBall v N, A.ψ v ((a : v.adicCompletion F) * t * x ^ 2)
          ∂W.measure v) ∂W.measure v)
      Filter.atTop
      (𝓝 (∫ t in localBallInt v M, A.ψ v (-t) * frequencyStableValue W v a t
        ∂W.measure v)) := by
  let : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (L := v.adicCompletion F)
      (Γ₀ := WithZero (Multiplicative ℤ))
  have : Measure.IsAddHaarMeasure (W.measure v) := W.isHaar v
  let G := fun (N : ℕ) (t : v.adicCompletion F) =>
    ∫ x in localBall v N, A.ψ v ((a : v.adicCompletion F) * t * x ^ 2) ∂W.measure v
  have hG : ∀ (N : ℕ) (t : v.adicCompletion F) (ht : t ≠ 0),
      G N t = quadraticIntegral A v (W.measure v) (a * Units.mk0 t ht) N := by
    intro N t ht
    rfl
  obtain ⟨C, hCpos, hC⟩ := uniform_quadratic_integral_norm_bound A W v
    (fun x => (hregular.2.2 x).le) hscale
  let bound := fun t : v.adicCompletion F =>
    (C * ‖(a : v.adicCompletion F)‖ ^ (-(1 / 2 : ℝ))) * ‖t‖ ^ (-(1 / 2 : ℝ))
  have hboundint : Integrable bound ((W.measure v).restrict (localBallInt v M)) :=
    (inverse_sqrt_norm_integrableOn_localBallInt A W v hscale M).const_mul _
  have hzero : ∀ᵐ t ∂(W.measure v).restrict (localBallInt v M), t ≠ 0 :=
    ae_restrict_of_ae ((W.measure v).ae_ne 0)
  have hGmeas : ∀ N, StronglyMeasurable (G N) := by
    intro N
    have hcont : Continuous (fun z : v.adicCompletion F × v.adicCompletion F =>
        A.ψ v ((a : v.adicCompletion F) * z.1 * z.2 ^ 2)) :=
      hregular.1.comp ((continuous_const.mul continuous_fst).mul (continuous_snd.pow 2))
    exact hcont.stronglyMeasurable.integral_prod_right'
  have hmeas : ∀ N, AEStronglyMeasurable
      (fun t : v.adicCompletion F => A.ψ v (-t) * G N t)
      ((W.measure v).restrict (localBallInt v M)) := by
    intro N
    exact ((hregular.1.comp continuous_neg).stronglyMeasurable.mul (hGmeas N)).aestronglyMeasurable
  have hbound : ∀ N, ∀ᵐ t ∂(W.measure v).restrict (localBallInt v M),
      ‖A.ψ v (-t) * G N t‖ ≤ bound t := by
    intro N
    filter_upwards [hzero] with t ht
    rw [norm_mul, hregular.2.2 (-t), one_mul, hG N t ht]
    have h := hC (a * Units.mk0 t ht) N
    simpa only [bound, Units.val_mul, Units.val_mk0, norm_mul,
      Real.mul_rpow (norm_nonneg (a : v.adicCompletion F)) (norm_nonneg t), mul_assoc] using h
  have hlim : ∀ᵐ t ∂(W.measure v).restrict (localBallInt v M),
      Filter.Tendsto (fun N : ℕ => A.ψ v (-t) * G N t) Filter.atTop
        (𝓝 (A.ψ v (-t) * frequencyStableValue W v a t)) := by
    filter_upwards [hzero] with t ht
    simp only [frequencyStableValue, dite_eq_right ht]
    have heq : (fun N : ℕ => A.ψ v (-t) * G N t) =ᶠ[Filter.atTop]
        (fun _ => A.ψ v (-t) * W.stableValue v (a * Units.mk0 t ht)) := by
      filter_upwards [Filter.eventually_ge_atTop (W.cutoff v (a * Units.mk0 t ht))] with N hN
      rw [hG N t ht, W.stable v (a * Units.mk0 t ht) N hN]
      rfl
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  exact tendsto_integral_of_dominated_convergence bound hmeas hboundint hbound hlim

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
