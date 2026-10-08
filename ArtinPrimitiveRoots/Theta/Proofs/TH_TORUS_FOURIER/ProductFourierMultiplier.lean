import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.TorusDerivativeLift
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.FourierCoordinateDerivative

set_option autoImplicit false

open MeasureTheory AddCircle
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private structure SmoothPeriodicFunction (n : ℕ) where
  fn : (Fin (n + 1) → ℝ) → ℂ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fn
  periodic : ∀ (x : Fin (n + 1) → ℝ) (k : Fin (n + 1) → ℤ),
    fn (x + fun j => (k j : ℝ)) = fn x

private def smoothPeriodicDerivative {n : ℕ} (f : SmoothPeriodicFunction n)
    (i : Fin (n + 1)) : SmoothPeriodicFunction n where
  fn x := fderiv ℝ f.fn x (Pi.single i (1 : ℝ))
  smooth := (smooth_periodic_coordinate_derivative f.fn f.smooth f.periodic i).1
  periodic := (smooth_periodic_coordinate_derivative f.fn f.smooth f.periodic i).2.1

private def smoothPeriodicLift {n : ℕ} (f : SmoothPeriodicFunction n) :
    C(UnitAddTorus (Fin (n + 1)), ℂ) :=
  Classical.choose (periodic_torus_lift f.fn f.smooth.continuous f.periodic)

private theorem smoothPeriodicLift_spec {n : ℕ} (f : SmoothPeriodicFunction n)
    (x : Fin (n + 1) → ℝ) :
    smoothPeriodicLift f (fun j => (x j : UnitAddCircle)) = f.fn x :=
  Classical.choose_spec (periodic_torus_lift f.fn f.smooth.continuous f.periodic) x

private theorem torus_lift_unique {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℂ)
    (F G : C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hF : ∀ x : Fin (n + 1) → ℝ, F (fun j => (x j : UnitAddCircle)) = f x)
    (hG : ∀ x : Fin (n + 1) → ℝ, G (fun j => (x j : UnitAddCircle)) = f x) :
    F = G := by
  ext z
  let x : Fin (n + 1) → ℝ := fun j => (AddCircle.equivIco (1 : ℝ) 0 (z j) : ℝ)
  have hx : (fun j => (x j : UnitAddCircle)) = z := by
    funext j
    exact AddCircle.coe_equivIco
  rw [← hx, hF, hG]

private theorem smoothPeriodicLift_derivative_coeff {n : ℕ}
    (f : SmoothPeriodicFunction n) (i : Fin (n + 1)) (k : Fin (n + 1) → ℤ) :
    UnitAddTorus.mFourierCoeff (smoothPeriodicLift (smoothPeriodicDerivative f i)) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) *
        UnitAddTorus.mFourierCoeff (smoothPeriodicLift f) k := by
  obtain ⟨F, F', hF, hF', hD⟩ :=
    periodic_torus_derivative_lift f.fn f.smooth f.periodic i
  have hEq := torus_lift_unique f.fn F (smoothPeriodicLift f) hF
    (smoothPeriodicLift_spec f)
  have hEq' := torus_lift_unique (smoothPeriodicDerivative f i).fn F'
    (smoothPeriodicLift (smoothPeriodicDerivative f i)) hF'
    (smoothPeriodicLift_spec (smoothPeriodicDerivative f i))
  rw [hEq, hEq'] at hD
  exact mFourierCoeff_coordinate_derivative i _ _ hD k

private def smoothPeriodicFactor {n : ℕ} (f : SmoothPeriodicFunction n)
    (i : Fin (n + 1)) : SmoothPeriodicFunction n where
  fn x := f.fn x - (smoothPeriodicDerivative (smoothPeriodicDerivative f i) i).fn x
  smooth := f.smooth.sub (smoothPeriodicDerivative (smoothPeriodicDerivative f i) i).smooth
  periodic x k := by
    rw [f.periodic, (smoothPeriodicDerivative (smoothPeriodicDerivative f i) i).periodic]

private theorem mFourierCoeff_sub_continuous {n : ℕ}
    (F G : C(UnitAddTorus (Fin (n + 1)), ℂ)) (k : Fin (n + 1) → ℤ) :
    UnitAddTorus.mFourierCoeff (F - G) k =
      UnitAddTorus.mFourierCoeff F k - UnitAddTorus.mFourierCoeff G k := by
  unfold UnitAddTorus.mFourierCoeff
  simp only [ContinuousMap.sub_apply, smul_sub]
  exact integral_sub
    ((UnitAddTorus.mFourier (-k) * F).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((UnitAddTorus.mFourier (-k) * G).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

private theorem smoothPeriodicFactor_coeff {n : ℕ}
    (f : SmoothPeriodicFunction n) (i : Fin (n + 1)) (k : Fin (n + 1) → ℤ) :
    UnitAddTorus.mFourierCoeff (smoothPeriodicLift (smoothPeriodicFactor f i)) k =
      ((1 + (2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ) : ℂ) *
        UnitAddTorus.mFourierCoeff (smoothPeriodicLift f) k := by
  have hLift : smoothPeriodicLift (smoothPeriodicFactor f i) =
      smoothPeriodicLift f -
        smoothPeriodicLift (smoothPeriodicDerivative (smoothPeriodicDerivative f i) i) := by
    apply torus_lift_unique (smoothPeriodicFactor f i).fn
    · exact smoothPeriodicLift_spec _
    · intro x
      simp only [ContinuousMap.sub_apply, smoothPeriodicLift_spec]
      rfl
  rw [hLift, mFourierCoeff_sub_continuous, smoothPeriodicLift_derivative_coeff,
    smoothPeriodicLift_derivative_coeff]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination
    -(2 * (Real.pi : ℂ) * (k i : ℂ)) ^ 2 *
      UnitAddTorus.mFourierCoeff (smoothPeriodicLift f) k * hI

private theorem smoothPeriodicFactors_coeff {n : ℕ} (s : Finset (Fin (n + 1)))
    (f : SmoothPeriodicFunction n) :
    ∃ u : SmoothPeriodicFunction n, ∀ k : Fin (n + 1) → ℤ,
      UnitAddTorus.mFourierCoeff (smoothPeriodicLift u) k =
        (∏ i ∈ s, ((1 + (2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ) : ℂ)) *
          UnitAddTorus.mFourierCoeff (smoothPeriodicLift f) k := by
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨f, fun k => by simp⟩
  | @insert i s hi ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨smoothPeriodicFactor u i, ?_⟩
      intro k
      rw [smoothPeriodicFactor_coeff, hu, Finset.prod_insert hi]
      exact (mul_assoc _ _ _).symm

/-- Applying one factor `1 - ∂ᵢ²` in each coordinate yields a continuous torus
function whose Fourier coefficients have the full positive product multiplier. -/
theorem periodic_fourier_product_multiplier {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hper : ∀ (x : Fin (n + 1) → ℝ) (k : Fin (n + 1) → ℤ),
      f (x + fun j => (k j : ℝ)) = f x) :
    ∃ (F U : C(UnitAddTorus (Fin (n + 1)), ℂ)),
      (∀ x : Fin (n + 1) → ℝ, F (fun j => (x j : UnitAddCircle)) = f x) ∧
      ∀ k : Fin (n + 1) → ℤ,
        UnitAddTorus.mFourierCoeff U k =
          (∏ i : Fin (n + 1), ((1 + (2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ) : ℂ)) *
            UnitAddTorus.mFourierCoeff F k := by
  let f₀ : SmoothPeriodicFunction n := ⟨f, hf, hper⟩
  obtain ⟨u, hu⟩ := smoothPeriodicFactors_coeff Finset.univ f₀
  exact ⟨smoothPeriodicLift f₀, smoothPeriodicLift u, smoothPeriodicLift_spec f₀, hu⟩

end ArtinPrimitiveRoots.Proofs.thsol_torusf
