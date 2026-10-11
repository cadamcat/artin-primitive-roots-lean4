import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSupport
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianFrequency

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

local instance fourierSeparationMeasurable (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance fourierSeparationBorel (v : FinPlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- A compact frequency test separates the actual stable Gaussians of a nonsquare and one.
Finite Fourier orthogonality evaluates both cutoff tests; dominated convergence
passes to their stable values. Positive finite Haar masses make the unscaled test nonzero.
Regularity and the scalar Jacobian remain explicit. -/
theorem stable_gaussian_fourier_separation (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F)
    (hregular : LocalCharacterRegular A v)
    (hscale : ∀ c : (v.adicCompletion F)ˣ,
      Measure.map (fun x : v.adicCompletion F => (c : v.adicCompletion F) * x) (W.measure v) =
        (ENNReal.ofReal ‖(c : v.adicCompletion F)‖)⁻¹ • W.measure v)
    (a : (v.adicCompletion F)ˣ) (ha : ¬ IsSquare (a : v.adicCompletion F)) :
    ∃ M : ℤ,
      (∫ t in localBallInt v M, A.ψ v (-t) * frequencyStableValue W v a t
        ∂W.measure v) = 0 ∧
      (∫ t in localBallInt v M, A.ψ v (-t) * frequencyStableValue W v 1 t
        ∂W.measure v) ≠ 0 := by
  have : Measure.IsAddHaarMeasure (W.measure v) := W.isHaar v
  obtain ⟨M, N₀, P, _hP, _hPcompact, hPpos, hPfinite, hscaled, hunscaled⟩ :=
    gaussian_fourier_support_separation A v (W.measure v) (W.isHaar v) hregular a ha
  obtain ⟨b, hb⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp M)
  have hb0 : b ≠ 0 := by
    intro h
    apply WithZero.exp_ne_zero (a := M)
    exact hb.symm.trans (by simp only [h, map_zero])
  have hbnorm : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have hTset : localBallInt v M = Metric.closedBall (0 : v.adicCompletion F) ‖b‖ := by
    ext t
    simpa only [localBallInt, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, hb] using
      (Valued.toNormedField.norm_le_iff (L := v.adicCompletion F)
        (Γ₀ := WithZero (Multiplicative ℤ)) (x := t) (x' := b)).symm
  have hTpos : 0 < W.measure v (localBallInt v M) := by
    rw [hTset]
    exact (Metric.isOpen_ball.measure_pos (W.measure v)
      ⟨0, Metric.mem_ball_self hbnorm⟩).trans_le
      (measure_mono Metric.ball_subset_closedBall)
  have hTfinite : W.measure v (localBallInt v M) < ⊤ := by
    rw [hTset]
    exact (isCompact_closedBall _ _).measure_lt_top
  let Test := fun (c : (v.adicCompletion F)ˣ) (N : ℕ) =>
    ∫ t in localBallInt v M, A.ψ v (-t) *
      (∫ x in localBall v N, A.ψ v ((c : v.adicCompletion F) * t * x ^ 2)
        ∂W.measure v) ∂W.measure v
  let L := fun c : (v.adicCompletion F)ˣ =>
    ∫ t in localBallInt v M, A.ψ v (-t) * frequencyStableValue W v c t ∂W.measure v
  have hlim : ∀ c, Filter.Tendsto (Test c) Filter.atTop (𝓝 (L c)) := fun c =>
    frequency_integral_tendsto_stable A W v hregular hscale c M
  have hzero : ∀ N, Test a N = 0 := by
    intro N
    dsimp only [Test]
    rw [finite_gaussian_fourier_test A v (W.measure v) (W.isHaar v) hregular a M N]
    change ((W.measure v (localBallInt v M)).toReal : ℂ) *
      ((W.measure v {x | x ∈ localBall v N ∧
        (a : v.adicCompletion F) * x ^ 2 - 1 ∈ localBallAnnihilator A v M}).toReal : ℂ) = 0
    rw [hscaled N]
    simp only [measure_empty, ENNReal.toReal_zero, Complex.ofReal_zero, mul_zero]
  let C : ℂ := ((W.measure v (localBallInt v M)).toReal : ℂ) *
    ((W.measure v P).toReal : ℂ)
  have hconstant : Test 1 =ᶠ[Filter.atTop] (fun _ => C) := by
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    dsimp only [Test, C]
    rw [finite_gaussian_fourier_test A v (W.measure v) (W.isHaar v) hregular 1 M N]
    simp only [Units.val_one, one_mul]
    change ((W.measure v (localBallInt v M)).toReal : ℂ) *
      ((W.measure v {x | x ∈ localBall v N ∧
        x ^ 2 - 1 ∈ localBallAnnihilator A v M}).toReal : ℂ) = _
    rw [hunscaled N hN]
  have hLzero : L a = 0 :=
    tendsto_nhds_unique_of_eventuallyEq (hlim a) tendsto_const_nhds
      (Filter.Eventually.of_forall hzero)
  have hLone : L 1 = C :=
    tendsto_nhds_unique_of_eventuallyEq (hlim 1) tendsto_const_nhds hconstant
  have hTreal : 0 < (W.measure v (localBallInt v M)).toReal :=
    ENNReal.toReal_pos hTpos.ne' hTfinite.ne
  have hPreal : 0 < (W.measure v P).toReal := ENNReal.toReal_pos hPpos.ne' hPfinite.ne
  refine ⟨M, hLzero, ?_⟩
  change L 1 ≠ 0
  rw [hLone]
  exact mul_ne_zero (by exact_mod_cast hTreal.ne') (by exact_mod_cast hPreal.ne')

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
