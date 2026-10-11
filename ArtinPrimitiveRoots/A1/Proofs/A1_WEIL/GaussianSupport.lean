import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianUniformBound
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.QuadraticSupport

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

local instance supportMeasurable (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) :=
  borel _
local instance supportBorel (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The frequency annihilator separates the two quadratic supports for a nonsquare.
The unscaled preimage has positive finite Haar mass and is eventually contained
in every spatial cutoff; the scaled preimage is empty at every cutoff.
Uses the actual character-annihilator bounds, polynomial
properness, and Haar positivity, without a Gaussian nondegeneracy assumption. -/
theorem gaussian_fourier_support_separation (A : AddCharData F) (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) (hμ : Measure.IsAddHaarMeasure μ)
    (hregular : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) (ha : ¬ IsSquare (a : v.adicCompletion F)) :
    ∃ (M : ℤ) (N₀ : ℕ) (P : Set (v.adicCompletion F)),
      P = {x | x ^ 2 - 1 ∈ localBallAnnihilator A v M} ∧
      IsCompact P ∧ 0 < μ P ∧ μ P < ⊤ ∧
      (∀ N : ℕ, {x | x ∈ localBall v N ∧
        (a : v.adicCompletion F) * x ^ 2 - 1 ∈ localBallAnnihilator A v M} = ∅) ∧
      (∀ N : ℕ, N₀ ≤ N → {x | x ∈ localBall v N ∧
        x ^ 2 - 1 ∈ localBallAnnihilator A v M} = P) := by
  have : Measure.IsAddHaarMeasure μ := hμ
  obtain ⟨r, hr, hempty, _hpos, _hfinite⟩ := nonsquare_quadratic_support_test μ a ha
  obtain ⟨M, hinner, houter⟩ := local_ball_annihilator_small A v hregular.2.1 r hr
  let T := localBallAnnihilator A v M
  let P := (fun x : v.adicCompletion F => x ^ 2 - 1) ⁻¹' T
  have hTclosed : IsClosed T := by
    have hsets : T = ⋂ t ∈ localBallInt v M,
        {z : v.adicCompletion F | A.ψ v (t * z) = 1} := by
      ext z
      simp only [T, localBallAnnihilator, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [hsets]
    apply isClosed_biInter
    intro t _ht
    exact isClosed_eq (hregular.1.comp (continuous_const.mul continuous_id)) continuous_const
  have hTcompact : IsCompact T :=
    (isCompact_closedBall (0 : v.adicCompletion F) r).of_isClosed_subset hTclosed
      (houter.trans Metric.ball_subset_closedBall)
  have hproper : IsProperMap (fun x : v.adicCompletion F => x ^ 2 - 1) := by
    convert (Polynomial.X ^ 2 - Polynomial.C 1 : Polynomial (v.adicCompletion F)).isProperMap_eval
      (by rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num) using 1
    funext x
    simp
  have hPcompact : IsCompact P := hproper.isCompact_preimage hTcompact
  obtain ⟨b, hb⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-M))
  have hb0 : b ≠ 0 := by
    intro h
    apply WithZero.exp_ne_zero (a := -M)
    exact hb.symm.trans (by simp only [h, map_zero])
  have hbnorm : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  let U := (fun x : v.adicCompletion F => x ^ 2 - 1) ⁻¹' Metric.ball 0 ‖b‖
  have hUopen : IsOpen U :=
    Metric.isOpen_ball.preimage ((continuous_id.pow 2).sub continuous_const)
  have hUnonempty : U.Nonempty := by
    refine ⟨1, ?_⟩
    simpa only [U, Set.mem_preimage, one_pow, sub_self] using Metric.mem_ball_self hbnorm
  have hUP : U ⊆ P := by
    intro x hx
    apply hinner
    have hxnorm : ‖x ^ 2 - 1‖ < ‖b‖ := by
      simpa only [U, Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hx
    change Valued.v (x ^ 2 - 1) ≤ WithZero.exp (-M)
    rw [← hb]
    exact ((Valued.toNormedField.norm_lt_iff (L := v.adicCompletion F)
      (Γ₀ := WithZero (Multiplicative ℤ))).mp hxnorm).le
  have hPpos : 0 < μ P := (hUopen.measure_pos μ hUnonempty).trans_le (measure_mono hUP)
  obtain ⟨R, _hR, hPR⟩ := hPcompact.isBounded.subset_closedBall_lt 0 (0 : v.adicCompletion F)
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have hcnorm : 1 < ‖c‖ := by
    have hval : Valued.v (1 : v.adicCompletion F) < Valued.v c := by
      rw [map_one, hc, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by norm_num)
    simpa only [norm_one] using
      (Valued.toNormedField.norm_lt_iff (L := v.adicCompletion F)
        (Γ₀ := WithZero (Multiplicative ℤ))).mpr hval
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt R hcnorm
  have hPN : P ⊆ localBall v N₀ := by
    intro x hx
    have hxnorm : ‖x‖ ≤ ‖c ^ N₀‖ := by
      rw [norm_pow]
      exact (show ‖x‖ ≤ R by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hPR hx).trans hN₀.le
    have hxval := (Valued.toNormedField.norm_le_iff (L := v.adicCompletion F)
      (Γ₀ := WithZero (Multiplicative ℤ))).mp hxnorm
    change Valued.v x ≤ WithZero.exp (N₀ : ℤ)
    simpa only [map_pow, hc, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_one] using hxval
  refine ⟨M, N₀, P, rfl, hPcompact, hPpos, hPcompact.measure_lt_top, ?_, ?_⟩
  · intro N
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxball : (a : v.adicCompletion F) * x ^ 2 ∈ Metric.ball 1 r := by
      have h := houter hx.2
      simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using h
    have hmem : x ∈ (fun x : v.adicCompletion F => (a : v.adicCompletion F) * x ^ 2) ⁻¹'
        Metric.ball 1 r := hxball
    rw [hempty] at hmem
    exact Set.notMem_empty x hmem
  · intro N hN
    ext x
    constructor
    · exact fun hx => hx.2
    · intro hx
      refine ⟨?_, hx⟩
      exact (hPN hx).trans (WithZero.exp_le_exp.mpr (by exact_mod_cast hN))

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
