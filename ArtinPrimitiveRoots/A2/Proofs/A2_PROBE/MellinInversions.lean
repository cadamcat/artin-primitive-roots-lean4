import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Contracts
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import ArtinPrimitiveRoots.A1.CoefficientsFacts

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory Complex
open ArtinPrimitiveRoots A1 A2
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)

/-- Supply the Gaussian and compact-weight inversions alongside the V₀ callback. -/
theorem mellin_inversions_of_v0 (W' : ProbeWeights (S := S))
    (hV0 : ∀ T : ℝ, 0 < T → leadV0 R sd W' T =
      leadVertical 2 (fun z => leadM R sd W' z * (T : ℂ) ^ (-z)))
    (hdecay : LeadWeightDecay R sd W') :
    LeadInversionsContract R sd W' := by
  have lineInversion (f : ℝ → ℂ) (σ : ℝ) (G : ℂ → ℂ)
      (hconv : IntegrableOn (fun t : ℝ => f t * (t : ℂ) ^ (σ : ℂ) / (t : ℂ)) (Set.Ioi 0))
      (hG : ∀ y : ℝ, ∫ t in Set.Ioi (0 : ℝ),
        f t * (t : ℂ) ^ ((σ : ℂ) + y * I) / (t : ℂ) = G (σ + y * I))
      (hvert : Integrable (fun y : ℝ => G (σ + y * I)))
      (T : ℝ) (hT : 0 < T) (hcont : ContinuousAt f T) :
      f T = (1 / (2 * Real.pi) : ℂ) *
        ∫ y : ℝ, G (σ + y * I) * (T : ℂ) ^ (-((σ : ℂ) + y * I)) := by
    have hpow (s : ℂ) (t : ℝ) (ht : 0 < t) :
        (t : ℂ) ^ (s - 1) • f t = f t * (t : ℂ) ^ s / (t : ℂ) := by
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
      rw [cpow_sub _ _ ht0, cpow_one, smul_eq_mul]
      ring
    have hconv' : MellinConvergent f (σ : ℂ) := by
      unfold MellinConvergent
      exact hconv.congr_fun (fun t ht => (hpow _ t ht).symm) measurableSet_Ioi
    have hmellin (y : ℝ) : mellin f (σ + y * I) = G (σ + y * I) := by
      rw [← hG y]
      unfold mellin
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hpow _ t ht
    have hvert' : VerticalIntegrable (mellin f) σ := by
      unfold VerticalIntegrable
      simp_rw [hmellin]
      exact hvert
    have hInv := mellinInv_mellin_eq σ f hT hconv' hvert' hcont
    symm
    calc
      _ = mellinInv σ (mellin f) T := by
        unfold mellinInv
        simp only [RCLike.real_smul_eq_coe_mul, smul_eq_mul]
        have hCoeff : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
          norm_cast
        rw [hCoeff]
        congr 1
        apply integral_congr_ae
        filter_upwards with y
        rw [hmellin]
        ring
      _ = f T := hInv
  have hPG (T : ℝ) (hT : 0 < T) : (PG T : ℂ) =
      leadVertical 5 (fun ξ => Complex.exp (ξ ^ 2) * (T : ℂ) ^ (-ξ)) := by
    have hsq (y : ℝ) : ((5 : ℂ) + y * I) ^ 2 =
        -1 * (y : ℂ) ^ 2 + (10 * I) * y + 25 := by
      linear_combination (y : ℂ) ^ 2 * I_sq
    have hvert : Integrable (fun y : ℝ => Complex.exp (((5 : ℂ) + y * I) ^ 2)) := by
      simp_rw [hsq]
      exact integrable_cexp_quadratic (b := 1) (by norm_num) _ _
    have hcont : ContinuousAt PG T := by
      unfold PG
      exact continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
        ((((Real.continuousAt_log hT.ne').pow 2).neg).div_const 4))
    exact lineInversion (fun t => (PG t : ℂ)) 5 (fun ξ => Complex.exp (ξ ^ 2))
      (PG_mellin _).1 (fun y => (PG_mellin _).2) hvert T hT
      (continuous_ofReal.continuousAt.comp hcont)
  have hWconv : IntegrableOn
      (fun t : ℝ => W'.W1 t * (t : ℂ) ^ (4 : ℂ) / (t : ℂ)) (Set.Ioi 0) := by
    have hf : Continuous W'.W1 := W'.W1_smooth.continuous
    have hcont : Continuous (fun t : ℝ => W'.W1 t * (t : ℂ) ^ (4 : ℂ) / (t : ℂ)) := by
      refine continuous_iff_continuousAt.mpr fun t => ?_
      by_cases ht : 0 < t
      · have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
        have hcp : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (4 : ℂ)) t :=
          (continuousAt_cpow_const (ofReal_mem_slitPlane.mpr ht)).comp
            continuous_ofReal.continuousAt
        exact (hf.continuousAt.mul hcp).div continuous_ofReal.continuousAt ht0
      · have hnot : t ∉ tsupport W'.W1 := fun h => ht (W'.W1_positive_support h)
        have hev := notMem_tsupport_iff_eventuallyEq.mp hnot
        refine (continuousAt_const (y := (0 : ℂ))).congr ?_
        filter_upwards [hev] with x hx
        simp [hx]
    have hsupp : HasCompactSupport
        (fun t : ℝ => W'.W1 t * (t : ℂ) ^ (4 : ℂ) / (t : ℂ)) := by
      refine W'.W1_compact.mono' fun t ht => subset_tsupport W'.W1 fun h0 => ht ?_
      simp [h0]
    exact (hcont.integrable_of_hasCompactSupport hsupp).integrableOn
  have hWvert : Integrable (fun y : ℝ => leadW1hat W' (4 + y * I)) := by
    obtain ⟨C, _, hBound⟩ := hdecay.2.2.2.1 4 4 2 (le_refl _) (by norm_num)
    have hmaj : Integrable (fun y : ℝ => C * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
      (integrable_one_add_norm (by norm_num)).const_mul C
    have hcont : Continuous (fun y : ℝ => leadW1hat W' (4 + y * I)) :=
      hdecay.2.1.continuous.comp (by fun_prop)
    refine hmaj.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    simpa using hBound 4 y (le_refl _) (le_refl _)
  have hW (T : ℝ) (hT : 0 < T) : W'.W1 T =
      leadVertical 4 (fun w => leadW1hat W' w * (T : ℂ) ^ (-w)) :=
    lineInversion W'.W1 4 (leadW1hat W') hWconv (fun y => rfl) hWvert T hT
      W'.W1_smooth.continuous.continuousAt
  exact ⟨hV0, hW, hPG⟩

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
