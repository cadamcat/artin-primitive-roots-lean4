import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalHaar
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianStabilization
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianNonzero

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableGaussianExists (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelGaussianExists (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- Assemble measures, actual stabilization cutoffs, and nonzero normalized ratios.
Guide: PROOFS.md:464–469. Uses: local_haar_exists; local_character_regular; quadratic_integral_stabilizes; stable_quadratic_integral_ne_zero; local_absolute_value. -/
theorem local_gaussian_data (D : FieldData F) (A : AddCharData F) :
    Nonempty (LocalGaussianData A) := by
  classical
  let μ : (v : FinPlace F) → Measure (v.adicCompletion F) :=
    fun v => Classical.choose (local_haar_exists v)
  have hμ (v : FinPlace F) : Measure.IsAddHaarMeasure (μ v) :=
    Classical.choose_spec (local_haar_exists v)
  have hψ (v : FinPlace F) : LocalCharacterRegular A v :=
    local_character_regular D A v
  let N : (v : FinPlace F) → (a : (v.adicCompletion F)ˣ) → ℕ := fun v a =>
    Classical.choose (quadratic_integral_stabilizes A v (μ v) (hμ v) (hψ v) a)
  have hN (v : FinPlace F) (a : (v.adicCompletion F)ˣ) :
      StabilizesAt A v (μ v) a (N v a) :=
    Classical.choose_spec (quadratic_integral_stabilizes A v (μ v) (hμ v) (hψ v) a)
  refine ⟨{
    measure := μ
    isHaar := hμ
    cutoff := N
    stable := ?_
    integral_ne_zero := ?_
    normalized_ne_zero := ?_ }⟩
  · intro v a M hM
    exact hN v a M hM
  · intro v a
    exact stable_quadratic_integral_ne_zero A v (μ v) (hμ v) (hψ v) a (N v a) (hN v a)
  · intro v a
    have hIa : quadraticIntegral A v (μ v) a (N v a) ≠ 0 :=
      stable_quadratic_integral_ne_zero A v (μ v) (hμ v) (hψ v) a (N v a) (hN v a)
    have hI1 : quadraticIntegral A v (μ v) 1 (N v 1) ≠ 0 :=
      stable_quadratic_integral_ne_zero A v (μ v) (hμ v) (hψ v) 1 (N v 1) (hN v 1)
    have hpos : 0 < absFin v (a : v.adicCompletion F) :=
      (local_absolute_value v).2.1 a
    have hcoef : absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) ≠ 0 := by
      exact ne_of_gt (by positivity)
    have hcoefC :
        ((absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hcoef
    have hnum :
        ((absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          quadraticIntegral A v (μ v) a (N v a) ≠ 0 :=
      mul_ne_zero hcoefC hIa
    exact div_ne_zero hnum hI1

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
