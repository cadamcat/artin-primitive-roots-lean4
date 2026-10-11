import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianOne
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_e.GaussianUnitHelpers

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance unitMeasurableSpace (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance unitBorelSpace (v : FinPlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- Local units have trivial index at odd unramified-character exterior places.
Uses: A.unramified; S.over6; S.different_mem; actual shell cancellation. -/
theorem exterior_local_index_unit (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F) (hv : v ∉ S.Sf) (a : Fˣ)
    (ha : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = 0) :
    W.index v (toLoc v a) = 1 := by
  let μ := W.measure v
  let u : (v.adicCompletion F)ˣ := toLoc v a
  let O := v.adicCompletionIntegers F
  letI : Measure.IsAddHaarMeasure μ := W.isHaar v
  have hu : Valued.v (u : v.adicCompletion F) = 1 :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_e.exterior_global_unit_valuation v a ha
  have hone := ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_e.unit_quadraticIntegral_eq_integer_mass
    S A v μ 1 hv (by simp) (W.cutoff v 1)
  have hmassComplex : (μ.real O : ℂ) ≠ 0 := by
    have hden := W.integral_ne_zero v (1 : (v.adicCompletion F)ˣ)
    rw [hone] at hden
    exact hden
  have hunit := ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_e.unit_quadraticIntegral_eq_integer_mass
    S A v μ u hv hu (W.cutoff v u)
  apply Units.ext
  change (((absFin v (u : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      quadraticIntegral A v μ u (W.cutoff v u) /
        quadraticIntegral A v μ 1 (W.cutoff v 1)) = 1
  rw [ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_e.absFin_eq_one_of_valued_eq_one v hu,
    hunit, hone]
  norm_num [hmassComplex]
  exact_mod_cast hmassComplex

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
