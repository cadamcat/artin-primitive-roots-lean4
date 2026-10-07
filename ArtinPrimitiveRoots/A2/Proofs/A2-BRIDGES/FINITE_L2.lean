import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Finite Euclidean triangle inequality; it applies before squaring the norm.
Guide: sol-thin-a2rp/PROOFS.md:67–68. Uses PiLp norm_sum_le. -/
theorem a2_bridge_FINITE_L2 {α β : Type*} (T : Finset α) (U : Finset β)
    (f : β → α → ℂ) :
    bridgeL2 T (fun i => ∑ j ∈ U, f j i) ≤ ∑ j ∈ U, bridgeL2 T (f j) := by
  sorry

/-- Finite-coordinate Bochner Minkowski bound, with actual integrability hypotheses.
Guide: sol-thin-a2rp/PROOFS.md:67–68. Uses norm_integral_le_integral_norm in PiLp. -/
theorem a2_bridge_FINITE_L2_integral {α Ω : Type*} [MeasurableSpace Ω]
    (T : Finset α) (ν : Measure Ω) (f : Ω → α → ℂ)
    (hf : ∀ i ∈ T, Integrable (fun x => f x i) ν) :
    Integrable (fun x => bridgeL2 T (f x)) ν ∧
    bridgeL2 T (fun i => ∫ x, f x i ∂ν) ≤ ∫ x, bridgeL2 T (f x) ∂ν := by
  sorry

/-- Infinite outer sum in a complete finite-dimensional target.
Guide: sol-thin-a2rp/PROOFS.md:67–68. Uses summable_norm_iff and norm_tsum_le. -/
theorem a2_bridge_FINITE_L2_tsum {α β : Type*} (T : Finset α) (f : β → α → ℂ)
    (hf : Summable (fun j => bridgeL2 T (f j))) :
    (∀ i ∈ T, Summable (fun j => f j i)) ∧
    bridgeL2 T (fun i => ∑' j, f j i) ≤ ∑' j, bridgeL2 T (f j) := by
  sorry

end ArtinPrimitiveRoots.A2
