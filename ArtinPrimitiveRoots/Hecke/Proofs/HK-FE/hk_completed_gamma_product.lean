import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs


set_option autoImplicit false
open NumberField ClassFieldTheory MeasureTheory
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Normalize H1's completed Mellin transform to the exact Deligne GammaC product, restricting
the product to regular Gamma arguments. Guide: sol-thin-hk2/PROOFS.md:1512–1545.
Uses heckeBeta, rayMellinNormalization and reciprocal Gamma cancellation. -/
theorem hk_completed_gamma_product [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    hkCompleted ψ s = hkCompletedValue (hkEntireL ψ) m s := by
  sorry

end ArtinPrimitiveRoots.Hecke
