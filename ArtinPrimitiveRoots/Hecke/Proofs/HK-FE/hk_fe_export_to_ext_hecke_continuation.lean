import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_entire_L_preliminary_growth


set_option autoImplicit false
open NumberField ClassFieldTheory
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Shared primitive ray-character producer for HK-H3 and A2-FE-GLUE. Its completion is
entire, its root number is unimodular, and the Gamma product is asserted only off poles.
Guide: sol-thin-hk2/PROOFS.md:1512–1592; sol-thin-a2zf/PROOFS.md:451–513.
Uses residue/trace producers, hk_root_number_norm, hk_mellin_FE_completed,
hk_completed_gamma_product and hk_entire_L_agreement. A2 supplies the idelic dictionary;
HK-H3 supplies polynomial growth from the preliminary exponential strip bounds. -/
theorem hk_fe_export_to_ext_hecke_continuation [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) (hp : HKPrimitive ψ) :
    Differentiable ℂ (hkEntireL ψ) ∧ Differentiable ℂ (hkEntireL (ψ⁻¹)) ∧
    (∀ s : ℂ, 1 < s.re → hkEntireL ψ s = LSeriesRay ψ s) ∧
    (∀ s : ℂ, 1 < s.re → hkEntireL (ψ⁻¹) s = LSeriesRay (ψ⁻¹) s) ∧
    Differentiable ℂ (hkCompleted ψ) ∧ Differentiable ℂ (hkCompleted (ψ⁻¹)) ∧
    (∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) →
      hkCompleted ψ s = hkCompletedValue (hkEntireL ψ) m s) ∧
    (∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) →
      hkCompleted (ψ⁻¹) s = hkCompletedValue (hkEntireL (ψ⁻¹)) m s) ∧
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ s : ℂ,
      hkCompleted ψ s = W * hkCompleted (ψ⁻¹) (1 - s) := by
  sorry

end ArtinPrimitiveRoots.Hecke
