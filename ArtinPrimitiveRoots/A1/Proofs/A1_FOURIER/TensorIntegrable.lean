import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Defs
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# A1-FOURIER part `a1_fourier_tensor_integrable` (IMPL)

Continuity and integrability of tensor sums for every Haar measure on `F_S`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A tensor sum is continuous and integrable for every additive Haar measure on `F_S`.

Proof hint: by Haar uniqueness (`MeasureTheory.Measure.isAddHaarMeasure_eq_smul`; `F_S` is
locally compact, second countable) reduce to the product measure
`(Measure.pi μ_v).prod (Measure.pi volume)` (product of Haar measures is Haar; compare the proof
of `a2_probe_sol.schwartz_tensor_fourier` and `covol_sFS_prod_eq_borel` in `A1/SLattice.lean`
for the Borel = product σ-algebra bridge). Each tensor is a product of an integrable function of
`x.1` (continuous, compact support) and of `x.2` (`SchwartzMap.integrable`); use
`Integrable.mul_prod` and `integrable_finset_sum`.
Used by: the glue of `SData.poisson` (`A1/SLattice.lean`). -/
theorem a1_fourier_tensor_integrable (S : SData F CE condη)
    {mS : MeasurableSpace S.FS} [BorelSpace S.FS]
    (g : S.FS → ℂ) (hg : S.IsFSTensorSum g)
    (μ : Measure S.FS) [μ.IsAddHaarMeasure] :
    Continuous g ∧ Integrable g μ := by
  sorry

end ArtinPrimitiveRoots.A1
