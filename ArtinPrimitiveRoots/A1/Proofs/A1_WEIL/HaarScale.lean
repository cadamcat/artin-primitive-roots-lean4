import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Data
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute
import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableHaarScale (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelHaarScale (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The Jacobian of multiplication is the normalized local absolute value.
Guide: PROOFS.md:466–470. Uses: local_absolute_value; Haar uniqueness; residue cardinality. -/
theorem local_haar_scale (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (b : (v.adicCompletion F)ˣ) :
    Measure.map (fun x => (b : v.adicCompletion F) * x) μ =
      (ENNReal.ofReal (absFin v (b : v.adicCompletion F)))⁻¹ • μ := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
