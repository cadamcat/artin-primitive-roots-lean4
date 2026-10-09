import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Data
import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableLocalHaar (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelLocalHaar (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- Choose a nonzero additive Haar measure on a finite completion.
Guide: PROOFS.md:464–466. Uses: built CFT Idele.LocallyCompact; Mathlib Haar existence. -/
theorem local_haar_exists (v : FinPlace F) : ∃ μ : Measure (v.adicCompletion F), Measure.IsAddHaarMeasure μ := by
  have : LocallyCompactSpace (v.adicCompletion F) := inferInstance
  exact ⟨Measure.addHaar, inferInstance⟩

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
