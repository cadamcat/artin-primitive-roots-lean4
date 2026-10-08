import ArtinPrimitiveRoots.Theta.Shared
import Mathlib.LinearAlgebra.Countable

set_option autoImplicit false
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open ArtinPrimitiveRoots.A1
open scoped Topology

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

variable {F : Type} [Field F] [NumberField F]

/-- Finite completions of a number field are second countable. -/
instance adicCompletion_secondCountable (v : FinPlace F) :
    SecondCountableTopology (v.adicCompletion F) := by
  have : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (WithZero (Multiplicative ℤ)) := by
    change Countable (Option ℤ)
    infer_instance
  let q : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  have : Countable (MonoidWithZeroHom.ValueGroup₀ (.ofClass q)) :=
    (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (f := .ofClass q)).injective.countable
  have : Countable (MonoidWithZeroHom.ValueGroup₀ (.ofClass q))ˣ :=
    Units.val_injective.countable
  have : Filter.IsCountablyGenerated (uniformity (v.adicCompletion F)) :=
    (Valued.hasBasis_uniformity (v.adicCompletion F) (WithZero (Multiplicative ℤ))).isCountablyGenerated
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    DenseRange.separableSpace' (algebraMap F (v.adicCompletion F))
      (HeightOneSpectrum.denseRange_algebraMap F v)
  exact UniformSpace.secondCountable_of_separable _

/-- The normalized local Haar measure is sigma-finite. -/
theorem locHaar_sigmaFinite (v : FinPlace F) (μ : ArtinPrimitiveRoots.A1.Theta.LocHaar v) :
    SigmaFinite μ.μ := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  haveI : IsLocallyFiniteMeasure μ.μ := ⟨fun x => by
    refine ⟨(fun y : v.adicCompletion F => -x + y) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)), ?_, ?_⟩
    · apply (hO.preimage (continuous_const.add continuous_id)).mem_nhds
      change -x + x ∈ v.adicCompletionIntegers F
      simpa only [neg_add_cancel] using (v.adicCompletionIntegers F).zero_mem
    · rw [measure_preimage_add, μ.norm_O]
      exact ENNReal.one_lt_top⟩
  infer_instance

end ArtinPrimitiveRoots.Proofs.thsol_smooth
