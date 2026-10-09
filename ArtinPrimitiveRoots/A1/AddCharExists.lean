import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».TateCharacter
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».CompletionTrace
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».TraceIntegral
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».RationalCharacter
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».TraceCharacters
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».NativeTraceCharacters
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».FiniteTraceCharacters
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».RationalProduct
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».IntegralGlobalCharacters
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».UnramifiedCharacters

/-!
# Existence of the standard additive character data

The construction uses the local trace characters, with the complex convention fixed in
`AddCharData.psiC`. The global compatibility is Tate's triviality on the diagonal copy of `F`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- The standard additive character data exists for a number field. -/
theorem AddCharData.nonempty (D : FieldData F) : Nonempty (AddCharData F) := by
  obtain ⟨ψ, hglobal, hint⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_bdata_sol.integralGlobalChar_family F
  exact ⟨{
    ψ := ψ
    trivial_on_F := hglobal
    integral := hint
    unramified := ArtinPrimitiveRoots.Proofs.a1_bdata_sol.integralGlobalChar_unramified
      ψ hglobal hint
  }⟩

end ArtinPrimitiveRoots.A1
