import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GLOBAL-DATUM».TameGeometry

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- Orthogonality to local units forces the uniformizer exponent to be divisible by three. -/
theorem tameLocal_lagrangian (T : TorusRep D H v) (B : TameTorusBasis T)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (Q : TameLocalGeometry v) :
    ∀ x : (v.adicCompletion F)ˣ,
      x ∈ Q.Alag ↔ ∀ y ∈ Q.Alag, torusPairing D H v x y = 1 := by
  sorry

/-- The coordinate at zero is fixed by the tame Lagrangian and has the required normalization. -/
theorem tameLocal_evaluation (T : TorusRep D H v) (B : TameTorusBasis T)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (Q : TameLocalGeometry v) :
    ∃ lam : T.V →ₗ[ℂ] ℂ, lam ≠ 0 ∧
      (∀ y ∈ Q.Alag, ∀ x, lam (T.σa y x) = lam x) ∧
      ∀ k : ZMod 3, lam (B.e k) = if k = 0 then 1 else 0 := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
