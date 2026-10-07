import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Local genuine/equivariant/right-invariant/table properties, including zero extension.
Uses the frozen `jacquet_equiv`, `jacquet_spherical_table`, and cover image laws;
feeds frozen `WvAll_spec` and `thetaWhit_factor_iteration`. -/
theorem WvAll_properties (P : CoverPackage D S H A) (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v) :
    (∀ v, v ∉ S.Sf → ∀ ζ g, WvAll P G μ v (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * WvAll P G μ v g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g, WvAll P G μ v (P.tc.n v (Multiplicative.ofAdd x) * g) =
      A.ψ v x * WvAll P G μ v g) ∧
    (∀ v, v ∉ S.Sf → ∀ g, ∀ k ∈ P.tc.Kext, k ∈ P.tc.Gloc v → WvAll P G μ v (g * k) = WvAll P G μ v g) ∧
    (∀ v, v ∉ S.Sf → ∀ (e : ℤ) (u : (v.adicCompletion F)ˣ),
      (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      WvAll P G μ v (P.tc.a v ((toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e * u)) =
        sphericalTable D A v e u) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
