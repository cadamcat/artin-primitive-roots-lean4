import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseCorrectedFinite
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseInfiniteCharacter

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA LEAD: Construct the conductor-(3) finite local factors from primary unit normalization; use the inverse angular factor at infinity. Prove the principal product formula before idelic descent.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem base_local_data_exists (σ : E →+* ℂ)
    (φ : Ideal OE →*₀ ℂ)
    (hφ : ∀ I : Ideal OE,
      φ I = integerComplex σ (primary I) / ‖integerComplex σ (primary I)‖)
    (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, ((a z : ℂˣ) : ℂ) = (z : ℂ) / ‖(z : ℂ)‖) :
    Nonempty (BaseLocalData σ) := by
  obtain ⟨κ, hκunit, hκprincipal⟩ := base_local_correction_exists σ φ hφ a ha
  refine ⟨{
    finite := correctedFinite σ κ
    infinite := baseInfiniteCharacter σ a
    eventually_unit_trivial := correctedFinite_eventually_unit_trivial σ κ
    finite_unitary := correctedFinite_unitary σ κ hκunit
    infinite_unitary := baseInfiniteCharacter_unitary σ a ha
    principal_product := ?_
    exterior_units := ?_
    prime_formula := ?_
    angular := baseInfiniteCharacter_angular σ a ha }⟩
  · intro t
    rw [baseInfiniteCharacter_product σ a ha t,
      correctedFinite_principal σ a κ hκprincipal t]
    exact inv_mul_cancel _
  · intro v hv u hu
    rw [correctedFinite_exterior σ κ v hv]
    exact baseFiniteCharacter_localUnit σ v u hu
  · intro v hv
    rw [correctedFinite_exterior σ κ v hv]
    exact baseFiniteCharacter_prime_formula σ v hv

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
