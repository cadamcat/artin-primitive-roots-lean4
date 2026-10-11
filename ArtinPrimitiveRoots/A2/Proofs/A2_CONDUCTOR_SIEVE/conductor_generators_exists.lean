import ArtinPrimitiveRoots.Proofs.a2_cond_lead_p.ConductorGeneratorBalance

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Balanced generators without a twelfth-root hypothesis: use S.pid and the
S-unit logarithmic lattice, with real-place weight one and complex-place weight two.
Uses only the existing SData; feeds conductor_additive_sieve_apply. -/
theorem conductor_generators_exists (S : A1.SData F CE condη) :
    Nonempty (ConductorGenerators S) := by
  exact conductor_generators_exists_helper S

end ArtinPrimitiveRoots.A2
