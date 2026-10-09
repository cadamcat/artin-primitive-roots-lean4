import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

theorem gamma_squarefree_norm_le_one (c : S.SqfExtIdeal) :
    ‖gamma D S A 2 c.1 (cgen R c)‖ ≤ 1 := by
  obtain ⟨a, ha, hgen, hallowed⟩ := cgen_valid R c
  rw [← ha]
  exact ArtinPrimitiveRoots.Proofs.a2_rffwd_sol.gamma_sqf_norm_le_one
    D S H Bd A c.1 c.2.1 c.2.2 a ⟨hgen, hallowed⟩

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
