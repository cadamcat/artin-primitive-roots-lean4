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

theorem bad_support (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (ξ w z : ℂ)
    (hfreq : frequencyValuation η U u v ≠ 0)
    (hC0 : ∀ k J, localC R v hv 0 k J = if k = 0 then 1 else if J = 0 then 1 else 0)
    (hC1 : ∀ J, 0 < J → localC R v hv 1 0 J = 0) :
    localEulerTerm R η U u v hv ξ w z (0, 0, 0, 0) = 1 ∧
    (∀ k m, k ≠ 0 → localEulerTerm R η U u v hv ξ w z (0, 0, k, m) = 0) ∧
    localEulerTerm R η U u v hv ξ w z (1, 0, 0, 0) = 0 := by
  have hj : 0 < frequencyValuation η U u v := Nat.pos_of_ne_zero hfreq
  refine ⟨?_, ?_⟩
  · have hC : localC R v hv 0 0 (frequencyValuation η U u v) = 1 := by
      simpa using hC0 0 (frequencyValuation η U u v)
    simp [localEulerTerm, hC]
  · refine ⟨?_, ?_⟩
    · intro k m hk
      have hJ : frequencyValuation η U u v + 6 * m ≠ 0 := by omega
      have hC : localC R v hv 0 k (frequencyValuation η U u v + 6 * m) = 0 := by
        rw [hC0]
        simp only [if_neg hk, if_neg hJ]
      simp [localEulerTerm, hC]
    · have hC : localC R v hv 1 0 (frequencyValuation η U u v) = 0 :=
        hC1 _ hj
      simp [localEulerTerm, hC]

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
