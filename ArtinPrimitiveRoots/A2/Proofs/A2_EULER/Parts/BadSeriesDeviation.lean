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

theorem bad_series_deviation (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (p : Triple)
    (hp : eulerNeighborhood p) (hQ : (2 : ℝ) ^ (2000 : ℕ) < qI v.asIdeal)
    (hs : Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
      ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖))
    (hVtail : ∀ m, localEulerTerm R η U u v hv (p 0) (p 1) (p 2) (0, 0, 0, m) =
      localV v (p 2) ^ m)
    (hsharp : ∀ i : Fin 2 × ℕ × ℕ × ℕ, 0 < i.1.1 + 3 * i.2.1 → i.2.2.1 ≤ 1 →
      ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖ ≤
        qI v.asIdeal ^ ((i.1.1 : ℝ) * (1 / 2 - (p 0).re) +
          (i.2.1 : ℝ) * (2 - 3 * (p 0).re) +
          (i.2.2.1 : ℝ) * (1 / 2 - (p 1).re) - 6 * (i.2.2.2 : ℝ) * (p 2).re))
    (hbase : localEulerTerm R η U u v hv (p 0) (p 1) (p 2) (0, 0, 0, 0) = 1)
    (ht0 : ∀ k m, k ≠ 0 → localEulerTerm R η U u v hv (p 0) (p 1) (p 2) (0, 0, k, m) = 0)
    (ht1 : localEulerTerm R η U u v hv (p 0) (p 1) (p 2) (1, 0, 0, 0) = 0)
    (hk2 : ∀ i : Fin 2 × ℕ × ℕ × ℕ, 0 < i.1.1 + 3 * i.2.1 → 2 ≤ i.2.2.1 →
      localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i = 0) :
    ‖localEuler R η U u v hv (p 0) (p 1) (p 2) - 1‖ ≤
      16 * qI v.asIdeal ^ (-1 / 4000 : ℝ) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
