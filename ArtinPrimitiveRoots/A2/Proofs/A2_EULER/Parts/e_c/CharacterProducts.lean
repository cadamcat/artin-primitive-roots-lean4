import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.LocalPhases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain MeasureTheory Function
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.e_c
open ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)





local macro "addchar% " n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `ArtinPrimitiveRoots.A1.AddChar
    (`ArtinPrimitiveRoots.A1 ++ n.getId)))
include R

theorem chiIdealPow_prime (v : FinPlace F) (x : F) (j : ℤ) :
    chiIdealPow D v.asIdeal x j = chiPow D v x j := by
  have hp : Prime v.asIdeal := (Ideal.prime_iff_isPrime v.ne_bot).2 v.isPrime
  have hn : normalize v.asIdeal = v.asIdeal :=
    associated_iff_eq.mp (normalize_associated v.asIdeal)
  rw [chiIdealPow, UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible, hn]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  have hcond : v.asIdeal.IsPrime ∧ v.asIdeal ≠ ⊥ := ⟨v.isPrime, v.ne_bot⟩
  rw [dif_pos hcond]

theorem chiIdealPow_prime_power (v : FinPlace F) (x : F) (j : ℤ) (k : ℕ) :
    chiIdealPow D (v.asIdeal ^ k) x j = chiPow D v x j ^ k := by
  induction k with
  | zero => simp [chiIdealPow, ← Ideal.one_eq_top]
  | succ k ih =>
    rw [pow_succ, (addchar% crt_chiIdealPow_mul_ideal) D
      (pow_ne_zero k v.ne_bot) v.ne_bot x j, ih, chiIdealPow_prime R, pow_succ]

theorem chiIdealPow_product (I : S.ExtIdeal) (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) (x : F) (j : ℤ) :
    chiIdealPow D I.1 x j = ∏ v ∈ V, chiPow D v.1 x j ^ idealExp v.1 I.1 := by
  classical
  let P (v : ExteriorPrime S) := v.1.asIdeal ^ idealExp v.1 I.1
  have hP (v : ExteriorPrime S) : P v ≠ ⊥ := pow_ne_zero _ v.1.ne_bot
  have hprod : ∀ T : Finset (ExteriorPrime S), (∏ v ∈ T, P v) ≠ ⊥ := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert v T hv ih =>
      rw [Finset.prod_insert hv]
      exact mul_ne_zero (hP v) ih
  have hmul : ∀ T : Finset (ExteriorPrime S),
      chiIdealPow D (∏ v ∈ T, P v) x j = ∏ v ∈ T, chiIdealPow D (P v) x j := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [chiIdealPow, ← Ideal.one_eq_top]
    | @insert v T hv ih =>
      rw [Finset.prod_insert hv, (addchar% crt_chiIdealPow_mul_ideal) D
        (hP v) (hprod T) x j, ih, Finset.prod_insert hv]
  calc
    _ = chiIdealPow D (∏ v ∈ V, P v) x j :=
      congrArg (fun J => chiIdealPow D J x j) (ideal_factorization_on R I V hV)
    _ = ∏ v ∈ V, chiIdealPow D (P v) x j := hmul V
    _ = _ := Finset.prod_congr rfl (fun v hv => chiIdealPow_prime_power R v.1 x j _)

theorem chiPow_one_pow (v : FinPlace F) (x : F) (k : ℕ) :
    chiPow D v x 1 ^ k = if k = 0 then 1 else chiPow D v x (k : ℤ) := by
  by_cases hk : k = 0
  · simp [hk]
  by_cases hr : residue v x = 0
  · simp [chiPow, hr, hk]
  · simp [chiPow, hr, hk]

end ArtinPrimitiveRoots.Proofs.e_c
