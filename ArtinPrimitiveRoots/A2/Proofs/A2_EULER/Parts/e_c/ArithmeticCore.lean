import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.FrequencyFactors
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.ExtraCharacters
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.GeneratorCharacters

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











local macro "reflection% " n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `ArtinPrimitiveRoots.A2.Reflection.Missing
    (`ArtinPrimitiveRoots.A2 ++ n.getId)))
include R





theorem tuple_finite_on (B : PrimeTupleBridge S) (u : U.U) (p : IdealTuple S) :
    finiteFactor R p.2.2.1 (Aideal R p.1 p.2.1) (Agen R p.1 p.2.1)
      ((U.repr u : F) * (bc.gen p.2.2.2 : F) ^ 6) =
      ∏ v ∈ (B.equiv p).support,
        (chi D v.1 ((U.repr u : F) / (primeGen R v.1 : F) ^ frequencyValuation η U u v.1) ^
            (((B.equiv p v).2.2.1 : ℤ) - (((B.equiv p v).1 : ℕ) : ℤ) -
              3 * ((B.equiv p v).2.1 : ℤ)) *
          chi D v.1 ((bc.gen p.2.2.1 : F) / (primeGen R v.1 : F) ^ (B.equiv p v).2.2.1) ^
            (((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1) *
          chi D v.1 ((Agen R p.1 p.2.1 : F) /
            (primeGen R v.1 : F) ^ (((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1)) ^
            ((((B.equiv p v).1 : ℕ) : ℤ) + 3 * ((B.equiv p v).2.1 : ℤ) -
              ((B.equiv p v).2.2.1 : ℤ))) *
          localC R v.1 v.2 (((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1)
            (B.equiv p v).2.2.1 (frequencyValuation η U u v.1 + 6 * (B.equiv p v).2.2.2) := by
  classical
  let V := (B.equiv p).support
  let a : S.R := R.exterior.genR (R.exterior.ofSqf p.1) * R.exterior.genR p.2.1 ^ 3
  let h : S.R := U.repr u * R.exterior.genR p.2.2.2 ^ 6
  have haeq : (a : F) = (Agen R p.1 p.2.1 : F) := by
    dsimp [a, Agen]
    simp only [R.exterior.genR_val, Units.val_mul, Units.val_pow_eq_pow_val]
  have hheq : (h : F) = (U.repr u : F) * (bc.gen p.2.2.2 : F) ^ 6 := by
    dsimp [h]
    simp only [R.exterior.genR_val]
  have ha : S.IsGen (a : F) (Aideal R p.1 p.2.1).1 := by
    rw [haeq]
    exact (tuple_Agen_spec R _ _).1
  have hunit : Units.mk0 (a : F) ha.2.1 = Agen R p.1 p.2.1 := Units.ext haeq
  have hsupp := tuple_support_contains R B p
  have haV : ∀ v : ExteriorPrime S, idealExp v.1 (Aideal R p.1 p.2.1).1 ≠ 0 → v ∈ V := by
    intro v hn
    by_contra hv
    have hi : B.equiv p v = 0 := Finsupp.notMem_support_iff.mp hv
    rw [tuple_Aideal_exponent R B p v] at hn
    simp [hi] at hn
  have hnorm := finiteFactor_localC R p.2.2.1 (Aideal R p.1 p.2.1) a h ha V
    hsupp.2.2.1 haV
    (fun v => frequencyValuation η U u v.1 + 6 * idealExp v.1 p.2.2.2.1)
    (fun v hv => frequency_r_valuation_pow R η U u p.2.2.2 v)
  rw [hunit, hheq] at hnorm
  rw [hnorm]
  apply Finset.prod_congr rfl
  intro v hv
  rw [haeq, R.exterior.genR_val, frequency_r_complement_character R η U u p.2.2.2 v,
    tuple_Aideal_exponent R B p v, (tuple_exponents R B p v).2.2.1,
    (tuple_exponents R B p v).2.2.2]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, sub_add_eq_sub_sub]

theorem tuple_arithmetic_core (B : PrimeTupleBridge S) (u : U.U) (p : IdealTuple S) :
    gamma D S A 2 p.1.1 (cgen R p.1) *
        finiteFactor R p.2.2.1 (Aideal R p.1 p.2.1) (Agen R p.1 p.2.1)
          ((U.repr u : F) * (bc.gen p.2.2.2 : F) ^ 6) =
      ∏ v ∈ (B.equiv p).support,
        gamma D S A 2 v.1.asIdeal (primeGen R v.1 : F) ^ ((B.equiv p v).1 : ℕ) *
          chi D v.1 ((U.repr u : F) / (primeGen R v.1 : F) ^ frequencyValuation η U u v.1) ^
            (((B.equiv p v).2.2.1 : ℤ) - (((B.equiv p v).1 : ℕ) : ℤ) -
              3 * ((B.equiv p v).2.1 : ℤ)) *
          localC R v.1 v.2 (((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1)
            (B.equiv p v).2.2.1 (frequencyValuation η U u v.1 + 6 * (B.equiv p v).2.2.2) := by
  classical
  rw [tuple_gamma_on R B p, tuple_finite_on R η U B u p]
  let V := (B.equiv p).support
  let extra (v : ExteriorPrime S) : ℂ :=
    chi D v.1 ((cgen R p.1) / (primeGen R v.1 : F) ^ ((B.equiv p v).1 : ℕ)) ^
        (2 * (((B.equiv p v).1 : ℕ) : ℤ)) *
      chi D v.1 ((bc.gen p.2.2.1 : F) / (primeGen R v.1 : F) ^ (B.equiv p v).2.2.1) ^
        (((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1) *
      chi D v.1 ((Agen R p.1 p.2.1 : F) /
        (primeGen R v.1 : F) ^ (((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1)) ^
        ((((B.equiv p v).1 : ℕ) : ℤ) + 3 * ((B.equiv p v).2.1 : ℤ) -
          ((B.equiv p v).2.2.1 : ℤ))
  have hExtra : (∏ v ∈ V, extra v) = 1 := tuple_extra_product R B p
  calc
    _ = (∏ v ∈ V,
        gamma D S A 2 v.1.asIdeal (primeGen R v.1 : F) ^ ((B.equiv p v).1 : ℕ) *
          chi D v.1 ((U.repr u : F) / (primeGen R v.1 : F) ^ frequencyValuation η U u v.1) ^
            (((B.equiv p v).2.2.1 : ℤ) - (((B.equiv p v).1 : ℕ) : ℤ) -
              3 * ((B.equiv p v).2.1 : ℤ)) *
          localC R v.1 v.2 (((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1)
            (B.equiv p v).2.2.1 (frequencyValuation η U u v.1 + 6 * (B.equiv p v).2.2.2)) *
        ∏ v ∈ V, extra v := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hv
      dsimp [extra]
      ring
    _ = _ := by rw [hExtra, mul_one]

end ArtinPrimitiveRoots.Proofs.e_c
