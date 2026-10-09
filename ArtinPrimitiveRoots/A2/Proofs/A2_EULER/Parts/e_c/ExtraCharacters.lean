import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.GammaOnSupport
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.CrossCancellation

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





theorem tuple_Agen_spec (c : S.SqfExtIdeal) (n : S.ExtIdeal) :
    S.IsGen (Agen R c n : F) (Aideal R c n).1 ∧ Bd.Allowed (Agen R c n) :=
  ArtinPrimitiveRoots.Proofs.a2_rffwd_sol.exterior_cube_generator D S H Bd bc R.exterior c n

theorem tuple_extra_product (B : PrimeTupleBridge S) (p : IdealTuple S) :
    (∏ v ∈ (B.equiv p).support,
      chi D v.1 ((cgen R p.1) / (primeGen R v.1 : F) ^ ((B.equiv p v).1 : ℕ)) ^
          (2 * (((B.equiv p v).1 : ℕ) : ℤ)) *
        chi D v.1 ((bc.gen p.2.2.1 : F) / (primeGen R v.1 : F) ^ (B.equiv p v).2.2.1) ^
          (((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1) *
        chi D v.1 ((Agen R p.1 p.2.1 : F) /
          (primeGen R v.1 : F) ^ (((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1)) ^
          ((((B.equiv p v).1 : ℕ) : ℤ) + 3 * ((B.equiv p v).2.1 : ℤ) -
            ((B.equiv p v).2.2.1 : ℤ))) = 1 := by
  classical
  let V := (B.equiv p).support
  let e (v : ExteriorPrime S) : ℤ := ((B.equiv p v).1 : ℕ)
  let l (v : ExteriorPrime S) : ℤ := (B.equiv p v).2.1
  let k (v : ExteriorPrime S) : ℤ := (B.equiv p v).2.2.1
  have hsupp := tuple_support_contains R B p
  have haV : ∀ v : ExteriorPrime S, idealExp v.1 (Aideal R p.1 p.2.1).1 ≠ 0 → v ∈ V := by
    intro v hn
    by_contra hv
    have hz := tuple_exponents_zero R B p v hv
    rw [tuple_Aideal_exponent R B p v] at hn
    have hc : ((B.equiv p v).1 : ℕ) = 0 := by
      rw [← (tuple_exponents R B p v).1]
      exact hz.1
    have hl : (B.equiv p v).2.1 = 0 := by
      rw [← (tuple_exponents R B p v).2.1]
      exact hz.2.1
    simp only [hc, hl, mul_zero, add_zero, ne_eq, not_true_eq_false] at hn
  have hcross := symmetric_cross_product V (fun v w => chi D v.1 (primeGen R w.1 : F)) e l k
    (fun v hv w hw hne => prime_chi_symm R v w hne)
    (fun v hv w hw hne => prime_chi_six R v w hne)
  apply Eq.trans _ hcross
  apply Finset.prod_congr rfl
  intro v hv
  have hc := allowed_generator_complement_character R (R.exterior.ofSqf p.1)
    (bc.gen (R.exterior.ofSqf p.1)) (bc.gen_spec _) V hsupp.1 v hv
  have hs := allowed_generator_complement_character R p.2.2.1
    (bc.gen p.2.2.1) (bc.gen_spec _) V hsupp.2.2.1 v hv
  have ha := allowed_generator_complement_character R (Aideal R p.1 p.2.1)
    (Agen R p.1 p.2.1) (tuple_Agen_spec R _ _) V haV v hv
  simp only [R.exterior.ofSqf_val, (tuple_exponents R B p v).1] at hc
  rw [(tuple_exponents R B p v).2.2.1] at hs
  rw [tuple_Aideal_exponent R B p v] at ha
  have hce (w : ExteriorPrime S) : idealExp w.1 p.1.1 = ((B.equiv p w).1 : ℕ) :=
    (tuple_exponents R B p w).1
  simp only [hce] at hc
  have hse (w : ExteriorPrime S) : idealExp w.1 p.2.2.1.1 = (B.equiv p w).2.2.1 :=
    (tuple_exponents R B p w).2.2.1
  simp only [hse] at hs
  simp only [tuple_Aideal_exponent R B p] at ha
  change chi D v.1 ((bc.gen (R.exterior.ofSqf p.1) : F) /
      (primeGen R v.1 : F) ^ ((B.equiv p v).1 : ℕ)) ^ _ * _ * _ = _
  rw [hc, hs, ha]
  simp only [← zpow_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ← Finset.prod_zpow]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro w hw
  have hn : v ≠ w := (Finset.mem_erase.mp hw).1.symm
  have hz0 : chi D v.1 (primeGen R w.1 : F) ≠ 0 :=
    chi_unit_ne_zero R v _ (primeGen_other_valuation R w v hn.symm)
  rw [← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hz0, ← zpow_add₀ hz0]
  congr 1
  dsimp [e,l,k]
  ring

end ArtinPrimitiveRoots.Proofs.e_c
