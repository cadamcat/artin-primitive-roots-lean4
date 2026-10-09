import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.LocalSubstitution

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

theorem primeGen_spec (v : ExteriorPrime S) :
    S.IsGen (primeGen R v.1 : F) v.1.asIdeal ∧ Bd.Allowed (primeGen R v.1) := by
  simpa [primeGen, v.2, R.exterior.prime_val] using
    bc.gen_spec (R.exterior.prime v.1 v.2)

theorem weighted_prime_generators (V : Finset (ExteriorPrime S)) (n : ExteriorPrime S → ℕ) :
    ∃ I : S.ExtIdeal,
      I.1 = ∏ v ∈ V, v.1.asIdeal ^ n v ∧
      S.IsGen ((∏ v ∈ V, primeGen R v.1 ^ n v : Fˣ) : F) I.1 ∧
      Bd.Allowed (∏ v ∈ V, primeGen R v.1 ^ n v) := by
  classical
  induction V using Finset.induction_on with
  | empty =>
    refine ⟨R.exterior.one, ?_, ?_, ?_⟩
    · simpa only [Finset.prod_empty, Ideal.one_eq_top] using R.exterior.one_val
    · have hgen : S.IsGen (1 : F) (⊤ : Ideal (𝓞 F)) := by exact (reflection% rf_isGen_one)
      simpa only [Finset.prod_empty, Units.val_one, R.exterior.one_val] using hgen
    · have hallow : Bd.Allowed (1 : Fˣ) := by exact (reflection% rf_allowed_one)
      simpa only [Finset.prod_empty] using hallow
  | @insert v V hv ih =>
    obtain ⟨I, hI, hgenI, hallowI⟩ := ih
    let P := R.exterior.pow (R.exterior.prime v.1 v.2) (n v)
    have hprime : S.IsGen (primeGen R v.1 : F) (R.exterior.prime v.1 v.2).1 := by
      simpa only [R.exterior.prime_val] using (primeGen_spec R v).1
    have hgenP : S.IsGen ((primeGen R v.1 ^ n v : Fˣ) : F) P.1 :=
      (reflection% rf_isGen_extPow) R _ (primeGen R v.1) hprime (n v)
    refine ⟨R.exterior.mul P I, ?_, ?_, ?_⟩
    · rw [R.exterior.mul_val, R.exterior.pow_val, R.exterior.prime_val,
        Finset.prod_insert hv, hI]
    · have h := (reflection% rf_isGen_extMul) R P I (primeGen R v.1 ^ n v)
        (∏ w ∈ V, primeGen R w.1 ^ n w) hgenP hgenI
      simpa only [Finset.prod_insert hv, Units.val_mul] using h
    · change (QuotientGroup.mk (S.diagU (∏ w ∈ insert v V, primeGen R w.1 ^ n w)) : S.V) ∈ Bd.B
      rw [Finset.prod_insert hv, map_mul]
      change (QuotientGroup.mk (S.diagU (primeGen R v.1 ^ n v)) : S.V) *
        (QuotientGroup.mk (S.diagU (∏ w ∈ V, primeGen R w.1 ^ n w)) : S.V) ∈ Bd.B
      apply Bd.B.mul_mem
      · have h := Bd.B.pow_mem (primeGen_spec R v).2 (n v)
        simpa only [BData.Allowed, map_pow, QuotientGroup.mk_pow] using h
      · exact hallowI

theorem allowed_generator_sixth_relation (I : S.ExtIdeal) (a : Fˣ)
    (ha : S.IsGen (a : F) I.1 ∧ Bd.Allowed a) (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) :
    ∃ ε : S.US, a = (ε : Fˣ) ^ (6 : ℕ) *
      ∏ v ∈ V, primeGen R v.1 ^ idealExp v.1 I.1 := by
  classical
  obtain ⟨J, hJ, hgenJ, hallowJ⟩ := weighted_prime_generators R V (fun v => idealExp v.1 I.1)
  have hJI : J.1 = I.1 := hJ.trans (ideal_factorization_on R I V hV).symm
  have hgen : S.IsGen ((∏ v ∈ V, primeGen R v.1 ^ idealExp v.1 I.1 : Fˣ) : F) I.1 := by
    simpa only [hJI] using hgenJ
  obtain ⟨ε, hε, heq⟩ := Bd.allowed_unique I.1 a
    (∏ v ∈ V, primeGen R v.1 ^ idealExp v.1 I.1) ha ⟨hgen, hallowJ⟩
  exact ⟨⟨ε, hε⟩, heq⟩

theorem allowed_generator_complement_character (I : S.ExtIdeal) (a : Fˣ)
    (ha : S.IsGen (a : F) I.1 ∧ Bd.Allowed a) (V : Finset (ExteriorPrime S))
    (hV : ∀ w : ExteriorPrime S, idealExp w.1 I.1 ≠ 0 → w ∈ V)
    (v : ExteriorPrime S) (hv : v ∈ V) :
    chi D v.1 ((a : F) / (primeGen R v.1 : F) ^ idealExp v.1 I.1) =
      ∏ w ∈ V.erase v, chi D v.1 (primeGen R w.1 : F) ^ idealExp w.1 I.1 := by
  classical
  let n (w : ExteriorPrime S) := idealExp w.1 I.1
  let G : Fˣ := ∏ w ∈ V.erase v, primeGen R w.1 ^ n w
  have hunit (w : ExteriorPrime S) (hw : w ∈ V.erase v) :
      v.1.valuation F (primeGen R w.1 : F) = 1 :=
    primeGen_other_valuation R w v (Finset.mem_erase.mp hw).1
  have hprodUnit : ∀ T : Finset (ExteriorPrime S), T ⊆ V.erase v →
      v.1.valuation F ((∏ w ∈ T, primeGen R w.1 ^ n w : Fˣ) : F) = 1 := by
    intro T hT
    induction T using Finset.induction_on with
    | empty => simp
    | @insert w T hw ih =>
      have hTail : T ⊆ V.erase v := (Finset.subset_insert w T).trans hT
      rw [Finset.prod_insert hw, Units.val_mul, map_mul,
        Units.val_pow_eq_pow_val, map_pow, hunit w (hT (Finset.mem_insert_self w T)),
        one_pow, ih hTail, one_mul]
  have hχprod : ∀ T : Finset (ExteriorPrime S), T ⊆ V.erase v →
      chi D v.1 ((∏ w ∈ T, primeGen R w.1 ^ n w : Fˣ) : F) =
        ∏ w ∈ T, chi D v.1 (primeGen R w.1 : F) ^ n w := by
    intro T hT
    induction T using Finset.induction_on with
    | empty =>
      have hone : chi D v.1 (1 : F) = 1 := by
        simpa using (reflection% rf_chi_argument_zpow) v.1 v.2 (1 : Fˣ) (by simp) (0 : ℤ)
      simp only [Finset.prod_empty, Units.val_one, hone]
    | @insert w T hw ih =>
      have hTail : T ⊆ V.erase v := (Finset.subset_insert w T).trans hT
      have hwVal := hunit w (hT (Finset.mem_insert_self w T))
      have hwPowVal : v.1.valuation F ((primeGen R w.1 ^ n w : Fˣ) : F) = 1 := by
        rw [Units.val_pow_eq_pow_val, map_pow, hwVal, one_pow]
      have hχpow : chi D v.1 ((primeGen R w.1 ^ n w : Fˣ) : F) =
          chi D v.1 (primeGen R w.1 : F) ^ n w := by
        simpa only [zpow_natCast] using
          (reflection% rf_chi_argument_zpow) v.1 v.2 (primeGen R w.1) hwVal (n w : ℤ)
      rw [Finset.prod_insert hw, Units.val_mul,
        (a2_bridge_SYMBOL D S).chi_mul v.1 v.2 _ _ hwPowVal.le (hprodUnit T hTail).le,
        hχpow, ih hTail, Finset.prod_insert hw]
  obtain ⟨ε, hε⟩ := allowed_generator_sixth_relation R I a ha V hV
  have hsplit : (∏ w ∈ V, primeGen R w.1 ^ n w : Fˣ) = primeGen R v.1 ^ n v * G :=
    (Finset.mul_prod_erase V (fun w => primeGen R w.1 ^ n w) hv).symm
  have hComp : (a : F) / (primeGen R v.1 : F) ^ n v =
      (((ε : Fˣ) : F) ^ (6 : ℕ)) * (G : F) := by
    have heqF := congrArg (fun a : Fˣ => (a : F)) hε
    have hsplitF := congrArg (fun a : Fˣ => (a : F)) hsplit
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at heqF hsplitF
    rw [heqF, hsplitF]
    field_simp [(primeGen R v.1).ne_zero]
  have hεval : v.1.valuation F ((ε : Fˣ) : F) = 1 :=
    Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F) ε v.2
  have hε6val : v.1.valuation F (((ε : Fˣ) : F) ^ (6 : ℕ)) = 1 := by
    rw [map_pow, hεval, one_pow]
  have hres := (a2_bridge_SYMBOL D S).residue_ne_zero v.1 ((ε : Fˣ) : F) hεval.le
  have h6 := (a2_bridge_SYMBOL D S).chi_six v.1 ((ε : Fˣ) : F) (hres.mpr hεval)
  have hχ6 : chi D v.1 (((ε : Fˣ) : F) ^ (6 : ℕ)) = 1 := by
    have h : chi D v.1 (((ε : Fˣ) : F) ^ (6 : ℕ)) = chi D v.1 ((ε : Fˣ) : F) ^ (6 : ℤ) := by
      simpa using (reflection% rf_chi_argument_zpow) v.1 v.2 (ε : Fˣ) hεval (6 : ℤ)
    have h6z : chi D v.1 ((ε : Fˣ) : F) ^ (6 : ℤ) = 1 := by simpa using h6
    rw [h6z] at h
    exact h
  rw [hComp, (a2_bridge_SYMBOL D S).chi_mul v.1 v.2 _ _ hε6val.le
    (hprodUnit _ (Finset.Subset.refl _)).le, hχ6, one_mul]
  exact hχprod _ (Finset.Subset.refl _)

end ArtinPrimitiveRoots.Proofs.e_c
