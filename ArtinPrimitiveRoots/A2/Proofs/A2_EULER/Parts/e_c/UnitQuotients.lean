import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.CharacterProducts

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
local macro "reflection% " n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `ArtinPrimitiveRoots.A2.Reflection.Missing
    (`ArtinPrimitiveRoots.A2 ++ n.getId)))
include R

theorem prime_span_maximal (v : ExteriorPrime S) :
    (Ideal.span {primeR R v}).IsMaximal := by
  have hp : S.IsGen (primeR R v : F) v.1.asIdeal := by
    have h := (bc.gen_spec (R.exterior.prime v.1 v.2)).1
    simpa [primeR, R.exterior.genR_val, R.exterior.prime_val] using h
  let e := (addchar% crtResidueEquiv) S hp.1 hp
  have hF : IsField (S.R ⧸ Ideal.span {(addchar% crtSInteger) S hp}) :=
    e.toMulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient v.1.asIdeal).mp
      v.1.isMaximal)
  have hmax := (Ideal.Quotient.maximal_ideal_iff_isField_quotient
    (Ideal.span {(addchar% crtSInteger) S hp})).mpr hF
  have hr : (addchar% crtSInteger) S hp = primeR R v := by
    apply Subtype.ext
    rfl
  simpa only [hr] using hmax

theorem residue_isUnit_of_valuation_one (v : ExteriorPrime S) (k : ℕ) (r : S.R)
    (hr : v.1.valuation F (r : F) = 1) :
    IsUnit (Ideal.Quotient.mk
      (Ideal.span {R.exterior.genR (R.exterior.pow (R.exterior.prime v.1 v.2) k)}) r) := by
  let K : Ideal S.R := Ideal.span {primeR R v}
  have hnot : r ∉ K := by
    intro hm
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hm
    have hF : (r : F) = (primeR R v : F) * (a : F) := by
      simpa using congrArg (fun t : S.R => (t : F)) ha
    have hle : v.1.valuation F (r : F) ≤ v.1.valuation F (primeGen R v.1 : F) := by
      rw [hF, map_mul, primeR_val]
      simpa only [mul_one] using
        mul_le_mul' (le_rfl : v.1.valuation F (primeGen R v.1 : F) ≤
          v.1.valuation F (primeGen R v.1 : F)) (a.property v.1 v.2)
    have hlt : v.1.valuation F (primeGen R v.1 : F) < 1 := by
      rw [primeGen_valuation R v]
      exact WithZero.exp_lt_one_iff.mpr (by norm_num)
    rw [hr] at hle
    exact not_lt_of_ge hle hlt
  have hmax : K.IsMaximal := prime_span_maximal R v
  have hne : K ⊔ Ideal.span {r} ≠ K := by
    intro heq
    have hrSup : r ∈ K ⊔ Ideal.span {r} :=
      Submodule.mem_sup_right (Ideal.subset_span (by simp))
    exact hnot (by simpa only [heq] using hrSup)
  have hlt : K < K ⊔ Ideal.span {r} := lt_of_le_of_ne le_sup_left hne.symm
  have hcop : IsCoprime K (Ideal.span {r}) :=
    Ideal.isCoprime_iff_sup_eq.mpr (hmax.1.2 _ hlt)
  have hpow : IsCoprime (K ^ k) (Ideal.span {r}) := hcop.pow_left
  apply (addchar% crt_unit_mk_of_principal_coprime) _ r
  rw [prime_power_span R v k, ← Ideal.span_singleton_pow]
  exact hpow

theorem generator_valuation (I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1)
    (v : ExteriorPrime S) :
    v.1.valuation F (a : F) = WithZero.exp (-(idealExp v.1 I.1 : ℤ)) := by
  have hc : FractionalIdeal.count F v.1
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
        (idealExp v.1 I.1 : ℤ) := by
    rw [ha.2.2 v.1 v.2, FractionalIdeal.count_coe F v.1
      (by simpa only [Ideal.zero_eq_bot] using I.property.1)]
    rfl
  have hlog := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    v.1 (a : F) a.ne_zero
  rw [hc] at hlog
  calc
    _ = WithZero.exp (WithZero.log (v.1.valuation F (a : F))) :=
      (WithZero.exp_log ((v.1.valuation F).ne_zero_iff.mpr a.ne_zero)).symm
    _ = _ := by congr 1; linarith

def complementR (a : S.R) (v : ExteriorPrime S) (n : ℕ)
    (hn : v.1.valuation F (a : F) = (v.1.valuation F (primeGen R v.1 : F)) ^ n) : S.R :=
  ⟨(a : F) / (primeGen R v.1 : F) ^ n, by
    intro w hw
    by_cases hwv : w = v.1
    · subst w
      have hOne : v.1.valuation F ((a : F) / (primeGen R v.1 : F) ^ n) = 1 := by
        rw [map_div₀, map_pow, hn]
        exact div_self (pow_ne_zero n ((v.1.valuation F).ne_zero_iff.mpr (primeGen R v.1).ne_zero))
      exact hOne.le
    · have hpw : w.valuation F (primeGen R v.1 : F) = 1 :=
        (reflection% rf_primeGen_globalVal_one_of_ne) R v.1 w v.2 hw (Ne.symm hwv)
      rw [map_div₀, map_pow, hpw, one_pow, div_one]
      exact a.property w hw⟩

theorem complementR_val (a : S.R) (v : ExteriorPrime S) (n : ℕ)
    (hn : v.1.valuation F (a : F) = (v.1.valuation F (primeGen R v.1 : F)) ^ n) :
    (complementR R a v n hn : F) = (a : F) / (primeGen R v.1 : F) ^ n := rfl

theorem complementR_unit (a : S.R) (v : ExteriorPrime S) (n : ℕ)
    (hn : v.1.valuation F (a : F) = (v.1.valuation F (primeGen R v.1 : F)) ^ n) :
    v.1.valuation F (complementR R a v n hn : F) = 1 := by
  rw [complementR_val, map_div₀, map_pow, hn]
  exact div_self (pow_ne_zero n ((v.1.valuation F).ne_zero_iff.mpr (primeGen R v.1).ne_zero))

omit R in
noncomputable def quotientMulEquiv {Q : Type*} [CommRing Q] (u : Qˣ) : Q ≃ Q where
  toFun x := (u : Q) * x
  invFun x := ((u⁻¹ : Qˣ) : Q) * x
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]

end ArtinPrimitiveRoots.Proofs.e_c
