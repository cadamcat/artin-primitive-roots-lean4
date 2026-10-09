import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.FiniteFactorCRT

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

theorem valuation_one_ne_zero (v : ExteriorPrime S) (a : F)
    (ha : v.1.valuation F a = 1) : a ≠ 0 := by
  intro hz
  rw [hz, map_zero] at ha
  exact zero_ne_one ha

theorem chi_unit_ne_zero (v : ExteriorPrime S) (a : F)
    (ha : v.1.valuation F a = 1) : chi D v.1 a ≠ 0 := by
  have hres := (a2_bridge_SYMBOL D S).residue_ne_zero v.1 a ha.le
  have h6 := (a2_bridge_SYMBOL D S).chi_six v.1 a (hres.mpr ha)
  intro hz
  rw [hz] at h6
  norm_num at h6

theorem chiPow_one_eq_chi (v : FinPlace F) (a : F) : chiPow D v a 1 = chi D v a := by
  by_cases hr : residue v a = 0
  · simp [chiPow, chi, hr]
  · simp [chiPow, hr]

theorem chi_ratio (v : ExteriorPrime S) (a b : F)
    (ha : v.1.valuation F a = 1) (hb : v.1.valuation F b = 1) :
    chi D v.1 (b / a) = chi D v.1 b / chi D v.1 a := by
  let ua := Units.mk0 a (valuation_one_ne_zero R v a ha)
  have hInvVal : v.1.valuation F a⁻¹ = 1 := by rw [Valuation.map_inv, ha, inv_one]
  have hInvChi : chi D v.1 a⁻¹ = (chi D v.1 a)⁻¹ := by
    simpa [ua] using (reflection% rf_chi_argument_zpow)
      v.1 v.2 ua ha (-1 : ℤ)
  rw [div_eq_mul_inv, (a2_bridge_SYMBOL D S).chi_mul v.1 v.2 b a⁻¹ hb.le hInvVal.le,
    hInvChi, div_eq_mul_inv]

theorem prime_character_substitution (v : ExteriorPrime S) (k : ℕ)
    (a b d d' : S.R) (ha : v.1.valuation F (a : F) = 1)
    (hb : v.1.valuation F (b : F) = 1)
    (hd : a * d - b * d' ∈ Ideal.span {primeR R v ^ k}) :
    chiPow D v.1 (d : F) 1 ^ k =
      chi D v.1 ((b : F) / (a : F)) ^ k * chiPow D v.1 (d' : F) 1 ^ k := by
  by_cases hk : k = 0
  · simp only [hk, pow_zero, mul_one]
  have hkpos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hd
  have hF : ((a * d - b * d' : S.R) : F) = (primeGen R v.1 : F) ^ k * (y : F) := by
    simpa [primeR_val] using congrArg (fun t : S.R => (t : F)) hy
  have hlt : v.1.valuation F (((a * d - b * d' : S.R) : F)) < 1 := by
    rw [hF, map_mul, map_pow, primeGen_valuation R v, ← WithZero.exp_nsmul]
    refine lt_of_le_of_lt (mul_le_mul' le_rfl (y.property v.1 v.2)) ?_
    rw [mul_one]
    apply WithZero.exp_lt_one_iff.mpr
    simpa using neg_neg_of_pos hkpos
  have hres : residue v.1 ((a * d : S.R) : F) = residue v.1 ((b * d' : S.R) : F) :=
    (a2_bridge_SYMBOL D S).residue_congr v.1 _ _
      ((a * d).property v.1 v.2) ((b * d').property v.1 v.2) (by simpa using hlt)
  have hchi := (a2_bridge_SYMBOL D S).chi_congr v.1 _ _ hres
  have hmul : chi D v.1 (a : F) * chi D v.1 (d : F) =
      chi D v.1 (b : F) * chi D v.1 (d' : F) := by
    push_cast at hchi
    rw [(a2_bridge_SYMBOL D S).chi_mul v.1 v.2 (a : F) (d : F)
      ha.le (d.property v.1 v.2),
      (a2_bridge_SYMBOL D S).chi_mul v.1 v.2 (b : F) (d' : F)
      hb.le (d'.property v.1 v.2)] at hchi
    exact hchi

  have heq : chi D v.1 (d : F) =
      chi D v.1 ((b : F) / (a : F)) * chi D v.1 (d' : F) := by
    rw [chi_ratio R v (a : F) (b : F) ha hb]
    apply mul_left_cancel₀ (chi_unit_ne_zero R v (a : F) ha)
    rw [hmul]
    field_simp [chi_unit_ne_zero R v (a : F) ha]
  rw [chiPow_one_eq_chi R, chiPow_one_eq_chi R, heq, mul_pow]

theorem prime_substitution_phase (v : ExteriorPrime S) (k t J : ℕ)
    (sp ap hp d d' x x' : S.R)
    (hsp : v.1.valuation F (sp : F) = 1) (hap : v.1.valuation F (ap : F) = 1)
    (hd : ap * d - hp * d' ∈ Ideal.span {primeR R v ^ k})
    (hx : hp * x - sp * ap * x' ∈ Ideal.span {primeR R v ^ t})
    (hm : primeR R v ^ J - primeR R v ^ t * d' ∈ Ideal.span {primeR R v ^ k}) :
    A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
      (-(((primeR R v ^ J * hp - primeR R v ^ t * ap * d) * x : S.R) : F) /
        ((primeGen R v.1 : F) ^ (k + t) * (sp : F) * (ap : F)))) =
    A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
      (-(((primeR R v ^ J - primeR R v ^ t * d') * x' : S.R) : F) /
        (primeGen R v.1 : F) ^ (k + t))) := by
  obtain ⟨yd, hdy⟩ := Ideal.mem_span_singleton.mp hd
  obtain ⟨yx, hxy⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨ym, hmy⟩ := Ideal.mem_span_singleton.mp hm
  have hpoly : (primeR R v ^ J * hp - primeR R v ^ t * ap * d) * x -
      (primeR R v ^ J - primeR R v ^ t * d') * sp * ap * x' =
        primeR R v ^ (k + t) * (ym * yx - yd * x) := by
    calc
      _ = (primeR R v ^ J - primeR R v ^ t * d') * (hp * x - sp * ap * x') -
          primeR R v ^ t * (ap * d - hp * d') * x := by ring
      _ = _ := by rw [hxy, hdy, hmy, pow_add]; ring
  have hpolyF := congrArg (fun z : S.R => (z : F)) hpoly
  have hp0 : (primeGen R v.1 : F) ≠ 0 := (primeGen R v.1).ne_zero
  have hsp0 := valuation_one_ne_zero R v (sp : F) hsp
  have hap0 := valuation_one_ne_zero R v (ap : F) hap
  have harg :
      (-(((primeR R v ^ J * hp - primeR R v ^ t * ap * d) * x : S.R) : F) /
          ((primeGen R v.1 : F) ^ (k + t) * (sp : F) * (ap : F))) -
        (-(((primeR R v ^ J - primeR R v ^ t * d') * x' : S.R) : F) /
          (primeGen R v.1 : F) ^ (k + t)) =
      -(((ym * yx - yd * x : S.R) : F) / ((sp : F) * (ap : F))) := by
    push_cast at hpolyF ⊢
    simp only [primeR_val] at hpolyF ⊢
    field_simp [hp0, hsp0, hap0]
    linear_combination -hpolyF
  apply addchar_congr_integral R v.1
  rw [harg, Valuation.map_neg, map_div₀, map_mul, hsp, hap, one_mul, div_one]
  exact (ym * yx - yd * x).property v.1 v.2

end ArtinPrimitiveRoots.Proofs.e_c
