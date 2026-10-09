import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.UnitQuotients

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







local macro "characters% " n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `ArtinPrimitiveRoots.A1.Characters
    (`ArtinPrimitiveRoots.A1 ++ n.getId)))
include R

theorem coordinate_generator_valuation (I : S.ExtIdeal) (v : ExteriorPrime S) :
    v.1.valuation F (R.exterior.genR (coordinateIdeal R I v) : F) =
      v.1.valuation F (R.exterior.genR I : F) := by
  have he : idealExp v.1 (coordinateIdeal R I v).1 = idealExp v.1 I.1 := by
    simp only [coordinateIdeal, R.exterior.pow_val, R.exterior.prime_val]
    rw [(characters% conductor_idealExp_primePower_early) v.1 v.1]
    simp
  rw [R.exterior.genR_val, R.exterior.genR_val,
    generator_valuation R (coordinateIdeal R I v) (bc.gen _) (bc.gen_spec _).1 v,
    generator_valuation R I (bc.gen I) (bc.gen_spec I).1 v, he]

theorem generatorR_valuation (I : S.ExtIdeal) (a : S.R) (ha : S.IsGen (a : F) I.1)
    (v : ExteriorPrime S) :
    v.1.valuation F (a : F) = WithZero.exp (-(idealExp v.1 I.1 : ℤ)) := by
  simpa using generator_valuation R I (Units.mk0 (a : F) ha.2.1) ha v

theorem generatorR_valuation_eq (I : S.ExtIdeal) (a : S.R) (ha : S.IsGen (a : F) I.1)
    (v : ExteriorPrime S) :
    v.1.valuation F (R.exterior.genR I : F) = v.1.valuation F (a : F) := by
  rw [generatorR_valuation R I a ha v, R.exterior.genR_val,
    generator_valuation R I (bc.gen I) (bc.gen_spec I).1 v]

theorem mem_coordinate_valuation_le (I : S.ExtIdeal) (v : ExteriorPrime S)
    (r : S.R) (hr : r ∈ coordinateSpan R I v) :
    v.1.valuation F (r : F) ≤ v.1.valuation F (R.exterior.genR I : F) := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hr
  have hF : (r : F) = (R.exterior.genR (coordinateIdeal R I v) : F) * (y : F) := by
    simpa using congrArg (fun t : S.R => (t : F)) hy
  calc
    _ = v.1.valuation F (R.exterior.genR (coordinateIdeal R I v) : F) *
        v.1.valuation F (y : F) := by rw [hF, map_mul]
    _ ≤ v.1.valuation F (R.exterior.genR (coordinateIdeal R I v) : F) * 1 :=
      mul_le_mul' le_rfl (y.property v.1 v.2)
    _ = _ := by rw [mul_one, coordinate_generator_valuation R I v]

theorem psi_div_congr (v : FinPlace F) (n n' den : F) (hden : den ≠ 0)
    (hval : v.valuation F (n - n') ≤ v.valuation F den) :
    A.ψ v (algebraMap F (v.adicCompletion F) (-n / den)) =
      A.ψ v (algebraMap F (v.adicCompletion F) (-n' / den)) := by
  have hdv : v.valuation F den ≠ 0 := (v.valuation F).ne_zero_iff.mpr hden
  have hdpos : 0 < v.valuation F den := by
    change ⊥ < v.valuation F den
    exact bot_lt_iff_ne_bot.mpr hdv
  apply addchar_congr_integral R v
  have harg : (-n / den) - (-n' / den) = -((n - n') / den) := by ring
  rw [harg, Valuation.map_neg, map_div₀]
  exact (div_le_one₀ hdpos).mpr hval

theorem local_character_congr (I : S.ExtIdeal) (v : ExteriorPrime S) (d d' : S.R)
    (hd : d - d' ∈ coordinateSpan R I v) :
    chiPow D v.1 (d : F) 1 ^ idealExp v.1 I.1 =
      chiPow D v.1 (d' : F) 1 ^ idealExp v.1 I.1 := by
  by_cases he : idealExp v.1 I.1 = 0
  · simp only [he, pow_zero]
  have hpos : (0 : ℤ) < (idealExp v.1 I.1 : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero he
  have hlt : v.1.valuation F ((d - d' : S.R) : F) < 1 := by
    refine (mem_coordinate_valuation_le R I v (d - d') hd).trans_lt ?_
    rw [R.exterior.genR_val, generator_valuation R I (bc.gen I) (bc.gen_spec I).1 v]
    exact WithZero.exp_lt_one_iff.mpr (by linarith)
  have hres : residue v.1 (d : F) = residue v.1 (d' : F) :=
    (a2_bridge_SYMBOL D S).residue_congr v.1 (d : F) (d' : F)
      (d.property v.1 v.2) (d'.property v.1 v.2) (by simpa using hlt)
  rw [chiPow_residue_congr R v.1 (d : F) (d' : F) 1 hres]

end ArtinPrimitiveRoots.Proofs.e_c
