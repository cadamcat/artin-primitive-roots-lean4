import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.TupleLocalFactors
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



theorem frequency_valuation_pow (u : U.U) (v : ExteriorPrime S) :
    v.1.valuation F (U.repr u : F) =
      v.1.valuation F (primeGen R v.1 : F) ^ frequencyValuation η U u v.1 := by
  have hc : (frequencyValuation η U u v.1 : ℤ) =
      FractionalIdeal.count F v.1
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (U.repr u : F)) :=
    Int.toNat_of_nonneg (U.sixth_power_free u v.1 v.2).1
  have hlog := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    v.1 (U.repr u : F) (U.repr_nonzero u)
  rw [← hc] at hlog
  rw [primeGen_valuation R v]
  rw [← WithZero.exp_log ((v.1.valuation F).ne_zero_iff.mpr (U.repr_nonzero u))]
  have hl : WithZero.log (v.1.valuation F (U.repr u : F)) =
      -(frequencyValuation η U u v.1 : ℤ) := by linarith
  rw [hl]
  simp [← WithZero.exp_nsmul]

theorem frequency_r_valuation_pow (u : U.U) (r : S.ExtIdeal) (v : ExteriorPrime S) :
    v.1.valuation F (((U.repr u * R.exterior.genR r ^ 6 : S.R) : F)) =
      v.1.valuation F (primeGen R v.1 : F) ^
        (frequencyValuation η U u v.1 + 6 * idealExp v.1 r.1) := by
  have hr : S.IsGen (R.exterior.genR r : F) r.1 := by
    simpa only [R.exterior.genR_val] using (bc.gen_spec r).1
  change v.1.valuation F ((U.repr u : F) * (R.exterior.genR r : F) ^ 6) = _
  rw [map_mul, map_pow, frequency_valuation_pow R η U u v,
    generator_valuation_pow R r _ hr v, ← pow_mul, ← pow_add]
  congr 1
  omega

theorem frequency_r_complement_character (u : U.U) (r : S.ExtIdeal) (v : ExteriorPrime S) :
    chi D v.1 (((U.repr u : F) * (bc.gen r : F) ^ 6) /
      (primeGen R v.1 : F) ^ (frequencyValuation η U u v.1 + 6 * idealExp v.1 r.1)) =
      chi D v.1 ((U.repr u : F) / (primeGen R v.1 : F) ^ frequencyValuation η U u v.1) := by
  have hr : S.IsGen (R.exterior.genR r : F) r.1 := by
    simpa only [R.exterior.genR_val] using (bc.gen_spec r).1
  let up := complementR R (U.repr u) v _ (frequency_valuation_pow R η U u v)
  let rp := complementR R (R.exterior.genR r) v _ (generator_valuation_pow R r _ hr v)
  have hu := complementR_unit R (U.repr u) v _ (frequency_valuation_pow R η U u v)
  have hrp := complementR_unit R (R.exterior.genR r) v _ (generator_valuation_pow R r _ hr v)
  have h6 : chi D v.1 ((rp : F) ^ (6 : ℕ)) = 1 := by
    let pr := Units.mk0 (rp : F) (valuation_one_ne_zero R v _ hrp)
    have heq : chi D v.1 ((rp : F) ^ (6 : ℕ)) = chi D v.1 (rp : F) ^ (6 : ℤ) := by
      simpa [pr] using (reflection% rf_chi_argument_zpow) v.1 v.2 pr hrp (6 : ℤ)
    have hres := (a2_bridge_SYMBOL D S).residue_ne_zero v.1 (rp : F) hrp.le
    have hsix := (a2_bridge_SYMBOL D S).chi_six v.1 (rp : F) (hres.mpr hrp)
    have hsixz : chi D v.1 (rp : F) ^ (6 : ℤ) = 1 := by simpa using hsix
    exact heq.trans hsixz
  have hrp6 : v.1.valuation F ((rp : F) ^ (6 : ℕ)) = 1 := by rw [map_pow, hrp, one_pow]
  have harg : ((U.repr u : F) * (bc.gen r : F) ^ 6) /
      (primeGen R v.1 : F) ^ (frequencyValuation η U u v.1 + 6 * idealExp v.1 r.1) =
        (up : F) * (rp : F) ^ 6 := by
    dsimp [up, rp]
    rw [complementR_val, complementR_val, R.exterior.genR_val, pow_add]
    field_simp [(primeGen R v.1).ne_zero]
    ring
  rw [harg, (a2_bridge_SYMBOL D S).chi_mul v.1 v.2 _ _ hu.le hrp6.le, h6, mul_one]
  rfl

end ArtinPrimitiveRoots.Proofs.e_c
