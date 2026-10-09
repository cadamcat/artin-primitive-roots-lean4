import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.PrimeInfrastructure

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain MeasureTheory
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


include R

theorem tuple_weight_product (B : PrimeTupleBridge S) (p : IdealTuple S) (ξ w z : ℂ) :
    (qI p.1.1 : ℂ) ^ (-1 / 2 - ξ) * (qI p.2.1.1 : ℂ) ^ (-1 - 3 * ξ) *
      (qI p.2.2.1.1 : ℂ) ^ (-w) * (qI p.2.2.2.1 : ℂ) ^ (-6 * z) =
    ∏ v ∈ (B.equiv p).support, (qI v.1.asIdeal : ℂ) ^
      (-(((B.equiv p v).1 : ℕ) : ℂ) * (1 / 2 + ξ) -
        ((B.equiv p v).2.1 : ℂ) * (1 + 3 * ξ) -
        ((B.equiv p v).2.2.1 : ℂ) * w - 6 * ((B.equiv p v).2.2.2 : ℂ) * z) := by
  classical
  let V := (B.equiv p).support
  have hcV : ∀ v : ExteriorPrime S, idealExp v.1 (R.exterior.ofSqf p.1).1 ≠ 0 → v ∈ V := by
    intro v hn
    by_contra hv
    exact hn (by simpa only [R.exterior.ofSqf_val] using (tuple_exponents_zero R B p v hv).1)
  have hnV : ∀ v : ExteriorPrime S, idealExp v.1 p.2.1.1 ≠ 0 → v ∈ V := by
    intro v hn
    by_contra hv
    exact hn (tuple_exponents_zero R B p v hv).2.1
  have hsV : ∀ v : ExteriorPrime S, idealExp v.1 p.2.2.1.1 ≠ 0 → v ∈ V := by
    intro v hn
    by_contra hv
    exact hn (tuple_exponents_zero R B p v hv).2.2.1
  have hrV : ∀ v : ExteriorPrime S, idealExp v.1 p.2.2.2.1 ≠ 0 → v ∈ V := by
    intro v hn
    by_contra hv
    exact hn (tuple_exponents_zero R B p v hv).2.2.2
  have hcW := norm_weight_on R (R.exterior.ofSqf p.1) V hcV (-1 / 2 - ξ)
  have hnW := norm_weight_on R p.2.1 V hnV (-1 - 3 * ξ)
  have hsW := norm_weight_on R p.2.2.1 V hsV (-w)
  have hrW := norm_weight_on R p.2.2.2 V hrV (-6 * z)
  simp only [R.exterior.ofSqf_val] at hcW
  rw [hcW, hnW, hsW, hrW, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  rcases tuple_exponents R B p v with ⟨hc, hn, hs, hr⟩
  rw [hc, hn, hs, hr]
  have hq : (qI v.1.asIdeal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one (qI_prime_gt_one v.1)).ne'
  rw [← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
  congr 1
  ring

theorem coefficient_of_core (B : PrimeTupleBridge S) (u : U.U) (ξ w z : ℂ)
    (p : IdealTuple S)
    (hcore : gamma D S A 2 p.1.1 (cgen R p.1) *
        finiteFactor R p.2.2.1 (Aideal R p.1 p.2.1) (Agen R p.1 p.2.1)
          ((U.repr u : F) * (bc.gen p.2.2.2 : F) ^ 6) =
      ∏ v ∈ (B.equiv p).support,
        gamma D S A 2 v.1.asIdeal (primeGen R v.1 : F) ^ ((B.equiv p v).1 : ℕ) *
          chi D v.1 ((U.repr u : F) / (primeGen R v.1 : F) ^ frequencyValuation η U u v.1) ^
            (((B.equiv p v).2.2.1 : ℤ) - (((B.equiv p v).1 : ℕ) : ℤ) -
              3 * ((B.equiv p v).2.1 : ℤ)) *
          localC R v.1 v.2 (((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1)
            (B.equiv p v).2.2.1 (frequencyValuation η U u v.1 + 6 * (B.equiv p v).2.2.2)) :
    calFTerm R η U u ξ w z p =
      ∏ v ∈ (B.equiv p).support,
        localEulerTerm R η U u v.1 v.2 ξ w z (B.equiv p v) := by
  classical
  have htheta := theta_Aideal_product R B p
  have hweight := tuple_weight_product R B p ξ w z
  calc
    _ = (gamma D S A 2 p.1.1 (cgen R p.1) *
        finiteFactor R p.2.2.1 (Aideal R p.1 p.2.1) (Agen R p.1 p.2.1)
          ((U.repr u : F) * (bc.gen p.2.2.2 : F) ^ 6)) *
        ϑ.idealValue (Aideal R p.1 p.2.1).1 *
        ((qI p.1.1 : ℂ) ^ (-1 / 2 - ξ) * (qI p.2.1.1 : ℂ) ^ (-1 - 3 * ξ) *
          (qI p.2.2.1.1 : ℂ) ^ (-w) * (qI p.2.2.2.1 : ℂ) ^ (-6 * z)) := by
      unfold calFTerm
      ring
    _ = _ := by
      rw [hcore, htheta, hweight, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hv
      dsimp [localEulerTerm]
      ring

end ArtinPrimitiveRoots.Proofs.e_c
