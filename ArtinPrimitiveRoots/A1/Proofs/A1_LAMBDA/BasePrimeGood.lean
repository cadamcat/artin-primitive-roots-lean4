import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions
import OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: If lambda maps into v then the associated element 3 does too, contradicting S.over6. Apply OAI.card_sub_one_div_three to the base prime.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem base_prime_good (S : SData F CE condη) (ι : E →ₐ[ℚ] F)
    (v : FinPlace F) (hv : v ∉ S.Sf) :
    lambda ∉ (basePlace ι v).asIdeal ∧
      3 ∣ Nat.card (OE ⧸ (basePlace ι v).asIdeal) - 1 := by
  have hgood : lambda ∉ (basePlace ι v).asIdeal := by
    intro hmem
    have hpowmem : lambda ^ 2 ∈ (basePlace ι v).asIdeal := by
      simpa only [pow_two] using
        (basePlace ι v).asIdeal.mul_mem_left lambda hmem
    have h3E : (3 : OE) ∈ (basePlace ι v).asIdeal := by
      obtain ⟨c, hc⟩ := OAI.ActualEisensteinCubic.lambda_sq_dvd_three
      rw [hc]
      simpa only [mul_comm] using (basePlace ι v).asIdeal.mul_mem_left c hpowmem
    change integerEmbedding ι (3 : OE) ∈ v.asIdeal at h3E
    have h3F : (3 : 𝓞 F) ∈ v.asIdeal := by
      simpa only [integerEmbedding, map_ofNat] using h3E
    have h6 : (6 : 𝓞 F) ∈ v.asIdeal := by
      have hm := v.asIdeal.mul_mem_left (2 : 𝓞 F) h3F
      norm_num at hm ⊢
      exact hm
    exact hv (S.over6 v h6)
  refine ⟨hgood, ?_⟩
  let P := (basePlace ι v).asIdeal
  have hP : P.IsMaximal := (basePlace ι v).isMaximal
  exact @OAI.ActualEisensteinCubic.card_sub_one_div_three P hP hgood

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
