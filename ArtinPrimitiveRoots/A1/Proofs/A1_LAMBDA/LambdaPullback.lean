import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.AlignedEmbedding
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.RelativeNormConstruction
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.NormDescent
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.PrimePullback
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.AngularPullback
import OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private lemma lambda_not_mem_basePlace_of_not_mem_Sf (S : SData F CE condη)
    (ι : E →ₐ[ℚ] F) (v : FinPlace F) (hv : v ∉ S.Sf) :
    lambda ∉ (basePlace ι v).asIdeal := by
  intro hmem
  rw [basePlace_asIdeal, Ideal.mem_comap] at hmem
  have hrel' : OAI.ActualEisensteinCubic.omega ^ 2 + OAI.ActualEisensteinCubic.omega + 1 = 0 := by
    simpa only [IsCyclotomicExtension.Rat.Three.coe_eta, OAI.ActualEisensteinCubic.omega] using
      (IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
        (IsCyclotomicExtension.zeta_spec 3 ℚ E))
  have hrel : (3 : OE) = lambda * (OAI.ActualEisensteinCubic.omega ^ 2 - 1) := by
    change (3 : OE) = (OAI.ActualEisensteinCubic.omega - 1) * (OAI.ActualEisensteinCubic.omega ^ 2 - 1)
    linear_combination -(OAI.ActualEisensteinCubic.omega - 2) * hrel'
  have h3 : (3 : 𝓞 F) ∈ v.asIdeal := by
    have hmap : (3 : 𝓞 F) = integerEmbedding ι (3 : OE) := by
      simp only [map_ofNat]
    rw [hmap, hrel, map_mul]
    exact Ideal.mul_mem_right _ _ hmem
  have h6 : (6 : 𝓞 F) ∈ v.asIdeal := by
    have : (6 : 𝓞 F) = 2 * 3 := by norm_num
    rw [this]
    exact Ideal.mul_mem_left _ _ h3
  exact hv (S.over6 v h6)

/-- A1-LAMBDA IMPL: assemble the angular norm pullback and its exterior prime values.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: AlignedEmbedding, BaseCharacter,
RelativeNormConstruction, NormDescent, PrimePullback, AngularPullback. -/
theorem lambda_pullback_data (D : FieldData F) (S : SData F CE condη) :
    ∃ ι : E →ₐ[ℚ] F, ι (algebraMap OE E omega) = D.ζ12 ^ 4 ∧
      ∃ Λ : LambdaChar F, unitary Λ ∧ angularType D Λ ∧
        ∀ v : FinPlace F, v ∉ S.Sf → unramifiedAt Λ v ∧
          primeValue Λ v = eisensteinPrimeValue (complexEmbedding D ι)
            (basePlace ι v) ^ residueDegree ι v := by
  obtain ⟨ι, hι⟩ := aligned_eisenstein_embedding_exists D
  obtain ⟨χ, hχ_unit, hχ_ang, hχ_vals⟩ := base_character_exists (complexEmbedding D ι)
  obtain ⟨N⟩ := relative_norm_data_exists D ι
  obtain ⟨C, hC⟩ := relative_norm_descent D ι N
  refine ⟨ι, hι, χ.comp C, ?_, ?_, ?_⟩
  · intro x
    exact hχ_unit (C x)
  · exact relative_norm_angular_pullback D ι N C hC χ hχ_ang
  · intro v hv
    have hlamb : lambda ∉ (basePlace ι v).asIdeal :=
      lambda_not_mem_basePlace_of_not_mem_Sf S ι v hv
    have hbase := hχ_vals (basePlace ι v) hlamb
    have hpull := relative_norm_prime_pullback D ι N C hC χ v hbase.1
    refine ⟨hpull.1, ?_⟩
    rw [hpull.2, hbase.2]

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
