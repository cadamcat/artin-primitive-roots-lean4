import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.tame_lagrangian_vector_selector

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The spherical Weyl section has scalar torus support in the tame Lagrangian. -/
theorem sphWeyl_lam_zero {P : CoverPackage D S H A}
    (G : GlobalDatum P) (v : FinPlace F) (hv : v ∉ S.Sf)
    (s : ℂ) (y : (v.adicCompletion F)ˣ) (hy : y ∉ G.Alag v) :
    G.lam v (sphWeyl P G v hv s ((P.loc v).a y)) = 0 := by
  have hsec : IsSection (P.loc v) (G.T v).weyl (-s) (sphWeyl P G v hv s) :=
    (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
      (fun h => hv (S.over6 v h)) (-s)).choose_spec.1
  have hval : sphWeyl P G v hv s 1 = (G.B v hv).e 0 := by
    have h :=
      (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
        (fun h => hv (S.over6 v h)) (-s)).choose_spec.2.1
    change sphWeyl P G v hv s 1 = (G.B v hv).e (-0) at h
    simpa only [neg_zero] using h
  have hyinv : y⁻¹ ∉ G.Alag v := by
    intro hi
    apply hy
    simpa using (G.Alag v).inv_mem hi
  have hzero : G.lam v ((G.T v).σa y⁻¹ (sphWeyl P G v hv s 1)) = 0 := by
    rw [hval]
    exact tame_lagrangian_vector_selector G v hv y⁻¹ hyinv
  have h := congrArg (G.lam v) (hsec.1 0 y 1)
  simp only [ofAdd_zero, map_one, one_mul, mul_one] at h
  change G.lam v (sphWeyl P G v hv s ((P.loc v).a y)) =
    G.lam v ((_ : ℂ) • ((G.T v).σa y⁻¹ (sphWeyl P G v hv s 1))) at h
  rw [map_smul, hzero, smul_zero] at h
  exact h

end ArtinPrimitiveRoots.A1.Theta
