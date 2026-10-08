import ArtinPrimitiveRoots.Theta.Proofs.«TH-GOOD-SUBGROUP».ProjectedCongruence

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Uniqueness of the local level lifts makes their restricted-product lift a hom. -/
theorem th_good_level_hom (P : CoverPackage D S H A)
    (T0 : Finset (FinPlace F)) (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v) (j : P.RP) :
    ∃ Γ0 : Subgroup (SL(2, 𝓞 F)), Γ0.FiniteIndex ∧
      ∃ σ : Γ0 →* P.RP,
        (∀ γ, th_classical_finiteLevel P T0 hT0 m (σ γ)) ∧
        ∀ (γ : Γ0) (v : FinPlace F), (P.loc v).pr (P.compF v
          (P.ratRP (Matrix.SpecialLinearGroup.toGL (Spec.toSLF F (γ : SL(2, 𝓞 F)))) * j)) =
            (P.loc v).pr (P.compF v (j * σ γ)) := by
  classical
  obtain ⟨N, hN, hNk⟩ := th_good_projected_congruence P T0 hT0 m hm j
  let Γ0 : Subgroup (SL(2, 𝓞 F)) := Spec.congrSubgroup F N
  have hΓ0 : Γ0.FiniteIndex := by
    letI : Finite (𝓞 F ⧸ N) := Ring.HasFiniteQuotients.finiteQuotient hN
    letI : Fintype (𝓞 F ⧸ N) := Fintype.ofFinite _
    letI : Fintype (SL(2, 𝓞 F ⧸ N)) := Fintype.ofFinite _
    dsimp [Γ0, Spec.congrSubgroup]
    infer_instance
  choose k hklevel hkproj using fun γ : Γ0 => hNk (γ : SL(2, 𝓞 F)) γ.property
  let g : Γ0 →* GL (Fin 2) F :=
    Matrix.SpecialLinearGroup.toGL.comp ((Spec.toSLF F).comp Γ0.subtype)
  let φ (v : FinPlace F) : Γ0 →* PGL2 (v.adicCompletion F) :=
    { toFun := fun γ => QuotientGroup.mk
        (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (g γ))
      map_one' := by simp only [map_one, QuotientGroup.mk_one]
      map_mul' := by intro γ δ; simp only [map_mul, QuotientGroup.mk_mul] }
  let β (v : FinPlace F) : PGL2 (v.adicCompletion F) := (P.loc v).pr (P.compF v j)
  have hkp (γ : Γ0) (v : FinPlace F) :
      (P.loc v).pr (P.compF v (k γ)) = (β v)⁻¹ * φ v γ * β v := by
    have he : φ v γ * β v = β v * (P.loc v).pr (P.compF v (k γ)) := by
      change QuotientGroup.mk (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (Matrix.SpecialLinearGroup.toGL (Spec.toSLF F (γ : SL(2, 𝓞 F))))) * β v =
          β v * (P.loc v).pr (P.compF v (k γ))
      simpa only [map_mul, P.compF_ratRP, (P.loc v).sec_pr, β] using hkproj γ v
    calc
      (P.loc v).pr (P.compF v (k γ)) =
          (β v)⁻¹ * (β v * (P.loc v).pr (P.compF v (k γ))) :=
        (inv_mul_cancel_left _ _).symm
      _ = (β v)⁻¹ * (φ v γ * β v) := congrArg (fun a => (β v)⁻¹ * a) he.symm
      _ = (β v)⁻¹ * φ v γ * β v := (mul_assoc _ _ _).symm
  have hlevelOne : th_classical_finiteLevel P T0 hT0 m 1 := by
    refine ⟨fun w => map_one _, ?_, ?_⟩
    · intro v hv
      rw [map_one]
      exact ((P.loc v).Kc (m v)).one_mem
    · intro v hv
      rw [map_one]
      exact (P.tame v (fun h => hv (hT0 h))).Kmax.one_mem
  have hlevelMul (a b : P.RP)
      (ha : th_classical_finiteLevel P T0 hT0 m a)
      (hb : th_classical_finiteLevel P T0 hT0 m b) :
      th_classical_finiteLevel P T0 hT0 m (a * b) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w
      simp only [map_mul, ha.1 w, hb.1 w, mul_one]
    · intro v hv
      rw [map_mul]
      exact ((P.loc v).Kc (m v)).mul_mem (ha.2.1 v hv) (hb.2.1 v hv)
    · intro v hv
      rw [map_mul]
      exact (P.tame v (fun h => hv (hT0 h))).Kmax.mul_mem (ha.2.2 v hv) (hb.2.2 v hv)
  have huniq (a b : P.RP)
      (ha : th_classical_finiteLevel P T0 hT0 m a)
      (hb : th_classical_finiteLevel P T0 hT0 m b)
      (hp : ∀ v, (P.loc v).pr (P.compF v a) = (P.loc v).pr (P.compF v b)) : a = b := by
    apply P.comp_ext
    · intro v
      by_cases hv : v ∈ T0
      · exact (P.loc v).Kc_inj (m v) (hm v hv) (ha.2.1 v hv) (hb.2.1 v hv) (hp v)
      · exact (P.tame v (fun h => hv (hT0 h))).inj (ha.2.2 v hv) (hb.2.2 v hv) (hp v)
    · intro w
      rw [ha.1 w, hb.1 w]
  have hkOne : k 1 = 1 := by
    apply huniq _ _ (hklevel 1) hlevelOne
    intro v
    simp only [hkp, map_one, mul_one, inv_mul_cancel]
  have hkMul (γ δ : Γ0) : k (γ * δ) = k γ * k δ := by
    apply huniq _ _ (hklevel (γ * δ)) (hlevelMul _ _ (hklevel γ) (hklevel δ))
    intro v
    simp only [map_mul, hkp, mul_assoc, mul_inv_cancel_left]
  let σ : Γ0 →* P.RP :=
    { toFun := k
      map_one' := hkOne
      map_mul' := hkMul }
  exact ⟨Γ0, hΓ0, σ, hklevel, hkproj⟩

end ArtinPrimitiveRoots.A1.Theta
