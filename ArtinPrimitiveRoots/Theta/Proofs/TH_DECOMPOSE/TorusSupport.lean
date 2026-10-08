import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.CongruenceShrinking

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private def cubicSymbolHom (D : FieldData F) : rootsOfUnity 6 F →* rootsOfUnity 3 ℂ where
  toFun := muThree D
  map_one' := by
    apply rootsOfUnity.coe_injective
    simp [muThree]
  map_mul' ζ ξ := by
    apply rootsOfUnity.coe_injective
    simp [muThree, map_mul, mul_pow]

private def pairingCharacter (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (y : (v.adicCompletion F)ˣ) : (v.adicCompletion F)ˣ →* rootsOfUnity 3 ℂ :=
  let l : (v.adicCompletion F)ˣ →* rootsOfUnity 6 F :=
    { toFun := fun x => H.hilb v x y
      map_one' := H.sixth_power v 1 y ⟨1, by simp⟩
      map_mul' := fun x x' => H.mul_left v x x' y }
  let r : (v.adicCompletion F)ˣ →* rootsOfUnity 6 F :=
    { toFun := fun x => H.hilb v y x
      map_one' := by
        have h := H.skew v y 1
        rw [H.sixth_power v 1 y ⟨1, by simp⟩, mul_one] at h
        exact h
      map_mul' := fun x x' => H.mul_right v y x x' }
  ((cubicSymbolHom D).comp l) * ((cubicSymbolHom D).comp r)⁻¹

/-- The finite projective torus action bounds the quotient by a maximal isotropic subgroup. -/
theorem local_lagrangian_finiteIndex (P : CoverPackage D S H A) (G : GlobalDatum P)
    (v : FinPlace F) : (G.Alag v).FiniteIndex := by
  let T := G.T v
  obtain ⟨w, hw⟩ : ∃ w : T.V, G.lam v w ≠ 0 := by
    by_contra h
    push Not at h
    apply G.lam_ne v
    ext w
    exact h w
  have hsig (x : (v.adicCompletion F)ˣ) : T.σa x ≠ 0 := by
    intro hx
    have h := congrArg (fun f : T.V →ₗ[ℂ] T.V => G.lam v (f w))
      (T.σa_mul x⁻¹ x)
    rw [hx, LinearMap.comp_zero, inv_mul_cancel, T.σa_one] at h
    simp only [LinearMap.zero_apply, map_zero, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul, smul_eq_mul] at h
    exact (mul_ne_zero (Units.ne_zero _) hw) h.symm
  have hcomm (x y : (v.adicCompletion F)ˣ) :
      (T.σa x).comp (T.σa y) =
        ((torusPairing D H v x y : ℂˣ) : ℂ) • (T.σa y).comp (T.σa x) := by
    rw [T.σa_mul, T.σa_mul, mul_comm y x, smul_smul]
    congr 1
    simp [torusPairing]
  have hpair (x y : (v.adicCompletion F)ˣ) (hxy : T.σa x = T.σa y)
      (z : (v.adicCompletion F)ˣ) : torusPairing D H v x z = torusPairing D H v y z := by
    have hA : (T.σa z).comp (T.σa x) ≠ 0 := by
      rw [T.σa_mul]
      exact smul_ne_zero (Units.ne_zero _) (hsig (z * x))
    have hc : ((torusPairing D H v x z : ℂˣ) : ℂ) • (T.σa z).comp (T.σa x) =
        ((torusPairing D H v y z : ℂˣ) : ℂ) • (T.σa z).comp (T.σa x) := by
      calc
        _ = (T.σa x).comp (T.σa z) := (hcomm x z).symm
        _ = (T.σa y).comp (T.σa z) := by rw [hxy]
        _ = _ := by rw [hcomm y z, ← hxy]
    exact rootsOfUnity.coe_injective (smul_left_injective ℂ hA hc)
  have hcoset (x y : (v.adicCompletion F)ˣ) (hxy : T.σa x = T.σa y) :
      (Quotient.mk _ x : (v.adicCompletion F)ˣ ⧸ G.Alag v) = Quotient.mk _ y := by
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    apply (G.alag_lagrangian v (x⁻¹ * y)).mpr
    intro z _
    change pairingCharacter D H v z (x⁻¹ * y) = 1
    rw [map_mul, map_inv]
    change (torusPairing D H v x z)⁻¹ * torusPairing D H v y z = 1
    rw [hpair x y hxy z]
    exact inv_mul_cancel _
  let R := Set.range T.σa
  let : Fintype R := T.σa_finite.fintype
  let pick : R → (v.adicCompletion F)ˣ := fun f => Classical.choose f.property
  let q : R → (v.adicCompletion F)ˣ ⧸ G.Alag v := fun f => Quotient.mk _ (pick f)
  have hq : Function.Surjective q := by
    intro c
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective c
    let f : R := ⟨T.σa x, x, rfl⟩
    refine ⟨f, hcoset (pick f) x ?_⟩
    exact Classical.choose_spec f.property
  let : Finite ((v.adicCompletion F)ˣ ⧸ G.Alag v) := Finite.of_surjective q hq
  exact Subgroup.finiteIndex_of_finite_quotient

end ArtinPrimitiveRoots.A1.Theta
