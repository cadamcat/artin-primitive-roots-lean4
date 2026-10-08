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

/-- Rational torus classes with trivial exterior local classes form a finite set. -/
theorem finite_exterior_lagrangian_classes (P : CoverPackage D S H A)
    (G : GlobalDatum P) (T : Finset (FinPlace F)) :
    Set.Finite {δ : Fˣ ⧸ G.Δ | ∀ v, v ∉ T → toLoc v δ.out ∈ G.Alag v} := by
  let C : Set (Fˣ ⧸ G.Δ) := {δ | ∀ v, v ∉ T → toLoc v δ.out ∈ G.Alag v}
  let (v : FinPlace F) : (G.Alag v).FiniteIndex := local_lagrangian_finiteIndex P G v
  let f : C → (∀ v : T, (v.val.adicCompletion F)ˣ ⧸ G.Alag v.val) :=
    fun δ v => Quotient.mk _ (toLoc v.val δ.val.out)
  have hf : Function.Injective f := by
    intro δ η h
    apply Subtype.ext
    have hratio : δ.val.out⁻¹ * η.val.out ∈ G.Δ := by
      change δ.val.out⁻¹ * η.val.out ∈
        ⨅ v : FinPlace F, (G.Alag v).comap (toLoc v)
      rw [Subgroup.mem_iInf]
      intro v
      change toLoc v (δ.val.out⁻¹ * η.val.out) ∈ G.Alag v
      rw [map_mul, map_inv]
      by_cases hv : v ∈ T
      · have hlocal : (Quotient.mk _ (toLoc v δ.val.out) :
            (v.adicCompletion F)ˣ ⧸ G.Alag v) = Quotient.mk _ (toLoc v η.val.out) :=
          congrFun h ⟨v, hv⟩
        exact QuotientGroup.leftRel_apply.mp (Quotient.exact hlocal)
      · exact (G.Alag v).mul_mem ((G.Alag v).inv_mem (δ.property v hv))
          (η.property v hv)
    have hq : (Quotient.mk _ δ.val.out : Fˣ ⧸ G.Δ) = Quotient.mk _ η.val.out :=
      Quotient.sound (QuotientGroup.leftRel_apply.mpr hratio)
    simpa only [Quotient.out_eq] using hq
  let : Finite C := Finite.of_injective f hf
  exact C.toFinite

/-- A tame scalar coefficient vanishes outside the local Lagrangian subgroup. -/
theorem tame_lam_sigma_eq_zero (P : CoverPackage D S H A) (G : GlobalDatum P)
    (v : FinPlace F) (hv : v ∉ S.Sf) (x : (v.adicCompletion F)ˣ)
    (hx : x ∉ G.Alag v) : G.lam v ((G.T v).σa x ((G.B v hv).e 0)) = 0 := by
  have hv6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  have hfixed (y : (v.adicCompletion F)ˣ) (hy : y ∈ G.Alag v) :
      (G.T v).σa y ((G.B v hv).e 0) = (G.B v hv).e 0 := by
    obtain ⟨k, u, hu, rfl⟩ := (G.alag_tame v hv y).mp hy
    rw [(G.B v hv).act (3 * k) u hu 0]
    have hexp : 2 * (3 * k + 2 * ((0 : ZMod 3).val : ℤ)) = 6 * k := by
      simp
      ring
    have hidx : (0 : ZMod 3) + ((3 * k : ℤ) : ZMod 3) = 0 := by
      simp [Int.cast_mul, show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]
    have hpow : localChi D v u ^ (6 * k) = 1 := by
      rw [zpow_mul, zpow_ofNat, (localChi_basic (D := D) hv6).2.2.2.1 u hu,
        one_zpow]
    rw [hexp, hidx, hpow, one_smul]
  have hcomm (y : (v.adicCompletion F)ˣ) :
      ((G.T v).σa x).comp ((G.T v).σa y) =
        ((torusPairing D H v x y : ℂˣ) : ℂ) •
          ((G.T v).σa y).comp ((G.T v).σa x) := by
    rw [(G.T v).σa_mul, (G.T v).σa_mul, mul_comm y x, smul_smul]
    congr 1
    simp [torusPairing]
  by_contra hne
  apply hx
  apply (G.alag_lagrangian v x).mpr
  intro y hy
  have h := congrArg
    (fun f : (G.T v).V →ₗ[ℂ] (G.T v).V => G.lam v (f ((G.B v hv).e 0)))
    (hcomm y)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_eq_mul] at h
  rw [hfixed y hy, G.lam_equiv v y hy, G.ω_tame v hv y hy, one_mul] at h
  apply rootsOfUnity.coe_injective
  exact (mul_eq_right₀ hne).mp h.symm

end ArtinPrimitiveRoots.A1.Theta
