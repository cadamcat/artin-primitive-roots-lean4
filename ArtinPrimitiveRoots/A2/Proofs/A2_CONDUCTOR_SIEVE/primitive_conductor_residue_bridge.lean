import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.ideal_S_exterior_split_count
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_residues_exists
import ArtinPrimitiveRoots.Proofs.a2_cond_lead_p.RestrictedProductDensity

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
open scoped RestrictedProduct
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem conductor_localValue_finiteOrder_norm_one
    (ω : A1.HeckeChar F) (hω : IsOfFinOrder ω)
    (v : A1.FinPlace F) (u : (v.adicCompletion F)ˣ) :
    ‖((ω.loc v u : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := hω.exists_pow_eq_one
  have hclassPow :
      (ω (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) ^ n = 1 := by
    have h := congrArg
      (fun χ : A1.HeckeChar F => χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) hpow
    simpa using h
  have hclass : IsOfFinOrder (ω (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) :=
    (isOfFinOrder_iff_pow_eq_one).2 ⟨n, hn, hclassPow⟩
  have hlocal : IsOfFinOrder (ω.loc v u) := by
    change IsOfFinOrder (ω (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))
    exact hclass
  simpa using (Units.isOfFinOrder_val.mpr hlocal).norm_eq_one

private theorem conductor_infiniteValue_finiteOrder_norm_one
    (ω : A1.HeckeChar F) (hω : IsOfFinOrder ω)
    (w : InfinitePlace F) (u : w.Completionˣ) :
    ‖((ω.locInf w u : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := hω.exists_pow_eq_one
  have hclassPow :
      (ω (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ^ n = 1 := by
    have h := congrArg
      (fun χ : A1.HeckeChar F => χ (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) hpow
    simpa using h
  have hclass : IsOfFinOrder (ω (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) :=
    (isOfFinOrder_iff_pow_eq_one).2 ⟨n, hn, hclassPow⟩
  have hlocal : IsOfFinOrder (ω.locInf w u) := by
    change IsOfFinOrder (ω (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
    exact hclass
  simpa using (Units.isOfFinOrder_val.mpr hlocal).norm_eq_one

private theorem conductorLambdaS_norm_one_of_components
    (S : A1.SData F CE condη) (ℓ : SLocalCharacter S)
    (τ : ConductorInfiniteLocal F) (ω : A1.HeckeChar F)
    (hω : IsOfFinOrder ω) (hℓ : SComponent S ω = ℓ)
    (hτ : conductorInfiniteComponent ω = τ) :
    ∀ a : Fˣ, ‖conductorLambdaS S ℓ τ a‖ = 1 := by
  intro a
  have hfinite : ∀ v : S.Sf,
      ‖((ℓ v (Units.map
        (algebraMap F (v.1.adicCompletion F)).toMonoidHom a) : ℂ))‖ = 1 := by
    intro v
    have heq : ω.loc v.1 = ℓ v := by
      have h := congrFun hℓ v
      simpa [SComponent] using h
    have hval := congrArg (fun φ : (v.1.adicCompletion F)ˣ →* ℂˣ =>
      φ (Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom a)) heq
    rw [← hval]
    exact conductor_localValue_finiteOrder_norm_one ω hω v.1
      (Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom a)
  have hinfinite : ∀ w : InfinitePlace F,
      ‖((τ w (Units.map (algebraMap F w.Completion).toMonoidHom a) : ℂ))‖ = 1 := by
    intro w
    have heq : ω.locInf w = τ w := by
      have h := congrFun hτ w
      simpa [conductorInfiniteComponent] using h
    have hval := congrArg (fun φ : w.Completionˣ →* ℂˣ =>
      φ (Units.map (algebraMap F w.Completion).toMonoidHom a)) heq
    rw [← hval]
    exact conductor_infiniteValue_finiteOrder_norm_one ω hω w
      (Units.map (algebraMap F w.Completion).toMonoidHom a)
  simp only [conductorLambdaS, norm_inv, Units.val_mul, norm_mul]
  have hInfProd :
      (∏ w : InfinitePlace F,
        ‖((τ w (Units.map (algebraMap F w.Completion).toMonoidHom a) : ℂ))‖) = 1 := by
    apply Finset.prod_eq_one
    intro w hw
    exact hinfinite w
  have hFinProd :
      (∏ v ∈ S.Sf.attach,
        ‖((ℓ v (Units.map
          (algebraMap F (v.1.adicCompletion F)).toMonoidHom a) : ℂ))‖) = 1 := by
    apply Finset.prod_eq_one
    intro v hv
    exact hfinite v
  have hInfNorm :
      ‖((∏ w : InfinitePlace F,
        τ w (Units.map (algebraMap F w.Completion).toMonoidHom a) : ℂˣ) : ℂ)‖ = 1 := by
    change ‖Units.coeHom ℂ (∏ w : InfinitePlace F,
      τ w (Units.map (algebraMap F w.Completion).toMonoidHom a))‖ = 1
    rw [map_prod (Units.coeHom ℂ)
      (fun w : InfinitePlace F => τ w (Units.map (algebraMap F w.Completion).toMonoidHom a))
      Finset.univ, norm_prod]
    exact hInfProd
  have hFinNorm :
      ‖((∏ v : S.Sf,
        ℓ v (Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom a) : ℂˣ) : ℂ)‖ = 1 := by
    change ‖Units.coeHom ℂ (∏ v : S.Sf,
      ℓ v (Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom a))‖ = 1
    rw [map_prod (Units.coeHom ℂ)
      (fun v : S.Sf => ℓ v (Units.map
        (algebraMap F (v.1.adicCompletion F)).toMonoidHom a)) Finset.univ, norm_prod]
    exact hFinProd
  rw [hFinNorm, hInfNorm]
  simp

private theorem conductor_idealExp_mul (v : A1.FinPlace F)
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    A1.idealExp v (I * J) = A1.idealExp v I + A1.idealExp v J := by
  unfold A1.idealExp
  rw [← Associates.mk_mul_mk,
    Associates.count_mul (Associates.mk_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hI))
      (Associates.mk_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hJ)) v.associates_irreducible]

private theorem conductor_primitive_ramified_at_factor
    (ω : A1.HeckeChar F) (f : Ideal (𝓞 F)) (hf : IsPrimitiveConductor ω f)
    (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hPf : P ∣ f) :
    ¬ ω.UnramifiedAt ⟨P, hP, hP0⟩ := by
  intro hUnr
  classical
  let v : A1.FinPlace F := ⟨P, hP, hP0⟩
  let g : Ideal (𝓞 F) := (UniqueFactorizationMonoid.normalizedFactors f).erase P |>.prod
  have hfactors : P ∈ UniqueFactorizationMonoid.normalizedFactors f := by
    apply (Ideal.mem_normalizedFactors_iff hf.1).2
    exact ⟨hP, Ideal.dvd_iff_le.mp hPf⟩
  have hdecomp : f = P * g := by
    calc
      f = (UniqueFactorizationMonoid.normalizedFactors f).prod :=
        (Ideal.prod_normalizedFactors_eq_self hf.1).symm
      _ = (P ::ₘ (UniqueFactorizationMonoid.normalizedFactors f).erase P).prod :=
        congrArg Multiset.prod (Multiset.cons_erase hfactors).symm
      _ = P * ((UniqueFactorizationMonoid.normalizedFactors f).erase P).prod :=
        Multiset.prod_cons P _
      _ = P * g := rfl
  have hg : g ≠ ⊥ := by
    intro hg0
    apply hf.1
    rw [hdecomp, hg0]
    simp
  have hcond : ω.ConductorDvd g := by
    intro w u hu huinv hval
    by_cases hw : w = v
    · subst w
      exact hUnr u hu huinv
    · have hPexp : A1.idealExp w P = 0 := by
        have hc : FractionalIdeal.count F w
            (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 :=
          FractionalIdeal.count_maximal_coprime F w (Ne.symm hw)
        have hc' :
            ((Associates.mk w.asIdeal).count (Associates.mk P).factors : ℤ) = 0 := by
          rw [FractionalIdeal.count_coe F w hP0] at hc
          exact hc
        simpa [A1.idealExp, v] using (Int.natCast_eq_zero.mp hc')
      have hexp : A1.idealExp w f = A1.idealExp w g := by
        calc
          A1.idealExp w f = A1.idealExp w (P * g) := by rw [hdecomp]
          _ = A1.idealExp w P + A1.idealExp w g :=
            conductor_idealExp_mul w P g hP0 hg
          _ = A1.idealExp w g := by rw [hPexp]; simp
      apply hf.2.1 w u hu huinv
      simpa [hexp] using hval
  have hlt : Ideal.absNorm g < Ideal.absNorm f := by
    have hnorm : Ideal.absNorm f = Ideal.absNorm P * Ideal.absNorm g := by
      rw [hdecomp, map_mul]
    have hPnorm : 1 < Ideal.absNorm P := by
      simpa [v] using NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hgnorm : 0 < Ideal.absNorm g :=
      Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr (by
        simpa [Ideal.zero_eq_bot] using hg)
    rw [hnorm]
    simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hPnorm hgnorm
  exact False.elim ((not_le_of_gt hlt) (hf.2.2 g hg hcond))

private theorem conductor_unramified_of_idealExp_zero
    (ω : A1.HeckeChar F) (f : Ideal (𝓞 F)) (hcond : ω.ConductorDvd f)
    (v : A1.FinPlace F) (hexp : A1.idealExp v f = 0) : ω.UnramifiedAt v := by
  intro u hu huinv
  apply hcond v u hu huinv
  rw [hexp]
  have hsub : (u : v.adicCompletion F) - 1 ∈ v.adicCompletionIntegers F :=
    (v.adicCompletionIntegers F).sub_mem hu (v.adicCompletionIntegers F).one_mem
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hsub
  simpa using hsub

private abbrev ConductorLocalIntegralUnits :=
  ∀ v : A1.FinPlace F, (v.adicCompletionIntegers F).units

private def conductorIntegralStage (u : ConductorLocalIntegralUnits (F := F)) :
    Πʳ v : A1.FinPlace F,
      [v.adicCompletion F, v.adicCompletionIntegers F]_[⊤] := by
  refine ⟨fun v => ((u v).val : v.adicCompletion F), ?_⟩
  exact Filter.Eventually.of_forall fun v => (u v).property.1

private def conductorIntegralFiniteAdele (u : ConductorLocalIntegralUnits (F := F)) :
    FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.inclusion (𝓕 := Filter.cofinite) (𝓖 := ⊤)
    (R := fun v : A1.FinPlace F => v.adicCompletion F)
    (A := fun v => v.adicCompletionIntegers F) (by simp)
    (conductorIntegralStage u)

private theorem continuous_conductorIntegralFiniteAdele :
    Continuous (conductorIntegralFiniteAdele (F := F)) := by
  apply (RestrictedProduct.continuous_inclusion
    (R := fun v : A1.FinPlace F => v.adicCompletion F)
    (A := fun v => v.adicCompletionIntegers F) (by simp)).comp
  apply (RestrictedProduct.continuous_rng_of_top).2
  change Continuous (fun u : ConductorLocalIntegralUnits (F := F) =>
    fun v : A1.FinPlace F => ((u v).val : v.adicCompletion F))
  exact continuous_pi fun v => by fun_prop

private def conductorIntegralFiniteAdeleUnit
    (u : ConductorLocalIntegralUnits (F := F)) : (FiniteAdeleRing (𝓞 F) F)ˣ where
  val := conductorIntegralFiniteAdele u
  inv := conductorIntegralFiniteAdele fun v => (u v)⁻¹
  val_inv := by
    apply FiniteAdeleRing.ext
    intro v
    change (((u v).val : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      ((((u v).val)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1
    exact congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F))
      (mul_inv_cancel (u v).val)
  inv_val := by
    apply FiniteAdeleRing.ext
    intro v
    change ((((u v).val)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      (((u v).val : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1
    exact congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F))
      (inv_mul_cancel (u v).val)

private theorem continuous_conductorIntegralFiniteAdeleUnit :
    Continuous (conductorIntegralFiniteAdeleUnit (F := F)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_conductorIntegralFiniteAdele (F := F)
  · have hInv : Continuous (fun u : ConductorLocalIntegralUnits (F := F) =>
        conductorIntegralFiniteAdele (fun v => (u v)⁻¹)) :=
      (continuous_conductorIntegralFiniteAdele (F := F)).comp continuous_inv
    simpa [conductorIntegralFiniteAdeleUnit, Units.val_inv_eq_inv_val] using hInv

private def conductorIntegralFiniteAdeleUnitHom :
    ConductorLocalIntegralUnits (F := F) →* (FiniteAdeleRing (𝓞 F) F)ˣ where
  toFun := conductorIntegralFiniteAdeleUnit
  map_one' := by
    apply Units.ext
    apply FiniteAdeleRing.ext
    intro v
    change (((1 : ConductorLocalIntegralUnits (F := F)) v).val :
      v.adicCompletion F) = 1
    simp
  map_mul' u u' := by
    apply Units.ext
    apply FiniteAdeleRing.ext
    intro v
    change (((u v * u' v).val : v.adicCompletion F) =
      ((u v).val : v.adicCompletion F) * ((u' v).val : v.adicCompletion F))
    rfl

private def conductorFiniteAdeleUnitToIdele :
    (FiniteAdeleRing (𝓞 F) F)ˣ →* IdeleGroup (𝓞 F) F :=
  (MulEquiv.prodUnits (M := InfiniteAdeleRing F)
    (N := FiniteAdeleRing (𝓞 F) F)).symm.toMonoidHom.comp
      (MonoidHom.inr (InfiniteAdeleRing F)ˣ (FiniteAdeleRing (𝓞 F) F)ˣ)

private def conductorIntegralUnitIdeleHom :
    ConductorLocalIntegralUnits (F := F) →* IdeleGroup (𝓞 F) F :=
  (conductorFiniteAdeleUnitToIdele (F := F)).comp
    conductorIntegralFiniteAdeleUnitHom

private theorem continuous_conductorFiniteAdeleUnitToIdele :
    Continuous (conductorFiniteAdeleUnitToIdele (F := F)) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun a : (FiniteAdeleRing (𝓞 F) F)ˣ =>
      (1, (a : FiniteAdeleRing (𝓞 F) F)))
    fun_prop
  · change Continuous (fun a : (FiniteAdeleRing (𝓞 F) F)ˣ =>
      (1, ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)))
    fun_prop

private theorem continuous_conductorIntegralUnitIdeleHom :
    Continuous (conductorIntegralUnitIdeleHom (F := F)) := by
  exact (continuous_conductorFiniteAdeleUnitToIdele (F := F)).comp
    (continuous_conductorIntegralFiniteAdeleUnit (F := F))

private def conductorIntegralUnitClassHom :
    ConductorLocalIntegralUnits (F := F) →* NumberField.IdeleClassGroup (𝓞 F) F :=
  (QuotientGroup.mk'
    (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)).comp
    conductorIntegralUnitIdeleHom

private theorem continuous_conductorIntegralUnitClassHom :
    Continuous (conductorIntegralUnitClassHom (F := F)) := by
  exact QuotientGroup.continuous_mk.comp
    (continuous_conductorIntegralUnitIdeleHom (F := F))

private def conductorIntegralUnitCharacter (ω : A1.HeckeChar F) :
    ConductorLocalIntegralUnits (F := F) →* ℂˣ :=
  (ω : NumberField.IdeleClassGroup (𝓞 F) F →* ℂˣ).comp conductorIntegralUnitClassHom

private theorem continuous_conductorIntegralUnitCharacter (ω : A1.HeckeChar F) :
    Continuous (conductorIntegralUnitCharacter (F := F) ω) := by
  exact ω.continuous.comp (continuous_conductorIntegralUnitClassHom (F := F))

private theorem conductorIntegralFiniteAdeleUnitHom_mulSingle
    (v : A1.FinPlace F) (u : (v.adicCompletionIntegers F).units) :
    conductorIntegralFiniteAdeleUnitHom
      (Pi.mulSingle (M := fun w : A1.FinPlace F => (w.adicCompletionIntegers F).units) v u) =
      Units.map (FiniteAdeleRing.ofAdicCompletion F v) u.val := by
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro w
  change ((Pi.mulSingle
      (M := fun z : A1.FinPlace F => (z.adicCompletionIntegers F).units) v u w).val :
        w.adicCompletion F) =
    ((Units.map (FiniteAdeleRing.ofAdicCompletion F v) u.val :
      (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w
  rw [Units.coe_map]
  change ((Pi.mulSingle
      (M := fun z : A1.FinPlace F => (z.adicCompletionIntegers F).units) v u w).val :
        w.adicCompletion F) =
    RestrictedProduct.mulSingle (fun z : A1.FinPlace F => z.adicCompletionIntegers F)
      v (u.val : v.adicCompletion F) w
  by_cases hw : w = v
  · subst w
    simp [Pi.mulSingle, RestrictedProduct.mulSingle_eq_same]
  · simp [hw, Pi.mulSingle, RestrictedProduct.mulSingle_eq_of_ne]

private theorem conductorIntegralUnitIdeleHom_mulSingle
    (v : A1.FinPlace F) (u : (v.adicCompletionIntegers F).units) :
    conductorIntegralUnitIdeleHom
      (Pi.mulSingle (M := fun w : A1.FinPlace F => (w.adicCompletionIntegers F).units) v u) =
      IdeleGroup.ofAdicCompletion (𝓞 F) F v u.val := by
  apply Units.ext
  change (1, ((conductorIntegralFiniteAdeleUnitHom
      (Pi.mulSingle
        (M := fun w : A1.FinPlace F => (w.adicCompletionIntegers F).units) v u) :
      (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) =
    (1, ((Units.map (FiniteAdeleRing.ofAdicCompletion F v) u.val :
      (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
  apply Prod.ext
  · rfl
  · exact congrArg (fun x : (FiniteAdeleRing (𝓞 F) F)ˣ =>
      (x : FiniteAdeleRing (𝓞 F) F))
      (conductorIntegralFiniteAdeleUnitHom_mulSingle v u)

private theorem conductorIntegralUnitCharacter_mulSingle
    (ω : A1.HeckeChar F) (v : A1.FinPlace F)
    (u : (v.adicCompletionIntegers F).units) :
    conductorIntegralUnitCharacter (F := F) ω
      (Pi.mulSingle (M := fun w : A1.FinPlace F => (w.adicCompletionIntegers F).units) v u) =
      ω.loc v u.val := by
  simp only [conductorIntegralUnitCharacter, conductorIntegralUnitClassHom,
    MonoidHom.comp_apply]
  rw [conductorIntegralUnitIdeleHom_mulSingle]
  rfl

private def conductorTailUnitMap (T : Finset (A1.FinPlace F)) :
    ConductorLocalIntegralUnits (F := F) →* ConductorLocalIntegralUnits (F := F) := by
  classical
  refine {
    toFun := fun u v => if v ∈ T then 1 else u v
    map_one' := ?_
    map_mul' := ?_ }
  · funext v
    by_cases hv : v ∈ T <;> simp [hv]
  · intro u u'
    funext v
    by_cases hv : v ∈ T <;> simp [hv]

private theorem continuous_conductorTailUnitMap (T : Finset (A1.FinPlace F)) :
    Continuous (conductorTailUnitMap (F := F) T) := by
  classical
  apply continuous_pi
  intro v
  by_cases hv : v ∈ T
  · simpa [conductorTailUnitMap, hv] using (continuous_const :
      Continuous fun _ : ConductorLocalIntegralUnits (F := F) =>
        (1 : (v.adicCompletionIntegers F).units))
  · simpa [conductorTailUnitMap, hv] using (continuous_apply v :
      Continuous fun u : ConductorLocalIntegralUnits (F := F) => u v)

private def conductorTailUnitCharacter (ω : A1.HeckeChar F)
    (T : Finset (A1.FinPlace F)) :
    ConductorLocalIntegralUnits (F := F) →* ℂˣ :=
  (conductorIntegralUnitCharacter (F := F) ω).comp (conductorTailUnitMap T)

private theorem conductorTailUnitCharacter_eq_one (ω : A1.HeckeChar F)
    (T : Finset (A1.FinPlace F))
    (hlocal : ∀ v : A1.FinPlace F, v ∉ T →
      ∀ u : (v.adicCompletionIntegers F).units, ω.loc v u.val = 1) :
    ∀ u : ConductorLocalIntegralUnits (F := F), conductorTailUnitCharacter ω T u = 1 := by
  classical
  let φ := conductorTailUnitCharacter ω T
  have hφ : Continuous φ :=
    (continuous_conductorIntegralUnitCharacter (F := F) ω).comp
      (continuous_conductorTailUnitMap (F := F) T)
  have hsingle : ∀ v (x : (v.adicCompletionIntegers F).units),
      φ (Pi.mulSingle (M := fun w : A1.FinPlace F =>
        (w.adicCompletionIntegers F).units) v x) = 1 := by
    intro v x
    by_cases hv : v ∈ T
    · have hzero : conductorTailUnitMap (F := F) T
          (Pi.mulSingle (M := fun w : A1.FinPlace F =>
            (w.adicCompletionIntegers F).units) v x) = 1 := by
        ext w
        by_cases hw : w = v
        · subst w
          simp [conductorTailUnitMap, hv]
        · simp [conductorTailUnitMap, hw]
      change conductorIntegralUnitCharacter (F := F) ω
        (conductorTailUnitMap (F := F) T
          (Pi.mulSingle (M := fun w : A1.FinPlace F =>
            (w.adicCompletionIntegers F).units) v x)) = 1
      rw [hzero]
      simp [conductorIntegralUnitCharacter]
    · have hsame : conductorTailUnitMap (F := F) T
          (Pi.mulSingle (M := fun w : A1.FinPlace F =>
            (w.adicCompletionIntegers F).units) v x) =
          Pi.mulSingle (M := fun w : A1.FinPlace F =>
            (w.adicCompletionIntegers F).units) v x := by
        ext w
        by_cases hw : w = v
        · subst w
          simp [conductorTailUnitMap, hv]
        · simp [conductorTailUnitMap, hw]
      change conductorIntegralUnitCharacter (F := F) ω
        (conductorTailUnitMap (F := F) T
          (Pi.mulSingle (M := fun w : A1.FinPlace F =>
            (w.adicCompletionIntegers F).units) v x)) = 1
      rw [hsame, conductorIntegralUnitCharacter_mulSingle]
      exact hlocal v hv x
  have hfs : ∀ u, {v | u v ≠ 1}.Finite → φ u = 1 := by
    intro u hu
    exact piMonoidHom_eq_one_of_support_subset φ hsingle u hu.toFinset
      (fun v hv => hu.mem_toFinset.mpr hv)
  exact continuous_piMonoidHom_eq_one_of_finiteSupport φ hφ hfs

private noncomputable def conductorPrimeSupport (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) : Finset (A1.FinPlace F) :=
  (Ideal.finite_factors (I := I) (by simpa [Ideal.zero_eq_bot] using hI)).toFinset

private theorem mem_conductorPrimeSupport (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : A1.FinPlace F) :
    v ∈ conductorPrimeSupport I hI ↔ v.asIdeal ∣ I := by
  classical
  simp [conductorPrimeSupport]

private theorem conductor_idealExp_zero_of_not_dvd
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (v : A1.FinPlace F)
    (hnot : ¬ v.asIdeal ∣ I) : A1.idealExp v I = 0 := by
  unfold A1.idealExp
  by_contra hne
  have hI' : I ≠ 0 := by simpa [Ideal.zero_eq_bot] using hI
  exact hnot ((Associates.count_ne_zero_iff_dvd hI' v.irreducible).mp hne)

private theorem conductorLocalUnits_trivial_off_support
    (S : A1.SData F CE condη) (ω : A1.HeckeChar F)
    (f : Ideal (𝓞 F)) (hf : IsPrimitiveConductor ω f) :
    ∀ v : A1.FinPlace F,
      v ∉ (S.Sf ∪ conductorPrimeSupport f hf.1) →
      ∀ u : (v.adicCompletionIntegers F).units, ω.loc v u.val = 1 := by
  intro v hv u
  have hvS : v ∉ S.Sf := by
    intro h
    exact hv (Finset.mem_union.mpr (Or.inl h))
  have hvf : v ∉ conductorPrimeSupport f hf.1 := by
    intro h
    exact hv (Finset.mem_union.mpr (Or.inr h))
  have hnot : ¬ v.asIdeal ∣ f := by
    intro hdiv
    exact hvf ((mem_conductorPrimeSupport f hf.1 v).2 hdiv)
  have hexp := conductor_idealExp_zero_of_not_dvd f hf.1 v hnot
  have hunr := conductor_unramified_of_idealExp_zero ω f hf.2.1 v hexp
  exact hunr u.val u.property.1 u.property.2

private theorem conductorHeckeUnitTail_eq_one
    (S : A1.SData F CE condη) (ω : A1.HeckeChar F)
    (f : Ideal (𝓞 F)) (hf : IsPrimitiveConductor ω f) :
    ∀ u : ConductorLocalIntegralUnits (F := F),
      conductorTailUnitCharacter ω (S.Sf ∪ conductorPrimeSupport f hf.1) u = 1 := by
  exact conductorTailUnitCharacter_eq_one ω _
    (conductorLocalUnits_trivial_off_support S ω f hf)

private theorem conductorExteriorExp_eq_f
    (S : A1.SData F CE condη) (J q f : Ideal (𝓞 F))
    (hJ : ConductorSupportedAtS S J) (hq : S.IsExterior q) (hfactor : f = J * q)
    (v : A1.FinPlace F) (hvq : v.asIdeal ∣ q) :
    A1.idealExp v f = A1.idealExp v q := by
  have hvS : v ∉ S.Sf := by
    intro hv
    have hle : q ≤ v.asIdeal := Ideal.dvd_iff_le.mp hvq
    exact hq.2 v hv hle
  have hnotJ : ¬ v.asIdeal ∣ J := by
    intro hdiv
    exact hvS (hJ.2 v hdiv)
  have hJexp := conductor_idealExp_zero_of_not_dvd J hJ.1 v hnotJ
  calc
    A1.idealExp v f = A1.idealExp v (J * q) := by rw [hfactor]
    _ = A1.idealExp v J + A1.idealExp v q :=
      conductor_idealExp_mul v J q hJ.1 hq.1
    _ = A1.idealExp v q := by rw [hJexp]; simp

private theorem conductorExterior_le_prime_power
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (v : A1.FinPlace F) :
    q ≤ v.asIdeal ^ A1.idealExp v q := by
  have hq0 : q ≠ 0 := by simpa [Ideal.zero_eq_bot] using hq
  have hmax : v.maxPowDividing q = v.asIdeal ^ A1.idealExp v q := by
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count v hq0]
    congr 1
    simpa only [A1.idealExp] using
      (Ideal.count_associates_factors_eq hq0 v.isPrime v.ne_bot).symm
  calc
    q = ⨅ w : A1.FinPlace F, w.maxPowDividing q :=
      (Ideal.iInf_maxPowDividing_eq hq0).symm
    _ ≤ v.maxPowDividing q := iInf_le _ v
    _ = v.asIdeal ^ A1.idealExp v q := hmax

private noncomputable def conductorResidueLift
    (S : A1.SData F CE condη) (q : S.ExtIdeal)
    (x : (ConductorResidueRing q)ˣ) : 𝓞 F :=
  Classical.choose (Ideal.Quotient.mk_surjective (x : ConductorResidueRing q))

private theorem conductorResidueLift_spec
    (S : A1.SData F CE condη) (q : S.ExtIdeal)
    (x : (ConductorResidueRing q)ˣ) :
    Ideal.Quotient.mk q.1 (conductorResidueLift S q x) = (x : ConductorResidueRing q) :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (x : ConductorResidueRing q))

private noncomputable def conductorLocalIntegerUnitOfOElement
    (v : A1.FinPlace F) (a : 𝓞 F) (ha0 : a ≠ 0) (ha : a ∉ v.asIdeal) :
    (v.adicCompletionIntegers F).units := by
  have haF : algebraMap (𝓞 F) F a ≠ 0 := by
    intro h
    apply ha0
    exact (IsFractionRing.injective (𝓞 F) F) (by simpa using h)
  let u := A1.toLoc v (Units.mk0 (algebraMap (𝓞 F) F a) haF)
  have hu : Valued.v (u : v.adicCompletion F) = 1 := by
    calc
      Valued.v (u : v.adicCompletion F) =
          v.valuation F (algebraMap (𝓞 F) F a) := by
            change Valued.v (algebraMap F (v.adicCompletion F)
              (algebraMap (𝓞 F) F a)) = _
            exact v.valuedAdicCompletion_eq_valuation' _
      _ = 1 := (v.valuation_eq_one_iff_notMem).2 ha
  exact ⟨u,
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hu⟩

private theorem conductorResidueLift_not_mem_prime
    (S : A1.SData F CE condη) (q : S.ExtIdeal)
    (x : (ConductorResidueRing q)ˣ) (v : A1.FinPlace F)
    (hv : v.asIdeal ∣ q.1) : conductorResidueLift S q x ∉ v.asIdeal := by
  let a := conductorResidueLift S q x
  let b := conductorResidueLift S q x⁻¹
  have hmkA := conductorResidueLift_spec S q x
  have hmkB := conductorResidueLift_spec S q x⁻¹
  have hmod : a * b - 1 ∈ q.1 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hzero : Ideal.Quotient.mk q.1 (a * b - 1) = 0 := by
      simp [a, b, hmkA, hmkB]
    exact hzero
  have hqv : q.1 ≤ v.asIdeal := Ideal.dvd_iff_le.mp hv
  have hmodv : a * b - 1 ∈ v.asIdeal := hqv hmod
  intro ha
  have hab : a * b ∈ v.asIdeal := by
    simpa [mul_comm] using v.asIdeal.mul_mem_left b ha
  have hone : (1 : 𝓞 F) ∈ v.asIdeal := by
    have := v.asIdeal.sub_mem hab hmodv
    simpa [sub_sub_cancel] using this
  exact v.isPrime.ne_top (v.asIdeal.eq_top_iff_one.mpr hone)

private theorem conductorLocalCharacter_eq_of_congruence
    (ω : A1.HeckeChar F) (f q : Ideal (𝓞 F))
    (hcond : ω.ConductorDvd f) (v : A1.FinPlace F) (n : ℕ)
    (hexp : A1.idealExp v f = n) (hpow : q ≤ v.asIdeal ^ n)
    (a b : 𝓞 F) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : a ∉ v.asIdeal) (hb : b ∉ v.asIdeal)
    (hab : a - b ∈ q) :
    ω.loc v (conductorLocalIntegerUnitOfOElement v a ha0 ha).val =
      ω.loc v (conductorLocalIntegerUnitOfOElement v b hb0 hb).val := by
  let ua := conductorLocalIntegerUnitOfOElement v a ha0 ha
  let ub := conductorLocalIntegerUnitOfOElement v b hb0 hb
  let u := ua / ub
  let aF := algebraMap (𝓞 F) F a
  let bF := algebraMap (𝓞 F) F b
  have hpowmem : a - b ∈ v.asIdeal ^ n := hpow hab
  have hdiffVal :
      Valued.v (algebraMap F (v.adicCompletion F) (aF - bF)) ≤
        WithZero.exp (-(n : ℤ)) := by
    have hmap : algebraMap F (v.adicCompletion F) (aF - bF) =
        algebraMap (𝓞 F) (v.adicCompletion F) (a - b) := by
      rw [map_sub]
      rw [← IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) a]
      rw [← IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) b]
      rw [← map_sub]
    calc
      _ = v.valuation F (aF - bF) := v.valuedAdicCompletion_eq_valuation' _
      _ = v.intValuation (a - b) := by
        have hfield : aF - bF = algebraMap (𝓞 F) F (a - b) := by
          simp [aF, bF, map_sub]
        rw [hfield, v.valuation_of_algebraMap]
      _ ≤ WithZero.exp (-(n : ℤ)) :=
        (v.intValuation_le_pow_iff_mem (a - b) n).2 hpowmem
  have hvalBmap : Valued.v (algebraMap F (v.adicCompletion F) bF) = 1 := by
    calc
      _ = v.valuation F bF := v.valuedAdicCompletion_eq_valuation' bF
      _ = 1 := (v.valuation_eq_one_iff_notMem).2 hb
  have hbF : bF ≠ 0 := by
    intro h
    exact hb0 ((IsFractionRing.injective (𝓞 F) F) (by simpa [bF] using h))
  have hbLocal : algebraMap F (v.adicCompletion F) bF ≠ 0 :=
    (map_ne_zero (algebraMap F (v.adicCompletion F))).2 hbF
  have hratio : (u.val : v.adicCompletion F) =
      (algebraMap F (v.adicCompletion F) aF) /
        algebraMap F (v.adicCompletion F) bF := by
    simp [u, ua, ub, conductorLocalIntegerUnitOfOElement, A1.toLoc, aF, bF]
  have hdelta : (u.val : v.adicCompletion F) - 1 =
      algebraMap F (v.adicCompletion F) (aF - bF) /
        algebraMap F (v.adicCompletion F) bF := by
    rw [hratio, map_sub]
    exact div_sub_one hbLocal
  have hbound : Valued.v ((u.val : v.adicCompletion F) - 1) ≤
      WithZero.exp (-(n : ℤ)) := by
    rw [hdelta]
    rw [map_div₀, hvalBmap, div_one]
    exact hdiffVal
  have huInt := (Submonoid.mem_units_iff
      (v.adicCompletionIntegers F).toSubmonoid u.val).mp u.property
  have hram : ω.loc v u.val = 1 := by
    apply hcond v u.val huInt.1 huInt.2
    simpa [hexp] using hbound
  have hquot : ω.loc v ua.val / ω.loc v ub.val = 1 := by
    simpa [u, map_div] using hram
  have hmul :
      (ω.loc v ua.val / ω.loc v ub.val) * ω.loc v ub.val = ω.loc v ua.val := by
    rw [div_mul_cancel]
  calc
    ω.loc v ua.val = (ω.loc v ua.val / ω.loc v ub.val) * ω.loc v ub.val := hmul.symm
    _ = ω.loc v ub.val := by rw [hquot]; simp

private theorem conductorResidueLocalCharacter_exists
    (S : A1.SData F CE condη) (q : S.ExtIdeal)
    (ω : A1.HeckeChar F) (f : Ideal (𝓞 F))
    (hcond : ω.ConductorDvd f) (v : A1.FinPlace F)
    (hv : v.asIdeal ∣ q.1)
    (hexp : A1.idealExp v f = A1.idealExp v q.1) :
    ∃ χ : (ConductorResidueRing q)ˣ →* ℂˣ,
      ∀ (a : 𝓞 F) (ha0 : a ≠ 0) (ha : a ∉ v.asIdeal)
        (x : (ConductorResidueRing q)ˣ),
        Ideal.Quotient.mk q.1 a = (x : ConductorResidueRing q) →
        χ x = ω.loc v
          (conductorLocalIntegerUnitOfOElement v a ha0 ha).val := by
  let lift := conductorResidueLift S q
  have hlift : ∀ x, lift x ∉ v.asIdeal :=
    fun x => conductorResidueLift_not_mem_prime S q x v hv
  have hlift0 : ∀ x, lift x ≠ 0 := by
    intro x h
    exact hlift x (h ▸ v.asIdeal.zero_mem)
  let φ := fun x => ω.loc v
    (conductorLocalIntegerUnitOfOElement v (lift x) (hlift0 x) (hlift x)).val
  have hφ : ∀ (a : 𝓞 F) (ha0 : a ≠ 0) (ha : a ∉ v.asIdeal)
      (x : (ConductorResidueRing q)ˣ),
      Ideal.Quotient.mk q.1 a = (x : ConductorResidueRing q) →
      φ x = ω.loc v (conductorLocalIntegerUnitOfOElement v a ha0 ha).val := by
    intro a ha0 ha x hx
    exact conductorLocalCharacter_eq_of_congruence ω f q.1 hcond v
      (A1.idealExp v q.1) hexp
      (conductorExterior_le_prime_power q.1 q.2.1 v)
      (lift x) a (hlift0 x) ha0 (hlift x) ha
      ((Ideal.Quotient.mk_eq_mk_iff_sub_mem (lift x) a).mp
        ((conductorResidueLift_spec S q x).trans hx.symm))
  have hOne : (1 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    exact v.isPrime.ne_top (v.asIdeal.eq_top_iff_one.mpr h)
  let χ : (ConductorResidueRing q)ˣ →* ℂˣ := {
    toFun := φ
    map_one' := by
      have h := hφ 1 one_ne_zero hOne 1 (by simp)
      simpa [conductorLocalIntegerUnitOfOElement, A1.toLoc] using h
    map_mul' := by
      intro x y
      have hmul0 : lift x * lift y ≠ 0 := mul_ne_zero (hlift0 x) (hlift0 y)
      have hmul : lift x * lift y ∉ v.asIdeal := by
        intro h
        exact (v.isPrime.mem_or_mem h).elim (hlift x) (hlift y)
      have hred : Ideal.Quotient.mk q.1 (lift x * lift y) =
          ((x * y : (ConductorResidueRing q)ˣ) : ConductorResidueRing q) := by
        rw [map_mul, conductorResidueLift_spec S q x,
          conductorResidueLift_spec S q y]
        rfl
      rw [hφ (lift x * lift y) hmul0 hmul (x * y) hred]
      have hlocal :
          (conductorLocalIntegerUnitOfOElement v (lift x * lift y) hmul0 hmul).val =
          (conductorLocalIntegerUnitOfOElement v (lift x) (hlift0 x) (hlift x)).val *
          (conductorLocalIntegerUnitOfOElement v (lift y) (hlift0 y) (hlift y)).val := by
        apply Units.ext
        change algebraMap F (v.adicCompletion F)
            (algebraMap (𝓞 F) F (lift x * lift y)) =
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (lift x)) *
            algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (lift y))
        simp only [map_mul]
      rw [hlocal, map_mul] }
  exact ⟨χ, hφ⟩

private theorem conductorResidueCharacter_exists
    (S : A1.SData F CE condη) (q : S.ExtIdeal)
    (ω : A1.HeckeChar F) (f : Ideal (𝓞 F))
    (hcond : ω.ConductorDvd f)
    (hexp : ∀ v : A1.FinPlace F, v.asIdeal ∣ q.1 →
      A1.idealExp v f = A1.idealExp v q.1) :
    ∃ lambdaq : MulChar (ConductorResidueRing q) ℂ,
      ∀ (a : 𝓞 F) (ha0 : a ≠ 0)
        (ha : ∀ v : A1.FinPlace F, v.asIdeal ∣ q.1 → a ∉ v.asIdeal)
        (x : (ConductorResidueRing q)ˣ),
        Ideal.Quotient.mk q.1 a = (x : ConductorResidueRing q) →
        lambdaq (x : ConductorResidueRing q) =
          (((∏ v : conductorPrimeSupport q.1 q.2.1,
            ω.loc v.1 (conductorLocalIntegerUnitOfOElement v.1 a ha0
              (ha v.1 ((mem_conductorPrimeSupport q.1 q.2.1 v.1).mp v.2))).val)
              : ℂˣ)⁻¹ : ℂ) := by
  classical
  let P := conductorPrimeSupport q.1 q.2.1
  have hlocal : ∀ v : P, ∃ χ : (ConductorResidueRing q)ˣ →* ℂˣ,
      ∀ (a : 𝓞 F) (ha0 : a ≠ 0) (ha : a ∉ v.1.asIdeal)
        (x : (ConductorResidueRing q)ˣ),
        Ideal.Quotient.mk q.1 a = (x : ConductorResidueRing q) →
        χ x = ω.loc v.1
          (conductorLocalIntegerUnitOfOElement v.1 a ha0 ha).val := by
    intro v
    have hv : v.1.asIdeal ∣ q.1 :=
      (mem_conductorPrimeSupport q.1 q.2.1 v.1).mp v.2
    exact conductorResidueLocalCharacter_exists S q ω f hcond v.1 hv (hexp v.1 hv)
  choose χ hχ using hlocal
  let Λ : (ConductorResidueRing q)ˣ →* ℂˣ := (∏ v : P, χ v)⁻¹
  refine ⟨MulChar.ofUnitHom Λ, ?_⟩
  intro a ha0 ha x hx
  rw [MulChar.ofUnitHom_coe]
  have hprod : (∏ v : P, χ v x) =
      ∏ v : P, ω.loc v.1
        (conductorLocalIntegerUnitOfOElement v.1 a ha0
          (ha v.1 ((mem_conductorPrimeSupport q.1 q.2.1 v.1).mp v.2))).val := by
    apply Finset.prod_congr rfl
    intro v hv
    exact hχ v a ha0 (ha v.1
      ((mem_conductorPrimeSupport q.1 q.2.1 v.1).mp v.2)) x hx
  have hprodApply : (∏ v : P, χ v) x = ∏ v : P, χ v x :=
    map_prod (MonoidHom.eval x) χ Finset.univ
  simpa only [Λ, MonoidHom.inv_apply, hprodApply, Units.val_inv_eq_inv_val] using
    congrArg (fun u : ℂˣ => ((u⁻¹ : ℂˣ) : ℂ)) hprod

private theorem conductorIntegralUnitCharacter_eq_prod
    (S : A1.SData F CE condη) (ω : A1.HeckeChar F)
    (f : Ideal (𝓞 F)) (hf : IsPrimitiveConductor ω f)
    (u : ConductorLocalIntegralUnits (F := F)) :
    conductorIntegralUnitCharacter (F := F) ω u =
      ∏ v : {v : A1.FinPlace F // v ∈ S.Sf ∪ conductorPrimeSupport f hf.1},
        ω.loc v.1 (u v.1).val := by
  classical
  let T := S.Sf ∪ conductorPrimeSupport f hf.1
  let head : Finset (A1.FinPlace F) → ConductorLocalIntegralUnits (F := F) :=
    fun A v => if v ∈ A then u v else 1
  have hhead : ∀ A : Finset (A1.FinPlace F),
      conductorIntegralUnitCharacter (F := F) ω (head A) =
        ∏ v ∈ A, ω.loc v (u v).val := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      have heq : head ∅ = 1 := by
        funext v
        simp [head]
      rw [heq, map_one, Finset.prod_empty]
    | @insert v A hv ih =>
      have heq : head (insert v A) = Pi.mulSingle v (u v) * head A := by
        funext w
        by_cases hw : w = v
        · subst w
          simp [head, hv]
        · simp [head, Pi.mulSingle, hw]
      rw [heq, map_mul, conductorIntegralUnitCharacter_mulSingle, ih,
        Finset.prod_insert hv]
  have hsplit : u = head T * conductorTailUnitMap (F := F) T u := by
    funext v
    by_cases hv : v ∈ T <;> simp [head, conductorTailUnitMap, hv]
  have htail : conductorIntegralUnitCharacter (F := F) ω
      (conductorTailUnitMap (F := F) T u) = 1 :=
    conductorHeckeUnitTail_eq_one S ω f hf u
  calc
    conductorIntegralUnitCharacter (F := F) ω u =
        conductorIntegralUnitCharacter (F := F) ω (head T) *
          conductorIntegralUnitCharacter (F := F) ω
            (conductorTailUnitMap (F := F) T u) := by
              exact (congrArg (conductorIntegralUnitCharacter (F := F) ω) hsplit).trans
                (map_mul _ _ _)
    _ = conductorIntegralUnitCharacter (F := F) ω (head T) := by rw [htail, mul_one]
    _ = ∏ v ∈ T, ω.loc v (u v).val := hhead T
    _ = ∏ v : T, ω.loc v.1 (u v.1).val :=
      (Finset.prod_coe_sort T (fun v => ω.loc v (u v).val)).symm

set_option maxHeartbeats 600000 in
private theorem conductorPrincipalFactorization
    (S : A1.SData F CE condη) (ω : A1.HeckeChar F)
    (f : Ideal (𝓞 F)) (hf : IsPrimitiveConductor ω f)
    (a : Fˣ) (B : Finset (A1.FinPlace F))
    (z : ∀ v : B, (v.1.adicCompletion F)ˣ)
    (u : ConductorLocalIntegralUnits (F := F))
    (hfinite : ∀ v : A1.FinPlace F,
      A1.toLoc v a =
        (∏ w : B, Pi.mulSingle
          (M := fun t : A1.FinPlace F => (t.adicCompletion F)ˣ)
          w.1 (z w) v) * (u v).val) :
    (∏ w : InfinitePlace F, ω.locInf w
      (Units.map (algebraMap F w.Completion).toMonoidHom a)) *
      (∏ v : B, ω.loc v.1 (z v)) *
      (∏ v : {v : A1.FinPlace F //
          v ∈ S.Sf ∪ conductorPrimeSupport f hf.1},
        ω.loc v.1 (u v.1).val) = 1 := by
  classical
  let A : IdeleGroup (𝓞 F) F := ∏ w : InfinitePlace F,
    IdeleGroup.ofCompletion (𝓞 F) F w
      (Units.map (algebraMap F w.Completion).toMonoidHom a)
  let Z : IdeleGroup (𝓞 F) F := ∏ v : B,
    IdeleGroup.ofAdicCompletion (𝓞 F) F v.1 (z v)
  let evInf : ∀ w : InfinitePlace F, IdeleGroup (𝓞 F) F →* w.Completion :=
    fun w => {
      toFun := fun g => (g : AdeleRing (𝓞 F) F).1 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let evFin : ∀ v : A1.FinPlace F, IdeleGroup (𝓞 F) F →* v.adicCompletion F :=
    fun v => {
      toFun := fun g => (g : AdeleRing (𝓞 F) F).2 v
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hAInf : ∀ w : InfinitePlace F,
      evInf w A = algebraMap F w.Completion (a : F) := by
    intro w
    dsimp only [A]
    rw [map_prod]
    change (∏ t : InfinitePlace F,
      Pi.mulSingle t (algebraMap F t.Completion (a : F)) w) = _
    exact Fintype.prod_pi_mulSingle w _
  have hAFin : ∀ v : A1.FinPlace F, evFin v A = 1 := by
    intro v
    dsimp only [A]
    rw [map_prod]
    change (∏ _ : InfinitePlace F, (1 : v.adicCompletion F)) = 1
    simp
  have hZInf : ∀ w : InfinitePlace F, evInf w Z = 1 := by
    intro w
    dsimp only [Z]
    rw [map_prod]
    change (∏ _ : B, (1 : w.Completion)) = 1
    simp
  have hZFin : ∀ v : A1.FinPlace F, evFin v Z =
      ((∏ w : B, Pi.mulSingle
        (M := fun t : A1.FinPlace F => (t.adicCompletion F)ˣ)
        w.1 (z w) v : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
    intro v
    dsimp only [Z]
    rw [map_prod]
    change (∏ w : B, evFin v (IdeleGroup.ofAdicCompletion (𝓞 F) F w.1 (z w))) =
      Units.coeHom (v.adicCompletion F) (∏ w : B, Pi.mulSingle
        (M := fun t : A1.FinPlace F => (t.adicCompletion F)ˣ) w.1 (z w) v)
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro w hw
    change RestrictedProduct.mulSingle
        (fun t : A1.FinPlace F => t.adicCompletionIntegers F)
        w.1 (z w : w.1.adicCompletion F) v =
      ((Pi.mulSingle
        (M := fun t : A1.FinPlace F => (t.adicCompletion F)ˣ)
        w.1 (z w) v : (v.adicCompletion F)ˣ) : v.adicCompletion F)
    by_cases hv : v = w.1
    · subst v
      simp [Pi.mulSingle]
    · simp [Pi.mulSingle, hv]
  have hfactor : IdeleGroup.unitEmbedding (𝓞 F) F a =
      A * Z * conductorIntegralUnitIdeleHom (F := F) u := by
    apply Units.ext
    apply Prod.ext
    · funext w
      change evInf w (IdeleGroup.unitEmbedding (𝓞 F) F a) =
        evInf w (A * Z * conductorIntegralUnitIdeleHom (F := F) u)
      rw [map_mul, map_mul, hAInf, hZInf]
      change algebraMap F w.Completion (a : F) =
        algebraMap F w.Completion (a : F) * 1 * 1
      simp
    · apply FiniteAdeleRing.ext
      intro v
      change evFin v (IdeleGroup.unitEmbedding (𝓞 F) F a) =
        evFin v (A * Z * conductorIntegralUnitIdeleHom (F := F) u)
      rw [map_mul, map_mul, hAFin, hZFin]
      change ((A1.toLoc v a : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        (1 : v.adicCompletion F) *
          ((∏ w : B, Pi.mulSingle
            (M := fun t : A1.FinPlace F => (t.adicCompletion F)ˣ)
            w.1 (z w) v : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
          ((u v).val : v.adicCompletion F)
      simpa only [Units.val_mul, one_mul] using
        congrArg (fun x : (v.adicCompletion F)ˣ => (x : v.adicCompletion F)) (hfinite v)
  let φ : IdeleGroup (𝓞 F) F →* ℂˣ :=
    (ω : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp
      (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F))
  have hclass : (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 F) F a) :
      IdeleClassGroup (𝓞 F) F) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have hprincipal : φ (IdeleGroup.unitEmbedding (𝓞 F) F a) = 1 := by
    change ω (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 F) F a)) = 1
    rw [hclass, map_one]
  have hA : φ A = ∏ w : InfinitePlace F, ω.locInf w
      (Units.map (algebraMap F w.Completion).toMonoidHom a) := by
    dsimp only [A]
    rw [map_prod]
    rfl
  have hZ : φ Z = ∏ v : B, ω.loc v.1 (z v) := by
    dsimp only [Z]
    rw [map_prod]
    rfl
  have hU : φ (conductorIntegralUnitIdeleHom (F := F) u) =
      ∏ v : {v : A1.FinPlace F // v ∈ S.Sf ∪ conductorPrimeSupport f hf.1},
        ω.loc v.1 (u v.1).val :=
    conductorIntegralUnitCharacter_eq_prod S ω f hf u
  calc
    _ = φ A * φ Z * φ (conductorIntegralUnitIdeleHom (F := F) u) := by
      rw [hA, hZ, hU]
    _ = φ (A * Z * conductorIntegralUnitIdeleHom (F := F) u) := by
      rw [map_mul, map_mul]
    _ = φ (IdeleGroup.unitEmbedding (𝓞 F) F a) := congrArg φ hfactor.symm
    _ = 1 := hprincipal

private theorem conductorLocalValue_eq_primeValue_pow
    (ω : A1.HeckeChar F) (v : A1.FinPlace F)
    (hunr : ω.UnramifiedAt v) (a : Fˣ) (n : ℕ)
    (hval : v.valuation F (a : F) = WithZero.exp (-(n : ℤ))) :
    ((ω.loc v (A1.toLoc v a) : ℂˣ) : ℂ) = ω.primeValue v ^ n := by
  let α := A1.toLoc v a
  let π : (v.adicCompletion F)ˣ :=
    A1.toLoc v (Units.mk0 (A1.unif v) (A1.unif_ne_zero v))
  have hαval : Valued.v (α : v.adicCompletion F) = WithZero.exp (-(n : ℤ)) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = _
    exact (v.valuedAdicCompletion_eq_valuation' (a : F)).trans hval
  have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (A1.unif v)) = _
    refine (v.valuedAdicCompletion_eq_valuation' (A1.unif v)).trans ?_
    simpa [A1.unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hpow : Valued.v ((π ^ (n : ℤ) : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = Valued.v (α : v.adicCompletion F) := by
    calc
      _ = Valued.v (π : v.adicCompletion F) ^ (n : ℤ) := by simp
      _ = WithZero.exp (-(n : ℤ)) := by
        rw [hπval]
        simpa using (WithZero.exp_zsmul (n : ℤ) (-1 : ℤ)).symm
      _ = Valued.v (α : v.adicCompletion F) := hαval.symm
  have hαnonzero : Valued.v (α : v.adicCompletion F) ≠ 0 := by
    simpa using α.ne_zero
  let u₀ : (v.adicCompletion F)ˣ := α * (π ^ (n : ℤ))⁻¹
  have hu₀val : Valued.v (u₀ : v.adicCompletion F) = 1 := by
    dsimp [u₀]
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hpow]
    exact mul_inv_cancel₀ hαnonzero
  have hu₀int : (u₀ : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hu₀val.le
  have hu₀invint : ((u₀⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      Units.val_inv_eq_inv_val, map_inv₀, hu₀val]
    simp
  have hunit := hunr u₀ hu₀int hu₀invint
  have hdecomp : u₀ * π ^ (n : ℤ) = α := by
    dsimp [u₀]
    group
  have hvalue : ω.loc v α = ω.loc v π ^ (n : ℤ) := by
    calc
      ω.loc v α = ω.loc v (u₀ * π ^ (n : ℤ)) := congrArg (ω.loc v) hdecomp.symm
      _ = ω.loc v u₀ * ω.loc v π ^ (n : ℤ) := by rw [map_mul, map_zpow]
      _ = ω.loc v π ^ (n : ℤ) := by rw [hunit, one_mul]
  change ((ω.loc v α : ℂˣ) : ℂ) = _
  rw [hvalue]
  simp [A1.HeckeChar.primeValue, hunr, π]

private theorem conductorIdealValue_eq_prod_primeValue
    (ω : A1.HeckeChar F) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    ω.idealValue I =
      ∏ v : conductorPrimeSupport I hI, ω.primeValue v.1 ^ A1.idealExp v.1 I := by
  classical
  let factors := UniqueFactorizationMonoid.normalizedFactors I
  let value : Ideal (𝓞 F) → ℂ := fun J =>
    if h : J.IsPrime ∧ J ≠ ⊥ then ω.primeValue ⟨J, h.1, h.2⟩ else 1
  let P := conductorPrimeSupport I hI
  have hI0 : I ≠ 0 := by simpa [Ideal.zero_eq_bot] using hI
  have hfac : ∀ J ∈ factors.toFinset, J.IsPrime ∧ J ≠ ⊥ ∧ J ∣ I := by
    intro J hJ
    have h := (Ideal.mem_normalizedFactors_iff hI).mp (Multiset.mem_toFinset.mp hJ)
    refine ⟨h.1, ?_, Ideal.dvd_iff_le.mpr h.2⟩
    intro hJ0
    exact hI (le_bot_iff.mp (hJ0 ▸ h.2))
  let place : ∀ J : Ideal (𝓞 F), J ∈ factors.toFinset → P := fun J hJ =>
    ⟨⟨J, (hfac J hJ).1, (hfac J hJ).2.1⟩,
      (mem_conductorPrimeSupport I hI _).mpr (hfac J hJ).2.2⟩
  change (factors.map value).prod = ∏ v : P, ω.primeValue v.1 ^ A1.idealExp v.1 I
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_bij place ?_ ?_ ?_ ?_
  · intro J hJ
    exact Finset.mem_univ _
  · intro J hJ K hK h
    exact congrArg (fun v : P => v.1.asIdeal) h
  · intro v hv
    have hdiv : v.1.asIdeal ∣ I := (mem_conductorPrimeSupport I hI v.1).mp v.2
    have hmem : v.1.asIdeal ∈ factors.toFinset :=
      Multiset.mem_toFinset.mpr ((Ideal.mem_normalizedFactors_iff hI).mpr
        ⟨v.1.isPrime, Ideal.dvd_iff_le.mp hdiv⟩)
    refine ⟨v.1.asIdeal, hmem, ?_⟩
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    rfl
  · intro J hJ
    have hp := hfac J hJ
    have hcount : factors.count J = A1.idealExp (place J hJ).1 I :=
      (Ideal.count_associates_factors_eq hI0
        (place J hJ).1.isPrime (place J hJ).1.ne_bot).symm
    dsimp only [value]
    rw [dif_pos ⟨hp.1, hp.2.1⟩]
    change ω.primeValue (place J hJ).1 ^ factors.count J =
      ω.primeValue (place J hJ).1 ^ A1.idealExp (place J hJ).1 I
    rw [hcount]

/-- Minimal finite conductor gives an ideal-primitive residue character on its
exact exterior part. The inverse local factor has the rational-idele orientation,
and equality includes nonunits. Infinite components retain real-place signs.
Guide: sol-thin-a2zf/PROOFS.md:666–693.
Uses ideal_S_exterior_split_count, exact localization, and HK-DICT-RAY. -/
theorem primitive_conductor_residue_bridge (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (ρ : ConductorResidues S)
    (ℓ : SLocalCharacter S) (τ : ConductorInfiniteLocal F)
    (ω : A1.HeckeChar F) (hω : IsOfFinOrder ω)
    (f : Ideal (𝓞 F)) (hf : IsPrimitiveConductor ω f)
    (hℓ : SComponent S ω = ℓ) (hτ : conductorInfiniteComponent ω = τ) :
    (∀ a : Fˣ, ‖conductorLambdaS S ℓ τ a‖ = 1) ∧
    ∃ q : S.ExtIdeal, q.1 = conductorExteriorPart S f ∧
    Ideal.absNorm q.1 ≤ Ideal.absNorm f ∧
      ∃ lambdaq : MulChar (ConductorResidueRing q) ℂ,
        OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals lambdaq ∧
        ConductorResidueRealizes S G ρ ℓ τ q lambdaq ω := by
  constructor
  · exact conductorLambdaS_norm_one_of_components S ℓ τ ω hω hℓ hτ
  · rcases ideal_S_exterior_split_count S with ⟨hsplit, _, _⟩
    rcases hsplit f hf.1 with ⟨_, hqext, _, _, hqNorm, _⟩
    let q : S.ExtIdeal := ⟨conductorExteriorPart S f, hqext⟩
    refine ⟨q, rfl, hqNorm, ?_⟩
    sorry

end ArtinPrimitiveRoots.A2
