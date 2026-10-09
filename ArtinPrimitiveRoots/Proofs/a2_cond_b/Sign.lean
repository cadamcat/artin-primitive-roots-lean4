import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs
import ArtinPrimitiveRoots.A1.Hilbert

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open ArtinPrimitiveRoots.A2
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_cond_b

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

theorem heckeChar_local_value_finite {G : Type*} [Monoid G]
    [TopologicalSpace G]
    (ω : ContinuousMonoidHom G ℂˣ) (hω : IsOfFinOrder ω) (x : G) :
    IsOfFinOrder (ω x) := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hω)
  apply (isOfFinOrder_iff_pow_eq_one).mpr
  refine ⟨n, hn, ?_⟩
  have h := congrArg (fun f : ContinuousMonoidHom G ℂˣ => f x) hpow
  simpa using h

private theorem continuous_ideleClass_ofCompletion (w : InfinitePlace F) :
    Continuous (IdeleClassGroup.ofCompletion (𝓞 F) F w) := by
  have hAdele : Continuous (AdeleRing.ofCompletion (𝓞 F) F w) := by
    unfold AdeleRing.ofCompletion
    refine continuous_prodMk.mpr ⟨?_, continuous_const⟩
    apply continuous_pi
    intro w'
    by_cases hw : w' = w
    · subst w'
      have hfun : (fun x : w.Completion => Pi.mulSingle w x w) = id := by
        funext x
        exact Pi.mulSingle_eq_same w x
      exact hfun ▸ continuous_id
    · change Continuous fun x : w.Completion => Pi.mulSingle w x w'
      have hfun : (fun x : w.Completion => Pi.mulSingle w x w') = fun _ => 1 := by
        funext x
        exact Pi.mulSingle_eq_of_ne hw x
      exact hfun ▸ continuous_const
  have hIdele : Continuous (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w) := by
    change Continuous (Units.map (AdeleRing.ofCompletion (𝓞 F) F w))
    exact Units.continuous_map hAdele
  unfold IdeleClassGroup.ofCompletion
  exact continuous_quotient_mk'.comp hIdele

theorem heckeChar_locInf_continuous (ω : A1.HeckeChar F) (w : InfinitePlace F) :
    Continuous (ω.locInf w) := by
  change Continuous (fun x => ω (IdeleClassGroup.ofCompletion (𝓞 F) F w x))
  exact ω.continuous.comp (continuous_ideleClass_ofCompletion w)

theorem heckeChar_locInf_value_finite (ω : A1.HeckeChar F) (hω : IsOfFinOrder ω)
    (w : InfinitePlace F) (u : w.Completionˣ) : IsOfFinOrder (ω.locInf w u) := by
  exact heckeChar_local_value_finite ω hω (IdeleClassGroup.ofCompletion (𝓞 F) F w u)

private theorem continuous_range_subsingleton_of_pow_eq_one
    {G : Type*} [TopologicalSpace G] [PreconnectedSpace G]
    (f : G → ℂˣ) (hf : Continuous f) {n : ℕ} [NeZero n]
    (hpow : ∀ x, f x ^ n = 1) : ∀ x y, f x = f y := by
  classical
  let root : Set.range f → rootsOfUnity n ℂ := fun z =>
    ⟨z.1, (mem_rootsOfUnity n z.1).2 (by
      rcases z.2 with ⟨x, hx⟩
      simpa [hx] using hpow x)⟩
  have hroot : Function.Injective root := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : rootsOfUnity n ℂ => (z : ℂˣ)) hxy
  letI : Finite (Set.range f) := Finite.of_injective root hroot
  have hfinite : (Set.range f).Finite := Set.toFinite _
  have hpre : IsPreconnected (Set.range f) := isPreconnected_range hf
  have hsub : (Set.range f).Subsingleton := by
    by_contra hsub
    have hnontrivial : (Set.range f).Nontrivial := by
      by_contra hnontrivial
      apply hsub
      intro x hx y hy
      by_contra hxy
      exact hnontrivial ⟨x, hx, y, hy, hxy⟩
    exact hfinite.not_infinite (hpre.infinite_of_nontrivial hnontrivial)
  intro x y
  exact hsub (x := f x) ⟨x, rfl⟩ (y := f y) ⟨y, rfl⟩

private theorem connected_finite_order_monoidHom_trivial
    {G : Type*} [Monoid G] [TopologicalSpace G] [PreconnectedSpace G]
    (f : G →* ℂˣ) (hf : Continuous f) {n : ℕ} [NeZero n]
    (hpow : ∀ x, f x ^ n = 1) : f = 1 := by
  ext x
  have h := continuous_range_subsingleton_of_pow_eq_one f hf hpow x 1
  simpa using h

private theorem positive_real_character_eq_one
    (f : ℝˣ →* ℂˣ) (hf : Continuous f) {n : ℕ} [NeZero n]
    (hpow : ∀ x, f x ^ n = 1) (x : ℝˣ) (hx : 0 < (x : ℝ)) : f x = 1 := by
  letI : PreconnectedSpace (Set.Ioi (0 : ℝ)) :=
    Subtype.preconnectedSpace (isConnected_Ioi (a := (0 : ℝ))).isPreconnected
  let g : Set.Ioi (0 : ℝ) → ℂˣ := fun y => f (Units.mk0 (y : ℝ) y.2.ne')
  have hunit : Continuous fun y : Set.Ioi (0 : ℝ) => Units.mk0 (y : ℝ) y.2.ne' := by
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val
    · have hnonzero : Set.Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := by
        intro y hy
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt hy
      have h := (continuousOn_inv₀ (G₀ := ℝ)).mono hnonzero
      rw [continuousOn_iff_continuous_domRestrict] at h
      change Continuous ((Set.Ioi (0 : ℝ)).domRestrict Inv.inv)
      exact h
  have hg : Continuous g := hf.comp hunit
  have hpowg : ∀ y, g y ^ n = 1 := by
    intro y
    exact hpow (Units.mk0 (y : ℝ) y.2.ne')
  have hconst := continuous_range_subsingleton_of_pow_eq_one g hg hpowg
  have h := hconst ⟨x, hx⟩ ⟨1, by norm_num⟩
  simpa [g] using h

private noncomputable def completionComplexContinuousMulEquiv
    (w : InfinitePlace F) (hw : w.IsComplex) : w.Completion ≃ₜ* ℂ where
  __ := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv
  continuous_toFun :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry_toFun.continuous
  continuous_invFun :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry_toFun.continuous

private noncomputable def completionRealContinuousMulEquiv
    (w : InfinitePlace F) (hw : w.IsReal) : w.Completion ≃ₜ* ℝ where
  __ := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv
  continuous_toFun :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).isometry_toFun.continuous
  continuous_invFun :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry_toFun.continuous

private theorem heckeChar_locInf_pow_eq_one (ω : A1.HeckeChar F) {n : ℕ}
    (hpow : ω ^ n = 1) (w : InfinitePlace F) (u : w.Completionˣ) :
    (ω.locInf w u) ^ n = 1 := by
  have h := congrArg (fun χ : A1.HeckeChar F => χ
      (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) hpow
  simpa [A1.HeckeChar.locInf] using h

private theorem heckeChar_locInf_eq_one_of_isComplex
    (ω : A1.HeckeChar F) (hω : IsOfFinOrder ω) (w : InfinitePlace F)
    (hw : w.IsComplex) : ω.locInf w = 1 := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hω)
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let e := Units.mapContinuousMulEquiv (completionComplexContinuousMulEquiv w hw)
  let f : ℂˣ →* ℂˣ := (ω.locInf w).comp e.symm.toMulEquiv.toMonoidHom
  have hfcont : Continuous f := by
    change Continuous fun z => ω.locInf w (e.symm z)
    exact (heckeChar_locInf_continuous ω w).comp e.symm.continuous
  have hfpow : ∀ z, f z ^ n = 1 := by
    intro z
    change (ω.locInf w (e.symm z)) ^ n = 1
    exact heckeChar_locInf_pow_eq_one ω hpow w (e.symm z)
  have hf := connected_finite_order_monoidHom_trivial f hfcont hfpow
  ext u
  have h := DFunLike.congr_fun hf (e u)
  change ω.locInf w (e.symm (e u)) = 1 at h
  rw [e.symm_apply_apply] at h
  exact congrArg Units.val h

private theorem positive_unit_character_eq_negative_value
    (f : ℝˣ →* ℂˣ) (hf : Continuous f) {n : ℕ} [NeZero n]
    (hpow : ∀ x, f x ^ n = 1) (x : ℝˣ) (hx : (x : ℝ) < 0) :
    f x = f (-1) := by
  have hpos : 0 < ((-x : ℝˣ) : ℝ) := by simpa using neg_pos.mpr hx
  have hfx := positive_real_character_eq_one f hf hpow (-x) hpos
  have hxFact : x = (-1 : ℝˣ) * (-x) := by
    apply Units.ext
    simp
  rw [hxFact, map_mul, hfx, mul_one]

private theorem real_characters_eq_of_negative_value
    (f g : ℝˣ →* ℂˣ) (hf : Continuous f) (hg : Continuous g)
    {n m : ℕ} [NeZero n] [NeZero m]
    (hfPow : ∀ x, f x ^ n = 1) (hgPow : ∀ x, g x ^ m = 1)
    (hneg : f (-1) = g (-1)) : f = g := by
  ext x
  rcases lt_or_gt_of_ne (Units.ne_zero x) with hxneg | hxpos
  · rw [positive_unit_character_eq_negative_value f hf hfPow x hxneg,
      positive_unit_character_eq_negative_value g hg hgPow x hxneg, hneg]
  · rw [positive_real_character_eq_one f hf hfPow x hxpos,
      positive_real_character_eq_one g hg hgPow x hxpos]

private theorem heckeChar_locInf_eq_of_real_neg_value
    (ω ω' : A1.HeckeChar F) (hω : IsOfFinOrder ω) (hω' : IsOfFinOrder ω')
    (w : InfinitePlace F) (hw : w.IsReal)
    (hneg : ω.locInf w (-1) = ω'.locInf w (-1)) : ω.locInf w = ω'.locInf w := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hω)
  obtain ⟨m, hm, hpow'⟩ := (isOfFinOrder_iff_pow_eq_one.mp hω')
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let e := Units.mapContinuousMulEquiv (completionRealContinuousMulEquiv w hw)
  let f : ℝˣ →* ℂˣ := (ω.locInf w).comp e.symm.toMulEquiv.toMonoidHom
  let g : ℝˣ →* ℂˣ := (ω'.locInf w).comp e.symm.toMulEquiv.toMonoidHom
  have hfcont : Continuous f := by
    change Continuous fun x => ω.locInf w (e.symm x)
    exact (heckeChar_locInf_continuous ω w).comp e.symm.continuous
  have hgcont : Continuous g := by
    change Continuous fun x => ω'.locInf w (e.symm x)
    exact (heckeChar_locInf_continuous ω' w).comp e.symm.continuous
  have hfpow : ∀ x, f x ^ n = 1 := by
    intro x
    change (ω.locInf w (e.symm x)) ^ n = 1
    exact heckeChar_locInf_pow_eq_one ω hpow w (e.symm x)
  have hgpw : ∀ x, g x ^ m = 1 := by
    intro x
    change (ω'.locInf w (e.symm x)) ^ m = 1
    exact heckeChar_locInf_pow_eq_one ω' hpow' w (e.symm x)
  have hneg' : f (-1) = g (-1) := by
    have heMapNeg : e (-1 : w.Completionˣ) = (-1 : ℝˣ) := by
      change Units.mapEquiv (completionRealContinuousMulEquiv w hw).toMulEquiv (-1) = -1
      apply Units.ext
      change InfinitePlace.Completion.ringEquivRealOfIsReal hw
        ((-1 : w.Completionˣ) : w.Completion) = (-1 : ℝ)
      simp
    have heNeg : e.symm (-1 : ℝˣ) = (-1 : w.Completionˣ) := by
      calc
        e.symm (-1) = e.symm (e (-1)) := by rw [heMapNeg]
        _ = -1 := e.symm_apply_apply _
    change ω.locInf w (e.symm (-1 : ℝˣ)) = ω'.locInf w (e.symm (-1 : ℝˣ))
    rw [heNeg]
    exact hneg
  have hfg := real_characters_eq_of_negative_value f g hfcont hgcont hfpow hgpw hneg'
  ext u
  have h := DFunLike.congr_fun hfg (e u)
  change ω.locInf w (e.symm (e u)) = ω'.locInf w (e.symm (e u)) at h
  rw [e.symm_apply_apply] at h
  exact congrArg Units.val h

private def conductorInfiniteSign (τ : ConductorInfiniteLocal F) :
    {w : InfinitePlace F // w.IsReal} → Bool := fun w =>
  if τ w.1 (-1 : w.1.Completionˣ) = 1 then true else false

private theorem complexUnit_sq_eq_one (z : ℂˣ) (hz : z ^ 2 = 1) : z = 1 ∨ z = -1 := by
  have hzC : (z : ℂ) ^ 2 = 1 := by simpa using congrArg Units.val hz
  have hfactor : ((z : ℂ) - 1) * ((z : ℂ) + 1) = 0 := by
    calc
      ((z : ℂ) - 1) * ((z : ℂ) + 1) = (z : ℂ) ^ 2 - 1 := by ring
      _ = 0 := by rw [hzC]; ring
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    apply Units.ext
    exact sub_eq_zero.mp h
  · right
    apply Units.ext
    simpa using (eq_neg_of_add_eq_zero_left h : (z : ℂ) = -1)

private theorem conductorInfiniteComponent_eq_of_sign_eq
    (ω ω' : A1.HeckeChar F) (hω : IsOfFinOrder ω) (hω' : IsOfFinOrder ω')
    (hsign : conductorInfiniteSign (conductorInfiniteComponent ω) =
      conductorInfiniteSign (conductorInfiniteComponent ω')) :
    conductorInfiniteComponent ω = conductorInfiniteComponent ω' := by
  funext w
  by_cases hw : w.IsReal
  · have hbits := congrFun hsign ⟨w, hw⟩
    have hbit :
        (if ω.locInf w (-1 : w.Completionˣ) = 1 then true else false) =
          (if ω'.locInf w (-1 : w.Completionˣ) = 1 then true else false) := by
      change (if ω.locInf w (-1 : w.Completionˣ) = 1 then true else false) =
        (if ω'.locInf w (-1 : w.Completionˣ) = 1 then true else false) at hbits
      exact hbits
    have hsq : (ω.locInf w (-1 : w.Completionˣ)) ^ 2 = 1 := by
      simpa using ((ω.locInf w).map_pow (-1 : w.Completionˣ) 2).symm
    have hsq' : (ω'.locInf w (-1 : w.Completionˣ)) ^ 2 = 1 := by
      simpa using ((ω'.locInf w).map_pow (-1 : w.Completionˣ) 2).symm
    by_cases hneg : ω.locInf w (-1 : w.Completionˣ) = 1
    · have hneg' : ω'.locInf w (-1 : w.Completionˣ) = 1 := by
        by_contra hneg'
        have : true = false := by simpa [hneg, hneg'] using hbit
        cases this
      exact heckeChar_locInf_eq_of_real_neg_value ω ω' hω hω' w hw (hneg.trans hneg'.symm)
    · by_cases hneg' : ω'.locInf w (-1 : w.Completionˣ) = 1
      · have : false = true := by simpa [hneg, hneg'] using hbit
        cases this
      · have hroot := complexUnit_sq_eq_one _ hsq
        have hroot' := complexUnit_sq_eq_one _ hsq'
        have heq : ω.locInf w (-1 : w.Completionˣ) =
            ω'.locInf w (-1 : w.Completionˣ) := by
          rcases hroot with hroot | hroot
          · exact (hneg hroot).elim
          · rcases hroot' with hroot' | hroot'
            · exact (hneg' hroot').elim
            · rw [hroot, hroot']
        exact heckeChar_locInf_eq_of_real_neg_value ω ω' hω hω' w hw heq
  · have hwC : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    calc
      ω.locInf w = 1 := heckeChar_locInf_eq_one_of_isComplex ω hω w hwC
      _ = ω'.locInf w := (heckeChar_locInf_eq_one_of_isComplex ω' hω' w hwC).symm

theorem conductorInfiniteComponent_card_le (𝓧 : Finset (A1.HeckeChar F))
    (h𝓧 : ∀ ω ∈ 𝓧, IsOfFinOrder ω) :
    (𝓧.image conductorInfiniteComponent).card ≤
      2 ^ NumberField.InfinitePlace.nrRealPlaces F := by
  classical
  let τ : A1.HeckeChar F → ConductorInfiniteLocal F := conductorInfiniteComponent
  let sign : ConductorInfiniteLocal F → {w : InfinitePlace F // w.IsReal} → Bool :=
    conductorInfiniteSign
  have hcard : (𝓧.image τ).card ≤
      Fintype.card ({w : InfinitePlace F // w.IsReal} → Bool) := by
    refine Finset.card_le_card_of_injOn sign (s := 𝓧.image τ) (t := Finset.univ)
      (by simp) ?_
    intro t ht t' ht' hsign
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨ω', hω', rfl⟩ := Finset.mem_image.mp ht'
    exact conductorInfiniteComponent_eq_of_sign_eq ω ω' (h𝓧 ω hω) (h𝓧 ω' hω') hsign
  simpa [Fintype.card_fun, NumberField.InfinitePlace.nrRealPlaces] using hcard

private theorem conductorSupported_normalizedFactor_index
    (S : A1.SData F CE condη) {J P : Ideal (𝓞 F)}
    (hJ : ConductorSupportedAtS S J)
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors J) :
    ∃ v : S.Sf, P = v.1.asIdeal := by
  have hPprime : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let v : HeightOneSpectrum (𝓞 F) := HeightOneSpectrum.ofPrime hPprime
  have hPle : J ≤ P := (Ideal.mem_normalizedFactors_iff hJ.1).mp hP |>.2
  have hvdiv : v.asIdeal ∣ J := Ideal.dvd_iff_le.mpr (by simpa [v] using hPle)
  exact ⟨⟨v, hJ.2 v hvdiv⟩, by simp [v]⟩

private theorem heckePrimeValue_eq_of_loc_eq (ω ω' : A1.HeckeChar F)
    (v : A1.FinPlace F) (hloc : ω.loc v = ω'.loc v) :
    ω.primeValue v = ω'.primeValue v := by
  have hUnram : ω.UnramifiedAt v ↔ ω'.UnramifiedAt v := by
    unfold A1.HeckeChar.UnramifiedAt
    simp [hloc]
  by_cases hu : ω.UnramifiedAt v
  · have hu' : ω'.UnramifiedAt v := hUnram.mp hu
    simp [A1.HeckeChar.primeValue, hu, hu', hloc]
  · have hu' : ¬ω'.UnramifiedAt v := fun h => hu (hUnram.mpr h)
    simp [A1.HeckeChar.primeValue, hu, hu', hloc]

private theorem heckePrimeValue_norm_le_one (ω : A1.HeckeChar F)
    (hω : IsOfFinOrder ω) (v : A1.FinPlace F) : ‖ω.primeValue v‖ ≤ 1 := by
  by_cases hu : ω.UnramifiedAt v
  · let u := A1.toLoc v (Units.mk0 (A1.unif v) (A1.unif_ne_zero v))
    have hfinite : IsOfFinOrder (ω.loc v u) :=
      heckeChar_local_value_finite ω hω
        (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)
    have hfiniteC : IsOfFinOrder ((ω.loc v u : ℂˣ) : ℂ) :=
      (Units.coeHom ℂ).isOfFinOrder hfinite
    have hnorm : ‖((ω.loc v u : ℂˣ) : ℂ)‖ = 1 := by
      exact hfiniteC.norm_eq_one
    simpa [A1.HeckeChar.primeValue, hu, u] using (show
      ‖((ω.loc v u : ℂˣ) : ℂ)‖ ≤ 1 by rw [hnorm])
  · simp [A1.HeckeChar.primeValue, hu]

private theorem norm_multiset_map_prod_le_one {α : Type*} (s : Multiset α)
    (f : α → ℂ) (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      have ha := hf a (by simp)
      have hs : ∀ x, x ∈ s → ‖f x‖ ≤ 1 := fun x hx => hf x (by simp [hx])
      calc
        ‖f a‖ * ‖(s.map f).prod‖ ≤ 1 * 1 :=
          mul_le_mul ha (ih hs) (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num

theorem conductorSupported_idealValue_eq_and_norm (S : A1.SData F CE condη)
    (ω ω' : A1.HeckeChar F) (hω : IsOfFinOrder ω) (hω' : IsOfFinOrder ω')
    (hS : SComponent S ω = SComponent S ω')
    {J : Ideal (𝓞 F)} (hJ : ConductorSupportedAtS S J) :
    ω.idealValue J = ω'.idealValue J ∧ ‖ω.idealValue J‖ ≤ 1 := by
  classical
  constructor
  · unfold A1.HeckeChar.idealValue
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro P hP
    obtain ⟨v, hvP⟩ := conductorSupported_normalizedFactor_index S hJ hP
    have hvloc : ω.loc v.1 = ω'.loc v.1 := congrFun hS v
    have hprime := heckePrimeValue_eq_of_loc_eq ω ω' v.1 hvloc
    have hPprime : P.IsPrime ∧ P ≠ ⊥ := by
      exact ⟨Ideal.isPrime_of_prime
        (UniqueFactorizationMonoid.prime_of_normalized_factor P hP),
        (UniqueFactorizationMonoid.prime_of_normalized_factor P hP).ne_zero⟩
    have hright : v.1.asIdeal.IsPrime ∧ v.1.asIdeal ≠ ⊥ :=
      ⟨v.1.isPrime, v.1.ne_bot⟩
    have hidx : (⟨P, hPprime.1, hPprime.2⟩ : A1.FinPlace F) = v.1 :=
      HeightOneSpectrum.ext hvP
    simpa [hPprime, hright, hidx] using hprime
  · unfold A1.HeckeChar.idealValue
    apply norm_multiset_map_prod_le_one
    intro P hP
    by_cases hPprime : P.IsPrime ∧ P ≠ ⊥
    · obtain ⟨v, hvP⟩ := conductorSupported_normalizedFactor_index S hJ hP
      have hnorm := heckePrimeValue_norm_le_one ω hω v.1
      have hright : v.1.asIdeal.IsPrime ∧ v.1.asIdeal ≠ ⊥ :=
        ⟨v.1.isPrime, v.1.ne_bot⟩
      have hidx : (⟨P, hPprime.1, hPprime.2⟩ : A1.FinPlace F) = v.1 :=
        HeightOneSpectrum.ext hvP
      simpa [hPprime, hright, hidx] using hnorm
    · simp [hPprime]

end ArtinPrimitiveRoots.Proofs.a2_cond_b
