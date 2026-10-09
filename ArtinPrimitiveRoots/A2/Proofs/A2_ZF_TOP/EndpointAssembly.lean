import ArtinPrimitiveRoots.A2.Coherence
import ArtinPrimitiveRoots.A2.Proofs.A2_ZF_TOP.SelfDualMeasure
import ArtinPrimitiveRoots.A1.AddCharExists
import ArtinPrimitiveRoots.Hecke.Dictionary
import ArtinPrimitiveRoots.Hecke.Theta.IdealNormSummability
import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNDict
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayPrincipalIdealSubgroup

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain MeasureTheory ClassFieldTheory
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2 ArtinPrimitiveRoots.Hecke
open ArtinPrimitiveRoots.A1.Theta
open scoped Classical nonZeroDivisors
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_zf_top

structure EndpointAssemblyData (n : ℕ) [NeZero n] (h12 : 12 ∣ n)
    (m : RayClassModulus (CyclotomicField n ℚ))
    (η : RayClassGroup m →* ℂˣ) where
  CE : ℕ
  D : FieldData (CyclotomicField n ℚ)
  S : SData (CyclotomicField n ℚ) CE (modulusIdeal m)
  H : HilbertData (CyclotomicField n ℚ)
  Bd : BData S H
  bc : BalancedChoices D S H Bd
  A : AddCharData (CyclotomicField n ℚ)
  v0 : InfinitePlace (CyclotomicField n ℚ)
  μ : ∀ v : FinPlace (CyclotomicField n ℚ), LocHaar v
  χ : HeckeChar (CyclotomicField n ℚ)
  χ_finite : IsOfFinOrder χ
  χ_conductor : χ.ConductorDvd (modulusIdeal m)
  χ_prime : ∀ v, v ∉ m.finitePart.support →
    χ.UnramifiedAt v ∧ χ.primeValue v = charValue η v.asIdeal
  modulusSupport_subset : m.finitePart.support ⊆ S.Sf
  χ_unramified : ∀ v, v ∉ S.Sf → χ.UnramifiedAt v
  Λ : HeckeChar (CyclotomicField n ℚ)
  G : HeckeChar (CyclotomicField n ℚ)
  G_finite : IsOfFinOrder G
  Λ_unitary : ∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1
  Λ_angular : HeckeChar.HasAngularType D Λ
  gauss : ∀ v, v ∉ S.Sf → ∀ p : (CyclotomicField n ℚ)ˣ,
    S.IsGen (p : CyclotomicField n ℚ) v.asIdeal → Bd.Allowed p →
      gamma D S A 1 v.asIdeal (p : CyclotomicField n ℚ) *
        gamma D S A 2 v.asIdeal (p : CyclotomicField n ℚ) =
          -(Λ.primeValue v * G.primeValue v)
  R : ReflectionSetup D S H Bd A (vartheta Λ G χ) bc μ v0
  U : FrequencyData S D χ
  HA : HeckeAnalysis (CyclotomicField n ℚ)
  HC : EulerCorrection R χ U
  sd : S.SelfDualMeasure A
  W : PoissonWeights (S := S)
  split : GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A)
    (ϑ := vartheta Λ G χ) χ
  euler : EulerHypotheses R χ
  localSmall : ∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R χ U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2
  weightSpec : WeightSpec R sd W
  inputs : MellinInputs (Heta R χ U HC) (HA.LS S χ)

end ArtinPrimitiveRoots.Proofs.a2_zf_top

namespace ArtinPrimitiveRoots.Proofs.a2_zf_top

private theorem balancedChoices_nonempty
    {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) : Nonempty (BalancedChoices D S H Bd) := by
  classical
  obtain ⟨K, hK, hKn, hgen⟩ := BData.exists_balanced D Bd
  let gen : S.ExtIdeal → Fˣ := fun I => Classical.choose (hgen I.1 I.2)
  have hgenSpec (I : S.ExtIdeal) :
      S.IsGen (gen I : F) I.1 ∧ Bd.Allowed (gen I) ∧
        S.diag (gen I : F) * S.ell D (idealNorm I.1)⁻¹ (by
          have hnorm : 0 < Ideal.absNorm I.1 :=
            Ideal.absNorm_pos_of_nonZeroDivisors
              ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr
                (by simpa [Ideal.zero_eq_bot] using I.2.1)⟩
          have hnormR : 0 < (Ideal.absNorm I.1 : ℝ) := by exact_mod_cast hnorm
          exact inv_pos.mpr (by simpa [idealNorm] using hnormR)) ∈ K := by
    have hspec := Classical.choose_spec (hgen I.1 I.2)
    exact ⟨hspec.1, hspec.2.1, by simpa [idealNorm] using hspec.2.2⟩
  exact ⟨{
    Kbal := K
    Kbal_compact := hK
    Kbal_normOne := hKn
    gen := gen
    gen_spec := fun I => ⟨(hgenSpec I).1, (hgenSpec I).2.1⟩
    gen_balanced := fun I => (hgenSpec I).2.2 }⟩

theorem endpointAssemblyData_nonempty
    (n : ℕ) [NeZero n] (h12 : 12 ∣ n)
    (m : RayClassModulus (CyclotomicField n ℚ))
    (η : RayClassGroup m →* ℂˣ) :
    Nonempty (EndpointAssemblyData n h12 m η) := by
  classical
  obtain ⟨C, Q0, hC, hQ0, hAbsolute⟩ := po_H_local_bounds_absolute
  obtain ⟨Q1, hQ01, hQdecay⟩ := po_H_cutoff_from_constants C Q0
  let v0 : InfinitePlace (CyclotomicField n ℚ) := Classical.choice inferInstance
  let D : FieldData (CyclotomicField n ℚ) := cyclotomicFieldData n h12 v0.embedding
  let cond : Ideal (𝓞 (CyclotomicField n ℚ)) := modulusIdeal m
  have hcond : cond ≠ ⊥ := by exact modulusIdeal_ne_bot m
  let S : SData (CyclotomicField n ℚ) Q1 cond :=
    Classical.choice (SData.nonempty Q1 cond hcond)
  let H : HilbertData (CyclotomicField n ℚ) := Classical.choice (HilbertData.nonempty D)
  let Bd : BData S H := Classical.choice (BData.nonempty D S H)
  let bc : BalancedChoices D S H Bd := Classical.choice (balancedChoices_nonempty D S H Bd)
  let A : AddCharData (CyclotomicField n ℚ) := Classical.choice (AddCharData.nonempty D)
  obtain ⟨χ, hχfinite, hχcond, hχprime⟩ :=
    ArtinPrimitiveRoots.Dictionary.exists_heckeChar_of_rayClass m η
  have hModSupport : m.finitePart.support ⊆ S.Sf := by
    intro v hv
    have hpow : modulusIdeal m ≤ v.asIdeal ^ m.finitePart v := by
      change (∏ w ∈ m.finitePart.support, w.asIdeal ^ m.finitePart w) ≤ _
      exact (Ideal.prod_le_inf (s := m.finitePart.support)
        (f := fun w => w.asIdeal ^ m.finitePart w)).trans (Finset.inf_le hv)
    have hpos : 0 < m.finitePart v :=
      Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
    have hvdiv : modulusIdeal m ≤ v.asIdeal :=
      hpow.trans (Ideal.pow_le_self (Nat.ne_of_gt hpos))
    exact S.cond_mem v (by simpa [cond] using hvdiv)
  have hχunram : ∀ v : FinPlace (CyclotomicField n ℚ), v ∉ S.Sf → χ.UnramifiedAt v := by
    intro v hvS
    have hvmod : v ∉ m.finitePart.support := fun h => hvS (hModSupport h)
    exact (hχprime v hvmod).1
  obtain ⟨Λ, G, hGfinite, hΛunit, hΛangular, hθB, hGaussData⟩ :=
    ArtinPrimitiveRoots.A1.gauss_characters D S A H Bd
  have hΛunram : ∀ v : FinPlace (CyclotomicField n ℚ), v ∉ S.Sf → Λ.UnramifiedAt v := by
    intro v hv
    exact (hGaussData v hv).1
  have hGunram : ∀ v : FinPlace (CyclotomicField n ℚ), v ∉ S.Sf → G.UnramifiedAt v := by
    intro v hv
    exact (hGaussData v hv).2.1
  have hGauss : ∀ v : FinPlace (CyclotomicField n ℚ), v ∉ S.Sf →
      ∀ p : (CyclotomicField n ℚ)ˣ, S.IsGen (p : CyclotomicField n ℚ) v.asIdeal →
        Bd.Allowed p →
        gamma D S A 1 v.asIdeal (p : CyclotomicField n ℚ) *
          gamma D S A 2 v.asIdeal (p : CyclotomicField n ℚ) =
            -(Λ.primeValue v * G.primeValue v) := by
    intro v hv p hpgen hpAllowed
    exact ((hGaussData v hv).2.2 p hpgen hpAllowed).2.2
  have hGaussFull : ∀ v : FinPlace (CyclotomicField n ℚ), v ∉ S.Sf →
      Λ.UnramifiedAt v ∧ G.UnramifiedAt v ∧
        ∀ p : (CyclotomicField n ℚ)ˣ, S.IsGen (p : CyclotomicField n ℚ) v.asIdeal →
          Bd.Allowed p →
            gamma D S A 1 v.asIdeal (p : CyclotomicField n ℚ) *
              gamma D S A 2 v.asIdeal (p : CyclotomicField n ℚ) =
                -(Λ.primeValue v * G.primeValue v) := by
    intro v hv
    exact ⟨hΛunram v hv, hGunram v hv, fun p hpgen hpAllowed =>
      hGauss v hv p hpgen hpAllowed⟩
  have hVartheta := ArtinPrimitiveRoots.A1.vartheta_S D S A H Bd χ Λ G
    hχunram hΛunram hGunram hχfinite hGfinite hΛunit hΛangular hGauss
  obtain ⟨R⟩ := ArtinPrimitiveRoots.A2.reflectionSetup_exists D S H Bd A bc
    (fun v => Classical.choice (LocHaar.nonempty v)) v0 χ Λ G hχfinite hχunram
      hΛunit hΛangular hGfinite hGaussFull
  let μ : ∀ v : FinPlace (CyclotomicField n ℚ), LocHaar v :=
    fun v => Classical.choice (LocHaar.nonempty v)
  let U : FrequencyData S D χ :=
    Classical.choice (FrequencyData.nonempty S D χ hχfinite)
  haveI : IsTotallyComplex (CyclotomicField n ℚ) := D.isTotallyComplex
  let HA : HeckeAnalysis (CyclotomicField n ℚ) :=
    Classical.choice (ArtinPrimitiveRoots.A2.heckeAnalysis_exists _)
  let HC : EulerCorrection R χ U := canonicalEulerCorrection R χ U
  let sd : S.SelfDualMeasure A := Classical.choice
    (sDataSelfDualMeasure_exists D S A μ)
  obtain ⟨W, hWeightSpec⟩ := (po_weights_exist R sd).1
  have hEuler : EulerHypotheses R χ := by
    refine ⟨hχfinite, hχunram, ?_⟩
    intro v hv
    let I : S.ExtIdeal := R.exterior.prime v hv
    have hI : I.1 = v.asIdeal := R.exterior.prime_val v hv
    have hgen := bc.gen_spec I
    have hgen' : S.IsGen (bc.gen I : CyclotomicField n ℚ) v.asIdeal := by
      rw [← hI]
      exact hgen.1
    have hp : primeGen R v = bc.gen I := by simp [primeGen, hv, I]
    simpa [hp] using hVartheta.2.2.2 v hv (bc.gen I) hgen' hgen.2
  have hBound := hAbsolute (CyclotomicField n ℚ) Q1 cond D S H Bd A
    (vartheta Λ G χ) bc μ v0 R χ U hEuler
  have hLocalSmall := ArtinPrimitiveRoots.A2.po_H_principal_cutoff R χ U C Q0 Q1
    hEuler hBound hQ01 (Nat.le_refl Q1) hQdecay
  let split : GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A)
      (ϑ := vartheta Λ G χ) χ := gaussSplit_of_data χ Λ G hχfinite hχunram
        hΛunit hΛangular hGfinite hGaussFull
  have hInputs := principal_mellin_inputs R sd W χ U HA HC
    split hEuler hLocalSmall hWeightSpec
  exact ⟨{
    CE := Q1
    D := D
    S := S
    H := H
    Bd := Bd
    bc := bc
    A := A
    v0 := v0
    μ := μ
    χ := χ
    χ_finite := hχfinite
    χ_conductor := hχcond
    χ_prime := hχprime
    modulusSupport_subset := hModSupport
    χ_unramified := hχunram
    Λ := Λ
    G := G
    G_finite := hGfinite
    Λ_unitary := hΛunit
    Λ_angular := hΛangular
    gauss := hGauss
    R := R
    U := U
    HA := HA
    HC := HC
    sd := sd
    W := W
    split := split
    euler := hEuler
    localSmall := hLocalSmall
    weightSpec := hWeightSpec
    inputs := hInputs }⟩

private noncomputable def enlargedModulus
    {n : ℕ} [NeZero n] {h12 : 12 ∣ n}
    {m : RayClassModulus (CyclotomicField n ℚ)}
    {η : RayClassGroup m →* ℂˣ}
    (d : EndpointAssemblyData n h12 m η) :
    RayClassModulus (CyclotomicField n ℚ) := {
  finitePart := Finsupp.onFinset d.S.Sf
    (fun v => if v ∈ d.S.Sf then m.finitePart v + 1 else 0) (by
      intro v hv
      by_contra hnot
      simp [hnot] at hv)
  infinitePart := m.infinitePart
}

private theorem enlargedModulus_support
    {n : ℕ} [NeZero n] {h12 : 12 ∣ n}
    {m : RayClassModulus (CyclotomicField n ℚ)}
    {η : RayClassGroup m →* ℂˣ}
    (d : EndpointAssemblyData n h12 m η) :
    (enlargedModulus d).finitePart.support = d.S.Sf := by
  classical
  ext v
  simp [enlargedModulus, Finsupp.support_onFinset]

private theorem modulus_le_enlarged
    {n : ℕ} [NeZero n] {h12 : 12 ∣ n}
    {m : RayClassModulus (CyclotomicField n ℚ)}
    {η : RayClassGroup m →* ℂˣ}
    (d : EndpointAssemblyData n h12 m η) : m ≤ enlargedModulus d := by
  refine ⟨?_, fun v hv => hv⟩
  intro v
  by_cases hv : v ∈ d.S.Sf
  · simp [enlargedModulus, hv]
  · have hnot : v ∉ m.finitePart.support := by
      intro h
      exact hv (d.modulusSupport_subset h)
    have hzero : m.finitePart v = 0 := Finsupp.notMem_support_iff.mp hnot
    simp [enlargedModulus, hv, hzero]

private def rayLocalIntegralValue_local
    {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (y : (v.adicCompletionIntegers F).units) :
    v.adicCompletionIntegers F :=
  ((v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType y :
    (v.adicCompletionIntegers F)ˣ).1

private theorem rayLocalHigherUnitMap_eq_one_iff_local
    {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℕ) (y : (v.adicCompletionIntegers F).units) :
    ClassFieldTheory.rayLocalHigherUnitMap v k y = 1 ↔
      rayLocalIntegralValue_local v y - 1 ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ k := by
  let I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ k
  change Units.map (Ideal.Quotient.mk I).toMonoidHom
      ((v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType y) = 1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk I (rayLocalIntegralValue_local v y) =
      Ideal.Quotient.mk I 1 ↔ _
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I)
    (rayLocalIntegralValue_local v y) (1 : v.adicCompletionIntegers F)

private theorem rayLocalHigherUnitGroup_antitone_local
    {F : Type} [Field F] [NumberField F] (v : FinPlace F)
    {k l : ℕ} (hkl : k ≤ l) :
    ClassFieldTheory.rayLocalHigherUnitGroup v l ≤
      ClassFieldTheory.rayLocalHigherUnitGroup v k := by
  intro x hx
  change x ∈ Subgroup.map (v.adicCompletionIntegers F).units.subtype
    (ClassFieldTheory.rayLocalHigherUnitMap v l).ker at hx
  change x ∈ Subgroup.map (v.adicCompletionIntegers F).units.subtype
    (ClassFieldTheory.rayLocalHigherUnitMap v k).ker
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, ?_, rfl⟩
  change ClassFieldTheory.rayLocalHigherUnitMap v l y = 1 at hy
  change ClassFieldTheory.rayLocalHigherUnitMap v k y = 1
  rw [rayLocalHigherUnitMap_eq_one_iff_local] at hy ⊢
  exact Ideal.pow_le_pow_right hkl hy

private theorem rayCongruent_le_local
    {F : Type} [Field F] [NumberField F]
    {m n : RayClassModulus F} (hmn : m ≤ n) {x : Fˣ}
    (hx : ClassFieldTheory.IsRayCongruent n x) :
    ClassFieldTheory.IsRayCongruent m x := by
  constructor
  · intro v hv
    have hvn : v ∈ n.finitePart.support := by
      apply Finsupp.mem_support_iff.mpr
      have hpos : 0 < m.finitePart v :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
      exact Nat.ne_of_gt (lt_of_lt_of_le hpos (hmn.1 v))
    exact rayLocalHigherUnitGroup_antitone_local v (hmn.1 v) (hx.1 v hvn)
  · intro v hv
    exact hx.2 v (hmn.2 hv)

private theorem rayPrincipalIdeals_antitone_local
    {F : Type} [Field F] [NumberField F]
    {m n : RayClassModulus F} (hmn : m ≤ n) :
    rayPrincipalIdealSubgroup n ≤ rayPrincipalIdealSubgroup m := by
  apply Subgroup.closure_mono
  rintro I ⟨x, hx, hIx⟩
  exact ⟨x, rayCongruent_le_local hmn hx, hIx⟩

private noncomputable def rayClassProjection_local
    {F : Type} [Field F] [NumberField F]
    {m n : RayClassModulus F} (hmn : m ≤ n) : RayClassGroup n →* RayClassGroup m := by
  let hI : rayClassPrimeToIdeals n ≤ rayClassPrimeToIdeals m := by
    intro I hI v hv
    exact hI v (Finsupp.support_mono hmn.1 hv)
  letI : (rayPrincipalIdealSubgroupInPrimeTo m).Normal :=
    Subgroup.normal_of_isMulCommutative _
  refine QuotientGroup.map (rayPrincipalIdealSubgroupInPrimeTo n)
    (rayPrincipalIdealSubgroupInPrimeTo m) (Subgroup.inclusion hI) ?_
  intro I hI'
  change (I : NumberFieldFractionalIdealGroup F) ∈ rayPrincipalIdealSubgroup n at hI'
  change (I : NumberFieldFractionalIdealGroup F) ∈ rayPrincipalIdealSubgroup m
  exact rayPrincipalIdeals_antitone_local hmn hI'

private noncomputable def liftedRayChar
    {n : ℕ} [NeZero n] {h12 : 12 ∣ n}
    {m : RayClassModulus (CyclotomicField n ℚ)}
    {η : RayClassGroup m →* ℂˣ}
    (d : EndpointAssemblyData n h12 m η) :
    RayClassGroup (enlargedModulus d) →* ℂˣ :=
  η.comp (rayClassProjection_local (modulus_le_enlarged d))

private noncomputable def finiteRayFactor
    {n : ℕ} [NeZero n] {h12 : 12 ∣ n}
    {m : RayClassModulus (CyclotomicField n ℚ)}
    {η : RayClassGroup m →* ℂˣ}
    (d : EndpointAssemblyData n h12 m η) (s : ℂ) : ℂ :=
  ∏ v ∈ d.S.Sf \ m.finitePart.support,
    (1 - d.χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))

private theorem heckeChar_value_norm_one
    {F : Type} [Field F] [NumberField F] (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) (x : IdeleClassGroup (𝓞 F) F) :
    ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨k, hk, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hχ)
  have hpowx : (χ x : ℂˣ) ^ k = 1 := by
    have h := congrArg (fun f : HeckeChar F => f x) hpow
    simpa using h
  have hpowC : ((χ x : ℂˣ) : ℂ) ^ k = 1 := by
    have h := congrArg (fun z : ℂˣ => (z : ℂ)) hpowx
    change ((χ x : ℂˣ) ^ k : ℂ) = 1 at h
    simpa only [Units.val_pow_eq_pow_val] using h
  exact Complex.norm_eq_one_of_pow_eq_one hpowC (Nat.ne_of_gt hk)

private theorem heckeChar_primeValue_norm_le_one
    {F : Type} [Field F] [NumberField F] (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) (v : FinPlace F) : ‖χ.primeValue v‖ ≤ 1 := by
  classical
  unfold HeckeChar.primeValue
  split_ifs with hu
  · have h := heckeChar_value_norm_one χ hχ
      (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
        (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) )
    exact le_of_eq (by simpa [HeckeChar.loc] using h)
  · simp

private theorem norm_multiset_map_prod_le_one
    {α : Type*} (s : Multiset α) (f : α → ℂ)
    (hf : ∀ a ∈ s, ‖f a‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _)
        (ih fun x hx => hf x (Multiset.mem_cons_of_mem hx))

private theorem heckeChar_idealValue_norm_le_one
    {F : Type} [Field F] [NumberField F] (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) (I : Ideal (𝓞 F)) : ‖χ.idealValue I‖ ≤ 1 := by
  unfold HeckeChar.idealValue
  apply norm_multiset_map_prod_le_one
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using heckeChar_primeValue_norm_le_one χ hχ ⟨P, h.1, h.2⟩
  · simp [h]

private theorem heckeChar_idealValue_prime
    {F : Type} [Field F] [NumberField F] (χ : HeckeChar F) (v : FinPlace F) :
    χ.idealValue v.asIdeal = χ.primeValue v := by
  classical
  have hvIr : Irreducible v.asIdeal :=
    (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible
  unfold HeckeChar.idealValue
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hvIr]
  simp [normalize_eq, v.isPrime, v.ne_bot]

private theorem heckeChar_idealValue_mul
    {F : Type} [Field F] [NumberField F] (χ : HeckeChar F)
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    χ.idealValue (I * J) = χ.idealValue I * χ.idealValue J := by
  classical
  simp only [HeckeChar.idealValue,
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,
    Multiset.map_add, Multiset.prod_add]

private theorem heckeChar_idealValue_primePow
    {F : Type} [Field F] [NumberField F] (χ : HeckeChar F)
    (v : FinPlace F) (k : ℕ) :
  χ.idealValue (v.asIdeal ^ k) = χ.primeValue v ^ k := by
  induction k with
  | zero =>
      rw [pow_zero]
      change χ.idealValue (1 : Ideal (𝓞 F)) = 1
      unfold HeckeChar.idealValue
      rw [UniqueFactorizationMonoid.normalizedFactors_one]
      rfl
  | succ k ih =>
      rw [pow_succ, heckeChar_idealValue_mul χ _ _ (pow_ne_zero _ v.ne_bot) v.ne_bot,
        ih, heckeChar_idealValue_prime, pow_succ]

private noncomputable def heckeIdealWeight
    {F : Type} [Field F] [NumberField F] (χ : HeckeChar F) :
    Hecke.EulerProduct.IdealArithmeticFunction F :=
  fun I => χ.idealValue (I : Ideal (𝓞 F))

private theorem heckeIdealWeight_isMultiplicative
    {F : Type} [Field F] [NumberField F] (χ : HeckeChar F) :
  (heckeIdealWeight χ).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · change χ.idealValue (1 : Ideal (𝓞 F)) = 1
    unfold HeckeChar.idealValue
    rw [UniqueFactorizationMonoid.normalizedFactors_one]
    rfl
  · intro I J hIJ
    change χ.idealValue ((I : Ideal (𝓞 F)) * (J : Ideal (𝓞 F))) = _
    exact heckeChar_idealValue_mul χ _ _ (nonZeroDivisors.coe_ne_zero I)
      (nonZeroDivisors.coe_ne_zero J)

private theorem heckeIdealWeight_summable
    {F : Type} [Field F] [NumberField F] (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 1 < s.re) :
    Summable (Hecke.EulerProduct.idealTerm (heckeIdealWeight χ) s) := by
  let f := heckeIdealWeight χ
  have hbase : Summable (fun I : (Ideal (𝓞 F))⁰ =>
      Hecke.idealNormRpowTerm s.re (I : Ideal (𝓞 F))) := by
    have h := (Hecke.summable_idealNormRpow (K := F) hs).comp_injective
      (i := fun I : (Ideal (𝓞 F))⁰ => (I : Ideal (𝓞 F))) Subtype.val_injective
    convert h using 1
    funext I
    rfl
  have hnorm : Summable (fun I : (Ideal (𝓞 F))⁰ =>
      ‖Hecke.EulerProduct.idealTerm f s I‖) := by
    refine Summable.of_nonneg_of_le (by intro I; positivity) ?_ hbase
    intro I
    rw [Hecke.EulerProduct.norm_idealTerm]
    have hNpos : 0 < (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) := by
      exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
    have hNne : Ideal.absNorm (I : Ideal (𝓞 F)) ≠ 0 :=
      (Ideal.absNorm_pos_of_nonZeroDivisors I).ne'
    have hcoeff := heckeChar_idealValue_norm_le_one χ hχ (I : Ideal (𝓞 F))
    calc
      _ ≤ 1 / (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s.re := by
        exact div_le_div_of_nonneg_right hcoeff (by positivity)
      _ = Hecke.idealNormRpowTerm s.re (I : Ideal (𝓞 F)) := by
        simp [Hecke.idealNormRpowTerm, hNne, Real.rpow_neg (le_of_lt hNpos)]
  exact Summable.of_norm hnorm

private theorem heckeCoprime_iff_isPrimeTo
    {F : Type} [Field F] [NumberField F]
    (m : RayClassModulus F) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Hecke.IsCoprimeTo m I ↔ Ideal.IsPrimeTo I (m.finitePart.support : Set (FinPlace F)) := by
  have hcount (v : FinPlace F) :
      FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 ↔
        ¬ v.asIdeal ∣ I := by
    have hcount' :
        ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) = 0 ↔
          ¬ v.asIdeal ∣ I := by
      simpa using not_congr (Associates.count_ne_zero_iff_dvd hI v.irreducible)
    simpa [FractionalIdeal.count_coe F v hI] using hcount'
  constructor
  · rintro ⟨hI', hp⟩
    have hp' : ∀ v, v ∈ m.finitePart.support →
        FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
      intro v hv
      simpa [Hecke.idealUnit] using hp v hv
    rw [Ideal.isPrimeTo_iff]
    refine ⟨hI, ?_⟩
    intro v hv hdiv
    exact (hcount v).mp (hp' v hv) hdiv
  · intro hp
    refine ⟨hI, ?_⟩
    change ∀ v, v ∈ m.finitePart.support →
      FractionalIdeal.count F v
        ((Hecke.idealUnit I hI : NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
    intro v hv
    apply (hcount v).mpr
    exact (Ideal.isPrimeTo_iff.mp hp).2 v hv

private theorem liftedRayChar_primeValue_eq
    {n : ℕ} [NeZero n] {h12 : 12 ∣ n}
    {m : RayClassModulus (CyclotomicField n ℚ)}
    {η : RayClassGroup m →* ℂˣ}
    (d : EndpointAssemblyData n h12 m η)
    (v : FinPlace (CyclotomicField n ℚ)) (hv : v ∉ d.S.Sf) :
    charValue (liftedRayChar d) v.asIdeal = charValue η v.asIdeal := by
  classical
  let mS := enlargedModulus d
  have hsup : mS.finitePart.support = d.S.Sf := enlargedModulus_support d
  have hvM : v ∉ m.finitePart.support := fun h => hv (d.modulusSupport_subset h)
  have hcopM : Hecke.IsCoprimeTo m v.asIdeal := by
    refine ⟨v.ne_bot, ?_⟩
    change ∀ w, w ∈ m.finitePart.support →
      FractionalIdeal.count _ w
        ((Hecke.idealUnit v.asIdeal v.ne_bot : NumberFieldFractionalIdealGroup _ ) :
          FractionalIdeal (nonZeroDivisors (𝓞 (CyclotomicField n ℚ))) (CyclotomicField n ℚ)) = 0
    intro w hw
    have hwv : w ≠ v := by
      intro h
      subst w
      exact hv (d.modulusSupport_subset hw)
    simpa [Hecke.idealUnit] using
      (FractionalIdeal.count_maximal_coprime (CyclotomicField n ℚ) w (Ne.symm hwv))
  have hcopS : Hecke.IsCoprimeTo mS v.asIdeal :=
    (heckeCoprime_iff_isPrimeTo mS v.asIdeal v.ne_bot).2 (by
      rw [Ideal.isPrimeTo_iff]
      refine ⟨v.ne_bot, fun w hw hdiv => ?_⟩
      have hle : v.asIdeal ≤ w.asIdeal := Ideal.dvd_iff_le.mp hdiv
      have hEq : v.asIdeal = w.asIdeal :=
        v.isMaximal.eq_of_le w.isPrime.ne_top hle
      have hEq' : w = v := HeightOneSpectrum.ext hEq.symm
      subst w
      exact hv (by simpa [hsup] using hw))
  have hproj :
      rayClassProjection_local (modulus_le_enlarged d)
          (Hecke.rayClass mS v.asIdeal hcopS) =
        Hecke.rayClass m v.asIdeal hcopM := by
    simp [rayClassProjection_local, Hecke.rayClass, mS, hcopS, hcopM]
    rfl
  have hcopS' : Hecke.IsCoprimeTo (enlargedModulus d) v.asIdeal := by
    simpa [mS] using hcopS
  have hproj' : rayClassProjection_local (modulus_le_enlarged d)
        (Hecke.rayClass (enlargedModulus d) v.asIdeal hcopS') =
      Hecke.rayClass m v.asIdeal hcopM := by
    simpa [mS] using hproj
  simp only [liftedRayChar, Hecke.charValue, dif_pos hcopM, dif_pos hcopS',
    MonoidHom.comp_apply]
  rw [hproj']

private theorem liftedRaySeries_eq_incompleteHeckeLSeries
    {n : ℕ} [NeZero n] {h12 : 12 ∣ n}
    {m : RayClassModulus (CyclotomicField n ℚ)}
    {η : RayClassGroup m →* ℂˣ}
    (d : EndpointAssemblyData n h12 m η) {s : ℂ} (hs : 1 < s.re) :
    Hecke.LSeriesRay (liftedRayChar d) s =
      ArtinPrimitiveRoots.A2.incompleteHeckeLSeries d.S d.χ s := by
  classical
  let f := heckeIdealWeight d.χ
  let Sset : Set (FinPlace (CyclotomicField n ℚ)) := d.S.Sf
  let fS := Hecke.EulerProduct.IdealArithmeticFunction.supportedPart f
    Ssetᶜ
  let mS := enlargedModulus d
  let ηS := liftedRayChar d
  have hsup : mS.finitePart.support = d.S.Sf := enlargedModulus_support d
  have hχS : ∀ v : FinPlace (CyclotomicField n ℚ), v ∉ mS.finitePart.support →
      d.χ.UnramifiedAt v ∧ d.χ.primeValue v = Hecke.charValue ηS v.asIdeal := by
    intro v hv
    have hvS : v ∉ d.S.Sf := by simpa [hsup] using hv
    have hvM : v ∉ m.finitePart.support :=
      fun h => hvS (d.modulusSupport_subset h)
    refine ⟨d.χ_unramified v hvS, ?_⟩
    calc
      d.χ.primeValue v = Hecke.charValue η v.asIdeal := (d.χ_prime v hvM).2
      _ = Hecke.charValue ηS v.asIdeal :=
        (liftedRayChar_primeValue_eq d v hvS).symm
  have hvalue (I : Ideal (𝓞 (CyclotomicField n ℚ))) (hI : I ≠ ⊥) :
      fS ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ = Hecke.charValue ηS I := by
    have hcop := heckeCoprime_iff_isPrimeTo mS I hI
    by_cases hc : Ideal.IsPrimeTo I Sset
    · have hcRay : Hecke.IsCoprimeTo mS I := hcop.mpr (by simpa [hsup] using hc)
      change Hecke.EulerProduct.IdealArithmeticFunction.supportedPart f Ssetᶜ
        ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ = _
      have hc' : Ideal.IsPrimeTo I (Ssetᶜ)ᶜ := by simpa using hc
      rw [Hecke.EulerProduct.IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl
        hc']
      exact (ArtinPrimitiveRoots.Dictionary.idealValue_eq_charValue ηS d.χ hχS I hcRay)
    · have hcRay : ¬ Hecke.IsCoprimeTo mS I := by
        intro h
        exact hc (by simpa [hsup] using hcop.mp h)
      change Hecke.EulerProduct.IdealArithmeticFunction.supportedPart f Ssetᶜ
        ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ = _
      have hnc' : ¬ Ideal.IsPrimeTo I (Ssetᶜ)ᶜ := by simpa using hc
      rw [Hecke.EulerProduct.IdealArithmeticFunction.supportedPart_apply_of_not_isPrimeTo_compl
        hnc']
      unfold Hecke.charValue
      split_ifs with hcop
      · exact False.elim (hcRay (by simpa [mS] using hcop))
      · rfl
  have hχsum := heckeIdealWeight_summable d.χ d.χ_finite hs
  have hχsumS := Hecke.EulerProduct.summable_idealTerm_supportedPart hχsum
    Ssetᶜ
  have hcoeff (N : ℕ) :
      Hecke.EulerProduct.normCoeff (CyclotomicField n ℚ) fS N = Hecke.coeff ηS N := by
    rw [Hecke.EulerProduct.normCoeff_eq_sum_normFiber]
    by_cases hN : N = 0
    · subst N
      rw [Hecke.EulerProduct.normFiber_zero]
      unfold Hecke.coeff
      simp only [Finset.sum_empty]
      symm
      apply Finset.sum_eq_zero
      intro I hI
      have hnorm : Ideal.absNorm I = 0 := by
        simpa only [Set.mem_setOf_eq] using
          (Ideal.finite_setOfPred_absNorm_eq
            (S := 𝓞 (CyclotomicField n ℚ)) 0).mem_toFinset.mp hI
      have hbot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hnorm
      subst I
      simp [Hecke.charValue, Hecke.IsCoprimeTo]
    · let F0 := Ideal.finite_setOfPred_absNorm_eq
        (S := 𝓞 (CyclotomicField n ℚ)) N
      change (∑ I ∈ Hecke.EulerProduct.normFiber (CyclotomicField n ℚ) N, fS I) =
        ∑ I ∈ F0.toFinset, Hecke.charValue ηS I
      refine Finset.sum_bij (fun I _ => (I : Ideal (𝓞 (CyclotomicField n ℚ)))) ?_ ?_ ?_ ?_
      · intro I hI
        exact F0.mem_toFinset.mpr
          ((Hecke.EulerProduct.mem_normFiber (CyclotomicField n ℚ)).mp hI)
      · intro I hI J hJ hEq
        exact Subtype.ext hEq
      · intro J hJ
        have hnorm : Ideal.absNorm J = N := by
          simpa only [Set.mem_setOf_eq] using F0.mem_toFinset.mp hJ
        have hJ0 : J ≠ ⊥ := by
          intro hJbot
          subst J
          simp at hnorm
          exact hN hnorm.symm
        refine ⟨⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩,
          (Hecke.EulerProduct.mem_normFiber (CyclotomicField n ℚ)).mpr hnorm, rfl⟩
      · intro I hI
        exact hvalue (I : Ideal (𝓞 (CyclotomicField n ℚ)))
          (nonZeroDivisors.coe_ne_zero I)
  have hcoeffFun :
      Hecke.EulerProduct.normCoeff (CyclotomicField n ℚ) fS = Hecke.coeff ηS :=
    funext hcoeff
  have hLcoeff : Hecke.LSeriesRay ηS s =
      LSeries
        (Hecke.EulerProduct.normCoeff (CyclotomicField n ℚ) fS) s := by
    unfold Hecke.LSeriesRay
    rw [← hcoeffFun]
  have hSupport : Function.support
      (fun I : (Ideal (𝓞 (CyclotomicField n ℚ)))⁰ =>
        Hecke.EulerProduct.idealTerm fS s I) ⊆
      {I | Ideal.IsPrimeTo (I : Ideal (𝓞 (CyclotomicField n ℚ))) Sset} := by
    intro I hI
    have hval : fS I ≠ 0 := by
      intro hzero
      apply hI
      simp [Hecke.EulerProduct.idealTerm, hzero]
    have hprime := Hecke.EulerProduct.IdealArithmeticFunction.isPrimeTo_compl_of_supportedPart_apply_ne_zero
      hval
    change Ideal.IsPrimeTo (I : Ideal (𝓞 (CyclotomicField n ℚ))) Sset
    simpa using hprime
  have hsubtype :
      (∑' I : {I : (Ideal (𝓞 (CyclotomicField n ℚ)))⁰ //
          Ideal.IsPrimeTo (I : Ideal (𝓞 (CyclotomicField n ℚ))) Sset},
        Hecke.EulerProduct.idealTerm fS s I.1) =
      ∑' I : (Ideal (𝓞 (CyclotomicField n ℚ)))⁰,
        Hecke.EulerProduct.idealTerm fS s I :=
    tsum_subtype_eq_of_support_subset hSupport
  let T : Type := {I : Ideal (𝓞 (CyclotomicField n ℚ)) //
    I ≠ ⊥ ∧ ∀ v ∈ d.S.Sf, ¬ I ≤ v.asIdeal}
  let e : {I : (Ideal (𝓞 (CyclotomicField n ℚ)))⁰ //
      Ideal.IsPrimeTo (I : Ideal (𝓞 (CyclotomicField n ℚ))) Sset} ≃ T := {
    toFun := fun I => ⟨(I.1 : Ideal (𝓞 (CyclotomicField n ℚ))),
      ⟨nonZeroDivisors.coe_ne_zero I.1, fun v hv hle =>
        (Ideal.isPrimeTo_iff.mp I.2).2 v hv (Ideal.dvd_iff_le.mpr hle)⟩⟩
    invFun := fun I => ⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2.1⟩,
      (Ideal.isPrimeTo_iff).2 ⟨I.2.1, fun v hv hdiv =>
        I.2.2 v hv (Ideal.dvd_iff_le.mp hdiv)⟩⟩
    left_inv := by intro I; cases I; rfl
    right_inv := by intro I; cases I; rfl }
  let g : T → ℂ := fun I => d.χ.idealValue I.1 *
    ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
  have hterm (I : {I : (Ideal (𝓞 (CyclotomicField n ℚ)))⁰ //
      Ideal.IsPrimeTo (I : Ideal (𝓞 (CyclotomicField n ℚ))) Sset}) :
      g (e I) = Hecke.EulerProduct.idealTerm fS s I.1 := by
    have hcop' : Ideal.IsPrimeTo (I.1 : Ideal (𝓞 (CyclotomicField n ℚ)))
        (Ssetᶜ)ᶜ := by simpa only [compl_compl] using I.2
    have hfSχ : fS I.1 = d.χ.idealValue (I.1 : Ideal (𝓞 (CyclotomicField n ℚ))) := by
      change Hecke.EulerProduct.IdealArithmeticFunction.supportedPart
        (heckeIdealWeight d.χ) Ssetᶜ I.1 = _
      rw [Hecke.EulerProduct.IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl hcop']
      rfl
    change d.χ.idealValue (I.1 : Ideal (𝓞 (CyclotomicField n ℚ)) ) *
        ((Ideal.absNorm (I.1 : Ideal (𝓞 (CyclotomicField n ℚ))) : ℕ) : ℂ) ^ (-s) =
      Hecke.EulerProduct.idealTerm fS s I.1
    rw [Hecke.EulerProduct.idealTerm_def, Complex.cpow_neg,
      ← div_eq_mul_inv, ← hfSχ]
  calc
    Hecke.LSeriesRay ηS s =
        LSeries
          (Hecke.EulerProduct.normCoeff (CyclotomicField n ℚ) fS) s := hLcoeff
    _ = ∑' I : (Ideal (𝓞 (CyclotomicField n ℚ)))⁰,
          Hecke.EulerProduct.idealTerm fS s I :=
        Hecke.EulerProduct.LSeries_normCoeff hχsumS
    _ = ∑' I : {I : (Ideal (𝓞 (CyclotomicField n ℚ)))⁰ //
          Ideal.IsPrimeTo (I : Ideal (𝓞 (CyclotomicField n ℚ))) Sset},
          Hecke.EulerProduct.idealTerm fS s I.1 := hsubtype.symm
    _ = ∑' I : T, g I := by
          calc
            _ = ∑' I : {I : (Ideal (𝓞 (CyclotomicField n ℚ)))⁰ //
                Ideal.IsPrimeTo (I : Ideal (𝓞 (CyclotomicField n ℚ))) Sset},
                g (e I) := tsum_congr fun I => (hterm I).symm
            _ = ∑' I : T, g I := Equiv.tsum_eq e g
    _ = ArtinPrimitiveRoots.A2.incompleteHeckeLSeries d.S d.χ s := rfl

private theorem rayPrime_isCoprimeTo
    {F : Type} [Field F] [NumberField F]
    (m : RayClassModulus F) (v : FinPlace F)
    (hv : v ∉ m.finitePart.support) : Hecke.IsCoprimeTo m v.asIdeal := by
  refine ⟨v.ne_bot, ?_⟩
  change ∀ w, w ∈ m.finitePart.support →
    FractionalIdeal.count F w
      ((Hecke.idealUnit v.asIdeal v.ne_bot : NumberFieldFractionalIdealGroup F) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
  intro w hw
  have hwv : w ≠ v := by
    intro h
    subst w
    exact hv hw
  simpa [Hecke.idealUnit] using
    (FractionalIdeal.count_maximal_coprime F w (Ne.symm hwv))

private theorem rayCharValue_one_at_prime
    {F : Type} [Field F] [NumberField F]
    (m : RayClassModulus F) (v : FinPlace F)
    (hv : v ∉ m.finitePart.support) :
    Hecke.charValue (1 : RayClassGroup m →* ℂˣ) v.asIdeal = 1 := by
  have hcop := rayPrime_isCoprimeTo m v hv
  simp [Hecke.charValue, hcop]

private theorem haLS_eq_liftedRay
    {n : ℕ} [NeZero n] {h12 : 12 ∣ n}
    {m : RayClassModulus (CyclotomicField n ℚ)}
    {η : RayClassGroup m →* ℂˣ}
    (d : EndpointAssemblyData n h12 m η) {s : ℂ} (hs : 1 < s.re) :
    d.HA.LS d.S d.χ s = Hecke.LSeriesRay (liftedRayChar d) s := by
  classical
  let mS := enlargedModulus d
  let ηS := liftedRayChar d
  have hsup : mS.finitePart.support = d.S.Sf := enlargedModulus_support d
  by_cases hχ : d.χ = 1
  · have hχprimeOne (v : FinPlace (CyclotomicField n ℚ)) : d.χ.primeValue v = 1 := by
      rw [hχ]
      have hUnram : (1 : HeckeChar (CyclotomicField n ℚ)).UnramifiedAt v := by
        intro u hu hu'
        simp [HeckeChar.UnramifiedAt, HeckeChar.loc]
      unfold HeckeChar.primeValue
      simp [hUnram, HeckeChar.loc]
    have hηvals : ∀ v, v ∉ m.finitePart.support →
        Hecke.charValue η v.asIdeal =
          Hecke.charValue (1 : RayClassGroup m →* ℂˣ) v.asIdeal := by
      intro v hv
      have hp := (d.χ_prime v hv).2
      rw [hχprimeOne] at hp
      calc
        Hecke.charValue η v.asIdeal = 1 := hp.symm
        _ = Hecke.charValue (1 : RayClassGroup m →* ℂˣ) v.asIdeal := by
          exact (rayCharValue_one_at_prime m v hv).symm
    have hηone : η = (1 : RayClassGroup m →* ℂˣ) :=
      ArtinPrimitiveRoots.Dictionary.rayClassChar_eq_of_charValue
        η 1 m.finitePart.support hηvals
    have hηSone : ηS = (1 : RayClassGroup mS →* ℂˣ) := by
      ext x
      simp [ηS, liftedRayChar, hηone]
    let m0 : RayClassModulus (CyclotomicField n ℚ) := ⟨0, ∅⟩
    let η0 : RayClassGroup m0 →* ℂˣ := 1
    have hIval : ∀ I : Ideal (𝓞 (CyclotomicField n ℚ)), I ≠ ⊥ →
        (1 : HeckeChar (CyclotomicField n ℚ)).idealValue I =
          Hecke.charValue η0 I := by
      intro I hI
      have hcop : Hecke.IsCoprimeTo m0 I := by
        refine ⟨hI, ?_⟩
        intro v hv
        simp [m0] at hv
      have hleft : (1 : HeckeChar (CyclotomicField n ℚ)).idealValue I = 1 := by
        unfold HeckeChar.idealValue
        apply Multiset.prod_eq_one
        intro z hz
        obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hz
        by_cases h : P.IsPrime ∧ P ≠ ⊥
        · have hp : (1 : HeckeChar (CyclotomicField n ℚ)).primeValue
              ⟨P, h.1, h.2⟩ = 1 := by
            simpa [hχ] using hχprimeOne ⟨P, h.1, h.2⟩
          simp [h, hp]
        · simp [h]
      have hright : Hecke.charValue η0 I = 1 := by
        simp [Hecke.charValue, hcop, η0]
      exact hleft.trans hright.symm
    have hqsa : heckeLSeries (1 : HeckeChar (CyclotomicField n ℚ)) s =
        Hecke.LSeriesRay η0 s :=
      ArtinPrimitiveRoots.A2.qsa_heckeLSeries_eq_LSeriesRay
        (1 : HeckeChar (CyclotomicField n ℚ)) η0 hIval hs
    have hHAraw := d.HA.property.1 d.χ s hs
    have hHArawOne : d.HA.L (1 : HeckeChar (CyclotomicField n ℚ)) s =
        heckeLSeries (1 : HeckeChar (CyclotomicField n ℚ)) s := by
      simpa [HeckeAnalysis.L, hχ] using hHAraw
    have hFull : d.HA.L d.χ s = Hecke.LSeriesRay η0 s := by
      calc
        d.HA.L d.χ s = d.HA.L (1 : HeckeChar (CyclotomicField n ℚ)) s := by rw [hχ]
        _ = heckeLSeries (1 : HeckeChar (CyclotomicField n ℚ)) s := hHArawOne
        _ = Hecke.LSeriesRay η0 s := hqsa
    have hAgree : ∀ v : FinPlace (CyclotomicField n ℚ),
        v ∉ mS.finitePart.support →
          Hecke.charValue ηS v.asIdeal = Hecke.charValue η0 v.asIdeal := by
      intro v hv
      have hvS : v ∉ d.S.Sf := by simpa [hsup] using hv
      rw [hηSone]
      have h1 := rayCharValue_one_at_prime mS v (by simpa [hsup] using hv)
      have h0 := rayCharValue_one_at_prime m0 v (by simp [m0])
      exact h1.trans h0.symm
    have hchange := Hecke.LSeriesRay_change_modulus
      (m := mS) (n := m0) ηS η0 hAgree hs
    have hprod :
        (∏ v ∈ mS.finitePart.support,
          (1 - Hecke.charValue η0 v.asIdeal *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) =
        ∏ v ∈ d.S.Sf,
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
      rw [hsup]
      apply Finset.prod_congr rfl
      intro v hv
      have h0 := rayCharValue_one_at_prime m0 v (by simp [m0])
      rw [h0]
      ring
    have hchange' : Hecke.LSeriesRay ηS s =
        Hecke.LSeriesRay η0 s *
          ∏ v ∈ d.S.Sf,
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
      rw [hchange, hprod]
    calc
      d.HA.LS d.S d.χ s =
          d.HA.L d.χ s * ∏ v ∈ d.S.Sf,
            (1 - d.χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) := rfl
      _ = Hecke.LSeriesRay η0 s * ∏ v ∈ d.S.Sf,
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
          rw [hFull]
          congr 1
          apply Finset.prod_congr rfl
          intro v hv
          rw [hχprimeOne v]
          ring
      _ = Hecke.LSeriesRay ηS s := hchange'.symm
  · obtain ⟨K⟩ := ArtinPrimitiveRoots.A2.incompleteDictionary_exists d.χ d.U d.HA
    have htwist : d.χ * (d.U.kummer d.U.one)⁻¹ = d.χ := by
      ext x
      have hkx : d.U.kummer d.U.one x = 1 := by
        have h := congrArg (fun f : HeckeChar (CyclotomicField n ℚ) => f x)
          d.U.kummer_one
        simpa using h
      change (((d.χ x : ℂˣ) * (d.U.kummer d.U.one x)⁻¹ : ℂˣ) : ℂ) =
        ((d.χ x : ℂˣ) : ℂ)
      rw [hkx]
      simp
    have hω : d.U.omega d.U.one = d.χ := by
      calc
        d.U.omega d.U.one = d.χ * (d.U.kummer d.U.one)⁻¹ :=
          d.U.omega_induces_twist d.U.one
        _ = d.χ := htwist
    have hωne : d.U.omega d.U.one ≠ 1 := by
      rw [hω]
      exact hχ
    have h997 : 997 / 1000 < s.re := by linarith
    have hvalue := K.incomplete_eq d.U.one hωne s h997
    have hagree := (K.incomplete d.U.one hωne).agrees s hs
    have hinc : (K.incomplete d.U.one hωne).value s =
        ArtinPrimitiveRoots.A2.incompleteHeckeLSeries d.S d.χ s := by
      calc
        _ = ArtinPrimitiveRoots.A2.incompleteHeckeLSeries d.S
            (d.χ * (d.U.kummer d.U.one)⁻¹) s := hagree
        _ = ArtinPrimitiveRoots.A2.incompleteHeckeLSeries d.S d.χ s :=
          congrArg (fun ψ => ArtinPrimitiveRoots.A2.incompleteHeckeLSeries d.S ψ s) htwist
    have hvalue' : (K.incomplete d.U.one hωne).value s = d.HA.LS d.S d.χ s := by
      calc
        _ = d.HA.LS d.S (d.χ * (d.U.kummer d.U.one)⁻¹) s := hvalue
        _ = d.HA.LS d.S d.χ s := congrArg (fun ψ => d.HA.LS d.S ψ s) htwist
    calc
      d.HA.LS d.S d.χ s = (K.incomplete d.U.one hωne).value s := hvalue'.symm
      _ = ArtinPrimitiveRoots.A2.incompleteHeckeLSeries d.S d.χ s := hinc
      _ = Hecke.LSeriesRay (liftedRayChar d) s :=
        (liftedRaySeries_eq_incompleteHeckeLSeries d hs).symm

private theorem finiteRayFactor_differentiable
    {n : ℕ} [NeZero n] {h12 : 12 ∣ n}
    {m : RayClassModulus (CyclotomicField n ℚ)}
    {η : RayClassGroup m →* ℂˣ}
    (d : EndpointAssemblyData n h12 m η) :
    Differentiable ℂ (finiteRayFactor d) := by
  classical
  unfold finiteRayFactor
  refine Differentiable.fun_finsetProd ?_
  intro v hv
  have hNnat : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNnat
  have hpow : Differentiable ℂ
      (fun s : ℂ => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
    intro s
    exact (differentiableAt_id.neg).const_cpow (Or.inl hN)
  exact (differentiable_const (1 : ℂ)).sub
    ((differentiable_const (d.χ.primeValue v)).mul hpow)

private theorem finiteRayFactor_ne_zero
    {n : ℕ} [NeZero n] {h12 : 12 ∣ n}
    {m : RayClassModulus (CyclotomicField n ℚ)}
    {η : RayClassGroup m →* ℂˣ}
    (d : EndpointAssemblyData n h12 m η) {s : ℂ} (hs : 0 < s.re) :
    finiteRayFactor d s ≠ 0 := by
  classical
  unfold finiteRayFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  apply sub_ne_zero.mpr
  intro hzero
  have hterm : d.χ.primeValue v *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) = 1 := hzero.symm
  have hnormOne : ‖d.χ.primeValue v *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ = 1 := by
    rw [hterm]
    norm_num
  have hNne : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hNnat : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero hNne
  have hNgt : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hNpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  have hcpowNorm :
      ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
    simpa using Complex.norm_natCast_cpow_of_pos hNnat (-s)
  have htermNorm : ‖d.χ.primeValue v *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, hcpowNorm]
    calc
      ‖d.χ.primeValue v‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤
          1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right
              (heckeChar_primeValue_norm_le_one d.χ d.χ_finite v) (by positivity)
      _ < 1 := by
        rw [one_mul]
        exact Real.rpow_lt_one_of_one_lt_of_neg hNgt (neg_lt_zero.mpr hs)
  exact (ne_of_lt htermNorm) hnormOne

private noncomputable def rayDeletion_from_context
    {n : ℕ} [NeZero n] {h12 : 12 ∣ n}
    {m : RayClassModulus (CyclotomicField n ℚ)}
    {η : RayClassGroup m →* ℂˣ}
    (d : EndpointAssemblyData n h12 m η) :
    ArtinPrimitiveRoots.A2.RayDeletion d.S d.χ m η d.HA := by
  classical
  let mS := enlargedModulus d
  let ηS := liftedRayChar d
  have hsup : mS.finitePart.support = d.S.Sf := enlargedModulus_support d
  have hAgree : ∀ v : FinPlace (CyclotomicField n ℚ),
      v ∉ mS.finitePart.support →
        Hecke.charValue ηS v.asIdeal = Hecke.charValue η v.asIdeal := by
    intro v hv
    have hvS : v ∉ d.S.Sf := by simpa [hsup] using hv
    exact liftedRayChar_primeValue_eq d v hvS
  have hchange (s : ℂ) (hs : 1 < s.re) := Hecke.LSeriesRay_change_modulus
    (m := mS) (n := m) (s := s) ηS η hAgree hs
  have hfactorProd (s : ℂ) :
      (∏ v ∈ mS.finitePart.support,
        (1 - Hecke.charValue η v.asIdeal *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) = finiteRayFactor d s := by
    rw [hsup]
    let A := m.finitePart.support
    let B := d.S.Sf \ A
    have hdecomp : A ∪ B = d.S.Sf := Finset.union_sdiff_of_subset d.modulusSupport_subset
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro v hvA hvB
      exact (Finset.mem_sdiff.mp hvB).2 hvA
    rw [← hdecomp, Finset.prod_union hdisj]
    have hA : ∏ v ∈ A,
        (1 - Hecke.charValue η v.asIdeal *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) = 1 := by
      apply Finset.prod_eq_one
      intro v hv
      rw [ArtinPrimitiveRoots.Dictionary.charValue_eq_zero_of_mem_support η hv]
      ring
    have hB : ∏ v ∈ B,
        (1 - Hecke.charValue η v.asIdeal *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) =
        ∏ v ∈ B,
          (1 - d.χ.primeValue v *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
      apply Finset.prod_congr rfl
      intro v hv
      have hvM : v ∉ m.finitePart.support := (Finset.mem_sdiff.mp hv).2
      rw [← d.χ_prime v hvM |>.2]
    rw [hA, hB]
    simp [finiteRayFactor, B, A]
  refine {
    factor := finiteRayFactor d
    factor_holomorphic := finiteRayFactor_differentiable d
    factor_nonzero := fun s hs => finiteRayFactor_ne_zero d hs
    agrees := ?_ }
  intro s hs
  calc
    d.HA.LS d.S d.χ s = Hecke.LSeriesRay ηS s := haLS_eq_liftedRay d hs
    _ = Hecke.LSeriesRay η s * finiteRayFactor d s := by
      rw [hchange s hs, hfactorProd s]

theorem thm_hecke_zero_free_assembly
    (n : ℕ) [NeZero n] (h12 : 12 ∣ n)
    (m : RayClassModulus (CyclotomicField n ℚ))
    (η : RayClassGroup m →* ℂˣ) (Λ : ℂ → ℂ)
    (hΛ : DifferentiableOn ℂ Λ
      ({s : ℂ | 1 - a2Delta0 < s.re} \ {s | η = 1 ∧ s = 1}))
    (hL : ∀ s : ℂ, 1 < s.re → Λ s = Hecke.LSeriesRay η s) :
    ∀ s : ℂ, 1 - a2Delta0 < s.re → (η ≠ 1 ∨ s ≠ 1) → Λ s ≠ 0 := by
  classical
  obtain ⟨d⟩ := endpointAssemblyData_nonempty n h12 m η
  let RD := rayDeletion_from_context d
  exact ArtinPrimitiveRoots.A2.boundary_from_mellin
    ArtinPrimitiveRoots.A2.mellin_identification_narrow n h12 d.χ m η d.HA
    (Heta d.R d.χ d.U d.HC) d.inputs RD Λ hΛ hL

end ArtinPrimitiveRoots.Proofs.a2_zf_top
