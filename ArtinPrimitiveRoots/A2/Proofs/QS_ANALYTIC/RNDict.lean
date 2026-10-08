import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M0
import ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs
import ArtinPrimitiveRoots.Hecke.Dictionary
import ArtinPrimitiveRoots.Hecke.Theta.IdealNormSummability

/-!
# QS-ANALYTIC, RN-D: from a quadratic idelic character to a primitive ray character

For a nonprincipal quadratic idelic character `χ` with primitive conductor `f` over a totally
complex field, DICT-2 (`Dictionary.exists_rayClass_of_heckeChar`) gives a ray character `ψ` of a
modulus with finite part `f`.  It is nontrivial, quadratic, primitive in the HK-FE sense
(DICT-1, DICT-3 and the least-norm property of `f`), and its L-series is `heckeLSeries χ`
(prime values agree off `f`; both ideal values vanish at ideals meeting `f`, by
`qs_idealValue_eq_zero_of_conductor_M0`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open scoped NumberField nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- RN-D1: conductor divisibility gives unramifiedness at the places outside the modulus. -/
theorem qsa_unramifiedAt_of_conductorDvd (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (n : Ideal (𝓞 K)) (hn : χ.ConductorDvd n) (v : HeightOneSpectrum (𝓞 K))
    (hv : ArtinPrimitiveRoots.A1.idealExp v n = 0) : χ.UnramifiedAt v := by
  intro u hu hu'
  apply hn v u hu hu'
  rw [hv]
  have h1 : ((u : v.adicCompletion K) - 1) ∈ v.adicCompletionIntegers K :=
    sub_mem hu (one_mem _)
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h1
  simpa using h1

/-- RN-D2 (IMPL candidate): the raw ideal series is the ray L-series when the ideal values
agree with the ray character values on nonzero ideals. -/
theorem qsa_heckeLSeries_eq_LSeriesRay (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (h : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → χ.idealValue I = Hecke.charValue ψ I)
    {s : ℂ} (hs : 1 < s.re) :
    heckeLSeries χ s = Hecke.LSeriesRay ψ s := by
  classical
  let f : Hecke.EulerProduct.IdealArithmeticFunction K :=
    fun I => Hecke.charValue ψ (I : Ideal (𝓞 K))
  have hcoeff (n : ℕ) : Hecke.EulerProduct.normCoeff K f n = Hecke.coeff ψ n := by
    rw [Hecke.EulerProduct.normCoeff_eq_sum_normFiber]
    by_cases hn : n = 0
    · subst n
      rw [Hecke.EulerProduct.normFiber_zero]
      unfold Hecke.coeff
      simp only [Finset.sum_empty]
      symm
      apply Finset.sum_eq_zero
      intro I hI
      have hnorm : Ideal.absNorm I = 0 := by
        simpa only [Set.mem_setOf_eq] using
          (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) 0).mem_toFinset.mp hI
      have hbot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hnorm
      subst I
      simp [Hecke.charValue, Hecke.IsCoprimeTo]
    · let F := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
      change (∑ I ∈ Hecke.EulerProduct.normFiber K n, Hecke.charValue ψ (I : Ideal (𝓞 K))) =
        ∑ I ∈ F.toFinset, Hecke.charValue ψ I
      refine Finset.sum_bij (fun I _ ↦ (I : Ideal (𝓞 K))) ?_ ?_ ?_ ?_
      · intro I hI
        exact F.mem_toFinset.mpr ((Hecke.EulerProduct.mem_normFiber K).mp hI)
      · intro I hI J hJ hEq
        exact Subtype.ext hEq
      · intro J hJ
        have hnorm : Ideal.absNorm J = n := by
          simpa only [Set.mem_setOf_eq] using F.mem_toFinset.mp hJ
        have hJ0 : J ≠ ⊥ := by
          intro hJbot
          subst J
          simp at hnorm
          exact hn hnorm.symm
        refine ⟨⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩,
          (Hecke.EulerProduct.mem_normFiber K).mpr hnorm, rfl⟩
      · intro I hI
        rfl
  have hsum : Summable (Hecke.EulerProduct.idealTerm f s) := by
    have hbase := Hecke.summable_idealNormRpow (K := K) hs
    have hinj : Function.Injective (fun I : (Ideal (𝓞 K))⁰ => (I : Ideal (𝓞 K))) :=
      Subtype.val_injective
    refine Summable.of_norm_bounded (hbase.comp_injective hinj) ?_
    intro I
    rw [Hecke.EulerProduct.norm_idealTerm]
    have hN : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 :=
      (Ideal.absNorm_pos_of_nonZeroDivisors I).ne'
    simp only [Function.comp_apply, Hecke.idealNormRpowTerm, if_neg hN]
    rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) (Hecke.norm_charValue_le_one ψ _)
  have h1 : Hecke.LSeriesRay ψ s = ∑' I, Hecke.EulerProduct.idealTerm f s I := by
    rw [← Hecke.EulerProduct.LSeries_normCoeff hsum]
    unfold Hecke.LSeriesRay
    congr 1
    funext n
    exact (hcoeff n).symm
  rw [h1]
  unfold heckeLSeries
  let e : (Ideal (𝓞 K))⁰ ≃ {I : Ideal (𝓞 K) // I ≠ ⊥} :=
    { toFun := fun I => ⟨I.1, nonZeroDivisors.coe_ne_zero I⟩
      invFun := fun I => ⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.tsum_eq]
  refine tsum_congr fun I => ?_
  simp only [e, Equiv.coe_fn_mk, Hecke.EulerProduct.idealTerm_def, f]
  rw [h I.1 (nonZeroDivisors.coe_ne_zero I), Complex.cpow_neg, div_eq_mul_inv]

/-- RN-D3: a ray character matching `χ` off a modulus with finite part the primitive conductor
of `χ` is primitive in the HK-FE sense (totally complex: no real places). -/
theorem qsa_hkPrimitive_of_primitiveConductor [IsTotallyComplex K]
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f : Ideal (𝓞 K))
    (hf : IsPrimitiveConductor χ f) {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (hm : Dictionary.modulusIdeal m = f)
    (hψ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
      Hecke.charValue ψ v.asIdeal = χ.primeValue v) :
    Hecke.HKPrimitive ψ := by
  classical
  intro n hn
  obtain ⟨ψ', hψ'⟩ := Dictionary.exists_rayClassChar_of_factorsThrough hn.1 ψ hn
  obtain ⟨χ', -, hcond', hval'⟩ := Dictionary.exists_heckeChar_of_rayClass n ψ'
  have hsupp : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
      v ∉ n.finitePart.support := fun v hv hvn => hv (Finsupp.support_mono hn.1.1 hvn)
  have hcop : ∀ (k : RayClassModulus K) (v : HeightOneSpectrum (𝓞 K)),
      v ∉ k.finitePart.support → Hecke.IsCoprimeTo k v.asIdeal := by
    intro k v hv
    refine ⟨v.ne_bot, ?_⟩
    intro w hw
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    simpa [Hecke.idealUnit] using FractionalIdeal.count_maximal_coprime K w (Ne.symm hwv)
  have hchar : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
      Hecke.charValue ψ v.asIdeal = Hecke.charValue ψ' v.asIdeal := by
    intro v hv
    simp only [Hecke.charValue, dif_pos (hcop m v hv), dif_pos (hcop n v (hsupp v hv))]
    rw [hψ']
    rfl
  have hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support → χ.UnramifiedAt v := by
    intro v hv
    refine qsa_unramifiedAt_of_conductorDvd χ f hf.2.1 v ?_
    rw [← hm, Dictionary.idealExp_modulusIdeal]
    exact Finsupp.notMem_support_iff.mp hv
  have hχχ' : χ = χ' := by
    refine Dictionary.heckeChar_eq_of_primeValue χ χ' m.finitePart.support ?_
    intro v hv
    refine ⟨hunr v hv, (hval' v (hsupp v hv)).1, ?_⟩
    rw [← hψ v hv, hchar v hv, (hval' v (hsupp v hv)).2]
  have hcondN : χ.ConductorDvd (Dictionary.modulusIdeal n) := hχχ' ▸ hcond'
  have hle := hf.2.2 _ (Dictionary.modulusIdeal_ne_bot n) hcondN
  have hsub : Dictionary.modulusIdeal m ≤ Dictionary.modulusIdeal n := by
    let d := m.finitePart - n.finitePart
    have hd : n.finitePart + d = m.finitePart := by
      ext v
      exact Nat.add_sub_of_le (hn.1.1 v)
    unfold Dictionary.modulusIdeal
    rw [← hd, Finsupp.prod_add_index' (h_zero := by intro v; simp)
      (h_add := by intro v a b; simp [pow_add])]
    exact Ideal.mul_le_left
  have hdvd : Dictionary.modulusIdeal n ∣ f := hm ▸ Ideal.dvd_iff_le.mpr hsub
  obtain ⟨Q, hQ⟩ := hdvd
  have hfpos : 0 < Ideal.absNorm f := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact hf.1
  have hnorm : Ideal.absNorm f = Ideal.absNorm (Dictionary.modulusIdeal n) * Ideal.absNorm Q := by
    rw [hQ, map_mul]
  have hQ1 : Ideal.absNorm Q = 1 := by
    have hpos : 0 < Ideal.absNorm (Dictionary.modulusIdeal n) := by
      rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
      exact Dictionary.modulusIdeal_ne_bot n
    have h1 : Ideal.absNorm (Dictionary.modulusIdeal n) * Ideal.absNorm Q ≤
        Ideal.absNorm (Dictionary.modulusIdeal n) * 1 := by
      rw [← hnorm, mul_one]; exact hle
    have hQpos : 0 < Ideal.absNorm Q := by
      rcases Nat.eq_zero_or_pos (Ideal.absNorm Q) with h0 | h0
      · rw [hnorm, h0, mul_zero] at hfpos; exact absurd hfpos (lt_irrefl 0)
      · exact h0
    have := Nat.le_of_mul_le_mul_left h1 hpos
    omega
  rw [Ideal.absNorm_eq_one_iff] at hQ1
  have hEq : Dictionary.modulusIdeal n = Dictionary.modulusIdeal m := by
    rw [hm, hQ, hQ1, Ideal.mul_top]
  have hfin : n.finitePart = m.finitePart := by
    ext v
    rw [← Dictionary.idealExp_modulusIdeal, ← Dictionary.idealExp_modulusIdeal, hEq]
  have hempty : IsEmpty (RayClassRealPlace K) := by
    refine ⟨fun v => ?_⟩
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v.1)) v.2
  have hinf : n.infinitePart = m.infinitePart := by
    rw [Finset.eq_empty_of_isEmpty n.infinitePart, Finset.eq_empty_of_isEmpty m.infinitePart]
  cases n
  cases m
  simp only at hfin hinf
  subst hfin hinf
  rfl

/-- RN-D: the ray character attached to a nonprincipal quadratic idelic character. -/
theorem qsa_ray_of_quadratic [IsTotallyComplex K]
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f : Ideal (𝓞 K))
    (hf : IsPrimitiveConductor χ f) (hsq : χ ^ 2 = 1) (hne : χ ≠ 1) :
    ∃ (m : RayClassModulus K) (ψ : RayClassGroup m →* ℂˣ),
      Hecke.modulusNorm m = Ideal.absNorm f ∧ ψ ≠ 1 ∧ ψ⁻¹ = ψ ∧ Hecke.HKPrimitive ψ ∧
      ∀ s : ℂ, 1 < s.re → heckeLSeries χ s = Hecke.LSeriesRay ψ s := by
  classical
  have hfin : IsOfFinOrder χ := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, hsq⟩
  obtain ⟨m, ψ, hmI, -, hval⟩ := Dictionary.exists_rayClass_of_heckeChar χ hfin f hf.1 hf.2.1
  have hcop : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
      Hecke.IsCoprimeTo m v.asIdeal := by
    intro v hv
    refine ⟨v.ne_bot, ?_⟩
    intro w hw
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    simpa [Hecke.idealUnit] using FractionalIdeal.count_maximal_coprime K w (Ne.symm hwv)
  have hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support → χ.UnramifiedAt v := by
    intro v hv
    refine qsa_unramifiedAt_of_conductorDvd χ f hf.2.1 v ?_
    rw [← hmI, Dictionary.idealExp_modulusIdeal]
    exact Finsupp.notMem_support_iff.mp hv
  have hsqval : ∀ x, χ x ^ 2 = 1 := by
    intro x
    have := DFunLike.congr_fun hsq x
    simpa [pow_two] using this
  have hprime_sq : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
      (Hecke.charValue ψ v.asIdeal) ^ 2 = 1 := by
    intro v hv
    rw [hval v hv, ArtinPrimitiveRoots.A1.HeckeChar.primeValue, if_pos (hunr v hv)]
    have := hsqval ((IdeleClassGroup.ofAdicCompletion (𝓞 K) K v)
      (ArtinPrimitiveRoots.A1.toLoc v
        (Units.mk0 (ArtinPrimitiveRoots.A1.unif v) (ArtinPrimitiveRoots.A1.unif_ne_zero v))))
    have h' := congrArg (fun z : ℂˣ => (z : ℂ)) this
    simpa [ArtinPrimitiveRoots.A1.HeckeChar.loc] using h'
  have hinv : ψ⁻¹ = ψ := by
    refine Dictionary.rayClassChar_eq_of_charValue ψ⁻¹ ψ m.finitePart.support ?_
    intro v hv
    have h2 := hprime_sq v hv
    have hc := hcop v hv
    rw [Hecke.charValue, dif_pos hc] at h2
    have hz : (ψ (Hecke.rayClass m v.asIdeal hc)) ^ 2 = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h2)
    have hz' : (ψ (Hecke.rayClass m v.asIdeal hc))⁻¹ = ψ (Hecke.rayClass m v.asIdeal hc) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, hz]
    rw [Hecke.charValue, Hecke.charValue, dif_pos hc, dif_pos hc, MonoidHom.inv_apply, hz']
  have hne1 : ψ ≠ 1 := by
    intro h1
    apply hne
    refine Dictionary.heckeChar_eq_of_primeValue χ 1 m.finitePart.support ?_
    intro v hv
    have hun1 : (1 : ArtinPrimitiveRoots.A1.HeckeChar K).UnramifiedAt v := by
      intro u _ _
      rfl
    refine ⟨hunr v hv, hun1, ?_⟩
    rw [← hval v hv, h1, ArtinPrimitiveRoots.A1.HeckeChar.primeValue, if_pos hun1]
    simp [Hecke.charValue, dif_pos (hcop v hv), ArtinPrimitiveRoots.A1.HeckeChar.loc]
  refine ⟨m, ψ, ?_, hne1, hinv,
    qsa_hkPrimitive_of_primitiveConductor χ f hf ψ hmI hval, ?_⟩
  · rw [Dictionary.modulusNorm_eq_absNorm, hmI]
  · intro s hs
    refine qsa_heckeLSeries_eq_LSeriesRay χ ψ ?_ hs
    intro I hI
    by_cases hc : Hecke.IsCoprimeTo m I
    · exact Dictionary.idealValue_eq_charValue ψ χ
        (fun v hv => ⟨hunr v hv, (hval v hv).symm⟩) I hc
    · rw [Hecke.charValue, dif_neg hc]
      have hex : ∃ v ∈ m.finitePart.support, v.asIdeal ∣ I := by
        by_contra hnot
        push_neg at hnot
        apply hc
        refine ⟨hI, ?_⟩
        intro v hv
        simp only [Hecke.idealUnit, Units.val_mk0]
        rw [FractionalIdeal.count_coe K v hI]
        have := (Associates.count_ne_zero_iff_dvd hI v.irreducible).not.mpr (hnot v hv)
        push_neg at this
        exact_mod_cast this
      obtain ⟨v, hv, hvI⟩ := hex
      have hvf : v.asIdeal ∣ f := by
        rw [← hmI]
        unfold Dictionary.modulusIdeal
        have hpos : m.finitePart v ≠ 0 := Finsupp.mem_support_iff.mp hv
        exact (dvd_pow_self v.asIdeal hpos).trans
          (Finset.dvd_prod_of_mem (fun w => w.asIdeal ^ m.finitePart w) hv)
      exact qs_idealValue_eq_zero_of_conductor_M0 χ f hf v.asIdeal I v.isPrime v.ne_bot hvf hI hvI

end ArtinPrimitiveRoots.A2
