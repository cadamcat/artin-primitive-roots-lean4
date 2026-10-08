import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.QuadraticSieve
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».SYMBOL
import ArtinPrimitiveRoots.A1.AddChar

/-!
# Section 4: row replacement, moving twists, S-characters, and the finite mask
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private lemma rf_qs_ext_ne_bot {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) : I.1 ≠ ⊥ := by
  simpa [Ideal.zero_eq_bot] using I.2.1.1

private noncomputable def rf_qs_support {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) : Finset (ArtinPrimitiveRoots.A1.FinPlace F) :=
  (Ideal.finite_factors (rf_qs_ext_ne_bot I)).toFinset

private lemma rf_qs_support_mem {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    v ∈ rf_qs_support I ↔ v.asIdeal ∣ I.1 := by
  simp [rf_qs_support, rf_qs_ext_ne_bot]

private lemma rf_qs_support_disjoint {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) :
    Disjoint (rf_qs_support I) S.Sf := by
  apply Finset.disjoint_left.mpr
  intro v hvI hvS
  have hdiv : v.asIdeal ∣ I.1 := (rf_qs_support_mem I v).mp hvI
  have hle : I.1 ≤ v.asIdeal := (Ideal.dvd_iff_le).mp hdiv
  exact (I.2.1.2 v hvS) hle

private lemma rf_qs_support_normalizedFactors {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) :
    (UniqueFactorizationMonoid.normalizedFactors I.1).toFinset =
      (rf_qs_support I).image (fun v : ArtinPrimitiveRoots.A1.FinPlace F => v.asIdeal) := by
  classical
  have hI : I.1 ≠ ⊥ := rf_qs_ext_ne_bot I
  ext P
  constructor
  · intro hPfin
    have hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I.1 :=
      Multiset.mem_toFinset.mp hPfin
    have hprime : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    have hfactor := (Ideal.mem_normalizedFactors_iff hI).mp hP
    let v : ArtinPrimitiveRoots.A1.FinPlace F := ⟨P, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩
    have hvdiv : v.asIdeal ∣ I.1 := by
      apply Ideal.dvd_iff_le.mpr
      simpa [v] using hfactor.2
    exact Finset.mem_image.mpr ⟨v, (rf_qs_support_mem I v).2 hvdiv, rfl⟩
  · intro hPfin
    have hPfin' : ∃ v, v ∈ rf_qs_support I ∧ v.asIdeal = P := by
      simpa only [Finset.mem_image] using hPfin
    rcases hPfin' with ⟨v, hv, hEq⟩
    subst P
    apply Multiset.mem_toFinset.mpr
    apply (Ideal.mem_normalizedFactors_iff hI).2
    constructor
    · exact v.isPrime
    · exact (Ideal.dvd_iff_le).mp ((rf_qs_support_mem I v).mp hv)

private lemma rf_qs_support_factorization {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) :
    (∏ v ∈ rf_qs_support I, v.asIdeal) = I.1 := by
  classical
  have hI : I.1 ≠ ⊥ := rf_qs_ext_ne_bot I
  let nf := UniqueFactorizationMonoid.normalizedFactors I.1
  let T := rf_qs_support I
  have hnodup : nf.Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI).mp I.2.2
  have hcount (P : Ideal (𝓞 F)) (hP : P ∈ nf.toFinset) : nf.count P = 1 := by
    have hpos : 0 < nf.count P := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hP)
    have hle := (Multiset.nodup_iff_count_le_one.mp hnodup) P
    omega
  have hprodNF : nf.prod = ∏ P ∈ nf.toFinset, P := by
    rw [Finset.prod_multiset_count]
    apply Finset.prod_congr rfl
    intro P hP
    rw [hcount P hP, pow_one]
  have hinj : Set.InjOn (fun v : ArtinPrimitiveRoots.A1.FinPlace F => v.asIdeal)
      (T : Set (ArtinPrimitiveRoots.A1.FinPlace F)) := by
    intro v hv w hw h
    exact HeightOneSpectrum.ext h
  have hprodImage :
      (∏ P ∈ nf.toFinset, P) = ∏ v ∈ T, v.asIdeal := by
    rw [rf_qs_support_normalizedFactors I]
    exact Finset.prod_image hinj
  calc
    (∏ v ∈ T, v.asIdeal) = nf.prod := by rw [hprodNF, ← hprodImage]
    _ = I.1 := Ideal.prod_normalizedFactors_eq_self hI

private lemma rf_qs_support_norm {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) :
    (normT (rf_qs_support I) : ℝ) = idealNorm I.1 := by
  have hprod := rf_qs_support_factorization I
  have hnorm : normT (rf_qs_support I) = Ideal.absNorm I.1 := by
    calc
      normT (rf_qs_support I) = Ideal.absNorm (∏ v ∈ rf_qs_support I, v.asIdeal) := by
        simp [normT, map_prod]
      _ = Ideal.absNorm I.1 := by rw [hprod]
  simpa [idealNorm] using congrArg (fun n : ℕ => (n : ℝ)) hnorm

private lemma rf_chiIdealPow_support (D : ArtinPrimitiveRoots.A1.FieldData F)
    {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) (x : F) (j : ℤ) :
    ArtinPrimitiveRoots.A1.chiIdealPow D I.1 x j =
      ∏ v ∈ rf_qs_support I, ArtinPrimitiveRoots.A1.chiPow D v x j := by
  classical
  let nf := UniqueFactorizationMonoid.normalizedFactors I.1
  let T := rf_qs_support I
  have hI : I.1 ≠ ⊥ := rf_qs_ext_ne_bot I
  have hnodup : nf.Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI).mp I.2.2
  have hcount (P : Ideal (𝓞 F)) (hP : P ∈ nf.toFinset) : nf.count P = 1 := by
    have hpos : 0 < nf.count P := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hP)
    have hle := (Multiset.nodup_iff_count_le_one.mp hnodup) P
    omega
  let f : Ideal (𝓞 F) → ℂ := fun P =>
    if h : P.IsPrime ∧ P ≠ ⊥ then ArtinPrimitiveRoots.A1.chiPow D ⟨P, h.1, h.2⟩ x j else 1
  have hprodMultiset : (nf.map f).prod = ∏ P ∈ nf.toFinset, f P := by
    rw [Finset.prod_multiset_map_count]
    apply Finset.prod_congr rfl
    intro P hP
    rw [hcount P hP, pow_one]
  have hinj : Set.InjOn (fun v : ArtinPrimitiveRoots.A1.FinPlace F => v.asIdeal)
      (T : Set (ArtinPrimitiveRoots.A1.FinPlace F)) := by
    intro v hv w hw h
    exact HeightOneSpectrum.ext h
  calc
    ArtinPrimitiveRoots.A1.chiIdealPow D I.1 x j = (nf.map f).prod := by
      simp [ArtinPrimitiveRoots.A1.chiIdealPow, nf, f]
    _ = ∏ P ∈ nf.toFinset, f P := hprodMultiset
    _ = ∏ v ∈ T, f v.asIdeal := by
      rw [rf_qs_support_normalizedFactors I]
      exact Finset.prod_image hinj
    _ = ∏ v ∈ T, ArtinPrimitiveRoots.A1.chiPow D v x j := by
      apply Finset.prod_congr rfl
      intro v hv
      have hprime : v.asIdeal.IsPrime := v.isPrime
      have hne : v.asIdeal ≠ ⊥ := v.ne_bot
      simp [f, hprime, hne]

private lemma rf_qs_count_spanSingleton_div (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) -
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv]
  ring

private lemma rf_qs_count_spanSingleton_int (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (a : 𝓞 F) (ha : a ≠ 0) :
    FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (algebraMap (𝓞 F) F a)) =
        -WithZero.log (v.intValuation a) := by
  have hspan : (Ideal.span {a} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using ha
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg ha, WithZero.log_exp]
  ring

private lemma rf_qs_count_spanSingleton_log (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (z : F) (hz : z ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
      -WithZero.log (HeightOneSpectrum.valuation F v z) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
  have hn : n ≠ 0 := by
    intro hn
    apply hz
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : (algebraMap (𝓞 F) F n) ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hmapd : (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hval : HeightOneSpectrum.valuation F v z = v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    rf_qs_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    rf_qs_count_spanSingleton_int v n hn,
    rf_qs_count_spanSingleton_int v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private lemma rf_qs_isGen_mem_R {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    {I : Ideal (𝓞 F)} {c : F} (hc : S.IsGen c I) : c ∈ S.R := by
  change ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
    HeightOneSpectrum.valuation F v c ≤ 1
  intro v hv
  have hcount : 0 ≤ FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) := by
    rw [hc.2.2 v hv]
    exact FractionalIdeal.count_coe_nonneg F v I
  have hlog : WithZero.log (HeightOneSpectrum.valuation F v c) ≤ 0 := by
    rw [rf_qs_count_spanSingleton_log v c hc.2.1] at hcount
    linarith
  simpa using WithZero.le_exp_of_log_le hlog

private lemma rf_qs_idealExp_ne_zero_iff_dvd (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) :
    ArtinPrimitiveRoots.A1.idealExp v J ≠ 0 ↔ v.asIdeal ∣ J := by
  have hJ0 : J ≠ 0 := by simpa [Ideal.zero_eq_bot] using hJ
  exact Associates.count_ne_zero_iff_dvd hJ0 v.irreducible

set_option maxHeartbeats 800000 in
private lemma rf_qs_integral_generator_valid (D : ArtinPrimitiveRoots.A1.FieldData F)
    {S : ArtinPrimitiveRoots.A1.SData F CE condη} (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S)
    (c : Fˣ) (hc : S.IsGen (c : F) I.1) (b a : 𝓞 F) (hb : b ≠ 0)
    (hresB : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      ArtinPrimitiveRoots.A1.residue v (b : F) ≠ 0)
    (ha : (a : F) = (c : F) * (b : F) ^ 2) :
    ArtinPrimitiveRoots.A2.IsExteriorGenerator S.Sf (rf_qs_support I) a := by
  classical
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hbF : (b : F) ≠ 0 := by
    intro h
    apply hb
    apply (IsFractionRing.injective (𝓞 F) F)
    simpa [map_zero] using h
  have ha0 : a ≠ 0 := by
    intro hz
    have hzero : (c : F) * (b : F) ^ 2 = 0 := by rw [← ha, hz]; simp
    exact (mul_ne_zero c.ne_zero (pow_ne_zero 2 hbF)) hzero
  have hspanA0 : (Ideal.span {a} : Ideal (𝓞 F)) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using ha0
  have hspanB0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbF
  have hspanC0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr c.ne_zero
  have hspanA : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F) *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) ^ 2 := by
    rw [ha, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.spanSingleton_pow]
  have hCountA (v : ArtinPrimitiveRoots.A1.FinPlace F) :
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
        FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) +
          2 * FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) := by
    rw [hspanA, FractionalIdeal.count_mul F v hspanC0
      (pow_ne_zero 2 hspanB0), FractionalIdeal.count_pow]
    ring
  have hcountBzero (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) = 0 := by
    have hbnot : b ∉ v.asIdeal := by
      intro hbv
      have hzero : ArtinPrimitiveRoots.A1.residue v (b : F) = 0 := by
        rw [SB.residue_algebraMap]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hbv
      exact (hresB v hv) hzero
    have hbval : HeightOneSpectrum.valuation F v (b : F) = 1 :=
      (v.valuation_eq_one_iff_notMem (K := F) (r := b)).2 hbnot
    rw [rf_qs_count_spanSingleton_log v (b : F) hbF]
    simp [hbval]
  have hcountGen (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) =
        FractionalIdeal.count F v (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
    hc.2.2 v hv
  have hCountAeqI (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
      FractionalIdeal.count F v (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F v (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, hCountA v,
      hcountBzero v hv, hcountGen v hv]
    ring
  have hI0 : I.1 ≠ ⊥ := rf_qs_ext_ne_bot I
  have hcountAexp (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
      ArtinPrimitiveRoots.A1.idealExp v (Ideal.span {a}) =
        ArtinPrimitiveRoots.A1.idealExp v I.1 := by
    have hcast := hCountAeqI v hv
    rw [FractionalIdeal.count_coe F v hspanA0,
      FractionalIdeal.count_coe F v hI0] at hcast
    exact_mod_cast hcast
  have hnodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp I.2.2
  have hcountIle (v : ArtinPrimitiveRoots.A1.FinPlace F) :
      ArtinPrimitiveRoots.A1.idealExp v I.1 ≤ 1 := by
    dsimp [ArtinPrimitiveRoots.A1.idealExp]
    rw [Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot]
    exact (Multiset.nodup_iff_count_le_one.mp hnodup) v.asIdeal
  have hTmem (v : ArtinPrimitiveRoots.A1.FinPlace F) :
      v ∈ rf_qs_support I ↔ v.asIdeal ∣ I.1 := rf_qs_support_mem I v
  refine ⟨ha0, ?_⟩
  intro v hv
  have hcountNeA (hvS : v ∉ S.Sf) :
      ArtinPrimitiveRoots.A1.idealExp v (Ideal.span {a}) ≠ 0 ↔
        v.asIdeal ∣ Ideal.span {a} :=
    rf_qs_idealExp_ne_zero_iff_dvd v (Ideal.span {a}) hspanA0
  have hcountNeI (hvS : v ∉ S.Sf) :
      ArtinPrimitiveRoots.A1.idealExp v I.1 ≠ 0 ↔ v.asIdeal ∣ I.1 :=
    rf_qs_idealExp_ne_zero_iff_dvd v I.1 hI0
  have hmemSpan : a ∈ v.asIdeal ↔ v.asIdeal ∣ Ideal.span {a} := by
    constructor
    · intro haV
      apply Ideal.dvd_iff_le.mpr
      apply Ideal.span_le.mpr
      intro x hx
      have hx' : x = a := Set.mem_singleton_iff.mp hx
      rw [hx']
      exact haV
    · intro hdv
      exact (Ideal.dvd_iff_le.mp hdv) (Ideal.subset_span (Set.mem_singleton a))
  have hmemSupport : a ∈ v.asIdeal ↔ v ∈ rf_qs_support I := by
    rw [hmemSpan, ← hcountNeA hv, hcountAexp v hv, hcountNeI hv]
    exact (hTmem v).symm
  have hnotSq : a ∉ v.asIdeal ^ 2 := by
    intro haSq
    have hdiv : v.asIdeal ^ 2 ∣ Ideal.span {a} := by
      apply Ideal.dvd_iff_le.mpr
      apply Ideal.span_le.mpr
      intro x hx
      have hx' : x = a := Set.mem_singleton_iff.mp hx
      rw [hx']
      exact haSq
    have hdivA : Associates.mk v.asIdeal ^ 2 ∣ Associates.mk (Ideal.span {a}) :=
      Associates.mk_dvd_mk.mpr hdiv
    have hcountA2 : 2 ≤ ArtinPrimitiveRoots.A1.idealExp v (Ideal.span {a}) := by
      dsimp [ArtinPrimitiveRoots.A1.idealExp]
      exact (Associates.prime_pow_dvd_iff_le
        (Associates.mk_ne_zero.mpr hspanA0) v.associates_irreducible).1 hdivA
    have hcountI2 : 2 ≤ ArtinPrimitiveRoots.A1.idealExp v I.1 := by
      rw [← hcountAexp v hv]
      exact hcountA2
    have hIle := hcountIle v
    have hfalse : 2 ≤ (1 : ℕ) := le_trans hcountI2 hIle
    omega
  exact ⟨hmemSupport, hnotSq⟩

private noncomputable def rf_qs_residueUnitCard (v : ArtinPrimitiveRoots.A1.FinPlace F) : ℕ := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  exact Fintype.card ((𝓞 F ⧸ v.asIdeal)ˣ)

private lemma rf_qs_residueUnitCard_pos (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    0 < rf_qs_residueUnitCard v := by
  unfold rf_qs_residueUnitCard
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  exact Fintype.card_pos_iff.mpr ⟨1⟩

private lemma rf_qs_powered_residue_one (D : ArtinPrimitiveRoots.A1.FieldData F)
    {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (T : Finset (ArtinPrimitiveRoots.A1.FinPlace F))
    (b : 𝓞 F) (hb : ∀ v ∈ T, ArtinPrimitiveRoots.A1.residue v (b : F) ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ v ∈ T, ArtinPrimitiveRoots.A1.residue v ((b ^ n : 𝓞 F) : F) = 1 := by
  classical
  let n : ℕ := ∏ v ∈ T, rf_qs_residueUnitCard v
  have hn : 0 < n := by
    dsimp [n]
    apply Finset.prod_pos
    intro v hv
    exact rf_qs_residueUnitCard_pos v
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hres (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∈ T) :
      ArtinPrimitiveRoots.A1.residue v ((b ^ n : 𝓞 F) : F) = 1 := by
    letI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    letI : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    have hcardEq : Fintype.card ((𝓞 F ⧸ v.asIdeal)ˣ) = rf_qs_residueUnitCard v := by
      rfl
    have hcardDvd : Fintype.card ((𝓞 F ⧸ v.asIdeal)ˣ) ∣ n := by
      dsimp [n]
      exact Finset.dvd_prod_of_mem (fun w => rf_qs_residueUnitCard w) hv
    have hbres : ArtinPrimitiveRoots.A1.residue v (b : F) ≠ 0 := hb v hv
    let u : (𝓞 F ⧸ v.asIdeal)ˣ := Units.mk0 (ArtinPrimitiveRoots.A1.residue v (b : F)) hbres
    have huval : (u : 𝓞 F ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal b := by
      simpa [u] using (SB.residue_algebraMap v b)
    have hucard : u ^ Fintype.card ((𝓞 F ⧸ v.asIdeal)ˣ) = 1 :=
      pow_card_eq_one (x := u)
    obtain ⟨k, hk⟩ := hcardDvd
    have hun : u ^ n = 1 := by
      rw [hk, pow_mul, hucard, one_pow]
    calc
      ArtinPrimitiveRoots.A1.residue v ((b ^ n : 𝓞 F) : F) =
          Ideal.Quotient.mk v.asIdeal (b ^ n) := SB.residue_algebraMap v (b ^ n)
      _ = (Ideal.Quotient.mk v.asIdeal b) ^ n := by simp
      _ = (u ^ n : 𝓞 F ⧸ v.asIdeal) := by rw [← huval]
      _ = 1 := congrArg (fun x : (𝓞 F ⧸ v.asIdeal)ˣ => (x : 𝓞 F ⧸ v.asIdeal)) hun
  exact ⟨n, hn, hres⟩

set_option maxHeartbeats 800000 in
private lemma rf_qs_integral_rep (D : ArtinPrimitiveRoots.A1.FieldData F)
    {S : ArtinPrimitiveRoots.A1.SData F CE condη} (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S)
    (c : Fˣ) (hc : S.IsGen (c : F) I.1)
    (rowSupport : Finset (ArtinPrimitiveRoots.A1.FinPlace F))
    (hRowsDisjoint : Disjoint rowSupport S.Sf) :
    ∃ a : 𝓞 F,
      ArtinPrimitiveRoots.A2.IsExteriorGenerator S.Sf (rf_qs_support I) a ∧
      ∀ v ∈ rowSupport,
        ArtinPrimitiveRoots.A1.residue v (c : F) = ArtinPrimitiveRoots.A1.residue v (a : F) := by
  classical
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hcR : (c : F) ∈ S.R := rf_qs_isGen_mem_R hc
  obtain ⟨b₀, hb₀, hb₀outside, a₀, ha₀⟩ :=
    ArtinPrimitiveRoots.A2.qs_integralize_generators_NQ2 S c hcR
  have hb₀row : ∀ v ∈ rowSupport, ArtinPrimitiveRoots.A1.residue v (b₀ : F) ≠ 0 := by
    intro v hv
    have hvS : v ∉ S.Sf := by
      intro hvS
      exact (Finset.disjoint_left.mp hRowsDisjoint) hv hvS
    exact hb₀outside v hvS
  obtain ⟨n, hn, hresOne⟩ :=
    rf_qs_powered_residue_one (D := D) (S := S) rowSupport b₀ hb₀row
  let b : 𝓞 F := b₀ ^ n
  let a : 𝓞 F := a₀ * b₀ ^ (2 * (n - 1))
  have hb : b ≠ 0 := pow_ne_zero _ hb₀
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
  have hexp : 2 + 2 * (n - 1) = 2 * n := by omega
  have ha : (a : F) = (c : F) * (b : F) ^ 2 := by
    change algebraMap (𝓞 F) F (a₀ * b₀ ^ (2 * (n - 1))) =
      (c : F) * (algebraMap (𝓞 F) F (b₀ ^ n)) ^ 2
    simp only [map_mul, map_pow]
    calc
      (a₀ : F) * (b₀ : F) ^ (2 * (n - 1)) =
          (c : F) * (b₀ : F) ^ 2 * (b₀ : F) ^ (2 * (n - 1)) :=
        congrArg (fun x : F => x * (b₀ : F) ^ (2 * (n - 1))) ha₀
      _ = (c : F) * ((b₀ : F) ^ 2 * (b₀ : F) ^ (2 * (n - 1))) := by ring
      _ = (c : F) * (b₀ : F) ^ (2 + 2 * (n - 1)) := by rw [← pow_add]
      _ = (c : F) * (b₀ : F) ^ (2 * n) := by rw [hexp]
      _ = (c : F) * ((b₀ : F) ^ n) ^ 2 := by
        congr 1
        calc
          (b₀ : F) ^ (2 * n) = ((b₀ : F) ^ 2) ^ n := by rw [pow_mul]
          _ = (b₀ : F) ^ (n * 2) := by rw [← pow_mul, Nat.mul_comm]
          _ = ((b₀ : F) ^ n) ^ 2 := by rw [pow_mul]
  have hresB (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
      ArtinPrimitiveRoots.A1.residue v (b : F) ≠ 0 := by
    have hb₀res : ArtinPrimitiveRoots.A1.residue v (b₀ : F) ≠ 0 := hb₀outside v hv
    have hmk : Ideal.Quotient.mk v.asIdeal b₀ ≠ 0 := by
      simpa [SB.residue_algebraMap] using hb₀res
    have hresEq : ArtinPrimitiveRoots.A1.residue v (b : F) =
        (Ideal.Quotient.mk v.asIdeal b₀) ^ n := by
      rw [SB.residue_algebraMap]
      dsimp [b]
      simp
    rw [hresEq]
    exact pow_ne_zero n hmk
  have hgenA := rf_qs_integral_generator_valid D I c hc b a hb hresB ha
  have hresEq (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∈ rowSupport) :
      ArtinPrimitiveRoots.A1.residue v (c : F) = ArtinPrimitiveRoots.A1.residue v (a : F) := by
    have hvS : v ∉ S.Sf := by
      intro hvS
      exact (Finset.disjoint_left.mp hRowsDisjoint) hv hvS
    have hcval : HeightOneSpectrum.valuation F v (c : F) ≤ 1 := hcR v hvS
    have hbval : HeightOneSpectrum.valuation F v (b : F) ≤ 1 := v.valuation_le_one b
    have hb2val : HeightOneSpectrum.valuation F v ((b : F) ^ 2) ≤ 1 :=
      by
        rw [map_pow]
        exact pow_le_one₀ (bot_le : (0 : WithZero (Multiplicative ℤ)) ≤
          HeightOneSpectrum.valuation F v (b : F)) hbval
    have hbres1 : ArtinPrimitiveRoots.A1.residue v (b : F) = 1 := by
      simpa [b] using hresOne v hv
    have hb2res : ArtinPrimitiveRoots.A1.residue v ((b : F) ^ 2) = 1 := by
      have hcast : (b : F) ^ 2 = ((b ^ 2 : 𝓞 F) : F) := by simp
      rw [hcast, SB.residue_algebraMap]
      have hmk : Ideal.Quotient.mk v.asIdeal b = 1 := by
        simpa [SB.residue_algebraMap] using hbres1
      simp [map_pow, hmk]
    have hmul := SB.residue_mul v (c : F) ((b : F) ^ 2) hcval hb2val
    calc
      ArtinPrimitiveRoots.A1.residue v (c : F) =
          ArtinPrimitiveRoots.A1.residue v ((c : F) * (b : F) ^ 2) := by
            rw [hmul, hb2res, mul_one]
      _ = ArtinPrimitiveRoots.A1.residue v (a : F) := by rw [← ha]
  exact ⟨a, hgenA, fun v hv => hresEq v hv⟩

/-- Row elements in one fixed exterior ideal fiber. -/
def reflectionRowFiber (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (K : Set S.FSˣ) (t : S.FSˣ) (Z : ℝ) (hZ : 0 < Z)
    (I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S) : Set (ReflectionRow S) :=
  {r | InReflectionBox D S K t Z hZ r ∧ r.ideal = I}

/-- **rf:element-to-ideal** (04-reflection.tex:19-35, 1028-1029, 1225-1227).  On every fixed
compact annulus (also after a norm-one translate from the fixed compact `T`), ideal norms are
comparable to `Z^M₀`, row fibers have bounded cardinality, and the moving unit stays in a compact
norm-one set. -/
theorem rf_element_to_ideal
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (bc : BalancedChoices D S H Bd)
    (K T : Set S.FSˣ) (hK : IsCompact K) (hT : IsCompact T)
    (hTnorm : ∀ t ∈ T, S.absS (t : S.FS) = 1) :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ 0 < C ∧
      ∃ K' : Set S.FSˣ, IsCompact K' ∧ (∀ y ∈ K', S.absS (y : S.FS) = 1) ∧
        ∀ (Z : ℝ), (hZ : 2 ≤ Z) → ∀ t, t ∈ T → ∀ r : ReflectionRow S,
          InReflectionBox D S K t Z (by linarith) r →
            c₁ * Real.rpow Z M0 ≤ idealNorm r.ideal.1 ∧
            idealNorm r.ideal.1 ≤ c₂ * Real.rpow Z M0 ∧
            S.diagU (rowEpsilon S bc r) ∈ K' ∧
            Set.ncard (reflectionRowFiber D S K t Z (by linarith) r.ideal) ≤ ⌊C⌋₊ := by
  sorry

/-- **rf:moving-twist** (04-reflection.tex:37-49).  The zeroth-power convention is A1's masked
`chiPow`, so a shared prime makes both sides vanish. -/
theorem rf_moving_twist
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (bc : BalancedChoices D S H Bd)
    (r : ReflectionRow S) (J : Ideal (𝓞 F)) (hJ : S.IsExterior J)
    (a : Fˣ) (ha : S.IsGen (a : F) J ∧ Bd.Allowed a) :
    ArtinPrimitiveRoots.A1.chiIdealPow D J (rowElement S r : F) 1 =
      ArtinPrimitiveRoots.A1.chiIdealPow D J ((rowEpsilon S bc r : Fˣ) : F) 1 *
        (∏ᶠ P : ArtinPrimitiveRoots.A1.FinPlace F,
          if P.asIdeal ∣ r.ideal.1 then
            ArtinPrimitiveRoots.A1.chiPow D P (a : F) (rowPrimeExponent S r P)
          else 1) := by
  sorry

/-- **def:rf-S-character** (04-reflection.tex:51-65): `λ_ε(y)=H_S(ε,y)⁻¹`. -/
def lambdaEpsilon (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (ε : S.US) (y : S.FSˣ) : ℂ :=
  D.σ0 (((S.HS H (S.diagU ε) y)⁻¹ : Fˣ) : F)

/-- **def:rf-S-character** (04-reflection.tex:56-65): `L_υ=L_S·λ_ε` for the chosen representative
of the class `υ`. -/
def rfSCharacter (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (ϑ : ArtinPrimitiveRoots.A1.HeckeChar F) (ε : S.US) (y : S.FSˣ) : ℂ :=
  S.LS ϑ y * lambdaEpsilon D S H ε y

/-- **rf:S-character-identity** (04-reflection.tex:58-65). Includes the allowed-generator
identity, triviality on `U_S`, and dependence only on the class modulo `U_S^6`. Corrected per
sol-gate-a2 to require the combined character to be unramified outside `S`. -/
theorem rf_S_character_identity
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (Λ G η : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hΛG : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
        ArtinPrimitiveRoots.A1.gamma D S A 1 v.asIdeal p *
          ArtinPrimitiveRoots.A1.gamma D S A 2 v.asIdeal p =
            -(Λ.primeValue v * G.primeValue v))
    (ε : S.US)
    (houtside : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      (ArtinPrimitiveRoots.A1.vartheta Λ G η).UnramifiedAt v) :
    (∀ (J : Ideal (𝓞 F)) (hJ : S.IsExterior J) (a : Fˣ),
      S.IsGen (a : F) J → Bd.Allowed a →
      rfSCharacter D S H (ArtinPrimitiveRoots.A1.vartheta Λ G η) ε (S.diagU a) =
        (ArtinPrimitiveRoots.A1.vartheta Λ G η).idealValue J *
          ArtinPrimitiveRoots.A1.chiIdealPow D J ((ε : Fˣ) : F) 1) ∧
    (∀ γ : S.US, lambdaEpsilon D S H ε (S.diagU γ) = 1) ∧
    (∀ ε' : S.US, unitSixClass S ε' = unitSixClass S ε →
      ∀ y : S.FSˣ, lambdaEpsilon D S H ε' y = lambdaEpsilon D S H ε y) := by
  sorry

/-- **def:rf-mask** (04-reflection.tex:67-87): the local additive phase for the residue digits. -/
def maskPhase (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (p : Fˣ)
    (t x : 𝓞 F ⧸ P.asIdeal) : ℂ :=
  A.ψ P (algebraMap F (P.adicCompletion F)
    ((algebraMap (𝓞 F) F x.out) * (algebraMap (𝓞 F) F t.out) / (p : F)))

/-- **def:rf-mask** (04-reflection.tex:72-87): the local Gauss normalizer `τ_{p,j}`. -/
def maskTau (D : ArtinPrimitiveRoots.A1.FieldData F)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (p : Fˣ) (j : Fin 6) : ℂ :=
  ∑ᶠ v : 𝓞 F ⧸ P.asIdeal,
    if v = 0 then 0 else
      ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F v.out) ^ (-(j.1 : ℤ)) *
        maskPhase A P p 1 v

/-- **def:rf-mask** (04-reflection.tex:67-87): the normalized Gauss coefficient `α_{p,j}`. -/
def maskAlpha (D : ArtinPrimitiveRoots.A1.FieldData F)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (p : Fˣ) (j : Fin 6)
    (x : 𝓞 F ⧸ P.asIdeal) : ℂ :=
  if hj : j = 0 then
    if x = 0 then 1 - (Ideal.absNorm P.asIdeal : ℂ)⁻¹
    else - (Ideal.absNorm P.asIdeal : ℂ)⁻¹
  else if x = 0 then 0 else
    (maskTau D A P p j)⁻¹ *
      ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ))

/-- **rf:mask-identity** (04-reflection.tex:88-97): the finite Fourier transform of `α_{p,j}`
is the masked sextic character, including the zero-frequency convention at `j=0`. -/
theorem rf_mask_identity
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (hP : P ∉ S.Sf)
    (p : Fˣ) (hp : S.IsGen (p : F) P.asIdeal ∧ Bd.Allowed p) :
    ∀ (j : Fin 6) (t : 𝓞 F ⧸ P.asIdeal),
      ∑ᶠ x : 𝓞 F ⧸ P.asIdeal, maskAlpha D A P p j x * maskPhase A P p t x =
        ArtinPrimitiveRoots.A1.chiPow D P (algebraMap (𝓞 F) F t.out) (j.1 : ℤ) := by
  sorry

/-- Symbol dictionary consumed by `lem:reflection-quadratic-sieve`: cubing the sextic symbol is
the quadratic residue symbol at an exterior prime. -/
theorem chi_cube_eq_quadSymbolAt
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (h6 : (6 : 𝓞 F) ∉ P.asIdeal)
    (c : 𝓞 F) (hc : ArtinPrimitiveRoots.A1.residue P (algebraMap (𝓞 F) F c) ≠ 0) :
    ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F c) ^ 3 =
      (quadSymbolAt P c : ℂ) := by
  sorry

private lemma rf_qs_support_injective {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (I J : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S)
    (h : rf_qs_support I = rf_qs_support J) : I = J := by
  apply Subtype.ext
  calc
    I.1 = ∏ v ∈ rf_qs_support I, v.asIdeal := (rf_qs_support_factorization I).symm
    _ = ∏ v ∈ rf_qs_support J, v.asIdeal := by rw [h]
    _ = J.1 := rf_qs_support_factorization J

private def rf_qs_rows_support {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (rows : Finset (ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S)) :
    Finset (ArtinPrimitiveRoots.A1.FinPlace F) :=
  rows.biUnion rf_qs_support

private lemma rf_qs_rows_support_disjoint {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (rows : Finset (ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S)) :
    Disjoint (rf_qs_rows_support rows) S.Sf := by
  apply Finset.disjoint_left.mpr
  intro v hvrow hvS
  rcases Finset.mem_biUnion.mp hvrow with ⟨I, hI, hv⟩
  exact (Finset.disjoint_left.mp (rf_qs_support_disjoint I)) hv hvS

private lemma rf_qs_chiIdealPow_quadSymbol (D : ArtinPrimitiveRoots.A1.FieldData F)
    {S : ArtinPrimitiveRoots.A1.SData F CE condη}
    (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) (c : F) (a : 𝓞 F)
    (hres : ∀ v ∈ rf_qs_support I,
      ArtinPrimitiveRoots.A1.residue v c = ArtinPrimitiveRoots.A1.residue v (a : F)) :
    ArtinPrimitiveRoots.A1.chiIdealPow D I.1 c 3 =
      (quadSymbol (rf_qs_support I) a : ℂ) := by
  classical
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hlocal (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∈ rf_qs_support I) :
      ArtinPrimitiveRoots.A1.chiPow D v c 3 = (quadSymbolAt v a : ℂ) := by
    have hresA := hres v hv
    have h6 : (6 : 𝓞 F) ∉ v.asIdeal := by
      intro hv6
      have hvS : v ∈ S.Sf := S.over6 v hv6
      exact (Finset.disjoint_left.mp (rf_qs_support_disjoint I)) hv hvS
    by_cases hc0 : ArtinPrimitiveRoots.A1.residue v c = 0
    · rw [SB.chiPow_zero v c 3 hc0]
      have ha0 : ArtinPrimitiveRoots.A1.residue v (a : F) = 0 := by
        rw [← hresA]
        exact hc0
      have hmk : Ideal.Quotient.mk v.asIdeal a = 0 := by
        rw [← SB.residue_algebraMap v a]
        exact ha0
      have hquadZero : quadSymbolAt v a = 0 := by
        letI : v.asIdeal.IsMaximal := v.isMaximal
        letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
        letI : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
        letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
        change quadraticChar (𝓞 F ⧸ v.asIdeal) (Ideal.Quotient.mk v.asIdeal a) = 0
        exact quadraticChar_eq_zero_iff.mpr hmk
      rw [hquadZero]
      simp
    · have hcne : ArtinPrimitiveRoots.A1.residue v c ≠ 0 := hc0
      have hane : ArtinPrimitiveRoots.A1.residue v (a : F) ≠ 0 := by
        rw [← hresA]
        exact hcne
      rw [SB.chiPow_nonzero v c 3 hcne]
      calc
        ArtinPrimitiveRoots.A1.chi D v c ^ 3 =
            ArtinPrimitiveRoots.A1.chi D v (a : F) ^ 3 :=
          congrArg (fun x : ℂ => x ^ 3) (SB.chi_congr v c (a : F) hresA)
        _ = (quadSymbolAt v a : ℂ) := by
          change ArtinPrimitiveRoots.A1.chi D v (algebraMap (𝓞 F) F a) ^ 3 = _
          exact chi_cube_eq_quadSymbolAt D v h6 a (by simpa using hane)
  calc
    ArtinPrimitiveRoots.A1.chiIdealPow D I.1 c 3 =
        ∏ v ∈ rf_qs_support I, ArtinPrimitiveRoots.A1.chiPow D v c 3 :=
      rf_chiIdealPow_support D I c 3
    _ = ∏ v ∈ rf_qs_support I, (quadSymbolAt v a : ℂ) := by
      apply Finset.prod_congr rfl
      intro v hv
      exact hlocal v hv
    _ = (quadSymbol (rf_qs_support I) a : ℂ) := by
      simp [quadSymbol, map_prod]

/-- **lem:reflection-quadratic-sieve** (04-reflection.tex:941-1025): the narrow quadratic sieve
in the consumer form.  Rows and columns are squarefree exterior ideals, columns carry allowed
generators, and the symbol is A1's sextic symbol cubed. -/
theorem lem_reflection_quadratic_sieve
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ Cmax Dmax : ℝ, 1 ≤ Cmax → 1 ≤ Dmax →
        ∀ (rows cols : Finset (ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S))
          (cgen : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S → F),
          (∀ I ∈ rows, idealNorm I.1 ≤ Dmax) →
          (∀ I ∈ cols, idealNorm I.1 ≤ Cmax ∧
            ∃ c : Fˣ, (c : F) = cgen I ∧ S.IsGen (c : F) I.1 ∧ Bd.Allowed c) →
          ∀ z : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S → ℂ,
            ∑ I ∈ rows,
              ‖∑ J ∈ cols, z J *
                ArtinPrimitiveRoots.A1.chiIdealPow D (I.1) (cgen J) 3‖ ^ 2 ≤
              C * (Cmax + Dmax) * Real.rpow (Cmax * Dmax) ε *
                ∑ J ∈ cols, ‖z J‖ ^ 2 := by
  classical
  intro ε hε
  have hS : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      (2 : 𝓞 F) ∈ v.asIdeal → v ∈ S.Sf := by
    intro v hv2
    apply S.over6 v
    rw [show (6 : 𝓞 F) = (3 : 𝓞 F) * 2 by norm_num]
    exact Ideal.mul_mem_left _ _ hv2
  obtain ⟨C, hC, hNarrow⟩ :=
    narrow_quadratic_large_sieve (K := F) ⟨D.ζ12, D.hζ12⟩ S.Sf hS ε hε
  refine ⟨C, hC, ?_⟩
  intro Cmax Dmax hCmax hDmax rows cols cgen hrows hcols z
  let rowSupports := rows.image rf_qs_support
  let colSupports := cols.image rf_qs_support
  have hrowinj : Set.InjOn rf_qs_support
      (rows : Set (ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S)) := by
    intro I hI J hJ hIJ
    exact rf_qs_support_injective I J hIJ
  have hcolinj : Set.InjOn rf_qs_support
      (cols : Set (ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S)) := by
    intro I hI J hJ hIJ
    exact rf_qs_support_injective I J hIJ
  have hrowSupportDisjoint : Disjoint (rf_qs_rows_support rows) S.Sf :=
    rf_qs_rows_support_disjoint rows
  have hrowsNarrow : ∀ T ∈ rowSupports,
      Disjoint T S.Sf ∧ (normT T : ℝ) ≤ Dmax := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨I, hI, rfl⟩
    refine ⟨rf_qs_support_disjoint I, ?_⟩
    rw [rf_qs_support_norm I]
    exact hrows I hI
  let colRep : ∀ T, T ∈ colSupports → ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S :=
    fun T hT => Classical.choose (Finset.mem_image.mp hT)
  have hcolRepSpec (T : Finset (ArtinPrimitiveRoots.A1.FinPlace F)) (hT : T ∈ colSupports) :
      colRep T hT ∈ cols ∧ rf_qs_support (colRep T hT) = T := by
    exact Classical.choose_spec (Finset.mem_image.mp hT)
  let colUnit : ∀ T, (hT : T ∈ colSupports) → Fˣ := fun T hT =>
    Classical.choose (hcols (colRep T hT) (hcolRepSpec T hT).1).2
  have hcolUnitSpec (T : Finset (ArtinPrimitiveRoots.A1.FinPlace F))
      (hT : T ∈ colSupports) :
      ((colUnit T hT : Fˣ) : F) = cgen (colRep T hT) ∧
        S.IsGen (colUnit T hT : F) (colRep T hT).1 ∧ Bd.Allowed (colUnit T hT) := by
    exact Classical.choose_spec (hcols (colRep T hT) (hcolRepSpec T hT).1).2
  have hIntegralExists (T : Finset (ArtinPrimitiveRoots.A1.FinPlace F))
      (hT : T ∈ colSupports) :
      ∃ a : 𝓞 F, IsExteriorGenerator S.Sf T a ∧
        ∀ v ∈ rf_qs_rows_support rows,
          ArtinPrimitiveRoots.A1.residue v (cgen (colRep T hT)) =
            ArtinPrimitiveRoots.A1.residue v (a : F) := by
    let I := colRep T hT
    let c := colUnit T hT
    obtain ⟨a, ha, hres⟩ :=
      rf_qs_integral_rep D I c (hcolUnitSpec T hT).2.1
        (rf_qs_rows_support rows) hrowSupportDisjoint
    refine ⟨a, ?_, ?_⟩
    · rw [← (hcolRepSpec T hT).2]
      exact ha
    · intro v hv
      rw [← (hcolUnitSpec T hT).1]
      exact hres v hv
  let integralData : ∀ T, (hT : T ∈ colSupports) → 𝓞 F := fun T hT =>
    Classical.choose (hIntegralExists T hT)
  have hIntegralDataSpec (T : Finset (ArtinPrimitiveRoots.A1.FinPlace F))
      (hT : T ∈ colSupports) :
      IsExteriorGenerator S.Sf T (integralData T hT) ∧
        ∀ v ∈ rf_qs_rows_support rows,
          ArtinPrimitiveRoots.A1.residue v (cgen (colRep T hT)) =
            ArtinPrimitiveRoots.A1.residue v (integralData T hT : F) := by
    exact Classical.choose_spec (hIntegralExists T hT)
  let gen : Finset (ArtinPrimitiveRoots.A1.FinPlace F) → 𝓞 F := fun T =>
    if hT : T ∈ colSupports then integralData T hT else 0
  let z' : Finset (ArtinPrimitiveRoots.A1.FinPlace F) → ℂ := fun T =>
    if hT : T ∈ colSupports then z (colRep T hT) else 0
  have hgenSpec (T : Finset (ArtinPrimitiveRoots.A1.FinPlace F)) (hT : T ∈ colSupports) :
      IsExteriorGenerator S.Sf T (gen T) ∧
        ∀ v ∈ rf_qs_rows_support rows,
          ArtinPrimitiveRoots.A1.residue v (cgen (colRep T hT)) =
            ArtinPrimitiveRoots.A1.residue v (gen T : F) := by
    simpa [gen, hT] using hIntegralDataSpec T hT
  have hcolRepEq (J : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) (hJ : J ∈ cols) :
      colRep (rf_qs_support J) (Finset.mem_image.mpr ⟨J, hJ, rfl⟩) = J := by
    have hT : rf_qs_support J ∈ colSupports :=
      Finset.mem_image.mpr ⟨J, hJ, rfl⟩
    apply rf_qs_support_injective
    exact (hcolRepSpec (rf_qs_support J) hT).2
  have hzRep (J : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) (hJ : J ∈ cols) :
      z' (rf_qs_support J) = z J := by
    have hT : rf_qs_support J ∈ colSupports :=
      Finset.mem_image.mpr ⟨J, hJ, rfl⟩
    simp only [z', dif_pos hT]
    rw [hcolRepEq J hJ]
  have hcolsNarrow : ∀ T ∈ colSupports,
      Disjoint T S.Sf ∧ (normT T : ℝ) ≤ Cmax ∧ IsExteriorGenerator S.Sf T (gen T) := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨J, hJ, rfl⟩
    refine ⟨rf_qs_support_disjoint J, ?_, (hgenSpec _ hT).1⟩
    rw [rf_qs_support_norm J]
    exact (hcols J hJ).1
  have hNarrowApplied :=
    hNarrow Cmax Dmax hCmax hDmax gen colSupports rowSupports hcolsNarrow hrowsNarrow z'
  have hmatrix (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) (hI : I ∈ rows)
      (J : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) (hJ : J ∈ cols) :
      (quadSymbol (rf_qs_support I) (gen (rf_qs_support J)) : ℂ) =
        ArtinPrimitiveRoots.A1.chiIdealPow D I.1 (cgen J) 3 := by
    let T := rf_qs_support J
    have hT : T ∈ colSupports := Finset.mem_image.mpr ⟨J, hJ, rfl⟩
    have hrep : colRep T hT = J := by
      apply rf_qs_support_injective
      exact (hcolRepSpec T hT).2
    have hresData := (hIntegralDataSpec T hT).2
    rw [hrep] at hresData
    have hres : ∀ v ∈ rf_qs_support I,
        ArtinPrimitiveRoots.A1.residue v (cgen J) =
          ArtinPrimitiveRoots.A1.residue v (gen T : F) := by
      intro v hv
      have hvRows : v ∈ rf_qs_rows_support rows :=
        Finset.mem_biUnion.mpr ⟨I, hI, hv⟩
      simpa [T, gen, hT] using hresData v hvRows
    exact (rf_qs_chiIdealPow_quadSymbol D I (cgen J) (gen T) hres).symm
  have hinner (I : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S) (hI : I ∈ rows) :
      (∑ T ∈ colSupports,
        z' T * (quadSymbol (rf_qs_support I) (gen T) : ℂ)) =
        ∑ J ∈ cols, z J * ArtinPrimitiveRoots.A1.chiIdealPow D I.1 (cgen J) 3 := by
    rw [Finset.sum_image hcolinj]
    refine Finset.sum_congr rfl ?_
    intro J hJ
    rw [hzRep J hJ, hmatrix I hI J hJ]
  have hrowsum :
      (∑ T ∈ rowSupports,
        ‖∑ U ∈ colSupports, z' U * (quadSymbol T (gen U) : ℂ)‖ ^ 2) =
        ∑ I ∈ rows,
          ‖∑ J ∈ cols, z J * ArtinPrimitiveRoots.A1.chiIdealPow D I.1 (cgen J) 3‖ ^ 2 := by
    rw [Finset.sum_image hrowinj]
    refine Finset.sum_congr rfl ?_
    intro I hI
    exact congrArg (fun x : ℂ => ‖x‖ ^ 2) (hinner I hI)
  have hcoeff :
      (∑ T ∈ colSupports, ‖z' T‖ ^ 2) = ∑ J ∈ cols, ‖z J‖ ^ 2 := by
    rw [Finset.sum_image hcolinj]
    refine Finset.sum_congr rfl ?_
    intro J hJ
    rw [hzRep J hJ]
  rw [hrowsum, hcoeff] at hNarrowApplied
  exact hNarrowApplied

/-- **def:rf-active** (04-reflection.tex:433-499): a squarefree active ideal `𝔣|rad(𝔥)` must
contain every row prime whose exponent modulo six is nonzero. -/
def IsActiveFactor (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (r : ReflectionRow S) (f : Ideal (𝓞 F)) : Prop :=
  S.IsExterior f ∧ Squarefree f ∧
    (∀ P : ArtinPrimitiveRoots.A1.FinPlace F, P.asIdeal ∣ f → P.asIdeal ∣ r.h.1) ∧
    (∀ P : ArtinPrimitiveRoots.A1.FinPlace F, P.asIdeal ∣ r.h.1 →
      rowPrimeExponent S r P ≠ 0 → P.asIdeal ∣ f)

/-- **def:rf-active** (04-reflection.tex:478-499): the local Weyl coefficient envelope `β_p(e)`.
Corrected per rev-a2 to require the prime-norm domain `1 < q`. -/
def betaPrime (q : ℝ) (_hq : 1 < q) (e : ℕ) : ℝ :=
  if e = 0 then 1
  else if e % 3 = 1 then Real.rpow q (-((e / 3 : ℕ) : ℝ))
  else if e % 3 = 0 then Real.rpow q (1 / 2 - ((e / 3 : ℕ) : ℝ))
  else 0

/-- **def:rf-active** (04-reflection.tex:478-499): the local Euler sum for `β_p`. Corrected per
rev-a2 to require both `1 < q` and a summability proof. -/
def betaEulerFactor (q : ℝ) (hq : 1 < q) (σ : ℝ)
    (_hsum : Summable (fun e : ℕ =>
      ((betaPrime q hq e * Real.rpow q (-(σ * (e : ℝ))) : ℝ) : ℂ))) : ℂ :=
  ∑' e : ℕ,
    ((betaPrime q hq e * Real.rpow q (-(σ * (e : ℝ))):ℝ) : ℂ)

/-- **rf:active-support** (04-reflection.tex:433-503): for a squarefree `𝔣|rad(𝔥)`,
`q_𝔣² ≤ q_𝔥`. -/
theorem rf_active_support_norm
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (r : ReflectionRow S) (f : Ideal (𝓞 F))
    (hf : IsActiveFactor S r f) :
    (Ideal.absNorm f : ℝ) ^ 2 ≤ (Ideal.absNorm r.h.1 : ℝ) := by
  sorry

/-- **rf:powerful-count** (04-reflection.tex:1035-1044): powerful exterior ideals have count
`O_F(P^{1/2})` below norm `2P`. -/
def powerfulExteriorIdeals (S : ArtinPrimitiveRoots.A1.SData F CE condη) (P : ℝ) :
    Finset (Ideal (𝓞 F)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊2 * P⌋₊).toFinset).filter
    (fun I => S.IsExterior I ∧ IsPowerful I)

/-- **rf:powerful-count** (04-reflection.tex:1035-1044). -/
theorem rf_powerful_count
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      (powerfulExteriorIdeals S P).card ≤ C * Real.rpow P (1 / 2 : ℝ) := by
  sorry

/-- **def:rf-column-cutoff** (04-reflection.tex:915-931): `𝓛=8D²P/Z`. -/
def reflectionColumnLength (P D Z : ℝ) : ℝ := 8 * D ^ 2 * P / Z

/-- **def:rf-column-cutoff** (04-reflection.tex:915-931): `R₀=Z^δ𝓛`. -/
def reflectionColumnCutoff (P D Z δ : ℝ) : ℝ :=
  Real.rpow Z δ * reflectionColumnLength P D Z

end ArtinPrimitiveRoots.A2
