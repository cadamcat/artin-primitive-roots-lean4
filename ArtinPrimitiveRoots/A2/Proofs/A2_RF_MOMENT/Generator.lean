import ArtinPrimitiveRoots.A2.Reflection.Missing
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».All

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rf_mom_p

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem count_spanSingleton_div (v : FinPlace F) (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
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

private lemma chiPow_sixUS (D : FieldData F) (S : SData F CE condη)
    (v : FinPlace F) (hv : v ∉ S.Sf) (e : S.US)
    (he : residue v ((e : Fˣ) : F) ≠ 0) :
    chiPow D v ((e : Fˣ) : F) 2 ^ 6 = 1 := by
  let SB := a2_bridge_SYMBOL D S
  have hchi2 : chiPow D v ((e : Fˣ) : F) 2 =
      chi D v ((e : Fˣ) : F) ^ (2 : ℕ) := by
    rw [SB.chiPow_nonzero v ((e : Fˣ) : F) 2 he]
    rfl
  have h6 := SB.chi_six v ((e : Fˣ) : F) he
  calc
    chiPow D v ((e : Fˣ) : F) 2 ^ 6 =
        (chi D v ((e : Fˣ) : F) ^ (2 : ℕ)) ^ 6 := by rw [hchi2]
    _ = chi D v ((e : Fˣ) : F) ^ (2 * 6) := by rw [← pow_mul]
    _ = chi D v ((e : Fˣ) : F) ^ 12 := by norm_num
    _ = (chi D v ((e : Fˣ) : F) ^ 6) ^ 2 := by
      rw [show (12 : ℕ) = 6 * 2 by norm_num, pow_mul]
    _ = 1 := by rw [h6]; norm_num

private lemma chi_one_of_exterior (D : FieldData F) (S : SData F CE condη)
    (v : FinPlace F) (hv : v ∉ S.Sf) : chi D v 1 = 1 := by
  let SB := a2_bridge_SYMBOL D S
  have hval : HeightOneSpectrum.valuation F v (1 : F) = 1 := by simp
  have hres : residue v (1 : F) ≠ 0 :=
    (SB.residue_ne_zero v 1 (by simp [hval])).2 hval
  have hnorm := SB.chi_norm v 1 hres
  have hne : chi D v 1 ≠ 0 := by
    intro hz
    rw [hz] at hnorm
    norm_num at hnorm
  have hmul := SB.chi_mul v hv 1 1 (by simp [hval]) (by simp [hval])
  have hmul' : chi D v 1 * chi D v 1 = chi D v 1 * 1 := by simpa using hmul.symm
  exact mul_left_cancel₀ hne hmul'

private theorem chiIdealPow_sixUS (D : FieldData F) (S : SData F CE condη)
    (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (e : S.US) :
    chiIdealPow D I ((e : Fˣ) ^ 6 : F) 2 = 1 := by
  classical
  let SB := a2_bridge_SYMBOL D S
  have hval (v : FinPlace F) (hv : v ∉ S.Sf) :
      HeightOneSpectrum.valuation F v ((e : Fˣ) : F) = 1 :=
    Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F) e hv
  have hval_le (v : FinPlace F) (hv : v ∉ S.Sf) (n : ℕ) :
      HeightOneSpectrum.valuation F v (((e : Fˣ) : F) ^ n) ≤ 1 := by
    rw [map_pow, hval v hv]
    simp
  have hres (v : FinPlace F) (hv : v ∉ S.Sf) :
      residue v ((e : Fˣ) : F) ≠ 0 :=
    (SB.residue_ne_zero v ((e : Fˣ) : F)
      (by simp [hval v hv])).2 (hval v hv)
  have hunit : chiIdealPow D I (1 : F) 2 = 1 := by
    unfold chiIdealPow
    apply Multiset.prod_eq_one
    intro x hx
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hx
    by_cases hp : P.IsPrime ∧ P ≠ ⊥
    · simp only [dif_pos hp]
      let v : FinPlace F := ⟨P, hp.1, hp.2⟩
      have hvdiv : v.asIdeal ∣ I :=
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
      have hv : v ∉ S.Sf := by
        intro hvS
        exact hI.2 v hvS ((Ideal.dvd_iff_le).mp hvdiv)
      have hres₁ : residue v (1 : F) ≠ 0 :=
        (SB.residue_ne_zero v 1 (by norm_num)).2 (by norm_num)
      rw [SB.chiPow_nonzero v 1 2 hres₁, chi_one_of_exterior D S v hv]
      norm_num
    · simp [hp]
  have hbase : chiIdealPow D I ((e : Fˣ) : F) 2 ^ 6 = 1 := by
    unfold chiIdealPow
    rw [← Multiset.prod_map_pow]
    apply Multiset.prod_eq_one
    intro x hx
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hx
    by_cases hp : P.IsPrime ∧ P ≠ ⊥
    · simp only [dif_pos hp]
      let v : FinPlace F := ⟨P, hp.1, hp.2⟩
      have hvdiv : v.asIdeal ∣ I :=
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
      have hv : v ∉ S.Sf := by
        intro hvS
        exact hI.2 v hvS ((Ideal.dvd_iff_le).mp hvdiv)
      exact chiPow_sixUS D S v hv e (hres v hv)
    · simp [hp]
  have hpow : ∀ n : ℕ,
      chiIdealPow D I (((e : Fˣ) : F) ^ n) 2 =
        chiIdealPow D I ((e : Fˣ) : F) 2 ^ n := by
    intro n
    induction n with
    | zero =>
        simpa using hunit
    | succ n ih =>
        rw [pow_succ]
        rw [SB.ideal_element_mul I hI (((e : Fˣ) : F) ^ n) ((e : Fˣ) : F) 2]
        · rw [ih]
          simp [pow_succ]
        · intro v hvdiv
          have hvS : v ∉ S.Sf := by
            intro hvS
            exact hI.2 v hvS ((Ideal.dvd_iff_le).mp hvdiv)
          exact ⟨hval_le v hvS n, by simp [hval v hvS]⟩
  calc
    chiIdealPow D I ((e : Fˣ) ^ 6 : F) 2 =
        chiIdealPow D I ((e : Fˣ) : F) 2 ^ 6 := by
      simpa using hpow 6
    _ = 1 := hbase

private theorem gamma_top_eq_one (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (d : Fˣ) (hd : S.IsGen (d : F) ⊤) :
    gamma D S A 2 ⊤ (d : F) = 1 := by
  classical
  let SB := a2_bridge_SYMBOL D S
  have htop : S.IsExterior (⊤ : Ideal (𝓞 F)) := hd.1
  have hpair := (S.e_pairing_perfect D A ⊤ htop (d : F) hd).1
  have hterm (x : 𝓞 F ⧸ (⊤ : Ideal (𝓞 F))) :
      chiIdealPow D ⊤ (algebraMap (𝓞 F) F x.out) 2 *
        S.e A (S.diag (algebraMap (𝓞 F) F x.out / (d : F))) = 1 := by
    rw [SB.ideal_one]
    have he := hpair 1 (by simp) x.out
    have he' : S.e A (S.diag (algebraMap (𝓞 F) F x.out / (d : F))) = 1 := by
      simpa using he
    simp [he']
  letI : Unique (𝓞 F ⧸ (⊤ : Ideal (𝓞 F))) := {
    default := 0
    uniq := fun x => Subsingleton.elim _ _
  }
  letI : Fintype (𝓞 F ⧸ (⊤ : Ideal (𝓞 F))) :=
    Fintype.ofFinite (𝓞 F ⧸ (⊤ : Ideal (𝓞 F)))
  have hsum : (∑ᶠ x : 𝓞 F ⧸ (⊤ : Ideal (𝓞 F)), (1 : ℂ)) = 1 := by
    rw [finsum_eq_finsetSum_of_support_subset
      (fun _ : 𝓞 F ⧸ (⊤ : Ideal (𝓞 F)) => (1 : ℂ))
      (s := Finset.univ) (by intro x hx; exact Finset.mem_univ x)]
    simp
  unfold gamma
  rw [finsum_congr hterm, hsum]
  simp

/-- The normalized Gauss factor is unchanged when an allowed generator is changed by a sixth
power of an S-unit. -/
theorem gamma_generator_invariant
    (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (A : AddCharData F)
    (I : S.SqfExtIdeal) (a b : Fˣ)
    (ha : S.IsGen (a : F) I.1 ∧ Bd.Allowed a)
    (hb : S.IsGen (b : F) I.1 ∧ Bd.Allowed b) :
    gamma D S A 2 I.1 (a : F) = gamma D S A 2 I.1 (b : F) := by
  classical
  let SB := a2_bridge_SYMBOL D S
  obtain ⟨e, heUS, heq⟩ := Bd.allowed_unique I.1 a b ha hb
  let eUS : S.US := ⟨e, heUS⟩
  let dUS : S.US := eUS ^ 6
  let d : Fˣ := dUS
  have hd_eq : d = a / b := by
    rw [show a = (e : Fˣ) ^ 6 * b by exact heq]
    simp [d, dUS, eUS]
  have hdF : (d : F) = (a : F) / (b : F) := by
    simpa using congrArg (fun x : Fˣ => (x : F)) hd_eq
  have htop : S.IsExterior (⊤ : Ideal (𝓞 F)) := by
    refine ⟨top_ne_bot, ?_⟩
    intro v hv hle
    exact v.isPrime.ne_top (top_le_iff.mp hle)
  have hdgen : S.IsGen (d : F) ⊤ := by
    refine ⟨htop, Units.ne_zero d, ?_⟩
    intro v hv
    rw [hdF, count_spanSingleton_div v (a : F) (b : F)
      (Units.ne_zero a) (Units.ne_zero b)]
    rw [ha.1.2.2 v hv, hb.1.2.2 v hv]
    simpa using (FractionalIdeal.count_one F v).symm
  have hdallowed : Bd.Allowed d := by
    change (QuotientGroup.mk (S.diagU d) : S.V) ∈ Bd.B
    have hdiag : S.diagU d = (S.diagU (eUS : Fˣ)) ^ 6 := by
      simp [d, dUS, map_pow]
    rw [hdiag]
    have hq : (QuotientGroup.mk ((S.diagU (eUS : Fˣ)) ^ 6) : S.V) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨S.diagU (eUS : Fˣ), rfl⟩
    rw [hq]
    exact Bd.B.one_mem
  have hIext : S.IsExterior I.1 := I.2.1
  have hχI : chiIdealPow D I.1 (d : F) 2 = 1 := by
    simpa [d, dUS, eUS] using chiIdealPow_sixUS D S I.1 hIext eUS
  have hcop : IsCoprime I.1 ⊤ := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    simp
  have hcrt := gamma_crt D S A H Bd 2 I.1 ⊤ hIext htop I.2.2
    (by simp) hcop b d hb ⟨hdgen, hdallowed⟩
  have hcrt' : gamma D S A 2 I.1 ((b : F) * (d : F)) =
      gamma D S A 2 I.1 (b : F) := by
    rw [Ideal.mul_top] at hcrt
    rw [hχI, SB.ideal_one, gamma_top_eq_one D S A d hdgen] at hcrt
    simpa using hcrt
  have haeq : (a : F) = (b : F) * (d : F) := by
    rw [heq]
    simp [d, dUS, eUS, mul_comm]
  rw [haeq]
  exact hcrt'

theorem reflection_Bm_eq_balanced
    (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (A : AddCharData F)
    (ϑ : HeckeChar F) (bc : BalancedChoices D S H Bd)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (v0 : InfinitePlace F)
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (inputGen : S.SqfExtIdeal → F)
    (hcgen : ∀ I, ∃ c : Fˣ, (c : F) = inputGen I ∧
      S.IsGen (c : F) I.1 ∧ Bd.Allowed c)
    (m : F) (Z : ℝ) :
    Bm D S A ϑ inputGen m Z = Bm D S A ϑ (ArtinPrimitiveRoots.A2.cgen R) m Z := by
  classical
  unfold Bm
  refine tsum_congr ?_
  intro p
  obtain ⟨a, haEq, haGen, haAllowed⟩ := hcgen p.1
  obtain ⟨b, hbEq, hbGen, hbAllowed⟩ := cgen_valid R p.1
  have hγ := gamma_generator_invariant D S H Bd A p.1 a b
    ⟨haGen, haAllowed⟩ ⟨hbGen, hbAllowed⟩
  have hγ' : gamma D S A 2 p.1.1 (inputGen p.1) =
      gamma D S A 2 p.1.1 (ArtinPrimitiveRoots.A2.cgen R p.1) := by
    rw [← haEq, ← hbEq]
    exact hγ
  simp only [hγ']

end ArtinPrimitiveRoots.Proofs.a2_rf_mom_p
