import ArtinPrimitiveRoots.Proofs.a2_cond_lead_p.ConductorGenerator

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical nonZeroDivisors
noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private noncomputable def conductorClassPowerGen (v : A1.FinPlace F) : 𝓞 F :=
  Classical.choose (conductorDenominatorIdeal_pow_principal v.asIdeal v.ne_bot)

private theorem conductorClassPowerGen_spec (v : A1.FinPlace F) :
    Ideal.span {conductorClassPowerGen v} =
      v.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) :=
  Classical.choose_spec (conductorDenominatorIdeal_pow_principal v.asIdeal v.ne_bot)

private theorem conductorClassPowerGen_ne_zero (v : A1.FinPlace F) :
    conductorClassPowerGen v ≠ 0 := by
  intro h
  have hbot : v.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) = ⊥ := by
    simpa [h] using (conductorClassPowerGen_spec v).symm
  exact (pow_ne_zero _ v.ne_bot) hbot

private theorem conductorClassPowerGen_map_ne_zero (v : A1.FinPlace F) :
    (conductorClassPowerGen v : F) ≠ 0 := by
  intro h
  exact conductorClassPowerGen_ne_zero v
    ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))

private noncomputable def conductorFiniteCorrectionExponent
    (c : Fˣ) (v : A1.FinPlace F) : ℤ :=
  -((FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F))) /
      (Fintype.card (ClassGroup (𝓞 F)) : ℤ))

private theorem conductor_spanSingleton_zpow {x : F} (hx : x ≠ 0) (k : ℤ) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x ^ k) =
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) ^ k := by
  cases k with
  | ofNat n => simp [zpow_natCast, FractionalIdeal.spanSingleton_pow]
  | negSucc n =>
      simp [zpow_negSucc, FractionalIdeal.spanSingleton_pow,
        FractionalIdeal.spanSingleton_inv]

private theorem conductor_spanSingleton_finset_prod {α : Type*} (s : Finset α)
    (u : α → Fˣ) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
        (∏ i ∈ s, (u i : F)) =
      ∏ i ∈ s, FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (u i : F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      calc
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            ((u i : F) * ∏ x ∈ s, (u x : F)) =
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (u i : F) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (∏ x ∈ s, (u x : F)) :=
              (FractionalIdeal.spanSingleton_mul_spanSingleton _ _).symm
        _ = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (u i : F) *
            ∏ x ∈ s, FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (u x : F) := by
              rw [hs]

private noncomputable def conductorFiniteCorrectionValue
    (S : A1.SData F CE condη) (c : Fˣ) : F :=
  ∏ v : S.Sf,
    (conductorClassPowerGen v.1 : F) ^ conductorFiniteCorrectionExponent c v.1

private theorem conductorFiniteCorrectionValue_ne_zero
    (S : A1.SData F CE condη) (c : Fˣ) :
    conductorFiniteCorrectionValue S c ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  exact zpow_ne_zero _ (conductorClassPowerGen_map_ne_zero v.1)

private noncomputable def conductorFiniteCorrection
    (S : A1.SData F CE condη) (c : Fˣ) : Fˣ :=
  Units.mk0 (conductorFiniteCorrectionValue S c)
    (conductorFiniteCorrectionValue_ne_zero S c)

private theorem conductorFiniteCorrection_span (S : A1.SData F CE condη) (c : Fˣ) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
        (conductorFiniteCorrection S c : F) =
      ∏ v : S.Sf,
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (conductorClassPowerGen v.1 : F)) ^
            conductorFiniteCorrectionExponent c v.1 := by
  classical
  change FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
      (conductorFiniteCorrectionValue S c) = _
  unfold conductorFiniteCorrectionValue
  calc
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
        (∏ v : S.Sf,
          (conductorClassPowerGen v.1 : F) ^ conductorFiniteCorrectionExponent c v.1) =
      ∏ v : S.Sf,
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          ((conductorClassPowerGen v.1 : F) ^ conductorFiniteCorrectionExponent c v.1) := by
            simpa [Units.val_zpow_eq_zpow_val] using
              (conductor_spanSingleton_finset_prod (s := Finset.univ)
                (u := fun v : S.Sf =>
                  (Units.mk0 (conductorClassPowerGen v.1 : F)
                    (conductorClassPowerGen_map_ne_zero v.1)) ^
                      conductorFiniteCorrectionExponent c v.1))
    _ = ∏ v : S.Sf,
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (conductorClassPowerGen v.1 : F)) ^
            conductorFiniteCorrectionExponent c v.1 := by
              apply Finset.prod_congr rfl
              intro v hv
              exact conductor_spanSingleton_zpow
                (conductorClassPowerGen_map_ne_zero v.1) _

private theorem conductorFiniteCorrection_count
    (S : A1.SData F CE condη) (c : Fˣ) (w : A1.FinPlace F) :
    FractionalIdeal.count F w
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (conductorFiniteCorrection S c : F)) =
      if hw : w ∈ S.Sf then
        conductorFiniteCorrectionExponent c w *
          (Fintype.card (ClassGroup (𝓞 F)) : ℤ)
      else 0 := by
  classical
  rw [conductorFiniteCorrection_span, FractionalIdeal.count_prod]
  · simp only [FractionalIdeal.count_zpow]
    have hterm (v : S.Sf) :
        FractionalIdeal.count F w
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
              (conductorClassPowerGen v.1 : F)) =
          if w = v.1 then (Fintype.card (ClassGroup (𝓞 F)) : ℤ) else 0 := by
      by_cases h : w = v.1
      · simpa [h] using conductor_classPower_spanSingleton_count v.1 w _
          (conductorClassPowerGen_spec v.1)
      · simpa [h] using conductor_classPower_spanSingleton_count v.1 w _
          (conductorClassPowerGen_spec v.1)
    simp_rw [hterm]
    by_cases hw : w ∈ S.Sf
    · let v₀ : S.Sf := ⟨w, hw⟩
      have hsum :
          (∑ v : S.Sf, conductorFiniteCorrectionExponent c v.1 *
            (if w = v.1 then (Fintype.card (ClassGroup (𝓞 F)) : ℤ) else 0)) =
          conductorFiniteCorrectionExponent c w *
            (Fintype.card (ClassGroup (𝓞 F)) : ℤ) := by
        rw [Finset.sum_eq_single v₀]
        · simp [v₀]
        · intro v hv hne
          have hval : w ≠ v.1 := by
            intro heq
            apply hne
            exact Subtype.ext heq.symm
          simp [hval]
        · simp
      simpa [hw] using hsum
    · have hsum :
          (∑ v : S.Sf, conductorFiniteCorrectionExponent c v.1 *
            (if w = v.1 then (Fintype.card (ClassGroup (𝓞 F)) : ℤ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        have hval : w ≠ v.1 := by
          intro heq
          exact hw (heq ▸ v.2)
        simp [hval]
      simpa [hw] using hsum
  · intro v hv
    exact zpow_ne_zero _ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (conductorClassPowerGen_map_ne_zero v.1))

private theorem conductor_spanSingleton_mul_count (x y : F) (hx : x ≠ 0) (hy : y ≠ 0)
    (w : A1.FinPlace F) :
    FractionalIdeal.count F w
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x * y)) =
      FractionalIdeal.count F w
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) +
        FractionalIdeal.count F w
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul F w
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)]

private theorem conductorFiniteAdjusted_count
    (S : A1.SData F CE condη) (c : Fˣ) (w : A1.FinPlace F) :
    FractionalIdeal.count F w
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          ((c * conductorFiniteCorrection S c : Fˣ) : F)) =
      if hw : w ∈ S.Sf then
        FractionalIdeal.count F w
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) %
            (Fintype.card (ClassGroup (𝓞 F)) : ℤ)
      else FractionalIdeal.count F w
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) := by
  classical
  change FractionalIdeal.count F w
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
        ((c : F) * (conductorFiniteCorrection S c : F))) = _
  rw [conductor_spanSingleton_mul_count (c : F)
    (conductorFiniteCorrection S c : F)
    (Units.ne_zero c) (conductorFiniteCorrectionValue_ne_zero S c) w,
    conductorFiniteCorrection_count]
  by_cases hw : w ∈ S.Sf
  · simp only [dif_pos hw]
    dsimp [conductorFiniteCorrectionExponent]
    let m := FractionalIdeal.count F w
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F))
    let n : ℤ := Fintype.card (ClassGroup (𝓞 F))
    have hn : 0 < n := by
      dsimp [n]
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 F)))
    change m + -(m / n) * n = m % n
    have hdiv : m - n * (m / n) = m % n := by
      have h := congrArg (fun z : ℤ => z - n * (m / n))
        (Int.emod_add_mul_ediv m n).symm
      simpa [sub_eq_add_neg] using h
    calc
      m + -(m / n) * n = m - n * (m / n) := by ring
      _ = m % n := hdiv
  · simp [hw]

private theorem conductor_spanSingleton_integralUnit_count
    (v : A1.FinPlace F) (u : (𝓞 F)ˣ) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (u : F)) = 0 := by
  have hu0 : (u : F) ≠ 0 := by
    intro h
    exact Units.ne_zero u ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  rw [conductor_spanSingleton_count v (u : F) hu0]
  have hv : v.valuation F (u : F) = 1 := by
    have h := v.valuation_of_unit_eq (R := 𝓞 F) (K := F) u
    have h' : (v.valuationOfNeZero
        (Units.map (algebraMap (𝓞 F) F : (𝓞 F) →* F) u) :
        WithZero (Multiplicative ℤ)) = 1 := by
      simpa using congrArg (fun z : Multiplicative ℤ =>
        (z : WithZero (Multiplicative ℤ))) h
    rw [HeightOneSpectrum.valuationOfNeZero_eq, Units.coe_map] at h'
    exact h'
  simp [hv]

private theorem conductor_integralUnit_map_ne_zero (u : (𝓞 F)ˣ) :
    (u : F) ≠ 0 := by
  intro h
  exact Units.ne_zero u ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))

private theorem conductorBalancedUnit_count
    (c : Fˣ) (u : (𝓞 F)ˣ) (v : A1.FinPlace F) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          ((Units.map (algebraMap (𝓞 F) F) u * c : Fˣ) : F)) =
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) := by
  change FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
        ((u : F) * (c : F))) = _
  rw [conductor_spanSingleton_mul_count (u : F) (c : F)
    (conductor_integralUnit_map_ne_zero u) (Units.ne_zero c),
    conductor_spanSingleton_integralUnit_count, zero_add]

private noncomputable def conductorAdjustedGenerator
    (S : A1.SData F CE condη) (c : Fˣ) : Fˣ :=
  c * conductorFiniteCorrection S c

private theorem conductorAdjustedGenerator_isGen
    (S : A1.SData F CE condη) (I : S.ExtIdeal) (c : Fˣ)
    (hc : S.IsGen (c : F) I.1) :
    S.IsGen (conductorAdjustedGenerator S c : F) I.1 := by
  refine ⟨hc.1, Units.ne_zero (conductorAdjustedGenerator S c), ?_⟩
  intro v hv
  rw [conductorAdjustedGenerator, conductorFiniteAdjusted_count]
  simpa [hv] using hc.2.2 v hv

private theorem conductorFiniteAdjusted_count_nonneg_lt
    (S : A1.SData F CE condη) (c : Fˣ) (v : S.Sf) :
    0 ≤ FractionalIdeal.count F v.1
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          ((c * conductorFiniteCorrection S c : Fˣ) : F)) %
        (Fintype.card (ClassGroup (𝓞 F)) : ℤ) ∧
      FractionalIdeal.count F v.1
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          ((c * conductorFiniteCorrection S c : Fˣ) : F)) %
        (Fintype.card (ClassGroup (𝓞 F)) : ℤ) <
        (Fintype.card (ClassGroup (𝓞 F)) : ℤ) := by
  have hn : 0 < (Fintype.card (ClassGroup (𝓞 F)) : ℤ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 F)))
  exact ⟨Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩

private theorem conductorAdjustedGenerator_S_remainders
    (S : A1.SData F CE condη) (c : Fˣ) :
    ∀ v ∈ S.Sf,
      0 ≤ FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (conductorAdjustedGenerator S c : F)) ∧
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (conductorAdjustedGenerator S c : F)) <
        (Fintype.card (ClassGroup (𝓞 F)) : ℤ) := by
  intro v hv
  have hcount := conductorFiniteAdjusted_count S c v
  have hcount' := by simpa [hv] using hcount
  have hcount'' :
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            ((c * conductorFiniteCorrection S c : Fˣ) : F)) =
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) %
            (Fintype.card (ClassGroup (𝓞 F)) : ℤ) := by
    simpa only [Units.val_mul] using hcount'
  rw [conductorAdjustedGenerator, hcount'']
  have hn : 0 < (Fintype.card (ClassGroup (𝓞 F)) : ℤ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 F)))
  exact ⟨Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩

private noncomputable def conductorSNormProduct
    (S : A1.SData F CE condη) : ℝ :=
  ∏ v ∈ S.Sf, (Ideal.absNorm v.asIdeal : ℝ)

private noncomputable def conductorSNormConstant
    (S : A1.SData F CE condη) : ℝ :=
  (conductorSNormProduct S) ^ (Fintype.card (ClassGroup (𝓞 F)) : ℝ)

private theorem conductorSNormProduct_pos (S : A1.SData F CE condη) :
    0 < conductorSNormProduct S := by
  unfold conductorSNormProduct
  exact Finset.prod_pos fun v hv => by
    exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)

private theorem conductorSNormConstant_pos (S : A1.SData F CE condη) :
    0 < conductorSNormConstant S := by
  unfold conductorSNormConstant
  exact Real.rpow_pos_of_pos (conductorSNormProduct_pos S) _

private theorem conductorSFiniteProduct_lower
    (S : A1.SData F CE condη) (c : Fˣ)
    (hrem : ∀ v ∈ S.Sf,
      0 ≤ FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (c : F)) ∧
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (c : F)) < (Fintype.card (ClassGroup (𝓞 F)) : ℤ)) :
    (conductorSNormConstant S)⁻¹ ≤
      ∏ v ∈ S.Sf, ‖FinitePlace.embedding v (c : F)‖ := by
  classical
  let n : ℝ := (Fintype.card (ClassGroup (𝓞 F)) : ℝ)
  have hn0 : 0 ≤ n := by positivity
  have hn : 0 < (Fintype.card (ClassGroup (𝓞 F)) : ℤ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 F)))
  have hlocal (v : A1.FinPlace F) (hv : v ∈ S.Sf) :
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-n) ≤
        ‖FinitePlace.embedding v (c : F)‖ := by
    have hvnorm : 1 ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (HeightOneSpectrum.one_lt_absNorm v))
    have hm :
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) <
          (Fintype.card (ClassGroup (𝓞 F)) : ℤ) := (hrem v hv).2
    have hm' :
        (-n) ≤ ((-(FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) : ℤ) : ℤ) : ℝ) := by
      dsimp [n]
      exact_mod_cast (neg_le_neg hm.le)
    rw [A1.norm_embedding_eq_absNorm_zpow v (c : F) (Units.ne_zero c)]
    rw [← Real.rpow_intCast (Ideal.absNorm v.asIdeal : ℝ)
      (-(FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) : ℤ))]
    exact Real.rpow_le_rpow_of_exponent_le hvnorm hm'
  have hprod :
      (∏ v ∈ S.Sf, (Ideal.absNorm v.asIdeal : ℝ) ^ (-n)) ≤
        ∏ v ∈ S.Sf, ‖FinitePlace.embedding v (c : F)‖ := by
    exact Finset.prod_le_prod₀
      (fun v hv => (Real.rpow_pos_of_pos (by
        exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
          ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) _).le)
      (fun v hv => hlocal v hv)
  have hpow :
      (∏ v ∈ S.Sf, (Ideal.absNorm v.asIdeal : ℝ) ^ (-n)) =
        (conductorSNormProduct S) ^ (-n) := by
    unfold conductorSNormProduct
    exact Real.finsetProd_rpow S.Sf
      (fun v => (Ideal.absNorm v.asIdeal : ℝ))
      (fun v hv => by positivity) _
  have hpowInv : (conductorSNormProduct S) ^ (-n) =
      (conductorSNormConstant S)⁻¹ := by
    rw [Real.rpow_neg (conductorSNormProduct_pos S).le, conductorSNormConstant]
  rw [hpow, hpowInv] at hprod
  exact hprod

private theorem conductorFiniteProduct_eq_heightOne (c : Fˣ) :
    (∏ᶠ v : NumberField.FinitePlace F, v (c : F)) =
      ∏ᶠ v : A1.FinPlace F, ‖FinitePlace.embedding v (c : F)‖ := by
  classical
  simp only [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    FinitePlace.equivHeightOneSpectrum_symm_apply]

private theorem conductorFiniteProduct_split
    (S : A1.SData F CE condη) (c : Fˣ) :
    (∏ᶠ v : A1.FinPlace F, ‖FinitePlace.embedding v (c : F)‖) =
      (∏ᶠ v ∈ (S.Sf : Set (A1.FinPlace F)), ‖FinitePlace.embedding v (c : F)‖) *
        ∏ᶠ v ∉ (S.Sf : Set (A1.FinPlace F)), ‖FinitePlace.embedding v (c : F)‖ := by
  classical
  let f : A1.FinPlace F → ℝ := fun v => ‖FinitePlace.embedding v (c : F)‖
  have hf : f.HasFiniteMulSupport := by
    exact A1.finitePlace_mk_hasFiniteMulSupport (Units.ne_zero c)
  have hsplit : (∏ᶠ v : A1.FinPlace F, f v) =
      (∏ᶠ v ∈ (S.Sf : Set (A1.FinPlace F)), f v) *
        ∏ᶠ v ∉ (S.Sf : Set (A1.FinPlace F)), f v := by
    have hu := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hf Set.inter_subset_right) (f := f)
    rw [Set.union_compl_self, finprod_mem_univ] at hu
    exact hu
  simpa [f] using hsplit

private theorem conductorGlobalNorm_le
    (S : A1.SData F CE condη) (I : S.ExtIdeal) (c : Fˣ)
    (hc : S.IsGen (c : F) I.1)
    (hrem : ∀ v ∈ S.Sf,
      0 ≤ FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) ∧
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) <
        (Fintype.card (ClassGroup (𝓞 F)) : ℤ)) :
    NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding F (c : F)) ≤
      conductorSNormConstant S * (idealNorm I.1) := by
  classical
  let NI : ℝ := idealNorm I.1
  let C : ℝ := conductorSNormConstant S
  let g : ℝ := NumberField.mixedEmbedding.norm
    (NumberField.mixedEmbedding F (c : F))
  have hNI : 0 < NI := by
    dsimp [NI, idealNorm]
    exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr I.2.1⟩)
  have hC : 0 < C := conductorSNormConstant_pos S
  have hS : C⁻¹ ≤
      (∏ᶠ v ∈ (S.Sf : Set (A1.FinPlace F)), ‖FinitePlace.embedding v (c : F)‖) := by
    change (conductorSNormConstant S)⁻¹ ≤ _
    simpa only [finprod_mem_coe_finset] using conductorSFiniteProduct_lower S c hrem
  have hout : (∏ᶠ v ∉ (S.Sf : Set (A1.FinPlace F)),
        ‖FinitePlace.embedding v (c : F)‖) * NI = 1 := by
    simpa [NI, idealNorm] using
      (A1.finprod_exterior_norm_embedding_mul_absNorm hc.1 hc)
  have hPF := NumberField.prod_abs_eq_one (x := (c : F)) (Units.ne_zero c)
  rw [NumberField.InfinitePlace.prod_eq_abs_norm] at hPF
  rw [← NumberField.mixedEmbedding.norm_eq_norm, conductorFiniteProduct_eq_heightOne,
    conductorFiniteProduct_split] at hPF
  have hmul :
      NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding F (c : F)) *
        ((∏ᶠ v ∈ (S.Sf : Set (A1.FinPlace F)),
          ‖FinitePlace.embedding v (c : F)‖) *
          ∏ᶠ v ∉ (S.Sf : Set (A1.FinPlace F)),
            ‖FinitePlace.embedding v (c : F)‖) = 1 := by
    simpa only [g] using hPF
  have houtInv :
      (∏ᶠ v ∉ (S.Sf : Set (A1.FinPlace F)),
        ‖FinitePlace.embedding v (c : F)‖) = NI⁻¹ := by
    have h' := hout
    field_simp [hNI.ne'] at h' ⊢
    exact h'
  have hSNI : C⁻¹ * NI⁻¹ ≤
      (∏ᶠ v ∈ (S.Sf : Set (A1.FinPlace F)), ‖FinitePlace.embedding v (c : F)‖) *
        (∏ᶠ v ∉ (S.Sf : Set (A1.FinPlace F)),
          ‖FinitePlace.embedding v (c : F)‖) := by
    rw [houtInv]
    exact mul_le_mul_of_nonneg_right hS (inv_nonneg.mpr hNI.le)
  have hglobal : g * (C⁻¹ * NI⁻¹) ≤ 1 := by
    calc
      g * (C⁻¹ * NI⁻¹) ≤ g *
          ((∏ᶠ v ∈ (S.Sf : Set (A1.FinPlace F)), ‖FinitePlace.embedding v (c : F)‖) *
            ∏ᶠ v ∉ (S.Sf : Set (A1.FinPlace F)),
              ‖FinitePlace.embedding v (c : F)‖) :=
        mul_le_mul_of_nonneg_left hSNI (NumberField.mixedEmbedding.norm_nonneg _)
      _ = 1 := hmul
  have hgc : g ≤ C * NI := by
    let P : ℝ := C * NI
    have hPpos : 0 < P := mul_pos hC hNI
    have hglobal' : g * P⁻¹ ≤ 1 := by
      simpa [P, mul_inv, mul_comm, mul_left_comm, mul_assoc] using hglobal
    calc
      g = (g * P⁻¹) * P := by field_simp [hPpos.ne']
      _ ≤ 1 * P := mul_le_mul_of_nonneg_right hglobal' hPpos.le
      _ = C * NI := by simp [P]
  simpa [g, C, NI] using hgc

private theorem conductorInfiniteLogDeviation_sum (x : F) (hx : x ≠ 0) :
    ∑ w : InfinitePlace F,
      (w.mult : ℝ) *
        (Real.log (w x) -
          Real.log (NumberField.mixedEmbedding.norm
            (NumberField.mixedEmbedding F x)) /
            (Module.finrank ℚ F : ℝ)) = 0 := by
  have hlog :
      (∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w x)) =
        Real.log (NumberField.mixedEmbedding.norm
          (NumberField.mixedEmbedding F x)) := by
    calc
      (∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w x)) =
          ∑ w : InfinitePlace F, Real.log ((w x) ^ w.mult) := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [Real.log_pow]
      _ = Real.log (∏ w : InfinitePlace F, (w x) ^ w.mult) := by
            symm
            rw [Real.log_prod]
            intro w hw
            exact pow_ne_zero _ ((w.pos_iff).2 hx).ne'
      _ = Real.log (|(Algebra.norm ℚ x : ℝ)|) := by
            rw [NumberField.InfinitePlace.prod_eq_abs_norm]
            exact congrArg Real.log (Rat.cast_abs (Algebra.norm ℚ x))
      _ = Real.log (NumberField.mixedEmbedding.norm
          (NumberField.mixedEmbedding F x)) := by
            rw [NumberField.mixedEmbedding.norm_eq_norm]
            exact congrArg Real.log (Rat.cast_abs (Algebra.norm ℚ x)).symm
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hconst :
      (∑ w : InfinitePlace F, (w.mult : ℝ) *
        (Real.log (NumberField.mixedEmbedding.norm
          (NumberField.mixedEmbedding F x)) /
          (Module.finrank ℚ F : ℝ))) =
        Real.log (NumberField.mixedEmbedding.norm
          (NumberField.mixedEmbedding F x)) := by
    calc
      _ = (∑ w : InfinitePlace F, (w.mult : ℝ)) *
          (Real.log (NumberField.mixedEmbedding.norm
            (NumberField.mixedEmbedding F x)) /
            (Module.finrank ℚ F : ℝ)) := by rw [Finset.sum_mul]
      _ = (Module.finrank ℚ F : ℝ) *
          (Real.log (NumberField.mixedEmbedding.norm
            (NumberField.mixedEmbedding F x)) /
            (Module.finrank ℚ F : ℝ)) := by
          rw [← Nat.cast_sum, NumberField.InfinitePlace.sum_mult_eq]
      _ = Real.log (NumberField.mixedEmbedding.norm
          (NumberField.mixedEmbedding F x)) := by field_simp [hd]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hlog, hconst]
  ring

private noncomputable def conductorLogBox (K : Type) [Field K] [NumberField K] : ℝ :=
  ∑ i : Fin (NumberField.Units.rank K),
    ‖((NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
      (NumberField.Units.unitLattice K)) i‖

private theorem conductorLogBox_nonneg : 0 ≤ conductorLogBox F := by
  unfold conductorLogBox
  exact Finset.sum_nonneg fun i hi => norm_nonneg _

private noncomputable def conductorLogBasePlace : InfinitePlace F :=
  NumberField.Units.dirichletUnitTheorem.w₀ (K := F)

private theorem conductorFundamentalCone_log_bound
    (z : NumberField.mixedEmbedding.mixedSpace F)
    (hz : z ∈ NumberField.mixedEmbedding.fundamentalCone F) :
    ∀ w : {w : InfinitePlace F // w ≠ conductorLogBasePlace},
      |NumberField.mixedEmbedding.logMap z w| ≤ conductorLogBox F := by
  classical
  let B := (NumberField.Units.basisUnitLattice F).ofZLatticeBasis ℝ
    (NumberField.Units.unitLattice F)
  have hfund : NumberField.mixedEmbedding.logMap z ∈ ZSpan.fundamentalDomain B := hz.1
  have hbox : ‖NumberField.mixedEmbedding.logMap z‖ ≤ conductorLogBox F := by
    calc
      ‖NumberField.mixedEmbedding.logMap z‖ =
          ‖ZSpan.fract B (NumberField.mixedEmbedding.logMap z)‖ := by
            rw [(ZSpan.fract_eq_self.mpr hfund)]
      _ ≤ ∑ i : Fin (NumberField.Units.rank F), ‖B i‖ := ZSpan.norm_fract_le B _
  intro w
  have hcoord := norm_le_pi_norm (NumberField.mixedEmbedding.logMap z) w
  simpa only [Real.norm_eq_abs, B, conductorLogBox] using hcoord.trans hbox

private noncomputable def conductorArchDeviation (x : F) (w : InfinitePlace F) : ℝ :=
  Real.log (w x) -
    Real.log (NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding F x)) /
      (Module.finrank ℚ F : ℝ)

private theorem conductorAllPlaceDeviation_bound (x : F) (hx : x ≠ 0)
    (hcone : NumberField.mixedEmbedding F x ∈
      NumberField.mixedEmbedding.fundamentalCone F) :
    ∀ w : InfinitePlace F,
      |conductorArchDeviation x w| ≤
        ((Fintype.card {w : InfinitePlace F //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀ (K := F)} : ℝ) + 1) *
          conductorLogBox F := by
  classical
  let base : InfinitePlace F := NumberField.Units.dirichletUnitTheorem.w₀ (K := F)
  let idx := {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀ (K := F)}
  let f : InfinitePlace F → ℝ := fun w =>
    (w.mult : ℝ) * conductorArchDeviation x w
  have hsum : ∑ w : InfinitePlace F, f w = 0 := by
    simpa [f, conductorArchDeviation] using
      conductorInfiniteLogDeviation_sum x hx
  have hsplit : f base +
      (∑ w : idx, f w.1) = 0 := by
    rw [Fintype.sum_eq_add_sum_subtype_ne f base] at hsum
    simpa [idx] using hsum
  have hcoord : ∀ w : idx, |f w.1| ≤ conductorLogBox F := by
    intro w
    have h := conductorFundamentalCone_log_bound
      (NumberField.mixedEmbedding F x) hcone w
    have hmap : NumberField.mixedEmbedding.logMap
        (NumberField.mixedEmbedding F x) w = f w.1 := by
      rw [NumberField.mixedEmbedding.logMap_apply,
        NumberField.mixedEmbedding.normAtPlace_apply]
      rfl
    rw [hmap] at h
    exact h
  have htri : |∑ w : idx, f w.1| ≤ ∑ w : idx, |f w.1| := by
    simpa using (Finset.abs_sum_le_sum_abs (fun w : idx => f w.1) Finset.univ)
  have hsumR : (∑ w : idx, |f w.1|) ≤
      (Fintype.card idx : ℝ) * conductorLogBox F := by
    calc
      _ ≤ ∑ w : idx, conductorLogBox F :=
        Finset.sum_le_sum fun w hw => hcoord w
      _ = (Fintype.card idx : ℝ) * conductorLogBox F := by simp [nsmul_eq_mul]
  have hscaled0 :
      (base.mult : ℝ) *
        |conductorArchDeviation x base| ≤
          (Fintype.card idx : ℝ) * conductorLogBox F := by
    calc
      _ = |f base| := by
        dsimp [f]
        have hmulabs :
            |(base.mult : ℝ) * conductorArchDeviation x base| =
              (base.mult : ℝ) * |conductorArchDeviation x base| := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg base.mult)]
        exact hmulabs.symm
      _ = |∑ w : idx, f w.1| := by
        have hneg : f base = -(∑ w : idx, f w.1) := by linarith [hsplit]
        rw [hneg]
        simp
      _ ≤ ∑ w : idx, |f w.1| := htri
      _ ≤ (Fintype.card idx : ℝ) * conductorLogBox F := hsumR
  have hbaseAbs :
      |conductorArchDeviation x base| ≤
        (Fintype.card idx : ℝ) * conductorLogBox F := by
    have hm := NumberField.InfinitePlace.one_le_mult
      (w := base)
    calc
      _ = 1 * |conductorArchDeviation x base| := by ring
      _ ≤ (base.mult : ℝ) *
          |conductorArchDeviation x base| :=
            mul_le_mul_of_nonneg_right hm (abs_nonneg _)
      _ ≤ _ := hscaled0
  intro w
  by_cases hw : w = base
  · subst w
    have hR := conductorLogBox_nonneg (F := F)
    have hcard : 0 ≤ (Fintype.card idx : ℝ) := Nat.cast_nonneg _
    calc
      _ ≤ (Fintype.card idx : ℝ) * conductorLogBox F := hbaseAbs
      _ ≤ ((Fintype.card idx : ℝ) + 1) * conductorLogBox F := by nlinarith
  · let wi : idx := ⟨w, hw⟩
    have hwi : |f w| ≤ conductorLogBox F := by simpa [wi] using hcoord wi
    have hm := NumberField.InfinitePlace.one_le_mult (w := w)
    have hdelta : |conductorArchDeviation x w| ≤ |f w| := by
      have hmulabs :
          |(w.mult : ℝ) * conductorArchDeviation x w| =
            (w.mult : ℝ) * |conductorArchDeviation x w| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg w.mult)]
      calc
        _ = 1 * |conductorArchDeviation x w| := by ring
        _ ≤ (w.mult : ℝ) * |conductorArchDeviation x w| :=
              mul_le_mul_of_nonneg_right hm (abs_nonneg _)
        _ = |f w| := by simpa [f] using hmulabs.symm
    have hR := conductorLogBox_nonneg (F := F)
    have hcard : 0 ≤ (Fintype.card idx : ℝ) := Nat.cast_nonneg _
    calc
      _ ≤ |f w| := hdelta
      _ ≤ conductorLogBox F := hwi
      _ ≤ ((Fintype.card idx : ℝ) + 1) * conductorLogBox F := by nlinarith

private noncomputable def conductorArchBoxRadius
    (K : Type) [Field K] [NumberField K] : ℝ :=
  ((Fintype.card {w : InfinitePlace K // w ≠
    NumberField.Units.dirichletUnitTheorem.w₀ (K := K)} : ℝ) + 1) *
      conductorLogBox K

private noncomputable def conductorArchHeight (S : A1.SData F CE condη) : ℝ :=
  Real.exp (conductorArchBoxRadius F) *
    (conductorSNormConstant S) ^ (1 / (Module.finrank ℚ F : ℝ))

private theorem conductorArchHeight_pos (S : A1.SData F CE condη) :
    0 < conductorArchHeight S := by
  unfold conductorArchHeight
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos
    (conductorSNormConstant_pos S) _)

private theorem conductorArchBalanced_bound
    (S : A1.SData F CE condη) (I : S.ExtIdeal) (c : Fˣ)
    (hc : S.IsGen (c : F) I.1)
    (hrem : ∀ v ∈ S.Sf,
      0 ≤ FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) ∧
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) <
        (Fintype.card (ClassGroup (𝓞 F)) : ℤ))
    (u : (𝓞 F)ˣ)
    (hu : u • NumberField.mixedEmbedding F (c : F) ∈
      NumberField.mixedEmbedding.fundamentalCone F) :
    ∀ w : InfinitePlace F,
      ‖w.embedding ((Units.map (algebraMap (𝓞 F) F) u * c : Fˣ) : F)‖ ≤
        conductorArchHeight S * Real.rpow (idealNorm I.1)
          (1 / (Module.finrank ℚ F : ℝ)) := by
  classical
  let c' : Fˣ := Units.map (algebraMap (𝓞 F) F) u * c
  have hc' : S.IsGen (c' : F) I.1 := by
    refine ⟨hc.1, Units.ne_zero c', ?_⟩
    intro v hv
    rw [show c' = Units.map (algebraMap (𝓞 F) F) u * c from rfl,
      conductorBalancedUnit_count c u v]
    exact hc.2.2 v hv
  have hrem' : ∀ v ∈ S.Sf,
      0 ≤ FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c' : F)) ∧
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c' : F)) <
        (Fintype.card (ClassGroup (𝓞 F)) : ℤ) := by
    intro v hv
    have h := hrem v hv
    rw [show c' = Units.map (algebraMap (𝓞 F) F) u * c from rfl,
      conductorBalancedUnit_count c u v]
    exact h
  have hglobal := conductorGlobalNorm_le S I c' hc' hrem'
  have hne : (c' : F) ≠ 0 := Units.ne_zero c'
  have hcone : NumberField.mixedEmbedding F (c' : F) ∈
      NumberField.mixedEmbedding.fundamentalCone F := by
    have hmix : u • NumberField.mixedEmbedding F (c : F) =
        NumberField.mixedEmbedding F (c' : F) := by
      rw [NumberField.mixedEmbedding.unitSMul_smul, ← map_mul]
      rfl
    rw [← hmix]
    exact hu
  have hdev : ∀ w : InfinitePlace F,
      |conductorArchDeviation (c' : F) w| ≤ conductorArchBoxRadius F := by
    simpa [conductorArchBoxRadius] using
      conductorAllPlaceDeviation_bound (c' : F) hne hcone
  let NI : ℝ := idealNorm I.1
  let N : ℝ := NumberField.mixedEmbedding.norm
    (NumberField.mixedEmbedding F (c' : F))
  let d : ℝ := (Module.finrank ℚ F : ℝ)
  have hNI : 0 < NI := by
    dsimp [NI, idealNorm]
    exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr I.2.1⟩)
  have hN : 0 < N := by
    dsimp [N]
    rw [NumberField.mixedEmbedding.norm_eq_norm]
    exact_mod_cast abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hne)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F))
  have hglobal' : N ≤ conductorSNormConstant S * NI := by
    simpa [N, NI] using hglobal
  have hroot : Real.exp (Real.log N / d) = Real.rpow N (1 / d) := by
    calc
      Real.exp (Real.log N / d) = Real.exp (Real.log N * (1 / d)) := by
        congr 1
        dsimp [d]
        field_simp [hd.ne']
      _ = Real.rpow N (1 / d) := (Real.rpow_def_of_pos hN (1 / d)).symm
  have hrootle : Real.rpow N (1 / d) ≤
      Real.rpow (conductorSNormConstant S * NI) (1 / d) :=
    Real.rpow_le_rpow hN.le hglobal' (by positivity)
  have hfactor : Real.rpow (conductorSNormConstant S * NI) (1 / d) =
      Real.rpow (conductorSNormConstant S) (1 / d) * Real.rpow NI (1 / d) :=
    Real.mul_rpow (conductorSNormConstant_pos S).le hNI.le
  intro w
  have hlog : Real.log (w (c' : F)) ≤ Real.log N / d +
      conductorArchBoxRadius F := by
    have hδ := (abs_le.mp (hdev w)).2
    dsimp [conductorArchDeviation, N, d] at hδ ⊢
    linarith
  have hval : w (c' : F) ≤
      Real.exp (conductorArchBoxRadius F) * Real.rpow N (1 / d) := by
    have he := Real.le_exp_of_log_le hlog
    calc
      w (c' : F) ≤ Real.exp (Real.log N / d + conductorArchBoxRadius F) := he
      _ = Real.exp (Real.log N / d) * Real.exp (conductorArchBoxRadius F) := by
        rw [Real.exp_add]
      _ = Real.exp (conductorArchBoxRadius F) * Real.rpow N (1 / d) := by
        rw [hroot]
        ac_rfl
  calc
    ‖w.embedding (c' : F)‖ = w (c' : F) :=
      NumberField.InfinitePlace.norm_embedding_eq w (c' : F)
    _ ≤ Real.exp (conductorArchBoxRadius F) * Real.rpow N (1 / d) := hval
    _ ≤ Real.exp (conductorArchBoxRadius F) *
          Real.rpow (conductorSNormConstant S * NI) (1 / d) :=
        mul_le_mul_of_nonneg_left hrootle (Real.exp_nonneg _)
    _ = conductorArchHeight S * Real.rpow NI (1 / d) := by
        rw [hfactor, conductorArchHeight]
        ac_rfl

private theorem conductorBalancedGeneratorChoice_exists
    (S : A1.SData F CE condη) (I : S.ExtIdeal) :
    ∃ c : Fˣ, S.IsGen (c : F) I.1 ∧
      (∀ v ∈ S.Sf,
        0 ≤ FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) ∧
        FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) <
          (Fintype.card (ClassGroup (𝓞 F)) : ℤ)) ∧
      (∀ w : InfinitePlace F,
        ‖w.embedding (c : F)‖ ≤ conductorArchHeight S *
          Real.rpow (idealNorm I.1) (1 / (Module.finrank ℚ F : ℝ))) := by
  classical
  obtain ⟨c₀, hc₀⟩ := SData.exists_conductor_generator S I
  let c₁ := conductorAdjustedGenerator S c₀
  have hc₁ : S.IsGen (c₁ : F) I.1 := by
    simpa [c₁] using conductorAdjustedGenerator_isGen S I c₀ hc₀
  have hrem₁ := conductorAdjustedGenerator_S_remainders S c₀
  have hnz : NumberField.mixedEmbedding.norm
      (NumberField.mixedEmbedding F (c₁ : F)) ≠ 0 := by
    rw [NumberField.mixedEmbedding.norm_eq_norm]
    have hnz' : Algebra.norm ℚ (c₁ : F) ≠ 0 :=
      (Algebra.norm_ne_zero_iff (R := ℚ) (S := F)).mpr (Units.ne_zero c₁)
    exact_mod_cast abs_ne_zero.mpr hnz'
  obtain ⟨u, hu⟩ := NumberField.mixedEmbedding.fundamentalCone.exists_unit_smul_mem
    (x := NumberField.mixedEmbedding F (c₁ : F)) hnz
  let c₂ : Fˣ := Units.map (algebraMap (𝓞 F) F) u * c₁
  have hc₂ : S.IsGen (c₂ : F) I.1 := by
    refine ⟨hc₁.1, Units.ne_zero c₂, ?_⟩
    intro v hv
    change FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          ((Units.map (algebraMap (𝓞 F) F) u * c₁ : Fˣ) : F)) = _
    rw [conductorBalancedUnit_count c₁ u v]
    exact hc₁.2.2 v hv
  have hrem₂ : ∀ v ∈ S.Sf,
      0 ≤ FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c₂ : F)) ∧
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c₂ : F)) <
        (Fintype.card (ClassGroup (𝓞 F)) : ℤ) := by
    intro v hv
    have h := hrem₁ v hv
    change (0 ≤ FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          ((Units.map (algebraMap (𝓞 F) F) u * c₁ : Fˣ) : F)) ∧
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          ((Units.map (algebraMap (𝓞 F) F) u * c₁ : Fˣ) : F)) <
        (Fintype.card (ClassGroup (𝓞 F)) : ℤ))
    rw [conductorBalancedUnit_count c₁ u v]
    exact h
  exact ⟨c₂, hc₂, hrem₂,
    conductorArchBalanced_bound S I c₁ hc₁ hrem₁ u hu⟩

theorem conductor_generators_exists_helper (S : A1.SData F CE condη) :
    Nonempty (ConductorGenerators S) := by
  classical
  let pick := fun I : S.ExtIdeal =>
    Classical.choose (conductorBalancedGeneratorChoice_exists S I)
  let spec := fun I : S.ExtIdeal =>
    Classical.choose_spec (conductorBalancedGeneratorChoice_exists S I)
  let H : ℝ := max 1 (conductorArchHeight S)
  have hH : 0 < H := by
    dsimp [H]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (conductorArchHeight S))
  let G : ConductorGenerators S := {
    gen := fun I => ⟨pick I, by
      change ∀ v : A1.FinPlace F, v ∉ S.Sf →
        v.valuation F (pick I : F) ≤ 1
      intro v hv
      have hg : S.IsGen (pick I : F) I.1 := (spec I).1
      rw [SData.IsGen.valuation_eq_exp_neg_idealExp S hg v hv]
      apply WithZero.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (Nat.cast_nonneg _)
      ⟩
    generates := by
      intro I
      exact (spec I).1
    height := H
    height_pos := hH
    finite_bound := by
      intro I v
      rw [A1.absFin_algebraMap]
      have hcount : 0 ≤ FractionalIdeal.count F v.1
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (pick I : F)) :=
        ((spec I).2.1 v.1 v.2).1
      have hN : 1 ≤ (Ideal.absNorm v.1.asIdeal : ℝ) := by
        exact_mod_cast (Nat.le_of_lt (HeightOneSpectrum.one_lt_absNorm v.1))
      have hlocal : ‖FinitePlace.embedding v.1 (pick I : F)‖ ≤ 1 := by
        rw [A1.norm_embedding_eq_absNorm_zpow v.1 (pick I : F)
          ((spec I).1.2.1)]
        rw [← Real.rpow_intCast (Ideal.absNorm v.1.asIdeal : ℝ)
          (-FractionalIdeal.count F v.1
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (pick I : F)))]
        exact Real.rpow_le_one_of_one_le_of_nonpos hN (by
          exact_mod_cast (neg_nonpos.mpr hcount))
      exact hlocal.trans (le_max_left 1 (conductorArchHeight S))
    infinite_bound := by
      intro I w
      have hnorm : 0 ≤ idealNorm I.1 := by
        dsimp [idealNorm]
        positivity
      calc
        ‖w.embedding (pick I : F)‖ ≤ conductorArchHeight S *
            Real.rpow (idealNorm I.1) (1 / (Module.finrank ℚ F : ℝ)) :=
          (spec I).2.2 w
        _ ≤ H * Real.rpow (idealNorm I.1)
            (1 / (Module.finrank ℚ F : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right 1 (conductorArchHeight S))
            (Real.rpow_nonneg hnorm _)
  }
  exact ⟨G⟩

end ArtinPrimitiveRoots.A2
