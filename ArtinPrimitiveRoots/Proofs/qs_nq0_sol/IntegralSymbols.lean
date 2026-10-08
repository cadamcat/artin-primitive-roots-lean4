import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.SquareClearing

/-!
# Integral quadratic-symbol representatives

Cubing the sextic residue symbol gives the quadratic symbol at primes
away from six. The integral cube is a sign; its reduction determines
which sign by the finite-field quadratic-character formula.
-/

set_option autoImplicit false

open scoped NumberField Classical
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- Away from six, the cubed sextic residue symbol is the quadratic symbol. -/
theorem qs_nq0_chi_cube_quad_symbol
    (D : FieldData K) (v : FinPlace K)
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (c : 𝓞 K) :
    chi D v (c : K) ^ 3 = (qsQuadSymbolAt v c : ℂ) := by
  classical
  let : v.asIdeal.IsMaximal := v.isMaximal
  let : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  have hres : residue v (c : K) = Ideal.Quotient.mk v.asIdeal c :=
    qs_nq0_residue_algebraMap v c
  by_cases hx : residue v (c : K) = 0
  · have hc : Ideal.Quotient.mk v.asIdeal c = 0 := hres.symm.trans hx
    simp [chi, hx, qsQuadSymbolAt, hc]
  have hc : Ideal.Quotient.mk v.asIdeal c ≠ 0 := by
    simpa only [hres] using hx
  have hchar : ringChar (𝓞 K ⧸ v.asIdeal) ≠ 2 := by
    intro hchar
    have htwo : (2 : 𝓞 K ⧸ v.asIdeal) = 0 :=
      (ringChar.spec (𝓞 K ⧸ v.asIdeal) 2).mpr (by rw [hchar])
    have hmem : (2 : 𝓞 K) ∈ v.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using htwo)
    apply h6
    have hsix : (6 : 𝓞 K) = 3 * 2 := by norm_num
    rw [hsix]
    exact Ideal.mul_mem_left _ _ hmem
  have hcard : Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hdiv : Fintype.card (𝓞 K ⧸ v.asIdeal) / 2 =
      (Ideal.absNorm v.asIdeal - 1) / 2 := by
    have hodd := FiniteField.odd_card_of_char_ne_two hchar
    omega
  have hquad := quadraticChar_eq_pow_of_char_ne_two hchar hc
  rw [hdiv] at hquad
  let z : 𝓞 K := (((chiAlg v (c : K) : (𝓞 K)ˣ) : 𝓞 K) ^ 3)
  have hzsq : z ^ 2 = 1 := by
    have hsix := congrArg Units.val
      ((mem_rootsOfUnity 6 (chiAlg v (c : K) : (𝓞 K)ˣ)).1
        (chiAlg v (c : K)).property)
    simpa only [z, ← pow_mul, Units.val_pow_eq_pow_val, Units.val_one] using hsix
  have hred : Ideal.Quotient.mk v.asIdeal z =
      Ideal.Quotient.mk v.asIdeal c ^ ((Ideal.absNorm v.asIdeal - 1) / 2) := by
    simpa only [z, hres] using qs_nq0_chiAlg_cube_reduction D v h6 (c : K) hx
  have hcube : chi D v (c : K) ^ 3 = D.σ0 (algebraMap (𝓞 K) K z) := by
    rw [chi, if_neg hx, ← map_pow, ← map_pow]
  change chi D v (c : K) ^ 3 =
    (quadraticChar (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk v.asIdeal c) : ℂ)
  rcases sq_eq_one_iff.mp hzsq with hz | hz
  · have hp : Ideal.Quotient.mk v.asIdeal c ^
        ((Ideal.absNorm v.asIdeal - 1) / 2) = 1 := by
      rw [← hred, hz, map_one]
    rw [hp, if_pos rfl] at hquad
    rw [hcube, hz, map_one, map_one, hquad, Int.cast_one]
  · have hp : Ideal.Quotient.mk v.asIdeal c ^
        ((Ideal.absNorm v.asIdeal - 1) / 2) ≠ 1 := by
      rw [← hred, hz, map_neg, map_one]
      exact Ring.neg_one_ne_one_of_char_ne_two hchar
    rw [if_neg hp] at hquad
    rw [hcube, hz, map_neg, map_one, map_neg, map_one, hquad,
      Int.cast_neg, Int.cast_one]

/-- A generator of an exterior integral ideal belongs to the ring of S-integers. -/
theorem qs_nq0_generator_is_sinteger
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (Sd : SData K CE condη) (I : Ideal (𝓞 K)) (c : K)
    (hc : Sd.IsGen c I) : c ∈ Sd.R := by
  change ∀ v : FinPlace K, v ∉ Sd.Sf → v.valuation K c ≤ 1
  intro v hv
  have hcount := qs_nq0_count_spanSingleton_eq_neg_log_valuation v c hc.2.1
  rw [hc.2.2 v hv] at hcount
  have hnonneg := FractionalIdeal.count_coe_nonneg K v I
  have hnonpos : WithZero.log (v.valuation K c) ≤ 0 := by omega
  calc
    v.valuation K c = WithZero.exp (WithZero.log (v.valuation K c)) :=
      (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hc.2.1)).symm
    _ ≤ 1 := WithZero.exp_le_one_iff.mpr hnonpos

/-- Multiplying the local parameter by a square preserves the quadratic character. -/
theorem qs_nq0_quadratic_local_square_correction
    (D : FieldData K) (H : HilbertData K) (v : FinPlace K)
    (a b : (v.adicCompletion K)ˣ) :
    qsNQQuadraticLocal D H v (a * b ^ 2) = qsNQQuadraticLocal D H v a := by
  rw [pow_two, (qs_nq0_quadratic_local_mul_div D H v a (b * b)).1,
    (qs_nq0_quadratic_local_mul_div D H v b b).1]
  apply MonoidHom.ext
  intro u
  change qsNQQuadraticLocal D H v a u *
    (qsNQQuadraticLocal D H v b u * qsNQQuadraticLocal D H v b u) =
      qsNQQuadraticLocal D H v a u
  have hsq : qsNQQuadraticLocal D H v b u ^ 2 = 1 :=
    congrArg (fun f : (v.adicCompletion K)ˣ →* ℂˣ => f u)
      (qs_nq0_quadratic_local_square D H v b)
  rw [← pow_two, hsq, mul_one]

/-- An integral generator of a finite exterior prime product has the exterior-generator predicate. -/
theorem qs_nq0_integral_exterior_of_isGen
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (Sd : SData K CE condη) (T : Finset (FinPlace K)) (c : 𝓞 K)
    (hc : Sd.IsGen (c : K) (qsIdealOf T)) :
    qsIsExteriorGenerator Sd.Sf T c := by
  classical
  have hcount (v : FinPlace K) :
      FractionalIdeal.count K v
        (qsIdealOf T : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
          if v ∈ T then 1 else 0 := by
    change FractionalIdeal.count K v
      ((FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K)) K)
        (∏ w ∈ T, w.asIdeal)) = _
    rw [map_prod]
    change FractionalIdeal.count K v
      (∏ w ∈ T, (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) = _
    rw [FractionalIdeal.count_prod K v T
      (fun w : FinPlace K => (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
      (fun w _ => FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)]
    simp [FractionalIdeal.count_maximal]
  have hc0 : c ≠ 0 := fun h => hc.2.1 (by simp [h])
  refine ⟨hc0, ?_⟩
  intro v hv
  have hlog : WithZero.log (v.valuation K (c : K)) =
      -(if v ∈ T then (1 : ℤ) else 0) := by
    have h := qs_nq0_count_spanSingleton_eq_neg_log_valuation v (c : K) hc.2.1
    rw [hc.2.2 v hv, hcount v] at h
    omega
  have hval : v.valuation K (c : K) =
      if v ∈ T then WithZero.exp (-1 : ℤ) else 1 := by
    calc
      v.valuation K (c : K) = WithZero.exp (WithZero.log (v.valuation K (c : K))) :=
        (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hc.2.1)).symm
      _ = _ := by rw [hlog]; split_ifs <;> simp
  constructor
  · rw [← v.valuation_lt_one_iff_mem (K := K) c, hval]
    by_cases hvT : v ∈ T <;> simp [hvT]
  · intro hmem
    have hle := (v.intValuation_le_pow_iff_mem c 2).mpr hmem
    rw [← v.valuation_of_algebraMap (K := K), hval] at hle
    by_cases hvT : v ∈ T <;> norm_num [hvT] at hle

/-- An exterior generator becomes an integral exterior generator after an S-supported square. -/
theorem qs_nq0_integral_corrected_generator
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (Sd : SData K CE condη) (T : Finset (FinPlace K)) (a : Kˣ)
    (ha : Sd.IsGen (a : K) (qsIdealOf T)) :
    ∃ b c : 𝓞 K, b ≠ 0 ∧
      (c : K) = (a : K) * (b : K) ^ 2 ∧
      Sd.IsGen (c : K) (qsIdealOf T) ∧ qsIsExteriorGenerator Sd.Sf T c := by
  obtain ⟨b, hb, hbsupport, c, hceq⟩ := qs_nq0_integral_square_clearing Sd a
    (qs_nq0_generator_is_sinteger Sd (qsIdealOf T) (a : K) ha)
  have hbK : (b : K) ≠ 0 := by
    intro h
    exact hb ((IsFractionRing.injective (𝓞 K) K) (by simpa using h))
  have hcK : (c : K) ≠ 0 := by
    rw [hceq]
    exact mul_ne_zero a.ne_zero (pow_ne_zero _ hbK)
  have hval (v : FinPlace K) (hv : v ∉ Sd.Sf) :
      v.valuation K (c : K) = v.valuation K (a : K) := by
    have hbval : v.valuation K (b : K) = 1 :=
      (qs_nq0_residue_ne_zero_iff_valuation_one v (b : K)).mp (hbsupport v hv)
    rw [hceq, map_mul, map_pow, hbval, one_pow, mul_one]
  have hcgen : Sd.IsGen (c : K) (qsIdealOf T) := by
    refine ⟨ha.1, hcK, ?_⟩
    intro v hv
    rw [qs_nq0_count_spanSingleton_eq_neg_log_valuation v (c : K) hcK,
      hval v hv, ← qs_nq0_count_spanSingleton_eq_neg_log_valuation v (a : K) a.ne_zero]
    exact ha.2.2 v hv
  exact ⟨b, c, hb, hceq, hcgen, qs_nq0_integral_exterior_of_isGen Sd T c hcgen⟩

/-- The integral quadratic symbol equals the quadratic prime value, including ramified zeros. -/
theorem qs_nq0_integral_quadratic_prime_value
    (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (c : 𝓞 K) (hc : (c : K) ≠ 0) (hsq : c ∉ v.asIdeal ^ 2)
    (χ : HeckeChar K)
    (hloc : χ.loc v = qsNQQuadraticLocal D H v
      (toLoc v (Units.mk0 (c : K) hc))) :
    χ.primeValue v = (qsQuadSymbolAt v c : ℂ) := by
  classical
  let a : Kˣ := Units.mk0 (c : K) hc
  by_cases hmem : c ∈ v.asIdeal
  · have hexp : v.valuation K (c : K) =
        WithZero.exp (WithZero.log (v.valuation K (c : K))) :=
      (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hc)).symm
    have hloglt : WithZero.log (v.valuation K (c : K)) < 0 := by
      have hlt := (v.valuation_lt_one_iff_mem (K := K) c).mpr hmem
      rw [hexp, WithZero.exp_lt_one_iff] at hlt
      exact hlt
    have hloggt : (-2 : ℤ) < WithZero.log (v.valuation K (c : K)) := by
      have hnotle : ¬ v.valuation K (c : K) ≤ WithZero.exp (-2 : ℤ) := by
        intro hle
        apply hsq
        apply (v.intValuation_le_pow_iff_mem c 2).mp
        rwa [← v.valuation_of_algebraMap (K := K)]
      have hlt := lt_of_not_ge hnotle
      rw [hexp, WithZero.exp_lt_exp] at hlt
      exact hlt
    have hlog : WithZero.log (v.valuation K (c : K)) = -1 := by omega
    have hcount : FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = 1 := by
      rw [qs_nq0_count_spanSingleton_eq_neg_log_valuation v (a : K) a.ne_zero]
      change -WithZero.log (v.valuation K (c : K)) = 1
      rw [hlog]
      norm_num
    obtain ⟨b, hbval, hbnontrivial⟩ :=
      qs_nq0_quadratic_local_nontrivial D H v h6 a hcount
    have hram : ¬ χ.UnramifiedAt v := by
      intro hunram
      let L := v.adicCompletion K
      have hval : Valued.v ((toLoc v b : Lˣ) : L) = 1 := by
        change Valued.v (algebraMap K L (b : K)) = 1
        exact (v.valuedAdicCompletion_eq_valuation' (b : K)).trans hbval
      have hunit : toLoc v b ∈ (v.adicCompletionIntegers K).units :=
        HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hval
      apply hbnontrivial
      rw [← hloc]
      exact hunram (toLoc v b) hunit.1 hunit.2
    let : v.asIdeal.IsMaximal := v.isMaximal
    let : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    let : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
    have hzero : Ideal.Quotient.mk v.asIdeal c = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simp [HeckeChar.primeValue, hram, qsQuadSymbolAt, hzero]
  · have hval : v.valuation K (c : K) = 1 :=
      v.valuation_eq_one_iff_notMem.mpr hmem
    calc
      χ.primeValue v = chi D v (c : K) ^ 3 :=
        (qs_nq0_quadratic_prime_value D H v h6 a hval χ hloc).2
      _ = (qsQuadSymbolAt v c : ℂ) := qs_nq0_chi_cube_quad_symbol D v h6 c

end ArtinPrimitiveRoots.A2
