import ArtinPrimitiveRoots.Proofs.a2_cond_lead_p.ConductorGenerator
import Mathlib.Analysis.Complex.Circle
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.NumberField.Discriminant.Different

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical nonZeroDivisors
noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private noncomputable def conductorPrimePowerGen (v : A1.FinPlace F) : 𝓞 F :=
  Classical.choose (conductorDenominatorIdeal_pow_principal v.asIdeal v.ne_bot)

private theorem conductorPrimePowerGen_spec (v : A1.FinPlace F) :
    Ideal.span {conductorPrimePowerGen v} =
      v.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) :=
  Classical.choose_spec (conductorDenominatorIdeal_pow_principal v.asIdeal v.ne_bot)

private theorem conductor_count_span_prime_power (v w : A1.FinPlace F) (n : ℕ)
    {a : 𝓞 F} (ha : Ideal.span {a} = v.asIdeal ^ n) :
    FractionalIdeal.count F w
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
        if w = v then n else 0 := by
  classical
  have ha0 : a ≠ 0 := by
    intro h
    have hbot : v.asIdeal ^ n = (⊥ : Ideal (𝓞 F)) := by
      simpa [h] using ha.symm
    exact (pow_ne_zero n v.ne_bot) hbot
  rw [← FractionalIdeal.coeIdeal_span_singleton, ha, FractionalIdeal.coeIdeal_pow]
  by_cases hwv : w = v
  · subst w
    simpa using (FractionalIdeal.count_pow_self F v n)
  · have hvw : v ≠ w := Ne.symm hwv
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime F w hvw]
    simp [hwv]

private noncomputable def conductorBetaExponent (c : Fˣ) (v : A1.FinPlace F) : ℕ :=
  Int.toNat (max 0 (-WithZero.log (v.valuation F (c : F))))

private noncomputable def conductorBeta (S : A1.SData F CE condη) (c : Fˣ) : F :=
  ∏ v : S.Sf, (conductorPrimePowerGen v.1 : F) ^ conductorBetaExponent c v.1

private theorem conductorPrimePowerGen_ne_zero (v : A1.FinPlace F) :
    conductorPrimePowerGen v ≠ 0 := by
  intro h
  have hspan := conductorPrimePowerGen_spec v
  have hbot : (⊥ : Ideal (𝓞 F)) = v.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) := by
    simpa [h] using hspan
  exact (pow_ne_zero (Fintype.card (ClassGroup (𝓞 F))) v.ne_bot) hbot.symm

private theorem conductorBeta_ne_zero (S : A1.SData F CE condη) (c : Fˣ) :
    conductorBeta S c ≠ 0 := by
  classical
  unfold conductorBeta
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  exact pow_ne_zero _ ((FaithfulSMul.algebraMap_injective (𝓞 F) F).ne
    (conductorPrimePowerGen_ne_zero v.1))

private theorem conductorPrimePowerGen_valuation (v w : A1.FinPlace F) :
    v.valuation F (conductorPrimePowerGen w : F) =
      WithZero.exp (-(if v = w then Fintype.card (ClassGroup (𝓞 F)) else 0 : ℤ)) := by
  have hcount := conductor_count_span_prime_power w v
    (Fintype.card (ClassGroup (𝓞 F))) (conductorPrimePowerGen_spec w)
  have ha0 : (conductorPrimePowerGen w : F) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) F).ne
      (conductorPrimePowerGen_ne_zero w)
  have hlog : WithZero.log (v.valuation F (conductorPrimePowerGen w : F)) =
      -(if v = w then (Fintype.card (ClassGroup (𝓞 F)) : ℤ) else 0) := by
    rw [conductor_spanSingleton_count v _ ha0] at hcount
    norm_cast at hcount ⊢
    linarith
  rw [← hlog, WithZero.exp_log]
  exact (v.valuation F).ne_zero_iff.mpr ha0

private theorem conductorPrimePowerGen_pow_valuation (c : Fˣ)
    (v w : A1.FinPlace F) :
    v.valuation F ((conductorPrimePowerGen w : F) ^ conductorBetaExponent c w) =
      if v = w then
        WithZero.exp (-((Fintype.card (ClassGroup (𝓞 F)) : ℕ) *
          conductorBetaExponent c w : ℤ)) else 1 := by
  rw [map_pow, conductorPrimePowerGen_valuation]
  by_cases hvw : v = w
  · subst v
    rw [← WithZero.exp_nsmul]
    congr 1
    simp [nsmul_eq_mul, mul_comm]
  · simp [hvw]

private theorem conductorBeta_valuation (S : A1.SData F CE condη) (c : Fˣ)
    (v : A1.FinPlace F) :
    v.valuation F (conductorBeta S c) =
      if hv : v ∈ S.Sf then
        WithZero.exp (-((Fintype.card (ClassGroup (𝓞 F)) : ℕ) *
          conductorBetaExponent c v : ℤ)) else 1 := by
  classical
  by_cases hv : v ∈ S.Sf
  · let vi : S.Sf := ⟨v, hv⟩
    rw [conductorBeta, map_prod]
    rw [Finset.prod_eq_single vi]
    · simpa [hv] using conductorPrimePowerGen_pow_valuation c v v
    · intro j hj hne
      have hvj : v ≠ j.1 := by
        intro h
        exact hne (Subtype.ext h.symm)
      simpa [hvj] using conductorPrimePowerGen_pow_valuation c v j.1
    · intro hnot
      exact (hnot (Finset.mem_univ vi)).elim
  · rw [conductorBeta, map_prod]
    simp [hv]
    change (S.Sf.attach.prod fun t : S.Sf =>
      v.valuation F (conductorPrimePowerGen t.1 : F) ^ conductorBetaExponent c t.1) = 1
    apply Finset.prod_eq_one
    intro t ht
    have htv : v ≠ t.1 := by
      intro h
      exact hv (h ▸ t.2)
    simpa [htv] using conductorPrimePowerGen_pow_valuation c v t.1

private theorem conductorBetaExponent_bound (c : Fˣ) (v : A1.FinPlace F) :
    -WithZero.log (v.valuation F (c : F)) ≤
      ((Fintype.card (ClassGroup (𝓞 F)) : ℕ) * conductorBetaExponent c v : ℤ) := by
  let ord : ℤ := -WithZero.log (v.valuation F (c : F))
  let n := conductorBetaExponent c v
  have hcast : (n : ℤ) = max 0 ord := by
    simpa [n, ord, conductorBetaExponent] using
      (Int.toNat_of_nonneg (le_max_left (0 : ℤ) ord))
  have hcard : 1 ≤ Fintype.card (ClassGroup (𝓞 F)) :=
    Nat.succ_le_of_lt (Fintype.card_pos)
  have hmul : n ≤ Fintype.card (ClassGroup (𝓞 F)) * n := by
    calc
      n = 1 * n := by simp
      _ ≤ Fintype.card (ClassGroup (𝓞 F)) * n := Nat.mul_le_mul_right n hcard
  have hmul' : (n : ℤ) ≤
      ((Fintype.card (ClassGroup (𝓞 F)) : ℕ) * n : ℤ) := by exact_mod_cast hmul
  change ord ≤ _
  calc
    ord ≤ max 0 ord := le_max_right _ _
    _ = (n : ℤ) := hcast.symm
    _ ≤ ((Fintype.card (ClassGroup (𝓞 F)) : ℕ) * n : ℤ) := hmul'

private theorem conductorBeta_div_le_one_of_mem (S : A1.SData F CE condη)
    (c : Fˣ) (v : A1.FinPlace F) (hv : v ∈ S.Sf) :
    v.valuation F (conductorBeta S c) / v.valuation F (c : F) ≤ 1 := by
  have hc0 : v.valuation F (c : F) ≠ 0 := (v.valuation F).ne_zero_iff.mpr c.ne_zero
  let ord : ℤ := -WithZero.log (v.valuation F (c : F))
  have hcval : v.valuation F (c : F) = WithZero.exp (-ord) := by
    simpa [ord, neg_neg] using (WithZero.exp_log hc0).symm
  have hβ := conductorBeta_valuation S c v
  rw [dif_pos hv] at hβ
  have hβle : v.valuation F (conductorBeta S c) ≤ v.valuation F (c : F) := by
    rw [hβ, hcval]
    exact (WithZero.exp_le_exp).2 (neg_le_neg (conductorBetaExponent_bound c v))
  exact (div_le_one₀ (pos_iff_ne_zero.mpr hc0)).2 hβle

private theorem conductorBeta_valuation_le_one (S : A1.SData F CE condη)
    (c : Fˣ) (v : A1.FinPlace F) : v.valuation F (conductorBeta S c) ≤ 1 := by
  rw [conductorBeta_valuation]
  by_cases hv : v ∈ S.Sf
  · rw [dif_pos hv]
    apply (WithZero.exp_le_one_iff).2
    exact neg_nonpos.mpr (by exact_mod_cast (Nat.zero_le
      (Fintype.card (ClassGroup (𝓞 F)) * conductorBetaExponent c v)))
  · simp [hv]

private theorem conductorBeta_valuation_eq_one_of_not_mem (S : A1.SData F CE condη)
    (c : Fˣ) (v : A1.FinPlace F) (hv : v ∉ S.Sf) :
    v.valuation F (conductorBeta S c) = 1 := by
  simpa [conductorBeta_valuation, hv]

private theorem conductorTrace_argument_integral (S : A1.SData F CE condη)
    (q : S.ExtIdeal) (c : Fˣ) (hgen : S.IsGen (c : F) q.1)
    (t : 𝓞 F) (ht : t ∈ q.1) (x : 𝓞 F) :
    (conductorBeta S c) * (t : F) * (x : F) / (c : F) ∈
      Set.range (algebraMap (𝓞 F) F) := by
  let z : F := conductorBeta S c * (t : F) * (x : F) / (c : F)
  have hc0 (v : A1.FinPlace F) : v.valuation F (c : F) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr c.ne_zero
  have htx (v : A1.FinPlace F) : v.valuation F (t : F) ≤ 1 ∧
      v.valuation F (x : F) ≤ 1 := by
    exact ⟨v.valuation_le_one t, v.valuation_le_one x⟩
  have hval (v : A1.FinPlace F) : v.valuation F z ≤ 1 := by
    dsimp [z]
    rw [map_div₀, map_mul, map_mul]
    by_cases hv : v ∈ S.Sf
    · have hbc := conductorBeta_div_le_one_of_mem S c v hv
      have hparts := htx v
      calc
        (v.valuation F (conductorBeta S c) * v.valuation F (t : F) *
            v.valuation F (x : F)) / v.valuation F (c : F) =
            (v.valuation F (conductorBeta S c) / v.valuation F (c : F)) *
              v.valuation F (t : F) * v.valuation F (x : F) := by
                simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ 1 :=
          mul_le_one₀ (mul_le_one₀ hbc bot_le hparts.1) bot_le hparts.2
    · have hbeta := conductorBeta_valuation_eq_one_of_not_mem S c v hv
      have hcval := SData.IsGen.valuation_eq_exp_neg_idealExp S hgen v hv
      have he := conductorIdeal_le_local_power q.1 q.2.1 v
      have htP : t ∈ v.asIdeal ^ A1.idealExp v q.1 := he ht
      have htval : v.valuation F (t : F) ≤
          WithZero.exp (-(A1.idealExp v q.1 : ℤ)) := by
        change v.valuation F (algebraMap (𝓞 F) F t) ≤ _
        rw [v.valuation_of_algebraMap]
        exact (v.intValuation_le_pow_iff_mem t _).2 htP
      have hratio : v.valuation F (t : F) / v.valuation F (c : F) ≤ 1 := by
        apply (div_le_one₀ (pos_iff_ne_zero.mpr (hc0 v))).2
        rw [hcval]
        exact htval
      have hparts := htx v
      calc
        (v.valuation F (conductorBeta S c) * v.valuation F (t : F) *
            v.valuation F (x : F)) / v.valuation F (c : F) =
            (v.valuation F (t : F) / v.valuation F (c : F)) *
              v.valuation F (x : F) := by
                simp [hbeta, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ 1 := mul_le_one₀ hratio bot_le hparts.2
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one F z hval

private theorem conductorTraceFourier_eq_one_of_traceDual (z : F)
    (hz : z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F)) :
    Real.fourierChar (((Algebra.trace ℚ F z : ℚ) : ℝ)) = 1 := by
  have htr := (Submodule.mem_traceDual.mp hz) 1 (by simp)
  have htr' : Algebra.trace ℚ F z ∈ (algebraMap ℤ ℚ).range := by
    simpa only [Algebra.traceForm_apply, mul_one] using htr
  obtain ⟨n, hn⟩ := RingHom.mem_range.mp htr'
  have hcast : ((Algebra.trace ℚ F z : ℚ) : ℝ) = (n : ℝ) := by
    exact_mod_cast hn.symm
  rw [hcast]
  rw [Real.fourierChar_apply', show 2 * Real.pi * (n : ℝ) =
    (n : ℝ) * (2 * Real.pi) by ring, Circle.exp_intCast_mul, Circle.exp_two_pi]
  simp

private abbrev conductorCodifferent : FractionalIdeal (𝓞 F)⁰ F :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)

private theorem conductorTraceDual_valuation_le_one (S : A1.SData F CE condη)
    (v : A1.FinPlace F) (hvS : v ∉ S.Sf) {z : F} (hz0 : z ≠ 0)
    (hdual : z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F)) :
    v.valuation F z ≤ 1 := by
  let D := differentIdeal ℤ (𝓞 F)
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot
  have hDnot : ¬ D ≤ v.asIdeal := by
    intro hle
    exact hvS (S.different_mem v hle)
  have hDcount : FractionalIdeal.count F v (D : FractionalIdeal (𝓞 F)⁰ F) = 0 := by
    rw [FractionalIdeal.count_coe F v hD0]
    have hcount : (Associates.mk v.asIdeal).count (Associates.mk D).factors = 0 := by
      by_contra hcount
      have hdvd := (Associates.count_ne_zero_iff_dvd hD0 v.irreducible).mp hcount
      exact hDnot (Ideal.dvd_iff_le.mp hdvd)
    exact_mod_cast hcount
  have hDcod : (D : FractionalIdeal (𝓞 F)⁰ F) = conductorCodifferent⁻¹ := by
    simpa [D, conductorCodifferent] using
      (coeIdeal_differentIdeal ℤ ℚ F (𝓞 F))
  have hcodcount : FractionalIdeal.count F v conductorCodifferent = 0 := by
    rw [hDcod, FractionalIdeal.count_inv] at hDcount
    linarith
  have hzCod : z ∈ (conductorCodifferent (F := F) : Submodule (𝓞 F) F) := by
    simpa [conductorCodifferent, FractionalIdeal.coe_dual_one] using hdual
  have hspanle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z ≤
      conductorCodifferent :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hzCod
  have hcountle := FractionalIdeal.count_mono F v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hz0) hspanle
  have hcountz := conductor_spanSingleton_count v z hz0
  have hlogle : WithZero.log (v.valuation F z) ≤ 0 := by
    rw [hcountz] at hcountle
    linarith
  simpa using (WithZero.log_le_iff_le_exp
    ((v.valuation F).ne_zero_iff.mpr hz0)).mp hlogle

private theorem conductorTraceDual_not_mem_of_valuation_gt_one (S : A1.SData F CE condη)
    (v : A1.FinPlace F) (hvS : v ∉ S.Sf) {z : F} (hz0 : z ≠ 0)
    (hzval : 1 < v.valuation F z) :
    z ∉ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) := by
  intro hzdual
  have hle := conductorTraceDual_valuation_le_one S v hvS hz0 hzdual
  exact (not_lt_of_ge hle) hzval

private theorem conductorRealFourierChar_eq_one_iff_int (r : ℚ) :
    Real.fourierChar (r : ℝ) = 1 ↔ ∃ n : ℤ, (n : ℚ) = r := by
  constructor
  · intro h
    have hC : Complex.exp ((2 * Real.pi * (r : ℝ)) * Complex.I) = 1 := by
      have h' := congrArg (fun z : Circle => (z : ℂ)) h
      simpa [Real.fourierChar_apply'] using h'
    have hC' : Complex.exp ((2 * Real.pi * (r : ℝ)) * Complex.I) = Complex.exp 0 := by
      simpa using hC
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hC'
    have him := congrArg Complex.im hn
    have hreal : (2 * Real.pi : ℝ) * (r : ℝ) = (n : ℝ) * (2 * Real.pi) := by
      simpa [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using him
    have hrat : (n : ℚ) = r := by
      have hreal' : (r : ℝ) = (n : ℝ) := by
        apply (mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0))
        calc
          (2 * Real.pi : ℝ) * (r : ℝ) = (n : ℝ) * (2 * Real.pi) := hreal
          _ = (2 * Real.pi : ℝ) * (n : ℝ) := by ring
      exact_mod_cast hreal'.symm
    exact ⟨n, hrat⟩
  · rintro ⟨n, rfl⟩
    rw [Real.fourierChar_apply']
    norm_cast
    rw [show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring,
      Circle.exp_intCast_mul, Circle.exp_two_pi]
    simp

private noncomputable def conductorTraceScale (β : F) (c : Fˣ) : 𝓞 F →+ ℝ :=
  (algebraMap ℚ ℝ).toAddMonoidHom.comp
    ((Algebra.trace ℚ F).toAddMonoidHom.comp
      ((AddMonoidHom.mulLeft (β / (c : F))).comp
        (algebraMap (𝓞 F) F).toAddMonoidHom))

private noncomputable def conductorTraceAddChar (β : F) (c : Fˣ) : AddChar (𝓞 F) ℂ :=
  Circle.coeHom.compAddChar
    (Real.fourierChar.compAddMonoidHom (conductorTraceScale β c))

private theorem conductorTraceAddChar_apply (β : F) (c : Fˣ) (x : 𝓞 F) :
    conductorTraceAddChar β c x =
      (Real.fourierChar (((Algebra.trace ℚ F (β * (x : F) / (c : F)) : ℚ) : ℝ)) : ℂ) := by
  change (Real.fourierChar
      (((Algebra.trace ℚ F ((β / (c : F)) * (x : F)) : ℚ) : ℝ)) : ℂ) = _
  congr 2
  congr 1
  field_simp [c.ne_zero]

private theorem conductorTraceAddChar_one_on_ideal (S : A1.SData F CE condη)
    (q : S.ExtIdeal) (c : Fˣ) (hgen : S.IsGen (c : F) q.1)
    (t : 𝓞 F) (ht : t ∈ q.1) : conductorTraceAddChar (conductorBeta S c) c t = 1 := by
  let z : F := conductorBeta S c * (t : F) / (c : F)
  have hzrange : z ∈ Set.range (algebraMap (𝓞 F) F) := by
    simpa [z] using conductorTrace_argument_integral S q c hgen t ht 1
  have hzsub : z ∈ (1 : Submodule (𝓞 F) F) := by
    rw [Submodule.one_eq_range]
    change ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = z
    exact hzrange
  have hzdual : z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) :=
    Submodule.one_le_traceDual_one hzsub
  have hfour := conductorTraceFourier_eq_one_of_traceDual z hzdual
  have hfour' := congrArg (fun y : Circle => (y : ℂ)) hfour
  simpa [z, conductorTraceAddChar_apply, mul_div_assoc] using hfour'

private noncomputable def conductorTraceQuotientChar (S : A1.SData F CE condη)
    (q : S.ExtIdeal) (c : Fˣ) (hgen : S.IsGen (c : F) q.1) :
    AddChar (ConductorResidueRing q) ℂ := by
  classical
  let θ := conductorTraceAddChar (conductorBeta S c) c
  refine ⟨fun x => θ (Quotient.out x), ?_, ?_⟩
  · have h0 : Quotient.out (0 : ConductorResidueRing q) ∈ q.1 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa using (Ideal.Quotient.mk_out (0 : ConductorResidueRing q))
    exact conductorTraceAddChar_one_on_ideal S q c hgen _ h0
  · intro x y
    let a : 𝓞 F := Quotient.out x
    let b : 𝓞 F := Quotient.out y
    let d : 𝓞 F := Quotient.out (x + y)
    have hmk : Ideal.Quotient.mk q.1 d = Ideal.Quotient.mk q.1 (a + b) := by
      calc
        Ideal.Quotient.mk q.1 d = x + y := Ideal.Quotient.mk_out (x + y)
        _ = Ideal.Quotient.mk q.1 a + Ideal.Quotient.mk q.1 b := by
          rw [← Ideal.Quotient.mk_out x, ← Ideal.Quotient.mk_out y]
        _ = Ideal.Quotient.mk q.1 (a + b) := by rw [map_add]
    have hdiff : d - (a + b) ∈ q.1 := Ideal.Quotient.eq.mp hmk
    have hθdiff := conductorTraceAddChar_one_on_ideal S q c hgen _ hdiff
    have hθdiff' : θ (d - (a + b)) = 1 := by simpa [θ] using hθdiff
    have hd : d = (a + b) + (d - (a + b)) := by ring
    calc
      θ d = θ ((a + b) + (d - (a + b))) := congrArg θ hd
      _ = θ (a + b) * θ (d - (a + b)) := θ.map_add_eq_mul _ _
      _ = θ a * θ b := by simp [hθdiff', θ.map_add_eq_mul]

@[simp] private theorem conductorTraceQuotientChar_mk (S : A1.SData F CE condη)
    (q : S.ExtIdeal) (c : Fˣ) (hgen : S.IsGen (c : F) q.1) (a : 𝓞 F) :
    conductorTraceQuotientChar S q c hgen (Ideal.Quotient.mk q.1 a) =
      conductorTraceAddChar (conductorBeta S c) c a := by
  let θ := conductorTraceAddChar (conductorBeta S c) c
  let r : 𝓞 F := Quotient.out (Ideal.Quotient.mk q.1 a)
  have hmk : Ideal.Quotient.mk q.1 r = Ideal.Quotient.mk q.1 a :=
    Ideal.Quotient.mk_out (Ideal.Quotient.mk q.1 a)
  have hdiff : r - a ∈ q.1 := Ideal.Quotient.eq.mp hmk
  have hθdiff := conductorTraceAddChar_one_on_ideal S q c hgen _ hdiff
  have hr : r = a + (r - a) := by ring
  change θ (Quotient.out (Ideal.Quotient.mk q.1 a)) = θ a
  rw [show Quotient.out (Ideal.Quotient.mk q.1 a) = r from rfl, hr,
    θ.map_add_eq_mul, hθdiff, mul_one]

private theorem conductor_ideal_has_valuation_gap (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (a : 𝓞 F) (ha : a ∉ I) :
    ∃ v : A1.FinPlace F, a ∉ v.asIdeal ^ A1.idealExp v I := by
  have hnot : a ∉ (⨅ v : A1.FinPlace F, v.maxPowDividing I) := by
    simpa [Ideal.iInf_maxPowDividing_eq hI] using ha
  simp only [Ideal.mem_iInf, not_forall] at hnot
  obtain ⟨v, hv⟩ := hnot
  refine ⟨v, ?_⟩
  simpa [A1.idealExp, IsDedekindDomain.HeightOneSpectrum.maxPowDividing] using hv

private theorem conductor_idealExp_eq_zero_of_supported (S : A1.SData F CE condη)
    (I : S.ExtIdeal) (v : A1.FinPlace F) (hv : v ∈ S.Sf) :
    A1.idealExp v I.1 = 0 := by
  by_contra hne
  have hdiv : v.asIdeal ∣ I.1 :=
    (Associates.count_ne_zero_iff_dvd I.2.1 v.irreducible).mp hne
  exact I.2.2 v hv (Ideal.dvd_iff_le.mp hdiv)

private theorem conductor_idealExp_positive_of_valuation_gap
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) {a : 𝓞 F}
    (v : A1.FinPlace F) (ha : a ∉ v.asIdeal ^ A1.idealExp v I) :
    0 < A1.idealExp v I := by
  by_contra hpos
  have hzero : A1.idealExp v I = 0 := Nat.eq_zero_of_not_pos hpos
  rw [hzero] at ha
  exact ha (by simp)

private theorem exists_trace_fourier_ne_one_of_not_traceDual (z : F)
    (hz : z ∉ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F)) :
    ∃ x : 𝓞 F,
      Real.fourierChar (((Algebra.trace ℚ F (z * (x : F)) : ℚ) : ℝ)) ≠ 1 := by
  by_contra h
  push_neg at h
  apply hz
  rw [Submodule.mem_traceDual]
  intro x hx
  have hxRange : ∃ x₀ : 𝓞 F, algebraMap (𝓞 F) F x₀ = x := by
    rw [Submodule.one_eq_range] at hx
    exact hx
  obtain ⟨x₀, hx₀⟩ := hxRange
  have hchar := h x₀
  have htr : Algebra.trace ℚ F (z * (x : F)) ∈ (algebraMap ℤ ℚ).range := by
    obtain ⟨n, hn⟩ := (conductorRealFourierChar_eq_one_iff_int _).mp hchar
    exact ⟨n, by simpa [← hx₀] using hn⟩
  simpa only [Algebra.traceForm_apply, hx₀, mul_comm] using htr

private theorem conductorTraceQuotientChar_isPrimitive (S : A1.SData F CE condη)
    (q : S.ExtIdeal) (c : Fˣ) (hgen : S.IsGen (c : F) q.1) :
    (conductorTraceQuotientChar S q c hgen).IsPrimitive := by
  classical
  intro a ha
  intro hshift
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective a
  have ha₀ : a₀ ∉ q.1 := by
    intro hmem
    exact ha (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  obtain ⟨v, hva⟩ := conductor_ideal_has_valuation_gap q.1 q.2.1 a₀ ha₀
  have hvS : v ∉ S.Sf := by
    intro hv
    have he0 := conductor_idealExp_eq_zero_of_supported S q v hv
    simpa [he0] using hva
  have hepos : 0 < A1.idealExp v q.1 :=
    conductor_idealExp_positive_of_valuation_gap q.1 q.2.1 v hva
  have hcval := SData.IsGen.valuation_eq_exp_neg_idealExp S hgen v hvS
  have haInt : v.valuation F (a₀ : F) ≤ 1 := v.valuation_le_one a₀
  have haNotLe : ¬ v.valuation F (a₀ : F) ≤
      WithZero.exp (-(A1.idealExp v q.1 : ℤ)) := by
    intro hle
    have hmem : a₀ ∈ v.asIdeal ^ A1.idealExp v q.1 := by
      apply (v.intValuation_le_pow_iff_mem a₀ _).mp
      rw [v.valuation_of_algebraMap] at hle
      exact hle
    exact hva hmem
  have haGt : WithZero.exp (-(A1.idealExp v q.1 : ℤ)) <
      v.valuation F (a₀ : F) := lt_of_not_ge haNotLe
  have hbeta := conductorBeta_valuation_eq_one_of_not_mem S c v hvS
  have hratio : 1 < v.valuation F
      ((conductorBeta S c) * (a₀ : F) / (c : F)) := by
    have hcpos : 0 < v.valuation F (c : F) :=
      WithZero.pos_iff_ne_zero.mpr ((v.valuation F).ne_zero_iff.mpr c.ne_zero)
    have hval := calc
      v.valuation F ((conductorBeta S c) * (a₀ : F) / (c : F)) =
          v.valuation F (a₀ : F) / v.valuation F (c : F) := by
            rw [map_div₀, map_mul, hbeta, one_mul]
      _ > 1 := (one_lt_div₀ hcpos).2 (by simpa [hcval] using haGt)
    exact hval
  have ha₀0 : (a₀ : F) ≠ 0 := by
    intro hzero
    have hzero' : (algebraMap (𝓞 F) F) a₀ = algebraMap (𝓞 F) F 0 := by simpa using hzero
    have hzero'' : a₀ = 0 := (FaithfulSMul.algebraMap_injective (𝓞 F) F) hzero'
    exact ha₀ (hzero'' ▸ q.1.zero_mem)
  have hz0 : ((conductorBeta S c) * (a₀ : F) / (c : F)) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (conductorBeta_ne_zero S c) ha₀0) c.ne_zero
  have hznot := conductorTraceDual_not_mem_of_valuation_gt_one S v hvS hz0 hratio
  obtain ⟨x, hx⟩ := exists_trace_fourier_ne_one_of_not_traceDual
    ((conductorBeta S c) * (a₀ : F) / (c : F)) hznot
  have hshiftEval := congrArg (fun ψ : AddChar (ConductorResidueRing q) ℂ =>
    ψ (Ideal.Quotient.mk q.1 x)) hshift
  have hzero : conductorTraceQuotientChar S q c hgen
      (Ideal.Quotient.mk q.1 (a₀ * x)) = 1 := by
    simpa [AddChar.mulShift_apply, map_mul] using hshiftEval
  have hnontriv : conductorTraceQuotientChar S q c hgen
      (Ideal.Quotient.mk q.1 (a₀ * x)) ≠ 1 := by
    rw [conductorTraceQuotientChar_mk]
    intro heq
    have hfour : Real.fourierChar
        (((Algebra.trace ℚ F ((conductorBeta S c) * ((a₀ * x : 𝓞 F) : F) / (c : F)) : ℚ) : ℝ)) = 1 := by
      apply Circle.coe_injective
      simpa [conductorTraceAddChar_apply] using heq
    have harg : (conductorBeta S c) * ((a₀ * x : 𝓞 F) : F) / (c : F) =
        ((conductorBeta S c) * (a₀ : F) / (c : F)) * (x : F) := by
      change (conductorBeta S c) * algebraMap (𝓞 F) F (a₀ * x) / (c : F) = _
      rw [map_mul]
      field_simp [c.ne_zero]
    rw [harg] at hfour
    exact hx hfour
  exact hnontriv hzero

theorem conductor_primitive_addChar_exists (S : A1.SData F CE condη)
    (q : S.ExtIdeal) : ∃ ψ : AddChar (ConductorResidueRing q) ℂ, ψ.IsPrimitive := by
  obtain ⟨c, hgen⟩ := SData.exists_conductor_generator S q
  exact ⟨conductorTraceQuotientChar S q c hgen,
    conductorTraceQuotientChar_isPrimitive S q c hgen⟩

end ArtinPrimitiveRoots.A2
