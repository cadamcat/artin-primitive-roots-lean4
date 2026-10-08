import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_residues_exists
import ArtinPrimitiveRoots.Arith.SUnit
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical nonZeroDivisors
noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem conductor_spanSingleton_div_count (v : A1.FinPlace F) (x y : F)
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

private theorem conductor_spanSingleton_intValuation_count (v : A1.FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (algebraMap (𝓞 F) F r)) =
      -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

theorem conductor_spanSingleton_count (v : A1.FinPlace F) (z : F)
    (hz : z ≠ 0) :
    FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
      -WithZero.log (v.valuation F z) := by
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
  have hval : v.valuation F z = v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    conductor_spanSingleton_div_count v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    conductor_spanSingleton_intValuation_count v n hn,
    conductor_spanSingleton_intValuation_count v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private theorem conductor_ideal_has_exact_local_element (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) (v : A1.FinPlace F) :
    ∃ a : 𝓞 F, a ∈ I ∧
      a ∉ v.asIdeal ^ (A1.idealExp v I + 1) := by
  let e := A1.idealExp v I
  have hnot : ¬ I ≤ v.asIdeal ^ (e + 1) := by
    intro hle
    have hdvd : v.asIdeal ^ (e + 1) ∣ I := Ideal.dvd_iff_le.mpr hle
    have hdvd' : Associates.mk (v.asIdeal ^ (e + 1)) ∣ Associates.mk I :=
      Associates.mk_dvd_mk.mpr hdvd
    rw [Associates.mk_pow] at hdvd'
    have hcount := (Associates.prime_pow_dvd_iff_le
      (Associates.mk_ne_zero.mpr hI) v.associates_irreducible).mp hdvd'
    change e + 1 ≤ e at hcount
    omega
  obtain ⟨a, haI, hanot⟩ := Set.not_subset_iff_exists_mem_notMem.mp hnot
  exact ⟨a, haI, by simpa [e] using hanot⟩

theorem conductorIdeal_le_local_power (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : A1.FinPlace F) : I ≤ v.asIdeal ^ A1.idealExp v I := by
  calc
    I = ⨅ w : A1.FinPlace F, w.maxPowDividing I := (Ideal.iInf_maxPowDividing_eq hI).symm
    _ ≤ v.maxPowDividing I := iInf_le _ v
    _ = v.asIdeal ^ A1.idealExp v I := rfl

private theorem conductor_exact_local_count (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : A1.FinPlace F) :
    ∃ a : 𝓞 F, a ∈ I ∧ a ≠ 0 ∧
      v.valuation F (a : F) = WithZero.exp (-(A1.idealExp v I : ℤ)) := by
  obtain ⟨a, haI, hanot⟩ := conductor_ideal_has_exact_local_element I hI v
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    exact hanot (v.asIdeal ^ (A1.idealExp v I + 1)).zero_mem
  have hqP : I ≤ v.asIdeal ^ A1.idealExp v I := conductorIdeal_le_local_power I hI v
  have haP : a ∈ v.asIdeal ^ A1.idealExp v I := hqP haI
  have hmultLo : A1.idealExp v I ≤
      emultiplicity v.asIdeal (Ideal.span {a}) := by
    exact (v.intValuation_le_exp_iff_le_emultiplicity).mp
      ((v.intValuation_le_pow_iff_mem a (A1.idealExp v I)).mpr haP)
  have hmultNot : ¬ A1.idealExp v I + 1 ≤
      emultiplicity v.asIdeal (Ideal.span {a}) := by
    intro h
    have hv' : v.intValuation a ≤ WithZero.exp (-((A1.idealExp v I + 1 : ℕ) : ℤ)) :=
      (v.intValuation_le_exp_iff_le_emultiplicity).2 h
    have hmem := (v.intValuation_le_pow_iff_mem a (A1.idealExp v I + 1)).mp hv'
    exact hanot hmem
  have hmult_lt : emultiplicity v.asIdeal (Ideal.span {a}) < ⊤ :=
    lt_of_lt_of_le (lt_of_not_ge hmultNot) le_top
  have hfinite : FiniteMultiplicity v.asIdeal (Ideal.span {a}) :=
    emultiplicity_lt_top.mp hmult_lt
  have hmultNat : multiplicity v.asIdeal (Ideal.span {a}) = A1.idealExp v I := by
    have hlt := hmultNot
    rw [hfinite.emultiplicity_eq_multiplicity] at hlt
    have hle := hmultLo
    rw [hfinite.emultiplicity_eq_multiplicity] at hle
    have hltNat : multiplicity v.asIdeal (Ideal.span {a}) < A1.idealExp v I + 1 :=
      by exact_mod_cast (not_le.mp hlt)
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hltNat)
      (by exact_mod_cast hle)
  have hval : v.valuation F (a : F) =
      WithZero.exp (-(A1.idealExp v I : ℤ)) := by
    rw [v.valuation_of_algebraMap, v.intValuation_eq_exp_neg_multiplicity ha0, hmultNat]
  exact ⟨a, haI, ha0, hval⟩

theorem SData.IsGen.valuation_eq_exp_neg_idealExp (S : A1.SData F CE condη)
    {c : F} {I : Ideal (𝓞 F)} (hgen : S.IsGen c I)
    (v : A1.FinPlace F) (hv : v ∉ S.Sf) :
    v.valuation F c = WithZero.exp (-(A1.idealExp v I : ℤ)) := by
  have hc0 : c ≠ 0 := hgen.2.1
  have hcountC := conductor_spanSingleton_count v c hc0
  rw [hgen.2.2 v hv] at hcountC
  have hcountI : FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F) =
      A1.idealExp v I := by
    rw [FractionalIdeal.count_coe F v hgen.1.1]
    rfl
  rw [hcountI] at hcountC
  have hlog : WithZero.log (v.valuation F c) = -(A1.idealExp v I : ℤ) := by
    linarith
  rw [← hlog, WithZero.exp_log]
  exact (v.valuation F).ne_zero_iff.mpr hc0

theorem conductor_classPower_spanSingleton_count (v w : A1.FinPlace F) (n : ℕ)
    {a : 𝓞 F} (ha : Ideal.span {a} = v.asIdeal ^ n) :
    FractionalIdeal.count F w
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
        if w = v then n else 0 :=
  by
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

/-- Every exterior ideal has an S-integer generator, using the PID hypothesis in SData. -/
theorem SData.exists_conductor_generator (S : A1.SData F CE condη)
    (I : S.ExtIdeal) : ∃ c : Fˣ, S.IsGen (c : F) I.1 := by
  classical
  letI : IsLocalization (conductorDenominators S) S.R :=
    conductorSInteger_isLocalization S
  letI : IsPrincipalIdealRing S.R := S.pid
  let A := Ideal.map (algebraMap (𝓞 F) S.R) I.1
  have hA0 : A ≠ ⊥ := by
    intro hbot
    obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot I.2.1
    have hmap : algebraMap (𝓞 F) S.R a ∈ A := Ideal.mem_map_of_mem _ haI
    rw [hbot] at hmap
    have : algebraMap (𝓞 F) S.R a = 0 := by simpa using hmap
    exact ha0 ((FaithfulSMul.algebraMap_injective (𝓞 F) S.R) this)
  have hprincipal : A.IsPrincipal := by infer_instance
  obtain ⟨c, hc⟩ := hprincipal.principal
  have hspan : Ideal.span {c} = A := hc.symm
  have hc0 : (c : S.R) ≠ 0 := by
    intro h
    apply hA0
    rw [← hspan, h, Ideal.span_singleton_eq_bot]
  have hcF : (c : F) ≠ 0 := by
    intro h
    exact hc0 (Subtype.ext h)
  let cu : Fˣ := Units.mk0 (c : F) hcF
  refine ⟨cu, ?_⟩
  refine ⟨I.2, hcF, ?_⟩
  intro v hvS
  obtain ⟨a, haI, ha0, haval⟩ := conductor_exact_local_count I.1 I.2.1 v
  have hcA : (c : S.R) ∈ A := by rw [← hspan]; exact Ideal.mem_span_singleton_self _
  obtain ⟨y, hcd⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (conductorDenominators S) S.R
      (I := I.1) (z := (c : S.R))).mp hcA
  let b : 𝓞 F := y.1
  let d : conductorDenominators S := y.2
  have hbI : b ∈ I.1 := y.1.property
  have hcdF : (c : F) * ((d : 𝓞 F) : F) = (b : F) := by
    exact congrArg (fun z : S.R => (z : F)) hcd
  have hdval : v.valuation F ((d : 𝓞 F) : F) = 1 := d.property.2 v hvS
  have hbval : v.valuation F (b : F) ≤
      WithZero.exp (-(A1.idealExp v I.1 : ℤ)) := by
    have hbP : b ∈ v.asIdeal ^ A1.idealExp v I.1 := by
      have hIP : I.1 ≤ v.asIdeal ^ A1.idealExp v I.1 :=
        conductorIdeal_le_local_power I.1 I.2.1 v
      exact hIP hbI
    have hbint : v.intValuation b ≤ WithZero.exp (-(A1.idealExp v I.1 : ℤ)) :=
      (v.intValuation_le_pow_iff_mem b _).2 hbP
    change v.valuation F (algebraMap (𝓞 F) F b) ≤ _
    rw [v.valuation_of_algebraMap]
    exact hbint
  have hcvalUpper : v.valuation F (c : F) ≤
      WithZero.exp (-(A1.idealExp v I.1 : ℤ)) := by
    have hmul := congrArg (v.valuation F) hcdF
    rw [map_mul, hdval, mul_one] at hmul
    simpa [hmul] using hbval
  have hxA : algebraMap (𝓞 F) S.R a ∈ A := Ideal.mem_map_of_mem _ haI
  have hxspan : algebraMap (𝓞 F) S.R a ∈ Ideal.span {c} := by simpa [hspan] using hxA
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hxspan
  have hxaF : (a : F) = (c : F) * (r : F) := by
    have hr' := congrArg (fun z : S.R => (z : F)) hr
    simpa [mul_comm] using hr'
  have hrval : v.valuation F (r : F) ≤ 1 := r.property v hvS
  have hcvalLower : WithZero.exp (-(A1.idealExp v I.1 : ℤ)) ≤
      v.valuation F (c : F) := by
    rw [hxaF] at haval
    rw [map_mul] at haval
    calc
      WithZero.exp (-(A1.idealExp v I.1 : ℤ)) =
          v.valuation F (c : F) * v.valuation F (r : F) := haval.symm
      _ ≤ v.valuation F (c : F) := mul_le_of_le_one_right (bot_le) hrval
  have hcval : v.valuation F (c : F) =
      WithZero.exp (-(A1.idealExp v I.1 : ℤ)) := le_antisymm hcvalUpper hcvalLower
  have hcountI : FractionalIdeal.count F v (I.1 : FractionalIdeal (𝓞 F)⁰ F) =
      A1.idealExp v I.1 := by
    rw [FractionalIdeal.count_coe F v I.2.1]
    rfl
  calc
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) =
        A1.idealExp v I.1 := by
          rw [conductor_spanSingleton_count v (c : F) hcF, hcval]
          simp
    _ = FractionalIdeal.count F v (I.1 : FractionalIdeal (𝓞 F)⁰ F) := hcountI.symm

end ArtinPrimitiveRoots.A2
