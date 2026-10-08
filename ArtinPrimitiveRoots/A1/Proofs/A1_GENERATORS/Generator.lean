import ArtinPrimitiveRoots.A1.Residue
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Localization.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A1Generators

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Denominators which are units at every finite place outside the chosen set. -/
def generatorDenominators (S : SData F CE condη) : Submonoid (𝓞 F) where
  carrier := {d | d ≠ 0 ∧ ∀ v : FinPlace F, v ∉ S.Sf → v.valuation F (d : F) = 1}
  one_mem' := by
    refine ⟨by norm_num, ?_⟩
    intro v hv
    exact v.valuation_eq_one_iff_notMem.mpr (Ideal.IsPrime.one_notMem v.isPrime)
  mul_mem' := by
    rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩
    refine ⟨mul_ne_zero ha hb, ?_⟩
    intro v hv
    change v.valuation F ((a : F) * (b : F)) = 1
    rw [map_mul, hfa v hv, hfb v hv]
    simp

private def generatorDenominatorIdeal (x : F) : Ideal (𝓞 F) where
  carrier := {d | ∃ a : 𝓞 F, (d : F) * x = (a : F)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩
    refine ⟨x₀ + y₀, ?_⟩
    change ((a : F) + (b : F)) * x = (x₀ : F) + (y₀ : F)
    rw [add_mul, hx₀, hy₀]
  smul_mem' := by
    rintro a d ⟨x₀, hx₀⟩
    refine ⟨a * x₀, ?_⟩
    change ((a : F) * (d : F)) * x = (a : F) * (x₀ : F)
    rw [mul_assoc, hx₀]

private theorem generatorDenominatorIdeal_mem (x : F) (d : 𝓞 F) :
    d ∈ generatorDenominatorIdeal (F := F) x ↔
      ∃ a : 𝓞 F, (d : F) * x = (a : F) := Iff.rfl

private theorem generatorDenominatorIdeal_ne_bot (x : F) :
    generatorDenominatorIdeal (F := F) x ≠ ⊥ := by
  obtain ⟨a, b, hab⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) x
  have hden : ((b : 𝓞 F) : F) * x = (a : 𝓞 F) := by
    rw [← hab, IsFractionRing.mk'_eq_div]
    have hb : ((b : 𝓞 F) : F) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
    field_simp [hb]
  have hb : (b : 𝓞 F) ∈ generatorDenominatorIdeal (F := F) x := ⟨a, hden⟩
  intro h
  have : (b : 𝓞 F) ∈ (⊥ : Ideal (𝓞 F)) := h ▸ hb
  have hbzero : (b : 𝓞 F) = 0 := by simpa using this
  exact (mem_nonZeroDivisors_iff_ne_zero.mp b.property) hbzero

private theorem generatorDenominatorIdeal_not_le (S : SData F CE condη)
    (x : S.R) (v : FinPlace F) (hv : v ∉ S.Sf) :
    ¬ generatorDenominatorIdeal (F := F) (x : F) ≤ v.asIdeal := by
  have hxv : v.valuation F (x : F) ≤ 1 := x.property v hv
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (x : F) hxv
  have hd : (d : 𝓞 F) ∈ generatorDenominatorIdeal (F := F) (x : F) := by
    rw [generatorDenominatorIdeal_mem]
    exact ⟨n, by
      change ((d : 𝓞 F) : F) * (x : F) = (n : 𝓞 F)
      rw [mul_comm]
      exact hnd⟩
  intro hle
  exact d.property (hle hd)

private def generatorIdealExponent (v : FinPlace F) (I : Ideal (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

private theorem generatorIdeal_has_exact_local_element (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) (v : FinPlace F) :
    ∃ a : 𝓞 F, a ∈ I ∧ a ∉ v.asIdeal ^ (generatorIdealExponent v I + 1) := by
  let e := generatorIdealExponent v I
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

private theorem generatorIdeal_le_local_power (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : FinPlace F) : I ≤ v.asIdeal ^ generatorIdealExponent v I := by
  calc
    I = ⨅ w : FinPlace F, w.maxPowDividing I := (Ideal.iInf_maxPowDividing_eq hI).symm
    _ ≤ v.maxPowDividing I := iInf_le _ v
    _ = v.asIdeal ^ generatorIdealExponent v I := rfl

private theorem generatorExactLocalCount (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : FinPlace F) :
    ∃ a : 𝓞 F, a ∈ I ∧ a ≠ 0 ∧
      v.valuation F (a : F) = WithZero.exp (-(generatorIdealExponent v I : ℤ)) := by
  obtain ⟨a, haI, hanot⟩ := generatorIdeal_has_exact_local_element I hI v
  let e := generatorIdealExponent v I
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    exact hanot (v.asIdeal ^ (e + 1)).zero_mem
  have hqP : I ≤ v.asIdeal ^ e := generatorIdeal_le_local_power I hI v
  have haP : a ∈ v.asIdeal ^ e := hqP haI
  have hmultLo : e ≤ emultiplicity v.asIdeal (Ideal.span {a}) := by
    exact (v.intValuation_le_exp_iff_le_emultiplicity).mp
      ((v.intValuation_le_pow_iff_mem a e).mpr haP)
  have hmultNot : ¬ e + 1 ≤ emultiplicity v.asIdeal (Ideal.span {a}) := by
    intro h
    have hv' : v.intValuation a ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ)) :=
      (v.intValuation_le_exp_iff_le_emultiplicity).2 h
    have hmem := (v.intValuation_le_pow_iff_mem a (e + 1)).mp hv'
    exact hanot hmem
  have hmult_lt : emultiplicity v.asIdeal (Ideal.span {a}) < ⊤ :=
    lt_of_lt_of_le (lt_of_not_ge hmultNot) le_top
  have hfinite : FiniteMultiplicity v.asIdeal (Ideal.span {a}) :=
    emultiplicity_lt_top.mp hmult_lt
  have hmultNat : multiplicity v.asIdeal (Ideal.span {a}) = e := by
    have hlt := hmultNot
    rw [hfinite.emultiplicity_eq_multiplicity] at hlt
    have hle := hmultLo
    rw [hfinite.emultiplicity_eq_multiplicity] at hle
    have hltNat : multiplicity v.asIdeal (Ideal.span {a}) < e + 1 := by
      exact_mod_cast (not_le.mp hlt)
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hltNat) (by exact_mod_cast hle)
  have hval : v.valuation F (a : F) = WithZero.exp (-(e : ℤ)) := by
    rw [v.valuation_of_algebraMap, v.intValuation_eq_exp_neg_multiplicity ha0, hmultNat]
  exact ⟨a, haI, ha0, by simpa [e] using hval⟩

private theorem generatorSpanSingleton_div_count (v : FinPlace F) (x y : F)
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

private theorem generatorSpanSingleton_integral_count (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private theorem generatorSpanSingleton_count (v : FinPlace F) (z : F)
    (hz : z ≠ 0) :
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
  have hval : HeightOneSpectrum.valuation F v z =
      v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    generatorSpanSingleton_div_count v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    generatorSpanSingleton_integral_count v n hn,
    generatorSpanSingleton_integral_count v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private theorem generator_spanSingleton_count (v : FinPlace F) (z : F)
    (hz : z ≠ 0) :
    FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
        -WithZero.log (HeightOneSpectrum.valuation F v z) :=
  generatorSpanSingleton_count v z hz

private theorem generator_count_coe (v : FinPlace F) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) :
    FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F) =
      generatorIdealExponent v I := by
  rw [FractionalIdeal.count_coe F v hI]
  rfl

private theorem generatorDenominatorIdeal_pow_principal (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) :
    ∃ a : 𝓞 F, Ideal.span {a} = I ^ Fintype.card (ClassGroup (𝓞 F)) := by
  let p0 : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let n := Fintype.card (ClassGroup (𝓞 F))
  have hClass : ClassGroup.mk0 p0 ^ n = 1 := by
    simpa [n] using (pow_card_eq_one (x := ClassGroup.mk0 p0))
  have hn0 : I ^ n ≠ ⊥ := pow_ne_zero _ hI
  have hClassPow : ClassGroup.mk0
      ⟨I ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr hn0⟩ = 1 := by
    change ClassGroup.mk0 (p0 ^ n) = 1
    rw [map_pow]
    exact hClass
  have hPrincipal : (I ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hn0)).mp hClassPow
  obtain ⟨a, ha⟩ := hPrincipal.principal
  exact ⟨a, ha.symm⟩

private theorem generatorDenominatorIdeal_pow_not_le (S : SData F CE condη)
    (x : S.R) (v : FinPlace F) (hv : v ∉ S.Sf) :
    ¬ (generatorDenominatorIdeal (F := F) (x : F)) ^
        Fintype.card (ClassGroup (𝓞 F)) ≤ v.asIdeal := by
  intro hle
  have hD : generatorDenominatorIdeal (F := F) (x : F) ≤ v.asIdeal :=
    v.isPrime.le_of_pow_le hle
  exact generatorDenominatorIdeal_not_le S x v hv hD

private theorem generatorSInteger_fraction (S : SData F CE condη) (x : S.R) :
    ∃ a : 𝓞 F, ∃ d : generatorDenominators S,
      (x : F) * ((d : 𝓞 F) : F) = (a : F) := by
  classical
  let D := generatorDenominatorIdeal (F := F) (x : F)
  have hD : D ≠ ⊥ := generatorDenominatorIdeal_ne_bot (x : F)
  obtain ⟨a, ha⟩ := generatorDenominatorIdeal_pow_principal D hD
  have hpow : Ideal.span {a} = D ^ Fintype.card (ClassGroup (𝓞 F)) := ha
  have hcard : Fintype.card (ClassGroup (𝓞 F)) ≠ 0 :=
    (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 F))).ne'
  have hpowle : D ^ Fintype.card (ClassGroup (𝓞 F)) ≤ D := Ideal.pow_le_self hcard
  have haDpow : a ∈ D ^ Fintype.card (ClassGroup (𝓞 F)) := by
    rw [← hpow]
    exact Ideal.subset_span (by simp)
  have haD : a ∈ D := hpowle haDpow
  obtain ⟨b, hbx⟩ := (generatorDenominatorIdeal_mem (x : F) a).mp haD
  have ha0 : a ≠ 0 := by
    intro h
    have hpownz : D ^ Fintype.card (ClassGroup (𝓞 F)) ≠ ⊥ := pow_ne_zero _ hD
    have hbot : D ^ Fintype.card (ClassGroup (𝓞 F)) = (⊥ : Ideal (𝓞 F)) := by
      simpa [h] using hpow.symm
    exact hpownz hbot
  have hfinite (v : FinPlace F) (hv : v ∉ S.Sf) : v.valuation F (a : F) = 1 := by
    have hnotle := generatorDenominatorIdeal_pow_not_le S x v hv
    have hnotmem : a ∉ v.asIdeal := by
      intro hamem
      apply hnotle
      rw [← hpow]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hamem)
    exact v.valuation_eq_one_iff_notMem.mpr hnotmem
  refine ⟨b, ⟨a, ⟨ha0, hfinite⟩⟩, ?_⟩
  change (x : F) * ((a : 𝓞 F) : F) = (b : F)
  rw [mul_comm]
  exact hbx

private theorem generatorDenominator_inverse_mem (S : SData F CE condη)
    (d : generatorDenominators S) : (((d : 𝓞 F) : F)⁻¹) ∈ S.R := by
  intro v hv
  have hd := d.property.2 v hv
  rw [map_inv₀, hd]
  simp

private theorem generatorSInteger_isLocalization (S : SData F CE condη) :
    IsLocalization (generatorDenominators S) S.R := by
  rw [isLocalization_iff]
  constructor
  · intro d
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨((d : 𝓞 F) : F)⁻¹, generatorDenominator_inverse_mem S d⟩, ?_⟩
    apply Subtype.ext
    change ((d : 𝓞 F) : F) * ((d : 𝓞 F) : F)⁻¹ = 1
    exact mul_inv_cancel₀ ((FaithfulSMul.algebraMap_injective (𝓞 F) F).ne d.property.1)
  constructor
  · intro x
    obtain ⟨a, d, hxd⟩ := generatorSInteger_fraction S x
    refine ⟨(a, d), ?_⟩
    apply Subtype.ext
    change (x : F) * ((d : 𝓞 F) : F) = (a : F)
    exact hxd
  · intro a b hab
    have habF : (a : F) = (b : F) := congrArg (fun z : S.R => (z : F)) hab
    have habO : a = b := (FaithfulSMul.algebraMap_injective (𝓞 F) F) habF
    exact ⟨1, by simp [habO]⟩

/-- The PID hypothesis on `S.R` gives a generator of every exterior ideal, with the
valuation predicate used by `S.IsGen`. -/
theorem exists_generator_of_pid (S : SData F CE condη) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) : ∃ a : Fˣ, S.IsGen (a : F) I := by
  classical
  letI : IsLocalization (generatorDenominators S) S.R := generatorSInteger_isLocalization S
  letI : IsPrincipalIdealRing S.R := S.pid
  let A := Ideal.map (algebraMap (𝓞 F) S.R) I
  have hA0 : A ≠ ⊥ := by
    intro hbot
    obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI.1
    have hmap : algebraMap (𝓞 F) S.R a ∈ A := Ideal.mem_map_of_mem _ haI
    rw [hbot] at hmap
    have hzero : algebraMap (𝓞 F) S.R a = 0 := by simpa using hmap
    exact ha0 ((FaithfulSMul.algebraMap_injective (𝓞 F) S.R) hzero)
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
  refine ⟨hI, hcF, ?_⟩
  intro v hvS
  obtain ⟨a, haI, ha0, haval⟩ := generatorExactLocalCount I hI.1 v
  have hcA : (c : S.R) ∈ A := by rw [← hspan]; exact Ideal.mem_span_singleton_self _
  obtain ⟨y, hcd⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (generatorDenominators S) S.R
      (I := I) (z := (c : S.R))).mp hcA
  let b : 𝓞 F := y.1
  let d : generatorDenominators S := y.2
  have hbI : b ∈ I := y.1.property
  have hcdF : (c : F) * ((d : 𝓞 F) : F) = (b : F) := by
    exact congrArg (fun z : S.R => (z : F)) hcd
  have hdval : v.valuation F ((d : 𝓞 F) : F) = 1 := d.property.2 v hvS
  have hbval : v.valuation F (b : F) ≤
      WithZero.exp (-(generatorIdealExponent v I : ℤ)) := by
    have hbP : b ∈ v.asIdeal ^ generatorIdealExponent v I := by
      have hIP : I ≤ v.asIdeal ^ generatorIdealExponent v I :=
        generatorIdeal_le_local_power I hI.1 v
      exact hIP hbI
    have hbint : v.intValuation b ≤
        WithZero.exp (-(generatorIdealExponent v I : ℤ)) :=
      (v.intValuation_le_pow_iff_mem b _).2 hbP
    change v.valuation F (algebraMap (𝓞 F) F b) ≤ _
    rw [v.valuation_of_algebraMap]
    exact hbint
  have hcvalUpper : v.valuation F (c : F) ≤
      WithZero.exp (-(generatorIdealExponent v I : ℤ)) := by
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
  have hcvalLower : WithZero.exp (-(generatorIdealExponent v I : ℤ)) ≤
      v.valuation F (c : F) := by
    rw [hxaF] at haval
    rw [map_mul] at haval
    calc
      WithZero.exp (-(generatorIdealExponent v I : ℤ)) =
          v.valuation F (c : F) * v.valuation F (r : F) := haval.symm
      _ ≤ v.valuation F (c : F) := mul_le_of_le_one_right bot_le hrval
  have hcval : v.valuation F (c : F) =
      WithZero.exp (-(generatorIdealExponent v I : ℤ)) :=
    le_antisymm hcvalUpper hcvalLower
  have hcountI : FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F) =
      generatorIdealExponent v I := generator_count_coe v I hI.1
  calc
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) =
        generatorIdealExponent v I := by
          rw [generatorSpanSingleton_count v (c : F) hcF, hcval]
          simp
    _ = FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F) := hcountI.symm

/-- Multiplication by an `S`-unit preserves the frozen generator predicate. -/
theorem isGen_mul_sUnit (S : SData F CE condη) (u : S.US) (a : Fˣ)
    {I : Ideal (𝓞 F)} (ha : S.IsGen (a : F) I) :
    S.IsGen (((u : Fˣ) * a : Fˣ) : F) I := by
  refine ⟨ha.1, mul_ne_zero (u : Fˣ).ne_zero a.ne_zero, ?_⟩
  intro v hv
  have huval : v.valuation F (u : Fˣ) = 1 := u.property v hv
  have hcountsame :
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            ((((u : Fˣ) * a : Fˣ) : F))) =
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) := by
    rw [generatorSpanSingleton_count v
        ((((u : Fˣ) * a : Fˣ) : F)) (mul_ne_zero (u : Fˣ).ne_zero a.ne_zero),
      generatorSpanSingleton_count v (a : F) a.ne_zero]
    have hcast : (((u : Fˣ) * a : Fˣ) : F) = ((u : Fˣ) : F) * (a : F) := rfl
    rw [hcast, map_mul, huval, one_mul]
  exact hcountsame.trans (ha.2.2 v hv)

end ArtinPrimitiveRoots.Proofs.A1Generators
