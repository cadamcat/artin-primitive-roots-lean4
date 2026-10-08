import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.TorusInd
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! Shared declarations used by the local Jacquet packages and P-ANALYSIS-S. -/

open MeasureTheory Filter
open Set

/-- Borel σ-algebra on a completion (Mathlib has no `MeasurableSpace` instance on `adicCompletion`). -/
noncomputable instance instMeasurableSpaceAdicCompletion (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _

instance instBorelSpaceAdicCompletion (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- **def:loc-haar**: the additive Haar measure of `K_v` normalized by `μ(O_v) = 1`. -/
structure LocHaar (v : FinPlace F) where
  μ : Measure (v.adicCompletion F)
  isHaar : μ.IsAddHaarMeasure
  norm_O : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1

attribute [instance] LocHaar.isHaar

section SharedJacquet

variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

local instance theta_residue_maximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance theta_residue_field (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

private theorem theta_residue_rep (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal) (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply IsFractionRing.injective (𝓞 F) F
    simp only [map_mul]
    rw [← hex.choose_spec.2, ← hab]
    ring
  have hqcross := congrArg (Ideal.Quotient.mk v.asIdeal) hcross
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hdq : Ideal.Quotient.mk v.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold residue
  rw [dif_pos hex]
  rw [← div_eq_mul_inv, div_eq_div_iff hdq hbq]
  simpa only [map_mul] using hqcross

private theorem theta_residue_algInt (v : FinPlace F) (a : 𝓞 F) :
    residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a := by
  have h := theta_residue_rep v (algebraMap (𝓞 F) F a) a 1
    (Ideal.IsPrime.one_notMem v.isPrime) (by simp)
  simpa using h

private theorem theta_residue_integral_congr (v : FinPlace F) (a b : 𝓞 F)
    (hab : Valued.v (((a : F) : v.adicCompletion F) - ((b : F) : v.adicCompletion F)) < 1) :
    residue v (a : F) = residue v (b : F) := by
  have hab' : Valued.v (algebraMap F (v.adicCompletion F) ((a : F) - (b : F))) < 1 := by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, map_sub] using hab
  have hval : v.valuation F ((a : F) - (b : F)) < 1 := by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using hab'
  have hmem : a - b ∈ v.asIdeal := (v.valuation_lt_one_iff_mem (K := F) _).1 hval
  rw [theta_residue_algInt, theta_residue_algInt]
  rw [← sub_eq_zero, ← map_sub]
  exact (Ideal.Quotient.eq_zero_iff_mem).2 hmem

private theorem theta_chi_congr (D : FieldData F) (v : FinPlace F) (x y : F)
    (h : residue v x = residue v y) : chi D v x = chi D v y := by
  simp only [chi, chiAlg, h]

private theorem theta_chi_six (D : FieldData F) (v : FinPlace F) (x : F)
    (hx : residue v x ≠ 0) : chi D v x ^ (6 : ℕ) = 1 := by
  have h := congrArg Units.val
    ((mem_rootsOfUnity 6 (chiAlg v x : (𝓞 F)ˣ)).1 (chiAlg v x).property)
  rw [chi, if_neg hx, ← map_pow, ← map_pow]
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_one] using
    congrArg (fun a : 𝓞 F => D.σ0 (algebraMap (𝓞 F) F a)) h

private theorem localChi_of_approx (D : FieldData F) (v : FinPlace F)
    (t : (v.adicCompletion F)ˣ) (a : 𝓞 F) (ha : a ∉ v.asIdeal)
    (hta : Valued.v ((t : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F a)) < 1) :
    localChi D v t = chi D v (a : F) := by
  have hex : ∃ b : 𝓞 F, b ∉ v.asIdeal ∧ Valued.v ((t : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F b)) < 1 := ⟨a, ha, hta⟩
  have hcmp' : Valued.v (((hex.choose : F) : v.adicCompletion F) -
      ((a : F) : v.adicCompletion F)) < 1 := by
    have h := (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).map_sub_lt hta hex.choose_spec.2
    have hEq : ((t : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) -
        ((t : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F hex.choose)) =
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F hex.choose) -
            algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := by ring
    rw [hEq] at h
    exact h
  have hres : residue v (hex.choose : F) = residue v (a : F) := by
    exact theta_residue_integral_congr v hex.choose a hcmp'
  unfold localChi
  rw [dif_pos hex]
  exact theta_chi_congr D v _ _ hres

private theorem local_unit_approximant (v : FinPlace F) (u : (v.adicCompletion F)ˣ)
    (hu : IsLocUnit v u) :
    ∃ a : 𝓞 F, a ∉ v.asIdeal ∧ Valued.v ((u : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F a)) < 1 := by
  let O := v.adicCompletionIntegers F
  let uO : O := ⟨(u : v.adicCompletion F), hu.1⟩
  let uInvO : O := ⟨((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), hu.2⟩
  have hprod : uO * uInvO = (1 : O) := by
    apply Subtype.ext
    simp [uO, uInvO]
  have hresNe : IsLocalRing.residue O uO ≠ 0 := by
    intro hz
    have hp := congrArg (IsLocalRing.residue O) hprod
    rw [map_mul, map_one, hz, zero_mul] at hp
    exact zero_ne_one hp
  let e := v.residueFieldEquivAdicCompletionIntegers (K := F)
  let r := e.symm (IsLocalRing.residue O uO)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective r
  have hbar : e (Ideal.Quotient.mk v.asIdeal a) = IsLocalRing.residue O uO := by
    rw [ha]
    exact e.apply_symm_apply _
  have hresA : IsLocalRing.residue O uO =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (algebraMap (𝓞 F) O a) := by
    rw [← hbar, v.residueFieldEquivAdicCompletionIntegers_apply_mk]
  have ha_not : a ∉ v.asIdeal := by
    intro hamem
    have hmk : Ideal.Quotient.mk v.asIdeal a = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hamem
    have hzero : IsLocalRing.residue O uO = 0 := by
      rw [← hbar, hmk]
      rfl
    exact hresNe hzero
  have hdiff_mem : uO - algebraMap (𝓞 F) O a ∈ IsLocalRing.maximalIdeal O := by
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    have hzero : IsLocalRing.residue O (uO - algebraMap (𝓞 F) O a) = 0 := by
      rw [map_sub]
      have hresA' : IsLocalRing.residue O uO =
          IsLocalRing.residue O (algebraMap (𝓞 F) O a) := by
        change IsLocalRing.residue O uO =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (algebraMap (𝓞 F) O a)
        exact hresA
      rw [hresA', sub_self]
    exact hzero
  have hmax (z : O) : z ∈ IsLocalRing.maximalIdeal O ↔
      Valued.v (z : v.adicCompletion F) < 1 := by
    change z ∈ IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (v.adicCompletion F)
          (WithZero (Multiplicative ℤ))).valuationSubring) ↔ _
    exact Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))
  have hlt : Valued.v ((uO - algebraMap (𝓞 F) O a : O) : v.adicCompletion F) < 1 :=
    (hmax _).1 hdiff_mem
  have hmap : ((algebraMap (𝓞 F) O a : O) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := by
    exact (HeightOneSpectrum.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers
      (K := F) (v := v) a).symm
  have hcoerce : ((uO - algebraMap (𝓞 F) O a : O) : v.adicCompletion F) =
      (u : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := by
    change (uO : v.adicCompletion F) -
      ((algebraMap (𝓞 F) O a : O) : v.adicCompletion F) = _
    rw [hmap]
  rw [hcoerce] at hlt
  refine ⟨a, ha_not, ?_⟩
  exact hlt

private theorem theta_roots6_reduce_injective (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) :
    Function.Injective (fun ζ : rootsOfUnity 6 (𝓞 F) =>
      Ideal.Quotient.mk v.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F)) := by
  intro ζ η h
  let ρ : rootsOfUnity 6 (𝓞 F) := ζ * η⁻¹
  let q : (𝓞 F)ˣ →* (𝓞 F ⧸ v.asIdeal)ˣ :=
    Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom
  have hq : q ζ = q η := by
    apply Units.ext
    exact h
  have hqηinv : q (η⁻¹ : rootsOfUnity 6 (𝓞 F)) = (q η)⁻¹ := by
    apply Units.ext
    simp [q, Units.val_inv_eq_inv_val]
  have hqρ : q ρ = 1 := by
    change q (ζ * η⁻¹) = 1
    rw [map_mul, hqηinv, hq]
    exact mul_inv_cancel (q η)
  have hρ : Ideal.Quotient.mk v.asIdeal ((ρ : (𝓞 F)ˣ) : 𝓞 F) = 1 := by
    exact congrArg Units.val hqρ
  let r : 𝓞 F := ((ρ : (𝓞 F)ˣ) : 𝓞 F)
  have hrpow : r ^ 6 = 1 := by
    have hp := (mem_rootsOfUnity 6 (ρ : (𝓞 F)ˣ)).mp ρ.2
    exact congrArg (fun z : (𝓞 F)ˣ => (z : 𝓞 F)) hp
  let S : 𝓞 F := ∑ i ∈ Finset.range 6, r ^ i
  have hsexp : S = 1 + r + r ^ 2 + r ^ 3 + r ^ 4 + r ^ 5 := by
    simp [S, Finset.sum_range_succ]
  have hgeom : (r - 1) * S = 0 := by
    rw [hsexp]
    calc
      (r - 1) * (1 + r + r ^ 2 + r ^ 3 + r ^ 4 + r ^ 5) = r ^ 6 - 1 := by ring
      _ = 0 := by rw [hrpow]; ring
  by_contra hne
  have hr_ne : r ≠ 1 := by
    intro heq
    have hρval : (ρ : (𝓞 F)ˣ) = 1 := by
      apply Units.ext
      exact heq
    have hρroot : ρ = 1 := by
      apply Subtype.ext
      exact hρval
    have hz := congrArg (fun z : rootsOfUnity 6 (𝓞 F) => z * η) hρroot
    apply hne
    simpa [ρ] using hz
  have hSzero : S = 0 := (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hr_ne)
  have hsum : Ideal.Quotient.mk v.asIdeal S = 6 := by
    have hρr : Ideal.Quotient.mk v.asIdeal r = 1 := by
      dsimp [r]
      exact hρ
    rw [hsexp]
    simp only [map_add, map_one, map_pow, hρr, one_pow]
    norm_num
  have hmk6 : Ideal.Quotient.mk v.asIdeal (6 : 𝓞 F) = 0 := by
    calc
      Ideal.Quotient.mk v.asIdeal (6 : 𝓞 F) = (6 : 𝓞 F ⧸ v.asIdeal) :=
        map_natCast (Ideal.Quotient.mk v.asIdeal) 6
      _ = Ideal.Quotient.mk v.asIdeal S := hsum.symm
      _ = 0 := by rw [hSzero]; exact map_zero (Ideal.Quotient.mk v.asIdeal)
  exact hv ((Ideal.Quotient.eq_zero_iff_mem).1 hmk6)

private theorem theta_chiAlg_spec (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (x : F) (hx : residue v x ≠ 0) :
    Ideal.Quotient.mk v.asIdeal ((chiAlg v x : (𝓞 F)ˣ) : 𝓞 F) =
      residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
  have ⟨hcop, hne1⟩ := coprime_six_of_not_mem_six v hv
  have hdvd6 := six_dvd_absNorm_sub_one D v hv
  have hζ6 : IsPrimitiveRoot (D.ζ12 ^ 2) 6 :=
    D.hζ12.pow_of_dvd (p := 2) (by decide) (by decide)
  have hprim := hζ6.toInteger_isPrimitiveRoot.idealQuotient_mk
    (I := v.asIdeal) hne1 hcop
  have hru : IsUnit (residue v x) := isUnit_iff_ne_zero.mpr hx
  let ru : (𝓞 F ⧸ v.asIdeal)ˣ := hru.unit
  have hrueq : (ru : 𝓞 F ⧸ v.asIdeal) = residue v x := rfl
  have hrpow : (residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, Nat.mul_div_cancel' hdvd6]
    have hvalpow : ((ru : 𝓞 F ⧸ v.asIdeal) ^ (Ideal.absNorm v.asIdeal - 1)) =
        (((ru ^ (Ideal.absNorm v.asIdeal - 1) : (𝓞 F ⧸ v.asIdeal)ˣ) :
          𝓞 F ⧸ v.asIdeal)) := by
      exact (Units.val_pow_eq_pow_val ru _).symm
    have hrucard : ru ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
      have hcard : Nat.card (𝓞 F ⧸ v.asIdeal)ˣ = Ideal.absNorm v.asIdeal - 1 := by
        rw [Nat.card_units, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
      rw [← hcard]
      exact pow_card_eq_one'
    rw [← hrueq, hvalpow, hrucard, Units.val_one]
  obtain ⟨i, hi, heq⟩ := hprim.eq_pow_of_pow_eq_one hrpow
  have hζpow : (hζ6.toInteger ^ i) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ6.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  let ζ₀ : rootsOfUnity 6 (𝓞 F) := rootsOfUnity.mkOfPowEq (hζ6.toInteger ^ i) hζpow
  have hex : ∃ ζ : rootsOfUnity 6 (𝓞 F),
      Ideal.Quotient.mk v.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) =
        residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    refine ⟨ζ₀, ?_⟩
    have hcoe : ((ζ₀ : (𝓞 F)ˣ) : 𝓞 F) = hζ6.toInteger ^ i :=
      rootsOfUnity.coe_mkOfPowEq hζpow
    rw [hcoe, map_pow]
    exact heq
  rw [chiAlg, dif_pos hex]
  exact hex.choose_spec

private theorem theta_chiAlg_mul (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (a b : 𝓞 F)
    (ha : a ∉ v.asIdeal) (hb : b ∉ v.asIdeal) :
    chiAlg v ((a : F) * (b : F)) = chiAlg v (a : F) * chiAlg v (b : F) := by
  have hres_a : residue v (a : F) ≠ 0 := by
    rw [theta_residue_algInt]
    intro hz
    exact ha ((Ideal.Quotient.eq_zero_iff_mem).1 hz)
  have hres_b : residue v (b : F) ≠ 0 := by
    rw [theta_residue_algInt]
    intro hz
    exact hb ((Ideal.Quotient.eq_zero_iff_mem).1 hz)
  have hres_mul : residue v ((a : F) * (b : F)) =
      residue v (a : F) * residue v (b : F) := by
    calc
      residue v ((a : F) * (b : F)) = residue v (algebraMap (𝓞 F) F (a * b)) := by
        congr 1
      _ = Ideal.Quotient.mk v.asIdeal (a * b) := theta_residue_algInt v (a * b)
      _ = Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal b := map_mul _ _ _
      _ = residue v (a : F) * residue v (b : F) := by
        rw [theta_residue_algInt, theta_residue_algInt]
  have hres_mul_ne : residue v ((a : F) * (b : F)) ≠ 0 := by
    rw [hres_mul]
    exact mul_ne_zero hres_a hres_b
  apply theta_roots6_reduce_injective v hv
  change Ideal.Quotient.mk v.asIdeal
      ((chiAlg v ((a : F) * (b : F)) : (𝓞 F)ˣ) : 𝓞 F) =
    Ideal.Quotient.mk v.asIdeal
        (((chiAlg v (a : F) * chiAlg v (b : F) : rootsOfUnity 6 (𝓞 F)) :
        (𝓞 F)ˣ) : 𝓞 F)
  rw [theta_chiAlg_spec D v hv _ hres_mul_ne]
  have hcoe : (((chiAlg v (a : F) * chiAlg v (b : F) : rootsOfUnity 6 (𝓞 F)) :
      (𝓞 F)ˣ) : 𝓞 F) =
      (((chiAlg v (a : F) : (𝓞 F)ˣ) : 𝓞 F) *
        ((chiAlg v (b : F) : (𝓞 F)ˣ) : 𝓞 F)) := by
    push_cast
    rfl
  rw [hcoe, map_mul, theta_chiAlg_spec D v hv _ hres_a,
    theta_chiAlg_spec D v hv _ hres_b]
  rw [← mul_pow, ← hres_mul]

private theorem theta_twelve_dvd_absNorm_sub_one (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) : 12 ∣ Ideal.absNorm v.asIdeal - 1 := by
  have ⟨hcop6, hne1⟩ := coprime_six_of_not_mem_six v hv
  have hcop2 : Nat.Coprime (Ideal.absNorm v.asIdeal) 2 :=
    Nat.Coprime.of_dvd_right (by norm_num : 2 ∣ 6) hcop6
  have hcop3 : Nat.Coprime (Ideal.absNorm v.asIdeal) 3 :=
    Nat.Coprime.of_dvd_right (by norm_num : 3 ∣ 6) hcop6
  have hcop4 : Nat.Coprime (Ideal.absNorm v.asIdeal) 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
      Nat.coprime_pow_right_iff (n := 2) (by norm_num : 0 < 2)]
    exact hcop2
  have hcop12 : Nat.Coprime (Ideal.absNorm v.asIdeal) 12 := by
    rw [show (12 : ℕ) = 3 * 4 by norm_num]
    exact Nat.Coprime.mul_right hcop3 hcop4
  have hζ12 := D.hζ12.toInteger_isPrimitiveRoot.idealQuotient_mk
    (I := v.asIdeal) hne1 hcop12
  let u : (𝓞 F ⧸ v.asIdeal)ˣ := (hζ12.isUnit (by decide)).unit
  have hprim_u : IsPrimitiveRoot u 12 := IsPrimitiveRoot.coe_units_iff.mp hζ12
  have hdiv : 12 ∣ Nat.card (𝓞 F ⧸ v.asIdeal)ˣ := by
    rw [hprim_u.eq_orderOf]
    exact orderOf_dvd_natCard (x := u)
  rwa [Nat.card_units, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] at hdiv

private theorem theta_chiAlg_one (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) : chiAlg v (1 : F) = 1 := by
  have hres : residue v (1 : F) = 1 := by
    simpa using theta_residue_algInt v (1 : 𝓞 F)
  have hresNe : residue v (1 : F) ≠ 0 := by rw [hres]; exact one_ne_zero
  apply theta_roots6_reduce_injective v hv
  change Ideal.Quotient.mk v.asIdeal ((chiAlg v (1 : F) : (𝓞 F)ˣ) : 𝓞 F) =
    Ideal.Quotient.mk v.asIdeal (1 : 𝓞 F)
  rw [theta_chiAlg_spec D v hv (1 : F) hresNe, hres]
  simp

private theorem theta_chiAlg_neg_one (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) : chiAlg v (-1 : F) = 1 := by
  have h12 := theta_twelve_dvd_absNorm_sub_one D v hv
  have hmeq : (Ideal.absNorm v.asIdeal - 1) / 6 =
      2 * ((Ideal.absNorm v.asIdeal - 1) / 12) := by
    rcases h12 with ⟨k, hk⟩
    rw [hk]
    omega
  have hres : residue v (-1 : F) = Ideal.Quotient.mk v.asIdeal (-1 : 𝓞 F) :=
    theta_residue_algInt v (-1 : 𝓞 F)
  have hnot : (-1 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    exact Ideal.IsPrime.one_notMem v.isPrime (by simpa using v.asIdeal.neg_mem h)
  have hresNe : residue v (-1 : F) ≠ 0 := by
    rw [hres]
    intro h
    exact hnot ((Ideal.Quotient.eq_zero_iff_mem).1 h)
  apply theta_roots6_reduce_injective v hv
  change Ideal.Quotient.mk v.asIdeal ((chiAlg v (-1 : F) : (𝓞 F)ˣ) : 𝓞 F) =
    Ideal.Quotient.mk v.asIdeal (1 : 𝓞 F)
  rw [theta_chiAlg_spec D v hv (-1 : F) hresNe, hres, hmeq]
  simp [pow_mul]

private theorem theta_chi_mul (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (a b : 𝓞 F)
    (ha : a ∉ v.asIdeal) (hb : b ∉ v.asIdeal) :
    chi D v ((a : F) * (b : F)) = chi D v (a : F) * chi D v (b : F) := by
  have hres_a : residue v (a : F) ≠ 0 := by
    rw [theta_residue_algInt]
    intro hz
    exact ha ((Ideal.Quotient.eq_zero_iff_mem).1 hz)
  have hres_b : residue v (b : F) ≠ 0 := by
    rw [theta_residue_algInt]
    intro hz
    exact hb ((Ideal.Quotient.eq_zero_iff_mem).1 hz)
  have hres_mul : residue v ((a : F) * (b : F)) =
      residue v (a : F) * residue v (b : F) := by
    calc
      residue v ((a : F) * (b : F)) = residue v (algebraMap (𝓞 F) F (a * b)) := by
        congr 1
      _ = Ideal.Quotient.mk v.asIdeal (a * b) := theta_residue_algInt v (a * b)
      _ = Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal b := map_mul _ _ _
      _ = residue v (a : F) * residue v (b : F) := by
        rw [theta_residue_algInt, theta_residue_algInt]
  have hres_mul_ne : residue v ((a : F) * (b : F)) ≠ 0 := by
    rw [hres_mul]
    exact mul_ne_zero hres_a hres_b
  unfold chi
  rw [if_neg hres_mul_ne, if_neg hres_a, if_neg hres_b,
    theta_chiAlg_mul D v hv a b ha hb]
  simp [map_mul]

private theorem theta_chi_one (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) : chi D v (1 : F) = 1 := by
  have hresEq : residue v (1 : F) = 1 := by
    simpa using theta_residue_algInt v (1 : 𝓞 F)
  have hres : residue v (1 : F) ≠ 0 := by
    rw [hresEq]
    exact one_ne_zero
  simp [chi, hres, theta_chiAlg_one D v hv]

private theorem theta_chi_neg_one (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) : chi D v (-1 : F) = 1 := by
  have hnot : (-1 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    exact Ideal.IsPrime.one_notMem v.isPrime (by simpa using v.asIdeal.neg_mem h)
  have hresEq : residue v (-1 : F) = Ideal.Quotient.mk v.asIdeal (-1 : 𝓞 F) := by
    simpa using theta_residue_algInt v (-1 : 𝓞 F)
  have hres : residue v (-1 : F) ≠ 0 := by
    rw [hresEq]
    intro hz
    exact hnot ((Ideal.Quotient.eq_zero_iff_mem).1 hz)
  simp [chi, hres, theta_chiAlg_neg_one D v hv]

private theorem theta_local_unit_product_approx (v : FinPlace F)
    (u u' : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u) (hu' : IsLocUnit v u')
    (a b : 𝓞 F) (hta : Valued.v ((u : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F a)) < 1)
    (htb : Valued.v ((u' : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F b)) < 1) :
    Valued.v ((((u * u') : (v.adicCompletion F)ˣ) : v.adicCompletion F) -
      algebraMap F _ (algebraMap (𝓞 F) F (a * b))) < 1 := by
  have huval : Valued.v (u : v.adicCompletion F) ≤ 1 := hu.1
  have hbval : Valued.v (algebraMap F (v.adicCompletion F) (b : F)) ≤ 1 := by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using
      (v.valuation_le_one b)
  let A := algebraMap F (v.adicCompletion F) (a : F)
  let B := algebraMap F (v.adicCompletion F) (b : F)
  have hterm1 : Valued.v ((u : v.adicCompletion F) * ((u' : v.adicCompletion F) - B)) < 1 := by
    rw [map_mul]
    calc
      Valued.v (u : v.adicCompletion F) * Valued.v ((u' : v.adicCompletion F) - B) ≤
          1 * Valued.v ((u' : v.adicCompletion F) - B) :=
        mul_le_mul_of_nonneg_right huval zero_le
      _ = Valued.v ((u' : v.adicCompletion F) - B) := one_mul _
      _ < 1 := by simpa [B] using htb
  have hterm2 : Valued.v (((u : v.adicCompletion F) - A) * B) < 1 := by
    rw [map_mul]
    calc
      Valued.v ((u : v.adicCompletion F) - A) * Valued.v B ≤
          Valued.v ((u : v.adicCompletion F) - A) * 1 :=
        mul_le_mul_of_nonneg_left hbval zero_le
      _ = Valued.v ((u : v.adicCompletion F) - A) := mul_one _
      _ < 1 := by simpa [A] using hta
  have hdecomp : (u : v.adicCompletion F) * (u' : v.adicCompletion F) - A * B =
      (u : v.adicCompletion F) * ((u' : v.adicCompletion F) - B) +
        ((u : v.adicCompletion F) - A) * B := by ring
  have hsum : Valued.v ((u : v.adicCompletion F) * ((u' : v.adicCompletion F) - B) +
      ((u : v.adicCompletion F) - A) * B) ≤
      max (Valued.v ((u : v.adicCompletion F) * ((u' : v.adicCompletion F) - B)))
        (Valued.v (((u : v.adicCompletion F) - A) * B)) :=
    Valued.v.map_add_le (le_max_left _ _) (le_max_right _ _)
  have hlt : Valued.v ((u : v.adicCompletion F) * (u' : v.adicCompletion F) - A * B) < 1 := by
    rw [hdecomp]
    exact lt_of_le_of_lt hsum (max_lt_iff.mpr ⟨hterm1, hterm2⟩)
  have hlt' : Valued.v ((((u * u') : (v.adicCompletion F)ˣ) : v.adicCompletion F) - A * B) < 1 := by
    simpa only [Units.val_mul] using hlt
  simpa only [A, B, map_mul] using hlt'

private theorem theta_localChi_mul (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (u u' : (v.adicCompletion F)ˣ)
    (hu : IsLocUnit v u) (hu' : IsLocUnit v u') :
    localChi D v (u * u') = localChi D v u * localChi D v u' := by
  obtain ⟨a, ha, hta⟩ := local_unit_approximant v u hu
  obtain ⟨b, hb, htb⟩ := local_unit_approximant v u' hu'
  have hab : a * b ∉ v.asIdeal := by
    intro hab
    rcases v.isPrime.mem_or_mem hab with ha' | hb'
    · exact ha ha'
    · exact hb hb'
  have hprod := theta_local_unit_product_approx v u u' hu hu' a b hta htb
  have hlocalprod := localChi_of_approx D v (u * u') (a * b) hab hprod
  have hlocala := localChi_of_approx D v u a ha hta
  have hlocalb := localChi_of_approx D v u' b hb htb
  calc
    localChi D v (u * u') = chi D v ((a : F) * (b : F)) := by
      simpa only [map_mul] using hlocalprod
    _ = chi D v (a : F) * chi D v (b : F) := theta_chi_mul D v hv a b ha hb
    _ = localChi D v u * localChi D v u' := by rw [← hlocala, ← hlocalb]

private theorem theta_localChi_six (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (u : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u) :
    localChi D v u ^ (6 : ℕ) = 1 := by
  obtain ⟨a, ha, hta⟩ := local_unit_approximant v u hu
  have hlocal := localChi_of_approx D v u a ha hta
  have hres : residue v (a : F) ≠ 0 := by
    rw [theta_residue_algInt]
    intro hz
    exact ha ((Ideal.Quotient.eq_zero_iff_mem).1 hz)
  rw [hlocal]
  exact theta_chi_six D v (a : F) hres

private theorem theta_localChi_congr (D : FieldData F) (v : FinPlace F)
    (u u' : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u) (hu' : IsLocUnit v u')
    (h : Valued.v ((u : v.adicCompletion F) - (u' : v.adicCompletion F)) < 1) :
    localChi D v u = localChi D v u' := by
  obtain ⟨a, ha, hta⟩ := local_unit_approximant v u hu
  obtain ⟨b, hb, htb⟩ := local_unit_approximant v u' hu'
  let A := algebraMap F (v.adicCompletion F) (a : F)
  let B := algebraMap F (v.adicCompletion F) (b : F)
  have hcast_a : ((a : F) : v.adicCompletion F) = A := by
    exact (congrFun (HeightOneSpectrum.algebraMap_adicCompletion
      (S := 𝓞 F) (K := F) (v := v)) a).symm
  have hcast_b : ((b : F) : v.adicCompletion F) = B := by
    exact (congrFun (HeightOneSpectrum.algebraMap_adicCompletion
      (S := 𝓞 F) (K := F) (v := v)) b).symm
  have hcommonMap : Valued.v ((u' : v.adicCompletion F) - A) < 1 := by
    have h' := (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).map_sub_lt hta h
    have hEq : ((u : v.adicCompletion F) - A) -
        ((u : v.adicCompletion F) - (u' : v.adicCompletion F)) =
          (u' : v.adicCompletion F) - A := by ring
    rw [hEq] at h'
    exact h'
  have hcommon : Valued.v ((u' : v.adicCompletion F) - ((a : F) : v.adicCompletion F)) < 1 := by
    simpa only [hcast_a] using hcommonMap
  have htbMap : Valued.v ((u' : v.adicCompletion F) - B) < 1 := by
    simpa only [B] using htb
  have hbaMap : Valued.v (B - A) < 1 := by
    have h' := (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).map_sub_lt hcommonMap htbMap
    have hEq : ((u' : v.adicCompletion F) - A) -
        ((u' : v.adicCompletion F) - B) = B - A := by ring
    rw [hEq] at h'
    exact h'
  have hba : Valued.v (((b : F) : v.adicCompletion F) -
      ((a : F) : v.adicCompletion F)) < 1 := by
    simpa only [hcast_a, hcast_b] using hbaMap
  have hab : Valued.v (((a : F) : v.adicCompletion F) -
      ((b : F) : v.adicCompletion F)) < 1 := by
    simpa only [Valuation.map_sub_swap] using hba
  have hres := theta_residue_integral_congr v a b hab
  calc
    localChi D v u = chi D v (a : F) := localChi_of_approx D v u a ha hta
    _ = chi D v (b : F) := theta_chi_congr D v _ _ hres
    _ = localChi D v u' := (localChi_of_approx D v u' b hb htb).symm

/-- **jq:localchi**: basic properties of `localChi` on local units at `v ∤ 6`. -/
theorem localChi_basic (hv : (6 : 𝓞 F) ∉ v.asIdeal) :
    localChi D v 1 = 1 ∧ localChi D v (-1) = 1 ∧
    (∀ u u', IsLocUnit v u → IsLocUnit v u' → localChi D v (u * u') = localChi D v u * localChi D v u') ∧
    (∀ u, IsLocUnit v u → localChi D v u ^ 6 = 1) ∧
    (∀ u u', IsLocUnit v u → IsLocUnit v u' →
      Valued.v ((u : v.adicCompletion F) - u') < 1 → localChi D v u = localChi D v u') := by
  have hnegnot : (-1 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    exact Ideal.IsPrime.one_notMem v.isPrime (by simpa using v.asIdeal.neg_mem h)
  have hone := localChi_of_approx D v (1 : (v.adicCompletion F)ˣ) (1 : 𝓞 F)
    (Ideal.IsPrime.one_notMem v.isPrime) (by simp)
  have hminus := localChi_of_approx D v (-1 : (v.adicCompletion F)ˣ) (-1 : 𝓞 F)
    hnegnot (by simp)
  constructor
  · exact hone.trans (theta_chi_one D v hv)
  constructor
  · exact hminus.trans (theta_chi_neg_one D v hv)
  constructor
  · intro u u' hu hu'
    exact theta_localChi_mul D v hv u u' hu hu'
  constructor
  · intro u hu
    exact theta_localChi_six D v hv u hu
  · intro u u' hu hu' h
    exact theta_localChi_congr D v u u' hu hu' h

private lemma theta_count_spanSingleton_div (v : FinPlace F) (x y : F)
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

private lemma theta_count_spanSingleton_eq_neg_log_intValuation (v : FinPlace F)
    (a : 𝓞 F) (ha : a ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F a)) = -WithZero.log (v.intValuation a) := by
  have hspan : (Ideal.span {a} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using ha
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg ha, WithZero.log_exp]
  ring

private lemma theta_count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
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
  have hval : HeightOneSpectrum.valuation F v z =
      v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    theta_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    theta_count_spanSingleton_eq_neg_log_intValuation v n hn,
    theta_count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

/-- **jq:hilb-unit** (tame case of P-COVER cov:ext-law): `C(ϖ^e, u) = χ(u)^{-2e}`. -/
theorem muThree_hilb_unif_unit (hv : (6 : 𝓞 F) ∉ v.asIdeal) (e : ℤ) (u : (v.adicCompletion F)ˣ)
    (hu : IsLocUnit v u) :
    ((muThree D (H.hilb v (unifLoc v ^ e) u) : ℂˣ) : ℂ) = localChi D v u ^ (-(2 * e)) := by
  obtain ⟨a, ha, hta⟩ := local_unit_approximant v u hu
  let a₀ : Fˣ := Units.mk0 (a : F) (by
    intro hz
    apply ha
    have h : a = 0 := IsFractionRing.injective (𝓞 F) F (by simpa using hz)
    rw [h]
    exact Ideal.zero_mem _)
  let aLoc : (v.adicCompletion F)ˣ := toLoc v a₀
  let O := v.adicCompletionIntegers F
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let uO : O := ⟨(u : v.adicCompletion F), hu.1⟩
  let aO : O := algebraMap (𝓞 F) O a
  have hvalA : v.valuation F (a : F) = 1 := by
    apply le_antisymm (v.valuation_le_one (R := 𝓞 F) (K := F) a)
    apply le_of_not_gt
    intro hlt
    exact ha ((v.valuation_lt_one_iff_mem (K := F) a).mp hlt)
  have hmapA : (aO : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (a : F) := by
    exact (v.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers a).symm
  have hvalAO : Valued.v (aO : v.adicCompletion F) = 1 := by
    rw [hmapA]
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using hvalA
  have haUnit : IsUnit aO :=
    (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).2 hvalAO
  let aOUnit : Oˣ := haUnit.unit
  have haOUnit : (aOUnit : O) = aO := haUnit.unit_spec
  let huInvO : O := ⟨((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), hu.2⟩
  have huOInv : uO * huInvO = 1 := by
    apply Subtype.ext
    simp [uO, huInvO]
  have huInvO' : huInvO * uO = 1 := by
    apply Subtype.ext
    simp [uO, huInvO]
  have huUnit : IsUnit uO := ⟨⟨uO, huInvO, huOInv, huInvO'⟩, rfl⟩
  let uOUnit : Oˣ := huUnit.unit
  have huOUnit : (uOUnit : O) = uO := huUnit.unit_spec
  let rOUnit : Oˣ := uOUnit * aOUnit⁻¹
  let rLoc : (v.adicCompletion F)ˣ := u * aLoc⁻¹
  have hmapA₀ : (aLoc : v.adicCompletion F) = (aO : v.adicCompletion F) := by
    rw [hmapA]
    simp [aLoc, a₀, toLoc]
  have hratioO : (rOUnit : O) - 1 = (uO - aO) * ((aOUnit⁻¹ : Oˣ) : O) := by
    have haInv : aO * ((aOUnit⁻¹ : Oˣ) : O) = 1 := by
      rw [← haOUnit]
      simp
    calc
      (rOUnit : O) - 1 = uO * ((aOUnit⁻¹ : Oˣ) : O) - 1 := by
        simp [rOUnit, huOUnit]
      _ = (uO - aO) * ((aOUnit⁻¹ : Oˣ) : O) := by
        rw [sub_mul, haInv]
  have hmax (z : O) : z ∈ m ↔
      Valued.v (z : v.adicCompletion F) < 1 := by
    change z ∈ IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (v.adicCompletion F)
          (WithZero (Multiplicative ℤ))).valuationSubring) ↔ _
    exact Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))
  have hdiffO : uO - aO ∈ m := by
    apply (hmax _).2
    have hcoerce : ((uO - aO : O) : v.adicCompletion F) =
        (u : v.adicCompletion F) - algebraMap F (v.adicCompletion F) (a : F) := by
      change (uO : v.adicCompletion F) - (aO : v.adicCompletion F) = _
      rw [hmapA]
    rw [hcoerce]
    exact hta
  have hrNear : (rOUnit : O) - 1 ∈ m := by
    rw [hratioO]
    exact m.mul_mem_right _ hdiffO
  have h6val : v.valuation F (6 : F) = 1 := by
    apply le_antisymm (v.valuation_le_one (R := 𝓞 F) (K := F) (6 : 𝓞 F))
    apply le_of_not_gt
    intro hlt
    exact hv ((v.valuation_lt_one_iff_mem (K := F) (6 : 𝓞 F)).mp hlt)
  have h6map : (6 : O) = algebraMap (𝓞 F) O (6 : 𝓞 F) := by
    exact (map_natCast (algebraMap (𝓞 F) O) 6).symm
  have hmap6 : ((algebraMap (𝓞 F) O (6 : 𝓞 F) : O) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (6 : F) :=
    (v.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (6 : 𝓞 F)).symm
  have hval6O : Valued.v ((6 : O) : v.adicCompletion F) = 1 := by
    rw [h6map, hmap6]
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using h6val
  have h6not : (6 : O) ∉ m := by
    intro h
    have hlt := (hmax (6 : O)).1 h
    rw [hval6O] at hlt
    exact (lt_irrefl 1) hlt
  have h6Unit : IsUnit (6 : O) := IsLocalRing.notMem_maximalIdeal.mp h6not
  letI : HenselianRing O m := inferInstance
  obtain ⟨cO, hcPow, hcNear⟩ :=
    TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem
      (I := m) (J := m) le_rfl (n := 6) h6Unit hrNear
  have hc0 : (cO : O) ≠ 0 := by
    intro hc
    have hr0 : (rOUnit : O) = 0 := by rw [← hcPow, hc]; simp
    exact rOUnit.ne_zero hr0
  let cLoc : (v.adicCompletion F)ˣ := Units.mk0 (cO : v.adicCompletion F) (by
    simpa using hc0)
  let algU : Oˣ →* (v.adicCompletion F)ˣ :=
    Units.map (algebraMap O (v.adicCompletion F)).toMonoidHom
  have hmapu : algU uOUnit = u := by
    apply Units.ext
    change algebraMap O (v.adicCompletion F) (uOUnit : O) = (u : v.adicCompletion F)
    rw [huOUnit]
    rfl
  have hmapa : algU aOUnit = aLoc := by
    apply Units.ext
    change algebraMap O (v.adicCompletion F) (aOUnit : O) = (aLoc : v.adicCompletion F)
    rw [haOUnit]
    exact hmapA₀.symm
  have hmapr : algU rOUnit = rLoc := by
    calc
      algU rOUnit = algU uOUnit * (algU aOUnit)⁻¹ := by simp [rOUnit]
      _ = rLoc := by rw [hmapu, hmapa]
  have hrOtoK : (rOUnit : v.adicCompletion F) = (rLoc : v.adicCompletion F) := by
    have h := congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) hmapr
    change algebraMap O (v.adicCompletion F) (rOUnit : O) = (rLoc : v.adicCompletion F) at h
    change algebraMap O (v.adicCompletion F) (rOUnit : O) = (rLoc : v.adicCompletion F)
    exact h
  have hcLoc : cLoc ^ 6 = rLoc := by
    apply Units.ext
    change ((cO : O) : v.adicCompletion F) ^ 6 = (rLoc : v.adicCompletion F)
    calc
      ((cO : O) : v.adicCompletion F) ^ 6 = (rOUnit : v.adicCompletion F) := by
        exact congrArg (algebraMap O (v.adicCompletion F)) hcPow
      _ = (rLoc : v.adicCompletion F) := hrOtoK
  have hfactor : rLoc * aLoc = u := by
    dsimp [rLoc]
    simp [mul_assoc]
  have hsymbol_local (b : (v.adicCompletion F)ˣ) :
      H.hilb v u b = H.hilb v aLoc b := by
    calc
      H.hilb v u b = H.hilb v (rLoc * aLoc) b := by rw [hfactor]
      _ = H.hilb v rLoc b * H.hilb v aLoc b := H.mul_left v rLoc aLoc b
      _ = H.hilb v aLoc b := by
        rw [H.sixth_power v rLoc b ⟨cLoc, hcLoc.symm⟩]
        simp
  let π : Fˣ := Units.mk0 (unif v) (unif_ne_zero v)
  have hπval : v.valuation F (unif v) = WithZero.exp (-1 : ℤ) := by
    dsimp [unif]
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (unif v)) = 1 := by
    rw [theta_count_spanSingleton_eq_neg_log_valuation v (unif v) (unif_ne_zero v),
      hπval, WithZero.log_exp]
    norm_num
  have hresA : residue v (a : F) ≠ 0 := by
    rw [theta_residue_algInt]
    exact fun hz => ha ((Ideal.Quotient.eq_zero_iff_mem).1 hz)
  have htame := H.tame v hv a₀ π hresA
  have htame' : (((H.hilb v aLoc (unifLoc v) : rootsOfUnity 6 F) : Fˣ) : F) =
      algebraMap (𝓞 F) F (((chiAlg v (a : F) : (𝓞 F)ˣ) : 𝓞 F)) := by
    simpa [a₀, aLoc, π, unifLoc, hcount, zpow_one] using htame
  have hchi : D.σ0 ((((H.hilb v aLoc (unifLoc v) : rootsOfUnity 6 F) : Fˣ) : F)) =
      chi D v (a : F) := by
    rw [chi, if_neg hresA]
    exact congrArg D.σ0 htame'
  let φ : (v.adicCompletion F)ˣ →* rootsOfUnity 6 F := {
    toFun := fun b => H.hilb v aLoc b
    map_one' := by
      have h := H.skew v aLoc 1
      rw [H.sixth_power v 1 aLoc ⟨1, by simp⟩] at h
      simpa using h
    map_mul' := by intro b b'; exact H.mul_right v aLoc b b'
  }
  let ζ : rootsOfUnity 6 F := H.hilb v aLoc (unifLoc v)
  have hpow : H.hilb v u (unifLoc v ^ e) = ζ ^ e := by
    rw [hsymbol_local]
    change φ (unifLoc v ^ e) = φ (unifLoc v) ^ e
    exact φ.map_zpow (unifLoc v) e
  have htarget : H.hilb v (unifLoc v ^ e) u = ζ ^ (-e) := by
    have h := H.skew v (unifLoc v ^ e) u
    rw [hpow] at h
    rw [mul_comm] at h
    calc
      H.hilb v (unifLoc v ^ e) u = (ζ ^ e)⁻¹ := eq_inv_of_mul_eq_one_right h
      _ = ζ ^ (-e) := by simp
  have hmuEval (ξ : rootsOfUnity 6 F) :
      ((muThree D ξ : ℂˣ) : ℂ) = (D.σ0 ((ξ : Fˣ) : F)) ^ 2 := by
    simp [muThree]
  let σu : Fˣ →* ℂˣ := Units.map D.σ0.toMonoidHom
  have hσzpow (n : ℤ) :
      D.σ0 ((((ζ : Fˣ) ^ n : Fˣ) : F)) =
        (D.σ0 ((ζ : Fˣ) : F)) ^ n := by
    have h := congrArg (fun z : ℂˣ => (z : ℂ)) (σu.map_zpow (ζ : Fˣ) n)
    simpa [σu] using h
  have hζcoe (n : ℤ) :
      ((ζ ^ n : rootsOfUnity 6 F) : Fˣ) = (ζ : Fˣ) ^ n := by
    rfl
  have hmu : ((muThree D (H.hilb v (unifLoc v ^ e) u) : ℂˣ) : ℂ) =
      D.σ0 ((((ζ ^ (-(2 * e)) : rootsOfUnity 6 F) : Fˣ) : F)) := by
    rw [htarget, hmuEval]
    change (D.σ0 (((ζ : Fˣ) ^ (-e) : Fˣ) : F)) ^ 2 =
      D.σ0 (((ζ : Fˣ) ^ (-(2 * e)) : Fˣ) : F)
    rw [hσzpow (-e), hσzpow (-(2 * e))]
    let s : ℂ := D.σ0 ((ζ : Fˣ) : F)
    change (s ^ (-e)) ^ 2 = s ^ (-(2 * e))
    calc
      (s ^ (-e)) ^ 2 = s ^ ((-e) * 2) := by
        rw [← zpow_natCast]
        exact (zpow_mul s (-e) 2).symm
      _ = s ^ (-(2 * e)) := by congr 1 <;> ring
  have hσpow : D.σ0 (((ζ : Fˣ) : F) ^ (-(2 * e))) =
      (D.σ0 ((ζ : Fˣ) : F)) ^ (-(2 * e)) := by
    simpa using hσzpow (-(2 * e))
  calc
    ((muThree D (H.hilb v (unifLoc v ^ e) u) : ℂˣ) : ℂ) =
        D.σ0 ((((ζ ^ (-(2 * e)) : rootsOfUnity 6 F) : Fˣ) : F)) := hmu
    _ = D.σ0 (((ζ : Fˣ) : F) ^ (-(2 * e))) := by simp
    _ = (D.σ0 ((ζ : Fˣ) : F)) ^ (-(2 * e)) := hσpow
    _ = chi D v (a : F) ^ (-(2 * e)) := by rw [hchi]
    _ = localChi D v u ^ (-(2 * e)) := by
      rw [← localChi_of_approx D v u a ha hta]

/-- Normalized prime Gauss sums `g_j = q^{-1/2} Σ_{x mod 𝔭} χ(x)^j ψ(x/ϖ)` (10:384–390). -/
def gaussLoc (D : FieldData F) (A : AddCharData F) (v : FinPlace F) (j : ℤ) : ℂ :=
  ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
    ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, chiPow D v (algebraMap (𝓞 F) F x.out) j *
      A.ψ v (algebraMap F _ (algebraMap (𝓞 F) F x.out / unif v))

theorem g2_eq_gaussLoc (D : FieldData F) (A : AddCharData F) (v : FinPlace F) :
    g2 D A v = gaussLoc D A v 2 := rfl

/-- **jq:gauss-product** (10:391–400): `g_j g_{-j} = 1` for `6 ∤ j` at `v ∤ 6𝔇`. -/
theorem gaussLoc_mul_neg (D : FieldData F) (A : AddCharData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (j : ℤ)
    (hj : ¬ (6 : ℤ) ∣ j) : gaussLoc D A v j * gaussLoc D A v (-j) = 1 := by
  sorry

private def besselExpKernel (ν x u : ℝ) : ℝ :=
  Real.exp (-x * Real.cosh u + ν * u)

private def schlafliKernel (ν x t : ℝ) : ℝ :=
  t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t))

private theorem integrableOn_besselExpKernel_pos (ν x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun u => besselExpKernel ν x u) (Ioi 0) := by
  let g : ℝ → ℝ := fun t => t⁻¹ * Real.exp (-x * Real.cosh (Real.log t) + ν * Real.log t)
  rw [show (fun u => besselExpKernel ν x u) =
      (fun u => Real.exp u * g (Real.exp u)) by
        funext u
        simp [g, besselExpKernel, Real.log_exp]
      ]
  have hbase : IntegrableOn
      (fun t : ℝ => t ^ |ν| * Real.exp (-(x / 2) * t ^ (1 : ℝ))) (Ioi 0) := by
    exact integrableOn_rpow_mul_exp_neg_mul_rpow (s := |ν|) (p := 1) (b := x / 2)
      (by have := abs_nonneg ν; linarith) one_pos (by linarith)
  have hbase1 : IntegrableOn
      (fun t : ℝ => t ^ |ν| * Real.exp (-(x / 2) * t ^ (1 : ℝ))) (Ioi 1) :=
    hbase.mono_set (by intro t ht; change 1 < t at ht; exact lt_trans zero_lt_one ht)
  have hg : IntegrableOn g (Ioi 1) := by
    apply Integrable.mono' hbase1
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 1 < t at ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      have htlog : 0 < Real.log t := Real.log_pos ht
      have hcosh : t / 2 ≤ Real.cosh (Real.log t) := by
        rw [Real.cosh_eq, Real.exp_log ht0]
        have he := Real.exp_pos (-Real.log t)
        nlinarith
      have hexp : -x * Real.cosh (Real.log t) + ν * Real.log t ≤
          -(x / 2) * t + |ν| * Real.log t := by
        nlinarith [mul_le_mul_of_nonpos_left hcosh (neg_nonpos.mpr hx.le),
          mul_le_mul_of_nonneg_right (le_abs_self ν) htlog.le]
      have h_exp_le :
          Real.exp (-x * Real.cosh (Real.log t) + ν * Real.log t) ≤
            Real.exp (-(x / 2) * t + |ν| * Real.log t) :=
        Real.exp_le_exp.mpr hexp
      have h_inv : t⁻¹ ≤ 1 := by
        rw [inv_le_one₀ ht0]
        exact le_of_lt ht
      have hpow : Real.exp (|ν| * Real.log t) = t ^ |ν| := by
        rw [Real.rpow_def_of_pos ht0]
        congr 1
        ring
      have hnonneg : 0 ≤ Real.exp (-x * Real.cosh (Real.log t) + ν * Real.log t) :=
        (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ht0.le) hnonneg)]
      calc
        t⁻¹ * Real.exp (-x * Real.cosh (Real.log t) + ν * Real.log t) ≤
            1 * Real.exp (-(x / 2) * t + |ν| * Real.log t) :=
          (mul_le_mul_of_nonneg_right h_inv hnonneg).trans
            (mul_le_mul_of_nonneg_left h_exp_le (by norm_num))
        _ = t ^ |ν| * Real.exp (-(x / 2) * t ^ (1 : ℝ)) := by
          rw [one_mul, Real.exp_add, hpow, Real.rpow_one]
          ring
  have hfun : (fun u => Real.exp u * g (Real.exp u)) =
      (fun u => Real.exp u • g (Real.exp u)) := by
    funext u
    simp
  rw [hfun]
  have hg' : IntegrableOn g (Ioi (Real.exp 0)) := by simpa using hg
  exact (integrableOn_comp_exp_Ioi g 0).mpr hg'

private theorem integrable_besselExpKernel (ν x : ℝ) (hx : 0 < x) :
    Integrable (fun u => besselExpKernel ν x u) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici ℝ _ (0 : ℝ), integrableOn_union]
  constructor
  · rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [Function.comp_def, neg_preimage, neg_Iio, neg_zero]
    have hpos := integrableOn_besselExpKernel_pos (-ν) x hx
    convert hpos using 1
    funext u
    simp [besselExpKernel, Real.cosh_neg]
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_besselExpKernel_pos ν x hx

private theorem integral_besselExpKernel_eq_two_besselK (ν x : ℝ) (hx : 0 < x) :
    (∫ u, besselExpKernel ν x u) = 2 * besselK ν x := by
  have hfull := integrable_besselExpKernel ν x hx
  rw [← integral_add_compl measurableSet_Ioi hfull]
  rw [compl_Ioi]
  rw [← integral_comp_neg_Ioi 0 (fun u => besselExpKernel ν x u)]
  simp only [neg_zero]
  have hnegEq : (fun u => besselExpKernel ν x (-u)) =
      (fun u => besselExpKernel (-ν) x u) := by
    funext u
    simp [besselExpKernel, Real.cosh_neg]
  rw [hnegEq]
  have hpoint' : ∀ u ∈ Ioi (0 : ℝ),
      besselExpKernel ν x u + besselExpKernel (-ν) x u =
        2 * (Real.exp (-x * Real.cosh u) * Real.cosh (ν * u)) := by
    intro u hu
    simp_rw [besselExpKernel, Real.cosh_eq, Real.exp_add]
    ring
  calc
    (∫ u in Ioi (0 : ℝ), besselExpKernel ν x u) +
        ∫ u in Ioi (0 : ℝ), besselExpKernel (-ν) x u =
      ∫ u in Ioi (0 : ℝ),
        (besselExpKernel ν x u + besselExpKernel (-ν) x u) := by
          exact (integral_add (integrableOn_besselExpKernel_pos ν x hx)
            (integrableOn_besselExpKernel_pos (-ν) x hx)).symm
    _ = ∫ u in Ioi (0 : ℝ),
        2 * (Real.exp (-x * Real.cosh u) * Real.cosh (ν * u)) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact hpoint' u hu
    _ = 2 * ∫ u in Ioi (0 : ℝ),
        Real.exp (-x * Real.cosh u) * Real.cosh (ν * u) := by
          rw [integral_const_mul]
    _ = 2 * besselK ν x := rfl

private theorem integral_schlafliKernel_eq (ν x : ℝ) (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), schlafliKernel ν x t) =
      (x / 2) ^ ν * ∫ u, besselExpKernel ν x u := by
  let c := x / 2
  have hc : 0 < c := by dsimp [c]; linarith
  calc
    (∫ t in Ioi (0 : ℝ), schlafliKernel ν x t) =
        c * ∫ s in Ioi (0 : ℝ), schlafliKernel ν x (c * s) := by
          symm
          simpa [c] using (integral_comp_mul_left_Ioi' (fun t => schlafliKernel ν x t)
            0 hc)
    _ = ∫ u, (Real.exp u * (c * schlafliKernel ν x (c * Real.exp u))) := by
          rw [← integral_const_mul]
          exact (integral_comp_exp (fun s => c * schlafliKernel ν x (c * s))).symm
    _ = _ := by
          have hEq : ∀ u : ℝ,
              Real.exp u * (c * schlafliKernel ν x (c * Real.exp u)) =
                c ^ ν * besselExpKernel ν x u := by
            intro u
            have hcpos : 0 < c := hc
            have hepos : 0 < Real.exp u := Real.exp_pos u
            have hcosh : c * Real.exp u + x ^ 2 / (4 * (c * Real.exp u)) =
                x * Real.cosh u := by
              dsimp [c]
              rw [Real.cosh_eq]
              rw [Real.exp_neg]
              field_simp
              ring
            rw [schlafliKernel, besselExpKernel]
            have hneg : -(c * Real.exp u) - x ^ 2 / (4 * (c * Real.exp u)) =
                -x * Real.cosh u := by linarith [hcosh]
            rw [hneg]
            have hpower : Real.exp u * (c * (c * Real.exp u) ^ (ν - 1)) =
                c ^ ν * Real.exp (ν * u) := by
              have hstep : (c * Real.exp u) ^ ν =
                  (c * Real.exp u) ^ (ν - 1) * (c * Real.exp u) := by
                simpa [sub_add_cancel] using
                  (Real.rpow_add_one (mul_ne_zero hcpos.ne' hepos.ne') (ν - 1))
              calc
                Real.exp u * (c * (c * Real.exp u) ^ (ν - 1)) =
                    (c * Real.exp u) ^ (ν - 1) * (c * Real.exp u) := by ring
                _ = (c * Real.exp u) ^ ν := hstep.symm
                _ = c ^ ν * (Real.exp u) ^ ν := Real.mul_rpow hcpos.le hepos.le
                _ = c ^ ν * Real.exp (ν * u) := by
                  rw [Real.rpow_def_of_pos hepos, Real.log_exp]
                  congr 1
                  ring
            calc
              Real.exp u * (c * ((c * Real.exp u) ^ (ν - 1) *
                  Real.exp (-x * Real.cosh u))) =
                  (Real.exp u * (c * (c * Real.exp u) ^ (ν - 1))) *
                    Real.exp (-x * Real.cosh u) := by ring
              _ = (c ^ ν * Real.exp (ν * u)) * Real.exp (-x * Real.cosh u) :=
                    congrArg (fun z => z * Real.exp (-x * Real.cosh u)) hpower
              _ = c ^ ν * Real.exp (-x * Real.cosh u + ν * u) := by
                    rw [Real.exp_add]
                    ring
          calc
            (∫ u, Real.exp u * (c * schlafliKernel ν x (c * Real.exp u))) =
                ∫ u, c ^ ν * besselExpKernel ν x u := by
                  apply integral_congr_ae
                  filter_upwards [] with u
                  exact hEq u
            _ = c ^ ν * ∫ u, besselExpKernel ν x u := by rw [integral_const_mul]

private theorem besselK_eq_schlafli_proof (ν x : ℝ) (hx : 0 < x) :
    besselK ν x = 1 / 2 * (x / 2) ^ (-ν) *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t)) := by
  have hSch := integral_schlafliKernel_eq ν x hx
  have hfull := integral_besselExpKernel_eq_two_besselK ν x hx
  have hc : 0 < x / 2 := by linarith
  have hI :
      (∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t))) =
        (x / 2) ^ ν * (2 * besselK ν x) := by
    dsimp [schlafliKernel] at hSch
    exact hSch.trans (congrArg (fun z : ℝ => (x / 2) ^ ν * z) hfull)
  calc
    besselK ν x = (1 / 2 : ℝ) * (x / 2) ^ (-ν) *
        ((x / 2) ^ ν * (2 * besselK ν x)) := by
          rw [Real.rpow_neg hc.le]
          field_simp
    _ = (1 / 2 : ℝ) * (x / 2) ^ (-ν) *
        ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t)) := by
          rw [← hI]

/-- **jq:bessel-bridge**: the frozen `besselK` (cosh form) equals Schläfli's form. -/
theorem besselK_eq_schlafli (ν x : ℝ) (hx : 0 < x) :
    besselK ν x = 1 / 2 * (x / 2) ^ (-ν) *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t)) := by
  exact besselK_eq_schlafli_proof ν x hx

end SharedJacquet

end ArtinPrimitiveRoots.A1.Theta
