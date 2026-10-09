import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.LocalSubstitution

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain MeasureTheory Function
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.e_c
open ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)











include R

def primeLocalSummand (v : ExteriorPrime S) (k t J : ℕ) (d x : S.R) : ℂ :=
  if primeR R v ^ J - primeR R v ^ t * d ∈ Ideal.span {primeR R v ^ k} then
    chiPow D v.1 (d : F) 1 ^ k * chiPow D v.1 (x : F) 1 ^ t *
      A.ψ v.1 (algebraMap F (v.1.adicCompletion F)
        (-(((primeR R v ^ J - primeR R v ^ t * d) * x : S.R) : F) /
          (primeGen R v.1 : F) ^ (k + t)))
  else 0

theorem prime_divisibility_iff (v : ExteriorPrime S) (k : ℕ) (r : S.R) :
    (∃ y : S.R, (r : F) = (primeGen R v.1 : F) ^ k * (y : F)) ↔
      r ∈ Ideal.span {primeR R v ^ k} := by
  constructor
  · rintro ⟨y, hy⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨y, ?_⟩
    apply Subtype.ext
    simpa [primeR_val] using hy
  · intro hm
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hm
    refine ⟨y, ?_⟩
    simpa [primeR_val] using congrArg (fun t : S.R => (t : F)) hy

theorem unit_mul_mem_iff (v : ExteriorPrime S) (k : ℕ) (hp r : S.R)
    (hhp : v.1.valuation F (hp : F) = 1) :
    hp * r ∈ Ideal.span {primeR R v ^ k} ↔ r ∈ Ideal.span {primeR R v ^ k} := by
  let K : Ideal S.R := Ideal.span {primeR R v ^ k}
  have hU : IsUnit (Ideal.Quotient.mk K hp) := by
    let e := Ideal.quotEquivOfEq (prime_power_span R v k)
    have hu := (residue_isUnit_of_valuation_one R v k hp hhp).map e.toMonoidHom
    change IsUnit (e (Ideal.Quotient.mk _ hp)) at hu
    dsimp [e] at hu
    exact hu
  constructor
  · intro hmem
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h0 : Ideal.Quotient.mk K hp * Ideal.Quotient.mk K r = 0 := by
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    let u := hU.unit
    have hu : (u : S.R ⧸ K) = Ideal.Quotient.mk K hp := hU.unit_spec
    have h0u : (u : S.R ⧸ K) * Ideal.Quotient.mk K r = 0 := by rw [hu]; exact h0
    have h1 := congrArg (fun z : S.R ⧸ K => ((u⁻¹ : (S.R ⧸ K)ˣ) : S.R ⧸ K) * z) h0u
    have hcancel : ((u⁻¹ : (S.R ⧸ K)ˣ) : S.R ⧸ K) * (u : S.R ⧸ K) = 1 := by
      simpa only [Units.val_mul, Units.val_one] using
        congrArg (fun z : (S.R ⧸ K)ˣ => (z : S.R ⧸ K)) (inv_mul_cancel u)
    rw [← mul_assoc, hcancel, one_mul, mul_zero] at h1
    exact h1
  · intro hm
    exact K.mul_mem_left hp hm

theorem prime_mask_substitution (v : ExteriorPrime S) (k t J : ℕ)
    (ap hp d d' : S.R) (hhp : v.1.valuation F (hp : F) = 1)
    (hd : ap * d - hp * d' ∈ Ideal.span {primeR R v ^ k}) :
    primeR R v ^ J * hp - primeR R v ^ t * ap * d ∈ Ideal.span {primeR R v ^ k} ↔
      primeR R v ^ J - primeR R v ^ t * d' ∈ Ideal.span {primeR R v ^ k} := by
  have hdiff : (primeR R v ^ J * hp - primeR R v ^ t * ap * d) -
      hp * (primeR R v ^ J - primeR R v ^ t * d') ∈ Ideal.span {primeR R v ^ k} := by
    have h := (Ideal.span {primeR R v ^ k}).mul_mem_left (-(primeR R v ^ t)) hd
    convert h using 1 <;> ring
  exact (ideal_mem_iff_of_sub_mem R _ _ _ hdiff).trans (unit_mul_mem_iff R v k hp _ hhp)

theorem localizedSummand_substitution (s I : S.ExtIdeal) (v : ExteriorPrime S)
    (k t J : ℕ) (sp ap hp d d' x x' : S.R)
    (hk : idealExp v.1 s.1 = k) (ht : idealExp v.1 I.1 = t)
    (hS : R.exterior.genR s = primeR R v ^ k * sp)
    (hsp : v.1.valuation F (sp : F) = 1) (hap : v.1.valuation F (ap : F) = 1)
    (hhp : v.1.valuation F (hp : F) = 1)
    (hd : ap * d - hp * d' ∈ Ideal.span {primeR R v ^ k})
    (hx : hp * x - sp * ap * x' ∈ Ideal.span {primeR R v ^ t}) :
    localizedSummand R s I (primeR R v ^ t * ap) (primeR R v ^ J * hp) v d x =
      (chi D v.1 ((hp : F) / (ap : F)) ^ k *
        chi D v.1 (((sp * ap : S.R) : F) / (hp : F)) ^ t) *
          primeLocalSummand R v k t J d' x' := by
  classical
  have hK : coordinateSpan R s v = Ideal.span {primeR R v ^ k} := by
    simp only [coordinateSpan, coordinateIdeal, hk]
    exact prime_power_span R v k
  have hmask := prime_mask_substitution R v k t J ap hp d d' hhp hd
  have hspap : v.1.valuation F ((sp * ap : S.R) : F) = 1 := by
    simpa using congrArg₂ (fun a b => a * b) hsp hap
  have hden : (R.exterior.genR s : F) * ((primeR R v ^ t * ap : S.R) : F) =
      (primeGen R v.1 : F) ^ (k + t) * (sp : F) * (ap : F) := by
    rw [hS]
    push_cast
    rw [primeR_val, pow_add]
    ring
  by_cases hm : primeR R v ^ J - primeR R v ^ t * d' ∈ Ideal.span {primeR R v ^ k}
  · have hmOld := hmask.mpr hm
    simp only [localizedSummand, primeLocalSummand, hK, hk, ht, if_pos hm, if_pos hmOld]
    rw [hden, prime_character_substitution R v k ap hp d d' hap hhp hd,
      prime_character_substitution R v t hp (sp * ap) x x' hhp hspap hx,
      prime_substitution_phase R v k t J sp ap hp d d' x x' hsp hap hd hx hm]
    ring
  · have hmOld := fun H => hm (hmask.mp H)
    simp only [localizedSummand, primeLocalSummand, hK, hk, ht, if_neg hm, if_neg hmOld, mul_zero]

theorem localC_primeLocalSummand (v : ExteriorPrime S) (k t J : ℕ) :
    localC R v.1 v.2 t k J =
      ∑ᶠ d : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) k),
      ∑ᶠ x : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) t),
        primeLocalSummand R v k t J d.out x.out := by
  classical
  letI := R.exterior.residueFinite (R.exterior.pow (R.exterior.prime v.1 v.2) k)
  letI := R.exterior.residueFinite (R.exterior.pow (R.exterior.prime v.1 v.2) t)
  simp only [localC, finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro d hd
  have hm : (∃ y : S.R, (primeGen R v.1 : F) ^ J - (primeGen R v.1 : F) ^ t * (d.out : F) =
      (primeGen R v.1 : F) ^ k * (y : F)) ↔
      primeR R v ^ J - primeR R v ^ t * d.out ∈ Ideal.span {primeR R v ^ k} := by
    simpa [primeR_val] using prime_divisibility_iff R v k (primeR R v ^ J - primeR R v ^ t * d.out)
  rw [hm]
  by_cases hc : primeR R v ^ J - primeR R v ^ t * d.out ∈ Ideal.span {primeR R v ^ k}
  · simp only [if_pos hc, ← chiPow_one_pow R, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [primeLocalSummand, if_pos hc]
    first | rfl | (simp [primeR_val, neg_div, mul_assoc])
  · simp only [if_neg hc, primeLocalSummand, Finset.sum_const_zero]

noncomputable def primeResidueUnit (v : ExteriorPrime S) (k : ℕ) (r : S.R)
    (hr : v.1.valuation F (r : F) = 1) :
    (ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) k))ˣ :=
  (residue_isUnit_of_valuation_one R v k r hr).unit

theorem primeResidueUnit_val (v : ExteriorPrime S) (k : ℕ) (r : S.R)
    (hr : v.1.valuation F (r : F) = 1) :
    (primeResidueUnit R v k r hr : ResidueRing R.exterior
      (R.exterior.pow (R.exterior.prime v.1 v.2) k)) = Ideal.Quotient.mk _ r :=
  (residue_isUnit_of_valuation_one R v k r hr).unit_spec

theorem first_multiplier_congruence (v : ExteriorPrime S) (k : ℕ) (ap hp : S.R)
    (hap : v.1.valuation F (ap : F) = 1) (hhp : v.1.valuation F (hp : F) = 1)
    (d : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) k)) :
    ap * (quotientMulEquiv
      (primeResidueUnit R v k hp hhp * (primeResidueUnit R v k ap hap)⁻¹) d).out - hp * d.out ∈
        Ideal.span {primeR R v ^ k} := by
  rw [← prime_power_span R v k]
  let uA := primeResidueUnit R v k ap hap
  let uH := primeResidueUnit R v k hp hhp
  have hA := primeResidueUnit_val R v k ap hap
  have hH := primeResidueUnit_val R v k hp hhp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simp only [map_sub, map_mul, Ideal.Quotient.mk_out]
  change Ideal.Quotient.mk _ ap *
    (((uH * uA⁻¹ : (ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) k))ˣ) :
      ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) k)) * d) -
    Ideal.Quotient.mk _ hp * d = 0
  rw [← hA, ← hH]
  have heq : uA * (uH * uA⁻¹) = uH := by
    rw [mul_comm uH uA⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hc := congrArg (fun z : (ResidueRing R.exterior
    (R.exterior.pow (R.exterior.prime v.1 v.2) k))ˣ =>
      (z : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) k))) heq
  simp only [Units.val_mul, Units.val_inv_eq_inv_val] at hc
  simp only [Units.val_mul]
  rw [← mul_assoc (uA : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) k))
    ((uH : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) k)) *
      ((uA⁻¹ : _) : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) k))) d,
    hc, sub_self]

theorem second_multiplier_congruence (v : ExteriorPrime S) (t : ℕ) (sp ap hp : S.R)
    (hsp : v.1.valuation F (sp : F) = 1) (hap : v.1.valuation F (ap : F) = 1)
    (hhp : v.1.valuation F (hp : F) = 1)
    (x : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) t)) :
    hp * (quotientMulEquiv (primeResidueUnit R v t sp hsp * primeResidueUnit R v t ap hap *
      (primeResidueUnit R v t hp hhp)⁻¹) x).out - sp * ap * x.out ∈
        Ideal.span {primeR R v ^ t} := by
  rw [← prime_power_span R v t]
  let uS := primeResidueUnit R v t sp hsp
  let uA := primeResidueUnit R v t ap hap
  let uH := primeResidueUnit R v t hp hhp
  have hS := primeResidueUnit_val R v t sp hsp
  have hA := primeResidueUnit_val R v t ap hap
  have hH := primeResidueUnit_val R v t hp hhp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simp only [map_sub, map_mul, Ideal.Quotient.mk_out]
  change Ideal.Quotient.mk _ hp *
    (((uS * uA * uH⁻¹ : (ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) t))ˣ) :
      ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) t)) * x) -
    Ideal.Quotient.mk _ sp * Ideal.Quotient.mk _ ap * x = 0
  rw [← hS, ← hA, ← hH]
  have heq : uH * ((uS * uA) * uH⁻¹) = uS * uA := by
    rw [mul_comm (uS * uA) uH⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hc := congrArg (fun z : (ResidueRing R.exterior
    (R.exterior.pow (R.exterior.prime v.1 v.2) t))ˣ =>
      (z : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) t))) heq
  simp only [Units.val_mul, Units.val_inv_eq_inv_val] at hc
  simp only [Units.val_mul]
  rw [← mul_assoc (uH : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) t))
    ((uS : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) t)) *
      (uA : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) t)) *
      ((uH⁻¹ : _) : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) t))) x,
    hc, sub_self]

theorem localizedSum_eq_localC (s I : S.ExtIdeal) (v : ExteriorPrime S)
    (J : ℕ) (sp ap hp : S.R)
    (hS : R.exterior.genR s = primeR R v ^ idealExp v.1 s.1 * sp)
    (hsp : v.1.valuation F (sp : F) = 1) (hap : v.1.valuation F (ap : F) = 1)
    (hhp : v.1.valuation F (hp : F) = 1) :
    (∑ᶠ d : ResidueRing R.exterior (coordinateIdeal R s v),
      ∑ᶠ x : ResidueRing R.exterior (coordinateIdeal R I v),
        localizedSummand R s I (primeR R v ^ idealExp v.1 I.1 * ap)
          (primeR R v ^ J * hp) v d.out x.out) =
      (chi D v.1 ((hp : F) / (ap : F)) ^ idealExp v.1 s.1 *
        chi D v.1 (((sp * ap : S.R) : F) / (hp : F)) ^ idealExp v.1 I.1) *
          localC R v.1 v.2 (idealExp v.1 I.1) (idealExp v.1 s.1) J := by
  classical
  let k := idealExp v.1 s.1
  let t := idealExp v.1 I.1
  let Qd := ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) k)
  let Qx := ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v.1 v.2) t)
  letI : Fintype Qd := R.exterior.residueFinite _
  letI : Fintype Qx := R.exterior.residueFinite _
  let Ed := quotientMulEquiv (primeResidueUnit R v k hp hhp * (primeResidueUnit R v k ap hap)⁻¹)
  let Ex := quotientMulEquiv (primeResidueUnit R v t sp hsp * primeResidueUnit R v t ap hap *
    (primeResidueUnit R v t hp hhp)⁻¹)
  let P := chi D v.1 ((hp : F) / (ap : F)) ^ k *
    chi D v.1 (((sp * ap : S.R) : F) / (hp : F)) ^ t
  let f (d : Qd) (x : Qx) :=
    localizedSummand R s I (primeR R v ^ t * ap) (primeR R v ^ J * hp) v d.out x.out
  have hpoint (d : Qd) (x : Qx) : f (Ed d) (Ex x) = P * primeLocalSummand R v k t J d.out x.out :=
    localizedSummand_substitution R s I v k t J sp ap hp (Ed d).out d.out (Ex x).out x.out
      rfl rfl hS hsp hap hhp (first_multiplier_congruence R v k ap hp hap hhp d)
      (second_multiplier_congruence R v t sp ap hp hsp hap hhp x)
  have hbody : (∑ᶠ d : Qd, ∑ᶠ x : Qx, f d x) = P * localC R v.1 v.2 t k J := by
    rw [finsum_eq_sum_of_fintype]
    simp only [finsum_eq_sum_of_fintype]
    change (∑ d : Qd, ∑ x : Qx, f d x) = P * localC R v.1 v.2 t k J
    calc
      _ = ∑ d : Qd, ∑ x : Qx, f (Ed d) x := (Ed.sum_comp (fun d => ∑ x : Qx, f d x)).symm
      _ = ∑ d : Qd, ∑ x : Qx, f (Ed d) (Ex x) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact (Ex.sum_comp (fun x => f (Ed d) x)).symm
      _ = ∑ d : Qd, ∑ x : Qx, P * primeLocalSummand R v k t J d.out x.out := by
        apply Finset.sum_congr rfl
        intro d hd
        exact Finset.sum_congr rfl (fun x hx => hpoint d x)
      _ = P * (∑ d : Qd, ∑ x : Qx, primeLocalSummand R v k t J d.out x.out) := by
        simp only [Finset.mul_sum]
      _ = _ := by
        rw [localC_primeLocalSummand R v k t J]
        simp only [finsum_eq_sum_of_fintype]
        rfl
  exact hbody

end ArtinPrimitiveRoots.Proofs.e_c
