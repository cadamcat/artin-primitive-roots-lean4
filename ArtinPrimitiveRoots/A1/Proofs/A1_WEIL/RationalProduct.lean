import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalUnit

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Odd valuation places of a nonzero rational have finite support. -/
private def rationalOddValSupport (a : ℚˣ) : Set Nat.Primes :=
  {p | ¬ Even (padicValRat p.1 (a : ℚ))}

private theorem rationalOddValSupport_finite (a : ℚˣ) :
    (rationalOddValSupport a).Finite := by
  classical
  let M : ℕ := 2 + (a : ℚ).num.natAbs + (a : ℚ).den
  have hnumPos : 0 < (a : ℚ).num.natAbs :=
    Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr a.ne_zero)
  have hdenPos : 0 < (a : ℚ).den := Rat.den_pos _
  have hval : Function.Injective (fun p : Nat.Primes => p.1) := Subtype.val_injective
  refine ((Set.finite_Iic M).preimage hval.injOn).subset ?_
  intro p hp
  change p.1 ≤ M
  by_contra hpM
  have hpLarge : M < p.1 := lt_of_not_ge hpM
  have hnum : ¬ p.1 ∣ (a : ℚ).num.natAbs := by
    intro hdiv
    have hpLe : p.1 ≤ (a : ℚ).num.natAbs := Nat.le_of_dvd hnumPos hdiv
    have : p.1 ≤ M := by dsimp [M]; omega
    omega
  have hden : ¬ p.1 ∣ (a : ℚ).den := by
    intro hdiv
    have hpLe : p.1 ≤ (a : ℚ).den := Nat.le_of_dvd hdenPos hdiv
    have : p.1 ≤ M := by dsimp [M]; omega
    omega
  have hnumZ : ¬ (p.1 : ℤ) ∣ (a : ℚ).num := by
    intro hdiv
    exact hnum (Int.natCast_dvd.mp hdiv)
  have hk : padicValRat p.1 (a : ℚ) = 0 := by
    rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnumZ,
      padicValNat.eq_zero_of_not_dvd hden, sub_self]
  exact hp (by simp [rationalOddValSupport, hk])

private theorem rationalPrimeProduct_padicVal (S : Finset Nat.Primes) (p : Nat.Primes) :
    padicValRat p.1 (∏ q ∈ S, (q.1 : ℚ)) = if p ∈ S then 1 else 0 := by
  classical
  let n : ℕ := ∏ q ∈ S, q.1
  have hn : n ≠ 0 := by
    dsimp [n]
    exact Finset.prod_ne_zero_iff.mpr fun q hq => q.2.ne_zero
  have hcast : (∏ q ∈ S, (q.1 : ℚ)) = (n : ℚ) := by
    simp [n]
  have hfac : n.factorization p.1 = if p ∈ S then 1 else 0 := by
    rw [Nat.factorization_prod (S := S) (g := fun q => q.1)
      (fun q hq => q.2.ne_zero)]
    rw [Finsupp.finsetSum_apply]
    change (∑ q ∈ S, q.1.factorization p.1) = _
    calc
      (∑ q ∈ S, q.1.factorization p.1) =
          ∑ q ∈ S, if q = p then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [q.2.factorization]
        simp only [Finsupp.single_apply]
        by_cases hqp : q = p
        · simp [hqp]
        · have hval : q.1 ≠ p.1 := by
            intro he
            exact hqp (Subtype.ext he)
          simp [hval, hqp]
      _ = if p ∈ S then 1 else 0 := by
        by_cases hp : p ∈ S <;> simp [hp]
  rw [hcast, padicValRat.of_nat, ← Nat.factorization_def n p.2]
  exact_mod_cast hfac

private theorem rationalUnitPart_mul (p : Nat.Primes) (a b : ℚˣ) :
    rationalUnitPart p.1 (a * b) =
      rationalUnitPart p.1 a * rationalUnitPart p.1 b := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  have hpq : (p.1 : ℚ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  simp only [rationalUnitPart, Units.val_mul]
  rw [padicValRat.mul a.ne_zero b.ne_zero, zpow_add₀ hpq]
  field_simp

private theorem rationalUnitPart_square (p : Nat.Primes) (a b : ℚˣ) :
    rationalUnitPart p.1 (a * b ^ 2) =
      rationalUnitPart p.1 a * (rationalUnitPart p.1 b) ^ 2 := by
  rw [rationalUnitPart_mul p a (b ^ 2)]
  have hb : rationalUnitPart p.1 (b ^ 2) = (rationalUnitPart p.1 b) ^ 2 := by
    simpa [pow_two] using rationalUnitPart_mul p b b
  rw [hb]

private def rationalJacobiArg (x : ℚ) : ℤ := x.num * (x.den : ℤ)

private def rationalJacobiCancel (u v : ℚ) : ℕ :=
  (u.num * (v ^ 2).num).natAbs.gcd (u.den * (v ^ 2).den)

private theorem rationalJacobiArg_mul_square (u v : ℚ) :
    rationalJacobiArg (u * v ^ 2) * (rationalJacobiCancel u v : ℤ) ^ 2 =
      rationalJacobiArg u * (rationalJacobiArg v) ^ 2 := by
  let w : ℚ := u * v ^ 2
  let c : ℕ := (u.num * (v ^ 2).num).natAbs.gcd (u.den * (v ^ 2).den)
  have hnum : u.num * (v ^ 2).num = w.num * (c : ℤ) := by
    dsimp [w, c]
    exact Rat.num_mul_num_eq_num_mul_gcd u (v ^ 2)
  have hden : u.den * (v ^ 2).den = w.den * c := by
    dsimp [w, c]
    exact Rat.den_mul_den_eq_den_mul_gcd u (v ^ 2)
  have hdenZ : (u.den : ℤ) * ((v ^ 2).den : ℤ) =
      (w.den : ℤ) * (c : ℤ) := by exact_mod_cast hden
  have hvnum : (v ^ 2).num = v.num ^ 2 := by
    simpa [pow_two] using Rat.mul_self_num v
  have hvden : (v ^ 2).den = v.den ^ 2 := by
    simpa [pow_two] using Rat.mul_self_den v
  change rationalJacobiArg w * (c : ℤ) ^ 2 =
    rationalJacobiArg u * (rationalJacobiArg v) ^ 2
  calc
    rationalJacobiArg w * (c : ℤ) ^ 2 =
        (w.num * (c : ℤ)) * ((w.den : ℤ) * (c : ℤ)) := by
      dsimp [rationalJacobiArg]
      ring
    _ = (u.num * (v ^ 2).num) * ((u.den * (v ^ 2).den : ℕ) : ℤ) := by
      rw [← hnum, ← hdenZ]
      push_cast
      ring
    _ = rationalJacobiArg u * rationalJacobiArg (v ^ 2) := by
      dsimp [rationalJacobiArg]
      push_cast
      ring
    _ = rationalJacobiArg u * (rationalJacobiArg v) ^ 2 := by
      rw [show rationalJacobiArg (v ^ 2) = (rationalJacobiArg v) ^ 2 by
        dsimp [rationalJacobiArg]
        ring]

private theorem jacobiSym_square_one (p : Nat.Primes) (z : ℤ)
    (hz : ¬ (p.1 : ℤ) ∣ z) : jacobiSym (z ^ 2) p.1 = 1 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym p.1 (z ^ 2)]
  apply legendreSym.sq_one'
  intro hz0
  exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z p.1).mp hz0)

private theorem rationalJacobiArg_mul_square_jacobi (p : Nat.Primes) (u v : ℚ)
    (huDen : ¬ p.1 ∣ u.den)
    (hvNum : ¬ p.1 ∣ v.num.natAbs) (hvDen : ¬ p.1 ∣ v.den) :
    jacobiSym (rationalJacobiArg (u * v ^ 2)) p.1 =
      jacobiSym (rationalJacobiArg u) p.1 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let c : ℕ := (u.num * (v ^ 2).num).natAbs.gcd (u.den * (v ^ 2).den)
  have hv2Den : ¬ p.1 ∣ (v ^ 2).den := by
    have hvden : (v ^ 2).den = v.den ^ 2 := by
      simpa [pow_two] using Rat.mul_self_den v
    rw [hvden]
    intro h
    exact hvDen (p.2.dvd_of_dvd_pow h)
  have hc : ¬ p.1 ∣ c := by
    intro h
    have hden : p.1 ∣ u.den * (v ^ 2).den :=
      h.trans (Nat.gcd_dvd_right _ _)
    rcases p.2.dvd_mul.mp hden with h | h
    · exact huDen h
    · exact hv2Den h
  have hcInt : ¬ (p.1 : ℤ) ∣ (c : ℤ) := by
    intro h
    exact hc (Int.natCast_dvd_natCast.mp h)
  have hvArg : ¬ (p.1 : ℤ) ∣ rationalJacobiArg v := by
    intro h
    have hnat : p.1 ∣ (rationalJacobiArg v).natAbs := Int.natCast_dvd.mp h
    simp [rationalJacobiArg, Int.natAbs_mul, Int.natAbs_natCast] at hnat
    rcases p.2.dvd_mul.mp hnat with hnum | hden
    · exact hvNum hnum
    · exact hvDen hden
  have hmul := congrArg (fun z : ℤ => jacobiSym z p.1)
    (rationalJacobiArg_mul_square u v)
  simp only [jacobiSym.mul_left, rationalJacobiCancel] at hmul
  rw [jacobiSym_square_one p (c : ℤ) hcInt,
    jacobiSym_square_one p (rationalJacobiArg v) hvArg] at hmul
  simpa using hmul

private theorem zmod8_unit_square {x : ZMod 8} (hx : IsUnit x) : x ^ 2 = 1 := by
  letI : Fact (1 < 8) := ⟨by norm_num⟩
  have hxcast : (x.val : ZMod 8) = x := by simpa using ZMod.natCast_val x
  have hxval : IsUnit (x.val : ZMod 8) := by
    rw [hxcast]
    exact hx
  have hcop : Nat.Coprime x.val 8 := (ZMod.isUnit_iff_coprime x.val 8).mp hxval
  have hnot : ¬2 ∣ x.val := by
    intro hd
    have h2eight : 2 ∣ 8 := by norm_num
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2) hd h2eight) hcop
  have hlt : x.val < 8 := ZMod.val_lt x
  apply (ZMod.val_injective 8)
  rw [pow_two, ZMod.val_mul, ZMod.val_one]
  interval_cases hval : x.val <;> omega

private theorem zmod8_nat_square_of_not_dvd_two (n : ℕ) (hn : ¬2 ∣ n) :
    (n : ZMod 8) ^ 2 = 1 := by
  have hcop' : Nat.Coprime n (2 ^ 3) :=
    Nat.prime_two.coprime_pow_of_not_dvd (m := 3) hn
  have hcop : Nat.Coprime n 8 := by
    rw [show 8 = 2 ^ 3 by norm_num]
    exact hcop'
  exact zmod8_unit_square ((ZMod.isUnit_iff_coprime n 8).2 hcop)

private theorem zmod8_int_square_of_not_dvd_two (z : ℤ) (hz : ¬(2 : ℤ) ∣ z) :
    (z : ZMod 8) ^ 2 = 1 := by
  have hn : ¬2 ∣ z.natAbs := by
    intro h
    exact hz (Int.natCast_dvd.mpr h)
  have hsq := zmod8_nat_square_of_not_dvd_two z.natAbs hn
  rcases Int.natAbs_eq z with hz₁ | hz₁
  · rw [hz₁]
    exact hsq
  · rw [hz₁, Int.cast_neg, neg_sq]
    exact hsq

private theorem rationalDyadicResidue_eq_arg (a : ℚˣ)
    (hden : ¬2 ∣ (rationalUnitPart 2 a).den) :
    rationalDyadicResidue a =
      (rationalJacobiArg (rationalUnitPart 2 a) : ZMod 8).val := by
  let u := rationalUnitPart 2 a
  have hsq : (u.den : ZMod 8) ^ 2 = 1 :=
    zmod8_nat_square_of_not_dvd_two u.den hden
  have hcop2 : Nat.Coprime 2 u.den := Nat.prime_two.coprime_iff_not_dvd.mpr hden
  have hcop' : Nat.Coprime (2 ^ 3) u.den := hcop2.pow_left 3
  have hcop : Nat.Coprime u.den 8 := by
    convert hcop'.symm using 1 <;> norm_num
  have hunit : IsUnit (u.den : ZMod 8) := (ZMod.isUnit_iff_coprime u.den 8).2 hcop
  have hmul : (u.den : ZMod 8) * (u.den : ZMod 8) = 1 := by
    simpa [pow_two] using hsq
  have hinv : (u.den : ZMod 8)⁻¹ = (u.den : ZMod 8) := by
    have hcopMod : Nat.Coprime (u.den % 8) 8 :=
      (ZMod.coprime_mod_iff_coprime u.den 8).2 hcop
    have hmulInv : (u.den : ZMod 8) * (u.den : ZMod 8)⁻¹ = 1 := by
      rw [ZMod.mul_inv_eq_gcd]
      simp [ZMod.val_natCast, Nat.coprime_iff_gcd_eq_one.mp hcopMod]
    exact hunit.mul_left_cancel (hmulInv.trans hmul.symm)
  change ((u.num : ZMod 8) * (u.den : ZMod 8)⁻¹).val =
    (rationalJacobiArg u : ZMod 8).val
  rw [hinv]
  simp [rationalJacobiArg, Int.cast_mul]

private theorem rationalUnitPart_val_zero (p : Nat.Primes) (a : ℚˣ) :
    padicValRat p.1 (rationalUnitPart p.1 a) = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  have hpq : (p.1 : ℚ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hpow : (p.1 : ℚ) ^ padicValRat p.1 (a : ℚ) ≠ 0 :=
    zpow_ne_zero _ hpq
  rw [rationalUnitPart, padicValRat.div a.ne_zero hpow,
    padicValRat.zpow, padicValRat.self p.2.one_lt]
  ring

private theorem rationalUnitPart_ne_zero (p : Nat.Primes) (a : ℚˣ) :
    rationalUnitPart p.1 a ≠ 0 := by
  unfold rationalUnitPart
  exact div_ne_zero a.ne_zero (zpow_ne_zero _ (by exact_mod_cast p.2.ne_zero))

private theorem rationalUnitPart_num_den_not_dvd (p : Nat.Primes) (a : ℚˣ) :
    ¬ p.1 ∣ (rationalUnitPart p.1 a).num.natAbs ∧
      ¬ p.1 ∣ (rationalUnitPart p.1 a).den := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let u := rationalUnitPart p.1 a
  have hu0 : padicValRat p.1 u = 0 := by
    simpa [u] using rationalUnitPart_val_zero p a
  have hnumden := Rat.num_or_den_zero_padicVal u p.2
  have hnum0 : padicValInt p.1 u.num = 0 := by
    rcases hnumden with hn | hd
    · exact hn
    · rw [padicValRat_def] at hu0
      omega
  have hden0 : padicValNat p.1 u.den = 0 := by
    rcases hnumden with hn | hd
    · rw [padicValRat_def] at hu0
      omega
    · exact hd
  have hnumN : padicValNat p.1 u.num.natAbs = 0 := by
    simpa [padicValInt] using hnum0
  constructor
  · intro hdiv
    have hle : 1 ≤ padicValNat p.1 u.num.natAbs :=
      one_le_padicValNat_of_dvd
        (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (rationalUnitPart_ne_zero p a))).ne' hdiv
    omega
  · intro hdiv
    have hle : 1 ≤ padicValNat p.1 u.den :=
      one_le_padicValNat_of_dvd (Rat.den_pos u).ne' hdiv
    omega

private theorem rationalDyadicResidue_mul_square (a b : ℚˣ) :
    rationalDyadicResidue (a * b ^ 2) = rationalDyadicResidue a := by
  classical
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  let u : ℚ := rationalUnitPart 2 a
  let v : ℚ := rationalUnitPart 2 b
  let w : ℚ := rationalUnitPart 2 (a * b ^ 2)
  have hw : w = u * v ^ 2 := by
    simpa [u, v, w] using rationalUnitPart_square p2 a b
  have hu := rationalUnitPart_num_den_not_dvd p2 a
  have hv := rationalUnitPart_num_den_not_dvd p2 b
  have hw' := rationalUnitPart_num_den_not_dvd p2 (a * b ^ 2)
  have hv2 : rationalUnitPart 2 (b ^ 2) = v ^ 2 := by
    simpa [v, pow_two] using rationalUnitPart_mul p2 b b
  have hv2Den : ¬2 ∣ (v ^ 2).den := by
    rw [← hv2]
    exact (rationalUnitPart_num_den_not_dvd p2 (b ^ 2)).2
  have hc : ¬2 ∣ rationalJacobiCancel u v := by
    intro h
    have hden : 2 ∣ u.den * (v ^ 2).den := h.trans (Nat.gcd_dvd_right _ _)
    rcases Nat.prime_two.dvd_mul.mp hden with h | h
    · exact hu.2 h
    · exact hv2Den h
  have hvArg : ¬(2 : ℤ) ∣ rationalJacobiArg v := by
    intro h
    have hnat : 2 ∣ (rationalJacobiArg v).natAbs := Int.natCast_dvd.mp h
    simp [rationalJacobiArg, Int.natAbs_mul, Int.natAbs_natCast] at hnat
    rcases Nat.prime_two.dvd_mul.mp hnat with hnum | hden
    · exact hv.1 hnum
    · exact hv.2 hden
  have hraw : (rationalJacobiArg w : ZMod 8) =
      (rationalJacobiArg u : ZMod 8) := by
    rw [hw]
    have hArg := rationalJacobiArg_mul_square u v
    have harg : (rationalJacobiArg (u * v ^ 2) : ZMod 8) *
        (rationalJacobiCancel u v : ZMod 8) ^ 2 =
        (rationalJacobiArg u : ZMod 8) * (rationalJacobiArg v : ZMod 8) ^ 2 := by
      simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ZMod 8)) hArg
    have hcSq : (rationalJacobiCancel u v : ZMod 8) ^ 2 = 1 :=
      zmod8_nat_square_of_not_dvd_two _ hc
    rw [hcSq, zmod8_int_square_of_not_dvd_two (rationalJacobiArg v) hvArg] at harg
    simpa using harg
  rw [rationalDyadicResidue_eq_arg (a * b ^ 2) hw'.2,
    rationalDyadicResidue_eq_arg a hu.2]
  exact congrArg ZMod.val hraw

private theorem rationalPrimePhase_mul_square (p : Nat.Primes) (a b : ℚˣ) :
    rationalPrimePhase p (a * b ^ 2) = rationalPrimePhase p a := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  have hval : padicValRat p.1 ((a * b ^ 2 : ℚˣ) : ℚ) =
    padicValRat p.1 (a : ℚ) + 2 * padicValRat p.1 (b : ℚ) := by
    have hco : ((a * b ^ 2 : ℚˣ) : ℚ) = (a : ℚ) * (b : ℚ) ^ 2 := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val b 2]
    rw [hco]
    calc
      padicValRat p.1 ((a : ℚ) * (b : ℚ) ^ 2) =
          padicValRat p.1 (a : ℚ) + padicValRat p.1 ((b : ℚ) ^ 2) :=
        padicValRat.mul a.ne_zero (pow_ne_zero 2 b.ne_zero)
      _ = padicValRat p.1 (a : ℚ) + 2 * padicValRat p.1 (b : ℚ) := by
        rw [padicValRat.pow]
        ring
  have hparity :
      Even (padicValRat p.1 ((a * b ^ 2 : ℚˣ) : ℚ)) ↔
        Even (padicValRat p.1 (a : ℚ)) := by
    rw [hval, Int.even_add]
    simp [Int.even_mul]
  have hparity' : Even (padicValRat p.1 ((a : ℚ) * (b : ℚ) ^ 2)) ↔
      Even (padicValRat p.1 (a : ℚ)) := by
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using hparity
  by_cases hp2 : p.1 = 2
  · have hres := rationalDyadicResidue_mul_square a b
    have hparity2 : Even (padicValRat 2 ((a : ℚ) * (b : ℚ) ^ 2)) ↔
        Even (padicValRat 2 (a : ℚ)) := by simpa [hp2] using hparity'
    simp [rationalPrimePhase, hp2, hparity2, hres]
  · let u : ℚ := rationalUnitPart p.1 a
    let v : ℚ := rationalUnitPart p.1 b
    have hu : rationalUnitPart p.1 (a * b ^ 2) = u * v ^ 2 := by
      simpa [u, v] using rationalUnitPart_square p a b
    have hJ :
        jacobiSym (rationalJacobiArg (rationalUnitPart p.1 (a * b ^ 2))) p.1 =
          jacobiSym (rationalJacobiArg (rationalUnitPart p.1 a)) p.1 := by
      rw [hu]
      exact rationalJacobiArg_mul_square_jacobi p u v
        (rationalUnitPart_num_den_not_dvd p a).2
        (rationalUnitPart_num_den_not_dvd p b).1
        (rationalUnitPart_num_den_not_dvd p b).2
    have hJ' :
        jacobiSym ((rationalUnitPart p.1 (a * b ^ 2)).num *
          (rationalUnitPart p.1 (a * b ^ 2)).den) p.1 =
        jacobiSym ((rationalUnitPart p.1 a).num *
          (rationalUnitPart p.1 a).den) p.1 := by
      simpa [rationalJacobiArg] using hJ
    by_cases he : Even (padicValRat p.1 (a : ℚ))
    · have he' : Even (padicValRat p.1 ((a : ℚ) * (b : ℚ) ^ 2)) := hparity'.mpr he
      simp [rationalPrimePhase, hp2, he, he']
    · have he' : ¬Even (padicValRat p.1 ((a : ℚ) * (b : ℚ) ^ 2)) := by
        intro h
        exact he (hparity'.mp h)
      simp [rationalPrimePhase, hp2, he, he', hJ']

private theorem rationalArchPhase_mul_square (a b : ℚˣ) :
    rationalArchPhase (a * b ^ 2) = rationalArchPhase a := by
  have hb : 0 < (b : ℚ) ^ 2 := sq_pos_of_ne_zero b.ne_zero
  have hsign : 0 < (a : ℚ) * (b : ℚ) ^ 2 ↔ 0 < (a : ℚ) :=
    (mul_pos_iff_of_pos_right hb)
  simp [rationalArchPhase, hsign]

private def rationalOddEpsilon (p : Nat.Primes) : ℂ :=
  if p.1 % 4 = 1 then 1 else Complex.I

private def rationalOddJacobiFactor (T : Finset Nat.Primes) (p : Nat.Primes) : ℂ :=
  rationalOddEpsilon p *
    (jacobiSym ((∏ q ∈ T.erase p, q.1 : ℕ) : ℤ) p.1 : ℂ)

private def rationalOddJacobiProduct (T : Finset Nat.Primes) : ℂ :=
  ∏ p ∈ T, rationalOddJacobiFactor T p

private theorem jacobiSym_finset_product (z : ℤ) (T : Finset Nat.Primes) :
    jacobiSym z (∏ q ∈ T, q.1) =
      ∏ q ∈ T, jacobiSym z q.1 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert q T hqnot ih =>
      have hT0 : (∏ r ∈ T, r.1) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun r hr => r.2.ne_zero
      rw [Finset.prod_insert hqnot]
      rw [jacobiSym.mul_right' z q.2.ne_zero hT0]
      rw [Finset.prod_insert hqnot, ih]

private theorem rationalOddJacobiFactor_insert_self (p : Nat.Primes)
    (T : Finset Nat.Primes) (hpnot : p ∉ T) :
    rationalOddJacobiFactor (insert p T) p =
      rationalOddEpsilon p *
        (jacobiSym ((∏ q ∈ T, q.1 : ℕ) : ℤ) p.1 : ℂ) := by
  simp [rationalOddJacobiFactor, rationalOddEpsilon, Finset.erase_insert hpnot]

private theorem rationalOddJacobiFactor_insert_of_mem (p : Nat.Primes)
    (T : Finset Nat.Primes) (hpnot : p ∉ T) {q : Nat.Primes} (hq : q ∈ T) :
    rationalOddJacobiFactor (insert p T) q =
      rationalOddJacobiFactor T q * (jacobiSym (p.1 : ℤ) q.1 : ℂ) := by
  have hpq : p ≠ q := by
    intro heq
    subst q
    exact hpnot hq
  have herase : (insert p T).erase q = insert p (T.erase q) :=
    Finset.erase_insert_of_ne hpq
  have hpnotErase : p ∉ T.erase q := by
    intro h
    exact hpnot (Finset.mem_of_mem_erase h)
  dsimp [rationalOddJacobiFactor]
  rw [herase, Finset.prod_insert hpnotErase, Nat.cast_mul, jacobiSym.mul_left]
  push_cast
  ac_rfl

private theorem rationalOddProduct_isOdd :
    ∀ T : Finset Nat.Primes, (∀ p ∈ T, p.1 ≠ 2) →
      Odd (∏ p ∈ T, p.1) := by
  intro T
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T hpnot ih =>
      intro hodd
      have hT : ∀ q ∈ T, q.1 ≠ 2 := fun q hq =>
        hodd q (Finset.mem_insert_of_mem hq)
      have hpne : p.1 ≠ 2 := hodd p (by simp)
      have hpOdd : Odd p.1 := by
        rcases p.2.eq_two_or_odd' with h | h
        · exact (hpne h).elim
        · exact h
      simpa [Finset.prod_insert hpnot] using hpOdd.mul (ih hT)

private theorem rationalOddJacobiProduct_insert (p : Nat.Primes)
    (T : Finset Nat.Primes) (hpnot : p ∉ T) :
    rationalOddJacobiProduct (insert p T) =
      rationalOddJacobiProduct T *
        (rationalOddEpsilon p *
          ((jacobiSym ((∏ q ∈ T, q.1 : ℕ) : ℤ) p.1 : ℂ) *
            (jacobiSym (p.1 : ℤ) (∏ q ∈ T, q.1) : ℂ))) := by
  classical
  let n : ℕ := ∏ q ∈ T, q.1
  have hnew : rationalOddJacobiFactor (insert p T) p =
      rationalOddEpsilon p * (jacobiSym (n : ℤ) p.1 : ℂ) := by
    simpa [n] using rationalOddJacobiFactor_insert_self p T hpnot
  have hOld : (∏ q ∈ T, rationalOddJacobiFactor (insert p T) q) =
      rationalOddJacobiProduct T *
        (∏ q ∈ T, (jacobiSym (p.1 : ℤ) q.1 : ℂ)) := by
    calc
      (∏ q ∈ T, rationalOddJacobiFactor (insert p T) q) =
          ∏ q ∈ T, rationalOddJacobiFactor T q *
            (jacobiSym (p.1 : ℤ) q.1 : ℂ) := by
        apply Finset.prod_congr rfl
        intro q hq
        exact rationalOddJacobiFactor_insert_of_mem p T hpnot hq
      _ = rationalOddJacobiProduct T *
          (∏ q ∈ T, (jacobiSym (p.1 : ℤ) q.1 : ℂ)) := by
        rw [Finset.prod_mul_distrib]
        rfl
  have hCross : (∏ q ∈ T, (jacobiSym (p.1 : ℤ) q.1 : ℂ)) =
      (jacobiSym (p.1 : ℤ) n : ℂ) := by
    have h := (jacobiSym_finset_product (p.1 : ℤ) T).symm
    exact_mod_cast h
  calc
    rationalOddJacobiProduct (insert p T) =
        rationalOddJacobiFactor (insert p T) p *
          (∏ q ∈ T, rationalOddJacobiFactor (insert p T) q) := by
      unfold rationalOddJacobiProduct
      rw [Finset.prod_insert hpnot]
    _ = (rationalOddEpsilon p * (jacobiSym (n : ℤ) p.1 : ℂ)) *
          (rationalOddJacobiProduct T *
            (∏ q ∈ T, (jacobiSym (p.1 : ℤ) q.1 : ℂ))) := by
      rw [hnew, hOld]
    _ = rationalOddJacobiProduct T *
          (rationalOddEpsilon p *
            ((jacobiSym (n : ℤ) p.1 : ℂ) *
              (jacobiSym (p.1 : ℤ) n : ℂ))) := by
      rw [hCross]
      ring

private theorem even_div_two_of_mod_four_eq_one {n : ℕ} (h : n % 4 = 1) :
    Even (n / 2) := by
  refine ⟨n / 4, ?_⟩
  have hn := Nat.mod_add_div n 4
  omega

private theorem odd_div_two_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) :
    Odd (n / 2) := by
  refine ⟨n / 4, ?_⟩
  have hn := Nat.mod_add_div n 4
  omega

private theorem rationalOddJacobiProduct_mod_four :
    ∀ T : Finset Nat.Primes, (∀ p ∈ T, p.1 ≠ 2) →
      rationalOddJacobiProduct T =
        if (∏ p ∈ T, p.1) % 4 = 1 then 1 else Complex.I := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro hodd; simp [rationalOddJacobiProduct, rationalOddJacobiFactor]
  | @insert p T hpnot ih =>
      intro hodd
      have hT : ∀ q ∈ T, q.1 ≠ 2 := fun q hq =>
        hodd q (Finset.mem_insert_of_mem hq)
      have hpne : p.1 ≠ 2 := hodd p (by simp)
      have hpOdd : Odd p.1 := by
        rcases p.2.eq_two_or_odd' with heq | ho
        · exact (hpne heq).elim
        · exact ho
      let n : ℕ := ∏ q ∈ T, q.1
      let e : ℕ := n / 2 * (p.1 / 2)
      have hnOdd : Odd n := rationalOddProduct_isOdd T hT
      have hpMod : p.1 % 4 = 1 ∨ p.1 % 4 = 3 :=
        Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpOdd)
      have hnMod : n % 4 = 1 ∨ n % 4 = 3 :=
        Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hnOdd)
      have hcop : Nat.Coprime p.1 n := by
        dsimp [n]
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        apply (p.2.coprime_iff_not_dvd).2
        intro hdiv
        have hval : p.1 = q.1 :=
          (Nat.prime_dvd_prime_iff_eq p.2 q.2).mp hdiv
        have hpq : p = q := Subtype.ext hval
        exact hpnot (hpq.symm ▸ hq)
      have hIntGcd : Int.gcd (p.1 : ℤ) (n : ℤ) = 1 := by
        rw [Int.gcd_natCast_natCast]
        exact hcop.gcd_eq_one
      have hJsq : jacobiSym (p.1 : ℤ) n ^ 2 = 1 := jacobiSym.sq_one hIntGcd
      have hpOddN : Odd p.1 := hpOdd
      have hQR := jacobiSym.quadratic_reciprocity hnOdd hpOddN
      have hRelZ : jacobiSym (n : ℤ) p.1 * jacobiSym (p.1 : ℤ) n =
          (-1 : ℤ) ^ e := by
        dsimp [e]
        rw [hQR, mul_assoc, ← pow_two, hJsq, mul_one]
      have hRel :
          (jacobiSym (n : ℤ) p.1 : ℂ) * (jacobiSym (p.1 : ℤ) n : ℂ) =
            (-1 : ℂ) ^ e := by
        exact_mod_cast hRelZ
      have hRec : rationalOddJacobiProduct (insert p T) =
          rationalOddJacobiProduct T *
            (rationalOddEpsilon p * (-1 : ℂ) ^ e) := by
        rw [rationalOddJacobiProduct_insert p T hpnot, hRel]
      rw [hRec, ih hT, Finset.prod_insert hpnot]
      change (if n % 4 = 1 then 1 else Complex.I) *
          (rationalOddEpsilon p * (-1 : ℂ) ^ e) =
        if (p.1 * n) % 4 = 1 then 1 else Complex.I
      rcases hpMod with hp1 | hp3
      · have hpHalfEven : Even (p.1 / 2) := even_div_two_of_mod_four_eq_one hp1
        have heven : Even e := by
          dsimp [e]
          rw [Nat.even_mul]
          exact Or.inr hpHalfEven
        have hpn : (p.1 * n) % 4 = n % 4 := by
          rw [Nat.mul_mod, hp1]
          simp
        rcases hnMod with hn1 | hn3
        · simp [rationalOddEpsilon, hp1, hn1, hpn, heven, neg_one_pow_eq_ite]
        · simp [rationalOddEpsilon, hp1, hn3, hpn, heven, neg_one_pow_eq_ite]
      · have hpHalfOdd : Odd (p.1 / 2) := odd_div_two_of_mod_four_eq_three hp3
        rcases hnMod with hn1 | hn3
        · have hpn3 : (p.1 * n) % 4 = 3 := by
            rw [Nat.mul_mod, hp3, hn1]
          have hnHalfEven : Even (n / 2) := even_div_two_of_mod_four_eq_one hn1
          have heven : Even e := by
            dsimp [e]
            rw [Nat.even_mul]
            exact Or.inl hnHalfEven
          simp [rationalOddEpsilon, hp3, hn1, hpn3, heven, neg_one_pow_eq_ite]
        · have hpn1 : (p.1 * n) % 4 = 1 := by
            rw [Nat.mul_mod, hp3, hn3]
          have hnHalfOdd : Odd (n / 2) := odd_div_two_of_mod_four_eq_three hn3
          have hnotEven : ¬Even e := by
            dsimp [e]
            rw [Nat.even_mul]
            exact not_or.mpr ⟨
              Nat.not_even_iff.mpr (Nat.odd_iff.mp hnHalfOdd),
              Nat.not_even_iff.mpr (Nat.odd_iff.mp hpHalfOdd)⟩
          simp [rationalOddEpsilon, hp3, hn3, hpn1, hnotEven,
            neg_one_pow_eq_ite, Complex.I_sq]

private def rationalOddPrimeSupport (a : ℚˣ) : Set Nat.Primes :=
  {p | p.1 ≠ 2 ∧ ¬ Even (padicValRat p.1 (a : ℚ))}

private theorem rationalOddPrimeSupport_finite (a : ℚˣ) :
    (rationalOddPrimeSupport a).Finite := by
  apply (rationalOddValSupport_finite a).subset
  intro p hp
  exact hp.2

private noncomputable def rationalSquarefreePart (a : ℚˣ) : ℚ :=
  (if (a : ℚ) < 0 then (-1 : ℚ) else 1) *
    (2 : ℚ) ^ (if Even (padicValRat 2 (a : ℚ)) then 0 else 1) *
    ∏ p ∈ (rationalOddPrimeSupport_finite a).toFinset, (p.1 : ℚ)

private theorem rationalTwo_padicVal (p : Nat.Primes) :
    padicValRat p.1 (2 : ℚ) = if p.1 = 2 then 1 else 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  have hcast : padicValRat p.1 (2 : ℚ) = padicValNat p.1 2 := by
    simp [padicValRat, padicValInt]
  by_cases hp2 : p.1 = 2
  · rw [hcast, hp2]
    simpa using (padicValNat.self (p := 2) (by norm_num : 1 < 2))
  · rw [hcast]
    rw [if_neg hp2]
    have hnot : ¬ p.1 ∣ 2 := by
      intro hdiv
      exact hp2 ((Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).mp hdiv)
    exact_mod_cast (padicValNat.eq_zero_of_not_dvd hnot)

private theorem rationalSquarefreePart_padicVal (a : ℚˣ) (p : Nat.Primes) :
    padicValRat p.1 (rationalSquarefreePart a) =
      if p.1 = 2 then
        (if Even (padicValRat 2 (a : ℚ)) then 0 else 1)
      else if Even (padicValRat p.1 (a : ℚ)) then 0 else 1 := by
  classical
  let S := (rationalOddPrimeSupport_finite a).toFinset
  let sgn : ℚ := if (a : ℚ) < 0 then -1 else 1
  let e : ℕ := if Even (padicValRat 2 (a : ℚ)) then 0 else 1
  let t : ℚ := (2 : ℚ) ^ e
  let n : ℚ := ∏ q ∈ S, (q.1 : ℚ)
  have hsgn : sgn ≠ 0 := by
    dsimp [sgn]
    split_ifs <;> norm_num
  have ht : t ≠ 0 := by
    dsimp [t]
    exact pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)
  have hn : n ≠ 0 := by
    dsimp [n]
    exact Finset.prod_ne_zero_iff.mpr fun q hq => by exact_mod_cast q.2.ne_zero
  have hdecomp : rationalSquarefreePart a = sgn * t * n := by
    rfl
  have hval : padicValRat p.1 (rationalSquarefreePart a) =
      padicValRat p.1 sgn + padicValRat p.1 t + padicValRat p.1 n := by
    rw [hdecomp, padicValRat.mul (mul_ne_zero hsgn ht) hn,
      padicValRat.mul hsgn ht]
  have hsgnval : padicValRat p.1 sgn = 0 := by
    dsimp [sgn]
    split_ifs <;> simp
  have hpowval : padicValRat p.1 t =
      (e : ℤ) * (if p.1 = 2 then 1 else 0) := by
    dsimp [t]
    rw [padicValRat.pow (p := p.1), rationalTwo_padicVal]
  have hnval : padicValRat p.1 n = if p ∈ S then 1 else 0 := by
    dsimp [n, S]
    exact rationalPrimeProduct_padicVal _ p
  by_cases hp2 : p.1 = 2
  · have hpnot : p ∉ S := by
      simp [S, rationalOddPrimeSupport, hp2]
    rw [hval, hsgnval, hpowval, hnval]
    simp [e, hp2, hpnot]
  · have hpS : p ∈ S ↔ ¬ Even (padicValRat p.1 (a : ℚ)) := by
      simp [S, rationalOddPrimeSupport, hp2]
    rw [hval, hsgnval, hpowval, hnval]
    by_cases he : Even (padicValRat p.1 (a : ℚ))
    · have hpnot : p ∉ S := by simpa [hpS] using he
      simp [hpnot, hp2, he]
    · have hpS' : p ∈ S := (hpS).2 he
      simp [hpS', hp2, he]

private theorem rationalSquarefreePart_ne_zero (a : ℚˣ) :
    rationalSquarefreePart a ≠ 0 := by
  classical
  unfold rationalSquarefreePart
  apply mul_ne_zero
  · apply mul_ne_zero
    · split_ifs <;> norm_num
    · exact pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)
  · exact Finset.prod_ne_zero_iff.mpr fun p hp => by exact_mod_cast p.2.ne_zero

private theorem rationalSquarefreePart_decomp (a : ℚˣ) :
    ∃ b : ℚˣ, (a : ℚ) = rationalSquarefreePart a * (b : ℚ) ^ 2 := by
  classical
  let q : ℚ := (a : ℚ)
  let d : ℚ := rationalSquarefreePart a
  let r : ℚ := q / d
  let S := (rationalOddPrimeSupport_finite a).toFinset
  let e : ℕ := if Even (padicValRat 2 q) then 0 else 1
  let n : ℚ := ∏ p ∈ S, (p.1 : ℚ)
  let m : ℚ := (2 : ℚ) ^ e * n
  have hnpos : 0 < n := by
    dsimp [n]
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast p.2.pos
  have hmpos : 0 < m := by
    dsimp [m]
    exact mul_pos (by positivity) hnpos
  have hdsign : d = (if q < 0 then (-1 : ℚ) else 1) * m := by
    dsimp [d, m, rationalSquarefreePart, q, e, S, n]
    ring
  have hd : d ≠ 0 := by
    rw [hdsign]
    by_cases hqneg : q < 0 <;> simp [hqneg, hmpos.ne']
  have hq0 : q ≠ 0 := a.ne_zero
  have hrpos : 0 < r := by
    change 0 < q / d
    by_cases hqneg : q < 0
    · have hdneg : d < 0 := by
        rw [hdsign]
        simp [hqneg]
        linarith
      have hfrac : q / d = (-q) / (-d) := by
        field_simp [hd]
      rw [hfrac]
      exact div_pos (neg_pos.mpr hqneg) (neg_pos.mpr hdneg)
    · have hqpos : 0 < q := lt_of_le_of_ne (le_of_not_gt hqneg) (Ne.symm hq0)
      have hdpos : 0 < d := by
        rw [hdsign]
        simp [hqneg]
        exact hmpos
      exact div_pos hqpos hdpos
  have hvalEven : ∀ p : ℕ, p.Prime → Even (padicValRat p r) := by
    intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    have hdiv : padicValRat p r = padicValRat p q - padicValRat p d := by
      dsimp [r, d, q]
      exact padicValRat.div a.ne_zero hd
    rw [hdiv]
    have hbase : padicValRat p d =
        if p = 2 then
          (if Even (padicValRat 2 q) then 0 else 1)
        else if Even (padicValRat p q) then 0 else 1 := by
      simpa [d, q] using rationalSquarefreePart_padicVal a ⟨p, hp⟩
    rw [hbase]
    by_cases hp2 : p = 2
    · subst p
      change Even (padicValRat 2 q -
        (if Even (padicValRat 2 q) then 0 else 1))
      by_cases he : Even (padicValRat 2 q)
      · simpa [he] using he
      · simpa [he] using Int.even_sub_one.mpr he
    · by_cases he : Even (padicValRat p q)
      · simpa [hp2, he] using he
      · simpa [hp2, he] using Int.even_sub_one.mpr he
  have hsquare : IsSquare r := by
    exact (Rat.isSquare_iff_even_factorization).2 ⟨le_of_lt hrpos, hvalEven⟩
  rcases hsquare with ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    intro hxzero
    subst x
    have hr0 : r = 0 := by simpa using hx
    exact (div_ne_zero hq0 hd) hr0
  refine ⟨Units.mk0 x hx0, ?_⟩
  change q = d * x ^ 2
  calc
    q = (q / d) * d := by field_simp [hd]
    _ = x * x * d := by rw [← hx]
    _ = d * x ^ 2 := by ring

private noncomputable def rationalSquarefreePartUnit (a : ℚˣ) : ℚˣ :=
  Units.mk0 (rationalSquarefreePart a) (rationalSquarefreePart_ne_zero a)

private theorem rationalSquarefreePart_odd_finite_product (a : ℚˣ) :
    let S := (rationalOddPrimeSupport_finite a).toFinset
    let n : ℕ := ∏ p ∈ S, p.1
    let e : ℕ := if Even (padicValRat 2 (a : ℚ)) then 0 else 1
    let s : ℤ := if (a : ℚ) < 0 then -1 else 1
    (∏ p ∈ S, rationalPrimePhase p (rationalSquarefreePartUnit a)) =
      rationalOddJacobiProduct S *
        (jacobiSym s n : ℂ) * (jacobiSym (2 : ℤ) n : ℂ) ^ e := by
  classical
  let S := (rationalOddPrimeSupport_finite a).toFinset
  let n : ℕ := ∏ p ∈ S, p.1
  let e : ℕ := if Even (padicValRat 2 (a : ℚ)) then 0 else 1
  let s : ℤ := if (a : ℚ) < 0 then -1 else 1
  let base : ℚˣ := rationalSquarefreePartUnit a
  change (∏ p ∈ S, rationalPrimePhase p base) =
    rationalOddJacobiProduct S * (jacobiSym s n : ℂ) *
      (jacobiSym (2 : ℤ) n : ℂ) ^ e
  have hS (p : Nat.Primes) :
      p ∈ S ↔ p.1 ≠ 2 ∧ ¬ Even (padicValRat p.1 (a : ℚ)) := by
    simp [S, rationalOddPrimeSupport]
  have hbase : (base : ℚ) = (s : ℚ) * (2 : ℚ) ^ e * (n : ℚ) := by
    change ((if (a : ℚ) < 0 then (-1 : ℚ) else 1) *
        (2 : ℚ) ^ (if Even (padicValRat 2 (a : ℚ)) then 0 else 1) *
        ∏ p ∈ (rationalOddPrimeSupport_finite a).toFinset, (p.1 : ℚ)) = _
    dsimp [s, e, n, S]
    push_cast
    ring_nf
  have hlocal (p : Nat.Primes) (hpS : p ∈ S) :
      ∃ r : ℤ,
        rationalPrimePhase p base = rationalOddEpsilon p * (jacobiSym r p.1 : ℂ) ∧
        jacobiSym r p.1 =
          jacobiSym s p.1 * jacobiSym (2 : ℤ) p.1 ^ e *
            jacobiSym ((∏ q ∈ S.erase p, q.1 : ℕ) : ℤ) p.1 := by
    have hpInfo := (hS p).mp hpS
    have hpne2 : p.1 ≠ 2 := hpInfo.1
    have hnotEven : ¬ Even (padicValRat p.1 (a : ℚ)) := hpInfo.2
    let rest : ℕ := ∏ q ∈ S.erase p, q.1
    let r : ℤ := s * (2 : ℤ) ^ e * (rest : ℤ)
    have hpnotErase : p ∉ S.erase p := by simp
    have hsplit : n = p.1 * rest := by
      dsimp [n, rest]
      exact (Finset.mul_prod_erase S (fun q => q.1) hpS).symm
    have hbasep : (base : ℚ) = (p.1 : ℚ) * (r : ℚ) := by
      rw [hbase, hsplit]
      dsimp [r]
      push_cast
      ring_nf
    have hvalp : padicValRat p.1 (base : ℚ) = 1 := by
      change padicValRat p.1 (rationalSquarefreePart a) = 1
      rw [rationalSquarefreePart_padicVal]
      simp [hpne2, hnotEven]
    have hpQ : (p.1 : ℚ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hunit : rationalUnitPart p.1 base = (r : ℚ) := by
      unfold rationalUnitPart
      rw [hvalp, hbasep, zpow_one]
      exact mul_div_cancel_left₀ _ hpQ
    have harg : rationalJacobiArg (rationalUnitPart p.1 base) = r := by
      rw [hunit]
      norm_num [rationalJacobiArg]
    have hsym : jacobiSym r p.1 =
        jacobiSym (s) p.1 * jacobiSym (2 : ℤ) p.1 ^ e *
          jacobiSym ((∏ q ∈ S.erase p, q.1 : ℕ) : ℤ) p.1 := by
      dsimp [r]
      rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.pow_left]
    refine ⟨r, ?_, hsym⟩
    simp [rationalPrimePhase, hpne2, hvalp, hunit, rationalOddEpsilon,
      rationalJacobiArg, Rat.num_intCast, Rat.den_intCast]
  have hterm (p : Nat.Primes) (hpS : p ∈ S) :
      rationalPrimePhase p base =
        rationalOddJacobiFactor S p *
          (jacobiSym s p.1 : ℂ) * (jacobiSym (2 : ℤ) p.1 : ℂ) ^ e := by
    obtain ⟨r, hphase, hsym⟩ := hlocal p hpS
    rw [hphase, hsym]
    simp only [rationalOddJacobiFactor, rationalOddEpsilon]
    push_cast
    ac_rfl
  have hprod : (∏ p ∈ S, rationalPrimePhase p base) =
      rationalOddJacobiProduct S *
        (∏ p ∈ S, (jacobiSym s p.1 : ℂ)) *
        (∏ p ∈ S, (jacobiSym (2 : ℤ) p.1 : ℂ) ^ e) := by
    calc
      (∏ p ∈ S, rationalPrimePhase p base) =
          ∏ p ∈ S, rationalOddJacobiFactor S p *
            (jacobiSym s p.1 : ℂ) * (jacobiSym (2 : ℤ) p.1 : ℂ) ^ e := by
        apply Finset.prod_congr rfl
        intro p hp
        exact hterm p hp
      _ = (∏ p ∈ S, rationalOddJacobiFactor S p) *
            (∏ p ∈ S, (jacobiSym s p.1 : ℂ)) *
            (∏ p ∈ S, (jacobiSym (2 : ℤ) p.1 : ℂ) ^ e) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hsignProd : (∏ p ∈ S, (jacobiSym s p.1 : ℂ)) =
      (jacobiSym s n : ℂ) := by
    exact_mod_cast (jacobiSym_finset_product s S).symm
  have htwoProd : (∏ p ∈ S, (jacobiSym (2 : ℤ) p.1 : ℂ) ^ e) =
      (jacobiSym (2 : ℤ) n : ℂ) ^ e := by
    rw [Finset.prod_pow]
    have hbaseTwo : (∏ p ∈ S, (jacobiSym (2 : ℤ) p.1 : ℂ)) =
        (jacobiSym (2 : ℤ) n : ℂ) := by
      exact_mod_cast (jacobiSym_finset_product (2 : ℤ) S).symm
    rw [hbaseTwo]
  rw [hprod, hsignProd, htwoProd]

private theorem rational_sqrt_two_half_eq_inv :
    Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  field_simp [hsqrtpos.ne']
  nlinarith

private theorem rational_exp_piI_div_four :
    Complex.exp (Real.pi * Complex.I / 4) =
      (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
  rw [show (Real.pi * Complex.I / 4 : ℂ) =
      (Real.pi / 4 : ℝ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hcast : (Real.sqrt 2 : ℂ) / 2 =
      (1 : ℂ) / (Real.sqrt 2 : ℂ) := by
    exact_mod_cast rational_sqrt_two_half_eq_inv
  push_cast
  rw [hcast]
  ring

private theorem rational_exp_neg_piI_div_four :
    Complex.exp (-(Real.pi * Complex.I / 4)) =
      (1 - Complex.I) / (Real.sqrt 2 : ℂ) := by
  rw [show (-(Real.pi * Complex.I / 4) : ℂ) =
      (-Real.pi / 4 : ℝ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I,
    show -Real.pi / 4 = -(Real.pi / 4) by ring, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hcast : (Real.sqrt 2 : ℂ) / 2 =
      (1 : ℂ) / (Real.sqrt 2 : ℂ) := by
    exact_mod_cast rational_sqrt_two_half_eq_inv
  push_cast
  rw [hcast]
  ring

private theorem rationalSquarefreePart_dyadic_unit (a : ℚˣ) :
    let S := (rationalOddPrimeSupport_finite a).toFinset
    let n : ℕ := ∏ p ∈ S, p.1
    let e : ℕ := if Even (padicValRat 2 (a : ℚ)) then 0 else 1
    let s : ℤ := if (a : ℚ) < 0 then -1 else 1
    rationalUnitPart 2 (rationalSquarefreePartUnit a) = (s : ℚ) * (n : ℚ) := by
  classical
  let S := (rationalOddPrimeSupport_finite a).toFinset
  let n : ℕ := ∏ p ∈ S, p.1
  let e : ℕ := if Even (padicValRat 2 (a : ℚ)) then 0 else 1
  let s : ℤ := if (a : ℚ) < 0 then -1 else 1
  let base := rationalSquarefreePartUnit a
  change rationalUnitPart 2 base = (s : ℚ) * (n : ℚ)
  have hbase : (base : ℚ) = (s : ℚ) * (2 : ℚ) ^ e * (n : ℚ) := by
    change ((if (a : ℚ) < 0 then (-1 : ℚ) else 1) *
        (2 : ℚ) ^ (if Even (padicValRat 2 (a : ℚ)) then 0 else 1) *
        ∏ p ∈ (rationalOddPrimeSupport_finite a).toFinset, (p.1 : ℚ)) = _
    dsimp [s, e, n, S]
    push_cast
    ring_nf
  have hval : padicValRat 2 (base : ℚ) = (e : ℤ) := by
    change padicValRat 2 (rationalSquarefreePart a) = (e : ℤ)
    have hv := rationalSquarefreePart_padicVal a ⟨2, Nat.prime_two⟩
    simpa [e] using hv
  unfold rationalUnitPart
  rw [hval, hbase]
  by_cases he : Even (padicValRat 2 (a : ℚ))
  · have heq : e = 0 := by simp [e, he]
    rw [heq]
    simp [zpow_zero]
  · have heq : e = 1 := by simp [e, he]
    rw [heq]
    norm_num [zpow_one]
    field_simp

private theorem rationalSquarefreePart_dyadic_residue (a : ℚˣ) :
    let S := (rationalOddPrimeSupport_finite a).toFinset
    let n : ℕ := ∏ p ∈ S, p.1
    let e : ℕ := if Even (padicValRat 2 (a : ℚ)) then 0 else 1
    let s : ℤ := if (a : ℚ) < 0 then -1 else 1
    rationalDyadicResidue (rationalSquarefreePartUnit a) =
      (((s * (n : ℤ) : ℤ) : ZMod 8).val) := by
  classical
  let S := (rationalOddPrimeSupport_finite a).toFinset
  let n : ℕ := ∏ p ∈ S, p.1
  let e : ℕ := if Even (padicValRat 2 (a : ℚ)) then 0 else 1
  let s : ℤ := if (a : ℚ) < 0 then -1 else 1
  let base := rationalSquarefreePartUnit a
  change rationalDyadicResidue base =
    (((s * (n : ℤ) : ℤ) : ZMod 8).val)
  have hu : rationalUnitPart 2 base =
      ((s * (n : ℤ) : ℤ) : ℚ) := by
    have h := rationalSquarefreePart_dyadic_unit a
    simpa [S, n, e, s] using h
  have hden : ¬2 ∣ (rationalUnitPart 2 base).den := by
    rw [hu]
    change ¬2 ∣ (((s * (n : ℤ) : ℤ) : ℚ).den)
    simp only [Rat.den_intCast]
    norm_num
  have harg : rationalJacobiArg (((s * (n : ℤ) : ℤ) : ℚ)) = s * (n : ℤ) := by
    simp only [rationalJacobiArg]
    rw [Rat.num_intCast, Rat.den_intCast]
    simp
  calc
    rationalDyadicResidue base =
        (rationalJacobiArg (rationalUnitPart 2 base) : ZMod 8).val :=
      rationalDyadicResidue_eq_arg base hden
    _ = (rationalJacobiArg (((s * (n : ℤ) : ℤ) : ℚ)) : ZMod 8).val := by
      rw [hu]
    _ = (((s * (n : ℤ) : ℤ) : ZMod 8).val) :=
      congrArg (fun z : ℤ => (z : ZMod 8).val) harg

private def rationalGaussPlus : ℂ :=
  (1 + Complex.I) / (Real.sqrt 2 : ℂ)

private def rationalGaussMinus : ℂ :=
  (1 - Complex.I) / (Real.sqrt 2 : ℂ)

private theorem rational_exp_three_half_piI :
    Complex.exp (3 * Real.pi / 2 * Complex.I) = -Complex.I := by
  rw [show (3 * Real.pi / 2 * Complex.I : ℂ) =
      (Real.pi / 2 * Complex.I) + Real.pi * Complex.I by ring]
  rw [Complex.exp_add, Complex.exp_pi_div_two_mul_I, Complex.exp_pi_mul_I]
  ring

private theorem rational_exp_three_quarter_piI :
    Complex.exp (Real.pi * Complex.I * 3 / 4) = -rationalGaussMinus := by
  rw [show (Real.pi * Complex.I * 3 / 4 : ℂ) =
      (Real.pi * Complex.I / 4) + (Real.pi / 2 * Complex.I) by ring]
  rw [Complex.exp_add, rational_exp_piI_div_four,
    Complex.exp_pi_div_two_mul_I]
  simp only [rationalGaussMinus]
  have hsqrtNe : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  field_simp [hsqrtNe]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem rational_exp_five_quarter_piI :
    Complex.exp (Real.pi * Complex.I * 5 / 4) = -rationalGaussPlus := by
  rw [show (Real.pi * Complex.I * 5 / 4 : ℂ) =
      (Real.pi * Complex.I / 4) + Real.pi * Complex.I by ring]
  rw [Complex.exp_add_pi_mul_I, rational_exp_piI_div_four]
  simp only [rationalGaussPlus]

private theorem rational_exp_seven_quarter_piI :
    Complex.exp (Real.pi * Complex.I * 7 / 4) = rationalGaussMinus := by
  rw [show (Real.pi * Complex.I * 7 / 4 : ℂ) =
      (Real.pi * Complex.I / 4) + (3 * Real.pi / 2 * Complex.I) by ring]
  rw [Complex.exp_add, rational_exp_piI_div_four,
    rational_exp_three_half_piI]
  simp only [rationalGaussMinus]
  have hsqrtNe : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  field_simp [hsqrtNe]
  ring_nf
  rw [Complex.I_sq]
  ring

@[simp] private theorem rational_exp_norm_one_quarter :
    Complex.exp (Complex.I * Real.pi * (1 / 4 : ℂ)) = rationalGaussPlus := by
  rw [show (Complex.I * Real.pi * (1 / 4 : ℂ) : ℂ) =
    Real.pi * Complex.I / 4 by ring, rational_exp_piI_div_four]
  rfl

@[simp] private theorem rational_exp_norm_neg_quarter :
    Complex.exp (Complex.I * Real.pi * (-1 / 4 : ℂ)) = rationalGaussMinus := by
  rw [show (Complex.I * Real.pi * (-1 / 4 : ℂ) : ℂ) =
    -(Real.pi * Complex.I / 4) by ring, rational_exp_neg_piI_div_four]
  rfl

@[simp] private theorem rational_exp_norm_three_quarters :
    Complex.exp (Complex.I * Real.pi * (3 / 4 : ℂ)) = -rationalGaussMinus := by
  rw [show (Complex.I * Real.pi * (3 / 4 : ℂ) : ℂ) =
    Real.pi * Complex.I * 3 / 4 by ring, rational_exp_three_quarter_piI]

@[simp] private theorem rational_exp_norm_five_quarters :
    Complex.exp (Complex.I * Real.pi * (5 / 4 : ℂ)) = -rationalGaussPlus := by
  rw [show (Complex.I * Real.pi * (5 / 4 : ℂ) : ℂ) =
    Real.pi * Complex.I * 5 / 4 by ring, rational_exp_five_quarter_piI]

@[simp] private theorem rational_exp_norm_seven_quarters :
    Complex.exp (Complex.I * Real.pi * (7 / 4 : ℂ)) = rationalGaussMinus := by
  rw [show (Complex.I * Real.pi * (7 / 4 : ℂ) : ℂ) =
    Real.pi * Complex.I * 7 / 4 by ring, rational_exp_seven_quarter_piI]

@[simp] private theorem rational_exp_norm_piI_one_quarter :
    Complex.exp (Real.pi * Complex.I * (1 / 4 : ℂ)) = rationalGaussPlus := by
  rw [show (Real.pi * Complex.I * (1 / 4 : ℂ) : ℂ) =
    Complex.I * Real.pi * (1 / 4 : ℂ) by ring, rational_exp_norm_one_quarter]

@[simp] private theorem rational_exp_norm_piI_three_quarters :
    Complex.exp (Real.pi * Complex.I * (3 / 4 : ℂ)) = -rationalGaussMinus := by
  rw [show (Real.pi * Complex.I * (3 / 4 : ℂ) : ℂ) =
    Complex.I * Real.pi * (3 / 4 : ℂ) by ring, rational_exp_norm_three_quarters]

@[simp] private theorem rational_exp_norm_piI_five_quarters :
    Complex.exp (Real.pi * Complex.I * (5 / 4 : ℂ)) = -rationalGaussPlus := by
  rw [show (Real.pi * Complex.I * (5 / 4 : ℂ) : ℂ) =
    Complex.I * Real.pi * (5 / 4 : ℂ) by ring, rational_exp_norm_five_quarters]

@[simp] private theorem rational_exp_norm_piI_seven_quarters :
    Complex.exp (Real.pi * Complex.I * (7 / 4 : ℂ)) = rationalGaussMinus := by
  rw [show (Real.pi * Complex.I * (7 / 4 : ℂ) : ℂ) =
    Complex.I * Real.pi * (7 / 4 : ℂ) by ring, rational_exp_norm_seven_quarters]

@[simp] private theorem rational_exp_reassociate (z : ℂ) :
    Complex.exp (Complex.I * Real.pi * z) =
      Complex.exp (Real.pi * Complex.I * z) := by
  congr 1 <;> ring

@[simp] private theorem rational_exp_factor_division (z : ℂ) :
    Complex.exp (Real.pi * Complex.I * (z / 4)) =
      Complex.exp (Real.pi * Complex.I * z / 4) := by
  congr 1 <;> ring

private theorem rationalJacobiNegOne_odd (n : ℕ) (hn : Odd n) :
    jacobiSym (-1 : ℤ) n = if n % 4 = 1 then 1 else -1 := by
  have hnMod4 := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn)
  rw [jacobiSym.at_neg_one hn]
  rcases hnMod4 with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1]
    simp [h1]
  · rw [ZMod.χ₄_nat_three_mod_four h3]
    simp [h3]

private theorem rationalJacobiTwo_odd (n : ℕ) (hn : Odd n) :
    jacobiSym (2 : ℤ) n = if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 := by
  rw [jacobiSym.at_two hn, ZMod.χ₈_nat_eq_if_mod_eight]
  simp [Nat.odd_iff.mp hn]

@[simp] private theorem rationalJacobiNegOne_odd_complex (n : ℕ) (hn : Odd n) :
    (jacobiSym (-1 : ℤ) n : ℂ) =
      if n % 4 = 1 then 1 else -1 := by
  exact_mod_cast rationalJacobiNegOne_odd n hn

@[simp] private theorem rationalJacobiTwo_odd_complex (n : ℕ) (hn : Odd n) :
    (jacobiSym (2 : ℤ) n : ℂ) =
      if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 := by
  exact_mod_cast rationalJacobiTwo_odd n hn

private theorem rationalArchQuarterFactor (s : ℤ) (hs : s = 1 ∨ s = -1) :
    Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / 4)) =
      if s = 1 then rationalGaussMinus else rationalGaussPlus := by
  rcases hs with hs | hs
  · subst s
    simp only [if_pos rfl]
    simpa [rationalGaussMinus] using rational_exp_neg_piI_div_four
  · subst s
    have hsneq : (-1 : ℤ) ≠ 1 := by norm_num
    simp only [if_neg hsneq]
    norm_num
    have harg : -( -(Real.pi * Complex.I) / 4) =
        Real.pi * Complex.I / 4 := by ring
    rw [harg]
    simpa [rationalGaussPlus] using rational_exp_piI_div_four

private theorem rationalGaussPlus_mul_minus :
    rationalGaussPlus * rationalGaussMinus = 1 := by
  change ((1 + Complex.I) / (Real.sqrt 2 : ℂ)) *
    ((1 - Complex.I) / (Real.sqrt 2 : ℂ)) = 1
  rw [← rational_exp_piI_div_four, ← rational_exp_neg_piI_div_four]
  calc
    Complex.exp (Real.pi * Complex.I / 4) *
        Complex.exp (-(Real.pi * Complex.I / 4)) =
        Complex.exp (Real.pi * Complex.I / 4 + -(Real.pi * Complex.I / 4)) :=
          (Complex.exp_add _ _).symm
    _ = 1 := by simp

private theorem rationalGaussPlus_sq : rationalGaussPlus ^ 2 = Complex.I := by
  change ((1 + Complex.I) / (Real.sqrt 2 : ℂ)) ^ 2 = Complex.I
  rw [← rational_exp_piI_div_four]
  calc
    Complex.exp (Real.pi * Complex.I / 4) ^ 2 =
        Complex.exp (Real.pi * Complex.I / 4) *
          Complex.exp (Real.pi * Complex.I / 4) := by rw [pow_two]
    _ =
        Complex.exp (Real.pi * Complex.I / 4 + Real.pi * Complex.I / 4) :=
          (Complex.exp_add _ _).symm
    _ = Complex.exp (Real.pi / 2 * Complex.I) := by congr 1 <;> ring
    _ = Complex.I := Complex.exp_pi_div_two_mul_I

private theorem rationalGaussMinus_sq : rationalGaussMinus ^ 2 = -Complex.I := by
  change ((1 - Complex.I) / (Real.sqrt 2 : ℂ)) ^ 2 = -Complex.I
  rw [← rational_exp_neg_piI_div_four]
  calc
    Complex.exp (-(Real.pi * Complex.I / 4)) ^ 2 =
        Complex.exp (-(Real.pi * Complex.I / 4)) *
          Complex.exp (-(Real.pi * Complex.I / 4)) := by rw [pow_two]
    _ =
        Complex.exp (-(Real.pi * Complex.I / 4) +
          -(Real.pi * Complex.I / 4)) := (Complex.exp_add _ _).symm
    _ = Complex.exp (-Real.pi / 2 * Complex.I) := by congr 1 <;> ring
    _ = -Complex.I := Complex.exp_neg_pi_div_two_mul_I

private theorem rational_zmod8_signed_nat_val (s : ℤ) (n : ℕ)
    (hn : Odd n) (hs : s = 1 ∨ s = -1) :
    (((s * (n : ℤ) : ℤ) : ZMod 8).val) =
      if s = 1 then n % 8 else 8 - n % 8 := by
  have hnMod2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hnMod8Odd : (n % 8) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 8)]
    exact hnMod2
  have hnz : (n : ZMod 8) ≠ 0 := by
    intro h
    have hval : n % 8 = 0 := by
      have hv := congrArg ZMod.val h
      simpa [ZMod.val_natCast] using hv
    omega
  rcases hs with hs | hs
  · rw [hs]
    simp [ZMod.val_natCast]
  · rw [hs, show (-1 : ℤ) * (n : ℤ) = -(n : ℤ) by ring,
      show ((-(n : ℤ) : ℤ) : ZMod 8) = -(n : ZMod 8) by simp]
    simp [ZMod.neg_val, hnz, ZMod.val_natCast]

private theorem rational_phase_supplement_table (s : ℤ) (n e : ℕ)
    (hs : s = 1 ∨ s = -1) (hn : Odd n) (he : e = 0 ∨ e = 1) :
    let r : ℕ := if s = 1 then n % 8 else 8 - n % 8
    (if e = 0 then (1 + Complex.I ^ r) / (Real.sqrt 2 : ℂ)
      else Complex.exp (Real.pi * Complex.I * (r : ℂ) / 4)) *
      (if n % 4 = 1 then 1 else Complex.I) *
      (jacobiSym s n : ℂ) * (jacobiSym (2 : ℤ) n : ℂ) ^ e *
      Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / 4)) = 1 := by
  classical
  let r : ℕ := if s = 1 then n % 8 else 8 - n % 8
  change (if e = 0 then (1 + Complex.I ^ r) / (Real.sqrt 2 : ℂ)
      else Complex.exp (Real.pi * Complex.I * (r : ℂ) / 4)) *
      (if n % 4 = 1 then 1 else Complex.I) *
      (jacobiSym s n : ℂ) * (jacobiSym (2 : ℤ) n : ℂ) ^ e *
      Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / 4)) = 1
  have hnMod2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hnMod8Odd : (n % 8) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 8)]
    exact hnMod2
  have hmod8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have hlt := Nat.mod_lt n (by norm_num : 0 < 8)
    interval_cases h : n % 8 <;> simp_all
  have hmod4eq : n % 4 = n % 8 % 4 := by
    symm
    exact Nat.mod_mod_of_dvd n (by norm_num : 4 ∣ 8)
  have hsqrtSq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hsqrtNeReal : Real.sqrt 2 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have hsqrtNe : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast hsqrtNeReal
  have harchQuarter := rationalArchQuarterFactor s hs
  rcases hs with hs | hs
  all_goals rcases he with he | he
  all_goals rcases hmod8 with hmod1 | hmod3 | hmod5 | hmod7
  all_goals
    rw [harchQuarter]
    rw [hs]
    try rw [rationalJacobiNegOne_odd_complex n hn]
    rw [rationalJacobiTwo_odd_complex n hn]
    simp_all [r, hmod4eq]
  all_goals
    repeat' first
    | rw [rational_exp_piI_div_four]
    | rw [rational_exp_neg_piI_div_four]
    | rw [rational_exp_three_quarter_piI]
    | rw [rational_exp_five_quarter_piI]
    | rw [rational_exp_seven_quarter_piI]
    | rw [rational_exp_norm_one_quarter]
    | rw [rational_exp_norm_neg_quarter]
    | rw [rational_exp_norm_three_quarters]
    | rw [rational_exp_norm_five_quarters]
    | rw [rational_exp_norm_seven_quarters]
    | rw [rational_exp_norm_piI_one_quarter]
    | rw [rational_exp_norm_piI_three_quarters]
    | rw [rational_exp_norm_piI_five_quarters]
    | rw [rational_exp_norm_piI_seven_quarters]
    try dsimp [rationalGaussPlus, rationalGaussMinus]
    have hsqrtNe : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
    have hsqrtSq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
    field_simp [hsqrtNe]
    all_goals
      ring_nf
      simp [Complex.I_sq, hsqrtSq] <;> ring_nf

/-- Rational one-dimensional product formula for the explicit local phases.
Guide: PROOFS.md:482–485. Uses: jacobiSym quadratic reciprocity and supplements; rational numerator/denominator factorization. -/
theorem rational_phase_product (a : ℚˣ) :
    (Function.mulSupport fun p : Nat.Primes => rationalPrimePhase p a).Finite ∧
    (∏ᶠ p : Nat.Primes, rationalPrimePhase p a) * rationalArchPhase a = 1 := by
  classical
  constructor
  · let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hs : Function.mulSupport (fun p : Nat.Primes => rationalPrimePhase p a) ⊆
        insert p2 (rationalOddValSupport a) := by
      intro p hp
      change rationalPrimePhase p a ≠ 1 at hp
      by_cases hp2 : p.1 = 2
      · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext hp2))
      · right
        by_contra hEven
        have hEven' : Even (padicValRat p.1 (a : ℚ)) := by
          simpa [rationalOddValSupport] using hEven
        have heq : rationalPrimePhase p a = 1 := by
          simp [rationalPrimePhase, hp2, hEven']
        exact hp heq
    exact (rationalOddValSupport_finite a).insert p2 |>.subset hs
  ·
    let S := (rationalOddPrimeSupport_finite a).toFinset
    let n : ℕ := ∏ p ∈ S, p.1
    let e : ℕ := if Even (padicValRat 2 (a : ℚ)) then 0 else 1
    let s : ℤ := if (a : ℚ) < 0 then -1 else 1
    let base : ℚˣ := rationalSquarefreePartUnit a
    let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    rcases rationalSquarefreePart_decomp a with ⟨b, hb⟩
    have ha : a = base * b ^ 2 := by
      apply Units.ext
      change (a : ℚ) = rationalSquarefreePart a * (b : ℚ) ^ 2
      exact hb
    have hpoint : ∀ p : Nat.Primes,
        rationalPrimePhase p a = rationalPrimePhase p base := by
      intro p
      rw [ha]
      exact rationalPrimePhase_mul_square p base b
    have hfinEq : (∏ᶠ p : Nat.Primes, rationalPrimePhase p a) =
        (∏ᶠ p : Nat.Primes, rationalPrimePhase p base) :=
      finprod_congr hpoint
    have harchEq : rationalArchPhase a = rationalArchPhase base := by
      rw [ha]
      exact rationalArchPhase_mul_square base b
    rw [hfinEq, harchEq]
    have hS (p : Nat.Primes) :
        p ∈ S ↔ p.1 ≠ 2 ∧ ¬Even (padicValRat p.1 (a : ℚ)) := by
      simp [S, rationalOddPrimeSupport]
    have hnot2 : ∀ p ∈ S, p.1 ≠ 2 := by
      intro p hp
      exact (hS p).mp hp |>.1
    have hp2notS : p2 ∉ S := by
      intro hp
      have h := (hS p2).mp hp
      exact h.1 rfl
    have hsuppBase :
        Function.mulSupport (fun p : Nat.Primes => rationalPrimePhase p base) ⊆
          insert p2 S := by
      intro p hp
      change rationalPrimePhase p base ≠ 1 at hp
      by_cases hp2 : p.1 = 2
      · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext hp2))
      · right
        by_contra hpnot
        have hEven : Even (padicValRat p.1 (a : ℚ)) := by
          by_contra hodd
          exact hpnot ((hS p).2 ⟨hp2, hodd⟩)
        have hval : padicValRat p.1 (base : ℚ) = 0 := by
          change padicValRat p.1 (rationalSquarefreePart a) = 0
          rw [rationalSquarefreePart_padicVal a p]
          simp [hp2, hEven]
        exact hp (by simp [rationalPrimePhase, hp2, hval])
    have hprodBase : (∏ᶠ p : Nat.Primes, rationalPrimePhase p base) =
        rationalPrimePhase p2 base * (∏ p ∈ S, rationalPrimePhase p base) := by
      rw [finprod_eq_prod_of_mulSupport_subset
          (f := fun p : Nat.Primes => rationalPrimePhase p base)
          (s := (insert p2 S : Finset Nat.Primes)) (by simpa using hsuppBase),
        Finset.prod_insert hp2notS]
    have hoddFin : (∏ p ∈ S, rationalPrimePhase p base) =
        rationalOddJacobiProduct S *
          (jacobiSym s n : ℂ) * (jacobiSym (2 : ℤ) n : ℂ) ^ e := by
      simpa [S, n, e, s, base] using
        rationalSquarefreePart_odd_finite_product a
    have hnOdd : Odd n := rationalOddProduct_isOdd S hnot2
    have hH : rationalOddJacobiProduct S =
        if n % 4 = 1 then 1 else Complex.I := by
      simpa [n] using rationalOddJacobiProduct_mod_four S hnot2
    have hsCases : s = 1 ∨ s = -1 := by
      dsimp [s]
      split_ifs <;> norm_num
    have heCases : e = 0 ∨ e = 1 := by
      dsimp [e]
      split_ifs <;> simp
    have hval2 : padicValRat 2 (base : ℚ) = (e : ℤ) := by
      change padicValRat 2 (rationalSquarefreePart a) = (e : ℤ)
      have hv := rationalSquarefreePart_padicVal a ⟨2, Nat.prime_two⟩
      simpa [e] using hv
    have hphase2 : rationalPrimePhase p2 base =
        if e = 0 then (1 + Complex.I ^ rationalDyadicResidue base) /
            (Real.sqrt 2 : ℂ)
        else Complex.exp
          (Real.pi * Complex.I * (rationalDyadicResidue base : ℂ) / 4) := by
      by_cases he0 : e = 0
      · simp [rationalPrimePhase, p2, hval2, he0]
      · have he1 : e = 1 := by
          rcases heCases with h0 | h1
          · exact (he0 h0).elim
          · exact h1
        simp [rationalPrimePhase, p2, hval2, he0, he1]
    have hnpos : 0 < n := by
      dsimp [n]
      apply Finset.prod_pos
      intro p hp
      exact_mod_cast p.2.pos
    have hbaseFormula : (base : ℚ) = (s : ℚ) * (2 : ℚ) ^ e * (n : ℚ) := by
      change ((if (a : ℚ) < 0 then (-1 : ℚ) else 1) *
          (2 : ℚ) ^ (if Even (padicValRat 2 (a : ℚ)) then 0 else 1) *
          ∏ p ∈ (rationalOddPrimeSupport_finite a).toFinset, (p.1 : ℚ)) = _
      dsimp [s, e, n, S]
      push_cast
      ring_nf
    have harchSignC :
        (if (base : ℚ) > 0 then (1 : ℂ) else -1) = (s : ℂ) := by
      rcases hsCases with hs1 | hsneg
      · have hbpos : (base : ℚ) > 0 := by
          rw [hbaseFormula, hs1]
          positivity
        simp [hbpos, hs1]
      · have hbneg : (base : ℚ) < 0 := by
          rw [hbaseFormula, hsneg]
          have hpos : (0 : ℚ) < (2 : ℚ) ^ e * (n : ℚ) :=
            mul_pos (by positivity) (by exact_mod_cast hnpos)
          have hnegCast : ((-1 : ℤ) : ℚ) = -1 := by norm_num
          have hneg : (-1 : ℚ) * ((2 : ℚ) ^ e * (n : ℚ)) < 0 :=
            mul_neg_of_neg_of_pos (by norm_num) hpos
          simpa only [hnegCast, mul_assoc] using hneg
        have hbnot : ¬(base : ℚ) > 0 := not_lt.mpr hbneg.le
        simp [hbnot, hsneg]
    have harch : rationalArchPhase base =
        Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / 4)) := by
      unfold rationalArchPhase
      rw [harchSignC]
    have hresVal : rationalDyadicResidue base =
        (((s * (n : ℤ) : ℤ) : ZMod 8).val) := by
      simpa [S, n, e, s, base] using rationalSquarefreePart_dyadic_residue a
    have hres : rationalDyadicResidue base =
        if s = 1 then n % 8 else 8 - n % 8 := by
      rw [hresVal]
      exact rational_zmod8_signed_nat_val s n hnOdd hsCases
    have htable := rational_phase_supplement_table s n e hsCases hnOdd heCases
    rw [hprodBase, hoddFin, hH, hphase2, hres, harch]
    simpa only [mul_assoc] using htable

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
