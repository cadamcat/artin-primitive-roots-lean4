import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem rationalUnitPart_padicVal_zero (p : Nat.Primes) (a : ℚˣ) :
    padicValRat p.1 (rationalUnitPart p.1 a) = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  have ha : (a : ℚ) ≠ 0 := by
    intro h
    have h' := a.val_inv
    rw [h, zero_mul] at h'
    exact zero_ne_one h'
  have hp : (p.1 : ℚ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  unfold rationalUnitPart
  rw [padicValRat.div ha (zpow_ne_zero _ hp), padicValRat.zpow,
    padicValRat.self p.2.one_lt]
  ring

private theorem rationalUnitPart_no_prime_factors (p : Nat.Primes) (a : ℚˣ) :
    ¬ p.1 ∣ (rationalUnitPart p.1 a).num.natAbs ∧
    ¬ p.1 ∣ (rationalUnitPart p.1 a).den := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let q := rationalUnitPart p.1 a
  have hqne : q ≠ 0 := by
    have ha : (a : ℚ) ≠ 0 := by
      intro h
      have h' := a.val_inv
      rw [h, zero_mul] at h'
      exact zero_ne_one h'
    have hp : (p.1 : ℚ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    change (a : ℚ) / (p.1 : ℚ) ^ padicValRat p.1 (a : ℚ) ≠ 0
    exact div_ne_zero ha (zpow_ne_zero _ hp)
  have hval : padicValInt p.1 q.num = padicValNat p.1 q.den := by
    have h := padicValRat_def p.1 q
    rw [show padicValRat p.1 q = 0 by simpa [q] using rationalUnitPart_padicVal_zero p a] at h
    omega
  have hnumne : q.num ≠ 0 := by
    intro h
    apply hqne
    exact Rat.zero_of_num_zero h
  have hred : Nat.gcd q.num.natAbs q.den = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp q.reduced
  have hboth (hn : p.1 ∣ q.num.natAbs) (hd : p.1 ∣ q.den) : False := by
    have hpgcd : p.1 ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hn hd
    rw [hred] at hpgcd
    have hpone : p.1 = 1 := Nat.dvd_one.mp hpgcd
    exact p.2.ne_one hpone
  constructor
  · intro hn
    have hnotden : ¬ p.1 ∣ q.den := by
      intro hd
      exact hboth hn hd
    have hdval : padicValNat p.1 q.den = 0 := padicValNat.eq_zero_of_not_dvd hnotden
    have hnumdvd : (p.1 : ℤ) ^ 1 ∣ q.num := by
      have hnumdvd : (p.1 : ℤ) ∣ q.num := Int.natCast_dvd.mpr hn
      simpa using hnumdvd
    have hge := (padicValInt_dvd_iff (p := p.1) 1 q.num).mp hnumdvd
    rcases hge with hz | hge
    · exact (hnumne hz).elim
    · have hnumval : padicValInt p.1 q.num = 0 := by rw [hval, hdval]
      omega
  · intro hd
    have hnotnum : ¬ p.1 ∣ q.num.natAbs := by
      intro hn
      exact hboth hn hd
    have hnotnumInt : ¬ (p.1 : ℤ) ∣ q.num := by
      intro hn
      exact hnotnum (Int.natCast_dvd.mp hn)
    have hnumval : padicValInt p.1 q.num = 0 :=
      padicValInt.eq_zero_of_not_dvd hnotnumInt
    have hdge := one_le_padicValNat_of_dvd q.den_nz hd
    have hdval : padicValNat p.1 q.den = 0 := by rw [← hval, hnumval]
    omega

private theorem rationalUnitPart_gcd_one (p : Nat.Primes) (a : ℚˣ) :
    ((rationalUnitPart p.1 a).num * (rationalUnitPart p.1 a).den : ℤ).gcd p.1 = 1 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let q := rationalUnitPart p.1 a
  rcases rationalUnitPart_no_prime_factors p a with ⟨hn, hd⟩
  have hprod : ¬ p.1 ∣ q.num.natAbs * q.den := by
    intro h
    rcases p.2.dvd_mul.mp h with h | h
    · exact hn h
    · exact hd h
  have hcop : Nat.Coprime (q.num.natAbs * q.den) p.1 := by
    rw [Nat.coprime_comm, p.2.coprime_iff_not_dvd]
    exact hprod
  rw [Int.gcd_eq_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.coprime_iff_gcd_eq_one.mp hcop

private theorem rationalDyadicResidue_odd (a : ℚˣ) :
    Odd (rationalDyadicResidue a) := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let q := rationalUnitPart 2 a
  rcases rationalUnitPart_no_prime_factors p a with ⟨hnum, hden⟩
  have hcopNum : Nat.Coprime q.num.natAbs 8 := by
    have hcop2 : Nat.Coprime q.num.natAbs 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      exact hnum
    rw [show 8 = 2 ^ 3 by norm_num, Nat.coprime_pow_right_iff (by norm_num : 0 < 3)]
    exact hcop2
  have hcopDen : Nat.Coprime q.den 8 := by
    have hcop2 : Nat.Coprime q.den 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      exact hden
    rw [show 8 = 2 ^ 3 by norm_num, Nat.coprime_pow_right_iff (by norm_num : 0 < 3)]
    exact hcop2
  have hnumUnit : IsUnit (q.num : ZMod 8) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime]
    simpa using hcopNum.symm
  have hdenUnit : IsUnit (q.den : ZMod 8) :=
    (ZMod.isUnit_iff_coprime q.den 8).2 hcopDen
  have hdenInv : IsUnit ((q.den : ZMod 8)⁻¹) := by
    rw [← hdenUnit.unit_spec, ZMod.inv_coe_unit]
    exact (hdenUnit.unit⁻¹).isUnit
  have hresUnit : IsUnit ((q.num : ZMod 8) * (q.den : ZMod 8)⁻¹) :=
    hnumUnit.mul hdenInv
  let v : (ZMod 8)ˣ := hresUnit.unit
  have hv : (v : ZMod 8) = (q.num : ZMod 8) * (q.den : ZMod 8)⁻¹ :=
    hresUnit.unit_spec
  have hvcop : Nat.Coprime ((v : ZMod 8).val) 8 := ZMod.val_coe_unit_coprime v
  have hvcop' : Nat.Coprime ((v : ZMod 8).val) (2 ^ 3) := by
    convert hvcop using 1 <;> norm_num
  have hvcop2 : Nat.Coprime ((v : ZMod 8).val) 2 :=
    (Nat.coprime_pow_right_iff (by norm_num : 0 < 3)
      ((v : ZMod 8).val) 2).mp hvcop'
  have hvnotEven : ¬ Even ((v : ZMod 8).val) := by
    intro he
    have hdvd : 2 ∣ (v : ZMod 8).val := even_iff_two_dvd.mp he
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hvcop2.symm hdvd
  have hvOdd : Odd ((v : ZMod 8).val) := Nat.not_even_iff_odd.mp hvnotEven
  have hr : rationalDyadicResidue a = (v : ZMod 8).val := by
    change (((q.num : ZMod 8) * (q.den : ZMod 8)⁻¹).val) = _
    rw [hv]
  rw [hr]
  exact hvOdd

private theorem norm_one_add_I : ‖(1 : ℂ) + Complex.I‖ = Real.sqrt 2 := by
  have hsq : ‖(1 : ℂ) + Complex.I‖ ^ 2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq, Complex.I_re, Complex.I_im]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg ((1 : ℂ) + Complex.I), Real.sqrt_nonneg (2 : ℝ)]

private theorem norm_one_sub_I : ‖(1 : ℂ) - Complex.I‖ = Real.sqrt 2 := by
  have hsq : ‖(1 : ℂ) - Complex.I‖ ^ 2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq, Complex.I_re, Complex.I_im]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg ((1 : ℂ) - Complex.I), Real.sqrt_nonneg (2 : ℝ)]

private theorem dyadic_even_phase_norm (r : ℕ) (hr : Odd r) :
    ‖(1 + Complex.I ^ r) / (Real.sqrt 2 : ℂ)‖ = 1 := by
  have hmod : r % 4 = 1 ∨ r % 4 = 3 := by
    rcases hr with ⟨k, hk⟩
    omega
  rcases hmod with hmod | hmod
  · have hpow : Complex.I ^ r = Complex.I := by
      rw [Complex.I_pow_eq_pow_mod, hmod]
      norm_num
    have hs : ‖(Real.sqrt 2 : ℂ)‖ = |Real.sqrt 2| := RCLike.norm_ofReal _
    rw [hpow, norm_div, norm_one_add_I, hs]
    rw [abs_of_pos (Real.sqrt_pos.2 (by norm_num))]
    exact div_self (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  · have hpow : Complex.I ^ r = -Complex.I := by
      rw [Complex.I_pow_eq_pow_mod, hmod]
      norm_num [Complex.I_pow_three]
    have hs : ‖(Real.sqrt 2 : ℂ)‖ = |Real.sqrt 2| := RCLike.norm_ofReal _
    rw [hpow, norm_div]
    have hn : ‖(1 : ℂ) + (-Complex.I)‖ = Real.sqrt 2 := by
      simpa only [sub_eq_add_neg] using norm_one_sub_I
    rw [hn, hs]
    rw [abs_of_pos (Real.sqrt_pos.2 (by norm_num))]
    exact div_self (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))

private theorem dyadic_odd_phase_norm (r : ℕ) :
    ‖Complex.exp (Real.pi * Complex.I * (r : ℂ) / 4)‖ = 1 := by
  simp [Complex.norm_exp]

/-- All explicit rational phases are nonzero units.
Guide: PROOFS.md:482–485. Uses: padicValRat arithmetic; jacobiSym abs bound; dyadic residues. -/
theorem rational_prime_phase_norm (p : Nat.Primes) (a : ℚˣ) :
    ‖rationalPrimePhase p a‖ = 1 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  by_cases hp2 : p.1 = 2
  · have hrOdd : Odd (rationalDyadicResidue a) := rationalDyadicResidue_odd a
    by_cases hk : Even (padicValRat 2 (a : ℚ))
    · simpa [rationalPrimePhase, hp2, hk] using
        dyadic_even_phase_norm (rationalDyadicResidue a) hrOdd
    · simpa [rationalPrimePhase, hp2, hk] using
        dyadic_odd_phase_norm (rationalDyadicResidue a)
  · by_cases hk : Even (padicValRat p.1 (a : ℚ))
    · simp [rationalPrimePhase, hp2, hk]
    · have hgcd := rationalUnitPart_gcd_one p a
      have hJ : ‖(jacobiSym
          ((rationalUnitPart p.1 a).num * (rationalUnitPart p.1 a).den) p.1 : ℂ)‖ = 1 := by
        rcases jacobiSym.eq_one_or_neg_one hgcd with h | h <;> rw [h] <;> norm_num
      have hphase : ‖if p.1 % 4 = 1 then
          (jacobiSym ((rationalUnitPart p.1 a).num *
            (rationalUnitPart p.1 a).den) p.1 : ℂ)
        else Complex.I *
          (jacobiSym ((rationalUnitPart p.1 a).num *
            (rationalUnitPart p.1 a).den) p.1 : ℂ)‖ = 1 := by
        by_cases h4 : p.1 % 4 = 1
        · rw [if_pos h4]
          exact hJ
        · rw [if_neg h4]
          calc
            ‖Complex.I *
                (jacobiSym ((rationalUnitPart p.1 a).num *
                  (rationalUnitPart p.1 a).den) p.1 : ℂ)‖ =
                ‖Complex.I‖ * ‖(jacobiSym ((rationalUnitPart p.1 a).num *
                  (rationalUnitPart p.1 a).den) p.1 : ℂ)‖ := norm_mul _ _
            _ = ‖(jacobiSym ((rationalUnitPart p.1 a).num *
                (rationalUnitPart p.1 a).den) p.1 : ℂ)‖ := by simp
            _ = 1 := hJ
      simpa [rationalPrimePhase, hp2, hk] using hphase

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
