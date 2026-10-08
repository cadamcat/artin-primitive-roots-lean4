import ArtinPrimitiveRoots.A1.Field

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- One integral denominator vanishes at every chosen prime and is a unit at all other primes. -/
theorem th_classical_supported_denominator (T : Finset (FinPlace F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧
      (∀ v ∈ T, v.valuation F (algebraMap (𝓞 F) F d) < 1) ∧
      ∀ v ∉ T, v.valuation F (algebraMap (𝓞 F) F d) = 1 := by
  classical
  let I : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal
  have hI : I ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v hv => v.ne_bot
  let I₀ : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let n : ℕ := Fintype.card (ClassGroup (𝓞 F))
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have hIn : I ^ n ∈ (Ideal (𝓞 F))⁰ := pow_mem I₀.property n
  have hclass : ClassGroup.mk0 ⟨I ^ n, hIn⟩ = 1 := by
    change ClassGroup.mk0 (I₀ ^ n) = 1
    rw [ClassGroup.mk0.map_pow]
    exact pow_card_eq_one
  letI : (I ^ n).IsPrincipal := (ClassGroup.mk0_eq_one_iff hIn).mp hclass
  let d : 𝓞 F := Submodule.IsPrincipal.generator (I ^ n)
  have hdspan : Ideal.span ({d} : Set (𝓞 F)) = I ^ n :=
    Ideal.span_singleton_generator (I ^ n)
  have hd : d ≠ 0 := by
    intro hd0
    apply pow_ne_zero n hI
    rw [← hdspan, hd0]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hpow : I ^ n ≤ I := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hk, pow_succ]
    exact Ideal.mul_le_right
  have hdmem : d ∈ I ^ n := Submodule.IsPrincipal.generator_mem (I ^ n)
  refine ⟨d, hd, ?_, ?_⟩
  · intro v hv
    apply (v.valuation_lt_one_iff_mem (K := F) d).mpr
    have hIv : I ≤ v.asIdeal := Ideal.prod_le_inf.trans (Finset.inf_le hv)
    exact (hpow.trans hIv) hdmem
  · intro v hv
    apply (v.valuation_eq_one_iff_notMem (K := F)).mpr
    intro hdv
    have hInV : I ^ n ≤ v.asIdeal := by
      rw [← hdspan]
      exact (Ideal.span_singleton_le_iff_mem (I := v.asIdeal)).mpr hdv
    have hIv : I ≤ v.asIdeal := Ideal.IsPrime.le_of_pow_le hInV
    obtain ⟨u, hu, huv⟩ := v.isPrime.prod_le.mp hIv
    have heq : u.asIdeal = v.asIdeal := u.isMaximal.eq_of_le v.isPrime.ne_top huv
    exact hv (HeightOneSpectrum.ext heq ▸ hu)

end ArtinPrimitiveRoots.A1.Theta
