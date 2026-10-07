import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

public section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain

namespace ArtinPrimitiveRoots.Hecke.EulerProduct

variable {K : Type*} [Field K] [NumberField K]

/-- The rational prime below a height-one prime of the ring of integers. -/
noncomputable def primeIndex (P : HeightOneSpectrum (𝓞 K)) : Nat.Primes := by
  letI : P.asIdeal.IsPrime := P.isPrime
  letI : NeZero P.asIdeal := ⟨P.ne_bot⟩
  exact ⟨Ideal.absNorm (P.asIdeal.under ℤ), Nat.absNorm_under_prime P.asIdeal⟩

/-- The rational prime below `P` divides its absolute norm. -/
theorem absNorm_eq_primeIndex_pow (P : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm P.asIdeal = (primeIndex P).val ^ P.asIdeal.inertiaDeg ℤ := by
  letI : P.asIdeal.IsPrime := P.isPrime
  letI : NeZero P.asIdeal := ⟨P.ne_bot⟩
  simpa [primeIndex] using
    (Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal).symm

/-- The height-one primes lying over a fixed rational prime. -/
def primeIndexFiber (p : Nat.Primes) : Set (HeightOneSpectrum (𝓞 K)) :=
  {P | primeIndex P = p}

/-- The prime ideal of `ℤ` corresponding to a rational prime. -/
def rationalPrimeIdeal (p : Nat.Primes) : Ideal ℤ := Ideal.span {(p.val : ℤ)}

private theorem rationalPrimeIdeal_ne_bot (p : Nat.Primes) : rationalPrimeIdeal p ≠ ⊥ := by
  intro hbot
  have hp0 : (p.val : ℤ) = 0 :=
    Ideal.span_singleton_eq_bot.mp (by simpa [rationalPrimeIdeal] using hbot)
  exact p.2.ne_zero (Int.natCast_eq_zero.mp hp0)

private theorem rationalPrimeIdeal_isMaximal (p : Nat.Primes) :
    (rationalPrimeIdeal p).IsMaximal := by
  have hpZ : Prime (p.val : ℤ) := Int.prime_iff_natAbs_prime.mpr p.2
  have hpmax : (Ideal.span {(p.val : ℤ)} : Ideal ℤ).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr hpZ).isMaximal
      (rationalPrimeIdeal_ne_bot p)
  simpa [rationalPrimeIdeal] using hpmax

private theorem liesOver_primeIndexFiber {p : Nat.Primes} {P : HeightOneSpectrum (𝓞 K)}
    (hP : P ∈ primeIndexFiber p) :
    P.asIdeal.LiesOver (rationalPrimeIdeal p) := by
  have hbase : Ideal.absNorm (P.asIdeal.under ℤ) = p.val := congrArg Subtype.val hP
  have hspan : P.asIdeal.under ℤ = rationalPrimeIdeal p := by
    calc
      P.asIdeal.under ℤ = Ideal.span {(Ideal.absNorm (P.asIdeal.under ℤ) : ℤ)} :=
        (Int.ideal_span_absNorm_eq_self _).symm
      _ = rationalPrimeIdeal p := by
        dsimp [rationalPrimeIdeal]
        exact congrArg (fun z : ℤ => Ideal.span ({z} : Set ℤ))
          (congrArg (fun n : ℕ => (n : ℤ)) hbase)
  rw [Ideal.liesOver_iff]
  exact hspan.symm

private def primeFiberToFinset (p : Nat.Primes) :
    {P : HeightOneSpectrum (𝓞 K) // P ∈ primeIndexFiber p} →
      {Q // Q ∈ IsDedekindDomain.primesOverFinset (rationalPrimeIdeal p) (𝓞 K)} := by
  classical
  letI : (rationalPrimeIdeal p).IsMaximal := rationalPrimeIdeal_isMaximal p
  intro P
  let hmem : P.1.asIdeal ∈ (rationalPrimeIdeal p).primesOver (𝓞 K) := by
    change P.1.asIdeal.IsPrime ∧ P.1.asIdeal.LiesOver (rationalPrimeIdeal p)
    exact ⟨P.1.isPrime, liesOver_primeIndexFiber P.2⟩
  exact ⟨P.1.asIdeal,
    (IsDedekindDomain.mem_primesOverFinset_iff (p := rationalPrimeIdeal p) (B := 𝓞 K)
      (rationalPrimeIdeal_ne_bot p)).mpr hmem⟩

private theorem primeFiberToFinset_injective (p : Nat.Primes) :
    Function.Injective (primeFiberToFinset (K := K) p) := by
  intro P Q h
  apply Subtype.ext
  apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
  exact congrArg Subtype.val h

theorem primeIndexFiber_finite (p : Nat.Primes) : (primeIndexFiber (K := K) p).Finite := by
  classical
  exact Finite.of_injective (primeFiberToFinset (K := K) p)
    (primeFiberToFinset_injective (K := K) p)

noncomputable instance primeIndexFiberFintype (p : Nat.Primes) :
    Fintype (primeIndexFiber (K := K) p) := (primeIndexFiber_finite (K := K) p).fintype

/-- There are at most `[K:ℚ]` height-one primes above any rational prime. -/
theorem card_primeIndexFiber_le_finrank (p : Nat.Primes) :
    Fintype.card (primeIndexFiber (K := K) p) ≤ Module.finrank ℚ K := by
  classical
  letI : (rationalPrimeIdeal p).IsMaximal := rationalPrimeIdeal_isMaximal p
  let T := IsDedekindDomain.primesOverFinset (rationalPrimeIdeal p) (𝓞 K)
  have hTcard : T.card ≤ Module.finrank ℚ K := by
    dsimp [T]
    exact Ideal.card_primesOverFinset_le_finrank (R := ℤ) (S := 𝓞 K)
      (K := ℚ) (L := K) (p := rationalPrimeIdeal p) (rationalPrimeIdeal_ne_bot p)
  letI : Fintype {Q // Q ∈ T} := T.fintypeCoeSort
  calc
    Fintype.card (primeIndexFiber p) ≤ Fintype.card {Q // Q ∈ T} :=
      Fintype.card_le_of_injective (primeFiberToFinset (K := K) p)
        (primeFiberToFinset_injective (K := K) p)
    _ = T.card := Fintype.card_coe T
    _ ≤ Module.finrank ℚ K := hTcard

end ArtinPrimitiveRoots.Hecke.EulerProduct
