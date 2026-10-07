import Mathlib
import ArtinPrimitiveRoots.Sieve.RoughDensity

/-!
# Shared definitions for the marked Type II argument

`def:marked-data` — `08-type-ii.tex:14-59`, identical to PD `03-determinant.tex:7-35`.
The rough density is deliberately the existing sieve definition.
-/

namespace ArtinPrimitiveRoots.TypeII

open Classical

/-- `def:marked-data` — `08-type-ii.tex:14-59`. Primes in the band
`[exp((log x)^a), exp(2(log x)^a)]`. -/
noncomputable def primeBand (x a : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.exp (2 * Real.rpow (Real.log x) a)⌋₊ + 1)).filter fun p =>
    p.Prime ∧ Real.exp (Real.rpow (Real.log x) a) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) a)

/-- `def:marked-data` — reciprocal prime mass of one marked band. -/
noncomputable def bandMass (x a : ℝ) : ℝ :=
  ∑ p ∈ primeBand x a, 1 / (p : ℝ)

/-- Number of prime factors from one marked band, counted without multiplicity. -/
noncomputable def bandOmega (x a : ℝ) (h : ℕ) : ℕ :=
  (primeBand x a).filter (fun p => p ∣ h) |>.card

/-- The finite set of all marked primes. `biUnion` removes any overlap for small `x`; theorems
about the asymptotic argument impose the separated-band hypotheses from N4. -/
noncomputable def markedPrimes (x : ℝ) (K : ℕ) (a : Fin K → ℝ) : Finset ℕ :=
  Finset.univ.biUnion fun i => primeBand x (a i)

/-- The marked part `h_𝒫 = ∏_{p∈𝒫} p^{v_p(h)}`. -/
noncomputable def markedPart (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (h : ℕ) : ℕ :=
  ∏ p ∈ markedPrimes x K a, p ^ padicValNat p h

/-- Total number of prime divisors counted by the marked groups. -/
noncomputable def markedOmega (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (h : ℕ) : ℕ :=
  ∑ i : Fin K, bandOmega x (a i) h

/-- `def:marked-data` — the marked weight `q_d^(ω(h)-K) ∏_i ω_i(h)/V_i`. It vanishes unless each group meets `h`,
so the natural subtraction in the exponent agrees with the paper's integer exponent. -/
noncomputable def markedWeight (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (q_d : ℝ) (h : ℕ) : ℝ :=
  if ∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ h then
    q_d ^ (markedOmega x K a h - K) *
      ∏ i : Fin K, (bandOmega x (a i) h : ℝ) / bandMass x (a i)
  else 0

/-- The least-prime-factor roughness condition, with `1` rough at every level (the empty
universal condition). -/
def roughAbove (n : ℕ) (y : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → y < (p : ℝ)

/-- The finite set of primes at most `y`. -/
noncomputable def primesUpTo (y : ℝ) : Finset ℕ :=
  (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime

/-- `V(y) = ∏_{p≤y}(1-1/p)`. -/
noncomputable def roughSieveProduct (y : ℝ) : ℝ :=
  ∏ p ∈ primesUpTo y, (1 - 1 / (p : ℝ))

/-- `def:marked-data` — N4's fixed band-exponent conditions. -/
def ValidBands (K : ℕ) (a : Fin K → ℝ) : Prop :=
  0 < K ∧ (∀ i, (1 / 10 : ℝ) < a i ∧ a i < 1 / 5) ∧
    ∀ i j : Fin K, i.val < j.val → a i < a j

/-- `def:marked-data` — the N1 scale `L = log x`. -/
noncomputable def logScale (x : ℝ) : ℝ := Real.log x

/-- `def:marked-data` — the N1 cutoff `W = exp(L^0.24)`. -/
noncomputable def roughCutoff (x : ℝ) : ℝ :=
  Real.exp (Real.rpow (Real.log x) (24 / 100 : ℝ))

/-- The marked multiplicative function conditions (N5), at a fixed `x` and fixed marked bands. -/
def IsMarkedInvariant (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (F : ℕ → ℂ) : Prop :=
  (∀ h, ‖F h‖ ≤ 1) ∧
    ∀ p h, p ∈ markedPrimes x K a → p.Prime → F (p * h) = F h

/-- An explicit dyadic interval of natural numbers. -/
noncomputable def dyadicIntegers (H : ℝ) : Finset ℕ :=
  (Finset.range (⌊2 * H⌋₊ + 1)).filter fun n => H ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * H

/-- Complex exponential `e(t)=exp(2πit)`, used by the imported Type II chains. -/
noncomputable def additiveCharacter (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * t))

end ArtinPrimitiveRoots.TypeII
