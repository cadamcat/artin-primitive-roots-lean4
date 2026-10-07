import ArtinPrimitiveRoots.TypeII.Defs

/-! Definitions of the prime-construction weight (`12-construction.tex:19-73`). -/

namespace ArtinPrimitiveRoots.Construction

open Classical
open ArtinPrimitiveRoots.TypeII

/-- `def:con-weights` — 12-construction.tex:19-73. The smooth test functions used in §12: a compactly supported smooth function on `(1,2)`,
bounded between zero and one, with positive integral. -/
def IsTestFunction (Ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ Ψ ∧ Function.support Ψ ⊆ Set.Ioo 1 2 ∧
    (∀ y, 0 ≤ Ψ y) ∧ (∀ y, Ψ y ≤ 1) ∧ 0 < ∫ y in (1 : ℝ)..2, Ψ y

/-- Integers all of whose prime factors belong to the marked prime groups; `1` is included. -/
def IsGroupInteger (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (r : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ r → p ∈ markedPrimes x K a

/-- `def:con-weights` — 12-construction.tex:19-73. The prime-indicator factor
`F(h)=1_{h/h_𝒫=cQ, Q>x^0.9 prime}`. -/
noncomputable def conFactor (x : ℝ) (c K : ℕ) (a : Fin K → ℝ) (h : ℕ) : ℝ :=
  if ∃ Q : ℕ, Q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
      h = c * markedPart x K a h * Q then 1 else 0

/-- `def:con-weights` — 12-construction.tex:19-73. The construction weight `w(d)` from equation
`con:weight`, with its natural domain made explicit. The test-function support forces `x<d<2x`.
-/
noncomputable def conWeight (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) (d : ℕ) : ℝ :=
  if 1 < d ∧ (d : ℤ) ≡ u [ZMOD M] then
    Ψ ((d : ℝ) / x) * conFactor x c K a (d - 1) *
      markedWeight x K a (1 / 2 : ℝ) (d - 1)
  else 0

/-- `def:con-weights` — the total construction mass `X₀ = ∑_d w(d)`. Compact support makes this the displayed finite
sum. -/
noncomputable def conTotalMass (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  ∑ d ∈ Finset.range (⌊2 * x⌋₊ + 1), conWeight x M c u K a Ψ d

/-- The smoothed prime count `A_r(ℓ)` used in the distribution estimates. -/
noncomputable def progressionPrimeSum (x : ℝ) (M c : ℕ) (u : ℤ)
    (Ψ : ℝ → ℝ) (r ℓ : ℕ) : ℝ :=
  ∑ Q ∈ (Finset.range (⌊2 * x⌋₊ + 1)).filter (fun Q =>
      (Q : ℕ).Prime ∧ Real.rpow x (9 / 10 : ℝ) < ((Q : ℕ) : ℝ) ∧
        (((c * r * (Q : ℕ) + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) ∧
          ℓ ∣ c * r * (Q : ℕ) + 1),
    Ψ (((c * r * (Q : ℕ) + 1 : ℕ) : ℝ) / x)

/-- The continuous main term `I_r` in `co:bv-smoothed`. -/
noncomputable def smoothedMainTerm (x : ℝ) (c r : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  (x / (c * r : ℕ)) *
    ∫ y in (1 : ℝ)..2, Ψ y / Real.log ((x * y - 1) / (c * r : ℕ))

/-- Odd squarefree sieve moduli up to a real bound. -/
noncomputable def oddSquarefreeUpTo (D : ℝ) : Finset ℕ :=
  (Finset.range (⌊D⌋₊ + 1)).filter fun ℓ => Odd ℓ ∧ Squarefree ℓ

/-- The local sieve density `g_r(ℓ)=1_{(ℓ,Mr)=1}/φ(ℓ)`. -/
noncomputable def localSieveDensity (M r ℓ : ℕ) : ℝ :=
  if Nat.Coprime ℓ (M * r) then 1 / (Nat.totient ℓ : ℝ) else 0

/-- The singular product for the progression modulo `M`. -/
noncomputable def singularProduct (M : ℕ) : ℝ :=
  2 * (∏' p : ℕ, if p.Prime ∧ 2 < p then
        (1 - 1 / ((p : ℝ) - 1) ^ 2) else 1) *
    (∏ p ∈ (primesUpTo (M : ℝ)).filter (fun p => p ∣ M ∧ 2 < p),
      (1 - 1 / ((p : ℝ) - 1))⁻¹)

/-- The Euler factor `E_i(t)=∏_{p∈P_i}(1+t/(p-1))`. -/
noncomputable def markedEulerFactor (x a t : ℝ) : ℝ :=
  ∏ p ∈ primeBand x a, (1 + t / ((p : ℝ) - 1))

/-- Harmonic mass of the group integers. -/
noncomputable def groupHarmonicMass (x : ℝ) (K : ℕ) (a : Fin K → ℝ) : ℝ :=
  ∑' r : ℕ, if IsGroupInteger x K a r then
    markedWeight x K a (1 / 2 : ℝ) r / (r : ℝ) else 0

/-- The progression sieve product `V_M(y)` from §12. -/
noncomputable def progressionSieveProduct (M : ℕ) (y : ℝ) : ℝ :=
  ∏ p ∈ (primesUpTo y).filter (fun p => 2 < p ∧ ¬ p ∣ M),
    (1 - 1 / ((p : ℝ) - 1))

/-- Product after incorporating the local factor `g_r`. -/
noncomputable def progressionSieveProductFor (M r : ℕ) (y : ℝ) : ℝ :=
  ∏ p ∈ (primesUpTo y).filter (fun p => 2 < p),
    (1 - localSieveDensity M r p)

/-- Weighted mass of construction integers that are `y`-rough. -/
noncomputable def roughConstructionMass (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (⌊2 * x⌋₊ + 1),
    if roughAbove d y then conWeight x M c u K a Ψ d else 0

/-- The prime-divisor bin sum in `con:bin-mass`. -/
noncomputable def primeDivisorBinSum (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) (γ γ' : ℝ) : ℝ :=
  ∑ n ∈ (primesUpTo (Real.rpow x γ')).filter (fun n =>
      Real.rpow x γ < (n : ℝ)),
    ∑ d ∈ Finset.range (⌊2 * x⌋₊ + 1),
      if n ∣ d ∧ roughAbove d (roughCutoff x) then
        conWeight x M c u K a Ψ d else 0

/-- Weighted pair sum on a dyadic box, used in `con:rough-pairs`. -/
noncomputable def roughPairBoxSum (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) (H₁ H₂ : ℝ) : ℝ :=
  ∑ m ∈ dyadicIntegers H₁,
    ∑ n ∈ dyadicIntegers H₂,
      if roughAbove m (roughCutoff x) ∧ roughAbove n (roughCutoff x) then
        conWeight x M c u K a Ψ (m * n) else 0

end ArtinPrimitiveRoots.Construction
