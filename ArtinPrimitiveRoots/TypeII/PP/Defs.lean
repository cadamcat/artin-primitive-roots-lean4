import ArtinPrimitiveRoots.Ext.TypeIIInputs

/-! Shared notation for the Prime Predecessors long-prime chain, PP
`02-long-prime.tex:48-579`. -/

namespace ArtinPrimitiveRoots.TypeII.PP

open Classical
open ArtinPrimitiveRoots.TypeII

/-- Finite tuples of natural numbers with each coordinate at most `M`. -/
noncomputable def boundedTuples (s M : ℕ) : Finset (Fin s → ℕ) :=
  (Finset.univ : Finset (Fin s → Fin (M + 1))).image fun v i => (v i : ℕ)

/-- The Vinogradov mean-value count `J_{s,k}(M)`. -/
noncomputable def vinogradovCount (s k M : ℕ) : ℕ :=
  (((boundedTuples s M).product (boundedTuples s M)).filter fun uv =>
    (∀ j : Fin k, ∑ i : Fin s, uv.1 i ^ (j.val + 1) =
      ∑ i : Fin s, uv.2 i ^ (j.val + 1)) ∧
    (∀ i, 1 ≤ uv.1 i ∧ uv.1 i ≤ M) ∧
    (∀ i, 1 ≤ uv.2 i ∧ uv.2 i ≤ M)).card

/-- `L(s,χ)` with a positive modulus, using Mathlib's analytic continuation. -/
noncomputable def dirichletLValue (q : ℕ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  exact DirichletCharacter.LFunction χ s

/-- The main-term coefficient `c_χ=q^{-1}∑_{a mod q}χ(a)`. -/
noncomputable def characterMean (q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ a ∈ Finset.range q, χ (a : ZMod q)

/-- Finite prime polynomial on a subinterval of `[N,2N]`. -/
noncomputable def primeDirichletPolynomial (N : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (I : Set ℕ) : ℂ :=
  ∑ p ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun (p : ℕ) =>
      p.Prime ∧ N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N ∧ p ∈ I),
    (χ (p : ZMod q) : ℂ) * Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ))

/-- Prime exponential sum on an arbitrary interval inside a dyad. -/
noncomputable def primePhaseSum (N : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (I : Set ℕ) : ℂ :=
  ∑ p ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun (p : ℕ) =>
      p.Prime ∧ N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N ∧ p ∈ I),
    (χ (p : ZMod q) : ℂ) * Complex.exp (Complex.I * t * Real.log (p : ℝ))

/-- Dirichlet polynomial truncated at `Y`. -/
noncomputable def dirichletPartialSum (q : ℕ) (χ : DirichletCharacter ℂ q)
    (Y : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊Y⌋₊ + 1)).filter (fun n => 1 ≤ n),
    (χ (n : ZMod q) : ℂ) * Complex.exp (-s * Real.log (n : ℝ))

/-- Sum of the principal phase over integers in an interval and one residue class. -/
noncomputable def residuePhaseSum (N' : ℝ) (q : ℕ) (a : ZMod q)
    (v : ℝ) (I : Set ℕ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊2 * N'⌋₊ + 1)).filter (fun (n : ℕ) =>
      N' ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N' ∧ n ∈ I ∧ (n : ZMod q) = a),
    Complex.exp (Complex.I * v * Real.log (n : ℝ))

end ArtinPrimitiveRoots.TypeII.PP
