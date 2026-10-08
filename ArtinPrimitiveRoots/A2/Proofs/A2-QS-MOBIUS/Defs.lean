import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».Defs

/-!
# A2-QS-MOBIUS / A2-QS-CANCEL: block-level definitions

Guide: `runs/lanes/sol-thin-found/PROOFS.md:380-550` (S0-S2, C0-C3), re-cut by the lead
(see `runs/lanes/qs-lead/STATEMENTS.md`).

Notation.  `F` a mirrored family with trivial ray factor; rows `a` of the smooth sums are nonzero
ideals coprime to a squarefree ideal `𝔮` (in the blocks `𝔮 = qsBadRad m qS * g`); `ψ = χ_c χ_d⁻¹`
the residual pair character of a coprime equal-class column pair, of exact conductor `f = c d`;
`κ` the squarefree-core cutoff (the guide's `K`); `Λ ≥ 1` the divisor cutoff ratio
(the guide's `P^η`).

Exact decomposition of one pair (lead's derivation, guide S1/S2):
* `qsHigh W M κ 𝔮 ψ = DualLow + DualHigh - OrigLow` (Möbius over `e ∣ 𝔮`, P1, `a = a₀ b²`);
* each low sum is `Σ_{a₀} ψ(a₀) · (coprime square sum)`, and the coprime square sum is
  `main - highDiv + res + trans + tail` (P2 divisor by divisor, cutoffs `Ylo ≤ Zhi`).
The main terms combine into the boundary kernel (C0/C1).
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- Real norm of an ideal. -/
abbrev qsN (a : Ideal (𝓞 K)) : ℝ := (Ideal.absNorm a : ℝ)

/-- The residual pair character `χ_c χ_d⁻¹`. -/
def qsPairChar {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (c d : Ideal (𝓞 K)) : ArtinPrimitiveRoots.A1.HeckeChar K :=
  F.character c * (F.character d)⁻¹

/-! ### Smooth row sums -/

open Classical in
/-- `Σ'_{a ≠ 0, (a,𝔮)=1} ψ(a) h(N a / X)`. -/
def qsTot (h : ℝ → ℂ) (X : ℝ) (𝔮 : Ideal (𝓞 K)) (ψ : ArtinPrimitiveRoots.A1.HeckeChar K) : ℂ :=
  ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
    if IsCoprime a.1 𝔮 then ψ.idealValue a.1 * h (qsN a.1 / X) else 0

open Classical in
/-- High-core row sum: as `qsTot`, restricted to `sf(a) > κ`. -/
def qsHigh (h : ℝ → ℂ) (X κ : ℝ) (𝔮 : Ideal (𝓞 K))
    (ψ : ArtinPrimitiveRoots.A1.HeckeChar K) : ℂ :=
  ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
    if IsCoprime a.1 𝔮 ∧ κ < (qsSfNorm a.1 : ℝ) then ψ.idealValue a.1 * h (qsN a.1 / X) else 0

open Classical in
/-- Low-core row sum: as `qsTot`, restricted to `sf(a) ≤ κ`. -/
def qsLow (h : ℝ → ℂ) (X κ : ℝ) (𝔮 : Ideal (𝓞 K))
    (ψ : ArtinPrimitiveRoots.A1.HeckeChar K) : ℂ :=
  ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
    if IsCoprime a.1 𝔮 ∧ (qsSfNorm a.1 : ℝ) ≤ κ then ψ.idealValue a.1 * h (qsN a.1 / X) else 0

open Classical in
/-- Squarefree ideals coprime to `𝔮` of norm at most `κ`. -/
def qsSqfUpTo (κ : ℝ) (𝔮 : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊κ⌋₊).toFinset).filter
    (fun a => a ≠ ⊥ ∧ Squarefree a ∧ IsCoprime a 𝔮 ∧ qsN a ≤ κ)

open Classical in
/-- The coprime square-variable sum `Σ'_{b ≠ 0, (b,𝔫)=1} F(N b / Z)`. -/
def qsCoprimeSq (F : ℝ → ℂ) (Z : ℝ) (𝔫 : Ideal (𝓞 K)) : ℂ :=
  ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, if IsCoprime b.1 𝔫 then F (qsN b.1 / Z) else 0

/-! ### The high-core matrix (guide `B₂`) -/

open Classical in
/-- Rows of the high-core matrix: nonzero ideals (not necessarily squarefree) coprime to the
modulus and to `qS`, of norm `≤ 3M`, with squarefree-part norm `> κ`. -/
def qsHighRows (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K)) (M κ : ℝ) :
    Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).toFinset).filter
    (fun a => ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a ∧ IsCoprime a qS ∧
      κ < (qsSfNorm a : ℝ))

/-- High-core matrix: entry `√W(N a / M) · χ_c(a)`, columns the up-to columns of norm `≤ N`. -/
def qsHighMatrix {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (W : ℝ → ℝ) (M N κ : ℝ) :
    Matrix (qsHighRows m qS M κ) (qsUpTo m qS N) ℂ :=
  fun a c => (Real.sqrt (W (qsN a.1 / M)) : ℂ) * (F.character c.1).idealValue a.1

/-- `B₂(M,N,κ)`: squared operator norm of the high-core matrix. -/
def qsHighNorm {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (W : ℝ → ℝ) (M N κ : ℝ) : ℝ :=
  ‖OAI.FiniteSieveOperator.operator (qsHighMatrix F W M N κ)‖ ^ 2

open Classical in
/-- High-core energy of a column vector: `Σ'_a W(N a/M) ‖Σ_{c ∈ cols} z(c) χ_c(a)‖²` over rows
coprime to `m` and `qS` with `sf(a) > κ` (the energy form of `B₂`). -/
def qsHighEnergy {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (W : ℝ → ℝ) (M κ : ℝ) (cols : Finset (Ideal (𝓞 K)))
    (z : Ideal (𝓞 K) → ℂ) : ℝ :=
  ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
    if ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧ IsCoprime a.1 qS ∧
        κ < (qsSfNorm a.1 : ℝ) then
      W (qsN a.1 / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue a.1‖ ^ 2
    else 0

open Classical in
/-- The high-core pair sum `Σ'_a W(N a/M) χ_c(a) conj(χ_d(a))`, rows coprime to `m` and `qS`
with `sf(a) > κ`. -/
def qsHighPair {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (W : ℝ → ℝ) (M κ : ℝ) (c d : Ideal (𝓞 K)) : ℂ :=
  ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
    if ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧ IsCoprime a.1 qS ∧
        κ < (qsSfNorm a.1 : ℝ) then
      (W (qsN a.1 / M) : ℂ) * (F.character c).idealValue a.1 *
        conj ((F.character d).idealValue a.1)
    else 0

open Classical in
/-- The gcd block: pairs of columns with `c ⊔ d = g` (i.e. `gcd(c,d) = g`). -/
def qsGcdBlock {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (W : ℝ → ℝ) (M κ : ℝ) (g : Ideal (𝓞 K))
    (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ) : ℂ :=
  ∑ c ∈ cols, ∑ d ∈ cols,
    if c ⊔ d = g then z c * conj (z d) * qsHighPair F W M κ c d else 0

open Classical in
/-- Coprime pair sum `Σ_{c,d ∈ cols, (c,d)=1} z(c) conj(z(d)) Φ(c,d)`. -/
def qsPairSum (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ)
    (Φ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) : ℂ :=
  ∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z c * conj (z d) * Φ c d else 0

/-- The residual block (guide `Σ₃`): coprime residual pairs, high-core sum of the pair
character with rows coprime to `𝔮`. -/
def qsResidualBlock {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (W : ℝ → ℝ) (M κ : ℝ) (𝔮 : Ideal (𝓞 K))
    (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ) : ℂ :=
  qsPairSum cols z (fun c d => qsHigh (fun x => (W x : ℂ)) M κ 𝔮 (qsPairChar F c d))

/-! ### P2 applied divisor by divisor: the five pieces of a coprime square sum

Uniform signature `(F Z 𝔫 Ylo Zhi)`; P2 is used for divisors `N e ≤ Zhi`, its dual sum is a
rapid tail for `N e ≤ Ylo`, and divisors with `N e > Zhi` are summed directly (rapid tail). -/

/-- Complete main term `ρ_K Z Mellin(F)(1) φ(𝔫)/N𝔫`. -/
def qsInnerMain (K : Type) [Field K] [NumberField K] (F : ℝ → ℂ) (Z : ℝ) (𝔫 : Ideal (𝓞 K))
    (_Ylo _Zhi : ℝ) : ℂ :=
  (qsResidueOne K : ℂ) * (Z : ℂ) * mellin F 1 * (qsPhiRatio 𝔫 : ℂ)

open Classical in
/-- High-divisor correction `ρ_K Z Mellin(F)(1) Σ_{e ∣ 𝔫, N e > Zhi} μ(e)/N e`. -/
def qsInnerHighDiv (K : Type) [Field K] [NumberField K] (F : ℝ → ℂ) (Z : ℝ)
    (𝔫 : Ideal (𝓞 K)) (_Ylo Zhi : ℝ) : ℂ :=
  (qsResidueOne K : ℂ) * (Z : ℂ) * mellin F 1 *
    ∑ e ∈ (qsDivisors 𝔫).filter (fun e => Zhi < qsN e), ((qsMu e : ℂ) / (qsN e : ℂ))

open Classical in
/-- Residue term `R_K(F) Σ_{e ∣ 𝔫, N e ≤ Zhi} μ(e)`. -/
def qsInnerRes (K : Type) [Field K] [NumberField K] (F : ℝ → ℂ) (_Z : ℝ)
    (𝔫 : Ideal (𝓞 K)) (_Ylo Zhi : ℝ) : ℂ :=
  qsResidueZero K F * ∑ e ∈ (qsDivisors 𝔫).filter (fun e => qsN e ≤ Zhi), (qsMu e : ℂ)

open Classical in
/-- Transition dual sum `Σ_{e ∣ 𝔫, Ylo < N e ≤ Zhi} μ(e) (Z/N e) Σ'_b (T F)(Z N b / N e)`. -/
def qsInnerTrans (K : Type) [Field K] [NumberField K] (F : ℝ → ℂ) (Z : ℝ)
    (𝔫 : Ideal (𝓞 K)) (Ylo Zhi : ℝ) : ℂ :=
  ∑ e ∈ (qsDivisors 𝔫).filter (fun e => Ylo < qsN e ∧ qsN e ≤ Zhi),
    (qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
      ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, qsTransform K F (Z * qsN b.1 / qsN e)

open Classical in
/-- Rapid tails: dual sums with `N e ≤ Ylo` and direct sums with `N e > Zhi`. -/
def qsInnerTail (K : Type) [Field K] [NumberField K] (F : ℝ → ℂ) (Z : ℝ)
    (𝔫 : Ideal (𝓞 K)) (Ylo Zhi : ℝ) : ℂ :=
  (∑ e ∈ (qsDivisors 𝔫).filter (fun e => qsN e ≤ Ylo),
    (qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
      ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, qsTransform K F (Z * qsN b.1 / qsN e)) +
  ∑ e ∈ (qsDivisors 𝔫).filter (fun e => Zhi < qsN e),
    (qsMu e : ℂ) * ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, F (qsN e * qsN b.1 / Z)

/-! ### Per-pair kernels -/

/-- The original low-core kernel with a piece `P`:
`Σ_{a₀ sqf, (a₀,𝔮)=1, N a₀ ≤ κ} ψ(a₀) · P(W∘sq, Z, 𝔮 c d, Z/Λ, Λ Z)`, `Z = √(M/N a₀)`. -/
def qsOrigKernel {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (P : (ℝ → ℂ) → ℝ → Ideal (𝓞 K) → ℝ → ℝ → ℂ)
    (F : QSFamily m qS) (W : ℝ → ℝ) (M κ Λ : ℝ) (𝔮 : Ideal (𝓞 K))
    (c d : Ideal (𝓞 K)) : ℂ :=
  ∑ a ∈ qsSqfUpTo κ 𝔮, (qsPairChar F c d).idealValue a *
    P (fun y => (W (y ^ 2) : ℂ)) (Real.sqrt (M / qsN a)) (𝔮 * (c * d))
      (Real.sqrt (M / qsN a) / Λ) (Λ * Real.sqrt (M / qsN a))

/-- The dual low-core kernel with a piece `P` (outer Möbius `e ∣ 𝔮` from P1):
`Σ_{e∣𝔮} μ(e) ψ(e) M/(N e √N(cd)) Σ_{a₀ sqf, N a₀ ≤ κ} ψ(a₀) · P(TW∘sq, Z, c d, Ylo, Zhi)`
with `Z = √(N e N(cd)/(M N a₀))`, `Ylo = √(N e n²/(M N a₀))/(2Λ)`, `Zhi = 2Λ√(N e n²/(M N a₀))`
(cutoffs use the column dyad length `n`, not the pair, so they do not depend on the columns). -/
def qsDualKernel {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (P : (ℝ → ℂ) → ℝ → Ideal (𝓞 K) → ℝ → ℝ → ℂ)
    (F : QSFamily m qS) (W : ℝ → ℝ) (M κ Λ n : ℝ) (𝔮 : Ideal (𝓞 K))
    (c d : Ideal (𝓞 K)) : ℂ :=
  ∑ e ∈ qsDivisors 𝔮, (qsMu e : ℂ) * (qsPairChar F c d).idealValue e *
    ((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ) *
    ∑ a ∈ qsSqfUpTo κ ⊤, (qsPairChar F c d).idealValue a *
      P (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
        (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
        (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
        (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))

/-- The dual high-core kernel (a rapid tail):
`Σ_{e∣𝔮} μ(e) ψ(e) M/(N e √N(cd)) · Σ'_{sf(a) > κ} ψ(a) (T W)(N a / Y_e)`, `Y_e = N e N(cd)/M`. -/
def qsDualHighKernel {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (W : ℝ → ℝ) (M κ : ℝ) (𝔮 : Ideal (𝓞 K))
    (c d : Ideal (𝓞 K)) : ℂ :=
  ∑ e ∈ qsDivisors 𝔮, (qsMu e : ℂ) * (qsPairChar F c d).idealValue e *
    ((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ) *
    qsHigh (qsTransform K (fun x => (W x : ℂ))) (qsN e * qsN (c * d) / M) κ ⊤
      (qsPairChar F c d)

/-- The boundary kernel of the main-term difference (lead's form of C1):
`-ρ_K Mellin(W∘sq)(1) √M (φ(cd)/N(cd)) · S_𝔮(ψ) · Σ_{t∣𝔮} ψ(t)/√N t ·
  Σ_{h sqf, (h,𝔮)=1, κ/N t < N h ≤ κ} ψ(h)/√N h`, with `S_𝔮(ψ) = Σ_{e∣𝔮} μ(e)ψ(e)/√N e`. -/
def qsBoundaryKernel {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (W : ℝ → ℝ) (M κ : ℝ) (𝔮 : Ideal (𝓞 K))
    (c d : Ideal (𝓞 K)) : ℂ :=
  -((qsResidueOne K : ℂ) * mellin (fun y => (W (y ^ 2) : ℂ)) 1 * (Real.sqrt M : ℂ) *
      (qsPhiRatio (c * d) : ℂ)) *
    (∑ e ∈ qsDivisors 𝔮, (qsMu e : ℂ) * (qsPairChar F c d).idealValue e /
      (Real.sqrt (qsN e) : ℂ)) *
    ∑ t ∈ qsDivisors 𝔮, (qsPairChar F c d).idealValue t / (Real.sqrt (qsN t) : ℂ) *
      ∑ h ∈ (qsSqfUpTo κ 𝔮).filter (fun h => κ / qsN t < qsN h),
        (qsPairChar F c d).idealValue h / (Real.sqrt (qsN h) : ℂ)

/-- Hypotheses on the columns of a residual block: squarefree coprimality ideal `𝔮` with
`qsBadRad m qS ∣ 𝔮`; columns admissible, coprime to `𝔮`, in the dyad `(n, 2n]` (so `≠ ⊤` when
`n ≥ 1`), all in one ray class. -/
def QSBlockCols (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K)) (𝔮 : Ideal (𝓞 K))
    (n : ℝ) (cols : Finset (Ideal (𝓞 K))) : Prop :=
  Squarefree 𝔮 ∧ qsBadRad m qS ∣ 𝔮 ∧
    (∀ c ∈ cols, QSAdm m qS c ∧ IsCoprime c 𝔮 ∧ n < qsN c ∧ qsN c ≤ 2 * n) ∧
    (∀ c ∈ cols, ∀ d ∈ cols, ∃ (hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc = ArtinPrimitiveRoots.Hecke.rayClass m d hd)

/-- Shape of the block bound: `M + n + √M κ^{α-1/2} + n √(M/κ)` (guide C3, found:536-540). -/
def qsBlockShape (M n κ α : ℝ) : ℝ :=
  M + n + Real.sqrt M * κ ^ (α - 1 / 2) + n * Real.sqrt (M / κ)

end ArtinPrimitiveRoots.A2
