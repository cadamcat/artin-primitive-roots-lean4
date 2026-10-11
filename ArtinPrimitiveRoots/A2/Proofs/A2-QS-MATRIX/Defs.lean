import Mathlib
import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.A2.ZeroFree.Results
import OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator

/-!
# A2-QS: shared definitions of the quadratic large sieve core (matrix layer)

The frozen family record `QuadraticHeckeFamily` lives in `A2/QuadraticSieve.lean` together with
the three frozen theorems whose proofs are glued from this chain.  To avoid an import cycle, the
chain works with the field-for-field mirror `QSFamily` below; the glue in `QuadraticSieve.lean`
rebuilds a `QSFamily` from a `QuadraticHeckeFamily` by the anonymous constructor (same fields,
same types).  Likewise `qsQuadSymbolAt`, `qsQuadSymbol`, `qsNormT`, `qsIsExteriorGenerator` are
verbatim copies of the frozen narrow-sieve definitions (definitionally equal; the glue closes by
unfolding).

The analytic core (MATRIX, POISSON, MOBIUS, CANCEL, BOOT) is proved for families with trivial ray
reciprocity factor over a totally complex field, with rows and columns coprime to `qS`
(`QSAdm`).  This is exactly what the narrow canonical family (NQ0) provides.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- Field-for-field mirror of the frozen `QuadraticHeckeFamily m qS`
(`A2/QuadraticSieve.lean:96-135`).  Used by the QS chain to avoid importing the frozen module. -/
structure QSFamily (m : ClassFieldTheory.RayClassModulus K)
    (qS : Ideal (𝓞 K)) where
  character : Ideal (𝓞 K) → ArtinPrimitiveRoots.A1.HeckeChar K
  conductor : Ideal (𝓞 K) → Ideal (𝓞 K)
  rayFactor : ClassFieldTheory.RayClassGroup m →
    ClassFieldTheory.RayClassGroup m → ℂˣ
  rayFactor_quadratic : ∀ g h, rayFactor g h ^ 2 = 1
  trivial_infinite_type : ∀ I : Ideal (𝓞 K), ∀ w : InfinitePlace K,
    ∀ u : w.Completionˣ, (character I).locInf w u = 1
  indexCondition : ∀ c : Ideal (𝓞 K),
    Squarefree c → ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c →
      IsOfFinOrder (character c) ∧
      IsPrimitiveConductor (character c) (conductor c) ∧
      (∃ s : Ideal (𝓞 K), conductor c = c * s ∧ s ∣ qS)
  character_order_two : ∀ c : Ideal (𝓞 K), Squarefree c →
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c → character c ^ 2 = 1
  quadraticValues : ∀ c : Ideal (𝓞 K),
    ∀ hcs : Squarefree c, ∀ hcm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c,
      ∀ I : Ideal (𝓞 K),
        (character c).idealValue I = 0 ∨ (character c).idealValue I ^ 2 = 1
  reciprocity : ∀ c d : Ideal (𝓞 K),
    ∀ hc : Squarefree c,
    ∀ hcm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c,
    ∀ hd : Squarefree d,
    ∀ hdm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d,
    IsCoprime c d →
      (character c).idealValue d =
        ((rayFactor (ArtinPrimitiveRoots.Hecke.rayClass m c hcm)
          (ArtinPrimitiveRoots.Hecke.rayClass m d hdm) : ℂˣ) : ℂ) *
          (character d).idealValue c
  equalClass_product_conductor : ∀ c d : Ideal (𝓞 K),
    ∀ hc : Squarefree c,
    ∀ hcm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c,
    ∀ hd : Squarefree d,
    ∀ hdm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d,
    IsCoprime c d →
    ArtinPrimitiveRoots.Hecke.rayClass m c hcm =
      ArtinPrimitiveRoots.Hecke.rayClass m d hdm →
      IsPrimitiveConductor (character c * (character d)⁻¹) (c * d)

/-! ### Verbatim copies of the frozen narrow-sieve definitions (`A2/QuadraticSieve.lean:59-81`) -/

open Classical in
/-- Copy of the frozen `quadSymbolAt` (definitionally equal). -/
def qsQuadSymbolAt (v : HeightOneSpectrum (𝓞 K)) (c : 𝓞 K) : ℤ :=
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  quadraticChar (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk v.asIdeal c)

/-- Copy of the frozen `quadSymbol`. -/
def qsQuadSymbol (T : Finset (HeightOneSpectrum (𝓞 K))) (c : 𝓞 K) : ℤ :=
  ∏ v ∈ T, qsQuadSymbolAt v c

/-- Copy of the frozen `normT`. -/
def qsNormT (T : Finset (HeightOneSpectrum (𝓞 K))) : ℕ :=
  ∏ v ∈ T, Ideal.absNorm v.asIdeal

/-- Copy of the frozen `IsExteriorGenerator`. -/
def qsIsExteriorGenerator (S T : Finset (HeightOneSpectrum (𝓞 K))) (c : 𝓞 K) : Prop :=
  c ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    ((c ∈ v.asIdeal ↔ v ∈ T) ∧ c ∉ v.asIdeal ^ 2)

/-- The ideal `∏_{v ∈ T} 𝔭_v` of a finite set of primes. -/
def qsIdealOf (T : Finset (HeightOneSpectrum (𝓞 K))) : Ideal (𝓞 K) :=
  ∏ v ∈ T, v.asIdeal

/-! ### Arithmetic helpers -/

open Classical in
/-- Radical of an ideal: the product of its distinct normalized prime factors
(`qsRad ⊥ = ⊤`, never used at `⊥`). -/
def qsRad (I : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset, P

/-- The radical of the finite part of a ray modulus. -/
def qsModulusRad (m : ClassFieldTheory.RayClassModulus K) : Ideal (𝓞 K) :=
  ∏ v ∈ m.finitePart.support, v.asIdeal

/-- The fixed squarefree bad ideal of the core: radical of `(finite part of m) · qS`.
Meaningful for `qS ≠ ⊥`. -/
def qsBadRad (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  qsRad (qsModulusRad m * qS)

open Classical in
/-- Ideal Möbius function: `(-1)^{ω(e)}` on squarefree ideals, `0` otherwise. -/
def qsMu (e : Ideal (𝓞 K)) : ℤ :=
  if Squarefree e then (-1) ^ (UniqueFactorizationMonoid.normalizedFactors e).card else 0

open Classical in
/-- Divisors of a nonzero ideal, as a finite set (for `I = ⊥` this is `{⊥}`, never used). -/
def qsDivisors (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Ideal.absNorm I)).toFinset).filter
    (fun e => e ∣ I)

open Classical in
/-- Norm of the squarefree part: for `a = a₀ b²` with `a₀` squarefree, `N a₀`
(product of the primes with odd multiplicity). -/
def qsSfNorm (a : Ideal (𝓞 K)) : ℕ :=
  Ideal.absNorm (∏ P ∈ ((UniqueFactorizationMonoid.normalizedFactors a).toFinset.filter
      (fun P => Odd ((UniqueFactorizationMonoid.normalizedFactors a).count P))), P)

/-- `φ(I)/N I = ∏_{P ∣ I} (1 - 1/N P)` (real). -/
def qsPhiRatio (I : Ideal (𝓞 K)) : ℝ :=
  ∑ e ∈ qsDivisors I, (qsMu e : ℝ) / (Ideal.absNorm e : ℝ)

/-! ### The finite matrix and its up-to norm (M0) -/

/-- Core index condition: squarefree, coprime to the ray modulus, coprime to `qS`. -/
def QSAdm (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K))
    (I : Ideal (𝓞 K)) : Prop :=
  Squarefree I ∧ ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I ∧ IsCoprime I qS

open Classical in
/-- Admissible ideals of norm at most `X`. -/
def qsUpTo (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K)) (X : ℝ) :
    Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊).toFinset).filter
    (fun I => QSAdm m qS I ∧ (Ideal.absNorm I : ℝ) ≤ X)

/-- The up-to matrix: rows `d` of norm `≤ M`, columns `c` of norm `≤ N`, entry `χ_c(d)`. -/
def qsMatrix {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (M N : ℝ) :
    Matrix (qsUpTo m qS M) (qsUpTo m qS N) ℂ :=
  fun d c => (F.character c.1).idealValue d.1

/-- `B1(M,N)`: squared operator norm of the up-to matrix -/
def qsNorm {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (M N : ℝ) : ℝ :=
  ‖OAI.FiniteSieveOperator.operator (qsMatrix F M N)‖ ^ 2

/-- `HasExponent α`: `B1(M,N) ≪_ε (MN)^ε (M + N^α)`, constants before lengths. -/
def QSHasExponent {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    qsNorm F M N ≤ C * (M * N) ^ ε * (M + N ^ α)

/-- The sharp core bound `B1(M,N) ≪_ε (M + N)(MN)^ε`. -/
def QSCoreBound {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    qsNorm F M N ≤ C * (M + N) * (M * N) ^ ε

/-- The conclusion of the frozen `ext_goldmakher_louvel` for the mirrored family
(statement shape verbatim, `A2/QuadraticSieve.lean:141-156`). -/
def QSFamilyBound {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ Cmax Dmax : ℝ, 1 ≤ Cmax → 1 ≤ Dmax →
      ∀ (rows cols : Finset (Ideal (𝓞 K))),
        (∀ I ∈ rows, Squarefree I ∧
          ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I ∧
          (Ideal.absNorm I : ℝ) ≤ Dmax) →
        (∀ I ∈ cols, Squarefree I ∧
          ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I ∧
          (Ideal.absNorm I : ℝ) ≤ Cmax) →
        ∀ z : Ideal (𝓞 K) → ℂ,
          ∑ d ∈ rows,
            ‖∑ c ∈ cols, z c * (F.character c).idealValue d‖ ^ 2 ≤
              C * (Cmax + Dmax) * Real.rpow (Cmax * Dmax) ε *
                ∑ c ∈ cols, ‖z c‖ ^ 2

end ArtinPrimitiveRoots.A2
