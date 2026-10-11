import Mathlib
import ArtinPrimitiveRoots.A2.ZeroFree.Results
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-NARROW».NQ

/-!
# Design draft A2-QuadraticSieve: the narrow quadratic large sieve consumed by A2

Status: design draft, compiled against Mathlib `d13f23b` only; the theorem is `sorry`.

Consumer: A2 `lem:reflection-quadratic-sieve` (04-reflection.tex:941-1025), which feeds
`rf:retained-mass` and hence `prop:reflection`.  Only this
narrow statement is formalized, not Goldmakher–Louvel's general family theorem.

Mathematical content.  `K` a number field containing a primitive 12th root of unity, `S` a finite
set of finite primes containing every prime above 2.  Rows: squarefree integral ideals `𝔡`
coprime to `S`, `N𝔡 ≤ D`.  Columns: squarefree integral ideals `𝔠` coprime to `S`, `N𝔠 ≤ C`,
each represented by an element `c ∈ 𝓞_K` whose prime factorization outside `S` is exactly `𝔠`
(arbitrary at `S`).  Symbol: the quadratic (Jacobi) symbol `(c/𝔡) = ∏_{𝔭 ∣ 𝔡} (c mod 𝔭)^{(N𝔭-1)/2}`
(zero when `𝔭 ∣ c`).  Conclusion: `Σ_𝔡 |Σ_𝔠 z_𝔠 (c/𝔡)|² ≪_{K,S,ε} (C + D)(CD)^ε Σ |z_𝔠|²`,
the constant independent of the choice of representatives `c`.

Relation to the consumer.  In 04-reflection the symbol is `χ_𝔡(c)^3` (A1's sextic symbol, A1
node for `χ_𝔭`) with `c` an *allowed* generator (A1 `lem:balanced-generators`) of the exterior
ideal `𝔠R`, `R = O_S`.  Since `χ_𝔭(x)^3 ≡ x^{(N𝔭-1)/2}`, `χ_𝔡(c)^3 = (c/𝔡)`.  An allowed `c ∈ R`
may have negative valuations at `S`; multiplying by `π^{2k}` with `π ∈ 𝓞_K` supported exactly on
`S` (exists: a power of each prime of `S` is principal) gives an integral representative with the
same symbol, since `(π/𝔡)² = 1` for `𝔡` coprime to `S`.  Rows of the consumer are the exterior
squarefree ideals of `R`, i.e. squarefree `𝓞_K`-ideals coprime to `S` (same norms).  Hence this
statement implies the consumer's eq. (reflection-quadratic-sieve) verbatim.

Why arbitrary representatives cost nothing in the proof.  The proof (A2-DESIGN §4) first treats
allowed generators, where `χ_𝔡(c)^3 = χ_𝔠(d)^3` exactly (A1 `eq:generator-reciprocity` cubed),
and then splits the columns into the finitely many classes of `c / (allowed generator) ∈ U_S`
modulo squares (finite: A1 `lem:balanced-generators`, injection `U_S/U_S^6 ↪ 𝒱`); each class
contributes a row twist of modulus one.  Enlarging `S` to A1's final set is likewise harmless.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

open Classical in
/-- The quadratic residue symbol of `c ∈ 𝓞_K` at a finite prime `v`: the quadratic character of
the residue field `𝓞_K/𝔭_v` applied to `c mod 𝔭_v` (value `0` if `𝔭_v ∣ c`).  Meaningful
(a quadratic character) for `v` of odd residue characteristic. -/
def quadSymbolAt (v : HeightOneSpectrum (𝓞 K)) (c : 𝓞 K) : ℤ :=
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  quadraticChar (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk v.asIdeal c)

/-- The Jacobi symbol `(c/𝔡)` for the squarefree ideal `𝔡 = ∏_{v ∈ T} 𝔭_v`. -/
def quadSymbol (T : Finset (HeightOneSpectrum (𝓞 K))) (c : 𝓞 K) : ℤ :=
  ∏ v ∈ T, quadSymbolAt v c

/-- `N𝔡` for `𝔡 = ∏_{v ∈ T} 𝔭_v`. -/
def normT (T : Finset (HeightOneSpectrum (𝓞 K))) : ℕ :=
  ∏ v ∈ T, Ideal.absNorm v.asIdeal

/-- `c` represents the squarefree ideal `∏_{v ∈ T} 𝔭_v` away from `S`: `c ≠ 0`, and for every
prime `v ∉ S`, `𝔭_v ∣ c ↔ v ∈ T`, and `𝔭_v² ∤ c`. -/
def IsExteriorGenerator (S T : Finset (HeightOneSpectrum (𝓞 K))) (c : 𝓞 K) : Prop :=
  c ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    ((c ∈ v.asIdeal ↔ v ∈ T) ∧ c ∉ v.asIdeal ^ 2)

/-- **lem:reflection-quadratic-sieve** (04-reflection.tex:941-1025).  This is the narrow
quadratic large sieve in the any-integral-representative form.  Quantifier
order: `K, S` fixed; for each `ε > 0` one constant `C`
serves all lengths, all row and column families and all choices of representatives `gen`. -/
theorem narrow_quadratic_large_sieve
    (hμ : ∃ ζ : K, IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (Cmax Dmax : ℝ), 1 ≤ Cmax → 1 ≤ Dmax →
      ∀ (gen : Finset (HeightOneSpectrum (𝓞 K)) → 𝓞 K)
        (cols rows : Finset (Finset (HeightOneSpectrum (𝓞 K)))),
        (∀ T ∈ cols, Disjoint T S ∧ (normT T : ℝ) ≤ Cmax ∧ IsExteriorGenerator S T (gen T)) →
        (∀ T ∈ rows, Disjoint T S ∧ (normT T : ℝ) ≤ Dmax) →
        ∀ z : Finset (HeightOneSpectrum (𝓞 K)) → ℂ,
          ∑ D ∈ rows, ‖∑ T ∈ cols, z T * (quadSymbol D (gen T) : ℂ)‖ ^ 2 ≤
            C * (Cmax + Dmax) * (Cmax * Dmax) ^ ε * ∑ T ∈ cols, ‖z T‖ ^ 2 :=
  qs_narrow_large_sieve hμ S hS

/-- **ext:goldmakher-louvel** (Goldmakher--Louvel 2013, Definition 1 and Theorem 1.1;
04-reflection.tex:958-1024). A quadratic Hecke family indexed by squarefree ideals prime to a
fixed ray modulus, with conductor supported on the index ideal and the fixed modulus, ray-class
reciprocity, and the equal-class product-conductor condition. Corrected per rev-a2 to require
nonzero primitive conductors, trivial infinite type, and a quadratic reciprocity factor. -/
structure QuadraticHeckeFamily (m : ClassFieldTheory.RayClassModulus K)
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

open Classical in
/-- Rational quadratic residue symbol at an odd prime, with value zero when the numerator is
divisible by the prime. -/
def rationalQuadraticSymbol (a p : ℕ) : ℤ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    quadraticChar (ZMod p) (a : ZMod p)
  else 1

open Classical in
/-- The Jacobi symbol as the product of the local quadratic characters over prime divisors. -/
def rationalJacobiSymbol (a m : ℕ) : ℤ :=
  ∏ p ∈ m.primeFactors, rationalQuadraticSymbol a p

open Classical in
/-- Odd squarefree integers at most `N`. -/
def oddSquarefreeUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => n % 2 = 1 ∧ Squarefree n)

end ArtinPrimitiveRoots.A2
