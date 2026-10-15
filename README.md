[English](README.md) | [简体中文](README_zh.md)

# Artin's primitive roots in Lean 4

Every integer other than −1 that is not a perfect square is a primitive root modulo infinitely many primes.

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [authors and attribution](AUTHORS.md).
- **Mathematical result:** OpenAI, [*Primitive roots for every admissible integer base*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf).
- Developed with AI assistance; all proofs are verified by the Lean 4 kernel.

## Main result

| Theorem | Statement |
| --- | --- |
| `ArtinPrimitiveRootsConjecture.artin_primitive_roots_infinite` | For every `a : ℤ` with `a ≠ -1` and `¬ IsSquare a`, the set `S a = {p : ℕ \| p.Prime ∧ orderOf (a : ZMod p) = (p-1 : ℕ)}` is infinite. |

The proof is in [ArtinPrimitiveRoots/Target.lean](ArtinPrimitiveRoots/Target.lean). The challenge statement, written with Mathlib definitions only, is in [Challenge.lean](Challenge.lean); [comparator.json](comparator.json) configures Comparator to compare the two. The definition of `S` is copied from `ArtinPrimitiveRootsConjecture.S` in Formal Conjectures (`FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean`, commit `9d259649abe0b02d7a25f7589b872db679b35e21`), which states only the density forms of the conjecture.

`orderOf` is the multiplicative order in `ZMod p`. If `p` divides `a`, the order of `0` is `0`, so such primes are never in `S a`. For odd `a`, the prime 2 is in `S a`, because the order of 1 is `1 = 2 - 1`; this adds at most one prime and does not affect infinitude.

## The proof

The formalization follows OpenAI's paper. Its Theorem 1.1 gives, for every admissible `a`, constants `c > 0` and `X ≥ 2` such that every interval `(x, 2x)` with `x ≥ X` contains at least `c x / (log x)²` primes `p` not dividing `a` for which `a` is a primitive root. This is `ArtinPrimitiveRoots.thm_main` in [ArtinPrimitiveRoots/Reduction.lean](ArtinPrimitiveRoots/Reduction.lean); the main theorem follows from it by choosing `x` beyond any finite set of primes.

A prime `p` fails to have `a` as a primitive root when some prime `q` divides the index `(p − 1)/ord_p(a)`. The proof builds primes for which every possible `q` is either very large or in a middle range, and removes each range separately. It has three parts, each a separate theorem in Lean:

1. **Primes with controlled predecessors** (`ArtinPrimitiveRoots.prop_controlled`, [Controlled.lean](ArtinPrimitiveRoots/Controlled.lean)). In a fixed residue class, there are `≫ x/(log x)²` primes `p ∈ (x, 2x)` with `p − 1 = c r Q`, where `c ∈ {2, 4}`, `Q > x^0.9` is prime, and every prime factor of `r` lies between `exp((log x)^0.1)` and `exp((log x)^0.3)`. The residue class makes `a` a quadratic non-residue, which excludes `q = 2`. The proof combines a sieve, a marked bilinear (Type II) estimate from OpenAI's Poisson–Dirichlet paper, Bombieri–Vinogradov, and Buchstab's identity.
2. **Uniform complete splitting** (`ArtinPrimitiveRoots.prop_splitting`, [Splitting.lean](ArtinPrimitiveRoots/Splitting.lean)). For a prime `q ≤ exp((log x)^0.3)`, the primes in `(x, 2x]` that split completely in `ℚ(μ_q, a^{1/q})` number `O(x/(q(q−1) log x) + x^{1−10⁻⁶})`, with constants independent of `q`. The formal statement counts primes `p` with `q ∣ p − 1` and `a^{(p−1)/q} = 1` in `ZMod p`.
3. **A Hecke zero-free region of fixed width** (`ArtinPrimitiveRoots.HeckeBoundary.thm_hecke_zero_free`, [Hecke/Boundary.lean](ArtinPrimitiveRoots/Hecke/Boundary.lean)). For the cyclotomic field `F = ℚ(μ_n)` with `12 ∣ n` and every character of a ray class group of `F`, the Hecke L-function continues meromorphically to `Re s > 1 − 10⁻⁶` and has no zeros there. The width does not depend on `F` or the character. This drives part 2. The proof compares two evaluations of one additive average of cubic theta coefficients under sextic Kummer twists, one by coefficient reflection and one by Poisson summation, following the paper's zero-free sections and its appendix on the Kazhdan–Patterson theta normalization.

For a prime from part 1, an index divisor `q ≠ 2` either equals `Q` or divides `r`. If it equals `Q`, the order of `a` divides `c r < 2x^0.1`, so `p` divides `a^j − 1` for some small `j`, and few primes do. Divisors of `r` lie in the range of part 2, and summed over that range they remove fewer primes than part 1 supplies.

## Build and verify

Requirements: Git, Python 3, and [elan](https://github.com/leanprover/elan), with `lake` available on `PATH`. From the repository root, a fresh checkout is prepared with:

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI's `lake update` hook exits with an error beginning `iut: Lake resolved an unexpected checkout at …` after resolving dependencies and writing `lake-manifest.json`. Run the patch script next; it applies OpenAI's Lean 4.34.1 compatibility patches to the fetched packages and can be run again after another `lake update`. `lake exe cache get` fetches compiled Mathlib; the other dependencies are compiled from source by `lake build`.

To check the statement and the final theorem's axioms, run `LEAN_NUM_THREADS=4 ./scripts/verify.sh`. It checks that [ArtinPrimitiveRoots/Target.lean](ArtinPrimitiveRoots/Target.lean) states the theorem with the same text as [Challenge.lean](Challenge.lean), checks each against one displayed statement in Lean, and prints the axioms of `ArtinPrimitiveRootsConjecture.artin_primitive_roots_infinite`; the accepted set is `propext`, `Classical.choice` and `Quot.sound`. Details are in [docs/verification.md](docs/verification.md).

## Fixed dependencies

- Lean `v4.34.1`, selected by [lean-toolchain](lean-toolchain).
- [Mathlib](https://github.com/leanprover-community/mathlib4), commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- OpenAI's [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean) at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, and the packages it pins. This project imports from [ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory) (`2eb22d6`, also its `ValuedFieldTheory` and `GaloisCohomology` libraries), [TauCeti](https://github.com/TauCetiProject/TauCeti) (`3bed7e3`), [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (`160e446`, its `DedekindResidue` library), [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (`c39a751`) and [rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov) (`70f85d4`).
- All revisions are fixed in [lake-manifest.json](lake-manifest.json).

## Mathematical references

- OpenAI, [*Primitive roots for every admissible integer base*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf).
- OpenAI, [*The Poisson–Dirichlet law for prime predecessors*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf), Theorem 3.1 (the marked prime estimate used in part 1).
- C. Hooley, *On Artin's conjecture*, J. reine angew. Math. 225 (1967), 209–220.
- D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142.

See [THIRD_PARTY.md](THIRD_PARTY.md) for code attribution and [LICENSE](LICENSE) for the project license.
