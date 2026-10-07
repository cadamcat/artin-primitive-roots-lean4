import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M1
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».Defs

/-!
# A2-QS-POISSON, part P2: unweighted ideal Poisson with the residue functional at zero

Guide: `runs/lanes/sol-thin-found/PROOFS.md:363-378`.  Uses the completed Dedekind zeta of
AINTLIB (`DedekindResidue.completedDedekindZetaEntire`, functional equation
`Hecke.dedekind_completed`, order bound `Hecke.dedekind_order_one`), `qs_transform_mellin_P0`,
`qs_transform_bounds_P0`, `qs_tail_bound_M1`.

Residue bookkeeping.  `Mellin(f)(s) Y^s ζ_K(s)` has a simple pole at `s = 1` (residue
`ρ_K Y Mellin(f)(1)`) and an at most simple pole at `s = 0`: for `f = h(y²)` the Mellin pole is
simple and `ζ_K` is regular; for `f = (T h)(y²)` the gamma quotient at `s/2` has a pole of
order `r₂` and `ζ_K` a zero of order `r₂ - 1`.  So the residue at `0` is `R_K(f)` (no `log Y`).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- P2 (OPUS): unweighted ideal Poisson with explicit residue functional at zero, for the
square-variable weights `h(y²)` and `(T h)(y²)` (found:363-370):
`Σ'_{b ≠ 0} f(N b / Y) = ρ_K Y Mellin(f)(1) + R_K(f) + Y Σ'_{b ≠ 0} (T f)(Y N b)`,
both series absolutely summable. -/
theorem qs_unweighted_poisson_residue_P2 [IsTotallyComplex K]
    (f : ℝ → ℂ) (hf : IsQSSquareWeight K f) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} => ‖f ((Ideal.absNorm b.1 : ℝ) / Y)‖) ∧
      Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        ‖qsTransform K f (Y * (Ideal.absNorm b.1 : ℝ))‖) ∧
      ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, f ((Ideal.absNorm b.1 : ℝ) / Y) =
        (qsResidueOne K : ℂ) * (Y : ℂ) * mellin f 1 + qsResidueZero K f +
          (Y : ℂ) * ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            qsTransform K f (Y * (Ideal.absNorm b.1 : ℝ)) := by
  sorry

/-- P2' (IMPL): the coprime square-variable sum split into the five pieces
(Möbius `Σ_{e∣𝔫} μ(e) 1_{e∣b}`, P2 at scale `Z/N e` for `N e ≤ Zhi`, direct sums for
`N e > Zhi`; dual sums with `N e ≤ Ylo` go to the tail).  Guide found:366-367, 376-378. -/
theorem qs_coprime_square_pieces_P2 [IsTotallyComplex K]
    (F : ℝ → ℂ) (hF : IsQSSquareWeight K F) (Z : ℝ) (hZ : 0 < Z) (𝔫 : Ideal (𝓞 K))
    (h𝔫 : 𝔫 ≠ ⊥) (Ylo Zhi : ℝ) (hYZ : Ylo ≤ Zhi) :
    qsCoprimeSq F Z 𝔫 =
      qsInnerMain K F Z 𝔫 Ylo Zhi - qsInnerHighDiv K F Z 𝔫 Ylo Zhi +
        qsInnerRes K F Z 𝔫 Ylo Zhi + qsInnerTrans K F Z 𝔫 Ylo Zhi +
          qsInnerTail K F Z 𝔫 Ylo Zhi := by
  sorry

end ArtinPrimitiveRoots.A2
