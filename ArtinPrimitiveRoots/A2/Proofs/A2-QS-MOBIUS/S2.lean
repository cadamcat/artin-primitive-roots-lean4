import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S1
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2

/-!
# A2-QS-MOBIUS, part S2: the full error tuple of one residual pair

Guide: `runs/lanes/sol-thin-found/PROOFS.md:419-432` (lead's exact form).  Insert
`qs_coprime_square_pieces_P2` into both low kernels of `qs_squarefree_removal_S1`.  In the
guide's names: `E₁ = dual highDiv`, `E₂ = dual res`, `E₃ = dual trans`, `E₄ = orig highDiv`,
`E₀ = orig res`, `E₅ = orig trans`; the main terms are kept as the signed difference
`dual main − orig main` (C1).  Cutoffs: original `Z/Λ ≤ ΛZ`, dual `r/(2Λ) ≤ 2Λr` (`Λ ≥ 1`).
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- S2 (IMPL): the exact error tuple of one residual pair. -/
theorem qs_pair_error_tuple_S2 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (M κ Λ n : ℝ) (hM : 0 < M) (hΛ : 1 ≤ Λ) (hn : 0 < n)
    (𝔮 c d : Ideal (𝓞 K)) (h𝔮 : Squarefree 𝔮) (h𝔮bad : qsBadRad m qS ∣ 𝔮)
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d) (hcd1 : c * d ≠ ⊤)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (hc𝔮 : IsCoprime c 𝔮) (hd𝔮 : IsCoprime d 𝔮) :
    qsHigh (fun x => (W x : ℂ)) M κ 𝔮 (qsPairChar F c d) =
      (qsDualKernel (qsInnerMain K) F W M κ Λ n 𝔮 c d -
          qsOrigKernel (qsInnerMain K) F W M κ Λ 𝔮 c d)
        - qsDualKernel (qsInnerHighDiv K) F W M κ Λ n 𝔮 c d
        + qsDualKernel (qsInnerRes K) F W M κ Λ n 𝔮 c d
        + qsDualKernel (qsInnerTrans K) F W M κ Λ n 𝔮 c d
        + qsOrigKernel (qsInnerHighDiv K) F W M κ Λ 𝔮 c d
        - qsOrigKernel (qsInnerRes K) F W M κ Λ 𝔮 c d
        - qsOrigKernel (qsInnerTrans K) F W M κ Λ 𝔮 c d
        + (qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d
            - qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d
            + qsDualHighKernel F W M κ 𝔮 c d) := by
  sorry

end ArtinPrimitiveRoots.A2
