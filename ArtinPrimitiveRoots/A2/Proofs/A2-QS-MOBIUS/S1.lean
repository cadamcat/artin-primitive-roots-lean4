import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P1

/-!
# A2-QS-MOBIUS, part S1: squarefree removal with both principal terms retained

Guide: `runs/lanes/sol-thin-found/PROOFS.md:409-418` (lead's exact form).  For one coprime
equal-class residual pair `(c, d)`, `c d ≠ ⊤`, with `ψ = χ_c χ_d⁻¹` of exact conductor `f = c d`
(`equalClass_product_conductor`) and the squarefree coprimality ideal `𝔮` coprime to `c d`:

`qsHigh W M κ 𝔮 ψ = DualLow + DualHigh − OrigLow`, where
* `Tot = Σ_{e∣𝔮} μ(e) ψ(e) Σ_a ψ(a) W(N e N a/M)` (Möbius), then P1 at `X = M/N e`;
* the dual sum `Σ_a ψ(a) (T W)(N a/Y_e)` splits at `sf(a) ≤ κ` / `> κ`;
* `a = a₀ b²` with `ψ(b)² = 1_{(b,f)=1}` turns each low sum into
  `Σ_{a₀} ψ(a₀) · qsCoprimeSq (h∘sq) √(X/N a₀) 𝔫`.
The "full" piece `fun F Z 𝔫 _ _ => qsCoprimeSq F Z 𝔫` inserted in the kernels expresses this.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- S1 (IMPL; RETIER `qs_squarefree_removal_S1`, hardest of MOBIUS): exact squarefree-removal
identity for one residual pair. -/
theorem qs_squarefree_removal_S1 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (M κ Λ n : ℝ) (hM : 0 < M)
    (𝔮 c d : Ideal (𝓞 K)) (h𝔮 : Squarefree 𝔮) (h𝔮bad : qsBadRad m qS ∣ 𝔮)
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d) (hcd1 : c * d ≠ ⊤)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (hc𝔮 : IsCoprime c 𝔮) (hd𝔮 : IsCoprime d 𝔮) :
    qsHigh (fun x => (W x : ℂ)) M κ 𝔮 (qsPairChar F c d) =
      qsDualKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫) F W M κ Λ n 𝔮 c d +
        qsDualHighKernel F W M κ 𝔮 c d -
          qsOrigKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫) F W M κ Λ 𝔮 c d := by
  sorry

end ArtinPrimitiveRoots.A2
