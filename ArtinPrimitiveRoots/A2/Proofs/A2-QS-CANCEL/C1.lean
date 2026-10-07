import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P0

/-!
# A2-QS-CANCEL, part C1: the main-term difference is a boundary sum

Guide: `runs/lanes/sol-thin-found/PROOFS.md:443-458` (lead's form).  With `I_W = Mellin(W∘sq)(1)
= Mellin((T W)∘sq)(1)` (`qs_half_mellin_P0`) and `φ(𝔮f)/N(𝔮f) = (φ(𝔮)/N𝔮)(φ(f)/N f)`,
`dual main − orig main = ρ_K I_W √M (φ(f)/N f) · D_κ(ψ)` with
`D_κ = A_κ · S_𝔮 − (φ(𝔮)/N𝔮) A_{κ,𝔮}`, `A_κ = Σ_{a₀ sqf, N a₀ ≤ κ} ψ(a₀)/√N a₀`,
`A_{κ,𝔮}` the same with `(a₀,𝔮) = 1`, `S_𝔮 = Σ_{e∣𝔮} μ(e)ψ(e)/√N e`.  Writing `a₀ = h t`,
`t = (a₀, 𝔮)`, and expanding `φ(𝔮)/N𝔮` by C0, the two sums agree on `N h N t ≤ κ`, leaving
`D_κ = −S_𝔮 Σ_{t∣𝔮} ψ(t)/√N t Σ_{(h,𝔮)=1, κ/N t < N h ≤ κ} ψ(h)/√N h` (`qsBoundaryKernel`).
At `𝔮 = ⊤` the boundary is empty: `T = T'` exactly.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- C1 (IMPL): exact support of `T − T'` for one residual pair. -/
theorem qs_difference_exact_support_C1 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (M κ Λ n : ℝ) (hM : 0 < M)
    (𝔮 c d : Ideal (𝓞 K)) (h𝔮 : Squarefree 𝔮) (h𝔮bad : qsBadRad m qS ∣ 𝔮)
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (hc𝔮 : IsCoprime c 𝔮) (hd𝔮 : IsCoprime d 𝔮) :
    qsDualKernel (qsInnerMain K) F W M κ Λ n 𝔮 c d -
        qsOrigKernel (qsInnerMain K) F W M κ Λ 𝔮 c d =
      qsBoundaryKernel F W M κ 𝔮 c d := by
  sorry

end ArtinPrimitiveRoots.A2
