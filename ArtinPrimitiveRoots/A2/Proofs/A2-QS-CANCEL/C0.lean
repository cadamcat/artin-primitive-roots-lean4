import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».Defs
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M0

/-!
# A2-QS-CANCEL, part C0: local signed divisor-pair identity

Guide: `runs/lanes/sol-thin-found/PROOFS.md:435-442`.  Local factor
`(1 + x/√q)(1 − x/√q) = 1 − 1/q` for `x = ψ(P) ∈ {±1}`; compiled algebra
`squarefree_mobius_pair`, `quadratic_local_factor` in
`runs/lanes/sol-thin-found/wt/ArtinPrimitiveRoots/Review/sol-thin-found/SieveAlgebra.lean`.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- C0 (IMPL): for squarefree `𝔮 ≠ ⊥` and a character `ψ` with `ψ(P)² = 1` at every prime
`P ∣ 𝔮` (unramified quadratic there),
`(Σ_{t∣𝔮} ψ(t)/√N t) · (Σ_{e∣𝔮} μ(e) ψ(e)/√N e) = φ(𝔮)/N 𝔮`. -/
theorem qs_local_signed_identity_C0 (ψ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (𝔮 : Ideal (𝓞 K)) (h𝔮 : Squarefree 𝔮)
    (hψ : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → P ∣ 𝔮 → ψ.idealValue P ^ 2 = 1) :
    (∑ t ∈ qsDivisors 𝔮, ψ.idealValue t / (Real.sqrt (qsN t) : ℂ)) *
      (∑ e ∈ qsDivisors 𝔮, (qsMu e : ℂ) * ψ.idealValue e / (Real.sqrt (qsN e) : ℂ)) =
        (qsPhiRatio 𝔮 : ℂ) := by
  sorry

/-- C0 (IMPL): `φ(I J)/N(I J) = (φ(I)/N I)(φ(J)/N J)` for coprime nonzero `I, J`. -/
theorem qs_phiRatio_mul_C0 (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIJ : IsCoprime I J) :
    qsPhiRatio (I * J) = qsPhiRatio I * qsPhiRatio J := by
  sorry

end ArtinPrimitiveRoots.A2
