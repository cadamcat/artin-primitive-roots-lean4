import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».Defs
import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNDict
import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNStrip
import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNRootOne

/-!
# A2-QS-POISSON, part RN: functional equation with root number `+1` for quadratic characters

Guide: `runs/lanes/sol-thin-found/PROOFS.md:350-358` (root number `+1`, not only modulus one;
`RouteGates.unit_root_number_does_not_determine_sign`).

FE source.  This part is stated directly in the form P1 consumes, against the raw ideal series
`A2.heckeLSeries` (`A2/ZeroFree/Results.lean:47-50`), so it does not wait for the exact export
names of the `hk-fe-lead` lane.  Its proof is expected to combine HK-FE (the Hecke functional
equation of the primitive character with some root number `W(χ)`, `|W(χ)| = 1`, and strip
boundedness of the completed function), the idelic-to-ray dictionary (HK-DICT-RAY), and the
`W(χ) = +1` argument (quadratic extension `E/K`, `ζ_E = ζ_K L(χ)`, conductor-discriminant
formula; or the signed quadratic Gauss product).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- RN (SOL-LEAD): for a nonprincipal quadratic idelic Hecke character `χ` of trivial infinite
type and primitive conductor `f` over a totally complex field, the completed function
`Λ(s) = (N f)^{s/2} G_K(s) L(s,χ)` (`G_K = Hecke.dedekindPrefactor K`) extends to an entire
function, bounded on every vertical strip, with `Λ(1-s) = Λ(s)` (root number exactly `+1`). -/
theorem qs_quadratic_FE_root_one [IsTotallyComplex K]
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f : Ideal (𝓞 K))
    (hf : IsPrimitiveConductor χ f) (hsq : χ ^ 2 = 1) (hne : χ ≠ 1)
    (hinf : ∀ w : InfinitePlace K, ∀ u : w.Completionˣ, χ.locInf w u = 1) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ s : ℂ, 1 < s.re →
        Λ s = ((Ideal.absNorm f : ℝ) : ℂ) ^ (s / 2) * Hecke.dedekindPrefactor K s *
          heckeLSeries χ s) ∧
      (∀ s : ℂ, Λ (1 - s) = Λ s) ∧
      (∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ C) := by
  obtain ⟨m, ψ, hN, hψ1, hinv, hprim, hL⟩ := qsa_ray_of_quadratic χ f hf hsq hne
  have hexp := Hecke.hk_fe_export_to_ext_hecke_continuation ψ hψ1 hprim
  refine ⟨Hecke.hkCompleted ψ, hexp.2.2.2.2.1, ?_, ?_, ?_⟩
  · intro s hs
    rw [qsa_hkCompleted_eq_series ψ hψ1 hs, hN, hL s hs]
  · intro s
    exact qsa_hkCompleted_one_sub ψ hψ1 hinv hprim s
  · intro a b
    exact qsa_hkCompleted_strip_bound ψ hψ1 a b

end ArtinPrimitiveRoots.A2
