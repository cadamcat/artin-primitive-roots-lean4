import ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_fe_export_to_ext_hecke_continuation
import ArtinPrimitiveRoots.Hecke.Dedekind

/-!
# QS-ANALYTIC, RN-A: `hkCompleted` against the Dedekind prefactor

On `Re s > 1`, `Hecke.hkCompleted ψ s = (N m)^{s/2} · G_K(s) · L(s, ψ)` with
`G_K = Hecke.dedekindPrefactor K` (totally complex, so no `Γ_ℝ` factor).
Uses the frozen HK-FE parts `hk_completed_gamma_product` and `hk_entire_L_agreement`.
-/

set_option autoImplicit false

open NumberField ClassFieldTheory
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.A2

/-- RN-A: the completed ray function agrees with `(N m)^{s/2} G_K(s) L(s, ψ)` for `Re s > 1`. -/
theorem qsa_hkCompleted_eq_series {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    Hecke.hkCompleted ψ s = ((Hecke.modulusNorm m : ℝ) : ℂ) ^ (s / 2) *
      Hecke.dedekindPrefactor K s * Hecke.LSeriesRay ψ s := by
  have hs' : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [Hecke.hk_completed_gamma_product ψ hs', Hecke.hkCompletedValue,
    (Hecke.hk_entire_L_agreement ψ hψ).2 s hs, Hecke.dedekindPrefactor,
    IsTotallyComplex.nrRealPlaces_eq_zero, pow_zero, one_mul]
  have hd : (((discr K).natAbs : ℕ) : ℝ) = |(discr K : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), hd]
  ring

end ArtinPrimitiveRoots.A2
