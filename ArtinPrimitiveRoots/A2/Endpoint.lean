import ArtinPrimitiveRoots.A2.Coherence

set_option autoImplicit false

open NumberField IsDedekindDomain
open ClassFieldTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- **thm:hecke-zero-free** (06-zero-free.tex:754-764). Every differentiable continuation of a
ray-class Hecke L-series is nonzero in the frozen half-plane, except for the principal pole point.
-/
theorem thm_hecke_zero_free (n : ℕ) [NeZero n] (h12 : 12 ∣ n)
    (m : RayClassModulus (CyclotomicField n ℚ))
    (η : RayClassGroup m →* ℂˣ) (Λ : ℂ → ℂ)
    (hΛ : DifferentiableOn ℂ Λ
      ({s : ℂ | 1 - a2Delta0 < s.re} \ {s | η = 1 ∧ s = 1}))
    (hL : ∀ s : ℂ, 1 < s.re → Λ s = ArtinPrimitiveRoots.Hecke.LSeriesRay η s) :
    ∀ s : ℂ, 1 - a2Delta0 < s.re → (η ≠ 1 ∨ s ≠ 1) → Λ s ≠ 0 := by
  sorry

end ArtinPrimitiveRoots.A2
